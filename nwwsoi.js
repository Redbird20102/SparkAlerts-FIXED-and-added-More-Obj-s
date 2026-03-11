/*
(c) 2024 Tyler Granzow - Apache License 2.0

This file hosts an asynchronous function to listen to the NWWS-OI
XMPP feed, parses incoming alert messages, and stores them in alerts.json
such that the server can be restarted without losing data.

It also performs periodic cleanup of expired alerts from the database.

*/


// Imports
const fs = require('fs');
const { nosyncLog } = require('./logging.js').nosyncLog;
const xml2js = require('xml2js');
const path = require('path');
const { log } = require('./logging.js');
const { sign } = require('crypto');
const https = require('https');

// Load phenomena mapping
const phenomena = require('./phenomena.json');

// For storing crexentials
var username = null;
var password = null;
var resource = null;
var MAX_RECONNECT_ATTEMPTS = 10;
var INITIAL_RECONNECT_DELAY = 2000;

// Startup alert filtering: remove alerts with same eventTrackingNumber if issued before another's startTime

function filterAlertsOnStartup() {
    try {
        let alerts = [];
        try {
            const raw = fs.readFileSync('alerts.json', 'utf8');
            alerts = raw.trim() ? JSON.parse(raw) : [];
            if (!Array.isArray(alerts)) alerts = [];
        } catch (readErr) {
            if (readErr.code !== 'ENOENT') {
                console.warn('alerts.json unreadable during startup filter:', readErr.message);
            }
            return;
        }
        const etnMap = {};
        alerts.forEach(alert => {
            const etn = alert.properties && alert.properties.event_tracking_number;
            if (!etn) return;
            const sent = new Date(alert.sent || alert.properties.recievedTime || 0).getTime();
            if (!etnMap[etn] || sent > etnMap[etn].sent) {
                etnMap[etn] = { alert, sent };
            }
        });
        // Add alerts without event_tracking_number
        const filteredAlerts = alerts.filter(alert => !(alert.properties && alert.properties.event_tracking_number));
        // Add only the latest alert for each eventTrackingNumber
        filteredAlerts.push(...Object.values(etnMap).map(obj => obj.alert));
        fs.writeFileSync('alerts.json', JSON.stringify(filteredAlerts, null, 2));
        console.log('Startup alert filter applied.');
    } catch (err) {
        console.error('Error during startup alert filter:', err);
    }
}

filterAlertsOnStartup();

// In-memory alerts cache to avoid synchronous disk I/O on every message
let alertsCache = [];
try {
    const raw = fs.readFileSync('alerts.json', 'utf8');
    alertsCache = raw.trim() ? JSON.parse(raw) : [];
    if (!Array.isArray(alertsCache)) alertsCache = [];
} catch (e) {
    alertsCache = [];
}

// Async persistence with debounce to batch frequent updates
const PERSIST_DEBOUNCE_MS = 250;
let _persistTimer = null;
function schedulePersistAlerts() {
    if (_persistTimer) clearTimeout(_persistTimer);
    _persistTimer = setTimeout(() => {
        fs.writeFile('alerts.json', JSON.stringify(alertsCache, null, 2), (err) => {
            if (err) {
                console.error('Error persisting alerts.json:', err);
                log('Error persisting alerts.json: ' + err);
            }
        });
        _persistTimer = null;
    }, PERSIST_DEBOUNCE_MS);
}
// Helper: build alert name from phenomena and significance codes
function buildAlertNameFromVtec(phenomCode, significanceCode) {
    if (!phenomCode || !significanceCode) return null;

    // Special-case: Red Flag Warning (FW + W)
    try {
        if (String(phenomCode).toUpperCase() === 'FW' && String(significanceCode).toUpperCase() === 'W') {
            return 'Red Flag Warning';
        }
    } catch (e) {
        // fallthrough
    }

    // Look up phenomenon name from phenomena.json
    const phenomEntry = phenomena[phenomCode];
    if (!phenomEntry || !phenomEntry.name) return null;

    // Map significance code to label
    const significanceMap = {
        'W': 'Warning',
        'A': 'Watch',
        'Y': 'Advisory',
        'S': 'Statement'
    };

    const label = significanceMap[significanceCode] || significanceCode;
    return `${phenomEntry.name} ${label}`;
}

(async () => {
    // Polyfill WebSocket for @xmpp/client
    const { client, xml } = await import('@xmpp/client');
    const wsModule = await import('ws');
    global.WebSocket = wsModule.default || wsModule.WebSocket || wsModule;

    // Variable to store the interval ID so we can stop it if needed
    let deleteExpiredAlertsInterval = null;

    // Task to clean up the alerts.json file
    async function deleteExpiredAlerts() {
        console.log('Running expired alerts cleanup...');
        try {
            let alerts = [];

            try {
                const raw = fs.readFileSync('alerts.json', 'utf8');
                alerts = raw.trim() ? JSON.parse(raw) : [];
                if (!Array.isArray(alerts)) alerts = [];
            } catch (readErr) {
                if (readErr.code !== 'ENOENT') {
                    console.warn('alerts.json unreadable during cleanup:', readErr.message);
                    log('alerts.json unreadable during cleanup: ' + readErr.message);
                }

                return; // Nothing to clean
            }

            // Remove alerts whose endTime (expires) is in the past
            const now = new Date();
            const initialCount = alerts.length;
            alerts = alerts.filter(alert => {
                let endTime = null;
                if (alert.expires) {
                    endTime = new Date(alert.expires);
                } else if (alert.properties && alert.properties.vtec && alert.properties.vtec.endTime) {
                    endTime = new Date(alert.properties.vtec.endTime);
                }
                if (!endTime || isNaN(endTime.getTime())) return true; // Keep if no valid endTime
                return now <= endTime; // Keep only non-expired alerts
            });

            const removedCount = initialCount - alerts.length;

            // Write back only if something was removed
            if (removedCount > 0) {
                fs.writeFileSync('alerts.json', JSON.stringify(alerts, null, 2));
                console.log(`Expired alerts cleanup: removed ${removedCount} alert(s).`);
                log(`Expired alerts cleanup: removed ${removedCount} alert(s).`);
            } else {
                console.log('Expired alerts cleanup: no expired alerts found.');
            }
        } catch (err) {
            log('Error in database cleanup: ' + err);
            console.error('Error in database cleanup:', err);
        }
    }

    // Run the deleteExpiredAlerts task every minute
    if (!deleteExpiredAlertsInterval) {
        deleteExpiredAlerts();
        deleteExpiredAlertsInterval = setInterval(deleteExpiredAlerts, 60 * 1000);
    }

    // Connection management
    let reconnectAttempt = 0;
    const MAX_RECONNECT_ATTEMPTS = 10;
    const RECONNECT_DELAY = 2000; // 2 seconds

    // Function to create XMPP client object
    function createXMPPClient() {
        console.log('Creating XMPP client...');
        // Read XMPP configuration from environment variables to avoid hard-coding credentials.
        const xmppConfig = {
            service: 'xmpp://nwws-oi.weather.gov',
            domain: 'nwws-oi.weather.gov',
            username: username,
            password: password,
            resource: resource
        };

        if (!xmppConfig.username || !xmppConfig.password) {
            console.warn('No credentials found in .env file! Did you set XMPP_USERNAME and XMPP_PASSWORD variables?');
            process.exit(1);
        }
        
        console.log(`Connecting as ${xmppConfig.username} with resource: ${xmppConfig.resource}`);

        const xmpp = client(xmppConfig);

        // Handle disconnections
        xmpp.on('disconnect', () => {
            log('XMPP client disconnected. Reconnecting...');
            handleReconnect();
        });

        // Handle connection closed
        xmpp.on('close', () => {
            log('XMPP connection closed. Reconnecting...');
            handleReconnect();
        });

        // Handle stream/client errors to avoid unhandled exceptions crashing the process.
        xmpp.on('error', (err) => {
            try {
                const msg = (err && err.message) ? err.message : String(err);
                log('XMPP error: ' + msg);
                console.error('XMPP error:', err);

                // If the error is a stream 'conflict', it's typically a resource/jid conflict
                // (another client connected with the same JID). Attempt a reconnect with backoff.
                if (err && err.condition === 'conflict') {
                    log('XMPP stream conflict detected; will attempt reconnect.');
                    handleReconnect();
                    return;
                }

                // For other errors, attempt reconnect as well but do not throw.
                handleReconnect();
            } catch (e) {
                console.error('Error handling XMPP error event:', e);
            }
        });

        return xmpp;
    }

    async function handleReconnect() {
        console.log('Handling reconnection...');
        // Clear any existing intervals
        if (deleteExpiredAlertsInterval) {
            clearInterval(deleteExpiredAlertsInterval);
            deleteExpiredAlertsInterval = null;
            console.log('Cleared existing cleanup interval');
        }

        if (reconnectAttempt >= MAX_RECONNECT_ATTEMPTS) {
            log('Max reconnection attempts reached. Check network connection and credentials, or increase MAX_RECONNECT_ATTEMPTS.');
            console.error('FATAL: Max reconnection attempts reached!');
            process.exit(1);
        }

        // Exponential backoff with jitter
        const delay = RECONNECT_DELAY * Math.pow(2, reconnectAttempt) + Math.random() * 1000;
        log(`Attempting reconnection in ${Math.round(delay / 1000)} seconds (attempt ${reconnectAttempt + 1}/${MAX_RECONNECT_ATTEMPTS})...`);
        await new Promise(resolve => setTimeout(resolve, delay));

        // Increment attempt counter
        reconnectAttempt++;

        try {
            // Attempt to create and start a new XMPP client
            xmpp = createXMPPClient();
            await xmpp.start();
            console.log('Reconnection successful!');
        } catch (err) {
            // If restart fails, log and try again
            log(`Reconnection attempt failed: ${err.message}`);
            console.error(`Reconnection attempt ${reconnectAttempt} failed:`, err.message);
            handleReconnect();
        }
    }



    // Create initial XMPP client
    var xmpp = createXMPPClient();

    // Event listener for online event
    xmpp.on('online', (address) => {
        // Reset reconnection counter on successful connection
        reconnectAttempt = 0;

        // Log connection
        log(`Connected to XMPP server as ${address}`);
        console.log('Connected to XMPP server successfully.');

        // Join the NWWS chat room
        try {
            xmpp.send(
                xml('presence', { to: 'nwws@conference.nwws-oi.weather.gov/Warnverlay' })
            );
        } catch (err) {
            // If there is an error joining, log and try again
            log(`Error joining NWWS room: ${err.message}`);
            handleReconnect();
        }
    });

    // Load allowed alerts at startup
const allowedAlertsPath = path.join(__dirname, 'allowedalerts.json');
let allowedAlerts = [];
try {
    allowedAlerts = JSON.parse(fs.readFileSync(allowedAlertsPath, 'utf8'));
} catch (e) {
    console.error('Could not load allowedalerts.json:', e);
    allowedAlerts = [];
}

// Event listener for incoming stanzas (messages)
    xmpp.on('stanza', (stanza) => {


        // Ignore non-message stanzas (specifically presence notifications)
        if (!stanza.is('message')) { console.log("Ignoring non-message stanza."); return; }

        // The chat room sends this warning when a user joins, safely ignore it
        if (stanza.toString().includes("**WARNING**WARNING**WARNING**WARNING")) { console.log("Ignoring non-message stanza."); return; }

        // Turn the XML to JSON because I hate XML
        var xml = stanza.toString();
        var parser = new xml2js.Parser();

        // Message processing
        parser.parseString(xml, async (err, result) => {
            // capture coordinates extracted from CAP XML (if any)
            let capCoordinates = null;
            // values extracted from non-VTEC CAP XML (used only for the minimal cleanup path)
            // - capSent / capExpires: ISO timestamps from <sent> / <expires>
            // - capIdentifier: alert <identifier> (used as fallback id / eventTrackingNumber)
            // - capNwsHeadline: parameter NWSheadline (preferred headline for non-VTEC cleanup)
            let capSent = null;
            let capExpires = null;
            let capIdentifier = null;
            let capNwsHeadline = null;

            // If there is any error parsing, log and ignore
            if (err) {
                log('Error parsing XML message:', err);
                console.error('Error parsing XML, message will not be processed:', err);
                return;
            } else if (!result || !result.message || !result.message.body || !Array.isArray(result.message.body)) {
                console.error('Invalid XML message structure:', result);
                log('Invalid XML message structure, message will not be processed. See console output for details.');
                return;
            }

            // Extract the message body
            var body = result.message.body[0];
            if (body === undefined || body === null) {
                console.error('Message body is empty, ignoring.');
                log('XML message body is empty, ignoring.');
                return;
            }

            // Extract raw text content
            var rawText = result.message.x[0]._;
            // Only do basic escaping cleanup early — preserve preamble structure
            rawText = rawText.replace(/\\r\\n/g, '\n').replace(/\\n/g, '\n');

            // Helper: parse a human-readable timestamp from the message text and return an ISO UTC string.
            // Matches examples like "1037 PM PST Fri Feb 13 2026" or "9:28 PM MST Fri Feb 13 2026".
            function parseHumanTimestampFromText(text) {
                if (!text || typeof text !== 'string') return null;
                const re = /\b(\d{3,4}|\d{1,2}:\d{2})\s*(AM|PM)\s*([A-Za-z]{2,4})\s*(?:Mon|Tue|Wed|Thu|Fri|Sat|Sun)\s+([A-Za-z]{3})\s+(\d{1,2})\s+(\d{4})\b/i;
                const m = text.match(re);
                if (!m) return null;
                let timeStr = m[1];
                const ampm = m[2].toUpperCase();
                const tz = m[3].toUpperCase();
                const monthStrRaw = m[4];
                const day = parseInt(m[5], 10);
                const year = parseInt(m[6], 10);

                // parse hour/minute
                let hour = 0, minute = 0;
                if (timeStr.includes(':')) {
                    const parts = timeStr.split(':');
                    hour = parseInt(parts[0], 10);
                    minute = parseInt(parts[1], 10);
                } else {
                    if (timeStr.length === 3) {
                        hour = parseInt(timeStr.slice(0, 1), 10);
                        minute = parseInt(timeStr.slice(1), 10);
                    } else {
                        hour = parseInt(timeStr.slice(0, 2), 10);
                        minute = parseInt(timeStr.slice(2), 10);
                    }
                }
                if (ampm === 'PM' && hour !== 12) hour += 12;
                if (ampm === 'AM' && hour === 12) hour = 0;

                const monthStr = monthStrRaw.charAt(0).toUpperCase() + monthStrRaw.slice(1).toLowerCase();
                const months = { Jan:0, Feb:1, Mar:2, Apr:3, May:4, Jun:5, Jul:6, Aug:7, Sep:8, Oct:9, Nov:10, Dec:11 };
                const month = months[monthStr];
                if (month === undefined) return null;

                const tzOffsets = { PST:-8, PDT:-7, MST:-7, MDT:-6, CST:-6, CDT:-5, EST:-5, EDT:-4, AKST:-9, AKDT:-8, HST:-10, GMT:0, UTC:0 };
                const tzOffset = tzOffsets[tz] !== undefined ? tzOffsets[tz] : null;
                if (tzOffset === null) return null;

                // local time -> UTC: utc = local - tzOffset
                const localMillis = Date.UTC(year, month, day, hour, minute);
                const utcMillis = localMillis - (tzOffset * 60 * 60 * 1000);
                return new Date(utcMillis).toISOString();
            }

            // Helper: parse 6-digit WMO/WMO-like header timestamps (DDHHMM) into ISO UTC strings.
            // Examples seen in preambles: "WUUS54 KMEG 270104" -> 27th day at 01:04 UTC
            function sixDigitHeaderToIso(s) {
                if (!s || !/^[0-9]{6}$/.test(s)) return null;
                try {
                    const now = new Date();
                    const day = parseInt(s.slice(0, 2), 10);
                    const hour = parseInt(s.slice(2, 4), 10);
                    const minute = parseInt(s.slice(4, 6), 10);

                    // Build candidate on current UTC month/year
                    let cand = new Date(Date.UTC(now.getUTCFullYear(), now.getUTCMonth(), day, hour, minute));

                    // If candidate is >16 days away from now, assume month roll-over and adjust by +/-1 month
                    const diff = cand.getTime() - now.getTime();
                    const sixteenDays = 16 * 24 * 60 * 60 * 1000;
                    if (Math.abs(diff) > sixteenDays) {
                        if (diff > 0) {
                            // candidate too far in future -> likely previous month
                            cand = new Date(Date.UTC(now.getUTCFullYear(), now.getUTCMonth() - 1, day, hour, minute));
                        } else {
                            // candidate too far in past -> likely next month
                            cand = new Date(Date.UTC(now.getUTCFullYear(), now.getUTCMonth() + 1, day, hour, minute));
                        }
                    }
                    return new Date(cand.getTime()).toISOString();
                } catch (e) {
                    return null;
                }
            }

            // Extract any 6-digit tokens often embedded in WMO/AWIPS headers or UGC timestamps.
            // Prefer the first as the issuing timestamp and the second as the expiry timestamp when present.
            let headerStartIso = null;
            let headerEndIso = null;
            try {
                const sixMatches = (String(rawText || '').match(/\b(\d{6})\b/g) || []).map(s => String(s));
                if (sixMatches.length >= 1) headerStartIso = sixDigitHeaderToIso(sixMatches[0]);
                if (sixMatches.length >= 2) headerEndIso = sixDigitHeaderToIso(sixMatches[1]);
            } catch (e) { /* ignore */ }


            // ===================== FULL MESSAGE FORMAT DETECTION ===========================
            // If the message contains any of the keywords, skip CAP XML cleanup.
            // Keywords: URGENT, STATEMENT, MESSAGE, REQUEST, BULLETIN (case-insensitive)
            const fullMsgKeywords = /\b(URGENT|STATEMENT|MESSAGE|REQUEST|BULLETIN)\b/i;
            const isFullMessage = fullMsgKeywords.test(rawText);

            let cleanedCAPXML = false;
            // set when we perform the non‑VTEC "minimal cleanup" from a CAP payload —
            // used to prevent splitting and other full-message behaviors
            let capMinimalCleanup = false;
            if (!isFullMessage) {
                // ===================== CAP XML CLEANUP ===========================
                // If the message contains a CAP XML payload, clean it up as requested
                const capMatch = rawText.match(/<\?xml[\s\S]*?<alert[\s\S]*?<\/alert>/);
                if (capMatch) {
                    cleanedCAPXML = true;
                    const capXml = capMatch[0];
                    const capParser = new xml2js.Parser({ explicitArray: false, mergeAttrs: true });
                    capParser.parseString(capXml, (capErr, capObj) => {
                        if (capErr || !capObj || !capObj.alert) {
                            // If parsing fails, fallback to original message
                            return;
                        }
                        const alert = capObj.alert;
                        const info = Array.isArray(alert.info) ? alert.info[0] : alert.info;

                        // Helper to get parameter by valueName
                        function getParam(name) {
                            if (!info.parameter) return '';
                            const params = Array.isArray(info.parameter) ? info.parameter : [info.parameter];
                            const found = params.find(p => p.valueName && p.valueName.toUpperCase() === name.toUpperCase());
                            return found ? found.value : '';
                        }

                        // Helper to get geocode by valueName
                        function getGeocode(name) {
                            if (!info.area || !info.area.geocode) return '';
                            const geos = Array.isArray(info.area.geocode) ? info.area.geocode : [info.area.geocode];
                            const found = geos.find(g => g.valueName && g.valueName.toUpperCase() === name.toUpperCase());
                            return found ? found.value : '';
                        }

                        // Format sent time
                        function formatSentTime(sent) {
                            if (!sent) return '';
                            try {
                                const d = new Date(sent);
                                // Example: 144 PM CST Sat Jan 31 2026
                                const options = { weekday: 'short', year: 'numeric', month: 'short', day: '2-digit' };
                                let hours = d.getHours();
                                let mins = d.getMinutes();
                                let ampm = hours >= 12 ? 'PM' : 'AM';
                                let hour12 = hours % 12 || 12;
                                let tz = sent.includes('-06:00') ? 'CST' : sent.includes('-05:00') ? 'EST' : 'UTC';
                                return `${hour12}${mins.toString().padStart(2, '0')} ${ampm} ${tz} ${d.toLocaleDateString('en-US', options).replace(/,/g, '')}`;
                            } catch {
                                return sent;
                            }
                        }

                        // Replace areaDesc and UGC with provided values
                        const areaDesc = `Lake Pontchartrain and Lake Maurepas-Mississippi Sound-
Lake Borgne-Chandeleur Sound-Breton Sound-
Coastal Waters from Port Fourchon LA to Lower Atchafalaya River
LA out 20 nm-
Coastal waters from the Southwest Pass of the Mississippi River
to Port Fourchon Louisiana out 20 NM-
Coastal Waters from Boothville LA to Southwest Pass of the
Mississippi River out 20 nm-
Coastal waters from Pascagoula Mississippi to Stake Island out
20 NM-
Coastal waters from Port Fourchon Louisiana to Lower Atchafalaya
River LA from 20 to 60 NM-
Coastal waters from Southwest Pass of the Mississippi River to
Port Fourchon Louisiana from 20 to 60 NM-
Coastal Waters from Stake Island LA to Southwest Pass of the
Mississippi River from 20 to 60 nm-
Coastal waters from Pascagoula Mississippi to Stake Island
Louisiana out 20 to 60 NM-`;

                        const ugc = `GMZ530-532-534-536-538-550-552-555-557-570-572-575-577-010945-`;

                        // Clean senderName
                        let sender = info.senderName || '';
                        sender = sender.replace(/^NWS\s*/i, 'National Weather Service ');

                        // Compose output in requested order
                        let cleanedMsg = '';
                        cleanedMsg += sender ? sender + '\n' : '';
                        cleanedMsg += ugc ? ugc + '\n' : '';
                        cleanedMsg += getParam('VTEC') ? getParam('VTEC') + '\n\n' : '';
                        cleanedMsg += areaDesc ? areaDesc + '\n' : '';
                        cleanedMsg += alert.sent ? formatSentTime(alert.sent) + '\n' : '';
                        // prefer to preserve NWSheadline in `headline` (do NOT duplicate into the message)
                        const _nwsHeadline = getParam('NWSheadline') || '';
                        if (_nwsHeadline) capNwsHeadline = _nwsHeadline;
                        cleanedMsg += info.description ? info.description + '\n' : '';
                        cleanedMsg += info.instruction ? info.instruction + '\n' : '';

                        // --- Try to preserve LAT...LON / coordinates from CAP for non-VTEC minimal cleanup ---
                        try {
                            function decToUgcpair(lat, lon) {
                                const la = Math.round(Math.abs(Number(lat)) * 100);
                                const lo = Math.round(Math.abs(Number(lon)) * 100);
                                return `${String(la).padStart(4, '0')} ${String(lo).padStart(4, '0')}`;
                            }
                            function ugcPairToCoord(pair) {
                                const parts = pair.trim().split(/\s+/);
                                const lat = parseFloat(parts[0].slice(0,2) + '.' + parts[0].slice(2));
                                const lon = -parseFloat(parts[1].slice(0,2) + '.' + parts[1].slice(2));
                                return [lat, lon];
                            }

                            let earlyPairs = [];

                            // 1) polygon points in info.area.polygon
                            if (info.area) {
                                const areas = Array.isArray(info.area) ? info.area : [info.area];
                                for (const a of areas) {
                                    const poly = a && (a.polygon || a.Polygon);
                                    if (!poly) continue;
                                    const pts = String(poly).trim().split(/\s+/);
                                    for (const pt of pts) {
                                        const m = pt.match(/^(-?\d{1,2}\.\d+),(-?\d{1,3}\.\d+)$/);
                                        if (m) earlyPairs.push(decToUgcpair(m[1], m[2]));
                                    }
                                }
                            }

                            // 2) decimal lat,lon anywhere in capXml
                            const decPairRe = /(-?\d{1,2}\.\d+)[,\s]+(-?\d{1,3}\.\d+)/g;
                            let _m;
                            while ((_m = decPairRe.exec(capXml)) !== null) {
                                earlyPairs.push(decToUgcpair(_m[1], _m[2]));
                            }

                            // 3) explicit LAT...LON line in CAP XML
                            const latLonRegex = /LAT\.\.\.LON\s+([0-9\s\-]+)/i;
                            const latLonMatch = capXml.match(latLonRegex);
                            if (latLonMatch && latLonMatch[1]) {
                                const groups = latLonMatch[1].replace(/[^0-9\s]/g, ' ').trim().split(/\s+/).filter(g => /^\d{4}$/.test(g));
                                for (const g of groups) earlyPairs.push(g);
                            }

                            earlyPairs = Array.from(new Set(earlyPairs)).filter(g => /^\d{4}\s+\d{4}$/.test(g));
                            if (earlyPairs.length > 0) {
                                // append LAT...LON to the cleaned minimal message
                                cleanedMsg += 'LAT...LON ' + earlyPairs.join(' ') + '\n';
                                // populate capCoordinates so later logic can attach `coordinates`
                                capCoordinates = earlyPairs.map(ugcPairToCoord).filter(Boolean);
                            }
                        } catch (e) {
                            // ignore errors extracting coordinates here
                        }

                        // Prepend any original preamble (e.g., 194\n\nXOUS54 KWBC 311944\n\nCAPLIX\n\n)
                        const preambleMatch = rawText.match(/^[\s\S]*?(?=<\?xml)/);
                        let finalMsg = (preambleMatch ? preambleMatch[0] : '') + cleanedMsg;

                        // Normalize paragraphs (preserve paragraph breaks; join wrapped lines)
                        finalMsg = normalizeParagraphs(finalMsg);
                        if (capNwsHeadline) {
                            // collapse any remaining newlines in the headline so it renders as a single line
                            capNwsHeadline = capNwsHeadline.replace(/\r?\n+/g, ' ').trim();

                            // remove leading occurrence of the headline from the message body
                            const re = new RegExp('^' + capNwsHeadline.replace(/[.*+?^${}()|[\\]\\]/g, '\\$&') + '\\s*\\n?', 'i');
                            if (/\/O\..*?\/\n?/.test(rawText) || /<parameter>\s*<valueName>VTEC<\/valueName>/i.test(rawText)) finalMsg = finalMsg.replace(re, '').trim();
                        }

                        // Replace message in parsedAlert/message
                        rawText = finalMsg;
                    });
                    // Normalize the full rawText after CAP cleanup to convert escape sequences and clean structure
                    rawText = formatMessageNewlines(rawText);
                }
                // ===================== END CAP XML CLEANUP ===========================
            }

            // ================================================================================
            // VTEC parser
            // https://www.weather.gov/bmx/vtec

            let thisObject = {};
            let vtec = null;
            let vtecObjects = [];
            try {
                vtec = rawText.match(/\/O\..*?\/\n?/);
                if (!vtec) {
                    vtec = rawText.match(/<parameter>\s*<valueName>VTEC<\/valueName>\s*<value>(.*?)<\/value>\s*<\/parameter>/);
                    if (vtec && vtec[1]) vtec = vtec[1];
                }
                if (!vtec) throw new Error('No VTEC found');
                vtecObjects = (typeof vtec === 'string' ? vtec : vtec[0]).split('.');
                function vtecToIso(ts) {
                    if (!ts || typeof ts !== 'string') return null;
                    const m = ts.match(/(\d{2})(\d{2})(\d{2})T(\d{2})(\d{2})Z/);
                    if (!m) return null;
                    const yy = parseInt(m[1], 10);
                    const year = 2000 + yy;
                    const month = parseInt(m[2], 10) - 1;
                    const day = parseInt(m[3], 10);
                    const hour = parseInt(m[4], 10);
                    const minute = parseInt(m[5], 10);
                    return new Date(Date.UTC(year, month, day, hour, minute)).toISOString();
                }
                thisObject = {
                    product: vtecObjects[0],
                    action: vtecObjects[1],
                    office: vtecObjects[2],
                    phenomena: vtecObjects[3],
                    significance: vtecObjects[4],
                    eventTrackingNumber: vtecObjects[5],
                    startTime: (headerStartIso || parseHumanTimestampFromText(rawText) || vtecToIso(vtecObjects[6].split('-')[0])),
                    endTime: (headerEndIso || vtecToIso(vtecObjects[6].split('-')[1]))
                }
            } catch (err) {
                // No VTEC, allow fallback to event-based logic
                thisObject = {};
            }

            // --- Remove alerts that have both VTEC and cleaned CAP XML ---
            if (
                cleanedCAPXML &&
                thisObject.phenomena &&
                thisObject.significance
            ) {
                // Do not add this alert
                console.log('Alert has both VTEC and cleaned CAP XML, skipping.');
                return;
            }

            // --- Remove alerts whose message is just the entire XML code ---
            // If the message is just a CAP XML block, skip it
            const isRawXMLOnly = (
                rawText.trim().startsWith('<?xml') &&
                rawText.trim().endsWith('</alert>')
            );
            if (isRawXMLOnly) {
                console.log('Alert message is raw XML only, skipping.');
                return;
            }

            // --- Reject messages that look like embedded/serialized JSON or a full CAP object ---
            // Some sources send the entire CAP object or a JSON-serialized payload inside the message
            // (contains lots of quoted key/value pairs, `properties`, `vtec`, `event_tracking_number`, `urn:oid`, etc.).
            // These should not be added to the public API -- skip them here.
            const jsonLikePairs = (rawText.match(/"\w+"\s*:\s*"/g) || []).length;
            const looksLikeEmbeddedJson = /urn:oid:|"properties"\s*:|"event_tracking_number"|"product_type"|\bvtec\b\s*:|\bstartTime\b/i.test(rawText) || jsonLikePairs >= 3;
            // If the message contains an actual CAP XML block, allow the CAP-cleanup paths to run
            // (do not treat CAP XML as "embedded JSON"). This ensures non-VTEC CAP XML gets the
            // minimal cleanup instead of being skipped entirely.
            const capXmlPresent = /<\?xml[\s\S]*?<alert[\s\S]*?<\/alert>/.test(rawText);
            if (looksLikeEmbeddedJson && !capXmlPresent) {
                console.log('Alert message appears to be embedded/serialized CAP/JSON — skipping.');
                log('Skipped message that appears to be embedded/serialized CAP/JSON.');
                return;
            }

            // --- Allow alerts with missing or undefined action ---
            if (!thisObject.action || thisObject.action === 'undefined') {
                console.log('Alert has no action or action is undefined, allowing it.');
                thisObject.action = 'default'; // Assign a default action if needed
            }

            // --- Allow alerts with missing VTEC/phenomena/significance if event is allowed ---
            let allowByEvent = false;
            let eventName = null;
            if (!thisObject.phenomena || !thisObject.significance) {
                // 1) Try to extract <event>...</event> from XML
                let eventMatch = rawText.match(/<event>(.*?)<\/event>/i);
                if (eventMatch && eventMatch[1]) {
                    eventName = eventMatch[1].trim();
                }

                // 2) If not found, try to detect a preamble pattern where an AWIPS/product
                //    code (e.g. "SPSMPX") appears on its own line followed by a blank
                //    line and then the human-readable headline. If that headline matches
                //    an entry in `allowedalerts.json`, treat it as the event.
                if (!eventName) {
                    try {
                        const preambleMatch = rawText.match(/^([\s\S]*?)(?=<\?xml|$)/);
                        if (preambleMatch && preambleMatch[1]) {
                            const preamble = preambleMatch[1];
                            const lines = preamble.split(/\r?\n/).map(l => l.trim()).filter(Boolean);
                            for (let i = 0; i < lines.length; i++) {
                                // Look for a product code line followed by a headline line
                                if (/^[A-Z]{3,6}$/.test(lines[i])) {
                                    const next = lines[i + 1] || '';
                                    if (next) {
                                        const found = allowedAlerts && Array.isArray(allowedAlerts) && allowedAlerts.find(a => {
                                            if (!a) return false;
                                            const au = String(a).toUpperCase();
                                            return String(next).toUpperCase() === au || String(next).toUpperCase().includes(au);
                                        });
                                        if (found) { eventName = next.trim(); break; }
                                    }
                                }
                            }
                        }

                        // Fallback: sometimes the product code and headline are inline or the product
                        // code is preceded by an AWIPS/WMO header. Try two regex patterns against
                        // the full rawText to capture: (1) product-code line then headline on next line,
                        // or (2) product-code followed by headline on the same line.
                        if (!eventName) {
                            const m1 = rawText.match(/(?:\n|^)(?:[A-Z]{2,6}\s+)?([A-Z0-9]{3,6})\s*\n\s*([A-Za-z][^\n]{3,200})/);
                            if (m1 && m1[2]) {
                                const candidate = m1[2].trim();
                                const found = Array.isArray(allowedAlerts) && allowedAlerts.find(a => a && String(candidate).toUpperCase() === String(a).toUpperCase() || String(candidate).toUpperCase().includes(String(a).toUpperCase()));
                                if (found) eventName = candidate;
                            }
                        }
                        if (!eventName) {
                            const m2 = rawText.match(/(?:\n|^)(?:[A-Z]{2,6}\s+)?([A-Z0-9]{3,6})\s+([A-Za-z][^\n]{3,200})/);
                            if (m2 && m2[2]) {
                                const candidate = m2[2].trim();
                                const found = Array.isArray(allowedAlerts) && allowedAlerts.find(a => a && String(candidate).toUpperCase() === String(a).toUpperCase() || String(candidate).toUpperCase().includes(String(a).toUpperCase()));
                                if (found) eventName = candidate;
                            }
                        }
                    } catch (e) { /* ignore preamble parse errors */ }
                }

                // 3) If still not found, try to extract from CAP XML if present
                if (!eventName) {
                    const capMatch = rawText.match(/<\?xml[\s\S]*?<alert[\s\S]*?<\/alert>/);
                    if (capMatch) {
                        const capXml = capMatch[0];
                        try {
                            const capParser = new xml2js.Parser({ explicitArray: false, mergeAttrs: true });
                            let capObj = await capParser.parseStringPromise(capXml);
                            if (capObj && capObj.alert && capObj.alert.info && capObj.alert.info.event) {
                                eventName = capObj.alert.info.event;
                            }
                        } catch (e) { /* ignore */ }
                    }
                }

                // If we found an eventName and it's listed in allowedAlerts (case-insensitive), allow by event
                if (eventName && Array.isArray(allowedAlerts) && allowedAlerts.some(a => String(a || '').toUpperCase() === String(eventName).toUpperCase())) {
                    allowByEvent = true;
                }
            }

            // If the alert does NOT have VTEC (no phenomena/significance) but contains CAP XML,
            // perform a minimal cleanup: keep only event, sender, ugc, areaDesc, sent, description,
            // and instruction (only if present). This prevents raw CAP XML from showing up.
            if ((!thisObject.phenomena || !thisObject.significance)) {
                const capMatch2 = rawText.match(/<\?xml[\s\S]*?<alert[\s\S]*?<\/alert>/);
                if (capMatch2) {
                    try {
                        const capXml = capMatch2[0];
                        const capParser = new xml2js.Parser({ explicitArray: false, mergeAttrs: true });
                        const capObj = await capParser.parseStringPromise(capXml);
                        if (capObj && capObj.alert && capObj.alert.info) {
                            const info = Array.isArray(capObj.alert.info) ? capObj.alert.info[0] : capObj.alert.info;

                            function extractText(node) {
                                if (!node) return '';
                                if (typeof node === 'string') return node.trim();
                                if (Array.isArray(node)) return node.map(extractText).join('\n').trim();
                                if (typeof node === 'object') {
                                    if (node._) return String(node._).trim();
                                    if (node['#text']) return String(node['#text']).trim();
                                    return Object.values(node).filter(v => typeof v === 'string' && v.trim()).join(' ').trim();
                                }
                                return '';
                            }

                            // --- Preserve preamble and UGC line ---
                            // Find preamble before CAP XML (e.g., "552\nWWUS83 KLMK 061958\nSPSLMK.")

                            const preambleMatch = rawText.match(/^([\s\S]*?)(?=<\?xml)/);
                            let preamble = preambleMatch ? preambleMatch[1].trim() : '';

                            // Split the preamble/header into individual lines for NWWS-OI format
                            if (preamble) {
                                // Try to match the typical NWWS-OI header pattern: digits, product code, WMO, AWIPS, etc.
                                // Example: "271 XOUS54 KWBC 211952 CAPMOB"
                                const headerRegex = /^(\d{3})\s+([A-Z]{6})\s+([A-Z]{4} \d{6} [A-Z]{6})/;
                                const headerMatch = preamble.match(headerRegex);
                                if (headerMatch) {
                                    // Split header into parts
                                    const headerParts = [headerMatch[1], headerMatch[2], headerMatch[3]];
                                    // Remove header from preamble
                                    preamble = preamble.replace(headerRegex, '').trim();
                                    // If there is any remaining preamble, split by double newlines
                                    let preambleLines = preamble ? preamble.split(/\n{2,}/).map(l => l.trim()).filter(Boolean) : [];
                                    preamble = headerParts.join('\n') + '\n\n' + preambleLines.join('\n');
                                } else {
                                    // Fallback: split by spaces for generic header
                                    preamble = preamble.split(/\s+/).join('\n');
                                }
                            }

                            const event = extractText(info.event);

                            // If the preamble (text before the CAP XML) begins with the same text as the
                            // CAP `NWSheadline` or the `<event>` string, drop that first line so we do
                            // not duplicate the headline inside the `message` for non‑VTEC cleanup.
                            if (preamble) {
                                const lines = preamble.split(/\r?\n/).map(l => l.trim()).filter(Boolean);
                                if (lines.length) {
                                    const first = lines[0];
                                    if ((capNwsHeadline && first.toUpperCase() === capNwsHeadline.toUpperCase()) ||
                                        (event && first.toUpperCase() === event.toUpperCase())) {
                                        lines.shift();
                                        preamble = lines.join('\n').trim();
                                    }
                                }
                            }

                            const senderRaw = extractText(info.senderName || capObj.alert.sender || capObj.alert.senderName);
                            const sender = senderRaw ? senderRaw.replace(/^NWS\s*/i, 'National Weather Service ') : '';

                            // --- Collect and normalize UGCs from any likely source ---
                            function collectUgcTokens(...sources) {
                                const rePair = /([A-Z]{2,3})(\d{3})/g;
                                const map = Object.create(null); // prefix -> Set(numbers)
                                let timestampSuffix = '';

                                for (const src of sources) {
                                    if (!src) continue;
                                    // Preserve possible timestamp like 121900-
                                    const tsMatch = String(src).match(/(\b\d{6}-)\b/);
                                    if (tsMatch) timestampSuffix = tsMatch[1];

                                    let m;
                                    while ((m = rePair.exec(String(src))) !== null) {
                                        const prefix = m[1];
                                        const num = parseInt(m[2], 10);
                                        map[prefix] = map[prefix] || new Set();
                                        map[prefix].add(num);
                                    }
                                }

                                // Build canonical UGC string
                                const prefixes = Object.keys(map).sort();
                                if (prefixes.length === 0) return '';

                                function compressNums(numsArr) {
                                    numsArr.sort((a,b)=>a-b);
                                    const parts = [];
                                    let i = 0;
                                    while (i < numsArr.length) {
                                        let start = numsArr[i];
                                        let j = i;
                                        while (j+1 < numsArr.length && numsArr[j+1] === numsArr[j] + 1) j++;
                                        const len = j - i + 1;
                                        const end = numsArr[j];
                                        if (len === 1) parts.push(String(start).padStart(3,'0'));
                                        else if (len === 2) parts.push(String(start).padStart(3,'0') + '-' + String(end).padStart(3,'0'));
                                        else parts.push(String(start).padStart(3,'0') + '>' + String(end).padStart(3,'0'));
                                        i = j + 1;
                                    }
                                    return parts.join('-');
                                }

                                const out = [];
                                for (const p of prefixes) {
                                    const nums = Array.from(map[p]);
                                    const compressed = compressNums(nums);
                                    if (compressed) out.push(p + compressed);
                                }

                                let result = out.join('-');
                                if (timestampSuffix && !result.endsWith('-')) result += '-';
                                if (timestampSuffix) result += timestampSuffix + '\n';
                                // Ensure trailing hyphen
                                if (!result.endsWith('-')) result += '-';
                                return result;
                            }

                            // Gather candidate sources for UGC tokens
                            const ugcCandidates = [];
                            if (info.parameter) {
                                const params = Array.isArray(info.parameter) ? info.parameter : [info.parameter];
                                const found = params.find(p => p.valueName && p.valueName.toUpperCase() === 'UGC');
                                if (found) ugcCandidates.push(extractText(found.value));
                            }
                            if (info.ugc) ugcCandidates.push(extractText(info.ugc));
                            if (info.area) {
                                const areas = Array.isArray(info.area) ? info.area : [info.area];
                                for (const a of areas) {
                                    if (!a) continue;
                                    if (a.geocode) {
                                        const geos = Array.isArray(a.geocode) ? a.geocode : [a.geocode];
                                        for (const g of geos) {
                                            if (g && g.value) ugcCandidates.push(extractText(g.value));
                                        }
                                    }
                                    if (a.areaDesc) ugcCandidates.push(extractText(a.areaDesc));
                                }
                            }
                            if (preamble) ugcCandidates.push(preamble);
                            if (rawText) ugcCandidates.push(rawText);

                            const ugcLine = collectUgcTokens(...ugcCandidates);

                            // Clean areaDesc: replace semicolons/commas/newlines with hyphens and ensure trailing '-'
                            let areaDesc = extractText(info.area && info.area.areaDesc);
                            if (areaDesc) {
                                areaDesc = areaDesc.replace(/[;,]/g, '-').replace(/\s*\n\s*/g, '-').replace(/\s+/g, ' ').trim();
                                areaDesc = areaDesc.replace(/-+/g, '-').replace(/^[-\s]+|[-\s]+$/g, '');
                                if (areaDesc.length) areaDesc = areaDesc + '-';
                            }

                            const sent = extractText(capObj.alert.sent);
                            let description = extractText(info.description);
                            const instruction = extractText(info.instruction);

                            // --- Capture CAP metadata for non-VTEC minimal-cleanup and populate fallbacks ---
                            try {
                                if (capObj && capObj.alert) {
                                    // identifier -> use as fallback id / eventTrackingNumber
                                    if (capObj.alert.identifier) capIdentifier = String(capObj.alert.identifier).trim();

                                    // sent -> canonical ISO used for issued / startTime
                                    if (capObj.alert.sent) {
                                        try { capSent = new Date(String(capObj.alert.sent)).toISOString(); } catch (e) { capSent = null; }
                                        if (!thisObject.startTime) thisObject.startTime = capSent;
                                    }

                                    // expires -> canonical ISO used for expiry / endTime
                                    // CAP <expires> is commonly found under <alert> or inside the first <info> block —
                                    // check both locations so we don't miss it due to tag placement or casing.
                                    let _capExpiresSrc = null;
                                    if (capObj.alert.expires) {
                                        _capExpiresSrc = capObj.alert.expires;
                                    } else if (capObj.alert.info) {
                                        const _info = Array.isArray(capObj.alert.info) ? capObj.alert.info[0] : capObj.alert.info;
                                        if (_info && _info.expires) _capExpiresSrc = _info.expires;
                                    }
                                    if (_capExpiresSrc) {
                                        try { capExpires = new Date(String(_capExpiresSrc)).toISOString(); } catch (e) { capExpires = null; }
                                        if (!thisObject.endTime) thisObject.endTime = capExpires;
                                    }

                                    // prefer NWSheadline parameter for headline when present
                                    if (info.parameter) {
                                        const params = Array.isArray(info.parameter) ? info.parameter : [info.parameter];
                                        const nh = params.find(p => p.valueName && String(p.valueName).toUpperCase() === 'NWSHEADLINE');
                                        if (nh) {
                                        capNwsHeadline = extractText(nh.value);
                                        // headline parameters often contain stray newlines; collapse them and trim
                                        capNwsHeadline = capNwsHeadline.replace(/\r?\n+/g, ' ').trim();
                                    }
                                    }

                                    // populate eventTrackingNumber fallback from CAP identifier or info/eventTrackingNumber param
                                    let capEventTrack = null;
                                    if (info.eventTrackingNumber) capEventTrack = extractText(info.eventTrackingNumber);
                                    if (!capEventTrack && info.parameter) {
                                        const params2 = Array.isArray(info.parameter) ? info.parameter : [info.parameter];
                                        const et = params2.find(p => p.valueName && /EVENTTRACKINGNUMBER/i.test(p.valueName));
                                        if (et) capEventTrack = extractText(et.value);
                                    }
                                    if (!thisObject.eventTrackingNumber) thisObject.eventTrackingNumber = capEventTrack || capIdentifier || '';
                                }
                            } catch (e) { /* ignore CAP metadata extraction errors */ }

                            // For non-VTEC minimal-cleanup prefer the CAP <event> as the alert `name`
                            if (event && event.length) {
                                alertName = event;
                            }

                            // Do NOT prepend NWSheadline into `description` here —
                            // the CAP `NWSheadline` will be inserted into the cleaned
                            // `message` parts (immediately before `description`).

                            // --- Format sent time as requested ---
                            function formatIssuedTime(sent) {
                                if (!sent) return '';
                                try {
                                    const d = new Date(sent);
                                    let hours = d.getHours();
                                    let mins = d.getMinutes();
                                    let ampm = hours >= 12 ? 'PM' : 'AM';
                                    let hour12 = hours % 12 || 12;
                                    let tz = '';
                                    const isDST = d.getMonth() >= 2 && d.getMonth() <= 10;
                                    if (sent.includes('-05:00')) tz = isDST ? 'EDT' : 'EST';
                                    else if (sent.includes('-06:00')) tz = isDST ? 'CDT' : 'CST';
                                    else if (sent.includes('-07:00')) tz = isDST ? 'MDT' : 'MST';
                                    else if (sent.includes('-08:00')) tz = isDST ? 'PDT' : 'PST';
                                    else if (sent.includes('-09:00')) tz = isDST ? 'AKDT' : 'AKST';
                                    else if (sent.includes('-10:00')) tz = isDST ? 'HDT' : 'HST';
                                    else if (sent.includes('-04:00')) tz = isDST ? 'ADT' : 'AST';
                                    else tz = 'UTC';
                                    const dateStr = d.toLocaleDateString('en-US', { weekday: 'short', year: 'numeric', month: 'short', day: '2-digit' }).replace(/,/g, '');
                                    return `${hour12}${mins.toString().padStart(2, '0')} ${ampm} ${tz}, ${dateStr}`;
                                } catch {
                                    return sent;
                                }
                            }
 // --- Reorder and build minimalParts per user spec:
                            // preamble (if any) -> event -> sender -> issued -> UGC -> areaDesc -> NWSheadline -> description -> instruction
                            let minimalParts = [];
                            if (preamble) minimalParts.push(formatMessageNewlines(preamble));
                            if (event) minimalParts.push(formatMessageNewlines(event));
                            if (sender) minimalParts.push(formatMessageNewlines(sender));
                            if (sent) minimalParts.push(formatMessageNewlines(formatIssuedTime(sent)));
                            if (ugcLine) minimalParts.push(formatMessageNewlines(ugcLine));
                            if (areaDesc) minimalParts.push(formatMessageNewlines(areaDesc));
                            if (capNwsHeadline) minimalParts.push(formatMessageNewlines(capNwsHeadline));
                            if (description) minimalParts.push(formatMessageNewlines(description));
                            if (instruction) minimalParts.push(formatMessageNewlines(instruction));

                            // --- START: Extract coordinates (LAT...LON) and Event Motion for message ---
                            function decToUgcpair(lat, lon) {
                                const la = Math.round(Math.abs(Number(lat)) * 100);
                                const lo = Math.round(Math.abs(Number(lon)) * 100);
                                return `${String(la).padStart(4, '0')} ${String(lo).padStart(4, '0')}`;
                            }
                            let latLonPairs = [];
                            try {
                                let groups = [];
                                // 1) Try CAP <area><polygon>
                                if (info && info.area) {
                                    const areas = Array.isArray(info.area) ? info.area : [info.area];
                                    for (const a of areas) {
                                        const poly = a && (a.polygon || a.Polygon);
                                        if (!poly) continue;
                                        const pts = String(poly).trim().split(/\s+/);
                                        for (const pt of pts) {
                                            const m = pt.match(/^(-?\d{1,2}\.\d+),(-?\d{1,3}\.\d+)$/);
                                            if (m) groups.push(decToUgcpair(m[1], m[2]));
                                        }
                                    }
                                }
                                // 2) Fallback: scan CAP XML for decimal lat,lon pairs anywhere
                                if (groups.length < 1 && capXml) {
                                    const decPairRe = /(-?\d{1,2}\.\d+)[,\s]+(-?\d{1,3}\.\d+)/g;
                                    let m;
                                    while ((m = decPairRe.exec(capXml)) !== null) {
                                        groups.push(decToUgcpair(m[1], m[2]));
                                    }
                                }
                                // 3) Fallback: scan rawText for decimal lat,lon pairs
                                if (groups.length < 1 && rawText) {
                                    const decPairRe = /(-?\d{1,2}\.\d+)[,\s]+(-?\d{1,3}\.\d+)/g;
                                    let m;
                                    while ((m = decPairRe.exec(rawText)) !== null) {
                                        groups.push(decToUgcpair(m[1], m[2]));
                                    }
                                }
                                // 4) Fallback: look for explicit LAT...LON line in CAP or raw text
                                if (groups.length < 1) {
                                    const latLonRegex = /LAT\.\.\.LON\s+([0-9\s\-]+)/i;
                                    const latLonSource = (capXml && capXml.match(latLonRegex)) ? capXml : rawText;
                                    const latLonMatch = latLonSource.match(latLonRegex);
                                    if (latLonMatch && latLonMatch[1]) {
                                        groups = latLonMatch[1].replace(/[^0-9\s]/g, ' ').trim().split(/\s+/).filter(g => /^\d{4}$/.test(g));
                                    }
                                }
                                // Deduplicate and validate 4-digit pairs
                                latLonPairs = Array.from(new Set(groups)).filter(g => /^\d{4}\s+\d{4}$/.test(g));
                                // Convert UGC-style pairs back to numeric [lat, lon] and store for later use
                                if (latLonPairs.length > 0) {
                                    function ugcPairToCoord(pair) {
                                        const parts = pair.trim().split(/\s+/);
                                        // lat 4-digit -> insert decimal after 2 digits, lon 4-digit -> insert decimal after 2 digits, assume west negative
                                        const lat = parseFloat(parts[0].slice(0,2) + '.' + parts[0].slice(2));
                                        const lon = -parseFloat(parts[1].slice(0,2) + '.' + parts[1].slice(2));
                                        return [lat, lon];
                                    }
                                    capCoordinates = latLonPairs.map(ugcPairToCoord).filter(Boolean);
                                }
                            } catch (e) {
                                 // ignore extraction errors
                             }
                            // --- Insert LAT...LON line FIRST ---
                            if (latLonPairs.length > 0) {
                                minimalParts.push('LAT...LON ' + latLonPairs.join(' '));
                            }                            
                            // Extract Event Motion Description from parameters or known fields
                            try {
                                let eventMotion = '';
                                if (info.parameter) {
                                    const params = Array.isArray(info.parameter) ? info.parameter : [info.parameter];
                                    const found = params.find(p => p.valueName && /event\s?motion|eventmotion|eventmotiondescription/i.test(p.valueName));
                                    if (found) eventMotion = (typeof found.value === 'string') ? found.value : (found.value && found.value._) || '';
                                }
                                if (!eventMotion && info.eventMotionDescription) {
                                    eventMotion = info.eventMotionDescription;
                                }

                                // --- CAP parameter extraction helpers ---
                                function getCapParam(name) {
                                    if (!info.parameter) return undefined;
                                    const params = Array.isArray(info.parameter) ? info.parameter : [info.parameter];
                                    const found = params.find(p => p.valueName && p.valueName.toUpperCase() === name.toUpperCase());
                                    return found ? found.value : undefined;
                                }

                                // --- Waterspout Detection ---
                                let waterspoutDetection = getCapParam('waterspoutDetection');
                                let waterspoutLine = '';
                                if (waterspoutDetection && String(waterspoutDetection).toLowerCase().includes('possible')) {
                                    waterspoutLine = 'WATERSPOUT...POSSIBLE';
                                }

                                // --- Max Hail Size ---
                                let maxHailSize = getCapParam('maxHailSize');
                                let maxHailLine = '';
                                if (maxHailSize !== undefined) {
                                    let hailVal = parseFloat(maxHailSize);
                                    if (!isNaN(hailVal)) {
                                        if (hailVal === 0.75) {
                                            maxHailLine = 'MAX HAIL SIZE...<.75';
                                        } else {
                                            maxHailLine = `MAX HAIL SIZE...${hailVal.toFixed(2)}`;
                                        }
                                    }
                                }

                                // --- Max Wind Gust ---
                                let maxWindGust = getCapParam('maxWindGust');
                                let maxWindLine = '';
                                if (maxWindGust !== undefined) {
                                    let windVal = parseFloat(maxWindGust);
                                    if (!isNaN(windVal)) {
                                        maxWindLine = `MAX WIND GUST...${windVal}`;
                                    }
                                }

                                // --- Event Motion ---
                                function isoToZuluHhmm(iso) {
                                    try {
                                        const d = new Date(iso);
                                        if (isNaN(d.getTime())) return null;
                                        const hh = String(d.getUTCHours()).padStart(2, '0');
                                        const mm = String(d.getUTCMinutes()).padStart(2, '0');
                                        return `${hh}${mm}Z`;
                                    } catch {
                                        return null;
                                    }
                                }

                                function extractCoords(txt) {
                                    const coords = [];
                                    const decPairRe = /(-?\d{1,2}\.\d+)[,\s]+(-?\d{1,3}\.\d+)/g;
                                    let m;
                                    while ((m = decPairRe.exec(txt)) !== null) {
                                        coords.push(decToUgcpair(m[1], m[2]));
                                    }
                                    const ugc4Re = /\b(\d{4})\s+(\d{4})\b/g;
                                    while ((m = ugc4Re.exec(txt)) !== null) {
                                        coords.push(`${m[1]} ${m[2]}`);
                                    }
                                    return coords;
                                }

                                const txt = String(eventMotion);
                                let time = null;
                                const isoMatch = txt.match(/\d{4}-\d{2}-\d{2}T\d{2}:\d{2}:\d{2}(?:Z|[+\-]\d{2}:\d{2})?/);
                                if (isoMatch) time = isoToZuluHhmm(isoMatch[0]);
                                if (!time) {
                                    const zMatch = txt.match(/\b(\d{3,4}Z)\b/);
                                    if (zMatch) time = zMatch[1];
                                }

                                const degMatch = txt.match(/(\d{1,3})\s*DEG/i);
                                const ktMatch = txt.match(/(\d{1,3})\s*KT/i);
                                let motion = null;
                                if (degMatch || ktMatch) {
                                    motion = `${degMatch ? degMatch[1] + 'DEG' : ''}${degMatch && ktMatch ? ' ' : ''}${ktMatch ? ktMatch[1] + 'KT' : ''}`.trim();
                                }

                                const coords = extractCoords(txt);

                                // Compose cleaned TIME...MOT...LOC string
                                const parts = [];
                                if (time) parts.push(time);
                                if (motion) parts.push(motion);
                                if (coords.length) parts.push(...coords);
                                const cleaned = parts.join(' ');
                                if (cleaned.length) {
                                    minimalParts.push('TIME...MOT...LOC ' + cleaned + '\n\n');
                                }
                                // Insert waterspout, hail, wind lines in order if present
                                if (waterspoutLine) minimalParts.push(waterspoutLine);
                                if (maxHailLine) minimalParts.push(maxHailLine);
                                if (maxWindLine) minimalParts.push(maxWindLine);
                            } catch (e) {
                                // ignore extraction errors
                            }
 // --- END: Extract coordinates and Event Motion ---

                            if (minimalParts.length) {
                                // join parts with double-newlines so that normalizeParagraphs treats them as separate
                                rawText = minimalParts.join('\n\n') + '\n';
                                // normalize newlines (convert escaped sequences and clean structure) first
                                rawText = formatMessageNewlines(rawText);
                                // then normalize paragraphs (preserve paragraph breaks; join wrapped lines)
                                rawText = normalizeParagraphs(rawText);
                                if (capNwsHeadline) {
                                    const re2 = new RegExp('^' + capNwsHeadline.replace(/[.*+?^${}()|[\\]\\]/g, '\\$&') + '\\s*\\n?', 'i');
                                    // keep NWSheadline in rawText for non-VTEC minimal-cleanup (do not strip)
                                }
                                // Mark that we performed a minimal CAP cleanup so these alerts are skipped
                                capMinimalCleanup = true;
                            }
                        }
                    } catch (e) {
                        // If parsing fails, leave rawText as-is (other logic will handle it)
                    }
                }
            }
            
            // If no VTEC and not allowed by event, skip
            // If no VTEC and not allowed by event, check allowedalerts.json
            if (
                (!thisObject.phenomena || !thisObject.significance) &&
                !allowByEvent
            ) {
                // Try to extract event name from rawText
                let eventName = null;
                let eventMatch = rawText && rawText.match(/<event>(.*?)<\/event>/i);
                if (eventMatch) {
                    eventName = eventMatch[1].trim();
                } else {
                    // Fallback: try to match allowed alert names in text
                    if (Array.isArray(allowedAlerts)) {
                        const txt = String(rawText || '').toUpperCase();
                        const matches = allowedAlerts.filter(a => {
                            const au = String(a || '').toUpperCase();
                            return au && txt.includes(au);
                        });
                        if (matches.length) {
                            eventName = matches[0];
                        }
                    }
                }
                // If eventName is allowed, let it through
                if (eventName && Array.isArray(allowedAlerts) && allowedAlerts.some(a => String(a).toUpperCase() === String(eventName).toUpperCase())) {
                    // Let it through
                } else {
                    return;
                }
                // This is a cancellation or expiration, delete the alert from the database
                try {
                    let alerts = [];

                    try {
                        const raw = fs.readFileSync('alerts.json', 'utf8');
                        alerts = raw.trim() ? JSON.parse(raw) : [];
                        if (!Array.isArray(alerts)) alerts = [];
                    } catch (readErr) {
                        // If the file is missing or malformed, nothing to delete
                        if (readErr.code !== 'ENOENT') {
                            console.warn('alerts.json unreadable, cannot delete alert:', readErr.message);
                            log('alerts.json unreadable, cannot delete alert: ' + readErr.message);
                        }
                        alerts = [];
                    }

                    // Find and remove matching alert
                    const alertIndex = alerts.findIndex(alert => 
                        alert.properties &&
                        alert.properties.vtec &&
                        alert.properties.vtec.office === thisObject.office &&
                        alert.properties.vtec.phenomena === thisObject.phenomena &&
                        alert.properties.vtec.significance === thisObject.significance &&
                        alert.properties.vtec.eventTrackingNumber === thisObject.eventTrackingNumber
                    );

                    if (alertIndex !== -1) {
                        const removedAlert = alerts.splice(alertIndex, 1)[0];
                        fs.writeFileSync('alerts.json', JSON.stringify(alerts, null, 2));
                        console.log('Alert cancelled/expired and removed:', removedAlert.name);
                        log('Alert cancelled/expired and removed: ' + removedAlert.name);
                    } else {
                        console.log('No matching alert found to cancel/expire.');
                        log('No matching alert found to cancel/expire.');
                    }
                } catch (err) {
                    console.error('Error updating alerts.json for cancellation/expiration:', err);
                    log('Error updating alerts.json for cancellation/expiration: ' + err);
                }
                return;
            } else if (thisObject.action !== 'UPG' && thisObject.action !== 'COR' && thisObject.action !== 'CON') {
                // Not update, correction, or continuation
                console.log(`Alert action type '${thisObject.action}' - processing as new alert`);
                // Continue to process as new alert
            } else {
                // Update, correction, or continuation
                console.log(`Alert action '${thisObject.action}' detected - update/correction/continuation`);
                // TODO: Implement update/correction logic
                // Preserve coordinates and other data not included with update.
            }

            // Extract alert name
            // Prefer CAP <event> (or CAP NWSheadline when available) since it describes the
            // specific message part — this avoids taking a blanket "BULLETIN" preamble
            // (for example a Watch) when the CAP payload is actually a different event
            // such as "Special Weather Statement".
            var alertNameMatch = rawText.match(/<event>(.*?)<\/event>/i);
            var alertName = alertNameMatch ? alertNameMatch[1].trim() : null;

            // Fallback to BULLETIN preamble if no CAP <event> found
            // Use a more precise pattern to avoid matching generic "WARNING" words
            if (!alertName) {
                // First try to match specific pattern with alert type immediately after BULLETIN
                alertNameMatch = rawText.match(/BULLETIN\s+(?:FOR\s+)?([A-Z][A-Z\s]*?(?:WARNING|WATCH|ADVISORY|STATEMENT|ALERT|EMERGENCY))/i);
                if (!alertNameMatch) {
                    // Fallback to original pattern
                    alertNameMatch = rawText.match(/BULLETIN.*?\s+(.*?)\s+National Weather Service/i);
                }
                alertName = alertNameMatch ? alertNameMatch[1].trim() : null;
            }

            // Final fallback
            if (!alertName) alertName = 'Unknown Alert';

            // If name is generic/unknown, or if allowedAlerts might have a better match, try to infer a better name
            // Rules:
            // - If message contains an allowed alert name (case-insensitive), prefer that.
            // - Do NOT use "Severe Weather Statement" or "Flash Flood Statement" even if present.
            // - "Special Weather Statement" is allowed and will be used if present in allowedalerts.json.
            let shouldCheckAllowed = (!alertName || alertName === 'Unknown Alert');
            if (!shouldCheckAllowed && Array.isArray(allowedAlerts)) {
                // Also check if current alertName is too generic or if allowedAlerts has a better/more specific match
                const txt = String(rawText || '').toUpperCase();
                const au = alertName.toUpperCase();
                // Re-check if current name is just a generic "WARNING" and allowedAlerts has something more specific
                if (/^[A-Z\s]{1,20}WARNING$/.test(au) && allowedAlerts.some(a => txt.includes(String(a || '').toUpperCase()))) {
                    shouldCheckAllowed = true;
                }
            }
            if (shouldCheckAllowed && Array.isArray(allowedAlerts)) {
                const txt = String(rawText || '').toUpperCase();
                const excluded = new Set(['SEVERE WEATHER STATEMENT', 'FLASH FLOOD STATEMENT']);
                const matches = allowedAlerts.filter(a => {
                    const au = String(a || '').toUpperCase();
                    return au && !excluded.has(au) && txt.includes(au);
                });
                if (matches.length) {
                    // Prefer Warning/Watch/Advisory over Statement; otherwise pick longest match
                    function rankName(n) {
                        const u = n.toUpperCase();
                        if (u.includes('WARNING')) return 1;
                        if (u.includes('WATCH')) return 2;
                        if (u.includes('ADVISORY')) return 3;
                        if (u.includes('STATEMENT')) return 4;
                        return 5;
                    }
                    matches.sort((a,b) => {
                        const ra = rankName(a), rb = rankName(b);
                        if (ra !== rb) return ra - rb;
                        return b.length - a.length;
                    });
                    alertName = matches[0];
                }
            }

            console.log(`Processing alert: ${alertName}`);

            // Extract recieved time
            var recievedTime = null;
            try {
                // Try to extract from the result object
                if (result.message.x && result.message.x[0] && result.message.x[0].$ && result.message.x[0].$.issued) {
                    recievedTime = result.message.x[0].$.issued;
                    console.log(`Received time: ${recievedTime}`);
                }
            } catch (err) {
                console.log('Could not extract received time');
            }

            // Extract lat/lon
            var latLonMatch = rawText.match(/LAT\.\.\.LON\s+([\d\s]+)/);
            let coordinates = [];
            var standardCoordinates = [];
 
            if (latLonMatch) {
                var nums = latLonMatch[1].trim().split(/\s+/);
                console.log(`Extracted ${nums.length / 2} coordinate pairs`);
                for (let i = 0; i < nums.length; i += 2) {
                    coordinates.push({
                        lat: parseFloat(nums[i].slice(0, 2) + '.' + nums[i].slice(2)),
                        lon: -parseFloat(nums[i + 1].slice(0, 2) + '.' + nums[i + 1].slice(2)) // Assuming western hemisphere
                    });
                }
 
                // Standardize coordinates to [[lat, lon], ...]
                if (Array.isArray(coordinates)) {
                    standardCoordinates = coordinates
                        .map(item => {
                            // handle already-array form [lat, lon]
                            if (Array.isArray(item) && item.length >= 2) {
                                return [Number(item[0]), Number(item[1])];
                            }
                            // handle object form {lat, lon}
                            if (item && typeof item === 'object' && 'lat' in item && 'lon' in item) {
                                return [Number(item.lat), Number(item.lon)];
                            }
                            return null;
                        })
                        .filter(pair => pair && isFinite(pair[0]) && isFinite(pair[1]));
                }
 
                // Replace original coordinates with standardized form
                coordinates = standardCoordinates;
            } else {
                // No coordinates found
                coordinates = null;
            }
            // If no LAT...LON line was present in rawText, but we captured coords from CAP XML, use them
            if ((!coordinates || coordinates.length === 0) && Array.isArray(capCoordinates) && capCoordinates.length > 0) {
                coordinates = capCoordinates;
             }
            // Do not skip alerts if no coordinates; just omit the property

            // Simple message beautification
            // TODO: filter and parse messages with description and instruction tags

            // Normalize paragraphs while preserving paragraph breaks:
            // - collapse 3+ blank lines to 2
            // - join single-line wraps inside a paragraph into a single line (replace single \n with space)
            // - trim leading/trailing blank lines
            // - additionally collapse *one* extra paragraph break (\n\n -> \n) for specific
            //   known patterns (preamble numbers, preamble codes, UGC lines, VTEC lines,
            //   timestamps, common headlines, and short capitalized name splits like
            //   "San\n\nJoaquin"). These are conservative, pattern-specific fixes.
            function normalizeParagraphs(text) {
                if (!text) return '';
                text = String(text).replace(/\r\n/g, '\n');
                // preserve up to two leading newlines (some preambles expect a double-blank line)
                text = text.replace(/^\n{3,}/, '\n\n');
                // remove leading/trailing spaces but keep newlines
                text = text.replace(/^[ \t]+|[ \t]+$/g, '');
                // collapse 2+ blank lines into 2
                text = text.replace(/\n{2,}/g, '\n\n');
                // split paragraphs on two or more blank lines, join wrapped lines inside each paragraph
                const paras = text.split(/\n{2,}/).map(p => p
                    .replace(/\n+(?=(?:At\s+)?(?:\d{3,4}|\d{1,2}(?::\d{2})?)\s*(?:AM|PM))/gi, '\n')
                    .replace(/\n+/g, ' ')
                    .trim()
                ).filter(Boolean);
                // Re-join paragraphs using a canonical paragraph separator
                let out = paras.join('\n\n');

                // Ensure delimiters '&&' and '$$' are surrounded by double-newlines
                out = out.replace(/\s*&&\s*/g, '\n\n&&\n\n');
                out = out.replace(/\s*\$\$\s*/g, '\n\n$$$$\n\n');

                // Ensure that a delimiter '&&' is followed by a double-newline before LAT...LON
                // handle cases with no whitespace, single newline, or multiple whitespace/newlines
                out = out.replace(/&&\s*\n+(?=\s*LAT\.\.\.LON)/g, '&&\n\n');
                out = out.replace(/&&(?=\s*LAT\.\.\.LON)/g, '&&\n\n');

                // --------------------------- Targeted fixes ---------------------------
                // 1) Number-only preamble lines (e.g. "140\n\nWGUS86 ...") -> keep a single newline
                out = out.replace(/(^|\n)(\d{1,4})\n\n(?=[A-Z0-9])/gm, '$1$2\n');

                // 2) UGC-style line that ends with a hyphen: keep a single newline after it
                out = out.replace(/([A-Z]{2,3}[0-9]{3}(?:[>-][0-9]{3,6})*-)\n\n/g, '$1\n');

                // 3) VTEC or other slash-enclosed blocks (e.g. "/O.NEW.../" or "/00000.N.ER.../")
                //    should not be separated by an extra blank line
                out = out.replace(/(\/[^\n\/]{1,200}?\/)\n\n/g, '$1\n');

                // 4) Short capitalized-name splits (e.g. "San\n\nJoaquin") -> merge to a single newline
                out = out.replace(/(\b[A-Z][a-z]{1,20})\n\n([A-Z][a-z]{1,20}\b)/g, '$1\n$2');

                // 5) AWIPS/preamble product headers and adjacent all-caps codes (WGUS86 KSTO 161749, FLSSTO, etc.)
                //    turn double-newline into a single newline so header lines remain adjacent
                out = out.replace(/(^|\n)([A-Z]{2,6}\s+[A-Z]{2,4}\s+\d{5,8})\n\n(?=[A-Z0-9])/gm, '$1$2\n');
                out = out.replace(/(^|\n)([A-Z]{4,10})\n\n(?=[A-Z0-9])/gm, '$1$2\n');

                // 6) Generic adjacent ALL-CAPS/code lines -> single newline (conservative catch-all)
                out = out.replace(/(^|\n)([A-Z0-9\/\.\-&' ]{1,60})\n\n([A-Z0-9\/\.\-&' ]{1,60})/gm, '$1$2\n$3');

                // 7) Specific phrase/timestamp fixes: Flood Advisory, NWS office line, human timestamp
                out = out.replace(/(Flood Advisory)\n\n/gi, '$1\n');
                // Collapse double-newline after 'National Weather Service <office>' whether or not there's a trailing comma
                out = out.replace(/(National Weather Service [^\n,]{1,120},)\n\n/gi, '$1\n');
                out = out.replace(/(National Weather Service [^\n,]{1,120})(?!,)\n\n/gi, '$1\n');
                // Ensure exactly one newline BEFORE a human timestamp (collapse multiple blank lines)
                // Accept times like "839 PM", "0839 PM", or "9:39 PM" and common real-world variants
                out = out.replace(/\n{2,}(?=(?:At\s+)?(?:\d{3,4}|\d{1,2}(?::\d{2})?)\s*(?:AM|PM)\s*(?:PST|PDT|MST|MDT|CST|CDT|EST|EDT|HST|HDT|AKDT|AKST)\s*(?:,?\s*(?:Mon|Tue|Wed|Thu|Fri|Sat|Sun))?\s*[A-Za-z]{3}\s+\d{1,2}\s+\d{4})/gi, '\n');
                // Extra fallback: collapse double-newline immediately before 3- or 4-digit times (e.g. "\n\n839 PM...")
                out = out.replace(/\n{2,}(?=(?:At\s+)?\d{3,4}\s*(?:AM|PM))/gi, '\n');
                // Ensure timestamp is followed by exactly two newlines (timestamp ends paragraph)
                out = out.replace(/((?:At\s+)?(?:\d{3,4}|\d{1,2}(?::\d{2})?)\s*(?:AM|PM)\s*(?:PST|PDT|MST|MDT|CST|CDT|EST|EDT|HST|HDT|AKDT|AKST)\s*(?:,?\s*(?:Mon|Tue|Wed|Thu|Fri|Sat|Sun))?\s*[A-Za-z]{3}\s+\d{1,2}\s+\d{4})\n*/gi, '$1\n\n');

                // 10) Collapse double-newline after common section headings (EXCEPT those that should remain their own paragraph)
                (function(){
                    // keep these compact (collapse the extra blank line)
                    const headings = [
                        'WIND',
                        'HAIL',
                        'HAIL THREAT',
                        'WIND THREAT',
                        'TORNADO',
                        'TORNADO DAMAGE THREAT',
                        'THUNDERSTORM DAMAGE THREAT',
                        'FLASH FLOOD DAMAGE THREAT',
                        'FLASH FLOOD',
                        'WATERSPOUT',
                        'EXPECTED RAINFALL RATE'
                    ];
                    for (const h of headings) {
                        const esc = h.replace(/[.*+?^${}()|[\]\\]/g, '\\$&');
                        // match the heading possibly followed by dots and whitespace, then two+ newlines
                        const re = new RegExp('(' + esc + '(?:\.{2,}|\.{0,3})?)\\n\\n', 'gi');
                        out = out.replace(re, '$1\n');
                    }
                })();

                // Ensure the following headings have TWO newlines BEFORE them but ONLY ONE newline AFTER
                (function(){
                    const adjust = ['LAT...LON','TIME...MOT...LOC','TIME.MOT.LOC','MAX HAIL SIZE','MAX WIND GUST','WATERSPOUT'];
                    for (const h of adjust) {
                        const esc = h.replace(/[.*+?^${}()|[\]\\]/g, '\\$&');

                        // 1) If the heading follows a paragraph without a blank line, ensure a blank line BEFORE it
                        //    (convert single-newline separation into a paragraph break)
                        out = out.replace(new RegExp('([^\\n])\\n(\\s*' + esc + '(?:\\.{2,}|\\.{0,3})?[^\\n]*)','gi'), '$1\\n\\n$2');

                        // 2) Normalize any amount of blank lines BEFORE the heading down to exactly TWO
                        out = out.replace(new RegExp('\\n{2,}(\\s*' + esc + '(?:\\.{2,}|\\.{0,3})?[^\\n]*)','gi'), '\\n\\n$1');

                        // 3) Ensure exactly ONE newline AFTER the heading (collapse 2+ following newlines to 1)
                        out = out.replace(new RegExp('(' + esc + '(?:\\.{2,}|\\.{0,3})?[^\\n]*)\\n{2,}','gi'), '$1\\n');

                        // 4) If heading is at EOF with no trailing newline, ensure a single trailing newline
                        out = out.replace(new RegExp('(' + esc + '(?:\\.{2,}|\\.{0,3})?[^\\n]*)$','gi'), '$1\\n');
                    }
                })();

                // 8) Hyphen-terminated areaDesc handling:
                //    - keep adjacent capitalized fragments joined (e.g. "X-\nY" -> "X-Y")
                //    - collapse stray newlines inside long hyphen-separated areaDesc paragraphs
                //      (e.g. "Mariposa-...-Kings Canyon NP-Grant Grove Area" should be a single paragraph)
                out = out.replace(/(-)\n+(?=\s*[A-Z][a-z])/g, '$1');

                // Collapse internal single-newlines inside paragraphs that contain multiple hyphen-separated
                // tokens (these are almost always areaDesc lines). Run this BEFORE we force a newline
                // before "Including" so the subsequent rule can place "Including" on its own line.
                out = out.replace(/(^|\n)((?:(?!\n).*-){2,}.*?)(?=\n{2,}|$)/gm, function(_, pfx, body){
                    return pfx + body.replace(/\n+/g, ' ');
                });

                // Ensure 'Including' starts on its own line when it follows an area-desc fragment
                out = out.replace(/-\s*(Including\b)/gi, '-\n$1');
                // Add newline after 'Including the cities' phrase
                out = out.replace(/(Including the cities[^\n]*?)(?=\d{1,2}:?\d{2}\s*(AM|PM)\s*[A-Z]{2,4}\s*[A-Za-z]{3}\s+\d{1,2}\s+\d{4})/gi, '$1\n');

                // 9) Collapse any newlines inside an "Including ..." list (until the next paragraph) into spaces
                //    (the "Including" heading will be on its own line due to the rule above)
                out = out.replace(/(Including\b[\s\S]*?)(?=\n{2,}|$)/gi, function(m){ return m.replace(/\n+/g, ' '); });

                // 9b) Normalize "locations ... include" blocks:
                //    - ensure exactly one newline after the heading, list each location on its own line,
                //      and end the list with two newlines (unless the following paragraph already provides separation).
                out = out.replace(/(locations(?:\s+impacted)?\s+includes?\b[^\n]*)\n+([\s\S]*?)(?=\n{2,}|$)/gi, function(_, heading, listBody){
                    // collapse internal newlines to spaces, then split on common separators
                    const flat = listBody.replace(/\n+/g, ' ').trim();
                    const parts = flat.split(/\s*(?:,|;|\/|\band\b|\s-\s|\s+—\s+)\s*/i).map(s=>s.trim()).filter(Boolean);
                    if (parts.length <= 1) {
                        // not a multi-item list — ensure single newline after heading and keep remainder
                        return heading + '\n' + flat;
                    }
                    // return heading + newline + one-item-per-line + paragraph break
                    return heading + '\n' + parts.join('\n') + '\n\n';
                });

                // 9c) Collapse an extra blank line before short all-caps region/state names (e.g. "\n\nKANSAS") to a single newline,
                //      but do not collapse section headings like PRECAUTIONARY/PREPAREDNESS ACTIONS or other known section headers.
                out = out.replace(/\n{2,}(?=\s*(?!PRECAUTIONARY|PREPAREDNESS|ACTIONS|WHAT|WHERE|IMPACTS|LAT\.{3}|TIME|WIND|HAIL|TORNADO)[A-Z0-9 '\&\-.]{1,40}\b(?:\.{3})?(?:\n|$))/gi, '\n');

                // 11) Collapse double-newline between numeric-only lines (UGC/LAT...LON number lists)
                // Convert patterns like "1234 56789\n\n2345 67890" -> single newline between numeric lines
                out = out.replace(/(^|\n)(\s*(?:\d{3,5}(?:\s+\d{3,5})*)\s*)\n\n(?=\s*\d{3,5})/gm, '$1$2\n');

                // 12) For starred sections like "* WHAT...", "* WHERE...", etc. collapse internal double-newlines
                // into single newlines while preserving a double-newline between different sections.
                // Do not allow the starred-section block to consume trailing delimiter lines
                // (lines that contain only &&, $ or $$). Stop the block before such delimiter lines.
                out = out.replace(/(\*\s+[A-Z][\s\S]*?)(?=\n\*\s+[A-Z]|\n\s*(?:&&|\$\$?|\$)\s*(?:\n|$)|$)/g, function(block) {
                    // collapse multiple blank lines inside the block to single newlines
                    // but do not remove the final blank-line separator (we'll re-ensure it)
                    let inner = block.replace(/\n{3,}/g, '\n\n');
                    // collapse internal double-newlines that are not immediately followed by '* '
                    inner = inner.replace(/\n\n(?!\*\s)/g, '\n');
                    // ensure block ends with exactly two newlines so sections stay separated
                    inner = inner.replace(/\n+$/g, '') + '\n\n';
                    return inner;
                });

                // 13) Ensure short all-caps product lines (e.g., "NPWBUF") are followed by a blank line
                // Keep double-newline by default, but if the following text is a UGC code
                // (e.g. "LAZ141-"), use a single newline so the UGC stays adjacent.
                out = out.replace(/(^|\n)([A-Z]{3,8})\n(?!\n)/gm, function(match, p1, p2, offset, string) {
                    const after = string.slice(offset + match.length);
                    // UGC pattern: 2-3 letters + 3 digits, optional ranges/timestamps, ending with a hyphen
                    const ugcRe = /^\s*[A-Z]{2,3}\d{3}(?:[>-]\d{3,6})*-/;
                    if (ugcRe.test(after)) return p1 + p2 + '\n';
                    return p1 + p2 + '\n\n';
                });

                // Ensure PRECAUTIONARY / PREPAREDNESS ACTIONS (with or without leading '*') is its own paragraph
                // Accept optional spaces around the slash and preserve a leading '* ' if present.
                out = out.replace(/\n{0,2}\s*(\*\s*)?(PRECAUTIONARY\s*\/\s*PREPAREDNESS ACTIONS\.{3,})\s*\n{0,2}/gi, '\n\n$1$2\n\n');

                // Final enforcement: ensure '&&' is surrounded by exactly two newlines
                // This runs last so earlier replacements can't collapse these separators.
                out = out.replace(/\n{0,2}&&\n{0,2}/g, '\n\n&&\n\n');
                out = out.replace(/\n{0,2}\$\$\n{0,2}/g, '\n\n$$$$\n\n');

                // Last-resort: if any double-newline still appears immediately before a 3- or 4-digit time
                // (examples: "\n\n839 PM...", "\n\n1139 PM..."), collapse it to a single newline.
                out = out.replace(/\n{2,}(?=(?:At\s+)?\d{3,4}\s*(?:AM|PM))/gi, '\n');

                // Final collapse: reduce any 3+ consecutive newlines to exactly two
                // (fixes cases where earlier replacements accidentally introduce a third blank line)
                out = out.replace(/\n{3,}/g, '\n\n');

                return out;
            }

            // Normalize incoming message newlines and enforce heading spacing rules.
            // Hoisted so it can be used early during CAP/rawText processing as well as per-part.
            function formatMessageNewlines(msg) {
                if (!msg) return msg;
                let formatted = String(msg);

                // 0) Remove all XML tags (anything between < and >)
                formatted = formatted.replace(/<[^>]+>/g, '');

                // 1) Convert literal escaped sequences ("\\n", "\\r\\n") into actual newlines
                formatted = formatted.replace(/\\r\\n/g, '\n');
                formatted = formatted.replace(/\\n/g, '\n');

                // 2) Normalize any remaining CR/LF into \n
                formatted = formatted.replace(/\r\n/g, '\n').replace(/\r/g, '\n');

                // 3) Remove stray trailing/leading whitespace around newlines (prevents " <newline>HEADING" cases)
                formatted = formatted.replace(/[ \t]+\n/g, '\n');
                formatted = formatted.replace(/\n[ \t]+/g, '\n');
                formatted = formatted.replace(/^\s+|\s+$/g, '');

                // 4) Defensive: replace any remaining backslash+n sequences
                formatted = formatted.replace(/\\+n/g, '\n');

                // 5) Collapse runs of 2+ newlines down to exactly 2 (paragraph separation)
                formatted = formatted.replace(/\n{2,}/g, '\n\n');

                // 6) Ensure exact spacing before headings that should have TWO newlines
                const twoNL = ['HAZARD\\.\\.\\.', 'SOURCE\\.\\.\\.', 'IMPACT\\.\\.\\.', 'Locations impacted include'];
                for (const h of twoNL) {
                    // If the heading is on the same line as previous text (possibly separated by spaces),
                    // strip those spaces and insert exactly two newlines before the heading.
                    formatted = formatted.replace(new RegExp('([^\\n\\s])\\s*(' + h + ')', 'g'), '$1\n\n$2');
                    // Collapse any existing newline(s)+optional spaces before the heading to exactly two newlines
                    formatted = formatted.replace(new RegExp('\\n+\\s*(' + h + ')', 'g'), '\n\n$1');
                }

                // 7) Ensure exact spacing before headings that should have ONE newline
                const oneNL = [
                    'TORNADO DAMAGE THREAT\\.\\.\\.',
                    'THUNDERSTORM DAMAGE THREAT\\.\\.\\.',
                    'FLASH FLOOD DAMAGE THREAT\\.\\.\\.',
                    'FLASH FLOOD\\.\\.\\.',
                    'TIME\\.\\.\\.MOT\\.\\.\\.LOC',
                    'TORNADO\\.\\.\\.',
                    'WATERSPOUT\\.\\.\\.',
                    'SNOW SQUAL\\.\\.\\.',
                    'SNOW SQUALL IMPACT\\.\\.\\.',
                    'SNOW SQUALL\\.\\.\\.',
                    'MAX WIND GUST\\.\\.\\.',
                    'MAX HAIL SIZE\\.\\.\\.',
                    'WIND THREAT\\.\\.\\.',
                    'HAIL THREAT\\.\\.\\.',
                    'WIND, AND HAIL\\.\\.\\.',
                    'AND HAIL\\.\\.\\.',
                    'EXPECTED RAINFALL RATE\\.\\.\\.'
                ];
                for (const h of oneNL) {
                    // If heading immediately follows text (possibly with spaces), strip spaces and insert one newline
                    formatted = formatted.replace(new RegExp('([^\\n\\s])\\s*(' + h + ')', 'g'), '$1\n$2');
                    // Collapse any existing newline(s)+optional spaces before the heading to exactly one newline
                    formatted = formatted.replace(new RegExp('\\n+\\s*(' + h + ')', 'g'), '\n$1');
                }

                // 8) Ensure TIME...MOT...LOC is single-lined (followed by normal spacing)
                formatted = formatted.replace(/(LAT\.\.\.LON[^\n]*)\n+(\s*TIME\.\.\.MOT\.\.\.LOC)/g, '$1\n$2');

                // 9) Final pass: remove any remaining trailing spaces before newlines, collapse multiples and trim
                formatted = formatted.replace(/[ \t]+\n/g, '\n');
                formatted = formatted.replace(/\n{2,}/g, '\n\n');
                formatted = formatted.replace(/^\s+|\s+$/g, '');

                // strip any $$ tokens left behind along with trailing text
                formatted = formatted.replace(/\$\$[^\n]*/g, '');

                return formatted;
            }

            // --- START: Message cleanup and splitting logic ---

            /**
             * Cleans up and splits the alert message so that && and $$ tokens (and any trailing text)
             * are appended to the previous message part, not as their own part.
             * Also removes XML tags and replaces 2+ spaces with \n.
             * @param {string} msg
             * @returns {string[]} Array of cleaned message blocks
             */
            function cleanAndSplitMessage(msg) {
                if (!msg) return [];

                // Remove XML tags (anything between <...>)
                msg = msg.replace(/<[^>]+>/g, '');

                // Replace 2+ spaces with \n
                msg = msg.replace(/ {2,}/g, '\n');

                // remove any $$ tokens and any text that follows them on the same line
                // these are usually end-of-message markers such as "$$ DW"
                msg = msg.replace(/\$\$[^\n]*/g, '');

                // Split at every && or $$, but append the delimiter and its trailing text to the previous part
                let splitRegex = /(\s*(?:&&|\$\$)[^\s]*)/g;
                let parts = [];
                let lastIndex = 0;
                let match;
                while ((match = splitRegex.exec(msg)) !== null) {
                    // Everything before the delimiter
                    let before = msg.slice(lastIndex, match.index);
                    if (parts.length === 0) {
                        parts.push(before + match[0]);
                    } else {
                        parts[parts.length - 1] += before + match[0];
                    }
                    lastIndex = splitRegex.lastIndex;
                }
                // Any remaining text after the last delimiter
                if (lastIndex < msg.length) {
                    let after = msg.slice(lastIndex);
                    if (parts.length === 0) {
                        parts.push(after);
                    } else {
                        parts[parts.length - 1] += after;
                    }
                }

                // UGC code pattern: capture full UGC groups (e.g. "LAZ141-142-152-241>243-" or "AKZ320>322-324-325-121300-")
                // - match 2–3 letter prefix, a 3-digit zone, then any number of -NNN or >NNN or -NNNNNN timestamp groups, ending with a hyphen
                const ugcPattern = /([A-Z]{2,3}[0-9]{3}(?:[>-][0-9]{3,6})*-)/g;

                let blocks = [];
                for (let part of parts) {
                    // Find all UGC code positions (record start and end)
                    let indices = [];
                    let match;
                    ugcPattern.lastIndex = 0;
                    while ((match = ugcPattern.exec(part)) !== null) {
                        const start = match.index;
                        const code = match[1];
                        const end = start + code.length;
                        indices.push({ start, end, code });
                    }

                    // If no UGC codes, keep the whole part
                    if (indices.length === 0) {
                        blocks.push(part);
                        continue;
                    }

                    // Group nearby UGC matches into clusters so adjacent UGC groups
                    // (e.g., "FLZ...-  GAZ...-") remain together and are not split.
                    const clusters = [];
                    let cur = { start: indices[0].start, end: indices[0].end };
                    for (let i = 1; i < indices.length; i++) {
                        const gapText = part.slice(cur.end, indices[i].start);
                        // If the gap between codes does NOT contain a paragraph break (\n\n)
                        // or explicit message delimiters (&&, $$), treat the codes as part
                        // of the same UGC cluster. This keeps multiple different UGC prefixes
                        // on the same block as long as they're in the same paragraph.
                        if (!(/\n{2,}/.test(gapText) || /&&|\$\$/.test(gapText))) {
                            // extend current cluster to include this code
                            cur.end = indices[i].end;
                        } else {
                            // close current cluster and start new
                            clusters.push({ start: cur.start, end: cur.end });
                            cur = { start: indices[i].start, end: indices[i].end };
                        }
                    }
                    clusters.push({ start: cur.start, end: cur.end });

                    // For each cluster, capture the text from cluster.start to the next cluster.start (or to end)
                    for (let ci = 0; ci < clusters.length; ci++) {
                        const c = clusters[ci];
                        const nextStart = (ci + 1 < clusters.length) ? clusters[ci + 1].start : part.length;
                        let block = part.slice(c.start, nextStart);

                        // Optionally, prepend any preamble before the first cluster to the first block
                        if (ci === 0 && c.start > 0) {
                            let preamble = part.slice(0, c.start);
                            if (preamble) block = preamble + block;
                        }

                        // Normalize paragraphs inside the block (preserve paragraph breaks; join wrapped lines)
                        block = normalizeParagraphs(block);
                        blocks.push(block);
                    }
                }

                // Before returning, ensure each block preserves surrounding newlines for delimiters
                blocks = blocks.map(b => {
                    if (!b) return b;
                    // ensure '&&' and '$$' are on their own with double-newline separators
                    b = b.replace(/\s*&&\s*/g, '\n\n&&\n\n');
                    b = b.replace(/\s*\$\$\s*/g, '\n\n$$$$\n\n');
                    return b;
                });

                // Remove empty blocks (but keep blocks with &&, $$, or text)
                return blocks.filter(b => b && b.replace(/\s/g, '').length > 0);
            }

            // Use the new cleanup/split function
            // For non‑VTEC CAP minimal-cleanup messages we must NOT split the text — keep a single part.
            let messageParts;
            if (capMinimalCleanup) {
                // keep the entire minimal-cleanup payload as a single message part (preserve formatting)
                messageParts = [rawText];
            } else {
                messageParts = cleanAndSplitMessage(rawText);
            }

            // If any CAP XML cleanup was performed (full cleanup or minimal-cleanup), skip storing this alert
            if (cleanedCAPXML || capMinimalCleanup) {
                console.log('CAP XML cleanup detected; skipping this alert.');
                log('CAP XML cleanup detected; skipping this alert.');
                return;
            }

            // --- END: Message cleanup and splitting logic ---

            // Prefer CAP identifier for non-VTEC minimal-cleanup messages when available
            var idString = (capIdentifier && capIdentifier.length) ? capIdentifier : (thisObject.product_type + thisObject.office + (Math.random() * 1000000).toFixed(0));

            // If a full VTEC is present on the main object, prefer a canonical VTEC-based id:
            // office.phenomena.significance.eventTrackingNumber (example: KSGX.HW.A.0002)
            var vtecId = (thisObject && thisObject.office && thisObject.phenomena && thisObject.significance && thisObject.eventTrackingNumber)
              ? `${thisObject.office}.${thisObject.phenomena}.${thisObject.significance}.${thisObject.eventTrackingNumber}`
              : null;

            // Headline extraction removed per user request.
            var headline = null;

            // Build parsedAlert objects for each message part
            // Helper: expand a UGC group string into individual UGC IDs (ignore timestamps / non-3-digit tokens)
            function expandUgcGroup(group) {
                if (!group) return [];
                // Trim trailing hyphens and capture prefix letters
                group = group.replace(/^-+|-+$/g, '').trim();
                const m = group.match(/^([A-Z]{2,3})([\s\S]*)$/);
                if (!m) return [];
                const prefix = m[1];
                const rest = m[2].replace(/-+$/g, '');
                const parts = rest.split('-').filter(Boolean);
                const out = new Set();

                for (const p of parts) {
                    // handle 6-digit timestamps like 282200 by adding newline after
                    if (/^\d{6}$/.test(p)) {
                        out.add(p + '\n');
                        continue;
                    }
                    // single 3-digit
                    let r;
                    if ((r = p.match(/^\s*(\d{3})\s*$/))) {
                        out.add(prefix + r[1]);
                        continue;
                    }
                    // range like 016>018
                    if ((r = p.match(/^(\d{3})>(\d{3})$/))) {
                        const start = parseInt(r[1], 10);
                        const end = parseInt(r[2], 10);
                        if (start <= end && end - start < 1000) {
                            for (let n = start; n <= end; n++) out.add(prefix + String(n).padStart(3, '0'));
                        }
                        continue;
                    }
                    // if part contains letters or unexpected format, ignore
                }
                return Array.from(out);
            }

            // Simple HTTPS GET -> JSON with small cache
            const __zoneInfoCache = (global.__zoneInfoCache = global.__zoneInfoCache || new Map());
            function getJson(url, timeout = 2000) {
                return new Promise((resolve, reject) => {
                    try {
                        const req = https.get(url, { headers: { 'User-Agent': 'SparkAlerts', 'Accept': 'application/geo+json, application/json' } }, (res) => {
                            let data = '';
                            res.on('data', (c) => data += c);
                            res.on('end', () => {
                                try {
                                    const obj = JSON.parse(data);
                                    resolve(obj);
                                } catch (e) {
                                    reject(e);
                                }
                            });
                        });
                        req.on('error', reject);
                        req.setTimeout(timeout, () => { req.destroy(new Error('timeout')); });
                    } catch (e) { reject(e); }
                });
            }

            async function lookupZoneDisplay(ugcId) {
                if (!ugcId) return null;
                if (__zoneInfoCache.has(ugcId)) return __zoneInfoCache.get(ugcId);

                // validate UGC format
                const m = ugcId.match(/^([A-Z]+)(\d{3})$/);
                if (!m) { __zoneInfoCache.set(ugcId, null); return null; }

                const prefix = m[1];
                const lastLetter = prefix[prefix.length - 1];
                const isCounty = (lastLetter === 'C');

                // County zones -> use county endpoint (keep existing behavior)
                if (isCounty) {
                    const url = `https://api.weather.gov/zones/county/${ugcId}`;
                    try {
                        const json = await getJson(url);
                        if (json && json.properties) {
                            const name = json.properties.name && json.properties.state ? `${json.properties.name}, ${json.properties.state}` : json.properties.name || null;
                            __zoneInfoCache.set(ugcId, name);
                            return name;
                        }
                    } catch (e) {
                        // treat as not found
                    }
                    __zoneInfoCache.set(ugcId, null);
                    return null;
                }

                // Non-county zones: try `zones/forecast` first, then fall back to `zones/fire` and return `properties.name`.
                const forecastUrl = `https://api.weather.gov/zones/forecast/${ugcId}`;
                try {
                    const json = await getJson(forecastUrl);
                    if (json && json.properties && json.properties.name) {
                        const name = json.properties.name;
                        __zoneInfoCache.set(ugcId, name);
                        return name;
                    }
                } catch (e) {
                    // ignore — we'll try fallback
                }

                // Fallback: zones/fire (some UGCs exist only under the fire namespace)
                const fireUrl = `https://api.weather.gov/zones/fire/${ugcId}`;
                try {
                    const json = await getJson(fireUrl);
                    if (json && json.properties && json.properties.name) {
                        const name = json.properties.name;
                        __zoneInfoCache.set(ugcId, name);
                        return name;
                    }
                } catch (e) {
                    // treat as not found
                }

                __zoneInfoCache.set(ugcId, null);
                return null;
            }

            // Build parsedAlerts asynchronously so we can fetch zone/county names
            let parsedAlerts = [];
            for (let idx = 0; idx < messageParts.length; idx++) {
                const msgPart = messageParts[idx];

                // --- Remove message parts that are just XML ---
                const isPartRawXMLOnly = (
                    msgPart.trim().startsWith('<?xml') &&
                    msgPart.trim().endsWith('</alert>')
                );
                if (isPartRawXMLOnly) continue;

                // Extract VTEC from each message part
                let vtec = msgPart.match(/\/O\..*?\/\n?/);
                if (!vtec) {
                    vtec = msgPart.match(/<parameter>\s*<valueName>VTEC<\/valueName>\s*<value>(.*?)<\/value>\s*<\/parameter>/);
                    if (vtec && vtec[1]) vtec = vtec[1];
                }
                if (!vtec) vtec = null;
                let vtecObjects = vtec ? (typeof vtec === 'string' ? vtec : vtec[0]).split('.') : [];

                // Function to convert VTEC time to ISO UTC timestamp
                function vtecToIso(ts) {
                    if (!ts || typeof ts !== 'string') return null;
                    const m = ts.match(/(\d{2})(\d{2})(\d{2})T(\d{2})(\d{2})Z/);
                    if (!m) return null;
                    const yy = parseInt(m[1], 10);
                    const year = 2000 + yy;
                    const month = parseInt(m[2], 10) - 1;
                    const day = parseInt(m[3], 10);
                    const hour = parseInt(m[4], 10);
                    const minute = parseInt(m[5], 10);
                    return new Date(Date.UTC(year, month, day, hour, minute)).toISOString();
                }

                // Build vtec object for this message part.
                // - If a full VTEC string is present, parse all fields.
                // - Otherwise, for true non‑VTEC minimal cleanup build a *minimal* vtec object
                //   containing only meaningful values (eventTrackingNumber/startTime/endTime)
                //   or set to `null` when nothing is available. This prevents empty string
                //   fields like office/phenomena/significance from being emitted.
                let vtecObj = null;
                if (vtecObjects.length >= 7) {
                    vtecObj = {
                            product: vtecObjects[0],
                            action: vtecObjects[1],
                            office: vtecObjects[2],
                            phenomena: vtecObjects[3],
                            significance: vtecObjects[4],
                            eventTrackingNumber: vtecObjects[5],
                            startTime: (headerStartIso || parseHumanTimestampFromText(msgPart) || vtecToIso(vtecObjects[6].split('-')[0])),
                            endTime: (headerEndIso || vtecToIso(vtecObjects[6].split('-')[1]))
                        };
                } else {
                    // fallback: if the main `thisObject` contains a genuine VTEC (has phenomena+significance), use it
                    if (thisObject && thisObject.phenomena && thisObject.significance) {
                        vtecObj = thisObject;
                    } else {
                        // non-VTEC: construct a minimal vtec object only if we have values to add
                        const minimal = {};
                        const etn = (thisObject && thisObject.eventTrackingNumber) || capIdentifier || null;
                        const st = (thisObject && thisObject.startTime) || capSent || headerStartIso || null;
                        const en = (thisObject && thisObject.endTime) || capExpires || headerEndIso || null;
                        if (etn) minimal.eventTrackingNumber = etn;
                        if (st) minimal.startTime = st;
                        if (en) minimal.endTime = en;
                        vtecObj = Object.keys(minimal).length ? minimal : null;
                    }
                }

                // Build properties dynamically to avoid emitting empty keys for non‑VTEC cleanup
                const props = { recievedTime: recievedTime };

                // Prefer eventTrackingNumber from vtecObj, then thisObject, then CAP identifier
                const _etn = (vtecObj && vtecObj.eventTrackingNumber) || (thisObject && thisObject.eventTrackingNumber) || capIdentifier || null;
                if (_etn) props.event_tracking_number = _etn;

                // Only attach `vtec` when there are meaningful fields present (prevents empty office/phenomena/significance)
                if (vtecObj && Object.keys(vtecObj).length) props.vtec = vtecObj;

                // Add product_type / phenomena / significance only when we have them
                const phen = (vtecObj && vtecObj.phenomena) || (thisObject && thisObject.phenomena) || null;
                const sig = (vtecObj && vtecObj.significance) || (thisObject && thisObject.significance) || null;
                if (phen && sig) {
                    props.product_type = phen + sig;
                    props.phenomena = phen;
                    props.significance = sig;
                }

                // Pit refer per-part VTEC for id when present, otherwise prefer main VTEC (`vtecId`), then fall back to idString
                const baseId = (vtecObj && vtecObj.office && vtecObj.phenomena && vtecObj.significance && vtecObj.eventTrackingNumber)
                    ? `${vtecObj.office}.${vtecObj.phenomena}.${vtecObj.significance}.${vtecObj.eventTrackingNumber}`
                    : (vtecId || idString);

                // Format message with proper newline spacing (hoisted to file scope)

                const formattedMessage = formatMessageNewlines(msgPart);

                // Build alert name for this specific message part (handle split alerts and VTEC+significance)
                let partAlertName = alertName; // start with the overall alert name
                
                // If we have phenomena and significance, try to build a proper name from VTEC data
                const partPhen = (vtecObj && vtecObj.phenomena) || phen;
                const partSig = (vtecObj && vtecObj.significance) || sig;
                if (partPhen && partSig) {
                    const vtecBasedName = buildAlertNameFromVtec(partPhen, partSig);
                    if (vtecBasedName) {
                        partAlertName = vtecBasedName;
                    }
                }
                
                // If still no good name, search the message part text for alert type keywords
                if (!partAlertName || partAlertName === 'Unknown Alert') {
                    const keywords = ['ADVISORY', 'WARNING', 'WATCH', 'ALERT', 'STATEMENT', 'EMERGENCY'];
                    const upperMsg = msgPart.toUpperCase();
                    for (const kw of keywords) {
                        const idx = upperMsg.indexOf(kw);
                        if (idx !== -1) {
                            // Extract context around the keyword
                            const start = Math.max(0, idx - 100);
                            const end = Math.min(upperMsg.length, idx + kw.length + 100);
                            const context = msgPart.substring(start, end);
                            const match = context.match(/([A-Z][A-Z\s\-]{3,60}?)\s+(ADVISORY|WARNING|WATCH|ALERT|STATEMENT|EMERGENCY)/i);
                            if (match && match[1]) {
                                partAlertName = match[1].trim().replace(/\s+/g, ' ');
                                break;
                            }
                        }
                    }
                }

                // Headline extraction from between ellipses: reintroduce smart extractor
                // Adds `NWSHeadline` property when a timestamp (time + day + date) is
                // immediately followed by three dots "..." and a headline that can
                // be delimited by known stop tokens. If no three dots are present
                // after the timestamp, no headline is returned.
                function extractNWSHeadlineFromText(txt) {
                    if (!txt || typeof txt !== 'string') return null;

                    // Find VTEC block if present and anchor search after it (only for common actions)
                    const vtecMatch = txt.match(/\/O\.[\s\S]*?\//i);
                    let searchStart = 0;
                    if (vtecMatch && vtecMatch[0]) {
                        try {
                            const parts = vtecMatch[0].split('.');
                            const action = parts[1] ? parts[1].toUpperCase().replace(/[^A-Z]/g, '') : '';
                            const allowed = new Set(['CON','NEW','UPG','COR','EXT','EXA','EXB']);
                            if (allowed.has(action)) searchStart = vtecMatch.index + vtecMatch[0].length;
                        } catch (e) { /* ignore and search from start */ }
                    }

                    // Look for a human timestamp after the chosen searchStart (or anywhere if none)
                    const timeOnlyRe = /(\b(?:\d{1,4}|\d{1,2}:\d{2})\s*(?:AM|PM)\s*(?:PST|PDT|MST|MDT|CST|CDT|EST|EDT|HST|HDT|AKDT|AKST)\s*(?:,?\s*(?:Mon|Tue|Wed|Thu|Fri|Sat|Sun))?\s+[A-Za-z]{3}\s+\d{1,2}\s+\d{4})/i;
                    const subTxt = txt.slice(searchStart);
                    const tm = subTxt.match(timeOnlyRe);
                    if (!tm || typeof tm.index !== 'number') return null;

                    // Start just after the timestamp match in the original text
                    const startIdx = searchStart + tm.index + tm[0].length;
                    let tail = txt.slice(startIdx);
                    if (!tail || !tail.trim()) return null;

                    // Require that the headline begins with literal ellipses '...'
                    const ellMatch = tail.match(/^\s*(\.\.\.)/);
                    if (!ellMatch) return null;
                    // remove the leading ellipses and any following whitespace
                    tail = tail.slice(tail.indexOf(ellMatch[1]) + ellMatch[1].length).replace(/^\s+/, '');

                    // Determine emergency style
                    const isEmergency = /TORNADO\s+EMERGENCY|FLASH\s+FLOOD\s+EMERGENCY/i.test(tail);

                    // Stop tokens per user: stop at a line beginning with 'At' (case-sensitive),
                    // stop at a '* WHAT' section, stop at 'The National Weather Service', or 'FLASH'.
                    const stops = [];
                    const atPos = tail.search(/\n\s*At\b/);
                    if (atPos >= 0) stops.push(atPos);
                    const starWhatPos = tail.search(/\n\s*\*\s*WHAT\b/);
                    if (starWhatPos >= 0) stops.push(starWhatPos);
                    const nwsPos = tail.search(/The National Weather Service/);
                    if (nwsPos >= 0) stops.push(nwsPos);
                    const flashPos = tail.search(/\bFLASH\b/i);
                    if (flashPos >= 0) stops.push(flashPos);

                    // Emergency extra stops
                    if (isEmergency) {
                        const aDotPos = tail.search(/\.\.\.\s*A\b/i);
                        if (aDotPos >= 0) stops.push(aDotPos);
                        const dotFlash = tail.search(/\.\.\.\s*FLASH/i);
                        if (dotFlash >= 0) stops.push(dotFlash);
                    }

                    // Default to paragraph end if no other stop found
                    const paraPos = tail.search(/\n{2,}/);
                    if (paraPos >= 0) stops.push(paraPos);

                    let end = -1;
                    if (stops.length) end = Math.min.apply(null, stops.filter(n => n >= 0));
                    if (end >= 0) tail = tail.slice(0, end);

                    let headline = tail.replace(/\s+/g, ' ').trim();
                    headline = headline.replace(/^[\-\:\,\.]+\s*/, '');
                    if (!headline || headline.length < 1) return null;
                    // Trim trailing punctuation and whitespace
                    headline = headline.replace(/[\s\-\:;\.]+$/g, '').trim();
                    return headline || null;
                }

                // Candidate headline extracted from timestamps (will be inserted into `alertinfo`)
                let extractedNWSHeadline = null;

                let alertObj = {
                    event: partAlertName || alertName || 'Unknown Alert',
                    id: (messageParts.length === 1) ? baseId : (baseId + '_' + idx),
                    sender: (vtecObj && vtecObj.office) ? vtecObj.office : (thisObject && thisObject.office) || '',
                    sent: (vtecObj && vtecObj.startTime) ? vtecObj.startTime : (thisObject && thisObject.startTime) || null,
                    expires: (vtecObj && vtecObj.endTime) ? vtecObj.endTime : ((thisObject && thisObject.endTime) ? thisObject.endTime : (capExpires || null)),
                    description: formattedMessage,
                    ugc: [],
                    areaDesc: '',
                    properties: props
                };
                // strip any $$ tokens that may have survived all previous cleanups
                if (alertObj.description && typeof alertObj.description === 'string') {
                    alertObj.description = alertObj.description.replace(/\$\$[^\n]*/g, '').trim();
                }
                // Ensure two newlines follow the word 'BULLETIN' (and common misspelling 'BULITTEN')
                    if (alertObj && alertObj.description && typeof alertObj.description === 'string') {
                    alertObj.description = alertObj.description
                        .replace(/\bBULLETIN\b[\s]*/gi, 'BULLETIN')
                        .replace(/\bBULITTEN\b[\s]*/gi, '\n\nBULITTEN');
                }

                // Add smart NWSHeadline when present (timestamp followed by '...')
                try {
                    let _nws = extractNWSHeadlineFromText(msgPart || '');
                    if (!_nws) _nws = extractNWSHeadlineFromText(rawText || '');
                    if (_nws) extractedNWSHeadline = _nws;
                } catch (e) {
                    // swallow extraction errors
                }

                // Attach coordinates if available (either from LAT...LON line or CAP polygon/params)
                if (coordinates && coordinates.length > 0) {
                    alertObj.coordinates = coordinates;
                }

                // headline property removed per user request.

                // --- Extract canonical UGC group from this message part (with fallbacks) and resolve friendly names ---
                (function(){})();
                const ugcPattern = /([A-Z]{2,3}[0-9]{3}(?:[>-][0-9]{3,6})*-)/g;
                let canonicalUgc = null;

                // 1) try to find a canonical UGC group in this message part
                const m1 = msgPart.match(ugcPattern);
                if (m1 && m1.length) canonicalUgc = m1[0];

                // 2) fallback: search the entire original rawText (useful when UGC is in preamble/CAP but not in this part)
                if (!canonicalUgc) {
                    const m2 = rawText.match(ugcPattern);
                    if (m2 && m2.length) canonicalUgc = m2[0];
                }

                // 3) final fallback: try to assemble a single-zone UGC from any prefix+3-digit token found in this part
                if (!canonicalUgc) {
                    const pairRe = /([A-Z]{2,3})(\d{3})/g;
                    const pairs = [];
                    let mm;
                    while ((mm = pairRe.exec(msgPart)) !== null) pairs.push(mm[1] + mm[2]);
                    if (pairs.length) canonicalUgc = pairs[0] + '-';
                }

                // Collect all candidate UGC IDs from canonical group (expanded) AND any standalone tokens
                const candidateSet = new Set();
                try {
                    if (canonicalUgc) {
                        const ugcIds = expandUgcGroup(canonicalUgc).filter(Boolean);
                        for (const id of ugcIds) candidateSet.add(id);
                    }

                    const pairReAll = /([A-Z]{2,3})(\d{3})/g;
                    let mmx;
                    const sourcesToScan = [msgPart, rawText];
                    for (const src of sourcesToScan) {
                        if (!src) continue;
                        const scanStr = String(src)
                            .replace(/\\u300C/g, '-')
                            .replace(/\u300C/g, '-');
                        while ((mmx = pairReAll.exec(scanStr)) !== null) {
                            candidateSet.add(mmx[1] + mmx[2]);
                        }
                    }
                } catch (e) {
                    // ignore collection errors
                }

                // Keep only well-formed zone IDs like 'ABC123'
                const candidateIds = Array.from(candidateSet).filter(x => /^[A-Z]{2,3}\d{3}$/.test(x));
                if (candidateIds.length) {
                    alertObj.ugc = candidateIds;

                    // Resolve display names for all candidate IDs (counties, forecast zones, etc.)
                    try {
                        const results = await Promise.all(candidateIds.map(id => lookupZoneDisplay(id)));
                        const names = results.map((n, i) => n ? n : null).filter(Boolean);
                        if (names.length) {
                            alertObj.areaDesc = names.join('; ');
                        }
                    } catch (e) {
                        // if lookups fail, leave areaDesc empty for later fallback
                    }
                }

                // Fallback: if lookup produced no areaDesc, try to extract an areaDesc string
                // inserted earlier (CAP areaDesc or minimalParts). Prefer multi-line hyphen-terminated
                // fragments, then per-line hyphen-terminated candidates. Skip UGC-like lines.
                if (!alertObj.areaDesc) {
                    // try multi-line fragment first
                    const multi = msgPart.match(/([A-Za-z][\s\S]{10,}?-)/);
                    if (multi && !/[A-Z]{2,3}\d{3}/.test(multi[1])) {
                        let cleaned = multi[1].replace(/[;,]/g, '-').replace(/\s*\n\s*/g, '-').replace(/\s+/g, ' ').trim();
                        cleaned = cleaned.replace(/-+/g, '-').replace(/^[-\s]+|[-\s]+$/g, '');
                        if (cleaned.length) alertObj.areaDesc = cleaned + '-';
                    }
                }

                if (!alertObj.areaDesc) {
                    const lines = msgPart.split('\n').map(l => l.trim()).filter(Boolean);
                    for (const line of lines) {
                        if (/[A-Z]{2,3}\d{3}/.test(line)) continue; // skip UGC lines
                        if (line.endsWith('-') || /\b(Coastal|County|Waters|Parish|City|Lake|River|Coastal Waters)\b/i.test(line)) {
                            let cleaned = line.replace(/[;,]/g, '-').replace(/\s*\n\s*/g, '-').replace(/\s+/g, ' ').trim();
                            cleaned = cleaned.replace(/-+/g, '-').replace(/^[-\s]+|[-\s]+$/g, '');
                            if (cleaned.length) { alertObj.areaDesc = cleaned + (cleaned.endsWith('-') ? '' : '-'); break; }
                        }
                    }
                }

                // --- Extract structured eventMotionDescription from TIME...MOT...LOC if present ---
                (function() {
                    const msgSource = (msgPart || alertObj.message || rawText || '');
                    // Example: "TIME...MOT...LOC 1349Z 246DEG 25KT 3458 9702"
                    const motRe = /TIME\.{0,3}MOT\.{0,3}LOC\s+([0-9]{3,4}Z)?\s*(\d{1,3})\s*DEG\s*(\d{1,3})\s*KT\s*((?:\d{4,5}(?:\s+\d{4,5})*))/i;
                    const m = msgSource.match(motRe);
                    if (m) {
                        const raw = m[0].trim();
                        const timeZ = m[1] || null;
                        const deg = m[2] ? parseInt(m[2], 10) : null;
                        const kt = m[3] ? parseInt(m[3], 10) : null;
                        const coordTokens = m[4] ? m[4].trim().split(/\s+/) : [];

                        let lat = null, lon = null;
                        if (coordTokens.length >= 2) {
                            const tLat = coordTokens[0];
                            const tLon = coordTokens[1];
                            function tokenToNum(tok) {
                                if (!/^\d+$/.test(tok)) return NaN;
                                const len = tok.length;
                                const intPart = tok.slice(0, len - 2);
                                const decPart = tok.slice(len - 2);
                                return Number(intPart + '.' + decPart);
                            }
                            const latNum = tokenToNum(tLat);
                            const lonNum = tokenToNum(tLon);
                            if (!isNaN(latNum)) lat = latNum;
                            if (!isNaN(lonNum)) lon = -Math.abs(lonNum);
                        }

                        // Build ISO time using alert issued date (UTC) + parsed HHMMZ
                        let isoTime = null;
                        if (timeZ) {
                            const issuedDate = alertObj.issued ? new Date(alertObj.issued) : new Date();
                            if (!isNaN(issuedDate.getTime())) {
                                const hhmm = timeZ.replace(/Z$/i, '');
                                const hh = parseInt(hhmm.slice(0, hhmm.length - 2), 10);
                                const mm = parseInt(hhmm.slice(-2), 10);
                                let isoDate = new Date(Date.UTC(issuedDate.getUTCFullYear(), issuedDate.getUTCMonth(), issuedDate.getUTCDate(), hh, mm));
                                const diff = Math.abs(isoDate.getTime() - issuedDate.getTime());
                                if (diff > 12 * 60 * 60 * 1000) {
                                    const prev = new Date(isoDate.getTime() - 24 * 60 * 60 * 1000);
                                    const next = new Date(isoDate.getTime() + 24 * 60 * 60 * 1000);
                                    if (Math.abs(prev.getTime() - issuedDate.getTime()) < diff) isoDate = prev;
                                    else if (Math.abs(next.getTime() - issuedDate.getTime()) < diff) isoDate = next;
                                }
                                isoTime = isoDate.toISOString();
                            }
                        }

                        // friendly type detection
                        let type = 'storm';
                        const head = (alertObj.name || '').toUpperCase();
                        const phen = (alertObj.properties && alertObj.properties.vtec && alertObj.properties.vtec.phenomena) || '';
                        if (/TORNADO|TO\./i.test(head) || /TO\./i.test(phen)) type = 'tornado';
                        else if (/FLASH FLOOD|FLOOD|FF\./i.test(head) || /FF\./i.test(phen)) type = 'flood';

                        const emd = {
                            raw: raw,
                            time: isoTime,
                            type: type,
                            heading: (deg !== null) ? `${deg}DEG` : null,
                            speed: (kt !== null) ? `${kt}KT` : null,
                            lat: (typeof lat === 'number' && !isNaN(lat)) ? Number(lat.toFixed(2)) : null,
                            lon: (typeof lon === 'number' && !isNaN(lon)) ? Number(lon.toFixed(2)) : null,
                            coord: (typeof lat === 'number' && !isNaN(lat) && typeof lon === 'number' && !isNaN(lon)) ? `${lat.toFixed(2)},${lon.toFixed(2)}` : null
                        };

                        // keep only the top-level `eventMotionDescription` (it will be moved under `coordinates` when present)
                        alertObj.eventMotionDescription = emd;

                        // Ensure the formatted message includes two blank lines immediately after
                        // the TIME...MOT...LOC raw token, and ensure two blank lines before
                        // any "FLASH FLOOD" heading. This makes the displayed message match
                        // the user's requested spacing.
                        if (alertObj && alertObj.description && typeof alertObj.description === 'string' && raw) {
                            const esc = raw.replace(/[.*+?^${}()|[\\]\\]/g, '\\$&');
                            try {
                                alertObj.description = alertObj.description.replace(new RegExp(esc + '(?:\\s*)'), raw + '\n\n');
                            } catch (e) {
                                // If regex construction fails for any reason, fall back to simple replace
                                alertObj.description = alertObj.description.replace(raw, raw + '\n\n');
                            }

                            // Normalize any occurrence of FLASH FLOOD to have two leading newlines
                            alertObj.description = alertObj.description.replace(/\n*\s*FLASH\s+FLOOD/gi, '\n\nFLASH FLOOD');
                        }

                        // If the eventMotionDescription includes a valid lat/lon and no coordinates were already
                        // attached from LAT...LON or CAP polygon, promote it to `coordinates` so API consumers
                        // always receive a `coordinates` property when a point is available.
                        if (typeof emd.lat === 'number' && !isNaN(emd.lat) && typeof emd.lon === 'number' && !isNaN(emd.lon) &&
                            (!alertObj.coordinates || !alertObj.coordinates.length)) {
                            alertObj.coordinates = [[Number(emd.lat), Number(emd.lon)]];
                        }
                    }
                })();

                // Headline normalization removed per user request.

                // If `eventMotionDescription` exists, ensure it is serialized directly after `coordinates`.
                // Do NOT add the property when it does not exist — this preserves compact output.
                if (Object.prototype.hasOwnProperty.call(alertObj, 'eventMotionDescription') && alertObj.coordinates) {
                    const ordered = {};
                    for (const k of Object.keys(alertObj)) {
                        if (k === 'coordinates') {
                            ordered['coordinates'] = alertObj['coordinates'];
                            ordered['eventMotionDescription'] = alertObj['eventMotionDescription'];
                        } else if (k !== 'eventMotionDescription') {
                            ordered[k] = alertObj[k];
                        }
                    }
                    alertObj = ordered;
                }

                // --- START: build `alertinfo` object from message sections (WHAT / WHEN /WHERE / IMPACTS / threat fields) ---
                (function() {
                    // Helper: decode common escaped unicode sequences and HTML entities
                    function decodeEscapesAndEntities(s) {
                        if (!s || typeof s !== 'string') return s;
                        // Normalize escaped newline sequences first (e.g. "\\r\\n", "\\n\\", "\\n")
                        s = s.replace(/\\r\\n/g, '\\n').replace(/\\r/g, '\\n');
                        // Remove stray patterns like "\\n\\" -> "\\n"
                        s = s.replace(/\\n\\/g, '\\n');
                        // Convert literal "\\n" sequences into actual newlines
                        s = s.replace(/\\n/g, '\n');

                        // Convert literal unicode escape sequences like "\\u003C" -> '<'
                        s = s.replace(/\\u([0-9a-fA-F]{4})/g, function(_, g) {
                            try { return String.fromCharCode(parseInt(g, 16)); } catch (e) { return '' + _; }
                        });
                        // Numeric character references (hex & decimal)
                        s = s.replace(/&#x([0-9a-fA-F]+);/g, function(_, g) { return String.fromCharCode(parseInt(g,16)); });
                        s = s.replace(/&#([0-9]+);/g, function(_, g) { return String.fromCharCode(parseInt(g,10)); });
                        // Named HTML entities (common ones)
                        s = s.replace(/&lt;|&gt;|&amp;|&quot;|&apos;/gi, function(m){
                            switch(m.toLowerCase()){
                                case '&lt;': return '<';
                                case '&gt;': return '>';
                                case '&amp;': return '&';
                                case '&quot;': return '"';
                                case '&apos;': return "'";
                                default: return m;
                            }
                        });
                        // Trim accidental trailing whitespace from lines and normalize non-breaking spaces
                        return s.replace(/\s+$/gm, '').replace(/\u00A0/g, ' ');
                    }

                    // trim any preamble/headers before the first "HEADING..." line to avoid
                    // including the CAP preamble/product header in alertinfo fields
                    let srcText = (msgPart || alertObj.message || '');
                    srcText = String(srcText || '');
                    // decode any escaped unicode / HTML entities that might hide headings like "MAX WIND GUST" or "TORNADO"
                    srcText = decodeEscapesAndEntities(srcText);
                    // Trim any leading product preamble up to the first heading-like line.
                    // Accept optional bullet markers and a variety of heading delimiters ("...", ":", "—", "-", etc.).
                    srcText = srcText.replace(/^[\s\S]*?(?=\n?[ \t]*[\*\-\u2022\u25BA\u25CF]?\s*[A-Z0-9][A-Z0-9 \-\/&']{0,60}?(?:\.{2,}|:|\u2014|-{1,2}))/i, '');

                    const lines = srcText.split(/\r?\n/);
                    const secs = {}; // map of SECTION_NAME -> text
                    let cur = null;

                    // Collect sections that use the `HEADING...content` style (e.g. "WHAT...", "TORNADO...", "MAX HAIL SIZE...")
                        for (let rawLine of lines) {
                        // strip common bullet markers and surrounding whitespace (e.g. "* WHAT...", "- WHAT...", •)
                        const line = rawLine.trim();
                        if (!line) continue;
                        const stripped = line.replace(/^[\s\*\-\u2022\u25BA\u25CF]+/, '').trim();

                        // split on each heading token so a single line can contain multiple sections
                        // Split a line into heading/content pieces. Accept headings followed by
                        // ellipses ("..."), a colon, an em-dash, or hyphen separators. Case-insensitive.
                        const tokens = stripped.split(/([A-Z0-9][A-Z0-9 \-\/&']{0,60}?)(?:\.{2,}|:|\u2014|-{1,2})/i);
                        if (tokens.length > 1) {
                            for (let i = 1; i + 1 < tokens.length; i += 2) {
                                const heading = tokens[i].toUpperCase();
                                const contentRaw = (tokens[i + 1] || '').trim();
                                const content = decodeEscapesAndEntities(contentRaw);
                                if (content) {
                                    secs[heading] = secs[heading] ? (secs[heading] + ' ' + content) : content;
                                }
                                cur = heading; // set current section for possible continuations
                            }
                        } else if (cur) {
                            // continuation line for current section
                            const cont = decodeEscapesAndEntities(stripped);
                            secs[cur] = ((secs[cur] || '') + ' ' + cont).trim();
                        }
                    }

                    // helpers to format values
                    function fmtHail(s) {
                        if (!s) return '';
                        // capture an optional comparator and numeric portion
                        const m = String(s).match(/([<>~]?)\s*([0-9]*\.?[0-9]+)/);
                        if (!m) return String(s).trim();
                        const cmp = (m[1] || '');
                        let num = m[2];
                        if (/^0\./.test(num)) num = num.replace(/^0/, ''); // ".75" instead of "0.75"
                        // always treat hail sizes as inches when numeric only
                        const unit = /IN\b/i.test(s) ? 'IN' : 'IN';
                        return (cmp + num + ' ' + unit).trim();
                    }
                    function fmtWind(s) {
                        if (!s) return '';
                        // Accept optional comparator like <, >, or ~ followed by a number and optional unit
                        const m = String(s).trim().match(/^([<>~]?)\s*([0-9]{1,3})(?:\s*(MPH|KT|KTS))?/i);
                        if (!m) return String(s).trim();
                        const cmp = (m[1] || '').trim();
                        const num = m[2];
                        const unit = (m[3] || 'MPH').toUpperCase().replace('KTS', 'KT');
                        return (cmp + num + ' ' + unit).trim();
                    }

                    const ai = {};

                    // Primary narrative sections — only add if present as explicit headings in the message
                    if (secs['WHAT']) ai.WHAT = secs['WHAT'];
                    if (secs['WHEN']) ai.WHEN = secs['WHEN'];
                    if (secs['WHERE']) ai.WHERE = secs['WHERE'];
                    if (secs['IMPACTS']) ai.IMPACTS = secs['IMPACTS'];

                    // metadata-like sections (preserve exact-match behavior; do NOT conflate IMPACT and IMPACTS)
                    if (secs['HAZARD']) ai.HAZARD = secs['HAZARD'];
                    if (secs['SOURCE']) ai.SOURCE = secs['SOURCE'];
                    if (secs['IMPACT']) ai.IMPACT = secs['IMPACT'];

                    // damage / threat-specific values (set from headings when present)
                    // Only add a threat key when the decoded source text actually contains
                    // the corresponding hazard keyword/heading to avoid false positives.
                    const srcUpper = String(srcText || '').toUpperCase();
                    if (secs['TORNADO'] && /\bTORNADO\b/i.test(srcText)) {
                        let tornadoVal = secs['TORNADO'].trim().toUpperCase();
                        const tornadoMatch = tornadoVal.match(/^(POSSIBLE|OBSERVED|RADAR\s+INDICATED|CONFIRMED|LIKELY)/);
                        ai.TORNADO = tornadoMatch ? tornadoMatch[1] : tornadoVal.split(/[\s\-\$\&]/)[0];
                    }
                    if (secs['TORNADO DAMAGE THREAT'] && /\bTORNADO\s*DAMAGE\s*THREAT\b/i.test(srcText)) ai.TORNADO_DAMAGE_THREAT = secs['TORNADO DAMAGE THREAT'];
                    if (secs['THUNDERSTORM DAMAGE THREAT'] && /\bTHUNDERSTORM\b/i.test(srcText)) ai.THUNDERSTORM_DAMAGE_THREAT = secs['THUNDERSTORM DAMAGE THREAT'];
                    if (secs['FLASH FLOOD DAMAGE THREAT'] && /\bFLASH\s*FLOOD\b/i.test(srcText)) ai.FLASH_FLOOD_DAMAGE_THREAT = secs['FLASH FLOOD DAMAGE THREAT'];

                    // new threat fields requested by user; only add when keyword present
                    if (secs['HAIL THREAT'] && /\bHAIL\b/i.test(srcText)) ai.HAIL_THREAT = secs['HAIL THREAT'];
                    if (secs['WIND THREAT'] && /\bWIND\b/i.test(srcText)) ai.WIND_THREAT = secs['WIND THREAT'];
                    if (secs['FLASH FLOOD'] && /\bFLASH\s*FLOOD\b/i.test(srcText)) ai.FLASH_FLOOD = secs['FLASH FLOOD'];

                    // Do not auto-promote between long and short threat names; only keep
                    // keys that were explicitly present or captured by targeted fallbacks.

                    // numeric measurements (accept values from section headings)
                    if (secs['MAX HAIL SIZE'] || secs['MAX HAIL']) ai.MAX_HAIL_SIZE = fmtHail(secs['MAX HAIL SIZE'] || secs['MAX HAIL']);
                    if (secs['MAX WIND GUST'] || secs['MAX WIND']) ai.MAX_WIND_GUST = fmtWind(secs['MAX WIND GUST'] || secs['MAX WIND']);

                    // Fallback: search the entire message for certain values only if they were not set by headings
                    let full = String(srcText || '').replace(/\u00A0/g, ' ');
                    // Also decode any entities in the fallback/full text
                    full = decodeEscapesAndEntities(full);
                    function fallbackSet(key, re, formatter) {
                        if (Object.prototype.hasOwnProperty.call(ai, key) && ai[key]) return;
                        const m = full.match(re);
                        if (m && m[1]) ai[key] = formatter ? formatter(m[1]) : String(m[1]).trim();
                    }

                    // MAX HAIL / MAX WIND fallbacks (catch same-line pairs like "MAX HAIL SIZE...0.25 MAX WIND GUST...40")
                    fallbackSet('MAX_HAIL_SIZE', /MAX\s*HAIL(?:\s*SIZE)?\.{2,}\s*([<>~]?\s*[0-9]*\.?[0-9]+)/i, fmtHail);
                    // Allow optional comparator (<, >, ~) before the numeric wind value
                    fallbackSet('MAX_WIND_GUST', /MAX\s*WIND(?:\s*GUST)?\.{2,}\s*([<>~]?\s*[0-9]{1,3})/i, fmtWind);
                    // Broad fallback: catch cases where the separator or comparator may be encoded
                    fallbackSet('MAX_WIND_GUST', /MAX\s*WIND(?:\s*GUST)?[\s\S]{0,30}?([<>~]?\s*[0-9]{1,3})/i, fmtWind);

                    // Threat fallbacks: only apply fallback extraction when the corresponding
                    // keyword actually appears in the message text. This avoids adding
                    // threat fields when the message doesn't mention that hazard.
                    const hailThreatRe = /HAIL(?:\s+(?:DAMAGE\s+)?THREAT(?:\(S\))?)?\.{2,}\s*([A-Z][A-Z\s\-]+)/i;
                    const windThreatRe = /WIND(?:\s+(?:DAMAGE\s+)?THREAT(?:\(S\))?)?\.{2,}\s*([A-Z][A-Z\s\-]+)/i;

                    const hasTornado = /\bTORNADO\b/i.test(full);
                    const hasHail = /\bHAIL\b/i.test(full);
                    const hasWind = /\bWIND\b/i.test(full);
                    const hasFlash = /\bFLASH\s*FLOOD\b/i.test(full);
                    const hasThunder = /\bTHUNDERSTORM\b/i.test(full);

                    if (hasHail) fallbackSet('HAIL_THREAT', hailThreatRe, s => s.trim());
                    if (hasWind) fallbackSet('WIND_THREAT', windThreatRe, s => s.trim());
                    // Thunderstorm damage threat: similar fallback when explicit heading wasn't parsed
                    if (hasThunder) fallbackSet('THUNDERSTORM_DAMAGE_THREAT', /THUNDERSTORM(?:\s+(?:DAMAGE\s+)?THREAT(?:\(S\))?)?\.{2,}\s*([A-Z][A-Z\s\-]+)/i, s => s.trim());
                    // NOTE: Do NOT add fallback for FLASH_FLOOD_DAMAGE_THREAT — only use explicit headings

                    // Also populate short-form FLASH_FLOOD only if the message mentions flash flood
                    if (hasFlash && !ai.FLASH_FLOOD) {
                        const mff = full.match(/(^|\n)FLASH\s*FLOOD(?:\s*[:\.]|\s+)([A-Z][A-Z\s\-]{0,40}?)(?=\s*$|\s*\n|(?:\s+(?:IN|AT|WILL|FOR|FROM|TO)))/i);
                        if (mff && mff[2]) ai.FLASH_FLOOD = mff[2].trim();
                    }

                    // Also attempt to populate `TORNADO` from inline sentences when not set by headings
                    // but only if the message actually contains the word "TORNADO".
                    if (!ai.TORNADO && hasTornado) {
                        const mt = full.match(/(^|\n)TORNADO(?:\s*[:\.]|\s+)([A-Z][A-Z\s\-]{0,40}?)(?=\s*$|\s*\n|(?:\s+(?:IN|AT|WILL|FOR|FROM|TO)))/i);
                        if (mt && mt[2]) ai.TORNADO = mt[2].trim();
                    }

                    // attach under the exact name the request used (only keys with values are present)
                    // --- Simplify and canonicalize threat fields (user request):
                    // convert long/freeform values into short canonical phrases (e.g. "RADAR INDICATED", "POSSIBLE", "CONSIDERABLE")
                    function simplifyThreatValue(v) {
                        if (!v) return v;
                        let s = String(v).trim();
                        if (!s) return s;
                        const up = s.toUpperCase();

                        // First, try to extract just the core threat indicator by stopping at "MAX" or other breaking points
                        const truncated = up.replace(/\s+(MAX|SIZE|HAIL|WIND|GUST|SPEED|DAMAGE|IMPACT|DEPTH|ACCUMULATION|RATE).*$/i, '').trim();
                        const core = truncated || up;

                        // Prefer to detect RADAR-based indicators
                        if (core.includes('RADAR INDICATED')) return 'RADAR INDICATED';
                        if (core.includes('RADAR ESTIMAT') || core.includes('RADAR-ESTIMAT')) return 'RADAR ESTIMATED';

                        // Common short keywords we want to preserve
                        if (/\bPOSSIBLE\b/.test(core)) return 'POSSIBLE';
                        if (/\bCONSIDERABLE\b/.test(core)) return 'CONSIDERABLE';
                        if (/\bDESTRUCTIVE\b/.test(core)) return 'DESTRUCTIVE';
                        if (/\bCATASTROPHIC\b/.test(core)) return 'CATASTROPHIC';
                        if (/\bNONE\b/.test(core)) return 'NONE';
                        if (/\bLIKELY\b/.test(core)) return 'LIKELY';
                        if (/\bCONFIRMED\b/.test(core)) return 'CONFIRMED';

                        // If the core string is already short (<= 30 chars) keep it as-is (cleaned)
                        if (core.length <= 30) return core;

                        // Otherwise return the first few words up to punctuation/newline/break
                        const m = core.match(/^([^\n\.,;:\$]{1,60})/);
                        return (m && m[1]) ? m[1].trim() : up.trim();
                    }

                    const _threatKeys = ['HAIL_THREAT','WIND_THREAT','TORNADO','TORNADO_DAMAGE_THREAT','FLASH_FLOOD_DAMAGE_THREAT','THUNDERSTORM_DAMAGE_THREAT','FLASH_FLOOD'];
                    for (const tk of _threatKeys) {
                        if (Object.prototype.hasOwnProperty.call(ai, tk) && ai[tk]) ai[tk] = simplifyThreatValue(ai[tk]);
                    }

                    // If we extracted a smart NWS headline earlier, append it at the bottom
                    // of the `alertinfo` object so it appears after the other fields.
                    if (typeof extractedNWSHeadline !== 'undefined' && extractedNWSHeadline) {
                        ai.NWSHeadline = extractedNWSHeadline;
                    }

                    alertObj.alertinfo = ai;
                })();
                // --- END: alertinfo build ---

                parsedAlerts.push(alertObj);
            }

            // Remove any null/undefined entries (in case)
            parsedAlerts = parsedAlerts.filter(Boolean);

            // ===================== DEDUPLICATION LOGIC ===========================
            try {
                let alerts = [];

                try {
                    const raw = fs.readFileSync('alerts.json', 'utf8');
                    alerts = raw.trim() ? JSON.parse(raw) : [];
                    if (!Array.isArray(alerts)) alerts = [];
                } catch (readErr) {
                    // If the file is missing or malformed, start fresh
                    if (readErr.code !== 'ENOENT') {
                        console.warn('alerts.json unreadable, recreating file:', readErr.message);
                        log('alerts.json unreadable, recreating file: ' + readErr.message);
                    }
                    alerts = [];
                }

                // For each parsedAlert, remove any existing alert with the same id, then add the new one
                parsedAlerts.forEach(parsedAlert => {
                    const alertId = parsedAlert.id;
                    if (alertId) {
                        const removedAlerts = alerts.filter(alert => alert.id === alertId);
                        if (removedAlerts.length > 0) {
                            removedAlerts.forEach(removedAlert => {
                                console.log(`✗ Alert removed: ${removedAlert.name} (ID: ${removedAlert.id})`);
                                log('Alert removed: ' + removedAlert.name + ' (ID: ' + removedAlert.id + ')');
                            });
                        }
                        alerts = alerts.filter(alert => {
                            return !(alert.id === alertId);
                        });
                    }
                    // Filtering rules (per user request):
                    // - If the alert name matches a phenomenon entry in phenomena.json AND there is no VTEC, skip it.
                    // - If the alert has a VTEC, allow it regardless of name.
                    // - If the alert has no VTEC but its name appears in allowedalerts.json, allow it.
                    try {
                        const name = String((parsedAlert.event || parsedAlert.name) || '').trim();
                        // Skip alerts that are Area Forecast Discussions embedded in the description
                        try {
                            if (parsedAlert.description && /Area\s+Forecast\s+Discussion/i.test(parsedAlert.description)) {
                                console.log(`Skipping alert (Area Forecast Discussion in description): ${name || parsedAlert.id}`);
                                log('Skipping alert (Area Forecast Discussion in description): ' + (name || parsedAlert.id));
                                return; // skip adding this parsedAlert
                            }
                        } catch (e) {
                            // If the check fails for any reason, continue normal processing
                        }
                        // Consider a VTEC 'present' only when phenomena and significance are available
                        const hasFullVtec = parsedAlert.properties && parsedAlert.properties.vtec && parsedAlert.properties.vtec.phenomena && parsedAlert.properties.vtec.significance;
                        // Treat an alert as a phenomena match when the alert name contains
                        // a phenomena.json `name` token as a whole word (e.g. "Tornado Warning"
                        // should match phenomena name "Tornado"). Use word-boundary regex to
                        // avoid accidental partial matches.
                        function _escapeRe(s) { return String(s).replace(/[.*+?^${}()|[\\]\\]/g, '\\$&'); }
                        const nameInPhenomena = name && Object.values(phenomena).some(p => {
                            if (!p || !p.name) return false;
                            const ph = String(p.name).trim();
                            if (!ph) return false;
                            const re = new RegExp('\\b' + _escapeRe(ph) + '\\b', 'i');
                            return re.test(name);
                        });

                        if (nameInPhenomena && !hasFullVtec) {
                            console.log(`Skipping alert (phenomena match, no VTEC): ${name}`);
                            log('Skipping alert (phenomena match, no VTEC): ' + name);
                            return; // skip adding this parsedAlert
                        }

                        if (!hasFullVtec) {
                            // No VTEC: allow only if explicitly listed in allowedalerts.json
                            const allowed = Array.isArray(allowedAlerts) && allowedAlerts.some(a => String(a || '').toUpperCase() === name.toUpperCase());
                            if (!allowed) {
                                console.log(`Skipping alert (no VTEC and not allowed): ${name}`);
                                log('Skipping alert (no VTEC and not allowed): ' + name);
                                return;
                            }
                        }
                    } catch (e) {
                        // If filtering check fails for any reason, default to storing the alert to avoid data loss
                        console.warn('Alert filtering error, defaulting to store:', e && e.message);
                    }

                    alerts.push(parsedAlert);
                    const storedName = String((parsedAlert.event || parsedAlert.name) || '').trim();
                    console.log(`✓ Alert stored successfully: ${storedName} (ID: ${parsedAlert.id})`);
                    log('Alert stored successfully: ' + storedName + ' (ID: ' + parsedAlert.id + ')');
                });
                fs.writeFileSync('alerts.json', JSON.stringify(alerts, null, 2));
            } catch (err) {
                console.error('Error updating alerts.json:', err);
                log('Error updating alerts.json:', err);
            }
            // ===================== END DEDUPLICATION LOGIC ===========================
        });

    });

    // Event listener for errors
    xmpp.on('error', (err) => {
        console.error('XMPP error:', err);
        log('XMPP error: ' + err.toString());
        
        // Handle DNS/network errors with reconnection
        if (err.errno === -3001 || err.code === 'EAI_AGAIN' || err.code === 'ENOTFOUND' || err.code === 'ETIMEDOUT') {
            console.log('Network error detected, attempting reconnection...');
            log('Network error detected: ' + err.code + ' - Initiating reconnection.');
            handleReconnect();
            return;
        }
        
        // Clean up interval on error
        if (deleteExpiredAlertsInterval) {
            clearInterval(deleteExpiredAlertsInterval);
            deleteExpiredAlertsInterval = null;
        }
    });

    // Clean up interval when offline
    xmpp.on('offline', () => {
        log("Connection offline")
        console.log('XMPP connection offline');
        if (deleteExpiredAlertsInterval) {
            clearInterval(deleteExpiredAlertsInterval);
            deleteExpiredAlertsInterval = null;
        }
    });

    // Start the connection
    try {
        await xmpp.start();
    } catch (err) {
        // Handle authentication errors
        if (err.toString().includes('not-authorized')) {
            console.error('XMPP Authentication failed: Check your username and password in the .env file.');
            log('XMPP Authentication failed: Check your username and password.');
            process.exit(1);
        }
        
        // Handle DNS/network errors with reconnection
        if (err.errno === -3001 || err.code === 'EAI_AGAIN' || err.code === 'ENOTFOUND' || err.code === 'ETIMEDOUT') {
            console.error('Network/DNS error connecting to XMPP server:', err.message);
            log('Network/DNS error: ' + err.message + ' - Will retry connection.');
            handleReconnect();
            return;
        }
        
        console.error('\nFailed to start XMPP client:', err);
        log('Failed to start XMPP client: ' + err);
        process.exit(1);
    }

})().catch(err => {
    console.error('\nAn error occurred:', err);
    log('An error occurred: ' + err);
    console.log('Restarting in 5 seconds...');
    setTimeout(() => { }, 5000);
});

// Exports
module.exports = {
    start: async () => { 
        console.log('NWWS-OI module start() called');
    },
    auth: (a, b, c, d, e) => {
        username = a;
        password = b; 
        resource = c || 'SparkAlerts NWWS Ingest Client';
        MAX_RECONNECT_ATTEMPTS = d || 10;
        INITIAL_RECONNECT_DELAY = e || 2000;
        console.log(`NWWS-OI configured: User=${username}, Resource=${resource}, MaxRetries=${MAX_RECONNECT_ATTEMPTS}`);
    }
};
