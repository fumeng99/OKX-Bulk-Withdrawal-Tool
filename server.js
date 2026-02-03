/**
 * OKX 批量提币工具 - 后端服务 (安全增强版)
 * 使用 HTTPS + Session Token 保护本地通信
 * 纯 JavaScript 实现，无需 OpenSSL
 */

const http = require('http');
const fs = require('fs');
const path = require('path');
const crypto = require('crypto');
const https = require('https');
const { URL } = require('url');

const MAX_BODY_SIZE = 1024 * 10;
const PROXY_URL = process.env.PROXY_URL || '';
const SESSION_TOKEN = crypto.randomBytes(16).toString('hex');
const ENCRYPTION_KEY = crypto.randomBytes(32).toString('hex');

// 🔒 传输层加密配置（每次启动随机生成）
const TRANSPORT_KEY = crypto.randomBytes(32).toString('hex');
const TRANSPORT_IV = crypto.randomBytes(16).toString('hex').slice(0, 16);

// 🔒 传输层加密（加密 API 响应）
function encryptTransport(plainText) {
    try {
        const key = crypto.createHash('sha256').update(TRANSPORT_KEY).digest();
        const ivBuffer = Buffer.from(TRANSPORT_IV, 'utf8');
        const cipher = crypto.createCipheriv('aes-256-cbc', key, ivBuffer);
        cipher.setAutoPadding(true);
        const encrypted = Buffer.concat([cipher.update(plainText, 'utf8'), cipher.final()]);
        return encrypted.toString('base64');
    } catch (e) {
        return null;
    }
}

// 🔒 传输层解密（解密 API 请求）
function decryptTransport(encryptedBase64) {
    try {
        const key = crypto.createHash('sha256').update(TRANSPORT_KEY).digest();
        const ivBuffer = Buffer.from(TRANSPORT_IV, 'utf8');
        const encrypted = Buffer.from(encryptedBase64, 'base64');
        const decipher = crypto.createDecipheriv('aes-256-cbc', key, ivBuffer);
        decipher.setAutoPadding(true);
        const decrypted = Buffer.concat([decipher.update(encrypted), decipher.final()]);
        return decrypted.toString('utf8');
    } catch (e) {
        return null;
    }
}

function decryptAES(encryptedHex) {
    try {
        if (!encryptedHex || typeof encryptedHex !== 'string') return null;
        if (encryptedHex.length < 32) return null;
        const iv = Buffer.from(encryptedHex.slice(0, 32), 'hex');
        const encrypted = Buffer.from(encryptedHex.slice(32), 'hex');
        const key = Buffer.from(ENCRYPTION_KEY, 'hex');
        const decipher = crypto.createDecipheriv('aes-256-cbc', key, iv);
        let decrypted = decipher.update(encrypted);
        decrypted = Buffer.concat([decrypted, decipher.final()]);
        return decrypted.toString('utf8');
    } catch (e) {
        console.error('decryptAES 解密失败:', e.message);
        return null;
    }
}

// 🔒 生成请求 ID
function generateRequestId() {
    return `${Date.now().toString(36)}-${crypto.randomBytes(4).toString('hex')}`;
}

// 🔒 清除敏感信息
function clearSensitiveData(obj) {
    if (obj && typeof obj === 'object') {
        if (obj.apiKey) obj.apiKey = null;
        if (obj.secretKey) obj.secretKey = null;
        if (obj.passphrase) obj.passphrase = null;
        if (obj.signature) obj.signature = null;
    }
}

const asn1 = {
    encodeLength(len) {
        if (len < 128) return Buffer.from([len]);
        const bytes = [];
        let temp = len;
        while (temp > 0) { bytes.unshift(temp & 0xff); temp >>= 8; }
        return Buffer.concat([Buffer.from([0x80 | bytes.length]), Buffer.from(bytes)]);
    },
    encodeTLV(tag, value) {
        return Buffer.concat([Buffer.from([tag]), this.encodeLength(value.length), value]);
    },
    sequence(...items) { return this.encodeTLV(0x30, Buffer.concat(items)); },
    set(...items) { return this.encodeTLV(0x31, Buffer.concat(items)); },
    integer(value) {
        if (Buffer.isBuffer(value)) {
            if (value[0] & 0x80) value = Buffer.concat([Buffer.from([0x00]), value]);
            return this.encodeTLV(0x02, value);
        }
        const bytes = [];
        let v = BigInt(value);
        do { bytes.unshift(Number(v & 0xffn)); v >>= 8n; } while (v > 0n);
        if (bytes[0] & 0x80) bytes.unshift(0);
        return this.encodeTLV(0x02, Buffer.from(bytes));
    },
    bitString(value) { return this.encodeTLV(0x03, Buffer.concat([Buffer.from([0x00]), value])); },
    octetString(value) { return this.encodeTLV(0x04, value); },
    null() { return Buffer.from([0x05, 0x00]); },
    oid(oidString) {
        const parts = oidString.split('.').map(Number);
        const bytes = [parts[0] * 40 + parts[1]];
        for (let i = 2; i < parts.length; i++) {
            let n = parts[i];
            if (n === 0) { bytes.push(0); }
            else {
                const temp = [];
                while (n > 0) { temp.unshift((n & 0x7f) | (temp.length ? 0x80 : 0)); n >>= 7; }
                bytes.push(...temp);
            }
        }
        return this.encodeTLV(0x06, Buffer.from(bytes));
    },
    utf8String(str) { return this.encodeTLV(0x0c, Buffer.from(str, 'utf8')); },
    utcTime(date) {
        const y = date.getUTCFullYear() % 100;
        const m = String(date.getUTCMonth() + 1).padStart(2, '0');
        const d = String(date.getUTCDate()).padStart(2, '0');
        const h = String(date.getUTCHours()).padStart(2, '0');
        const min = String(date.getUTCMinutes()).padStart(2, '0');
        const s = String(date.getUTCSeconds()).padStart(2, '0');
        return this.encodeTLV(0x17, Buffer.from(`${String(y).padStart(2, '0')}${m}${d}${h}${min}${s}Z`, 'ascii'));
    },
    contextTag(tagNum, value, constructed = true) {
        return this.encodeTLV(0xa0 | tagNum | (constructed ? 0x20 : 0), value);
    }
};

function generateSelfSignedCertificate() {
    const { publicKey, privateKey } = crypto.generateKeyPairSync('rsa', {
        modulusLength: 2048,
        publicKeyEncoding: { type: 'spki', format: 'der' },
        privateKeyEncoding: { type: 'pkcs8', format: 'pem' }
    });
    const notBefore = new Date();
    const notAfter = new Date(notBefore.getTime() + 365 * 24 * 60 * 60 * 1000);
    const serialNumber = crypto.randomBytes(8);
    serialNumber[0] &= 0x7f;
    const issuerName = asn1.sequence(asn1.set(asn1.sequence(asn1.oid('2.5.4.3'), asn1.utf8String('localhost'))));
    const signatureAlgorithm = asn1.sequence(asn1.oid('1.2.840.113549.1.1.11'), asn1.null());
    const validity = asn1.sequence(asn1.utcTime(notBefore), asn1.utcTime(notAfter));
    const sanExtension = asn1.sequence(asn1.oid('2.5.29.17'), asn1.octetString(asn1.sequence(
        Buffer.concat([Buffer.from([0x82]), asn1.encodeLength(9), Buffer.from('localhost')]),
        Buffer.concat([Buffer.from([0x87, 0x04, 127, 0, 0, 1])])
    )));
    const basicConstraints = asn1.sequence(asn1.oid('2.5.29.19'), asn1.octetString(asn1.sequence()));
    const extensions = asn1.contextTag(3, asn1.sequence(basicConstraints, sanExtension));
    const tbsCertificate = asn1.sequence(
        asn1.contextTag(0, asn1.integer(2), false), asn1.integer(serialNumber), signatureAlgorithm,
        issuerName, validity, issuerName, Buffer.from(publicKey), extensions
    );
    const sign = crypto.createSign('SHA256');
    sign.update(tbsCertificate);
    const signature = sign.sign(privateKey);
    const certificate = asn1.sequence(tbsCertificate, signatureAlgorithm, asn1.bitString(signature));
    return {
        cert: '-----BEGIN CERTIFICATE-----\n' + certificate.toString('base64').match(/.{1,64}/g).join('\n') + '\n-----END CERTIFICATE-----\n',
        key: privateKey
    };
}

function signOKX(timestamp, method, requestPath, body, secretKey) {
    return crypto.createHmac('sha256', secretKey).update(timestamp + method + requestPath + (body || '')).digest('base64');
}

function getISOTimestamp() { return new Date().toISOString(); }

function parseProxy(proxyStr) {
    if (!proxyStr) return null;
    proxyStr = proxyStr.trim();
    if (/^(https?|socks5?):\/\//i.test(proxyStr)) {
        try {
            const url = new URL(proxyStr);
            return { host: url.hostname, port: parseInt(url.port) || 80, username: url.username ? decodeURIComponent(url.username) : null, password: url.password ? decodeURIComponent(url.password) : null };
        } catch (e) { return null; }
    }
    if (proxyStr.includes('@')) {
        const [auth, hostPort] = proxyStr.split('@');
        const [user, pass] = auth.split(':');
        const [host, port] = hostPort.split(':');
        if (host && port) return { host, port: parseInt(port) || 80, username: user || null, password: pass || null };
    }
    const parts = proxyStr.split(':');
    if (parts.length === 4) return { host: parts[0], port: parseInt(parts[1]) || 80, username: parts[2] || null, password: parts[3] || null };
    if (parts.length === 2) return { host: parts[0], port: parseInt(parts[1]) || 80, username: null, password: null };
    return null;
}

function httpsRequest(options, postData = null, proxyUrl = null) {
    const effectiveProxy = proxyUrl || PROXY_URL;
    return new Promise((resolve, reject) => {
        const makeRequest = (socket = null) => {
            const reqOptions = { ...options };
            if (socket) { reqOptions.socket = socket; reqOptions.agent = false; }
            const req = https.request(reqOptions, (res) => {
                let data = '';
                res.on('data', chunk => data += chunk);
                res.on('end', () => {
                    try { resolve({ status: res.statusCode, data: JSON.parse(data) }); }
                    catch (e) { resolve({ status: res.statusCode, data: data }); }
                });
            });
            req.on('error', reject);
            if (postData) req.write(postData);
            req.end();
        };
        const proxyConfig = parseProxy(effectiveProxy);
        if (proxyConfig) {
            const connectOptions = {
                host: proxyConfig.host, port: proxyConfig.port, method: 'CONNECT',
                path: `${options.hostname}:${options.port || 443}`,
                headers: { 'Host': `${options.hostname}:${options.port || 443}` }
            };
            if (proxyConfig.username) {
                connectOptions.headers['Proxy-Authorization'] = `Basic ${Buffer.from(`${proxyConfig.username}:${proxyConfig.password || ''}`).toString('base64')}`;
            }
            const proxyReq = http.request(connectOptions);
            proxyReq.on('connect', (res, socket) => {
                if (res.statusCode === 200) makeRequest(socket);
                else reject(new Error(`代理连接失败: ${res.statusCode}`));
            });
            proxyReq.on('error', (e) => reject(new Error(`代理错误: ${e.message}`)));
            proxyReq.end();
        } else { makeRequest(); }
    });
}

// 🔒 安全的 Session Token 验证（防止时序攻击）
function validateSessionToken(req, res) {
    const token = req.headers['x-session-token'];
    if (!token || token.length !== SESSION_TOKEN.length) {
        res.writeHead(401, { 'Content-Type': 'application/json' });
        res.end(JSON.stringify({ error: 'Session Token 无效或缺失' }));
        return false;
    }

    // 使用时序安全比较防止时序攻击
    try {
        const tokenBuffer = Buffer.from(token, 'utf8');
        const sessionBuffer = Buffer.from(SESSION_TOKEN, 'utf8');
        if (!crypto.timingSafeEqual(tokenBuffer, sessionBuffer)) {
            res.writeHead(401, { 'Content-Type': 'application/json' });
            res.end(JSON.stringify({ error: 'Session Token 无效' }));
            return false;
        }
    } catch (e) {
        res.writeHead(401, { 'Content-Type': 'application/json' });
        res.end(JSON.stringify({ error: 'Session Token 验证失败' }));
        return false;
    }
    return true;
}

// 🔒 完整的安全响应头
function setSecurityHeaders(res) {
    // 防止点击劫持
    res.setHeader('X-Frame-Options', 'DENY');
    // 防止 MIME 类型嗅探
    res.setHeader('X-Content-Type-Options', 'nosniff');
    // XSS 保护
    res.setHeader('X-XSS-Protection', '1; mode=block');
    // 内容安全策略
    res.setHeader('Content-Security-Policy', "default-src 'self'; script-src 'self' 'unsafe-inline'; style-src 'self' 'unsafe-inline'; font-src 'self' https://fonts.gstatic.com https://fonts.googleapis.com; img-src 'self' data:");
    // Referrer 策略
    res.setHeader('Referrer-Policy', 'strict-origin-when-cross-origin');
    // 禁止缓存敏感数据
    res.setHeader('Cache-Control', 'no-store, no-cache, must-revalidate, private');
    res.setHeader('Pragma', 'no-cache');
}

async function handleApiRequest(req, res, body) {
    const requestId = generateRequestId();

    setSecurityHeaders(res);
    res.setHeader('Content-Type', 'application/json');
    res.setHeader('X-Request-ID', requestId);
    res.setHeader('Access-Control-Allow-Origin', req.headers.origin || `https://${req.headers.host}`);

    if (!validateSessionToken(req, res)) return;

    let sensitiveData = null;
    try {
        let data = JSON.parse(body);

        // 🔒 传输层解密
        if (data.encrypted && data.data) {
            const decrypted = decryptTransport(data.data);
            if (!decrypted) {
                res.writeHead(400);
                res.end(JSON.stringify({ error: '传输解密失败' }));
                return;
            }
            data = JSON.parse(decrypted);
        }

        const { action, apiKey: encApiKey, secretKey: encSecretKey, passphrase: encPassphrase, proxyUrl, params } = data;
        sensitiveData = { apiKey: null, secretKey: null, passphrase: null }; // 准备清理引用

        if (!encApiKey || !encSecretKey || !encPassphrase) {
            res.writeHead(400);
            res.end(JSON.stringify({ error: '缺少 API Key、Secret Key 或 Passphrase' }));
            return;
        }

        const apiKey = decryptAES(encApiKey);
        const secretKey = decryptAES(encSecretKey);
        const passphrase = decryptAES(encPassphrase);

        if (!apiKey || !secretKey || !passphrase) {
            res.writeHead(400);
            res.end(JSON.stringify({ error: '解密失败，请检查加密密钥是否正确' }));
            return;
        }

        const timestamp = getISOTimestamp();
        const headers = {
            'Content-Type': 'application/json',
            'OK-ACCESS-KEY': apiKey,
            'OK-ACCESS-TIMESTAMP': timestamp,
            'OK-ACCESS-PASSPHRASE': passphrase
        };

        if (action === 'withdraw') {
            const { ccy, chain, toAddr, amt } = params;
            const requestPath = '/api/v5/asset/withdrawal';
            const bodyData = JSON.stringify({ ccy, amt: String(amt), dest: '4', toAddr, chain });
            headers['OK-ACCESS-SIGN'] = signOKX(timestamp, 'POST', requestPath, bodyData, secretKey);
            const result = await httpsRequest({ hostname: 'www.okx.com', port: 443, path: requestPath, method: 'POST', headers }, bodyData, proxyUrl);
            if (result.data.code === '0') {
                res.writeHead(200);
                res.end(JSON.stringify({ success: true, data: result.data.data, wdId: result.data.data[0]?.wdId }));
            } else {
                res.writeHead(400);
                res.end(JSON.stringify({ error: result.data.msg || '提币失败', code: result.data.code }));
            }
        } else if (action === 'currencies') {
            const requestPath = '/api/v5/asset/currencies';
            headers['OK-ACCESS-SIGN'] = signOKX(timestamp, 'GET', requestPath, '', secretKey);
            delete headers['Content-Type'];
            const result = await httpsRequest({ hostname: 'www.okx.com', port: 443, path: requestPath, method: 'GET', headers }, null, proxyUrl);
            res.writeHead(result.data.code === '0' ? 200 : 400);
            res.end(JSON.stringify(result.data.code === '0' ? result.data.data : { error: result.data.msg }));
        } else if (action === 'balance') {
            const requestPath = '/api/v5/asset/balances';
            headers['OK-ACCESS-SIGN'] = signOKX(timestamp, 'GET', requestPath, '', secretKey);
            delete headers['Content-Type'];
            const result = await httpsRequest({ hostname: 'www.okx.com', port: 443, path: requestPath, method: 'GET', headers }, null, proxyUrl);
            res.writeHead(result.data.code === '0' ? 200 : 400);
            res.end(JSON.stringify(result.data.code === '0' ? result.data.data : { error: result.data.msg }));
        } else if (action === 'price') {
            const { symbol } = params;
            if (['USDT', 'USDC', 'DAI', 'FDUSD'].includes(symbol?.toUpperCase())) {
                res.writeHead(200);
                res.end(JSON.stringify({ symbol, price: '1' }));
                return;
            }
            const result = await httpsRequest({ hostname: 'www.okx.com', port: 443, path: `/api/v5/market/ticker?instId=${symbol}-USDT`, method: 'GET' }, null, proxyUrl);
            res.writeHead(200);
            res.end(JSON.stringify(result.data.code === '0' && result.data.data?.[0] ? { symbol, price: result.data.data[0].last } : { symbol, price: null }));
        } else {
            res.writeHead(400);
            res.end(JSON.stringify({ error: '未知操作' }));
        }
    } catch (e) {
        console.error('API 错误:', e);
        res.writeHead(500);
        res.end(JSON.stringify({ error: e.message, requestId }));
    } finally {
        // 🔒 清理敏感数据
        if (sensitiveData) {
            clearSensitiveData(sensitiveData);
        }
    }
}

function handleRequest(req, res) {
    const parsedUrl = new URL(req.url, `https://${req.headers.host}`);
    const pathname = parsedUrl.pathname;

    if (req.method === 'OPTIONS') {
        res.setHeader('Access-Control-Allow-Origin', req.headers.origin || '*');
        res.setHeader('Access-Control-Allow-Methods', 'GET, POST, OPTIONS');
        res.setHeader('Access-Control-Allow-Headers', 'Content-Type, X-Session-Token');
        res.writeHead(204);
        res.end();
        return;
    }

    if (pathname === '/api' && req.method === 'POST') {
        let body = '';
        req.on('data', chunk => { body += chunk; if (body.length > MAX_BODY_SIZE) req.destroy(); });
        req.on('end', () => handleApiRequest(req, res, body));
        return;
    }

    if (pathname === '/api/key' && req.method === 'GET') {
        setSecurityHeaders(res);
        res.setHeader('Content-Type', 'application/json');
        res.setHeader('Access-Control-Allow-Origin', req.headers.origin || '*');
        if (!validateSessionToken(req, res)) return;
        res.writeHead(200);
        res.end(JSON.stringify({ encryptionKey: ENCRYPTION_KEY }));
        return;
    }

    // 🔒 传输层密钥配置 API（前端获取动态生成的密钥）
    if (pathname === '/api/transport-config' && req.method === 'GET') {
        setSecurityHeaders(res);
        res.setHeader('Content-Type', 'application/json');
        res.setHeader('Access-Control-Allow-Origin', req.headers.origin || '*');
        if (!validateSessionToken(req, res)) return;
        res.writeHead(200);
        res.end(JSON.stringify({ key: TRANSPORT_KEY, iv: TRANSPORT_IV }));
        return;
    }

    // 代理测试端点
    if (pathname === '/api/proxy-test' && req.method === 'POST') {
        let body = '';
        req.on('data', chunk => { body += chunk; if (body.length > MAX_BODY_SIZE) req.destroy(); });
        req.on('end', async () => {
            setSecurityHeaders(res);
            res.setHeader('Content-Type', 'application/json');
            res.setHeader('Access-Control-Allow-Origin', req.headers.origin || '*');
            if (!validateSessionToken(req, res)) return;

            try {
                const data = JSON.parse(body);
                const { proxyUrl } = data;

                if (!proxyUrl) {
                    res.writeHead(400);
                    res.end(JSON.stringify({ success: false, error: '请输入代理地址' }));
                    return;
                }

                const startTime = Date.now();

                // 使用 ip-api.com 检测代理IP和国家
                const result = await httpsRequest({
                    hostname: 'ipinfo.io',
                    port: 443,
                    path: '/json',
                    method: 'GET',
                    headers: { 'Accept': 'application/json' }
                }, null, proxyUrl);

                const latency = Date.now() - startTime;

                if (result.data && result.data.ip) {
                    res.writeHead(200);
                    res.end(JSON.stringify({
                        success: true,
                        ip: result.data.ip,
                        country: result.data.country || result.data.region || 'Unknown',
                        latency: latency
                    }));
                } else {
                    res.writeHead(200);
                    res.end(JSON.stringify({ success: false, error: '无法获取代理信息' }));
                }
            } catch (e) {
                res.writeHead(200);
                res.end(JSON.stringify({ success: false, error: e.message }));
            }
        });
        return;
    }

    let filePath = pathname === '/' ? '/index.html' : pathname;
    filePath = path.resolve(path.join(__dirname, filePath));
    if (!filePath.startsWith(path.resolve(__dirname))) { res.writeHead(403); res.end('Forbidden'); return; }

    const contentTypes = { '.html': 'text/html', '.js': 'text/javascript', '.css': 'text/css', '.json': 'application/json', '.png': 'image/png' };
    fs.readFile(filePath, (err, content) => {
        if (err) { res.writeHead(err.code === 'ENOENT' ? 404 : 500); res.end(err.code === 'ENOENT' ? '404' : 'Error'); }
        else { res.setHeader('Content-Type', contentTypes[path.extname(filePath)] || 'text/plain'); res.writeHead(200); res.end(content); }
    });
}

function startServer() {
    let server, protocol = 'https';
    try {
        const { cert, key } = generateSelfSignedCertificate();
        server = https.createServer({ cert, key }, handleRequest);
    } catch (e) {
        server = http.createServer(handleRequest);
        protocol = 'http';
    }

    server.listen(0, '127.0.0.1', () => {
        const PORT = server.address().port;
        console.clear();
        console.log(`
============================================================
  OKX 批量提币工具 v1.0
============================================================

  访问地址: ${protocol}://127.0.0.1:${PORT}

  Session Token: ${SESSION_TOKEN.match(/.{1,4}/g).join('-')}

============================================================
  Twitter: @Nadiinn5 | 按 Ctrl+C 停止服务
============================================================
`);
    });
}

startServer();
