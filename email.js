import { existsSync, open, read, closeSync, close } from 'fs';
import { hostname } from 'os';
import { Stream } from 'stream';
import { TextEncoder, TextDecoder } from 'util';
import { createHmac } from 'crypto';
import { EventEmitter } from 'events';
import { Socket } from 'net';
import { connect, TLSSocket, createSecureContext } from 'tls';

const OPERATORS = new Map([
    ['"', '"'],
    ['(', ')'],
    ['<', '>'],
    [',', ''],
    [':', ';'],
    [';', ''],
]);
function tokenizeAddress(address = '') {
    var _a, _b;
    const tokens = [];
    let token = undefined;
    let operator = undefined;
    for (const character of address.toString()) {
        if (((_a = operator === null || operator === void 0 ? void 0 : operator.length) !== null && _a !== void 0 ? _a : 0) > 0 && character === operator) {
            tokens.push({ type: 'operator', value: character });
            token = undefined;
            operator = undefined;
        }
        else if (((_b = operator === null || operator === void 0 ? void 0 : operator.length) !== null && _b !== void 0 ? _b : 0) === 0 && OPERATORS.has(character)) {
            tokens.push({ type: 'operator', value: character });
            token = undefined;
            operator = OPERATORS.get(character);
        }
        else {
            if (token == null) {
                token = { type: 'text', value: character };
                tokens.push(token);
            }
            else {
                token.value += character;
            }
        }
    }
    return tokens
        .map((x) => {
        x.value = x.value.trim();
        return x;
    })
        .filter((x) => x.value.length > 0);
}
function convertAddressTokens(tokens) {
    const addressObjects = [];
    const groups = [];
    let addresses = [];
    let comments = [];
    let texts = [];
    let state = 'text';
    let isGroup = false;
    function handleToken(token) {
        if (token.type === 'operator') {
            switch (token.value) {
                case '<':
                    state = 'address';
                    break;
                case '(':
                    state = 'comment';
                    break;
                case ':':
                    state = 'group';
                    isGroup = true;
                    break;
                default:
                    state = 'text';
                    break;
            }
        }
        else if (token.value.length > 0) {
            switch (state) {
                case 'address':
                    addresses.push(token.value);
                    break;
                case 'comment':
                    comments.push(token.value);
                    break;
                case 'group':
                    groups.push(token.value);
                    break;
                default:
                    texts.push(token.value);
                    break;
            }
        }
    }
    for (const token of tokens) {
        handleToken(token);
    }
    if (texts.length === 0 && comments.length > 0) {
        texts = [...comments];
        comments = [];
    }
    if (isGroup) {
        addressObjects.push({
            name: texts.length === 0 ? undefined : texts.join(' '),
            group: groups.length > 0 ? addressparser(groups.join(',')) : [],
        });
    }
    else {
        if (addresses.length === 0 && texts.length > 0) {
            for (let i = texts.length - 1; i >= 0; i--) {
                if (texts[i].match(/^[^@\s]+@[^@\s]+$/)) {
                    addresses = texts.splice(i, 1);
                    break;
                }
            }
            if (addresses.length === 0) {
                for (let i = texts.length - 1; i >= 0; i--) {
                    texts[i] = texts[i]
                        .replace(/\s*\b[^@\s]+@[^@\s]+\b\s*/, (address) => {
                        if (addresses.length === 0) {
                            addresses = [address.trim()];
                            return ' ';
                        }
                        else {
                            return address;
                        }
                    })
                        .trim();
                    if (addresses.length > 0) {
                        break;
                    }
                }
            }
        }
        if (texts.length === 0 && comments.length > 0) {
            texts = [...comments];
            comments = [];
        }
        if (addresses.length > 1) {
            texts = [...texts, ...addresses.splice(1)];
        }
        if (addresses.length === 0 && isGroup) {
            return [];
        }
        else {
            let address = addresses.join(' ');
            let name = texts.length === 0 ? address : texts.join(' ');
            if (address === name) {
                if (address.match(/@/)) {
                    name = '';
                }
                else {
                    address = '';
                }
            }
            addressObjects.push({ address, name });
        }
    }
    return addressObjects;
}
function addressparser(address) {
    const addresses = [];
    let tokens = [];
    for (const token of tokenizeAddress(address)) {
        if (token.type === 'operator' &&
            (token.value === ',' || token.value === ';')) {
            if (tokens.length > 0) {
                addresses.push(...convertAddressTokens(tokens));
            }
            tokens = [];
        }
        else {
            tokens.push(token);
        }
    }
    if (tokens.length > 0) {
        addresses.push(...convertAddressTokens(tokens));
    }
    return addresses;
}

function getRFC2822Date(date = new Date(), useUtc = false) {
    if (useUtc) {
        return getRFC2822DateUTC(date);
    }
    const dates = date
        .toString()
        .replace('GMT', '')
        .replace(/\s\(.*\)$/, '')
        .split(' ');
    dates[0] = dates[0] + ',';
    const day = dates[1];
    dates[1] = dates[2];
    dates[2] = day;
    return dates.join(' ');
}
function getRFC2822DateUTC(date = new Date()) {
    const dates = date.toUTCString().split(' ');
    dates.pop();
    dates.push('+0000');
    return dates.join(' ');
}
const rfc2822re = /^(?:(Mon|Tue|Wed|Thu|Fri|Sat|Sun),?\s)?(\d{1,2})\s(Jan|Feb|Mar|Apr|May|Jun|Jul|Aug|Sep|Oct|Nov|Dec)\s(\d{2,4})\s(\d\d):(\d\d)(?::(\d\d))?\s(?:(UT|GMT|[ECMP][SD]T)|([Zz])|([+-]\d{4}))$/;
function isRFC2822Date(date) {
    return rfc2822re.test(date);
}

const encoder = new TextEncoder();
const RANGES = [
    [0x09],
    [0x0a],
    [0x0d],
    [0x20, 0x3c],
    [0x3e, 0x7e],
];
const LOOKUP = 'ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/'.split('');
const MAX_CHUNK_LENGTH = 16383;
const MAX_MIME_WORD_LENGTH = 52;
const MAX_B64_MIME_WORD_BYTE_LENGTH = 39;
function tripletToBase64(num) {
    return (LOOKUP[(num >> 18) & 0x3f] +
        LOOKUP[(num >> 12) & 0x3f] +
        LOOKUP[(num >> 6) & 0x3f] +
        LOOKUP[num & 0x3f]);
}
function encodeChunk(uint8, start, end) {
    let output = '';
    for (let i = start; i < end; i += 3) {
        output += tripletToBase64((uint8[i] << 16) + (uint8[i + 1] << 8) + uint8[i + 2]);
    }
    return output;
}
function encodeBase64(data) {
    const len = data.length;
    const extraBytes = len % 3;
    let output = '';
    for (let i = 0, len2 = len - extraBytes; i < len2; i += MAX_CHUNK_LENGTH) {
        output += encodeChunk(data, i, i + MAX_CHUNK_LENGTH > len2 ? len2 : i + MAX_CHUNK_LENGTH);
    }
    if (extraBytes === 1) {
        const tmp = data[len - 1];
        output += LOOKUP[tmp >> 2];
        output += LOOKUP[(tmp << 4) & 0x3f];
        output += '==';
    }
    else if (extraBytes === 2) {
        const tmp = (data[len - 2] << 8) + data[len - 1];
        output += LOOKUP[tmp >> 10];
        output += LOOKUP[(tmp >> 4) & 0x3f];
        output += LOOKUP[(tmp << 2) & 0x3f];
        output += '=';
    }
    return output;
}
function splitMimeEncodedString(str, maxlen = 12) {
    const minWordLength = 12;
    const maxWordLength = Math.max(maxlen, minWordLength);
    const lines = [];
    while (str.length) {
        let curLine = str.substr(0, maxWordLength);
        const match = curLine.match(/=[0-9A-F]?$/i);
        if (match) {
            curLine = curLine.substr(0, match.index);
        }
        let done = false;
        while (!done) {
            let chr;
            done = true;
            const match = str.substr(curLine.length).match(/^=([0-9A-F]{2})/i);
            if (match) {
                chr = parseInt(match[1], 16);
                if (chr < 0xc2 && chr > 0x7f) {
                    curLine = curLine.substr(0, curLine.length - 3);
                    done = false;
                }
            }
        }
        if (curLine.length) {
            lines.push(curLine);
        }
        str = str.substr(curLine.length);
    }
    return lines;
}
function checkRanges(nr) {
    return RANGES.reduce((val, range) => val ||
        (range.length === 1 && nr === range[0]) ||
        (range.length === 2 && nr >= range[0] && nr <= range[1]), false);
}
function mimeEncode(data = '', encoding = 'utf-8') {
    const decoder = new TextDecoder(encoding);
    const buffer = typeof data === 'string'
        ? encoder.encode(data)
        : encoder.encode(decoder.decode(data));
    return buffer.reduce((aggregate, ord, index) => checkRanges(ord) &&
        !((ord === 0x20 || ord === 0x09) &&
            (index === buffer.length - 1 ||
                buffer[index + 1] === 0x0a ||
                buffer[index + 1] === 0x0d))
        ?
            aggregate + String.fromCharCode(ord)
        : `${aggregate}=${ord < 0x10 ? '0' : ''}${ord
            .toString(16)
            .toUpperCase()}`, '');
}
function mimeWordEncode(data, mimeWordEncoding = 'Q', encoding = 'utf-8') {
    let parts = [];
    const decoder = new TextDecoder(encoding);
    const str = typeof data === 'string' ? data : decoder.decode(data);
    if (mimeWordEncoding === 'Q') {
        const encodedStr = mimeEncode(str, encoding).replace(/[^a-z0-9!*+\-/=]/gi, (chr) => chr === ' '
            ? '_'
            : '=' +
                (chr.charCodeAt(0) < 0x10 ? '0' : '') +
                chr.charCodeAt(0).toString(16).toUpperCase());
        parts =
            encodedStr.length < MAX_MIME_WORD_LENGTH
                ? [encodedStr]
                : splitMimeEncodedString(encodedStr, MAX_MIME_WORD_LENGTH);
    }
    else {
        let j = 0;
        let i = 0;
        while (i < str.length) {
            if (encoder.encode(str.substring(j, i)).length >
                MAX_B64_MIME_WORD_BYTE_LENGTH) {
                parts.push(str.substring(j, i - 1));
                j = i - 1;
            }
            else {
                i++;
            }
        }
        str.substring(j) && parts.push(str.substring(j));
        parts = parts.map((x) => encoder.encode(x)).map((x) => encodeBase64(x));
    }
    return parts
        .map((p) => `=?UTF-8?${mimeWordEncoding}?${p}?= `)
        .join('')
        .trim();
}

const CRLF$1 = '\r\n';
const MIMECHUNK = 76;
const MIME64CHUNK = (MIMECHUNK * 6);
const BUFFERSIZE = (MIMECHUNK * 24 * 7);
let counter = 0;
function generateBoundary() {
    let text = '';
    const possible = "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789'()+_,-./:=?";
    for (let i = 0; i < 69; i++) {
        text += possible.charAt(Math.floor(Math.random() * possible.length));
    }
    return text;
}
function convertPersonToAddress(person) {
    return addressparser(person)
        .map(({ name, address }) => {
        return name
            ? `${mimeWordEncode(name).replace(/,/g, '=2C')} <${address}>`
            : address;
    })
        .join(', ');
}
function convertDashDelimitedTextToSnakeCase(text) {
    return text
        .toLowerCase()
        .replace(/^(.)|-(.)/g, (match) => match.toUpperCase());
}
class Message {
    constructor(headers) {
        this.attachments = [];
        this.header = {
            'message-id': `<${new Date().getTime()}.${counter++}.${process.pid}@${hostname()}>`,
            date: getRFC2822Date(),
        };
        this.content = 'text/plain; charset=utf-8';
        this.alternative = null;
        for (const header in headers) {
            if (/^content-type$/i.test(header)) {
                this.content = headers[header];
            }
            else if (header === 'text') {
                this.text = headers[header];
            }
            else if (header === 'attachment' &&
                typeof headers[header] === 'object') {
                const attachment = headers[header];
                if (Array.isArray(attachment)) {
                    for (let i = 0; i < attachment.length; i++) {
                        this.attach(attachment[i]);
                    }
                }
                else if (attachment != null) {
                    this.attach(attachment);
                }
            }
            else if (header === 'subject') {
                this.header.subject = mimeWordEncode(headers.subject);
            }
            else if (/^(cc|bcc|to|from)/i.test(header)) {
                this.header[header.toLowerCase()] = convertPersonToAddress(headers[header]);
            }
            else {
                this.header[header.toLowerCase()] = headers[header];
            }
        }
    }
    attach(options) {
        if (options.alternative) {
            this.alternative = options;
            this.alternative.charset = options.charset || 'utf-8';
            this.alternative.type = options.type || 'text/html';
            this.alternative.inline = true;
        }
        else {
            this.attachments.push(options);
        }
        return this;
    }
    checkValidity() {
        if (typeof this.header.from !== 'string' &&
            Array.isArray(this.header.from) === false) {
            return {
                isValid: false,
                validationError: 'Message must have a `from` header',
            };
        }
        if (typeof this.header.to !== 'string' &&
            Array.isArray(this.header.to) === false &&
            typeof this.header.cc !== 'string' &&
            Array.isArray(this.header.cc) === false &&
            typeof this.header.bcc !== 'string' &&
            Array.isArray(this.header.bcc) === false) {
            return {
                isValid: false,
                validationError: 'Message must have at least one `to`, `cc`, or `bcc` header',
            };
        }
        if (this.attachments.length > 0) {
            const failed = [];
            this.attachments.forEach((attachment) => {
                if (attachment.path) {
                    if (existsSync(attachment.path) === false) {
                        failed.push(`${attachment.path} does not exist`);
                    }
                }
                else if (attachment.stream) {
                    if (!attachment.stream.readable) {
                        failed.push('attachment stream is not readable');
                    }
                }
                else if (!attachment.data) {
                    failed.push('attachment has no data associated with it');
                }
            });
            return {
                isValid: failed.length === 0,
                validationError: failed.join(', '),
            };
        }
        return { isValid: true, validationError: undefined };
    }
    valid(callback) {
        const { isValid, validationError } = this.checkValidity();
        callback(isValid, validationError);
    }
    stream() {
        return new MessageStream(this);
    }
    read(callback) {
        let buffer = '';
        const str = this.stream();
        str.on('data', (data) => (buffer += data));
        str.on('end', (err) => callback(err, buffer));
        str.on('error', (err) => callback(err, buffer));
    }
    readAsync() {
        return new Promise((resolve, reject) => {
            this.read((err, buffer) => {
                if (err != null) {
                    reject(err);
                }
                else {
                    resolve(buffer);
                }
            });
        });
    }
}
class MessageStream extends Stream {
    constructor(message) {
        super();
        this.message = message;
        this.readable = true;
        this.paused = false;
        this.buffer = Buffer.alloc(MIMECHUNK * 24 * 7);
        this.bufferIndex = 0;
        const output = (data) => {
            if (this.buffer != null) {
                const bytes = Buffer.byteLength(data);
                if (bytes + this.bufferIndex < this.buffer.length) {
                    this.buffer.write(data, this.bufferIndex);
                    this.bufferIndex += bytes;
                }
                else if (bytes > this.buffer.length) {
                    if (this.bufferIndex) {
                        this.emit('data', this.buffer.toString('utf-8', 0, this.bufferIndex));
                        this.bufferIndex = 0;
                    }
                    const loops = Math.ceil(data.length / this.buffer.length);
                    let loop = 0;
                    while (loop < loops) {
                        this.emit('data', data.substring(this.buffer.length * loop, this.buffer.length * (loop + 1)));
                        loop++;
                    }
                }
                else {
                    if (!this.paused) {
                        this.emit('data', this.buffer.toString('utf-8', 0, this.bufferIndex));
                        this.buffer.write(data, 0);
                        this.bufferIndex = bytes;
                    }
                    else {
                        this.once('resume', () => output(data));
                    }
                }
            }
        };
        const outputAttachmentHeaders = (attachment) => {
            let data = [];
            const headers = {
                'content-type': attachment.type +
                    (attachment.charset ? `; charset=${attachment.charset}` : '') +
                    (attachment.method ? `; method=${attachment.method}` : ''),
                'content-transfer-encoding': 'base64',
                'content-disposition': attachment.inline
                    ? 'inline'
                    : `attachment; filename="${mimeWordEncode(attachment.name)}"`,
            };
            if (attachment.headers != null) {
                for (const header in attachment.headers) {
                    headers[header.toLowerCase()] = attachment.headers[header];
                }
            }
            for (const header in headers) {
                data = data.concat([
                    convertDashDelimitedTextToSnakeCase(header),
                    ': ',
                    headers[header],
                    CRLF$1,
                ]);
            }
            output(data.concat([CRLF$1]).join(''));
        };
        const outputBase64 = (data, callback) => {
            const loops = Math.ceil(data.length / MIMECHUNK);
            let loop = 0;
            while (loop < loops) {
                output(data.substring(MIMECHUNK * loop, MIMECHUNK * (loop + 1)) + CRLF$1);
                loop++;
            }
            if (callback) {
                callback();
            }
        };
        const outputFile = (attachment, next) => {
            var _a;
            const chunk = MIME64CHUNK * 16;
            const buffer = Buffer.alloc(chunk);
            const inputEncoding = ((_a = attachment === null || attachment === void 0 ? void 0 : attachment.headers) === null || _a === void 0 ? void 0 : _a['content-transfer-encoding']) || 'base64';
            const encoding = inputEncoding === '7bit'
                ? 'ascii'
                : inputEncoding === '8bit'
                    ? 'binary'
                    : inputEncoding;
            const opened = (err, fd) => {
                if (err) {
                    this.emit('error', err);
                    return;
                }
                const readBytes = (err, bytes) => {
                    if (err || this.readable === false) {
                        this.emit('error', err || new Error('message stream was interrupted somehow!'));
                        return;
                    }
                    outputBase64(buffer.toString(encoding, 0, bytes), () => {
                        if (bytes == chunk) {
                            read(fd, buffer, 0, chunk, null, readBytes);
                        }
                        else {
                            this.removeListener('error', closeSync);
                            close(fd, next);
                        }
                    });
                };
                read(fd, buffer, 0, chunk, null, readBytes);
                this.once('error', closeSync);
            };
            open(attachment.path, 'r', opened);
        };
        const outputStream = (attachment, callback) => {
            const { stream } = attachment;
            if (stream === null || stream === void 0 ? void 0 : stream.readable) {
                let previous = Buffer.alloc(0);
                stream.resume();
                stream.on('end', () => {
                    outputBase64(previous.toString('base64'), callback);
                    this.removeListener('pause', stream.pause);
                    this.removeListener('resume', stream.resume);
                    this.removeListener('error', stream.resume);
                });
                stream.on('data', (buff) => {
                    let buffer = Buffer.isBuffer(buff) ? buff : Buffer.from(buff);
                    if (previous.byteLength > 0) {
                        buffer = Buffer.concat([previous, buffer]);
                    }
                    const padded = buffer.length % MIME64CHUNK;
                    previous = Buffer.alloc(padded);
                    if (padded > 0) {
                        buffer.copy(previous, 0, buffer.length - padded);
                    }
                    outputBase64(buffer.toString('base64', 0, buffer.length - padded));
                });
                this.on('pause', stream.pause);
                this.on('resume', stream.resume);
                this.on('error', stream.resume);
            }
            else {
                this.emit('error', { message: 'stream not readable' });
            }
        };
        const outputAttachment = (attachment, callback) => {
            const build = attachment.path
                ? outputFile
                : attachment.stream
                    ? outputStream
                    : outputData;
            outputAttachmentHeaders(attachment);
            build(attachment, callback);
        };
        const outputMessage = (boundary, list, index, callback) => {
            if (index < list.length) {
                output(`--${boundary}${CRLF$1}`);
                if (list[index].related) {
                    outputRelated(list[index], () => outputMessage(boundary, list, index + 1, callback));
                }
                else {
                    outputAttachment(list[index], () => outputMessage(boundary, list, index + 1, callback));
                }
            }
            else {
                output(`${CRLF$1}--${boundary}--${CRLF$1}${CRLF$1}`);
                callback();
            }
        };
        const outputMixed = () => {
            const boundary = generateBoundary();
            output(`Content-Type: multipart/mixed; boundary="${boundary}"${CRLF$1}${CRLF$1}--${boundary}${CRLF$1}`);
            if (this.message.alternative == null) {
                outputText(this.message);
                outputMessage(boundary, this.message.attachments, 0, close$1);
            }
            else {
                outputAlternative(this.message, () => outputMessage(boundary, this.message.attachments, 0, close$1));
            }
        };
        const outputData = (attachment, callback) => {
            var _a, _b;
            outputBase64(attachment.encoded
                ? (_a = attachment.data) !== null && _a !== void 0 ? _a : ''
                : Buffer.from((_b = attachment.data) !== null && _b !== void 0 ? _b : '').toString('base64'), callback);
        };
        const outputText = (message) => {
            let data = [];
            data = data.concat([
                'Content-Type:',
                message.content,
                CRLF$1,
                'Content-Transfer-Encoding: 7bit',
                CRLF$1,
            ]);
            data = data.concat(['Content-Disposition: inline', CRLF$1, CRLF$1]);
            data = data.concat([message.text || '', CRLF$1, CRLF$1]);
            output(data.join(''));
        };
        const outputRelated = (message, callback) => {
            const boundary = generateBoundary();
            output(`Content-Type: multipart/related; boundary="${boundary}"${CRLF$1}${CRLF$1}--${boundary}${CRLF$1}`);
            outputAttachment(message, () => {
                var _a;
                outputMessage(boundary, (_a = message.related) !== null && _a !== void 0 ? _a : [], 0, () => {
                    output(`${CRLF$1}--${boundary}--${CRLF$1}${CRLF$1}`);
                    callback();
                });
            });
        };
        const outputAlternative = (message, callback) => {
            const boundary = generateBoundary();
            output(`Content-Type: multipart/alternative; boundary="${boundary}"${CRLF$1}${CRLF$1}--${boundary}${CRLF$1}`);
            outputText(message);
            output(`--${boundary}${CRLF$1}`);
            const finish = () => {
                output([CRLF$1, '--', boundary, '--', CRLF$1, CRLF$1].join(''));
                callback();
            };
            if (message.alternative.related) {
                outputRelated(message.alternative, finish);
            }
            else {
                outputAttachment(message.alternative, finish);
            }
        };
        const close$1 = (err) => {
            var _a, _b;
            if (err) {
                this.emit('error', err);
            }
            else {
                this.emit('data', (_b = (_a = this.buffer) === null || _a === void 0 ? void 0 : _a.toString('utf-8', 0, this.bufferIndex)) !== null && _b !== void 0 ? _b : '');
                this.emit('end');
            }
            this.buffer = null;
            this.bufferIndex = 0;
            this.readable = false;
            this.removeAllListeners('resume');
            this.removeAllListeners('pause');
            this.removeAllListeners('error');
            this.removeAllListeners('data');
            this.removeAllListeners('end');
        };
        const outputHeaderData = () => {
            if (this.message.attachments.length || this.message.alternative) {
                output(`MIME-Version: 1.0${CRLF$1}`);
                outputMixed();
            }
            else {
                outputText(this.message);
                close$1();
            }
        };
        const outputHeader = () => {
            let data = [];
            for (const header in this.message.header) {
                if (!/bcc/i.test(header) &&
                    Object.prototype.hasOwnProperty.call(this.message.header, header)) {
                    data = data.concat([
                        convertDashDelimitedTextToSnakeCase(header),
                        ': ',
                        this.message.header[header],
                        CRLF$1,
                    ]);
                }
            }
            output(data.join(''));
            outputHeaderData();
        };
        this.once('destroy', close$1);
        process.nextTick(outputHeader);
    }
    pause() {
        this.paused = true;
        this.emit('pause');
    }
    resume() {
        this.paused = false;
        this.emit('resume');
    }
    destroy() {
        this.emit('destroy', this.bufferIndex > 0 ? { message: 'message stream destroyed' } : null);
    }
    destroySoon() {
        this.emit('destroy');
    }
}

const SMTPErrorStates = {
    COULDNOTCONNECT: 1,
    BADRESPONSE: 2,
    AUTHFAILED: 3,
    TIMEDOUT: 4,
    ERROR: 5,
    NOCONNECTION: 6,
    AUTHNOTSUPPORTED: 7,
    CONNECTIONCLOSED: 8,
    CONNECTIONENDED: 9,
    CONNECTIONAUTH: 10,
};
class SMTPError extends Error {
    constructor(message) {
        super(message);
        this.code = null;
        this.smtp = null;
        this.previous = null;
    }
    static create(message, code, error, smtp) {
        const msg = (error === null || error === void 0 ? void 0 : error.message) ? `${message} (${error.message})` : message;
        const err = new SMTPError(msg);
        err.code = code;
        err.smtp = smtp;
        if (error) {
            err.previous = error;
        }
        return err;
    }
}

class SMTPResponseMonitor {
    constructor(stream, timeout, onerror) {
        let buffer = '';
        const notify = () => {
            var _a, _b;
            if (buffer.length) {
                const line = buffer.replace('\r', '');
                if (!((_b = (_a = line
                    .trim()
                    .split(/\n/)
                    .pop()) === null || _a === void 0 ? void 0 : _a.match(/^(\d{3})\s/)) !== null && _b !== void 0 ? _b : false)) {
                    return;
                }
                const match = line ? line.match(/(\d+)\s?(.*)/) : null;
                const data = match !== null
                    ? { code: match[1], message: match[2], data: line }
                    : { code: -1, data: line };
                stream.emit('response', null, data);
                buffer = '';
            }
        };
        const error = (err) => {
            stream.emit('response', SMTPError.create('connection encountered an error', SMTPErrorStates.ERROR, err));
        };
        const timedout = (err) => {
            stream.end();
            stream.emit('response', SMTPError.create('timedout while connecting to smtp server', SMTPErrorStates.TIMEDOUT, err));
        };
        const watch = (data) => {
            if (data !== null) {
                buffer += data.toString();
                notify();
            }
        };
        const close = (err) => {
            stream.emit('response', SMTPError.create('connection has closed', SMTPErrorStates.CONNECTIONCLOSED, err));
        };
        const end = (err) => {
            stream.emit('response', SMTPError.create('connection has ended', SMTPErrorStates.CONNECTIONENDED, err));
        };
        this.stop = (err) => {
            stream.removeAllListeners('response');
            stream.removeListener('data', watch);
            stream.removeListener('end', end);
            stream.removeListener('close', close);
            stream.removeListener('error', error);
            if (err != null && typeof onerror === 'function') {
                onerror(err);
            }
        };
        stream.on('data', watch);
        stream.on('end', end);
        stream.on('close', close);
        stream.on('error', error);
        stream.setTimeout(timeout, timedout);
    }
}

const AUTH_METHODS = {
    PLAIN: 'PLAIN',
    'CRAM-MD5': 'CRAM-MD5',
    LOGIN: 'LOGIN',
    XOAUTH2: 'XOAUTH2',
};
const SMTPState = {
    NOTCONNECTED: 0,
    CONNECTING: 1,
    CONNECTED: 2,
};
const DEFAULT_TIMEOUT = 5000;
const SMTP_PORT = 25;
const SMTP_SSL_PORT = 465;
const SMTP_TLS_PORT = 587;
const CRLF = '\r\n';
const GREYLIST_DELAY = 300;
let DEBUG = 0;
const log = (...args) => {
    if (DEBUG === 1) {
        args.forEach((d) => console.log(typeof d === 'object'
            ? d instanceof Error
                ? d.message
                : JSON.stringify(d)
            : d));
    }
};
const caller = (callback, ...args) => {
    if (typeof callback === 'function') {
        callback(...args);
    }
};
class SMTPConnection extends EventEmitter {
    constructor({ timeout, host, user, password, domain, port, ssl, tls, logger, authentication, } = {}) {
        var _a;
        super();
        this.timeout = DEFAULT_TIMEOUT;
        this.log = log;
        this.authentication = [
            AUTH_METHODS['CRAM-MD5'],
            AUTH_METHODS.LOGIN,
            AUTH_METHODS.PLAIN,
            AUTH_METHODS.XOAUTH2,
        ];
        this._state = SMTPState.NOTCONNECTED;
        this._secure = false;
        this.loggedin = false;
        this.sock = null;
        this.features = null;
        this.monitor = null;
        this.domain = hostname();
        this.host = 'localhost';
        this.ssl = false;
        this.tls = false;
        this.greylistResponseTracker = new WeakSet();
        if (Array.isArray(authentication)) {
            this.authentication = authentication;
        }
        if (typeof timeout === 'number') {
            this.timeout = timeout;
        }
        if (typeof domain === 'string') {
            this.domain = domain;
        }
        if (typeof host === 'string') {
            this.host = host;
        }
        if (ssl != null &&
            (typeof ssl === 'boolean' ||
                (typeof ssl === 'object' && Array.isArray(ssl) === false))) {
            this.ssl = ssl;
        }
        if (tls != null &&
            (typeof tls === 'boolean' ||
                (typeof tls === 'object' && Array.isArray(tls) === false))) {
            this.tls = tls;
        }
        this.port = port || (ssl ? SMTP_SSL_PORT : tls ? SMTP_TLS_PORT : SMTP_PORT);
        this.loggedin = user && password ? false : true;
        if (!user && ((_a = password === null || password === void 0 ? void 0 : password.length) !== null && _a !== void 0 ? _a : 0) > 0) {
            throw new Error('`password` cannot be set without `user`');
        }
        this.user = () => user;
        this.password = () => password;
        if (typeof logger === 'function') {
            this.log = logger;
        }
    }
    debug(level) {
        DEBUG = level;
    }
    state() {
        return this._state;
    }
    authorized() {
        return this.loggedin;
    }
    connect(callback, port = this.port, host = this.host, options = {}) {
        this.port = port;
        this.host = host;
        this.ssl = options.ssl || this.ssl;
        if (this._state !== SMTPState.NOTCONNECTED) {
            this.quit(() => this.connect(callback, port, host, options));
        }
        const connected = () => {
            this.log(`connected: ${this.host}:${this.port}`);
            if (this.ssl && !this.tls) {
                if (typeof this.ssl !== 'boolean' &&
                    this.sock instanceof TLSSocket &&
                    !this.sock.authorized) {
                    this.close(true);
                    caller(callback, SMTPError.create('could not establish an ssl connection', SMTPErrorStates.CONNECTIONAUTH));
                }
                else {
                    this._secure = true;
                }
            }
        };
        const connectedErrBack = (err) => {
            if (!err) {
                connected();
            }
            else {
                this.close(true);
                this.log(err);
                caller(callback, SMTPError.create('could not connect', SMTPErrorStates.COULDNOTCONNECT, err));
            }
        };
        const response = (err, msg) => {
            if (err) {
                if (this._state === SMTPState.NOTCONNECTED && !this.sock) {
                    return;
                }
                this.close(true);
                caller(callback, err);
            }
            else if (msg.code == '220') {
                this.log(msg.data);
                this._state = SMTPState.CONNECTED;
                caller(callback, null, msg.data);
            }
            else {
                this.log(`response (data): ${msg.data}`);
                this.quit(() => {
                    caller(callback, SMTPError.create('bad response on connection', SMTPErrorStates.BADRESPONSE, err, msg.data));
                });
            }
        };
        this._state = SMTPState.CONNECTING;
        this.log(`connecting: ${this.host}:${this.port}`);
        if (this.ssl) {
            this.sock = connect(this.port, this.host.trim(), typeof this.ssl === 'object' ? this.ssl : {}, connected);
        }
        else {
            this.sock = new Socket();
            this.sock.connect(this.port, this.host.trim(), connectedErrBack);
        }
        this.monitor = new SMTPResponseMonitor(this.sock, this.timeout, () => this.close(true));
        this.sock.once('response', response);
        this.sock.once('error', response);
    }
    send(str, callback) {
        if (this.sock != null && this._state === SMTPState.CONNECTED) {
            this.log(str);
            this.sock.once('response', (err, msg) => {
                if (err) {
                    caller(callback, err);
                }
                else {
                    this.log(msg.data);
                    caller(callback, null, msg);
                }
            });
            if (this.sock.writable) {
                this.sock.write(str);
            }
        }
        else {
            this.close(true);
            caller(callback, SMTPError.create('no connection has been established', SMTPErrorStates.NOCONNECTION));
        }
    }
    command(cmd, callback, codes = [250]) {
        const codesArray = Array.isArray(codes)
            ? codes
            : typeof codes === 'number'
                ? [codes]
                : [250];
        const response = (err, msg) => {
            if (err) {
                caller(callback, err);
            }
            else {
                const code = Number(msg.code);
                if (codesArray.indexOf(code) !== -1) {
                    caller(callback, err, msg.data, msg.message);
                }
                else if ((code === 450 || code === 451) &&
                    msg.message.toLowerCase().includes('greylist') &&
                    this.greylistResponseTracker.has(response) === false) {
                    this.greylistResponseTracker.add(response);
                    setTimeout(() => {
                        this.send(cmd + CRLF, response);
                    }, GREYLIST_DELAY);
                }
                else {
                    const suffix = msg.message ? `: ${msg.message}` : '';
                    const errorMessage = `bad response on command '${cmd.split(' ')[0]}'${suffix}`;
                    caller(callback, SMTPError.create(errorMessage, SMTPErrorStates.BADRESPONSE, null, msg.data));
                }
            }
        };
        this.greylistResponseTracker.delete(response);
        this.send(cmd + CRLF, response);
    }
    helo(callback, domain) {
        this.command(`helo ${domain || this.domain}`, (err, data) => {
            if (err) {
                caller(callback, err);
            }
            else {
                this.parse_smtp_features(data);
                caller(callback, err, data);
            }
        });
    }
    starttls(callback) {
        const response = (err, msg) => {
            if (this.sock == null) {
                throw new Error('null socket');
            }
            if (err) {
                err.message += ' while establishing a starttls session';
                caller(callback, err);
            }
            else {
                const secureContext = createSecureContext(typeof this.tls === 'object' ? this.tls : {});
                const secureSocket = new TLSSocket(this.sock, { secureContext });
                secureSocket.on('error', (err) => {
                    this.close(true);
                    caller(callback, err);
                });
                this._secure = true;
                this.sock = secureSocket;
                new SMTPResponseMonitor(this.sock, this.timeout, () => this.close(true));
                caller(callback, msg.data);
            }
        };
        this.command('starttls', response, [220]);
    }
    parse_smtp_features(data) {
        data.split('\n').forEach((ext) => {
            const parse = ext.match(/^(?:\d+[-=]?)\s*?([^\s]+)(?:\s+(.*)\s*?)?$/);
            if (parse != null && this.features != null) {
                this.features[parse[1].toLowerCase()] = parse[2] || true;
            }
        });
    }
    ehlo(callback, domain) {
        this.features = {};
        this.command(`ehlo ${domain || this.domain}`, (err, data) => {
            if (err) {
                caller(callback, err);
            }
            else {
                this.parse_smtp_features(data);
                if (this.tls && !this._secure) {
                    this.starttls(() => this.ehlo(callback, domain));
                }
                else {
                    caller(callback, err, data);
                }
            }
        });
    }
    has_extn(opt) {
        var _a;
        return ((_a = this.features) !== null && _a !== void 0 ? _a : {})[opt.toLowerCase()] === undefined;
    }
    help(callback, domain) {
        this.command(domain ? `help ${domain}` : 'help', callback, [211, 214]);
    }
    rset(callback) {
        this.command('rset', callback);
    }
    noop(callback) {
        this.send('noop', callback);
    }
    mail(callback, from) {
        this.command(`mail FROM:${from}`, callback);
    }
    rcpt(callback, to) {
        this.command(`RCPT TO:${to}`, callback, [250, 251]);
    }
    data(callback) {
        this.command('data', callback, [354]);
    }
    data_end(callback) {
        this.command(`${CRLF}.`, callback);
    }
    message(data) {
        var _a, _b;
        this.log(data);
        (_b = (_a = this.sock) === null || _a === void 0 ? void 0 : _a.write(data)) !== null && _b !== void 0 ? _b : this.log('no socket to write to');
    }
    verify(address, callback) {
        this.command(`vrfy ${address}`, callback, [250, 251, 252]);
    }
    expn(address, callback) {
        this.command(`expn ${address}`, callback);
    }
    ehlo_or_helo_if_needed(callback, domain) {
        if (!this.features) {
            const response = (err, data) => caller(callback, err, data);
            this.ehlo((err, data) => {
                if (err) {
                    this.helo(response, domain);
                }
                else {
                    caller(callback, err, data);
                }
            }, domain);
        }
    }
    login(callback, user, password, options = {}) {
        var _a, _b;
        const login = {
            user: user ? () => user : this.user,
            password: password ? () => password : this.password,
            method: (_b = (_a = options === null || options === void 0 ? void 0 : options.method) === null || _a === void 0 ? void 0 : _a.toUpperCase()) !== null && _b !== void 0 ? _b : '',
        };
        const domain = (options === null || options === void 0 ? void 0 : options.domain) || this.domain;
        const initiate = (err, data) => {
            var _a;
            if (err) {
                caller(callback, err);
                return;
            }
            let method = null;
            const encodeCramMd5 = (challenge) => {
                const hmac = createHmac('md5', login.password());
                hmac.update(Buffer.from(challenge, 'base64').toString('ascii'));
                return Buffer.from(`${login.user()} ${hmac.digest('hex')}`).toString('base64');
            };
            const encodePlain = () => Buffer.from(`\u0000${login.user()}\u0000${login.password()}`).toString('base64');
            const encodeXoauth2 = () => Buffer.from(`user=${login.user()}\u0001auth=Bearer ${login.password()}\u0001\u0001`).toString('base64');
            if (!method) {
                const preferred = this.authentication;
                let auth = '';
                if (typeof ((_a = this.features) === null || _a === void 0 ? void 0 : _a['auth']) === 'string') {
                    auth = this.features['auth'];
                }
                for (let i = 0; i < preferred.length; i++) {
                    if (auth.includes(preferred[i])) {
                        method = preferred[i];
                        break;
                    }
                }
            }
            const failed = (err, data) => {
                this.loggedin = false;
                this.close();
                caller(callback, SMTPError.create('authorization.failed', SMTPErrorStates.AUTHFAILED, err, data));
            };
            const response = (err, data) => {
                if (err) {
                    failed(err, data);
                }
                else {
                    this.loggedin = true;
                    caller(callback, err, data);
                }
            };
            const attempt = (err, data, msg) => {
                if (err) {
                    failed(err, data);
                }
                else {
                    if (method === AUTH_METHODS['CRAM-MD5']) {
                        this.command(encodeCramMd5(msg), response, [235, 503]);
                    }
                    else if (method === AUTH_METHODS.LOGIN) {
                        this.command(Buffer.from(login.password()).toString('base64'), response, [235, 503]);
                    }
                }
            };
            const attemptUser = (err, data) => {
                if (err) {
                    failed(err, data);
                }
                else {
                    if (method === AUTH_METHODS.LOGIN) {
                        this.command(Buffer.from(login.user()).toString('base64'), attempt, [334]);
                    }
                }
            };
            switch (method) {
                case AUTH_METHODS['CRAM-MD5']:
                    this.command(`AUTH  ${AUTH_METHODS['CRAM-MD5']}`, attempt, [334]);
                    break;
                case AUTH_METHODS.LOGIN:
                    this.command(`AUTH ${AUTH_METHODS.LOGIN}`, attemptUser, [334]);
                    break;
                case AUTH_METHODS.PLAIN:
                    this.command(`AUTH ${AUTH_METHODS.PLAIN} ${encodePlain()}`, response, [235, 503]);
                    break;
                case AUTH_METHODS.XOAUTH2:
                    this.command(`AUTH ${AUTH_METHODS.XOAUTH2} ${encodeXoauth2()}`, response, [235, 503]);
                    break;
                default:
                    caller(callback, SMTPError.create('no form of authorization supported', SMTPErrorStates.AUTHNOTSUPPORTED, null, data));
                    break;
            }
        };
        this.ehlo_or_helo_if_needed(initiate, domain);
    }
    close(force = false) {
        if (this.sock) {
            if (force) {
                this.log('smtp connection destroyed!');
                this.sock.destroy();
            }
            else {
                this.log('smtp connection closed.');
                this.sock.end();
            }
        }
        if (this.monitor) {
            this.monitor.stop();
            this.monitor = null;
        }
        this._state = SMTPState.NOTCONNECTED;
        this._secure = false;
        this.sock = null;
        this.features = null;
        this.loggedin = !(this.user() && this.password());
    }
    quit(callback) {
        this.command('quit', (err, data) => {
            caller(callback, err, data);
            this.close();
        }, [221, 250]);
    }
}

class SMTPClient {
    constructor(server) {
        this.queue = [];
        this.sending = false;
        this.ready = false;
        this.timer = null;
        this.smtp = new SMTPConnection(server);
    }
    send(msg, callback) {
        const message = msg instanceof Message
            ? msg
            : this._canMakeMessage(msg)
                ? new Message(msg)
                : null;
        if (message == null) {
            callback(new Error('message is not a valid Message instance'), msg);
            return;
        }
        const { isValid, validationError } = message.checkValidity();
        if (isValid) {
            const stack = this.createMessageStack(message, callback);
            if (stack.to.length === 0) {
                return callback(new Error('No recipients found in message'), msg);
            }
            this.queue.push(stack);
            this._poll();
        }
        else {
            callback(new Error(validationError), msg);
        }
    }
    sendAsync(msg) {
        return new Promise((resolve, reject) => {
            console.log(`EMAILJS::INTERNAL::LOGGER - startSend; message: {${msg.text}}`);
            const time = Date.now();
            const intervalLogger = setInterval(() => {
                console.log(`EMAILJS::INTERNAL::LOGGER - time: ${time - Date.now()}; message: {${msg.text}}`);
            }, 10000);
            this.send(msg, (err, message) => {
                if (err != null) {
                    clearInterval(intervalLogger);
                    reject(err);
                }
                else {
                    clearInterval(intervalLogger);
                    resolve(message);
                }
            });
        });
    }
    createMessageStack(message, callback = function () {
    }) {
        const [{ address: from }] = addressparser(message.header.from);
        const stack = {
            message,
            to: [],
            from,
            callback: callback.bind(this),
        };
        const { header: { to, cc, bcc, 'return-path': returnPath }, } = message;
        if ((typeof to === 'string' || Array.isArray(to)) && to.length > 0) {
            stack.to = addressparser(to);
        }
        if ((typeof cc === 'string' || Array.isArray(cc)) && cc.length > 0) {
            stack.to = stack.to.concat(addressparser(cc).filter((x) => stack.to.some((y) => y.address === x.address) === false));
        }
        if ((typeof bcc === 'string' || Array.isArray(bcc)) && bcc.length > 0) {
            stack.to = stack.to.concat(addressparser(bcc).filter((x) => stack.to.some((y) => y.address === x.address) === false));
        }
        if (typeof returnPath === 'string' && returnPath.length > 0) {
            const parsedReturnPath = addressparser(returnPath);
            if (parsedReturnPath.length > 0) {
                const [{ address: returnPathAddress }] = parsedReturnPath;
                stack.returnPath = returnPathAddress;
            }
        }
        return stack;
    }
    _poll() {
        if (this.timer != null) {
            clearTimeout(this.timer);
        }
        if (this.queue.length) {
            if (this.smtp.state() == SMTPState.NOTCONNECTED) {
                this._connect(this.queue[0]);
            }
            else if (this.smtp.state() == SMTPState.CONNECTED &&
                !this.sending &&
                this.ready) {
                this._sendmail(this.queue.shift());
            }
        }
        else if (this.smtp.state() == SMTPState.CONNECTED) {
            this.timer = setTimeout(() => this.smtp.quit(), 1000);
        }
    }
    _connect(stack) {
        const connect = (err) => {
            if (!err) {
                const begin = (err) => {
                    if (!err) {
                        this.ready = true;
                        this._poll();
                    }
                    else {
                        stack.callback(err, stack.message);
                        this.queue.shift();
                        this._poll();
                    }
                };
                if (!this.smtp.authorized()) {
                    this.smtp.login(begin);
                }
                else {
                    this.smtp.ehlo_or_helo_if_needed(begin);
                }
            }
            else {
                stack.callback(err, stack.message);
                this.queue.shift();
                this._poll();
            }
        };
        this.ready = false;
        this.smtp.connect(connect);
    }
    _canMakeMessage(msg) {
        return (msg.from &&
            (msg.to || msg.cc || msg.bcc) &&
            (msg.text !== undefined || this._containsInlinedHtml(msg.attachment)));
    }
    _containsInlinedHtml(attachment) {
        if (Array.isArray(attachment)) {
            return attachment.some((att) => {
                return this._isAttachmentInlinedHtml(att);
            });
        }
        else {
            return this._isAttachmentInlinedHtml(attachment);
        }
    }
    _isAttachmentInlinedHtml(attachment) {
        return (attachment &&
            (attachment.data || attachment.path) &&
            attachment.alternative === true);
    }
    _sendsmtp(stack, next) {
        return (err) => {
            if (!err && next) {
                next.apply(this, [stack]);
            }
            else {
                this.smtp.rset(() => this._senddone(err, stack));
            }
        };
    }
    _sendmail(stack) {
        const from = stack.returnPath || stack.from;
        this.sending = true;
        this.smtp.mail(this._sendsmtp(stack, this._sendrcpt), '<' + from + '>');
    }
    _sendrcpt(stack) {
        var _a;
        if (stack.to == null || typeof stack.to === 'string') {
            throw new TypeError('stack.to must be array');
        }
        const to = (_a = stack.to.shift()) === null || _a === void 0 ? void 0 : _a.address;
        this.smtp.rcpt(this._sendsmtp(stack, stack.to.length ? this._sendrcpt : this._senddata), `<${to}>`);
    }
    _senddata(stack) {
        this.smtp.data(this._sendsmtp(stack, this._sendmessage));
    }
    _sendmessage(stack) {
        const stream = stack.message.stream();
        stream.on('data', (data) => this.smtp.message(data));
        stream.on('end', () => {
            this.smtp.data_end(this._sendsmtp(stack, () => this._senddone(null, stack)));
        });
        stream.on('error', (err) => {
            this.smtp.close();
            this._senddone(err, stack);
        });
    }
    _senddone(err, stack) {
        this.sending = false;
        stack.callback(err, stack.message);
        this._poll();
    }
}

export { AUTH_METHODS, BUFFERSIZE, DEFAULT_TIMEOUT, MIME64CHUNK, MIMECHUNK, Message, SMTPClient, SMTPConnection, SMTPError, SMTPErrorStates, SMTPResponseMonitor, SMTPState, addressparser, getRFC2822Date, getRFC2822DateUTC, isRFC2822Date, mimeEncode, mimeWordEncode };
//# sourceMappingURL=email.js.map
