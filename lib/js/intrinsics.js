// Not exposed to the user
const _fs = require("fs");
const _charToNum = (chr) => chr.charCodeAt(0);
const _makeChar = (str) => {
    let strc = new String(str[0]);
    strc._isChar = true;
    return strc;
};
const _numToChar = (num) => _makeChar(String.fromCharCode(num));
const _compare = (a) => (b) => {
    if (a._isChar && b._isChar) {
        return _charToNum(a) === _charToNum(b);
    } else {
        return a === b;
    }
}
// Expose intrinsics
let lengthString = (str) => str.length;
let indexString = (str) => (i) => _makeChar(str[i]);
let substring = (str) => (start) => (size) => str.substring(start, start+size);
let print = (str) => process.stdout.write(str);
let read = (_) => prompt("");
let readFile = (path) => _fs.readFileSync(path).toString();
let toFloat = (x) => {
    if (x._isChar) {
        return _charToNum(x);
    } else {
        return parseFloat(x);
    }
};
let toString = (x) => x.toString();
let toChar = (x) => {
    if (x._isChar) {
        return x;
    } else if (typeof x === "number") {
        return _numToChar(x);
    } else {
        return toString(x)[0];
    }
}
let toBool = (x) => {
    if (x._isChar) {
        return _charToNum(x) !== 0;
    } else if (x === "true") {
        return true;
    } else if (x === "false") {
        return false;
    } else {
        return !!x;
    }
};
let toInt = (x) => {
    if (x._isChar) {
        return _charToNum(x)|0;
    } else {
        return parseInt(x);
    }
};
let sqrt = (x) => Math.sqrt(x);
let sin = (x) => Math.sin(x);
let cos = (x) => Math.cos(x);
let tan = (x) => Math.tan(x);
let asin = (x) => Math.asin(x);
let acos = (x) => Math.acos(x);
let atan = (x) => Math.atan(x);
let atan2 = (y) => (x) => Math.atan2(y, x);
let exp = (x) => Math.exp(x);
let pow = (x) => (y) => Math.pow(x, y);
let ln = (x) => Math.log(x);
let floor = (x) => Math.floor(x);
let ceil = (x) => Math.ceil(x);
