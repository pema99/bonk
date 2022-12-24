// Not exposed to the user
const $fs = (() => { try { return require("fs"); } catch (e) { return null; } })();
// Expose intrinsics
let lengthString = (str) => str.length;
let indexString = (str) => (i) => str.charCodeAt(i);
let substring = (str) => (start) => (size) => str.substring(start, start+size);
let print = (str) => process.stdout.write(str);
let read = (_) => prompt("");
let readFile = (path) => $fs.readFileSync(path).toString();
let writeFile = (path) => (content) => $fs.writeFileSync(path, content);
let toFloat = (x) => parseFloat(x);
let toString = (x) => x.toString();
// TODO: toChar
let toBool = (x) => {
    if (x === "true") {
        return true;
    } else if (x === "false") {
        return false;
    } else {
        return !!x;
    }
};
let toInt = (x) => parseInt(x);
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
