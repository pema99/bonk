var Cons = function (v) {
    return { tag: "Cons", val: v };
};
var Nil = function (v) {
    return { tag: "Nil", val: v };
};
var iota = function (n) {
    var inner = function (acc) {
        if ((acc >= n)) {
            return Nil("<unit>");
        } else {
            return Cons([acc, inner((acc + 1))]);
        }
    };
    return inner(0);
};
var map = function (f) {
    return function (lst) {
        var h = null;
        var t = null;
        var _ = null;
        var matched = 0;
        if (((lst).tag === "Cons")) {
            h = ((lst).val)[0];
            t = ((lst).val)[1];
            matched = 0;
        }
        if (((lst).tag === "Nil")) {
            _ = (lst).val;
            matched = 1;
        }
        switch (matched) {
            case 0: {
                return Cons([f(h), map(f)(t)]);
            } break;
            case 1: {
                return Nil("<unit>");
            } break;
        }
    };
};
var fold = function (f) {
    return function (z) {
        return function (lst) {
            var h = null;
            var t = null;
            var _ = null;
            var matched = 0;
            if (((lst).tag === "Cons")) {
                h = ((lst).val)[0];
                t = ((lst).val)[1];
                matched = 0;
            }
            if (((lst).tag === "Nil")) {
                _ = (lst).val;
                matched = 1;
            }
            switch (matched) {
                case 0: {
                    return f(h)(fold(f)(z)(t));
                } break;
                case 1: {
                    return z;
                } break;
            }
        };
    };
};
var filter = function (f) {
    return function (lst) {
        var h = null;
        var t = null;
        var _ = null;
        var matched = 0;
        if (((lst).tag === "Cons")) {
            h = ((lst).val)[0];
            t = ((lst).val)[1];
            matched = 0;
        }
        if (((lst).tag === "Nil")) {
            _ = (lst).val;
            matched = 1;
        }
        switch (matched) {
            case 0: {
                if (f(h)) {
                    return Cons([h, filter(f)(t)]);
                } else {
                    return filter(f)(t);
                }
            } break;
            case 1: {
                return Nil(_);
            } break;
        }
    };
};
var myList = iota(20);
var r1 = map(function (x) {
    return (x * x);
})(myList);
var r2 = filter(function (x) {
    return ((x % 2) === 0);
})(r1);
var r3 = fold(function (x) {
    return function (y) {
        return (x + y);
    };
})(0)(r2);
r3;
