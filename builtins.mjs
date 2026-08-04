export class MhEx extends Error {
    constructor(type, value) {
        super();
        this.name = "Moorhen exception";
        this.type = type;
        this.value = value;
    }
}

export function $0builtins$1$2RealBuiltins$3eq(x, y) { return x == y; }
export function $0builtins$1$2RealBuiltins$3neq(x, y) { return x != y; }
export function $0builtins$1$2IntBuiltins$3eq(x, y) { return x == y; }
export function $0builtins$1$2IntBuiltins$3neq(x, y) { return x != y; }
export function $0builtins$1$2I32Builtins$3eq(x, y) { return x == y; }
export function $0builtins$1$2I32Builtins$3neq(x, y) { return x != y; }
export function $0builtins$1$2StringBuiltins$3eq(x, y) { return x == y; }
export function $0builtins$1$2StringBuiltins$3neq(x, y) { return x != y; }
export function $0builtins$1$2UnitBuiltins$3eq(x, y) { return true; }
export function $0builtins$1$2UnitBuiltins$3neq(x, y) { return false; }
export function $0builtins$1$2BoolBuiltins$3eq(x, y) { return x == y; }
export function $0builtins$1$2BoolBuiltins$3neq(x, y) { return x != y; }
export function $0builtins$1$2CodePointBuiltins$3eq(x, y) { return x == y; }
export function $0builtins$1$2CodePointBuiltins$3neq(x, y) { return x != y; }

export function $0builtins$1$2RealBuiltins$3show(x) { return x.toString(); }
export function $0builtins$1$2IntBuiltins$3show(x) { return x.toString(); }
export function $0builtins$1$2I32Builtins$3show(x) { return x.toString(); }
export function $0builtins$1$2BoolBuiltins$3show(x) { return x.toString(); }
export function $0builtins$1$2UnitBuiltins$3show(x) { return "()"; }
export function $0builtins$1$2StringBuiltins$3show(x) { return x; }



export function $0builtins$1$2RealBuiltins$3add(x, y) { return x + y; }
export function $0builtins$1$2RealBuiltins$3sub(x, y) { return x - y; }
export function $0builtins$1$2RealBuiltins$3mul(x, y) { return x * y; }
export function $0builtins$1$2RealBuiltins$3div(x, y) { return x / y; }
export function $0builtins$1$2RealBuiltins$3rem(x, y) { return x % y; }

export function $0builtins$1$2RealBuiltins$3gt(x, y) { return x > y; }
export function $0builtins$1$2RealBuiltins$3gte(x, y) { return x >= y; }
export function $0builtins$1$2RealBuiltins$3lt(x, y) { return x < y; }
export function $0builtins$1$2RealBuiltins$3lte(x, y) { return x <= y; }
export function $0builtins$1$2RealBuiltins$3neg(x) { return -x; }
export function $0builtins$1$2RealBuiltins$3truncI32(x) { return x | 0; }


export const $0builtins$1$2inf = Number.POSITIVE_INFINITY;
export const $0builtins$1$2negInf = Number.NEGATIVE_INFINITY;


export function $0builtins$1$2IntBuiltins$3add(x, y) { return x + y; }
export function $0builtins$1$2IntBuiltins$3sub(x, y) { return x - y; }
export function $0builtins$1$2IntBuiltins$3mul(x, y) { return x * y; }
export function $0builtins$1$2IntBuiltins$3div(x, y) { return Math.trunc(x / y); }
export function $0builtins$1$2IntBuiltins$3rem(x, y) { return Math.trunc(x % y); }

export function $0builtins$1$2IntBuiltins$3gt(x, y) { return x > y; }
export function $0builtins$1$2IntBuiltins$3gte(x, y) { return x >= y; }
export function $0builtins$1$2IntBuiltins$3lt(x, y) { return x < y; }
export function $0builtins$1$2IntBuiltins$3lte(x, y) { return x <= y; }
export function $0builtins$1$2IntBuiltins$3neg(x) { return -x; }
export function $0builtins$1$2IntBuiltins$3truncI32(x) { return x | 0; }


export function $0builtins$1$2I32Builtins$3add(x, y) { return (x + y) | 0; }
export function $0builtins$1$2I32Builtins$3sub(x, y) { return (x - y) | 0; }
export function $0builtins$1$2I32Builtins$3mul(x, y) { return Math.imul(x, y); }
export function $0builtins$1$2I32Builtins$3div(x, y) { return (x / y) | 0; }
export function $0builtins$1$2I32Builtins$3rem(x, y) { return (x % y) | 0; }

export function $0builtins$1$2I32Builtins$3gt(x, y) { return x > y; }
export function $0builtins$1$2I32Builtins$3gte(x, y) { return x >= y; }
export function $0builtins$1$2I32Builtins$3lt(x, y) { return x < y; }
export function $0builtins$1$2I32Builtins$3lte(x, y) { return x <= y; }
export function $0builtins$1$2I32Builtins$3neg(x) { return -x; }


export function $0builtins$1$2I32Builtins$3bAnd(x, y) { return x & y; }
export function $0builtins$1$2I32Builtins$3bOr(x, y) { return x | y; }
export function $0builtins$1$2I32Builtins$3bXor(x, y) { return x ^ y; }
export function $0builtins$1$2I32Builtins$3bNot(x) { return ~x; }





export function $0builtins$1$2StringBuiltins$3sizeInBytes(x) { return x.length * 2; }
export function $0builtins$1$2StringBuiltins$3append(x, y) { return x.concat(y); }
export function $0builtins$1$2StringBuiltins$3startsWith(x, y) { return x.startsWith(y); }
export function $0builtins$1$2StringBuiltins$3substring(x, i, j) { return x.substring(i / 2, j / 2); }
export function $0builtins$1$2StringBuiltins$3words(x) { return x.split(/\s+/); }
export function $0builtins$1$2StringBuiltins$3lines(x) { return x.split(/[\r\n]+/); }
export function $0builtins$1$2StringBuiltins$3split(x, y) { return x.split(y); }

export function $0builtins$1$2StringBuiltins$3ord(x) {
    if (x.length == 0) { return 0 | 0; }
    return x.codePointAt(0) | 0;
}
export function $0builtins$1$2CodePointBuiltins$3show(x) { return String.fromCodePoint(x); }
export function $0builtins$1$2StringBuiltins$3getCodePointAt(x, i) { return x.codePointAt(i / 2) | 0; }
export function $0builtins$1$2StringBuiltins$3contains(x, y) { return x.includes(y); }

export function $0builtins$1$2StringBuiltins$3iterCodePoints(s) {
    var i = 0;
    const f = function () {
        if (i >= s.length) { return [0, undefined]; }
        const c = s.codePointAt(i) | 0;
        i += c <= 0xffff ? 1 : 2;
        return [1, [c, f]];
    };
    return f();
}



export function $0builtins$1$2BoolBuiltins$3not(x) { return !x; }


export const $0builtins$1$2undefined = undefined;
export const $0builtins$1$2todo = undefined;
export function $0builtins$1$2panic(msg) { throw new Error(msg); }

// Lazy type stored as [isValue: Bool, (\ -> T) OR T]

export function $0builtins$1$2lazy(f) { return [false, f]; }
export function $0builtins$1$2AsLazy$3asLazy(x) { return [true, x]; }
export function $0builtins$1$2LazyFns$3eval(l) {
    if (l[0]) {
        return l[1];
    } else {
        let x = l[1]();
        l[0] = true;
        l[1] = x;
        return x;
    }
}



export const $0builtins$1$2emptyVec = [];

export function $0builtins$1$2singletonVec(x) {
    return [x];
}

export function $0builtins$1$2VecBuiltins$3append(xs, ys) {
    return xs.concat(ys);
}

export function $0builtins$1$2VecBuiltins$3atOrPanic(xs, i) {
    if (i < 0 || i >= xs.length) { throw new RangeError("Index " + i + " is out of range in Vec of length " + xs.length); }
    return xs[i];
}

export function $0builtins$1$2VecBuiltins$3setAtOrPanic(xs, i, x) {
    var ys = xs.slice();
    ys[i] = x;
    return ys;
}

export function $0builtins$1$2VecBuiltins$3length(xs) { return xs.length | 0; }

export function $0builtins$1$2VecBuiltins$3sort(xs, f) {
    var ys = xs.slice();
    ys.sort(function (x, y) { const a = f(x, y); return a == 0 ? -1 : (a == 1 ? 0 : 1); });
    return ys;
}

export function $0builtins$1$2buildVec$4sync(l, f) {
    var xs = new Array(l);
    for (var i = 0; i < l; i++) {
        xs[i] = f(i);
    }
    return xs;
}

export async function $0builtins$1$2buildVec$4async(l, f) {
    var xs = new Array(l);
    for (var i = 0; i < l; i++) {
        xs[i] = await f(i);
    }
    return xs;
}

export function $0builtins$1$2IterBuiltins$3collect(iter) {
    if (iter[0] == 0) {
        return [];
    }

    var x = iter[1];
    let xs = [];
    var i = 0;
    for (; ;) {
        xs[i] = x[0];
        iter = x[1]();
        if (iter[0] == 0) { break; }
        x = iter[1];
        i += 1;
    }

    return xs;
}


// This is the best way I can find of reading stdin line by line in Node.
// The builtin readline module does not work when stdin is coming from a non-terminal source
// such as a chess GUI or piped in from cat

import { stdin } from 'process';
var lines = [];

export async function $0builtins$1$2readLine() {
    if (lines.length > 0) {
        var l = lines[0];
        lines = lines.slice(1);
        return l;
    }

    for (; ;) {
        stdin.setEncoding('utf8');

        const s = await new Promise((resolve) => {
            process.stdin.once('data', (s) => {
                resolve(s);
            })
        });

        if (s == '' || s == null) { throw new Error("stdin closed"); }
        lines = s.split("\n");

        return await $0builtins$1$2readLine();
    }
}



export function $0builtins$1$2printLine(s) {
    console.log(s);
}

export function $0builtins$1$2dbgString(s) {
    if (typeof window === 'undefined') {
        console.warn(s);
    }
    else {
        console.log(s);
    }
}


export function $0builtins$1$2randomReal() {
    return Math.random();
}

export function $0builtins$1$2randomInt() {
    return Math.trunc((Math.random() * 2 - 1) * 4503599627370496);
}

export function $0builtins$1$2randomI32() {
    return (Math.random() * 2147483647) | 0;
}

export function $0builtins$1$2getTimeMs() {
    return (new Date()).getTime();
}

