"use strict";
var __haste_prog_id = '0c913d5c5b424102b3b0cdc5155eea4f64fae26677503d096fd3ff0b60052f88';
var __haste_script_elem = typeof document == 'object' ? document.currentScript : null;
// This object will hold all exports.
var Haste = {};
if(typeof window === 'undefined' && typeof global !== 'undefined') window = global;
window['__haste_crypto'] = window.crypto || window.msCrypto;
if(window['__haste_crypto'] && !window['__haste_crypto'].subtle && window.crypto.webkitSubtle) {
    window['__haste_crypto'].subtle = window.crypto.webkitSubtle;
}

/* Constructor functions for small ADTs. */
function T0(t){this._=t;}
function T1(t,a){this._=t;this.a=a;}
function T2(t,a,b){this._=t;this.a=a;this.b=b;}
function T3(t,a,b,c){this._=t;this.a=a;this.b=b;this.c=c;}
function T4(t,a,b,c,d){this._=t;this.a=a;this.b=b;this.c=c;this.d=d;}
function T5(t,a,b,c,d,e){this._=t;this.a=a;this.b=b;this.c=c;this.d=d;this.e=e;}
function T6(t,a,b,c,d,e,f){this._=t;this.a=a;this.b=b;this.c=c;this.d=d;this.e=e;this.f=f;}

/* Thunk
   Creates a thunk representing the given closure.
   If the non-updatable flag is undefined, the thunk is updatable.
*/
function T(f, nu) {
    this.f = f;
    if(nu === undefined) {
        this.x = __updatable;
    }
}

/* Hint to optimizer that an imported symbol is strict. */
function __strict(x) {return x}

// A tailcall.
function F(f) {
    this.f = f;
}

// A partially applied function. Invariant: members are never thunks.
function PAP(f, args) {
    this.f = f;
    this.args = args;
    this.arity = f.length - args.length;
}

// "Zero" object; used to avoid creating a whole bunch of new objects
// in the extremely common case of a nil-like data constructor.
var __Z = new T0(0);

// Special object used for blackholing.
var __blackhole = {};

// Used to indicate that an object is updatable.
var __updatable = {};

// Indicates that a closure-creating tail loop isn't done.
var __continue = {};

/* Generic apply.
   Applies a function *or* a partial application object to a list of arguments.
   See https://ghc.haskell.org/trac/ghc/wiki/Commentary/Rts/HaskellExecution/FunctionCalls
   for more information.
*/
function A(f, args) {
    while(true) {
        f = E(f);
        if(f instanceof Function) {
            if(args.length === f.length) {
                return f.apply(null, args);
            } else if(args.length < f.length) {
                return new PAP(f, args);
            } else {
                var f2 = f.apply(null, args.slice(0, f.length));
                args = args.slice(f.length);
                f = B(f2);
            }
        } else if(f instanceof PAP) {
            if(args.length === f.arity) {
                return f.f.apply(null, f.args.concat(args));
            } else if(args.length < f.arity) {
                return new PAP(f.f, f.args.concat(args));
            } else {
                var f2 = f.f.apply(null, f.args.concat(args.slice(0, f.arity)));
                args = args.slice(f.arity);
                f = B(f2);
            }
        } else {
            return f;
        }
    }
}

function A1(f, x) {
    f = E(f);
    if(f instanceof Function) {
        return f.length === 1 ? f(x) : new PAP(f, [x]);
    } else if(f instanceof PAP) {
        return f.arity === 1 ? f.f.apply(null, f.args.concat([x]))
                             : new PAP(f.f, f.args.concat([x]));
    } else {
        return f;
    }
}

function A2(f, x, y) {
    f = E(f);
    if(f instanceof Function) {
        switch(f.length) {
        case 2:  return f(x, y);
        case 1:  return A1(B(f(x)), y);
        default: return new PAP(f, [x,y]);
        }
    } else if(f instanceof PAP) {
        switch(f.arity) {
        case 2:  return f.f.apply(null, f.args.concat([x,y]));
        case 1:  return A1(B(f.f.apply(null, f.args.concat([x]))), y);
        default: return new PAP(f.f, f.args.concat([x,y]));
        }
    } else {
        return f;
    }
}

function A3(f, x, y, z) {
    f = E(f);
    if(f instanceof Function) {
        switch(f.length) {
        case 3:  return f(x, y, z);
        case 2:  return A1(B(f(x, y)), z);
        case 1:  return A2(B(f(x)), y, z);
        default: return new PAP(f, [x,y,z]);
        }
    } else if(f instanceof PAP) {
        switch(f.arity) {
        case 3:  return f.f.apply(null, f.args.concat([x,y,z]));
        case 2:  return A1(B(f.f.apply(null, f.args.concat([x,y]))), z);
        case 1:  return A2(B(f.f.apply(null, f.args.concat([x]))), y, z);
        default: return new PAP(f.f, f.args.concat([x,y,z]));
        }
    } else {
        return f;
    }
}

/* Eval
   Evaluate the given thunk t into head normal form.
   If the "thunk" we get isn't actually a thunk, just return it.
*/
function E(t) {
    if(t instanceof T) {
        if(t.f !== __blackhole) {
            if(t.x === __updatable) {
                var f = t.f;
                t.f = __blackhole;
                t.x = f();
            } else {
                return t.f();
            }
        }
        if(t.x === __updatable) {
            throw 'Infinite loop!';
        } else {
            return t.x;
        }
    } else {
        return t;
    }
}

/* Tail call chain counter. */
var C = 0, Cs = [];

/* Bounce
   Bounce on a trampoline for as long as we get a function back.
*/
function B(f) {
    Cs.push(C);
    while(f instanceof F) {
        var fun = f.f;
        f.f = __blackhole;
        C = 0;
        f = fun();
    }
    C = Cs.pop();
    return f;
}

// Export Haste, A, B and E. Haste because we need to preserve exports, A, B
// and E because they're handy for Haste.Foreign.
if(!window) {
    var window = {};
}
window['Haste'] = Haste;
window['A'] = A;
window['E'] = E;
window['B'] = B;


/* Throw an error.
   We need to be able to use throw as an exception so we wrap it in a function.
*/
function die(err) {
    throw E(err);
}

function quot(a, b) {
    return (a-a%b)/b;
}

function quotRemI(a, b) {
    return {_:0, a:(a-a%b)/b, b:a%b};
}

// 32 bit integer multiplication, with correct overflow behavior
// note that |0 or >>>0 needs to be applied to the result, for int and word
// respectively.
if(Math.imul) {
    var imul = Math.imul;
} else {
    var imul = function(a, b) {
        // ignore high a * high a as the result will always be truncated
        var lows = (a & 0xffff) * (b & 0xffff); // low a * low b
        var aB = (a & 0xffff) * (b & 0xffff0000); // low a * high b
        var bA = (a & 0xffff0000) * (b & 0xffff); // low b * high a
        return lows + aB + bA; // sum will not exceed 52 bits, so it's safe
    }
}

function addC(a, b) {
    var x = a+b;
    return {_:0, a:x & 0xffffffff, b:x > 0x7fffffff};
}

function subC(a, b) {
    var x = a-b;
    return {_:0, a:x & 0xffffffff, b:x < -2147483648};
}

function sinh (arg) {
    return (Math.exp(arg) - Math.exp(-arg)) / 2;
}

function tanh (arg) {
    return (Math.exp(arg) - Math.exp(-arg)) / (Math.exp(arg) + Math.exp(-arg));
}

function cosh (arg) {
    return (Math.exp(arg) + Math.exp(-arg)) / 2;
}

function isFloatFinite(x) {
    return isFinite(x);
}

function isDoubleFinite(x) {
    return isFinite(x);
}

function err(str) {
    die(toJSStr(str));
}

/* unpackCString#
   NOTE: update constructor tags if the code generator starts munging them.
*/
function unCStr(str) {return unAppCStr(str, __Z);}

function unFoldrCStr(str, f, z) {
    var acc = z;
    for(var i = str.length-1; i >= 0; --i) {
        acc = B(A(f, [str.charCodeAt(i), acc]));
    }
    return acc;
}

function unAppCStr(str, chrs) {
    var i = arguments[2] ? arguments[2] : 0;
    if(i >= str.length) {
        return E(chrs);
    } else {
        return {_:1,a:str.charCodeAt(i),b:new T(function() {
            return unAppCStr(str,chrs,i+1);
        })};
    }
}

function charCodeAt(str, i) {return str.charCodeAt(i);}

function fromJSStr(str) {
    return unCStr(E(str));
}

function toJSStr(hsstr) {
    var s = '';
    for(var str = E(hsstr); str._ == 1; str = E(str.b)) {
        s += String.fromCharCode(E(str.a));
    }
    return s;
}

// newMutVar
function nMV(val) {
    return ({x: val});
}

// readMutVar
function rMV(mv) {
    return mv.x;
}

// writeMutVar
function wMV(mv, val) {
    mv.x = val;
}

// atomicModifyMutVar
function mMV(mv, f) {
    var x = B(A(f, [mv.x]));
    mv.x = x.a;
    return x.b;
}

function localeEncoding() {
    var le = newByteArr(5);
    le['v']['i8'][0] = 'U'.charCodeAt(0);
    le['v']['i8'][1] = 'T'.charCodeAt(0);
    le['v']['i8'][2] = 'F'.charCodeAt(0);
    le['v']['i8'][3] = '-'.charCodeAt(0);
    le['v']['i8'][4] = '8'.charCodeAt(0);
    return le;
}

var isDoubleNaN = isNaN;
var isFloatNaN = isNaN;

function isDoubleInfinite(d) {
    return (d === Infinity);
}
var isFloatInfinite = isDoubleInfinite;

function isDoubleNegativeZero(x) {
    return (x===0 && (1/x)===-Infinity);
}
var isFloatNegativeZero = isDoubleNegativeZero;

function strEq(a, b) {
    return a == b;
}

function strOrd(a, b) {
    if(a < b) {
        return 0;
    } else if(a == b) {
        return 1;
    }
    return 2;
}

/* Convert a JS exception into a Haskell JSException */
function __hsException(e) {
  e = e.toString();
  var x = new Long(738919189, 2683596561, true)
  var y = new Long(3648966346, 573393410, true);
  var t = new T5(0, x, y
                  , new T5(0, x, y
                            , unCStr("haste-prim")
                            , unCStr("Haste.Prim.Foreign")
                            , unCStr("JSException")), __Z, __Z);
  var show = function(x) {return unCStr(E(x).a);}
  var dispEx = function(x) {return unCStr("JavaScript exception: " + E(x).a);}
  var showList = function(_, s) {return unAppCStr(e, s);}
  var showsPrec = function(_, _p, s) {return unAppCStr(e, s);}
  var showDict = new T3(0, showsPrec, show, showList);
  var self;
  var fromEx = function(_) {return new T1(1, self);}
  var dict = new T5(0, t, showDict, null /* toException */, fromEx, dispEx);
  self = new T2(0, dict, new T1(0, e));
  return self;
}

function jsCatch(act, handler) {
    try {
        return B(A(act,[0]));
    } catch(e) {
        if(typeof e._ === 'undefined') {
            e = __hsException(e);
        }
        return B(A(handler,[e, 0]));
    }
}

/* Haste represents constructors internally using 1 for the first constructor,
   2 for the second, etc.
   However, dataToTag should use 0, 1, 2, etc. Also, booleans might be unboxed.
 */
function dataToTag(x) {
    if(x instanceof Object) {
        return x._;
    } else {
        return x;
    }
}

function __word_encodeDouble(d, e) {
    return d * Math.pow(2,e);
}

var __word_encodeFloat = __word_encodeDouble;
var jsRound = Math.round, rintDouble = jsRound, rintFloat = jsRound;
var jsTrunc = Math.trunc ? Math.trunc : function(x) {
    return x < 0 ? Math.ceil(x) : Math.floor(x);
};
function jsRoundW(n) {
    return Math.abs(jsTrunc(n));
}
var realWorld = undefined;
if(typeof _ == 'undefined') {
    var _ = undefined;
}

function popCnt64(i) {
    return popCnt(i.low) + popCnt(i.high);
}

function popCnt(i) {
    i = i - ((i >> 1) & 0x55555555);
    i = (i & 0x33333333) + ((i >> 2) & 0x33333333);
    return (((i + (i >> 4)) & 0x0F0F0F0F) * 0x01010101) >> 24;
}

function __clz(bits, x) {
    x &= (Math.pow(2, bits)-1);
    if(x === 0) {
        return bits;
    } else {
        return bits - (1 + Math.floor(Math.log(x)/Math.LN2));
    }
}

// TODO: can probably be done much faster with arithmetic tricks like __clz
function __ctz(bits, x) {
    var y = 1;
    x &= (Math.pow(2, bits)-1);
    if(x === 0) {
        return bits;
    }
    for(var i = 0; i < bits; ++i) {
        if(y & x) {
            return i;
        } else {
            y <<= 1;
        }
    }
    return 0;
}

// Scratch space for byte arrays.
var rts_scratchBuf = new ArrayBuffer(8);
var rts_scratchW32 = new Uint32Array(rts_scratchBuf);
var rts_scratchFloat = new Float32Array(rts_scratchBuf);
var rts_scratchDouble = new Float64Array(rts_scratchBuf);

function decodeFloat(x) {
    if(x === 0) {
        return __decodedZeroF;
    }
    rts_scratchFloat[0] = x;
    var sign = x < 0 ? -1 : 1;
    var exp = ((rts_scratchW32[0] >> 23) & 0xff) - 150;
    var man = rts_scratchW32[0] & 0x7fffff;
    if(exp === 0) {
        ++exp;
    } else {
        man |= (1 << 23);
    }
    return {_:0, a:sign*man, b:exp};
}

var __decodedZero = {_:0,a:1,b:0,c:0,d:0};
var __decodedZeroF = {_:0,a:1,b:0};

function decodeDouble(x) {
    if(x === 0) {
        // GHC 7.10+ *really* doesn't like 0 to be represented as anything
        // but zeroes all the way.
        return __decodedZero;
    }
    rts_scratchDouble[0] = x;
    var sign = x < 0 ? -1 : 1;
    var manHigh = rts_scratchW32[1] & 0xfffff;
    var manLow = rts_scratchW32[0];
    var exp = ((rts_scratchW32[1] >> 20) & 0x7ff) - 1075;
    if(exp === 0) {
        ++exp;
    } else {
        manHigh |= (1 << 20);
    }
    return {_:0, a:sign, b:manHigh, c:manLow, d:exp};
}

function isNull(obj) {
    return obj === null;
}

function jsRead(str) {
    return Number(str);
}

function jsShowI(val) {return val.toString();}
function jsShow(val) {
    var ret = val.toString();
    return val == Math.round(val) ? ret + '.0' : ret;
}

window['jsGetMouseCoords'] = function jsGetMouseCoords(e) {
    var posx = 0;
    var posy = 0;
    if (!e) var e = window.event;
    if (e.pageX || e.pageY) 	{
	posx = e.pageX;
	posy = e.pageY;
    }
    else if (e.clientX || e.clientY) 	{
	posx = e.clientX + document.body.scrollLeft
	    + document.documentElement.scrollLeft;
	posy = e.clientY + document.body.scrollTop
	    + document.documentElement.scrollTop;
    }
    return [posx - (e.currentTarget.offsetLeft || 0),
	    posy - (e.currentTarget.offsetTop || 0)];
}

var jsRand = Math.random;

// Concatenate a Haskell list of JS strings
function jsCat(strs, sep) {
    var arr = [];
    strs = E(strs);
    while(strs._) {
        strs = E(strs);
        arr.push(E(strs.a));
        strs = E(strs.b);
    }
    return arr.join(sep);
}

// Parse a JSON message into a Haste.JSON.JSON value.
// As this pokes around inside Haskell values, it'll need to be updated if:
// * Haste.JSON.JSON changes;
// * E() starts to choke on non-thunks;
// * data constructor code generation changes; or
// * Just and Nothing change tags.
function jsParseJSON(str) {
    try {
        var js = JSON.parse(str);
        var hs = toHS(js);
    } catch(_) {
        return __Z;
    }
    return {_:1,a:hs};
}

function toHS(obj) {
    switch(typeof obj) {
    case 'number':
        return {_:0, a:jsRead(obj)};
    case 'string':
        return {_:1, a:obj};
    case 'boolean':
        return {_:2, a:obj}; // Booleans are special wrt constructor tags!
    case 'object':
        if(obj instanceof Array) {
            return {_:3, a:arr2lst_json(obj, 0)};
        } else if (obj == null) {
            return {_:5};
        } else {
            // Object type but not array - it's a dictionary.
            // The RFC doesn't say anything about the ordering of keys, but
            // considering that lots of people rely on keys being "in order" as
            // defined by "the same way someone put them in at the other end,"
            // it's probably a good idea to put some cycles into meeting their
            // misguided expectations.
            var ks = [];
            for(var k in obj) {
                ks.unshift(k);
            }
            var xs = [0];
            for(var i = 0; i < ks.length; i++) {
                xs = {_:1, a:{_:0, a:ks[i], b:toHS(obj[ks[i]])}, b:xs};
            }
            return {_:4, a:xs};
        }
    }
}

function arr2lst_json(arr, elem) {
    if(elem >= arr.length) {
        return __Z;
    }
    return {_:1, a:toHS(arr[elem]), b:new T(function() {return arr2lst_json(arr,elem+1);}),c:true}
}

/* gettimeofday(2) */
function gettimeofday(tv, _tz) {
    var t = new Date().getTime();
    writeOffAddr("i32", 4, tv, 0, (t/1000)|0);
    writeOffAddr("i32", 4, tv, 1, ((t%1000)*1000)|0);
    return 0;
}

// Create a little endian ArrayBuffer representation of something.
function toABHost(v, n, x) {
    var a = new ArrayBuffer(n);
    new window[v](a)[0] = x;
    return a;
}

function toABSwap(v, n, x) {
    var a = new ArrayBuffer(n);
    new window[v](a)[0] = x;
    var bs = new Uint8Array(a);
    for(var i = 0, j = n-1; i < j; ++i, --j) {
        var tmp = bs[i];
        bs[i] = bs[j];
        bs[j] = tmp;
    }
    return a;
}

window['toABle'] = toABHost;
window['toABbe'] = toABSwap;

// Swap byte order if host is not little endian.
var buffer = new ArrayBuffer(2);
new DataView(buffer).setInt16(0, 256, true);
if(new Int16Array(buffer)[0] !== 256) {
    window['toABle'] = toABSwap;
    window['toABbe'] = toABHost;
}

/* bn.js by Fedor Indutny, see doc/LICENSE.bn for license */
var __bn = {};
(function (module, exports) {
'use strict';

function BN(number, base, endian) {
  // May be `new BN(bn)` ?
  if (number !== null &&
      typeof number === 'object' &&
      Array.isArray(number.words)) {
    return number;
  }

  this.negative = 0;
  this.words = null;
  this.length = 0;

  if (base === 'le' || base === 'be') {
    endian = base;
    base = 10;
  }

  if (number !== null)
    this._init(number || 0, base || 10, endian || 'be');
}
if (typeof module === 'object')
  module.exports = BN;
else
  exports.BN = BN;

BN.BN = BN;
BN.wordSize = 26;

BN.max = function max(left, right) {
  if (left.cmp(right) > 0)
    return left;
  else
    return right;
};

BN.min = function min(left, right) {
  if (left.cmp(right) < 0)
    return left;
  else
    return right;
};

BN.prototype._init = function init(number, base, endian) {
  if (typeof number === 'number') {
    return this._initNumber(number, base, endian);
  } else if (typeof number === 'object') {
    return this._initArray(number, base, endian);
  }
  if (base === 'hex')
    base = 16;

  number = number.toString().replace(/\s+/g, '');
  var start = 0;
  if (number[0] === '-')
    start++;

  if (base === 16)
    this._parseHex(number, start);
  else
    this._parseBase(number, base, start);

  if (number[0] === '-')
    this.negative = 1;

  this.strip();

  if (endian !== 'le')
    return;

  this._initArray(this.toArray(), base, endian);
};

BN.prototype._initNumber = function _initNumber(number, base, endian) {
  if (number < 0) {
    this.negative = 1;
    number = -number;
  }
  if (number < 0x4000000) {
    this.words = [ number & 0x3ffffff ];
    this.length = 1;
  } else if (number < 0x10000000000000) {
    this.words = [
      number & 0x3ffffff,
      (number / 0x4000000) & 0x3ffffff
    ];
    this.length = 2;
  } else {
    this.words = [
      number & 0x3ffffff,
      (number / 0x4000000) & 0x3ffffff,
      1
    ];
    this.length = 3;
  }

  if (endian !== 'le')
    return;

  // Reverse the bytes
  this._initArray(this.toArray(), base, endian);
};

BN.prototype._initArray = function _initArray(number, base, endian) {
  if (number.length <= 0) {
    this.words = [ 0 ];
    this.length = 1;
    return this;
  }

  this.length = Math.ceil(number.length / 3);
  this.words = new Array(this.length);
  for (var i = 0; i < this.length; i++)
    this.words[i] = 0;

  var off = 0;
  if (endian === 'be') {
    for (var i = number.length - 1, j = 0; i >= 0; i -= 3) {
      var w = number[i] | (number[i - 1] << 8) | (number[i - 2] << 16);
      this.words[j] |= (w << off) & 0x3ffffff;
      this.words[j + 1] = (w >>> (26 - off)) & 0x3ffffff;
      off += 24;
      if (off >= 26) {
        off -= 26;
        j++;
      }
    }
  } else if (endian === 'le') {
    for (var i = 0, j = 0; i < number.length; i += 3) {
      var w = number[i] | (number[i + 1] << 8) | (number[i + 2] << 16);
      this.words[j] |= (w << off) & 0x3ffffff;
      this.words[j + 1] = (w >>> (26 - off)) & 0x3ffffff;
      off += 24;
      if (off >= 26) {
        off -= 26;
        j++;
      }
    }
  }
  return this.strip();
};

function parseHex(str, start, end) {
  var r = 0;
  var len = Math.min(str.length, end);
  for (var i = start; i < len; i++) {
    var c = str.charCodeAt(i) - 48;

    r <<= 4;

    // 'a' - 'f'
    if (c >= 49 && c <= 54)
      r |= c - 49 + 0xa;

    // 'A' - 'F'
    else if (c >= 17 && c <= 22)
      r |= c - 17 + 0xa;

    // '0' - '9'
    else
      r |= c & 0xf;
  }
  return r;
}

BN.prototype._parseHex = function _parseHex(number, start) {
  // Create possibly bigger array to ensure that it fits the number
  this.length = Math.ceil((number.length - start) / 6);
  this.words = new Array(this.length);
  for (var i = 0; i < this.length; i++)
    this.words[i] = 0;

  // Scan 24-bit chunks and add them to the number
  var off = 0;
  for (var i = number.length - 6, j = 0; i >= start; i -= 6) {
    var w = parseHex(number, i, i + 6);
    this.words[j] |= (w << off) & 0x3ffffff;
    this.words[j + 1] |= w >>> (26 - off) & 0x3fffff;
    off += 24;
    if (off >= 26) {
      off -= 26;
      j++;
    }
  }
  if (i + 6 !== start) {
    var w = parseHex(number, start, i + 6);
    this.words[j] |= (w << off) & 0x3ffffff;
    this.words[j + 1] |= w >>> (26 - off) & 0x3fffff;
  }
  this.strip();
};

function parseBase(str, start, end, mul) {
  var r = 0;
  var len = Math.min(str.length, end);
  for (var i = start; i < len; i++) {
    var c = str.charCodeAt(i) - 48;

    r *= mul;

    // 'a'
    if (c >= 49)
      r += c - 49 + 0xa;

    // 'A'
    else if (c >= 17)
      r += c - 17 + 0xa;

    // '0' - '9'
    else
      r += c;
  }
  return r;
}

BN.prototype._parseBase = function _parseBase(number, base, start) {
  // Initialize as zero
  this.words = [ 0 ];
  this.length = 1;

  // Find length of limb in base
  for (var limbLen = 0, limbPow = 1; limbPow <= 0x3ffffff; limbPow *= base)
    limbLen++;
  limbLen--;
  limbPow = (limbPow / base) | 0;

  var total = number.length - start;
  var mod = total % limbLen;
  var end = Math.min(total, total - mod) + start;

  var word = 0;
  for (var i = start; i < end; i += limbLen) {
    word = parseBase(number, i, i + limbLen, base);

    this.imuln(limbPow);
    if (this.words[0] + word < 0x4000000)
      this.words[0] += word;
    else
      this._iaddn(word);
  }

  if (mod !== 0) {
    var pow = 1;
    var word = parseBase(number, i, number.length, base);

    for (var i = 0; i < mod; i++)
      pow *= base;
    this.imuln(pow);
    if (this.words[0] + word < 0x4000000)
      this.words[0] += word;
    else
      this._iaddn(word);
  }
};

BN.prototype.copy = function copy(dest) {
  dest.words = new Array(this.length);
  for (var i = 0; i < this.length; i++)
    dest.words[i] = this.words[i];
  dest.length = this.length;
  dest.negative = this.negative;
};

BN.prototype.clone = function clone() {
  var r = new BN(null);
  this.copy(r);
  return r;
};

// Remove leading `0` from `this`
BN.prototype.strip = function strip() {
  while (this.length > 1 && this.words[this.length - 1] === 0)
    this.length--;
  return this._normSign();
};

BN.prototype._normSign = function _normSign() {
  // -0 = 0
  if (this.length === 1 && this.words[0] === 0)
    this.negative = 0;
  return this;
};

var zeros = [
  '',
  '0',
  '00',
  '000',
  '0000',
  '00000',
  '000000',
  '0000000',
  '00000000',
  '000000000',
  '0000000000',
  '00000000000',
  '000000000000',
  '0000000000000',
  '00000000000000',
  '000000000000000',
  '0000000000000000',
  '00000000000000000',
  '000000000000000000',
  '0000000000000000000',
  '00000000000000000000',
  '000000000000000000000',
  '0000000000000000000000',
  '00000000000000000000000',
  '000000000000000000000000',
  '0000000000000000000000000'
];

var groupSizes = [
  0, 0,
  25, 16, 12, 11, 10, 9, 8,
  8, 7, 7, 7, 7, 6, 6,
  6, 6, 6, 6, 6, 5, 5,
  5, 5, 5, 5, 5, 5, 5,
  5, 5, 5, 5, 5, 5, 5
];

var groupBases = [
  0, 0,
  33554432, 43046721, 16777216, 48828125, 60466176, 40353607, 16777216,
  43046721, 10000000, 19487171, 35831808, 62748517, 7529536, 11390625,
  16777216, 24137569, 34012224, 47045881, 64000000, 4084101, 5153632,
  6436343, 7962624, 9765625, 11881376, 14348907, 17210368, 20511149,
  24300000, 28629151, 33554432, 39135393, 45435424, 52521875, 60466176
];

BN.prototype.toString = function toString(base, padding) {
  base = base || 10;
  var padding = padding | 0 || 1;
  if (base === 16 || base === 'hex') {
    var out = '';
    var off = 0;
    var carry = 0;
    for (var i = 0; i < this.length; i++) {
      var w = this.words[i];
      var word = (((w << off) | carry) & 0xffffff).toString(16);
      carry = (w >>> (24 - off)) & 0xffffff;
      if (carry !== 0 || i !== this.length - 1)
        out = zeros[6 - word.length] + word + out;
      else
        out = word + out;
      off += 2;
      if (off >= 26) {
        off -= 26;
        i--;
      }
    }
    if (carry !== 0)
      out = carry.toString(16) + out;
    while (out.length % padding !== 0)
      out = '0' + out;
    if (this.negative !== 0)
      out = '-' + out;
    return out;
  } else if (base === (base | 0) && base >= 2 && base <= 36) {
    var groupSize = groupSizes[base];
    var groupBase = groupBases[base];
    var out = '';
    var c = this.clone();
    c.negative = 0;
    while (c.cmpn(0) !== 0) {
      var r = c.modn(groupBase).toString(base);
      c = c.idivn(groupBase);

      if (c.cmpn(0) !== 0)
        out = zeros[groupSize - r.length] + r + out;
      else
        out = r + out;
    }
    if (this.cmpn(0) === 0)
      out = '0' + out;
    while (out.length % padding !== 0)
      out = '0' + out;
    if (this.negative !== 0)
      out = '-' + out;
    return out;
  } else {
    throw 'Base should be between 2 and 36';
  }
};

BN.prototype.toJSON = function toJSON() {
  return this.toString(16);
};

BN.prototype.toArray = function toArray(endian, length) {
  this.strip();
  var littleEndian = endian === 'le';
  var res = new Array(this.byteLength());
  res[0] = 0;

  var q = this.clone();
  if (!littleEndian) {
    // Assume big-endian
    for (var i = 0; q.cmpn(0) !== 0; i++) {
      var b = q.andln(0xff);
      q.iushrn(8);

      res[res.length - i - 1] = b;
    }
  } else {
    for (var i = 0; q.cmpn(0) !== 0; i++) {
      var b = q.andln(0xff);
      q.iushrn(8);

      res[i] = b;
    }
  }

  if (length) {
    while (res.length < length) {
      if (littleEndian)
        res.push(0);
      else
        res.unshift(0);
    }
  }

  return res;
};

if (Math.clz32) {
  BN.prototype._countBits = function _countBits(w) {
    return 32 - Math.clz32(w);
  };
} else {
  BN.prototype._countBits = function _countBits(w) {
    var t = w;
    var r = 0;
    if (t >= 0x1000) {
      r += 13;
      t >>>= 13;
    }
    if (t >= 0x40) {
      r += 7;
      t >>>= 7;
    }
    if (t >= 0x8) {
      r += 4;
      t >>>= 4;
    }
    if (t >= 0x02) {
      r += 2;
      t >>>= 2;
    }
    return r + t;
  };
}

// Return number of used bits in a BN
BN.prototype.bitLength = function bitLength() {
  var hi = 0;
  var w = this.words[this.length - 1];
  var hi = this._countBits(w);
  return (this.length - 1) * 26 + hi;
};

BN.prototype.byteLength = function byteLength() {
  return Math.ceil(this.bitLength() / 8);
};

// Return negative clone of `this`
BN.prototype.neg = function neg() {
  if (this.cmpn(0) === 0)
    return this.clone();

  var r = this.clone();
  r.negative = this.negative ^ 1;
  return r;
};

BN.prototype.ineg = function ineg() {
  this.negative ^= 1;
  return this;
};

// Or `num` with `this` in-place
BN.prototype.iuor = function iuor(num) {
  while (this.length < num.length)
    this.words[this.length++] = 0;

  for (var i = 0; i < num.length; i++)
    this.words[i] = this.words[i] | num.words[i];

  return this.strip();
};

BN.prototype.ior = function ior(num) {
  //assert((this.negative | num.negative) === 0);
  return this.iuor(num);
};


// Or `num` with `this`
BN.prototype.or = function or(num) {
  if (this.length > num.length)
    return this.clone().ior(num);
  else
    return num.clone().ior(this);
};

BN.prototype.uor = function uor(num) {
  if (this.length > num.length)
    return this.clone().iuor(num);
  else
    return num.clone().iuor(this);
};


// And `num` with `this` in-place
BN.prototype.iuand = function iuand(num) {
  // b = min-length(num, this)
  var b;
  if (this.length > num.length)
    b = num;
  else
    b = this;

  for (var i = 0; i < b.length; i++)
    this.words[i] = this.words[i] & num.words[i];

  this.length = b.length;

  return this.strip();
};

BN.prototype.iand = function iand(num) {
  //assert((this.negative | num.negative) === 0);
  return this.iuand(num);
};


// And `num` with `this`
BN.prototype.and = function and(num) {
  if (this.length > num.length)
    return this.clone().iand(num);
  else
    return num.clone().iand(this);
};

BN.prototype.uand = function uand(num) {
  if (this.length > num.length)
    return this.clone().iuand(num);
  else
    return num.clone().iuand(this);
};


// Xor `num` with `this` in-place
BN.prototype.iuxor = function iuxor(num) {
  // a.length > b.length
  var a;
  var b;
  if (this.length > num.length) {
    a = this;
    b = num;
  } else {
    a = num;
    b = this;
  }

  for (var i = 0; i < b.length; i++)
    this.words[i] = a.words[i] ^ b.words[i];

  if (this !== a)
    for (; i < a.length; i++)
      this.words[i] = a.words[i];

  this.length = a.length;

  return this.strip();
};

BN.prototype.ixor = function ixor(num) {
  //assert((this.negative | num.negative) === 0);
  return this.iuxor(num);
};


// Xor `num` with `this`
BN.prototype.xor = function xor(num) {
  if (this.length > num.length)
    return this.clone().ixor(num);
  else
    return num.clone().ixor(this);
};

BN.prototype.uxor = function uxor(num) {
  if (this.length > num.length)
    return this.clone().iuxor(num);
  else
    return num.clone().iuxor(this);
};


// Add `num` to `this` in-place
BN.prototype.iadd = function iadd(num) {
  // negative + positive
  if (this.negative !== 0 && num.negative === 0) {
    this.negative = 0;
    var r = this.isub(num);
    this.negative ^= 1;
    return this._normSign();

  // positive + negative
  } else if (this.negative === 0 && num.negative !== 0) {
    num.negative = 0;
    var r = this.isub(num);
    num.negative = 1;
    return r._normSign();
  }

  // a.length > b.length
  var a;
  var b;
  if (this.length > num.length) {
    a = this;
    b = num;
  } else {
    a = num;
    b = this;
  }

  var carry = 0;
  for (var i = 0; i < b.length; i++) {
    var r = (a.words[i] | 0) + (b.words[i] | 0) + carry;
    this.words[i] = r & 0x3ffffff;
    carry = r >>> 26;
  }
  for (; carry !== 0 && i < a.length; i++) {
    var r = (a.words[i] | 0) + carry;
    this.words[i] = r & 0x3ffffff;
    carry = r >>> 26;
  }

  this.length = a.length;
  if (carry !== 0) {
    this.words[this.length] = carry;
    this.length++;
  // Copy the rest of the words
  } else if (a !== this) {
    for (; i < a.length; i++)
      this.words[i] = a.words[i];
  }

  return this;
};

// Add `num` to `this`
BN.prototype.add = function add(num) {
  if (num.negative !== 0 && this.negative === 0) {
    num.negative = 0;
    var res = this.sub(num);
    num.negative ^= 1;
    return res;
  } else if (num.negative === 0 && this.negative !== 0) {
    this.negative = 0;
    var res = num.sub(this);
    this.negative = 1;
    return res;
  }

  if (this.length > num.length)
    return this.clone().iadd(num);
  else
    return num.clone().iadd(this);
};

// Subtract `num` from `this` in-place
BN.prototype.isub = function isub(num) {
  // this - (-num) = this + num
  if (num.negative !== 0) {
    num.negative = 0;
    var r = this.iadd(num);
    num.negative = 1;
    return r._normSign();

  // -this - num = -(this + num)
  } else if (this.negative !== 0) {
    this.negative = 0;
    this.iadd(num);
    this.negative = 1;
    return this._normSign();
  }

  // At this point both numbers are positive
  var cmp = this.cmp(num);

  // Optimization - zeroify
  if (cmp === 0) {
    this.negative = 0;
    this.length = 1;
    this.words[0] = 0;
    return this;
  }

  // a > b
  var a;
  var b;
  if (cmp > 0) {
    a = this;
    b = num;
  } else {
    a = num;
    b = this;
  }

  var carry = 0;
  for (var i = 0; i < b.length; i++) {
    var r = (a.words[i] | 0) - (b.words[i] | 0) + carry;
    carry = r >> 26;
    this.words[i] = r & 0x3ffffff;
  }
  for (; carry !== 0 && i < a.length; i++) {
    var r = (a.words[i] | 0) + carry;
    carry = r >> 26;
    this.words[i] = r & 0x3ffffff;
  }

  // Copy rest of the words
  if (carry === 0 && i < a.length && a !== this)
    for (; i < a.length; i++)
      this.words[i] = a.words[i];
  this.length = Math.max(this.length, i);

  if (a !== this)
    this.negative = 1;

  return this.strip();
};

// Subtract `num` from `this`
BN.prototype.sub = function sub(num) {
  return this.clone().isub(num);
};

function smallMulTo(self, num, out) {
  out.negative = num.negative ^ self.negative;
  var len = (self.length + num.length) | 0;
  out.length = len;
  len = (len - 1) | 0;

  // Peel one iteration (compiler can't do it, because of code complexity)
  var a = self.words[0] | 0;
  var b = num.words[0] | 0;
  var r = a * b;

  var lo = r & 0x3ffffff;
  var carry = (r / 0x4000000) | 0;
  out.words[0] = lo;

  for (var k = 1; k < len; k++) {
    // Sum all words with the same `i + j = k` and accumulate `ncarry`,
    // note that ncarry could be >= 0x3ffffff
    var ncarry = carry >>> 26;
    var rword = carry & 0x3ffffff;
    var maxJ = Math.min(k, num.length - 1);
    for (var j = Math.max(0, k - self.length + 1); j <= maxJ; j++) {
      var i = (k - j) | 0;
      var a = self.words[i] | 0;
      var b = num.words[j] | 0;
      var r = a * b;

      var lo = r & 0x3ffffff;
      ncarry = (ncarry + ((r / 0x4000000) | 0)) | 0;
      lo = (lo + rword) | 0;
      rword = lo & 0x3ffffff;
      ncarry = (ncarry + (lo >>> 26)) | 0;
    }
    out.words[k] = rword | 0;
    carry = ncarry | 0;
  }
  if (carry !== 0) {
    out.words[k] = carry | 0;
  } else {
    out.length--;
  }

  return out.strip();
}

function bigMulTo(self, num, out) {
  out.negative = num.negative ^ self.negative;
  out.length = self.length + num.length;

  var carry = 0;
  var hncarry = 0;
  for (var k = 0; k < out.length - 1; k++) {
    // Sum all words with the same `i + j = k` and accumulate `ncarry`,
    // note that ncarry could be >= 0x3ffffff
    var ncarry = hncarry;
    hncarry = 0;
    var rword = carry & 0x3ffffff;
    var maxJ = Math.min(k, num.length - 1);
    for (var j = Math.max(0, k - self.length + 1); j <= maxJ; j++) {
      var i = k - j;
      var a = self.words[i] | 0;
      var b = num.words[j] | 0;
      var r = a * b;

      var lo = r & 0x3ffffff;
      ncarry = (ncarry + ((r / 0x4000000) | 0)) | 0;
      lo = (lo + rword) | 0;
      rword = lo & 0x3ffffff;
      ncarry = (ncarry + (lo >>> 26)) | 0;

      hncarry += ncarry >>> 26;
      ncarry &= 0x3ffffff;
    }
    out.words[k] = rword;
    carry = ncarry;
    ncarry = hncarry;
  }
  if (carry !== 0) {
    out.words[k] = carry;
  } else {
    out.length--;
  }

  return out.strip();
}

BN.prototype.mulTo = function mulTo(num, out) {
  var res;
  if (this.length + num.length < 63)
    res = smallMulTo(this, num, out);
  else
    res = bigMulTo(this, num, out);
  return res;
};

// Multiply `this` by `num`
BN.prototype.mul = function mul(num) {
  var out = new BN(null);
  out.words = new Array(this.length + num.length);
  return this.mulTo(num, out);
};

// In-place Multiplication
BN.prototype.imul = function imul(num) {
  if (this.cmpn(0) === 0 || num.cmpn(0) === 0) {
    this.words[0] = 0;
    this.length = 1;
    return this;
  }

  var tlen = this.length;
  var nlen = num.length;

  this.negative = num.negative ^ this.negative;
  this.length = this.length + num.length;
  this.words[this.length - 1] = 0;

  for (var k = this.length - 2; k >= 0; k--) {
    // Sum all words with the same `i + j = k` and accumulate `carry`,
    // note that carry could be >= 0x3ffffff
    var carry = 0;
    var rword = 0;
    var maxJ = Math.min(k, nlen - 1);
    for (var j = Math.max(0, k - tlen + 1); j <= maxJ; j++) {
      var i = k - j;
      var a = this.words[i] | 0;
      var b = num.words[j] | 0;
      var r = a * b;

      var lo = r & 0x3ffffff;
      carry += (r / 0x4000000) | 0;
      lo += rword;
      rword = lo & 0x3ffffff;
      carry += lo >>> 26;
    }
    this.words[k] = rword;
    this.words[k + 1] += carry;
    carry = 0;
  }

  // Propagate overflows
  var carry = 0;
  for (var i = 1; i < this.length; i++) {
    var w = (this.words[i] | 0) + carry;
    this.words[i] = w & 0x3ffffff;
    carry = w >>> 26;
  }

  return this.strip();
};

BN.prototype.imuln = function imuln(num) {
  // Carry
  var carry = 0;
  for (var i = 0; i < this.length; i++) {
    var w = (this.words[i] | 0) * num;
    var lo = (w & 0x3ffffff) + (carry & 0x3ffffff);
    carry >>= 26;
    carry += (w / 0x4000000) | 0;
    // NOTE: lo is 27bit maximum
    carry += lo >>> 26;
    this.words[i] = lo & 0x3ffffff;
  }

  if (carry !== 0) {
    this.words[i] = carry;
    this.length++;
  }

  return this;
};

BN.prototype.muln = function muln(num) {
  return this.clone().imuln(num);
};

// `this` * `this`
BN.prototype.sqr = function sqr() {
  return this.mul(this);
};

// `this` * `this` in-place
BN.prototype.isqr = function isqr() {
  return this.mul(this);
};

// Shift-left in-place
BN.prototype.iushln = function iushln(bits) {
  var r = bits % 26;
  var s = (bits - r) / 26;
  var carryMask = (0x3ffffff >>> (26 - r)) << (26 - r);

  if (r !== 0) {
    var carry = 0;
    for (var i = 0; i < this.length; i++) {
      var newCarry = this.words[i] & carryMask;
      var c = ((this.words[i] | 0) - newCarry) << r;
      this.words[i] = c | carry;
      carry = newCarry >>> (26 - r);
    }
    if (carry) {
      this.words[i] = carry;
      this.length++;
    }
  }

  if (s !== 0) {
    for (var i = this.length - 1; i >= 0; i--)
      this.words[i + s] = this.words[i];
    for (var i = 0; i < s; i++)
      this.words[i] = 0;
    this.length += s;
  }

  return this.strip();
};

BN.prototype.ishln = function ishln(bits) {
  return this.iushln(bits);
};

// Shift-right in-place
BN.prototype.iushrn = function iushrn(bits, hint, extended) {
  var h;
  if (hint)
    h = (hint - (hint % 26)) / 26;
  else
    h = 0;

  var r = bits % 26;
  var s = Math.min((bits - r) / 26, this.length);
  var mask = 0x3ffffff ^ ((0x3ffffff >>> r) << r);
  var maskedWords = extended;

  h -= s;
  h = Math.max(0, h);

  // Extended mode, copy masked part
  if (maskedWords) {
    for (var i = 0; i < s; i++)
      maskedWords.words[i] = this.words[i];
    maskedWords.length = s;
  }

  if (s === 0) {
    // No-op, we should not move anything at all
  } else if (this.length > s) {
    this.length -= s;
    for (var i = 0; i < this.length; i++)
      this.words[i] = this.words[i + s];
  } else {
    this.words[0] = 0;
    this.length = 1;
  }

  var carry = 0;
  for (var i = this.length - 1; i >= 0 && (carry !== 0 || i >= h); i--) {
    var word = this.words[i] | 0;
    this.words[i] = (carry << (26 - r)) | (word >>> r);
    carry = word & mask;
  }

  // Push carried bits as a mask
  if (maskedWords && carry !== 0)
    maskedWords.words[maskedWords.length++] = carry;

  if (this.length === 0) {
    this.words[0] = 0;
    this.length = 1;
  }

  this.strip();

  return this;
};

BN.prototype.ishrn = function ishrn(bits, hint, extended) {
  return this.iushrn(bits, hint, extended);
};

// Shift-left
BN.prototype.shln = function shln(bits) {
  var x = this.clone();
  var neg = x.negative;
  x.negative = false;
  x.ishln(bits);
  x.negative = neg;
  return x;
};

BN.prototype.ushln = function ushln(bits) {
  return this.clone().iushln(bits);
};

// Shift-right
BN.prototype.shrn = function shrn(bits) {
  var x = this.clone();
  if(x.negative) {
      x.negative = false;
      x.ishrn(bits);
      x.negative = true;
      return x.isubn(1);
  } else {
      return x.ishrn(bits);
  }
};

BN.prototype.ushrn = function ushrn(bits) {
  return this.clone().iushrn(bits);
};

// Test if n bit is set
BN.prototype.testn = function testn(bit) {
  var r = bit % 26;
  var s = (bit - r) / 26;
  var q = 1 << r;

  // Fast case: bit is much higher than all existing words
  if (this.length <= s) {
    return false;
  }

  // Check bit and return
  var w = this.words[s];

  return !!(w & q);
};

// Add plain number `num` to `this`
BN.prototype.iaddn = function iaddn(num) {
  if (num < 0)
    return this.isubn(-num);

  // Possible sign change
  if (this.negative !== 0) {
    if (this.length === 1 && (this.words[0] | 0) < num) {
      this.words[0] = num - (this.words[0] | 0);
      this.negative = 0;
      return this;
    }

    this.negative = 0;
    this.isubn(num);
    this.negative = 1;
    return this;
  }

  // Add without checks
  return this._iaddn(num);
};

BN.prototype._iaddn = function _iaddn(num) {
  this.words[0] += num;

  // Carry
  for (var i = 0; i < this.length && this.words[i] >= 0x4000000; i++) {
    this.words[i] -= 0x4000000;
    if (i === this.length - 1)
      this.words[i + 1] = 1;
    else
      this.words[i + 1]++;
  }
  this.length = Math.max(this.length, i + 1);

  return this;
};

// Subtract plain number `num` from `this`
BN.prototype.isubn = function isubn(num) {
  if (num < 0)
    return this.iaddn(-num);

  if (this.negative !== 0) {
    this.negative = 0;
    this.iaddn(num);
    this.negative = 1;
    return this;
  }

  this.words[0] -= num;

  // Carry
  for (var i = 0; i < this.length && this.words[i] < 0; i++) {
    this.words[i] += 0x4000000;
    this.words[i + 1] -= 1;
  }

  return this.strip();
};

BN.prototype.addn = function addn(num) {
  return this.clone().iaddn(num);
};

BN.prototype.subn = function subn(num) {
  return this.clone().isubn(num);
};

BN.prototype.iabs = function iabs() {
  this.negative = 0;

  return this;
};

BN.prototype.abs = function abs() {
  return this.clone().iabs();
};

BN.prototype._ishlnsubmul = function _ishlnsubmul(num, mul, shift) {
  // Bigger storage is needed
  var len = num.length + shift;
  var i;
  if (this.words.length < len) {
    var t = new Array(len);
    for (var i = 0; i < this.length; i++)
      t[i] = this.words[i];
    this.words = t;
  } else {
    i = this.length;
  }

  // Zeroify rest
  this.length = Math.max(this.length, len);
  for (; i < this.length; i++)
    this.words[i] = 0;

  var carry = 0;
  for (var i = 0; i < num.length; i++) {
    var w = (this.words[i + shift] | 0) + carry;
    var right = (num.words[i] | 0) * mul;
    w -= right & 0x3ffffff;
    carry = (w >> 26) - ((right / 0x4000000) | 0);
    this.words[i + shift] = w & 0x3ffffff;
  }
  for (; i < this.length - shift; i++) {
    var w = (this.words[i + shift] | 0) + carry;
    carry = w >> 26;
    this.words[i + shift] = w & 0x3ffffff;
  }

  if (carry === 0)
    return this.strip();

  carry = 0;
  for (var i = 0; i < this.length; i++) {
    var w = -(this.words[i] | 0) + carry;
    carry = w >> 26;
    this.words[i] = w & 0x3ffffff;
  }
  this.negative = 1;

  return this.strip();
};

BN.prototype._wordDiv = function _wordDiv(num, mode) {
  var shift = this.length - num.length;

  var a = this.clone();
  var b = num;

  // Normalize
  var bhi = b.words[b.length - 1] | 0;
  var bhiBits = this._countBits(bhi);
  shift = 26 - bhiBits;
  if (shift !== 0) {
    b = b.ushln(shift);
    a.iushln(shift);
    bhi = b.words[b.length - 1] | 0;
  }

  // Initialize quotient
  var m = a.length - b.length;
  var q;

  if (mode !== 'mod') {
    q = new BN(null);
    q.length = m + 1;
    q.words = new Array(q.length);
    for (var i = 0; i < q.length; i++)
      q.words[i] = 0;
  }

  var diff = a.clone()._ishlnsubmul(b, 1, m);
  if (diff.negative === 0) {
    a = diff;
    if (q)
      q.words[m] = 1;
  }

  for (var j = m - 1; j >= 0; j--) {
    var qj = (a.words[b.length + j] | 0) * 0x4000000 +
             (a.words[b.length + j - 1] | 0);

    // NOTE: (qj / bhi) is (0x3ffffff * 0x4000000 + 0x3ffffff) / 0x2000000 max
    // (0x7ffffff)
    qj = Math.min((qj / bhi) | 0, 0x3ffffff);

    a._ishlnsubmul(b, qj, j);
    while (a.negative !== 0) {
      qj--;
      a.negative = 0;
      a._ishlnsubmul(b, 1, j);
      if (a.cmpn(0) !== 0)
        a.negative ^= 1;
    }
    if (q)
      q.words[j] = qj;
  }
  if (q)
    q.strip();
  a.strip();

  // Denormalize
  if (mode !== 'div' && shift !== 0)
    a.iushrn(shift);
  return { div: q ? q : null, mod: a };
};

BN.prototype.divmod = function divmod(num, mode, positive) {
  if (this.negative !== 0 && num.negative === 0) {
    var res = this.neg().divmod(num, mode);
    var div;
    var mod;
    if (mode !== 'mod')
      div = res.div.neg();
    if (mode !== 'div') {
      mod = res.mod.neg();
      if (positive && mod.neg)
        mod = mod.add(num);
    }
    return {
      div: div,
      mod: mod
    };
  } else if (this.negative === 0 && num.negative !== 0) {
    var res = this.divmod(num.neg(), mode);
    var div;
    if (mode !== 'mod')
      div = res.div.neg();
    return { div: div, mod: res.mod };
  } else if ((this.negative & num.negative) !== 0) {
    var res = this.neg().divmod(num.neg(), mode);
    var mod;
    if (mode !== 'div') {
      mod = res.mod.neg();
      if (positive && mod.neg)
        mod = mod.isub(num);
    }
    return {
      div: res.div,
      mod: mod
    };
  }

  // Both numbers are positive at this point

  // Strip both numbers to approximate shift value
  if (num.length > this.length || this.cmp(num) < 0)
    return { div: new BN(0), mod: this };

  // Very short reduction
  if (num.length === 1) {
    if (mode === 'div')
      return { div: this.divn(num.words[0]), mod: null };
    else if (mode === 'mod')
      return { div: null, mod: new BN(this.modn(num.words[0])) };
    return {
      div: this.divn(num.words[0]),
      mod: new BN(this.modn(num.words[0]))
    };
  }

  return this._wordDiv(num, mode);
};

// Find `this` / `num`
BN.prototype.div = function div(num) {
  return this.divmod(num, 'div', false).div;
};

// Find `this` % `num`
BN.prototype.mod = function mod(num) {
  return this.divmod(num, 'mod', false).mod;
};

BN.prototype.umod = function umod(num) {
  return this.divmod(num, 'mod', true).mod;
};

// Find Round(`this` / `num`)
BN.prototype.divRound = function divRound(num) {
  var dm = this.divmod(num);

  // Fast case - exact division
  if (dm.mod.cmpn(0) === 0)
    return dm.div;

  var mod = dm.div.negative !== 0 ? dm.mod.isub(num) : dm.mod;

  var half = num.ushrn(1);
  var r2 = num.andln(1);
  var cmp = mod.cmp(half);

  // Round down
  if (cmp < 0 || r2 === 1 && cmp === 0)
    return dm.div;

  // Round up
  return dm.div.negative !== 0 ? dm.div.isubn(1) : dm.div.iaddn(1);
};

BN.prototype.modn = function modn(num) {
  var p = (1 << 26) % num;

  var acc = 0;
  for (var i = this.length - 1; i >= 0; i--)
    acc = (p * acc + (this.words[i] | 0)) % num;

  return acc;
};

// In-place division by number
BN.prototype.idivn = function idivn(num) {
  var carry = 0;
  for (var i = this.length - 1; i >= 0; i--) {
    var w = (this.words[i] | 0) + carry * 0x4000000;
    this.words[i] = (w / num) | 0;
    carry = w % num;
  }

  return this.strip();
};

BN.prototype.divn = function divn(num) {
  return this.clone().idivn(num);
};

BN.prototype.isEven = function isEven() {
  return (this.words[0] & 1) === 0;
};

BN.prototype.isOdd = function isOdd() {
  return (this.words[0] & 1) === 1;
};

// And first word and num
BN.prototype.andln = function andln(num) {
  return this.words[0] & num;
};

BN.prototype.cmpn = function cmpn(num) {
  var negative = num < 0;
  if (negative)
    num = -num;

  if (this.negative !== 0 && !negative)
    return -1;
  else if (this.negative === 0 && negative)
    return 1;

  num &= 0x3ffffff;
  this.strip();

  var res;
  if (this.length > 1) {
    res = 1;
  } else {
    var w = this.words[0] | 0;
    res = w === num ? 0 : w < num ? -1 : 1;
  }
  if (this.negative !== 0)
    res = -res;
  return res;
};

// Compare two numbers and return:
// 1 - if `this` > `num`
// 0 - if `this` == `num`
// -1 - if `this` < `num`
BN.prototype.cmp = function cmp(num) {
  if (this.negative !== 0 && num.negative === 0)
    return -1;
  else if (this.negative === 0 && num.negative !== 0)
    return 1;

  var res = this.ucmp(num);
  if (this.negative !== 0)
    return -res;
  else
    return res;
};

// Unsigned comparison
BN.prototype.ucmp = function ucmp(num) {
  // At this point both numbers have the same sign
  if (this.length > num.length)
    return 1;
  else if (this.length < num.length)
    return -1;

  var res = 0;
  for (var i = this.length - 1; i >= 0; i--) {
    var a = this.words[i] | 0;
    var b = num.words[i] | 0;

    if (a === b)
      continue;
    if (a < b)
      res = -1;
    else if (a > b)
      res = 1;
    break;
  }
  return res;
};
})(undefined, __bn);

// MVar implementation.
// Since Haste isn't concurrent, takeMVar and putMVar don't block on empty
// and full MVars respectively, but terminate the program since they would
// otherwise be blocking forever.

function newMVar() {
    return ({empty: true});
}

function tryTakeMVar(mv) {
    if(mv.empty) {
        return {_:0, a:0, b:undefined};
    } else {
        var val = mv.x;
        mv.empty = true;
        mv.x = null;
        return {_:0, a:1, b:val};
    }
}

function takeMVar(mv) {
    if(mv.empty) {
        // TODO: real BlockedOnDeadMVar exception, perhaps?
        err("Attempted to take empty MVar!");
    }
    var val = mv.x;
    mv.empty = true;
    mv.x = null;
    return val;
}

function putMVar(mv, val) {
    if(!mv.empty) {
        // TODO: real BlockedOnDeadMVar exception, perhaps?
        err("Attempted to put full MVar!");
    }
    mv.empty = false;
    mv.x = val;
}

function tryPutMVar(mv, val) {
    if(!mv.empty) {
        return 0;
    } else {
        mv.empty = false;
        mv.x = val;
        return 1;
    }
}

function sameMVar(a, b) {
    return (a == b);
}

function isEmptyMVar(mv) {
    return mv.empty ? 1 : 0;
}

// Implementation of stable names.
// Unlike native GHC, the garbage collector isn't going to move data around
// in a way that we can detect, so each object could serve as its own stable
// name if it weren't for the fact we can't turn a JS reference into an
// integer.
// So instead, each object has a unique integer attached to it, which serves
// as its stable name.

var __next_stable_name = 1;
var __stable_table;

function makeStableName(x) {
    if(x instanceof Object) {
        if(!x.stableName) {
            x.stableName = __next_stable_name;
            __next_stable_name += 1;
        }
        return {type: 'obj', name: x.stableName};
    } else {
        return {type: 'prim', name: Number(x)};
    }
}

function eqStableName(x, y) {
    return (x.type == y.type && x.name == y.name) ? 1 : 0;
}

// TODO: inefficient compared to real fromInt?
__bn.Z = new __bn.BN(0);
__bn.ONE = new __bn.BN(1);
__bn.MOD32 = new __bn.BN(0x100000000); // 2^32
var I_fromNumber = function(x) {return new __bn.BN(x);}
var I_fromInt = I_fromNumber;
var I_fromBits = function(lo,hi) {
    var x = new __bn.BN(lo >>> 0);
    var y = new __bn.BN(hi >>> 0);
    y.ishln(32);
    x.iadd(y);
    return x;
}
var I_fromString = function(s) {return new __bn.BN(s);}
var I_toInt = function(x) {return I_toNumber(x.mod(__bn.MOD32));}
var I_toWord = function(x) {return I_toInt(x) >>> 0;};
// TODO: inefficient!
var I_toNumber = function(x) {return Number(x.toString());}
var I_equals = function(a,b) {return a.cmp(b) === 0;}
var I_compare = function(a,b) {return a.cmp(b);}
var I_compareInt = function(x,i) {return x.cmp(new __bn.BN(i));}
var I_negate = function(x) {return x.neg();}
var I_add = function(a,b) {return a.add(b);}
var I_sub = function(a,b) {return a.sub(b);}
var I_mul = function(a,b) {return a.mul(b);}
var I_mod = function(a,b) {return I_rem(I_add(b, I_rem(a, b)), b);}
var I_quotRem = function(a,b) {
    var qr = a.divmod(b);
    return {_:0, a:qr.div, b:qr.mod};
}
var I_div = function(a,b) {
    if((a.cmp(__bn.Z)>=0) != (a.cmp(__bn.Z)>=0)) {
        if(a.cmp(a.rem(b), __bn.Z) !== 0) {
            return a.div(b).sub(__bn.ONE);
        }
    }
    return a.div(b);
}
var I_divMod = function(a,b) {
    return {_:0, a:I_div(a,b), b:a.mod(b)};
}
var I_quot = function(a,b) {return a.div(b);}
var I_rem = function(a,b) {return a.mod(b);}
var I_and = function(a,b) {return a.and(b);}
var I_or = function(a,b) {return a.or(b);}
var I_xor = function(a,b) {return a.xor(b);}
var I_shiftLeft = function(a,b) {return a.shln(b);}
var I_shiftRight = function(a,b) {return a.shrn(b);}
var I_signum = function(x) {return x.cmp(new __bn.BN(0));}
var I_abs = function(x) {return x.abs();}
var I_decodeDouble = function(x) {
    var dec = decodeDouble(x);
    var mantissa = I_fromBits(dec.c, dec.b);
    if(dec.a < 0) {
        mantissa = I_negate(mantissa);
    }
    return {_:0, a:dec.d, b:mantissa};
}
var I_toString = function(x) {return x.toString();}
var I_fromRat = function(a, b) {
    return I_toNumber(a) / I_toNumber(b);
}

function I_fromInt64(x) {
    if(x.isNegative()) {
        return I_negate(I_fromInt64(x.negate()));
    } else {
        return I_fromBits(x.low, x.high);
    }
}

function I_toInt64(x) {
    if(x.negative) {
        return I_toInt64(I_negate(x)).negate();
    } else {
        return new Long(I_toInt(x), I_toInt(I_shiftRight(x,32)));
    }
}

function I_fromWord64(x) {
    return I_fromBits(x.toInt(), x.shru(32).toInt());
}

function I_toWord64(x) {
    var w = I_toInt64(x);
    w.unsigned = true;
    return w;
}

/**
 * @license long.js (c) 2013 Daniel Wirtz <dcode@dcode.io>
 * Released under the Apache License, Version 2.0
 * see: https://github.com/dcodeIO/long.js for details
 */
function Long(low, high, unsigned) {
    this.low = low | 0;
    this.high = high | 0;
    this.unsigned = !!unsigned;
}

var INT_CACHE = {};
var UINT_CACHE = {};
function cacheable(x, u) {
    return u ? 0 <= (x >>>= 0) && x < 256 : -128 <= (x |= 0) && x < 128;
}

function __fromInt(value, unsigned) {
    var obj, cachedObj, cache;
    if (unsigned) {
        if (cache = cacheable(value >>>= 0, true)) {
            cachedObj = UINT_CACHE[value];
            if (cachedObj)
                return cachedObj;
        }
        obj = new Long(value, (value | 0) < 0 ? -1 : 0, true);
        if (cache)
            UINT_CACHE[value] = obj;
        return obj;
    } else {
        if (cache = cacheable(value |= 0, false)) {
            cachedObj = INT_CACHE[value];
            if (cachedObj)
                return cachedObj;
        }
        obj = new Long(value, value < 0 ? -1 : 0, false);
        if (cache)
            INT_CACHE[value] = obj;
        return obj;
    }
}

function __fromNumber(value, unsigned) {
    if (isNaN(value) || !isFinite(value))
        return unsigned ? UZERO : ZERO;
    if (unsigned) {
        if (value < 0)
            return UZERO;
        if (value >= TWO_PWR_64_DBL)
            return MAX_UNSIGNED_VALUE;
    } else {
        if (value <= -TWO_PWR_63_DBL)
            return MIN_VALUE;
        if (value + 1 >= TWO_PWR_63_DBL)
            return MAX_VALUE;
    }
    if (value < 0)
        return __fromNumber(-value, unsigned).neg();
    return new Long((value % TWO_PWR_32_DBL) | 0, (value / TWO_PWR_32_DBL) | 0, unsigned);
}
var pow_dbl = Math.pow;
var TWO_PWR_16_DBL = 1 << 16;
var TWO_PWR_24_DBL = 1 << 24;
var TWO_PWR_32_DBL = TWO_PWR_16_DBL * TWO_PWR_16_DBL;
var TWO_PWR_64_DBL = TWO_PWR_32_DBL * TWO_PWR_32_DBL;
var TWO_PWR_63_DBL = TWO_PWR_64_DBL / 2;
var TWO_PWR_24 = __fromInt(TWO_PWR_24_DBL);
var ZERO = __fromInt(0);
Long.ZERO = ZERO;
var UZERO = __fromInt(0, true);
Long.UZERO = UZERO;
var ONE = __fromInt(1);
Long.ONE = ONE;
var UONE = __fromInt(1, true);
Long.UONE = UONE;
var NEG_ONE = __fromInt(-1);
Long.NEG_ONE = NEG_ONE;
var MAX_VALUE = new Long(0xFFFFFFFF|0, 0x7FFFFFFF|0, false);
Long.MAX_VALUE = MAX_VALUE;
var MAX_UNSIGNED_VALUE = new Long(0xFFFFFFFF|0, 0xFFFFFFFF|0, true);
Long.MAX_UNSIGNED_VALUE = MAX_UNSIGNED_VALUE;
var MIN_VALUE = new Long(0, 0x80000000|0, false);
Long.MIN_VALUE = MIN_VALUE;
var __lp = Long.prototype;
__lp.toInt = function() {return this.unsigned ? this.low >>> 0 : this.low;};
__lp.toNumber = function() {
    if (this.unsigned)
        return ((this.high >>> 0) * TWO_PWR_32_DBL) + (this.low >>> 0);
    return this.high * TWO_PWR_32_DBL + (this.low >>> 0);
};
__lp.isZero = function() {return this.high === 0 && this.low === 0;};
__lp.isNegative = function() {return !this.unsigned && this.high < 0;};
__lp.isOdd = function() {return (this.low & 1) === 1;};
__lp.eq = function(other) {
    if (this.unsigned !== other.unsigned && (this.high >>> 31) === 1 && (other.high >>> 31) === 1)
        return false;
    return this.high === other.high && this.low === other.low;
};
__lp.neq = function(other) {return !this.eq(other);};
__lp.lt = function(other) {return this.comp(other) < 0;};
__lp.lte = function(other) {return this.comp(other) <= 0;};
__lp.gt = function(other) {return this.comp(other) > 0;};
__lp.gte = function(other) {return this.comp(other) >= 0;};
__lp.compare = function(other) {
    if (this.eq(other))
        return 0;
    var thisNeg = this.isNegative(),
        otherNeg = other.isNegative();
    if (thisNeg && !otherNeg)
        return -1;
    if (!thisNeg && otherNeg)
        return 1;
    if (!this.unsigned)
        return this.sub(other).isNegative() ? -1 : 1;
    return (other.high >>> 0) > (this.high >>> 0) || (other.high === this.high && (other.low >>> 0) > (this.low >>> 0)) ? -1 : 1;
};
__lp.comp = __lp.compare;
__lp.negate = function() {
    if (!this.unsigned && this.eq(MIN_VALUE))
        return MIN_VALUE;
    return this.not().add(ONE);
};
__lp.neg = __lp.negate;
__lp.add = function(addend) {
    var a48 = this.high >>> 16;
    var a32 = this.high & 0xFFFF;
    var a16 = this.low >>> 16;
    var a00 = this.low & 0xFFFF;

    var b48 = addend.high >>> 16;
    var b32 = addend.high & 0xFFFF;
    var b16 = addend.low >>> 16;
    var b00 = addend.low & 0xFFFF;

    var c48 = 0, c32 = 0, c16 = 0, c00 = 0;
    c00 += a00 + b00;
    c16 += c00 >>> 16;
    c00 &= 0xFFFF;
    c16 += a16 + b16;
    c32 += c16 >>> 16;
    c16 &= 0xFFFF;
    c32 += a32 + b32;
    c48 += c32 >>> 16;
    c32 &= 0xFFFF;
    c48 += a48 + b48;
    c48 &= 0xFFFF;
    return new Long((c16 << 16) | c00, (c48 << 16) | c32, this.unsigned);
};
__lp.subtract = function(subtrahend) {return this.add(subtrahend.neg());};
__lp.sub = __lp.subtract;
__lp.multiply = function(multiplier) {
    if (this.isZero())
        return ZERO;
    if (multiplier.isZero())
        return ZERO;
    if (this.eq(MIN_VALUE))
        return multiplier.isOdd() ? MIN_VALUE : ZERO;
    if (multiplier.eq(MIN_VALUE))
        return this.isOdd() ? MIN_VALUE : ZERO;

    if (this.isNegative()) {
        if (multiplier.isNegative())
            return this.neg().mul(multiplier.neg());
        else
            return this.neg().mul(multiplier).neg();
    } else if (multiplier.isNegative())
        return this.mul(multiplier.neg()).neg();

    if (this.lt(TWO_PWR_24) && multiplier.lt(TWO_PWR_24))
        return __fromNumber(this.toNumber() * multiplier.toNumber(), this.unsigned);

    var a48 = this.high >>> 16;
    var a32 = this.high & 0xFFFF;
    var a16 = this.low >>> 16;
    var a00 = this.low & 0xFFFF;

    var b48 = multiplier.high >>> 16;
    var b32 = multiplier.high & 0xFFFF;
    var b16 = multiplier.low >>> 16;
    var b00 = multiplier.low & 0xFFFF;

    var c48 = 0, c32 = 0, c16 = 0, c00 = 0;
    c00 += a00 * b00;
    c16 += c00 >>> 16;
    c00 &= 0xFFFF;
    c16 += a16 * b00;
    c32 += c16 >>> 16;
    c16 &= 0xFFFF;
    c16 += a00 * b16;
    c32 += c16 >>> 16;
    c16 &= 0xFFFF;
    c32 += a32 * b00;
    c48 += c32 >>> 16;
    c32 &= 0xFFFF;
    c32 += a16 * b16;
    c48 += c32 >>> 16;
    c32 &= 0xFFFF;
    c32 += a00 * b32;
    c48 += c32 >>> 16;
    c32 &= 0xFFFF;
    c48 += a48 * b00 + a32 * b16 + a16 * b32 + a00 * b48;
    c48 &= 0xFFFF;
    return new Long((c16 << 16) | c00, (c48 << 16) | c32, this.unsigned);
};
__lp.mul = __lp.multiply;
__lp.divide = function(divisor) {
    if (divisor.isZero())
        throw Error('division by zero');
    if (this.isZero())
        return this.unsigned ? UZERO : ZERO;
    var approx, rem, res;
    if (this.eq(MIN_VALUE)) {
        if (divisor.eq(ONE) || divisor.eq(NEG_ONE))
            return MIN_VALUE;
        else if (divisor.eq(MIN_VALUE))
            return ONE;
        else {
            var halfThis = this.shr(1);
            approx = halfThis.div(divisor).shl(1);
            if (approx.eq(ZERO)) {
                return divisor.isNegative() ? ONE : NEG_ONE;
            } else {
                rem = this.sub(divisor.mul(approx));
                res = approx.add(rem.div(divisor));
                return res;
            }
        }
    } else if (divisor.eq(MIN_VALUE))
        return this.unsigned ? UZERO : ZERO;
    if (this.isNegative()) {
        if (divisor.isNegative())
            return this.neg().div(divisor.neg());
        return this.neg().div(divisor).neg();
    } else if (divisor.isNegative())
        return this.div(divisor.neg()).neg();

    res = ZERO;
    rem = this;
    while (rem.gte(divisor)) {
        approx = Math.max(1, Math.floor(rem.toNumber() / divisor.toNumber()));
        var log2 = Math.ceil(Math.log(approx) / Math.LN2),
            delta = (log2 <= 48) ? 1 : pow_dbl(2, log2 - 48),
            approxRes = __fromNumber(approx),
            approxRem = approxRes.mul(divisor);
        while (approxRem.isNegative() || approxRem.gt(rem)) {
            approx -= delta;
            approxRes = __fromNumber(approx, this.unsigned);
            approxRem = approxRes.mul(divisor);
        }
        if (approxRes.isZero())
            approxRes = ONE;

        res = res.add(approxRes);
        rem = rem.sub(approxRem);
    }
    return res;
};
__lp.div = __lp.divide;
__lp.modulo = function(divisor) {return this.sub(this.div(divisor).mul(divisor));};
__lp.mod = __lp.modulo;
__lp.not = function not() {return new Long(~this.low, ~this.high, this.unsigned);};
__lp.and = function(other) {return new Long(this.low & other.low, this.high & other.high, this.unsigned);};
__lp.or = function(other) {return new Long(this.low | other.low, this.high | other.high, this.unsigned);};
__lp.xor = function(other) {return new Long(this.low ^ other.low, this.high ^ other.high, this.unsigned);};

__lp.shl = function(numBits) {
    if ((numBits &= 63) === 0)
        return this;
    else if (numBits < 32)
        return new Long(this.low << numBits, (this.high << numBits) | (this.low >>> (32 - numBits)), this.unsigned);
    else
        return new Long(0, this.low << (numBits - 32), this.unsigned);
};

__lp.shr = function(numBits) {
    if ((numBits &= 63) === 0)
        return this;
    else if (numBits < 32)
        return new Long((this.low >>> numBits) | (this.high << (32 - numBits)), this.high >> numBits, this.unsigned);
    else
        return new Long(this.high >> (numBits - 32), this.high >= 0 ? 0 : -1, this.unsigned);
};

__lp.shru = function(numBits) {
    numBits &= 63;
    if (numBits === 0)
        return this;
    else {
        var high = this.high;
        if (numBits < 32) {
            var low = this.low;
            return new Long((low >>> numBits) | (high << (32 - numBits)), high >>> numBits, this.unsigned);
        } else if (numBits === 32)
            return new Long(high, 0, this.unsigned);
        else
            return new Long(high >>> (numBits - 32), 0, this.unsigned);
    }
};

__lp.toSigned = function() {return this.unsigned ? new Long(this.low, this.high, false) : this;};
__lp.toUnsigned = function() {return this.unsigned ? this : new Long(this.low, this.high, true);};

// Int64
function hs_eqInt64(x, y) {return x.eq(y);}
function hs_neInt64(x, y) {return x.neq(y);}
function hs_ltInt64(x, y) {return x.lt(y);}
function hs_leInt64(x, y) {return x.lte(y);}
function hs_gtInt64(x, y) {return x.gt(y);}
function hs_geInt64(x, y) {return x.gte(y);}
function hs_quotInt64(x, y) {return x.div(y);}
function hs_remInt64(x, y) {return x.modulo(y);}
function hs_plusInt64(x, y) {return x.add(y);}
function hs_minusInt64(x, y) {return x.subtract(y);}
function hs_timesInt64(x, y) {return x.multiply(y);}
function hs_negateInt64(x) {return x.negate();}
function hs_uncheckedIShiftL64(x, bits) {return x.shl(bits);}
function hs_uncheckedIShiftRA64(x, bits) {return x.shr(bits);}
function hs_uncheckedIShiftRL64(x, bits) {return x.shru(bits);}
function hs_int64ToInt(x) {return x.toInt();}
var hs_intToInt64 = __fromInt;

// Word64
function hs_wordToWord64(x) {return __fromInt(x, true);}
function hs_word64ToWord(x) {return x.toInt(x);}
function hs_mkWord64(low, high) {return new Long(low,high,true);}
function hs_and64(a,b) {return a.and(b);};
function hs_or64(a,b) {return a.or(b);};
function hs_xor64(a,b) {return a.xor(b);};
function hs_not64(x) {return x.not();}
var hs_eqWord64 = hs_eqInt64;
var hs_neWord64 = hs_neInt64;
var hs_ltWord64 = hs_ltInt64;
var hs_leWord64 = hs_leInt64;
var hs_gtWord64 = hs_gtInt64;
var hs_geWord64 = hs_geInt64;
var hs_quotWord64 = hs_quotInt64;
var hs_remWord64 = hs_remInt64;
var hs_uncheckedShiftL64 = hs_uncheckedIShiftL64;
var hs_uncheckedShiftRL64 = hs_uncheckedIShiftRL64;
function hs_int64ToWord64(x) {return x.toUnsigned();}
function hs_word64ToInt64(x) {return x.toSigned();}

// Joseph Myers' MD5 implementation, ported to work on typed arrays.
// Used under the BSD license.
function md5cycle(x, k) {
    var a = x[0], b = x[1], c = x[2], d = x[3];

    a = ff(a, b, c, d, k[0], 7, -680876936);
    d = ff(d, a, b, c, k[1], 12, -389564586);
    c = ff(c, d, a, b, k[2], 17,  606105819);
    b = ff(b, c, d, a, k[3], 22, -1044525330);
    a = ff(a, b, c, d, k[4], 7, -176418897);
    d = ff(d, a, b, c, k[5], 12,  1200080426);
    c = ff(c, d, a, b, k[6], 17, -1473231341);
    b = ff(b, c, d, a, k[7], 22, -45705983);
    a = ff(a, b, c, d, k[8], 7,  1770035416);
    d = ff(d, a, b, c, k[9], 12, -1958414417);
    c = ff(c, d, a, b, k[10], 17, -42063);
    b = ff(b, c, d, a, k[11], 22, -1990404162);
    a = ff(a, b, c, d, k[12], 7,  1804603682);
    d = ff(d, a, b, c, k[13], 12, -40341101);
    c = ff(c, d, a, b, k[14], 17, -1502002290);
    b = ff(b, c, d, a, k[15], 22,  1236535329);

    a = gg(a, b, c, d, k[1], 5, -165796510);
    d = gg(d, a, b, c, k[6], 9, -1069501632);
    c = gg(c, d, a, b, k[11], 14,  643717713);
    b = gg(b, c, d, a, k[0], 20, -373897302);
    a = gg(a, b, c, d, k[5], 5, -701558691);
    d = gg(d, a, b, c, k[10], 9,  38016083);
    c = gg(c, d, a, b, k[15], 14, -660478335);
    b = gg(b, c, d, a, k[4], 20, -405537848);
    a = gg(a, b, c, d, k[9], 5,  568446438);
    d = gg(d, a, b, c, k[14], 9, -1019803690);
    c = gg(c, d, a, b, k[3], 14, -187363961);
    b = gg(b, c, d, a, k[8], 20,  1163531501);
    a = gg(a, b, c, d, k[13], 5, -1444681467);
    d = gg(d, a, b, c, k[2], 9, -51403784);
    c = gg(c, d, a, b, k[7], 14,  1735328473);
    b = gg(b, c, d, a, k[12], 20, -1926607734);

    a = hh(a, b, c, d, k[5], 4, -378558);
    d = hh(d, a, b, c, k[8], 11, -2022574463);
    c = hh(c, d, a, b, k[11], 16,  1839030562);
    b = hh(b, c, d, a, k[14], 23, -35309556);
    a = hh(a, b, c, d, k[1], 4, -1530992060);
    d = hh(d, a, b, c, k[4], 11,  1272893353);
    c = hh(c, d, a, b, k[7], 16, -155497632);
    b = hh(b, c, d, a, k[10], 23, -1094730640);
    a = hh(a, b, c, d, k[13], 4,  681279174);
    d = hh(d, a, b, c, k[0], 11, -358537222);
    c = hh(c, d, a, b, k[3], 16, -722521979);
    b = hh(b, c, d, a, k[6], 23,  76029189);
    a = hh(a, b, c, d, k[9], 4, -640364487);
    d = hh(d, a, b, c, k[12], 11, -421815835);
    c = hh(c, d, a, b, k[15], 16,  530742520);
    b = hh(b, c, d, a, k[2], 23, -995338651);

    a = ii(a, b, c, d, k[0], 6, -198630844);
    d = ii(d, a, b, c, k[7], 10,  1126891415);
    c = ii(c, d, a, b, k[14], 15, -1416354905);
    b = ii(b, c, d, a, k[5], 21, -57434055);
    a = ii(a, b, c, d, k[12], 6,  1700485571);
    d = ii(d, a, b, c, k[3], 10, -1894986606);
    c = ii(c, d, a, b, k[10], 15, -1051523);
    b = ii(b, c, d, a, k[1], 21, -2054922799);
    a = ii(a, b, c, d, k[8], 6,  1873313359);
    d = ii(d, a, b, c, k[15], 10, -30611744);
    c = ii(c, d, a, b, k[6], 15, -1560198380);
    b = ii(b, c, d, a, k[13], 21,  1309151649);
    a = ii(a, b, c, d, k[4], 6, -145523070);
    d = ii(d, a, b, c, k[11], 10, -1120210379);
    c = ii(c, d, a, b, k[2], 15,  718787259);
    b = ii(b, c, d, a, k[9], 21, -343485551);

    x[0] = add32(a, x[0]);
    x[1] = add32(b, x[1]);
    x[2] = add32(c, x[2]);
    x[3] = add32(d, x[3]);

}

function cmn(q, a, b, x, s, t) {
    a = add32(add32(a, q), add32(x, t));
    return add32((a << s) | (a >>> (32 - s)), b);
}

function ff(a, b, c, d, x, s, t) {
    return cmn((b & c) | ((~b) & d), a, b, x, s, t);
}

function gg(a, b, c, d, x, s, t) {
    return cmn((b & d) | (c & (~d)), a, b, x, s, t);
}

function hh(a, b, c, d, x, s, t) {
    return cmn(b ^ c ^ d, a, b, x, s, t);
}

function ii(a, b, c, d, x, s, t) {
    return cmn(c ^ (b | (~d)), a, b, x, s, t);
}

function md51(s, n) {
    var a = s['v']['w8'];
    var orig_n = n,
        state = [1732584193, -271733879, -1732584194, 271733878], i;
    for (i=64; i<=n; i+=64) {
        md5cycle(state, md5blk(a.subarray(i-64, i)));
    }
    a = a.subarray(i-64);
    n = n < (i-64) ? 0 : n-(i-64);
    var tail = [0,0,0,0, 0,0,0,0, 0,0,0,0, 0,0,0,0];
    for (i=0; i<n; i++)
        tail[i>>2] |= a[i] << ((i%4) << 3);
    tail[i>>2] |= 0x80 << ((i%4) << 3);
    if (i > 55) {
        md5cycle(state, tail);
        for (i=0; i<16; i++) tail[i] = 0;
    }
    tail[14] = orig_n*8;
    md5cycle(state, tail);
    return state;
}
window['md51'] = md51;

function md5blk(s) {
    var md5blks = [], i;
    for (i=0; i<64; i+=4) {
        md5blks[i>>2] = s[i]
            + (s[i+1] << 8)
            + (s[i+2] << 16)
            + (s[i+3] << 24);
    }
    return md5blks;
}

var hex_chr = '0123456789abcdef'.split('');

function rhex(n)
{
    var s='', j=0;
    for(; j<4; j++)
        s += hex_chr[(n >> (j * 8 + 4)) & 0x0F]
        + hex_chr[(n >> (j * 8)) & 0x0F];
    return s;
}

function hex(x) {
    for (var i=0; i<x.length; i++)
        x[i] = rhex(x[i]);
    return x.join('');
}

function md5(s, n) {
    return hex(md51(s, n));
}

window['md5'] = md5;

function add32(a, b) {
    return (a + b) & 0xFFFFFFFF;
}

function __hsbase_MD5Init(ctx) {}
// Note that this is a one time "update", since that's all that's used by
// GHC.Fingerprint.
function __hsbase_MD5Update(ctx, s, n) {
    ctx.md5 = md51(s, n);
}
function __hsbase_MD5Final(out, ctx) {
    var a = out['v']['i32'];
    a[0] = ctx.md5[0];
    a[1] = ctx.md5[1];
    a[2] = ctx.md5[2];
    a[3] = ctx.md5[3];
}

// Functions for dealing with arrays.

function newArr(n, x) {
    var arr = new Array(n);
    for(var i = 0; i < n; ++i) {
        arr[i] = x;
    }
    return arr;
}

// Create all views at once; perhaps it's wasteful, but it's better than having
// to check for the right view at each read or write.
function newByteArr(n) {
    return new ByteArray(new ArrayBuffer(n));
}

// Wrap a JS ArrayBuffer into a ByteArray. Truncates the array length to the
// closest multiple of 8 bytes.
function wrapByteArr(buffer) {
    var diff = buffer.byteLength % 8;
    if(diff != 0) {
        var buffer = buffer.slice(0, buffer.byteLength-diff);
    }
    return new ByteArray(buffer);
}

function ByteArray(buffer) {
    var len = buffer.byteLength;
    var views =
        { 'i8' : new Int8Array(buffer)
        , 'i16': len % 2 ? null : new Int16Array(buffer)
        , 'i32': len % 4 ? null : new Int32Array(buffer)
        , 'w8' : new Uint8Array(buffer)
        , 'w16': len % 2 ? null : new Uint16Array(buffer)
        , 'w32': len % 4 ? null : new Uint32Array(buffer)
        , 'f32': len % 4 ? null : new Float32Array(buffer)
        , 'f64': len % 8 ? null : new Float64Array(buffer)
        };
    this['b'] = buffer;
    this['v'] = views;
    this['off'] = 0;
}
window['newArr'] = newArr;
window['newByteArr'] = newByteArr;
window['wrapByteArr'] = wrapByteArr;
window['ByteArray'] = ByteArray;

// An attempt at emulating pointers enough for ByteString and Text to be
// usable without patching the hell out of them.
// The general idea is that Addr# is a byte array with an associated offset.

function plusAddr(addr, off) {
    var newaddr = {};
    newaddr['off'] = addr['off'] + off;
    newaddr['b']   = addr['b'];
    newaddr['v']   = addr['v'];
    return newaddr;
}

function writeOffAddr(type, elemsize, addr, off, x) {
    addr['v'][type][addr.off/elemsize + off] = x;
}

function writeOffAddr64(addr, off, x) {
    addr['v']['w32'][addr.off/8 + off*2] = x.low;
    addr['v']['w32'][addr.off/8 + off*2 + 1] = x.high;
}

function readOffAddr(type, elemsize, addr, off) {
    return addr['v'][type][addr.off/elemsize + off];
}

function readOffAddr64(signed, addr, off) {
    var w64 = hs_mkWord64( addr['v']['w32'][addr.off/8 + off*2]
                         , addr['v']['w32'][addr.off/8 + off*2 + 1]);
    return signed ? hs_word64ToInt64(w64) : w64;
}

// Two addresses are equal if they point to the same buffer and have the same
// offset. For other comparisons, just use the offsets - nobody in their right
// mind would check if one pointer is less than another, completely unrelated,
// pointer and then act on that information anyway.
function addrEq(a, b) {
    if(a == b) {
        return true;
    }
    return a && b && a['b'] == b['b'] && a['off'] == b['off'];
}

function addrLT(a, b) {
    if(a) {
        return b && a['off'] < b['off'];
    } else {
        return (b != 0); 
    }
}

function addrGT(a, b) {
    if(b) {
        return a && a['off'] > b['off'];
    } else {
        return (a != 0);
    }
}

function withChar(f, charCode) {
    return f(String.fromCharCode(charCode)).charCodeAt(0);
}

function u_towlower(charCode) {
    return withChar(function(c) {return c.toLowerCase()}, charCode);
}

function u_towupper(charCode) {
    return withChar(function(c) {return c.toUpperCase()}, charCode);
}

var u_towtitle = u_towupper;

function u_iswupper(charCode) {
    var c = String.fromCharCode(charCode);
    return c == c.toUpperCase() && c != c.toLowerCase();
}

function u_iswlower(charCode) {
    var c = String.fromCharCode(charCode);
    return  c == c.toLowerCase() && c != c.toUpperCase();
}

function u_iswdigit(charCode) {
    return charCode >= 48 && charCode <= 57;
}

function u_iswcntrl(charCode) {
    return charCode <= 0x1f || charCode == 0x7f;
}

function u_iswspace(charCode) {
    var c = String.fromCharCode(charCode);
    return c.replace(/\s/g,'') != c;
}

function u_iswalpha(charCode) {
    var c = String.fromCharCode(charCode);
    return c.replace(__hs_alphare, '') != c;
}

function u_iswalnum(charCode) {
    return u_iswdigit(charCode) || u_iswalpha(charCode);
}

function u_iswprint(charCode) {
    return !u_iswcntrl(charCode);
}

function u_gencat(c) {
    throw 'u_gencat is only supported with --full-unicode.';
}

// Regex that matches any alphabetic character in any language. Horrible thing.
var __hs_alphare = /[\u0041-\u005A\u0061-\u007A\u00AA\u00B5\u00BA\u00C0-\u00D6\u00D8-\u00F6\u00F8-\u02C1\u02C6-\u02D1\u02E0-\u02E4\u02EC\u02EE\u0370-\u0374\u0376\u0377\u037A-\u037D\u0386\u0388-\u038A\u038C\u038E-\u03A1\u03A3-\u03F5\u03F7-\u0481\u048A-\u0527\u0531-\u0556\u0559\u0561-\u0587\u05D0-\u05EA\u05F0-\u05F2\u0620-\u064A\u066E\u066F\u0671-\u06D3\u06D5\u06E5\u06E6\u06EE\u06EF\u06FA-\u06FC\u06FF\u0710\u0712-\u072F\u074D-\u07A5\u07B1\u07CA-\u07EA\u07F4\u07F5\u07FA\u0800-\u0815\u081A\u0824\u0828\u0840-\u0858\u08A0\u08A2-\u08AC\u0904-\u0939\u093D\u0950\u0958-\u0961\u0971-\u0977\u0979-\u097F\u0985-\u098C\u098F\u0990\u0993-\u09A8\u09AA-\u09B0\u09B2\u09B6-\u09B9\u09BD\u09CE\u09DC\u09DD\u09DF-\u09E1\u09F0\u09F1\u0A05-\u0A0A\u0A0F\u0A10\u0A13-\u0A28\u0A2A-\u0A30\u0A32\u0A33\u0A35\u0A36\u0A38\u0A39\u0A59-\u0A5C\u0A5E\u0A72-\u0A74\u0A85-\u0A8D\u0A8F-\u0A91\u0A93-\u0AA8\u0AAA-\u0AB0\u0AB2\u0AB3\u0AB5-\u0AB9\u0ABD\u0AD0\u0AE0\u0AE1\u0B05-\u0B0C\u0B0F\u0B10\u0B13-\u0B28\u0B2A-\u0B30\u0B32\u0B33\u0B35-\u0B39\u0B3D\u0B5C\u0B5D\u0B5F-\u0B61\u0B71\u0B83\u0B85-\u0B8A\u0B8E-\u0B90\u0B92-\u0B95\u0B99\u0B9A\u0B9C\u0B9E\u0B9F\u0BA3\u0BA4\u0BA8-\u0BAA\u0BAE-\u0BB9\u0BD0\u0C05-\u0C0C\u0C0E-\u0C10\u0C12-\u0C28\u0C2A-\u0C33\u0C35-\u0C39\u0C3D\u0C58\u0C59\u0C60\u0C61\u0C85-\u0C8C\u0C8E-\u0C90\u0C92-\u0CA8\u0CAA-\u0CB3\u0CB5-\u0CB9\u0CBD\u0CDE\u0CE0\u0CE1\u0CF1\u0CF2\u0D05-\u0D0C\u0D0E-\u0D10\u0D12-\u0D3A\u0D3D\u0D4E\u0D60\u0D61\u0D7A-\u0D7F\u0D85-\u0D96\u0D9A-\u0DB1\u0DB3-\u0DBB\u0DBD\u0DC0-\u0DC6\u0E01-\u0E30\u0E32\u0E33\u0E40-\u0E46\u0E81\u0E82\u0E84\u0E87\u0E88\u0E8A\u0E8D\u0E94-\u0E97\u0E99-\u0E9F\u0EA1-\u0EA3\u0EA5\u0EA7\u0EAA\u0EAB\u0EAD-\u0EB0\u0EB2\u0EB3\u0EBD\u0EC0-\u0EC4\u0EC6\u0EDC-\u0EDF\u0F00\u0F40-\u0F47\u0F49-\u0F6C\u0F88-\u0F8C\u1000-\u102A\u103F\u1050-\u1055\u105A-\u105D\u1061\u1065\u1066\u106E-\u1070\u1075-\u1081\u108E\u10A0-\u10C5\u10C7\u10CD\u10D0-\u10FA\u10FC-\u1248\u124A-\u124D\u1250-\u1256\u1258\u125A-\u125D\u1260-\u1288\u128A-\u128D\u1290-\u12B0\u12B2-\u12B5\u12B8-\u12BE\u12C0\u12C2-\u12C5\u12C8-\u12D6\u12D8-\u1310\u1312-\u1315\u1318-\u135A\u1380-\u138F\u13A0-\u13F4\u1401-\u166C\u166F-\u167F\u1681-\u169A\u16A0-\u16EA\u1700-\u170C\u170E-\u1711\u1720-\u1731\u1740-\u1751\u1760-\u176C\u176E-\u1770\u1780-\u17B3\u17D7\u17DC\u1820-\u1877\u1880-\u18A8\u18AA\u18B0-\u18F5\u1900-\u191C\u1950-\u196D\u1970-\u1974\u1980-\u19AB\u19C1-\u19C7\u1A00-\u1A16\u1A20-\u1A54\u1AA7\u1B05-\u1B33\u1B45-\u1B4B\u1B83-\u1BA0\u1BAE\u1BAF\u1BBA-\u1BE5\u1C00-\u1C23\u1C4D-\u1C4F\u1C5A-\u1C7D\u1CE9-\u1CEC\u1CEE-\u1CF1\u1CF5\u1CF6\u1D00-\u1DBF\u1E00-\u1F15\u1F18-\u1F1D\u1F20-\u1F45\u1F48-\u1F4D\u1F50-\u1F57\u1F59\u1F5B\u1F5D\u1F5F-\u1F7D\u1F80-\u1FB4\u1FB6-\u1FBC\u1FBE\u1FC2-\u1FC4\u1FC6-\u1FCC\u1FD0-\u1FD3\u1FD6-\u1FDB\u1FE0-\u1FEC\u1FF2-\u1FF4\u1FF6-\u1FFC\u2071\u207F\u2090-\u209C\u2102\u2107\u210A-\u2113\u2115\u2119-\u211D\u2124\u2126\u2128\u212A-\u212D\u212F-\u2139\u213C-\u213F\u2145-\u2149\u214E\u2183\u2184\u2C00-\u2C2E\u2C30-\u2C5E\u2C60-\u2CE4\u2CEB-\u2CEE\u2CF2\u2CF3\u2D00-\u2D25\u2D27\u2D2D\u2D30-\u2D67\u2D6F\u2D80-\u2D96\u2DA0-\u2DA6\u2DA8-\u2DAE\u2DB0-\u2DB6\u2DB8-\u2DBE\u2DC0-\u2DC6\u2DC8-\u2DCE\u2DD0-\u2DD6\u2DD8-\u2DDE\u2E2F\u3005\u3006\u3031-\u3035\u303B\u303C\u3041-\u3096\u309D-\u309F\u30A1-\u30FA\u30FC-\u30FF\u3105-\u312D\u3131-\u318E\u31A0-\u31BA\u31F0-\u31FF\u3400-\u4DB5\u4E00-\u9FCC\uA000-\uA48C\uA4D0-\uA4FD\uA500-\uA60C\uA610-\uA61F\uA62A\uA62B\uA640-\uA66E\uA67F-\uA697\uA6A0-\uA6E5\uA717-\uA71F\uA722-\uA788\uA78B-\uA78E\uA790-\uA793\uA7A0-\uA7AA\uA7F8-\uA801\uA803-\uA805\uA807-\uA80A\uA80C-\uA822\uA840-\uA873\uA882-\uA8B3\uA8F2-\uA8F7\uA8FB\uA90A-\uA925\uA930-\uA946\uA960-\uA97C\uA984-\uA9B2\uA9CF\uAA00-\uAA28\uAA40-\uAA42\uAA44-\uAA4B\uAA60-\uAA76\uAA7A\uAA80-\uAAAF\uAAB1\uAAB5\uAAB6\uAAB9-\uAABD\uAAC0\uAAC2\uAADB-\uAADD\uAAE0-\uAAEA\uAAF2-\uAAF4\uAB01-\uAB06\uAB09-\uAB0E\uAB11-\uAB16\uAB20-\uAB26\uAB28-\uAB2E\uABC0-\uABE2\uAC00-\uD7A3\uD7B0-\uD7C6\uD7CB-\uD7FB\uF900-\uFA6D\uFA70-\uFAD9\uFB00-\uFB06\uFB13-\uFB17\uFB1D\uFB1F-\uFB28\uFB2A-\uFB36\uFB38-\uFB3C\uFB3E\uFB40\uFB41\uFB43\uFB44\uFB46-\uFBB1\uFBD3-\uFD3D\uFD50-\uFD8F\uFD92-\uFDC7\uFDF0-\uFDFB\uFE70-\uFE74\uFE76-\uFEFC\uFF21-\uFF3A\uFF41-\uFF5A\uFF66-\uFFBE\uFFC2-\uFFC7\uFFCA-\uFFCF\uFFD2-\uFFD7\uFFDA-\uFFDC]/g;

// Simulate handles.
// When implementing new handles, remember that passed strings may be thunks,
// and so need to be evaluated before use.

function jsNewHandle(init, read, write, flush, close, seek, tell) {
    var h = {
        read: read || function() {},
        write: write || function() {},
        seek: seek || function() {},
        tell: tell || function() {},
        close: close || function() {},
        flush: flush || function() {}
    };
    init.call(h);
    return h;
}

function jsReadHandle(h, len) {return h.read(len);}
function jsWriteHandle(h, str) {return h.write(str);}
function jsFlushHandle(h) {return h.flush();}
function jsCloseHandle(h) {return h.close();}

function jsMkConWriter(op) {
    return function(str) {
        str = E(str);
        var lines = (this.buf + str).split('\n');
        for(var i = 0; i < lines.length-1; ++i) {
            op.call(console, lines[i]);
        }
        this.buf = lines[lines.length-1];
    }
}

function jsMkStdout() {
    return jsNewHandle(
        function() {this.buf = '';},
        function(_) {return '';},
        jsMkConWriter(console.log),
        function() {console.log(this.buf); this.buf = '';}
    );
}

function jsMkStderr() {
    return jsNewHandle(
        function() {this.buf = '';},
        function(_) {return '';},
        jsMkConWriter(console.warn),
        function() {console.warn(this.buf); this.buf = '';}
    );
}

function jsMkStdin() {
    return jsNewHandle(
        function() {this.buf = '';},
        function(len) {
            while(this.buf.length < len) {
                this.buf += prompt('[stdin]') + '\n';
            }
            var ret = this.buf.substr(0, len);
            this.buf = this.buf.substr(len);
            return ret;
        }
    );
}

// "Weak Pointers". Mostly useless implementation since
// JS does its own GC.

function mkWeak(key, val, fin) {
    fin = !fin? function() {}: fin;
    return {key: key, val: val, fin: fin};
}

function derefWeak(w) {
    return {_:0, a:1, b:E(w).val};
}

function finalizeWeak(w) {
    return {_:0, a:B(A1(E(w).fin, __Z))};
}

/* For foreign import ccall "wrapper" */
function createAdjustor(args, f, a, b) {
    return function(){
        var x = f.apply(null, arguments);
        while(x instanceof F) {x = x.f();}
        return x;
    };
}

var __apply = function(f,as) {
    var arr = [];
    for(; as._ === 1; as = as.b) {
        arr.push(as.a);
    }
    arr.reverse();
    return f.apply(null, arr);
}
var __app0 = function(f) {return f();}
var __app1 = function(f,a) {return f(a);}
var __app2 = function(f,a,b) {return f(a,b);}
var __app3 = function(f,a,b,c) {return f(a,b,c);}
var __app4 = function(f,a,b,c,d) {return f(a,b,c,d);}
var __app5 = function(f,a,b,c,d,e) {return f(a,b,c,d,e);}
var __jsNull = function() {return null;}
var __isUndef = function(x) {return typeof x == 'undefined';}
var __eq = function(a,b) {return a===b;}
var __createJSFunc = function(arity, f){
    if(f instanceof Function && arity === f.length) {
        return (function() {
            var x = f.apply(null,arguments);
            if(x instanceof T) {
                if(x.f !== __blackhole) {
                    var ff = x.f;
                    x.f = __blackhole;
                    return x.x = ff();
                }
                return x.x;
            } else {
                while(x instanceof F) {
                    x = x.f();
                }
                return E(x);
            }
        });
    } else {
        return (function(){
            var as = Array.prototype.slice.call(arguments);
            as.push(0);
            return E(B(A(f,as)));
        });
    }
}


function __arr2lst(elem,arr) {
    if(elem >= arr.length) {
        return __Z;
    }
    return {_:1,
            a:arr[elem],
            b:new T(function(){return __arr2lst(elem+1,arr);})};
}

function __lst2arr(xs) {
    var arr = [];
    xs = E(xs);
    for(;xs._ === 1; xs = E(xs.b)) {
        arr.push(E(xs.a));
    }
    return arr;
}

var __new = function() {return ({});}
var __set = function(o,k,v) {o[k]=v;}
var __get = function(o,k) {return o[k];}
var __has = function(o,k) {return o[k]!==undefined;}

/* Code for creating and querying the static pointer table. */
window.__hs_spt = [];

function __spt_insert(ptr) {
    ptr = E(B(ptr));
    var ks = [ (ptr.a.a.low>>>0).toString(16)
             , (ptr.a.a.high>>>0).toString(16)
             , (ptr.a.b.low>>>0).toString(16)
             , (ptr.a.b.high>>>0).toString(16)
             ]
    var key = ks.join();
    window.__hs_spt[key] = ptr;
}

function hs_spt_lookup(k) {
    var ks = [ k['v']['w32'][0].toString(16)
             , k['v']['w32'][1].toString(16)
             , k['v']['w32'][2].toString(16)
             , k['v']['w32'][3].toString(16)
             ]
    var key = ks.join();
    return window.__hs_spt[key];
}

var _0=function(_1,_2){while(1){var _3=B((function(_4,_5){var _6=E(_5);if(!_6._){_1=new T2(1,new T2(0,_6.b,_6.c),new T(function(){return B(_0(_4,_6.e));}));_2=_6.d;return __continue;}else{return E(_4);}})(_1,_2));if(_3!=__continue){return _3;}}},_7="metaKey",_8="shiftKey",_9="altKey",_a="ctrlKey",_b="keyCode",_c=function(_d,_){var _e=__get(_d,E(_b)),_f=__get(_d,E(_a)),_g=__get(_d,E(_9)),_h=__get(_d,E(_8)),_i=__get(_d,E(_7));return new T(function(){var _j=Number(_e),_k=jsTrunc(_j);return new T5(0,_k,E(_f),E(_g),E(_h),E(_i));});},_l=function(_m,_n,_){return new F(function(){return _c(E(_n),_);});},_o="keydown",_p="keyup",_q="keypress",_r=function(_s){switch(E(_s)){case 0:return E(_q);case 1:return E(_p);default:return E(_o);}},_t=new T2(0,_r,_l),_u="deltaZ",_v="deltaY",_w="deltaX",_x=function(_y,_z){var _A=E(_y);return (_A._==0)?E(_z):new T2(1,_A.a,new T(function(){return B(_x(_A.b,_z));}));},_B=function(_C,_D){var _E=jsShowI(_C);return new F(function(){return _x(fromJSStr(_E),_D);});},_F=41,_G=40,_H=function(_I,_J,_K){if(_J>=0){return new F(function(){return _B(_J,_K);});}else{if(_I<=6){return new F(function(){return _B(_J,_K);});}else{return new T2(1,_G,new T(function(){var _L=jsShowI(_J);return B(_x(fromJSStr(_L),new T2(1,_F,_K)));}));}}},_M=new T(function(){return B(unCStr(")"));}),_N=new T(function(){return B(_H(0,2,_M));}),_O=new T(function(){return B(unAppCStr(") is outside of enumeration\'s range (0,",_N));}),_P=function(_Q){return new F(function(){return err(B(unAppCStr("toEnum{MouseButton}: tag (",new T(function(){return B(_H(0,_Q,_O));}))));});},_R=function(_S,_){return new T(function(){var _T=Number(E(_S)),_U=jsTrunc(_T);if(_U<0){return B(_P(_U));}else{if(_U>2){return B(_P(_U));}else{return _U;}}});},_V=0,_W=new T3(0,_V,_V,_V),_X="button",_Y=new T(function(){return eval("jsGetMouseCoords");}),_Z=__Z,_10=function(_11,_){var _12=E(_11);if(!_12._){return _Z;}else{var _13=B(_10(_12.b,_));return new T2(1,new T(function(){var _14=Number(E(_12.a));return jsTrunc(_14);}),_13);}},_15=function(_16,_){var _17=__arr2lst(0,_16);return new F(function(){return _10(_17,_);});},_18=function(_19,_){return new F(function(){return _15(E(_19),_);});},_1a=function(_1b,_){return new T(function(){var _1c=Number(E(_1b));return jsTrunc(_1c);});},_1d=new T2(0,_1a,_18),_1e=function(_1f,_){var _1g=E(_1f);if(!_1g._){return _Z;}else{var _1h=B(_1e(_1g.b,_));return new T2(1,_1g.a,_1h);}},_1i=new T(function(){return B(unCStr("base"));}),_1j=new T(function(){return B(unCStr("GHC.IO.Exception"));}),_1k=new T(function(){return B(unCStr("IOException"));}),_1l=new T5(0,new Long(4053623282,1685460941,true),new Long(3693590983,2507416641,true),_1i,_1j,_1k),_1m=new T5(0,new Long(4053623282,1685460941,true),new Long(3693590983,2507416641,true),_1l,_Z,_Z),_1n=function(_1o){return E(_1m);},_1p=function(_1q){return E(E(_1q).a);},_1r=function(_1s,_1t,_1u){var _1v=B(A1(_1s,_)),_1w=B(A1(_1t,_)),_1x=hs_eqWord64(_1v.a,_1w.a);if(!_1x){return __Z;}else{var _1y=hs_eqWord64(_1v.b,_1w.b);return (!_1y)?__Z:new T1(1,_1u);}},_1z=function(_1A){var _1B=E(_1A);return new F(function(){return _1r(B(_1p(_1B.a)),_1n,_1B.b);});},_1C=new T(function(){return B(unCStr(": "));}),_1D=new T(function(){return B(unCStr(")"));}),_1E=new T(function(){return B(unCStr(" ("));}),_1F=new T(function(){return B(unCStr("interrupted"));}),_1G=new T(function(){return B(unCStr("system error"));}),_1H=new T(function(){return B(unCStr("unsatisified constraints"));}),_1I=new T(function(){return B(unCStr("user error"));}),_1J=new T(function(){return B(unCStr("permission denied"));}),_1K=new T(function(){return B(unCStr("illegal operation"));}),_1L=new T(function(){return B(unCStr("end of file"));}),_1M=new T(function(){return B(unCStr("resource exhausted"));}),_1N=new T(function(){return B(unCStr("resource busy"));}),_1O=new T(function(){return B(unCStr("does not exist"));}),_1P=new T(function(){return B(unCStr("already exists"));}),_1Q=new T(function(){return B(unCStr("resource vanished"));}),_1R=new T(function(){return B(unCStr("timeout"));}),_1S=new T(function(){return B(unCStr("unsupported operation"));}),_1T=new T(function(){return B(unCStr("hardware fault"));}),_1U=new T(function(){return B(unCStr("inappropriate type"));}),_1V=new T(function(){return B(unCStr("invalid argument"));}),_1W=new T(function(){return B(unCStr("failed"));}),_1X=new T(function(){return B(unCStr("protocol error"));}),_1Y=function(_1Z,_20){switch(E(_1Z)){case 0:return new F(function(){return _x(_1P,_20);});break;case 1:return new F(function(){return _x(_1O,_20);});break;case 2:return new F(function(){return _x(_1N,_20);});break;case 3:return new F(function(){return _x(_1M,_20);});break;case 4:return new F(function(){return _x(_1L,_20);});break;case 5:return new F(function(){return _x(_1K,_20);});break;case 6:return new F(function(){return _x(_1J,_20);});break;case 7:return new F(function(){return _x(_1I,_20);});break;case 8:return new F(function(){return _x(_1H,_20);});break;case 9:return new F(function(){return _x(_1G,_20);});break;case 10:return new F(function(){return _x(_1X,_20);});break;case 11:return new F(function(){return _x(_1W,_20);});break;case 12:return new F(function(){return _x(_1V,_20);});break;case 13:return new F(function(){return _x(_1U,_20);});break;case 14:return new F(function(){return _x(_1T,_20);});break;case 15:return new F(function(){return _x(_1S,_20);});break;case 16:return new F(function(){return _x(_1R,_20);});break;case 17:return new F(function(){return _x(_1Q,_20);});break;default:return new F(function(){return _x(_1F,_20);});}},_21=new T(function(){return B(unCStr("}"));}),_22=new T(function(){return B(unCStr("{handle: "));}),_23=function(_24,_25,_26,_27,_28,_29){var _2a=new T(function(){var _2b=new T(function(){var _2c=new T(function(){var _2d=E(_27);if(!_2d._){return E(_29);}else{var _2e=new T(function(){return B(_x(_2d,new T(function(){return B(_x(_1D,_29));},1)));},1);return B(_x(_1E,_2e));}},1);return B(_1Y(_25,_2c));}),_2f=E(_26);if(!_2f._){return E(_2b);}else{return B(_x(_2f,new T(function(){return B(_x(_1C,_2b));},1)));}}),_2g=E(_28);if(!_2g._){var _2h=E(_24);if(!_2h._){return E(_2a);}else{var _2i=E(_2h.a);if(!_2i._){var _2j=new T(function(){var _2k=new T(function(){return B(_x(_21,new T(function(){return B(_x(_1C,_2a));},1)));},1);return B(_x(_2i.a,_2k));},1);return new F(function(){return _x(_22,_2j);});}else{var _2l=new T(function(){var _2m=new T(function(){return B(_x(_21,new T(function(){return B(_x(_1C,_2a));},1)));},1);return B(_x(_2i.a,_2m));},1);return new F(function(){return _x(_22,_2l);});}}}else{return new F(function(){return _x(_2g.a,new T(function(){return B(_x(_1C,_2a));},1));});}},_2n=function(_2o){var _2p=E(_2o);return new F(function(){return _23(_2p.a,_2p.b,_2p.c,_2p.d,_2p.f,_Z);});},_2q=function(_2r,_2s,_2t){var _2u=E(_2s);return new F(function(){return _23(_2u.a,_2u.b,_2u.c,_2u.d,_2u.f,_2t);});},_2v=function(_2w,_2x){var _2y=E(_2w);return new F(function(){return _23(_2y.a,_2y.b,_2y.c,_2y.d,_2y.f,_2x);});},_2z=44,_2A=93,_2B=91,_2C=function(_2D,_2E,_2F){var _2G=E(_2E);if(!_2G._){return new F(function(){return unAppCStr("[]",_2F);});}else{var _2H=new T(function(){var _2I=new T(function(){var _2J=function(_2K){var _2L=E(_2K);if(!_2L._){return E(new T2(1,_2A,_2F));}else{var _2M=new T(function(){return B(A2(_2D,_2L.a,new T(function(){return B(_2J(_2L.b));})));});return new T2(1,_2z,_2M);}};return B(_2J(_2G.b));});return B(A2(_2D,_2G.a,_2I));});return new T2(1,_2B,_2H);}},_2N=function(_2O,_2P){return new F(function(){return _2C(_2v,_2O,_2P);});},_2Q=new T3(0,_2q,_2n,_2N),_2R=new T(function(){return new T5(0,_1n,_2Q,_2S,_1z,_2n);}),_2S=function(_2T){return new T2(0,_2R,_2T);},_2U=__Z,_2V=7,_2W=new T(function(){return B(unCStr("Pattern match failure in do expression at src/Haste/Prim/Any.hs:268:5-9"));}),_2X=new T6(0,_2U,_2V,_Z,_2W,_2U,_2U),_2Y=new T(function(){return B(_2S(_2X));}),_2Z=function(_){return new F(function(){return die(_2Y);});},_30=function(_31){return E(E(_31).a);},_32=function(_33,_34,_35,_){var _36=__arr2lst(0,_35),_37=B(_1e(_36,_)),_38=E(_37);if(!_38._){return new F(function(){return _2Z(_);});}else{var _39=E(_38.b);if(!_39._){return new F(function(){return _2Z(_);});}else{if(!E(_39.b)._){var _3a=B(A3(_30,_33,_38.a,_)),_3b=B(A3(_30,_34,_39.a,_));return new T2(0,_3a,_3b);}else{return new F(function(){return _2Z(_);});}}}},_3c=function(_){return new F(function(){return __jsNull();});},_3d=function(_3e){var _3f=B(A1(_3e,_));return E(_3f);},_3g=new T(function(){return B(_3d(_3c));}),_3h=new T(function(){return E(_3g);}),_3i=function(_3j,_3k,_){if(E(_3j)==7){var _3l=__app1(E(_Y),_3k),_3m=B(_32(_1d,_1d,_3l,_)),_3n=__get(_3k,E(_w)),_3o=__get(_3k,E(_v)),_3p=__get(_3k,E(_u));return new T(function(){return new T3(0,E(_3m),E(_2U),E(new T3(0,_3n,_3o,_3p)));});}else{var _3q=__app1(E(_Y),_3k),_3r=B(_32(_1d,_1d,_3q,_)),_3s=__get(_3k,E(_X)),_3t=__eq(_3s,E(_3h));if(!E(_3t)){var _3u=__isUndef(_3s);if(!E(_3u)){var _3v=B(_R(_3s,_));return new T(function(){return new T3(0,E(_3r),E(new T1(1,_3v)),E(_W));});}else{return new T(function(){return new T3(0,E(_3r),E(_2U),E(_W));});}}else{return new T(function(){return new T3(0,E(_3r),E(_2U),E(_W));});}}},_3w=function(_3x,_3y,_){return new F(function(){return _3i(_3x,E(_3y),_);});},_3z="mouseout",_3A="mouseover",_3B="mousemove",_3C="mouseup",_3D="mousedown",_3E="dblclick",_3F="click",_3G="wheel",_3H=function(_3I){switch(E(_3I)){case 0:return E(_3F);case 1:return E(_3E);case 2:return E(_3D);case 3:return E(_3C);case 4:return E(_3B);case 5:return E(_3A);case 6:return E(_3z);default:return E(_3G);}},_3J=new T2(0,_3H,_3w),_3K=function(_3L){return E(_3L);},_3M=function(_3N,_3O){return E(_3N)==E(_3O);},_3P=function(_3Q,_3R){return E(_3Q)!=E(_3R);},_3S=new T2(0,_3M,_3P),_3T="screenY",_3U="screenX",_3V="clientY",_3W="clientX",_3X="pageY",_3Y="pageX",_3Z="target",_40="identifier",_41=function(_42,_){var _43=__get(_42,E(_40)),_44=__get(_42,E(_3Z)),_45=__get(_42,E(_3Y)),_46=__get(_42,E(_3X)),_47=__get(_42,E(_3W)),_48=__get(_42,E(_3V)),_49=__get(_42,E(_3U)),_4a=__get(_42,E(_3T));return new T(function(){var _4b=Number(_43),_4c=jsTrunc(_4b);return new T5(0,_4c,_44,E(new T2(0,new T(function(){var _4d=Number(_45);return jsTrunc(_4d);}),new T(function(){var _4e=Number(_46);return jsTrunc(_4e);}))),E(new T2(0,new T(function(){var _4f=Number(_47);return jsTrunc(_4f);}),new T(function(){var _4g=Number(_48);return jsTrunc(_4g);}))),E(new T2(0,new T(function(){var _4h=Number(_49);return jsTrunc(_4h);}),new T(function(){var _4i=Number(_4a);return jsTrunc(_4i);}))));});},_4j=function(_4k,_){var _4l=E(_4k);if(!_4l._){return _Z;}else{var _4m=B(_41(E(_4l.a),_)),_4n=B(_4j(_4l.b,_));return new T2(1,_4m,_4n);}},_4o="touches",_4p=function(_4q){return E(E(_4q).b);},_4r=function(_4s,_4t,_){var _4u=__arr2lst(0,_4t),_4v=new T(function(){return B(_4p(_4s));}),_4w=function(_4x,_){var _4y=E(_4x);if(!_4y._){return _Z;}else{var _4z=B(A2(_4v,_4y.a,_)),_4A=B(_4w(_4y.b,_));return new T2(1,_4z,_4A);}};return new F(function(){return _4w(_4u,_);});},_4B=function(_4C,_){return new F(function(){return _4r(_1d,E(_4C),_);});},_4D=new T2(0,_18,_4B),_4E=new T(function(){return eval("(function(e) {  var len = e.changedTouches.length;  var chts = new Array(len);  for(var i = 0; i < len; ++i) {chts[i] = e.changedTouches[i].identifier;}  var len = e.targetTouches.length;  var tts = new Array(len);  for(var i = 0; i < len; ++i) {tts[i] = e.targetTouches[i].identifier;}  return [chts, tts];})");}),_4F=function(_4G){return E(E(_4G).a);},_4H=function(_4I,_4J,_4K){while(1){var _4L=E(_4K);if(!_4L._){return false;}else{if(!B(A3(_4F,_4I,_4J,_4L.a))){_4K=_4L.b;continue;}else{return true;}}}},_4M=function(_4N,_4O){while(1){var _4P=B((function(_4Q,_4R){var _4S=E(_4R);if(!_4S._){return __Z;}else{var _4T=_4S.a,_4U=_4S.b;if(!B(A1(_4Q,_4T))){var _4V=_4Q;_4N=_4V;_4O=_4U;return __continue;}else{return new T2(1,_4T,new T(function(){return B(_4M(_4Q,_4U));}));}}})(_4N,_4O));if(_4P!=__continue){return _4P;}}},_4W=function(_4X,_){var _4Y=__get(_4X,E(_4o)),_4Z=__arr2lst(0,_4Y),_50=B(_4j(_4Z,_)),_51=__app1(E(_4E),_4X),_52=B(_32(_4D,_4D,_51,_)),_53=E(_52),_54=new T(function(){var _55=function(_56){return new F(function(){return _4H(_3S,new T(function(){return E(_56).a;}),_53.a);});};return B(_4M(_55,_50));}),_57=new T(function(){var _58=function(_59){return new F(function(){return _4H(_3S,new T(function(){return E(_59).a;}),_53.b);});};return B(_4M(_58,_50));});return new T3(0,_50,_57,_54);},_5a=function(_5b,_5c,_){return new F(function(){return _4W(E(_5c),_);});},_5d="touchcancel",_5e="touchend",_5f="touchmove",_5g="touchstart",_5h=function(_5i){switch(E(_5i)){case 0:return E(_5g);case 1:return E(_5f);case 2:return E(_5e);default:return E(_5d);}},_5j=new T2(0,_5h,_5a),_5k=function(_5l,_5m,_){var _5n=B(A1(_5l,_)),_5o=B(A1(_5m,_));return _5n;},_5p=function(_5q,_5r,_){var _5s=B(A1(_5q,_)),_5t=B(A1(_5r,_));return new T(function(){return B(A1(_5s,_5t));});},_5u=function(_5v,_5w,_){var _5x=B(A1(_5w,_));return _5v;},_5y=function(_5z,_5A,_){var _5B=B(A1(_5A,_));return new T(function(){return B(A1(_5z,_5B));});},_5C=new T2(0,_5y,_5u),_5D=function(_5E,_){return _5E;},_5F=function(_5G,_5H,_){var _5I=B(A1(_5G,_));return new F(function(){return A1(_5H,_);});},_5J=new T5(0,_5C,_5D,_5p,_5F,_5k),_5K=new T(function(){return E(_2R);}),_5L=function(_5M){return E(E(_5M).c);},_5N=function(_5O){return new T6(0,_2U,_2V,_Z,_5O,_2U,_2U);},_5P=function(_5Q,_){var _5R=new T(function(){return B(A2(_5L,_5K,new T(function(){return B(A1(_5N,_5Q));})));});return new F(function(){return die(_5R);});},_5S=function(_5T,_){return new F(function(){return _5P(_5T,_);});},_5U=function(_5V){return new F(function(){return A1(_5S,_5V);});},_5W=function(_5X,_5Y,_){var _5Z=B(A1(_5X,_));return new F(function(){return A2(_5Y,_5Z,_);});},_60=new T5(0,_5J,_5W,_5F,_5D,_5U),_61=function(_62){return E(_62);},_63=new T2(0,_60,_61),_64=new T2(0,_63,_5D),_65=function(_66,_67){while(1){var _68=E(_66);if(!_68._){return (E(_67)._==0)?1:0;}else{var _69=E(_67);if(!_69._){return 2;}else{var _6a=E(_68.a),_6b=E(_69.a);if(_6a!=_6b){return (_6a>_6b)?2:0;}else{_66=_68.b;_67=_69.b;continue;}}}}},_6c=new T0(1),_6d=new T(function(){return B(unCStr("Failure in Data.Map.balanceR"));}),_6e=function(_6f){return new F(function(){return err(_6d);});},_6g=new T(function(){return B(_6e(_));}),_6h=function(_6i,_6j,_6k,_6l){var _6m=E(_6k);if(!_6m._){var _6n=_6m.a,_6o=E(_6l);if(!_6o._){var _6p=_6o.a,_6q=_6o.b,_6r=_6o.c;if(_6p<=(imul(3,_6n)|0)){return new T5(0,(1+_6n|0)+_6p|0,E(_6i),_6j,E(_6m),E(_6o));}else{var _6s=E(_6o.d);if(!_6s._){var _6t=_6s.a,_6u=_6s.b,_6v=_6s.c,_6w=_6s.d,_6x=E(_6o.e);if(!_6x._){var _6y=_6x.a;if(_6t>=(imul(2,_6y)|0)){var _6z=function(_6A){var _6B=E(_6i),_6C=E(_6s.e);return (_6C._==0)?new T5(0,(1+_6n|0)+_6p|0,E(_6u),_6v,E(new T5(0,(1+_6n|0)+_6A|0,E(_6B),_6j,E(_6m),E(_6w))),E(new T5(0,(1+_6y|0)+_6C.a|0,E(_6q),_6r,E(_6C),E(_6x)))):new T5(0,(1+_6n|0)+_6p|0,E(_6u),_6v,E(new T5(0,(1+_6n|0)+_6A|0,E(_6B),_6j,E(_6m),E(_6w))),E(new T5(0,1+_6y|0,E(_6q),_6r,E(_6c),E(_6x))));},_6D=E(_6w);if(!_6D._){return new F(function(){return _6z(_6D.a);});}else{return new F(function(){return _6z(0);});}}else{return new T5(0,(1+_6n|0)+_6p|0,E(_6q),_6r,E(new T5(0,(1+_6n|0)+_6t|0,E(_6i),_6j,E(_6m),E(_6s))),E(_6x));}}else{return E(_6g);}}else{return E(_6g);}}}else{return new T5(0,1+_6n|0,E(_6i),_6j,E(_6m),E(_6c));}}else{var _6E=E(_6l);if(!_6E._){var _6F=_6E.a,_6G=_6E.b,_6H=_6E.c,_6I=_6E.e,_6J=E(_6E.d);if(!_6J._){var _6K=_6J.a,_6L=_6J.b,_6M=_6J.c,_6N=_6J.d,_6O=E(_6I);if(!_6O._){var _6P=_6O.a;if(_6K>=(imul(2,_6P)|0)){var _6Q=function(_6R){var _6S=E(_6i),_6T=E(_6J.e);return (_6T._==0)?new T5(0,1+_6F|0,E(_6L),_6M,E(new T5(0,1+_6R|0,E(_6S),_6j,E(_6c),E(_6N))),E(new T5(0,(1+_6P|0)+_6T.a|0,E(_6G),_6H,E(_6T),E(_6O)))):new T5(0,1+_6F|0,E(_6L),_6M,E(new T5(0,1+_6R|0,E(_6S),_6j,E(_6c),E(_6N))),E(new T5(0,1+_6P|0,E(_6G),_6H,E(_6c),E(_6O))));},_6U=E(_6N);if(!_6U._){return new F(function(){return _6Q(_6U.a);});}else{return new F(function(){return _6Q(0);});}}else{return new T5(0,1+_6F|0,E(_6G),_6H,E(new T5(0,1+_6K|0,E(_6i),_6j,E(_6c),E(_6J))),E(_6O));}}else{return new T5(0,3,E(_6L),_6M,E(new T5(0,1,E(_6i),_6j,E(_6c),E(_6c))),E(new T5(0,1,E(_6G),_6H,E(_6c),E(_6c))));}}else{var _6V=E(_6I);return (_6V._==0)?new T5(0,3,E(_6G),_6H,E(new T5(0,1,E(_6i),_6j,E(_6c),E(_6c))),E(_6V)):new T5(0,2,E(_6i),_6j,E(_6c),E(_6E));}}else{return new T5(0,1,E(_6i),_6j,E(_6c),E(_6c));}}},_6W=function(_6X,_6Y){return new T5(0,1,E(_6X),_6Y,E(_6c),E(_6c));},_6Z=function(_70,_71,_72){var _73=E(_72);if(!_73._){return new F(function(){return _6h(_73.b,_73.c,_73.d,B(_6Z(_70,_71,_73.e)));});}else{return new F(function(){return _6W(_70,_71);});}},_74=new T(function(){return B(unCStr("Failure in Data.Map.balanceL"));}),_75=function(_76){return new F(function(){return err(_74);});},_77=new T(function(){return B(_75(_));}),_78=function(_79,_7a,_7b,_7c){var _7d=E(_7c);if(!_7d._){var _7e=_7d.a,_7f=E(_7b);if(!_7f._){var _7g=_7f.a,_7h=_7f.b,_7i=_7f.c;if(_7g<=(imul(3,_7e)|0)){return new T5(0,(1+_7g|0)+_7e|0,E(_79),_7a,E(_7f),E(_7d));}else{var _7j=E(_7f.d);if(!_7j._){var _7k=_7j.a,_7l=E(_7f.e);if(!_7l._){var _7m=_7l.a,_7n=_7l.b,_7o=_7l.c,_7p=_7l.d;if(_7m>=(imul(2,_7k)|0)){var _7q=function(_7r){var _7s=E(_7l.e);return (_7s._==0)?new T5(0,(1+_7g|0)+_7e|0,E(_7n),_7o,E(new T5(0,(1+_7k|0)+_7r|0,E(_7h),_7i,E(_7j),E(_7p))),E(new T5(0,(1+_7e|0)+_7s.a|0,E(_79),_7a,E(_7s),E(_7d)))):new T5(0,(1+_7g|0)+_7e|0,E(_7n),_7o,E(new T5(0,(1+_7k|0)+_7r|0,E(_7h),_7i,E(_7j),E(_7p))),E(new T5(0,1+_7e|0,E(_79),_7a,E(_6c),E(_7d))));},_7t=E(_7p);if(!_7t._){return new F(function(){return _7q(_7t.a);});}else{return new F(function(){return _7q(0);});}}else{return new T5(0,(1+_7g|0)+_7e|0,E(_7h),_7i,E(_7j),E(new T5(0,(1+_7e|0)+_7m|0,E(_79),_7a,E(_7l),E(_7d))));}}else{return E(_77);}}else{return E(_77);}}}else{return new T5(0,1+_7e|0,E(_79),_7a,E(_6c),E(_7d));}}else{var _7u=E(_7b);if(!_7u._){var _7v=_7u.a,_7w=_7u.b,_7x=_7u.c,_7y=_7u.e,_7z=E(_7u.d);if(!_7z._){var _7A=_7z.a,_7B=E(_7y);if(!_7B._){var _7C=_7B.a,_7D=_7B.b,_7E=_7B.c,_7F=_7B.d;if(_7C>=(imul(2,_7A)|0)){var _7G=function(_7H){var _7I=E(_7B.e);return (_7I._==0)?new T5(0,1+_7v|0,E(_7D),_7E,E(new T5(0,(1+_7A|0)+_7H|0,E(_7w),_7x,E(_7z),E(_7F))),E(new T5(0,1+_7I.a|0,E(_79),_7a,E(_7I),E(_6c)))):new T5(0,1+_7v|0,E(_7D),_7E,E(new T5(0,(1+_7A|0)+_7H|0,E(_7w),_7x,E(_7z),E(_7F))),E(new T5(0,1,E(_79),_7a,E(_6c),E(_6c))));},_7J=E(_7F);if(!_7J._){return new F(function(){return _7G(_7J.a);});}else{return new F(function(){return _7G(0);});}}else{return new T5(0,1+_7v|0,E(_7w),_7x,E(_7z),E(new T5(0,1+_7C|0,E(_79),_7a,E(_7B),E(_6c))));}}else{return new T5(0,3,E(_7w),_7x,E(_7z),E(new T5(0,1,E(_79),_7a,E(_6c),E(_6c))));}}else{var _7K=E(_7y);return (_7K._==0)?new T5(0,3,E(_7K.b),_7K.c,E(new T5(0,1,E(_7w),_7x,E(_6c),E(_6c))),E(new T5(0,1,E(_79),_7a,E(_6c),E(_6c)))):new T5(0,2,E(_79),_7a,E(_7u),E(_6c));}}else{return new T5(0,1,E(_79),_7a,E(_6c),E(_6c));}}},_7L=function(_7M,_7N,_7O){var _7P=E(_7O);if(!_7P._){return new F(function(){return _78(_7P.b,_7P.c,B(_7L(_7M,_7N,_7P.d)),_7P.e);});}else{return new F(function(){return _6W(_7M,_7N);});}},_7Q=function(_7R,_7S,_7T,_7U,_7V,_7W,_7X){return new F(function(){return _78(_7U,_7V,B(_7L(_7R,_7S,_7W)),_7X);});},_7Y=function(_7Z,_80,_81,_82,_83,_84,_85,_86){var _87=E(_81);if(!_87._){var _88=_87.a,_89=_87.b,_8a=_87.c,_8b=_87.d,_8c=_87.e;if((imul(3,_88)|0)>=_82){if((imul(3,_82)|0)>=_88){return new T5(0,(_88+_82|0)+1|0,E(_7Z),_80,E(_87),E(new T5(0,_82,E(_83),_84,E(_85),E(_86))));}else{return new F(function(){return _6h(_89,_8a,_8b,B(_7Y(_7Z,_80,_8c,_82,_83,_84,_85,_86)));});}}else{return new F(function(){return _78(_83,_84,B(_8d(_7Z,_80,_88,_89,_8a,_8b,_8c,_85)),_86);});}}else{return new F(function(){return _7Q(_7Z,_80,_82,_83,_84,_85,_86);});}},_8d=function(_8e,_8f,_8g,_8h,_8i,_8j,_8k,_8l){var _8m=E(_8l);if(!_8m._){var _8n=_8m.a,_8o=_8m.b,_8p=_8m.c,_8q=_8m.d,_8r=_8m.e;if((imul(3,_8g)|0)>=_8n){if((imul(3,_8n)|0)>=_8g){return new T5(0,(_8g+_8n|0)+1|0,E(_8e),_8f,E(new T5(0,_8g,E(_8h),_8i,E(_8j),E(_8k))),E(_8m));}else{return new F(function(){return _6h(_8h,_8i,_8j,B(_7Y(_8e,_8f,_8k,_8n,_8o,_8p,_8q,_8r)));});}}else{return new F(function(){return _78(_8o,_8p,B(_8d(_8e,_8f,_8g,_8h,_8i,_8j,_8k,_8q)),_8r);});}}else{return new F(function(){return _6Z(_8e,_8f,new T5(0,_8g,E(_8h),_8i,E(_8j),E(_8k)));});}},_8s=function(_8t,_8u,_8v,_8w){var _8x=E(_8v);if(!_8x._){var _8y=_8x.a,_8z=_8x.b,_8A=_8x.c,_8B=_8x.d,_8C=_8x.e,_8D=E(_8w);if(!_8D._){var _8E=_8D.a,_8F=_8D.b,_8G=_8D.c,_8H=_8D.d,_8I=_8D.e;if((imul(3,_8y)|0)>=_8E){if((imul(3,_8E)|0)>=_8y){return new T5(0,(_8y+_8E|0)+1|0,E(_8t),_8u,E(_8x),E(_8D));}else{return new F(function(){return _6h(_8z,_8A,_8B,B(_7Y(_8t,_8u,_8C,_8E,_8F,_8G,_8H,_8I)));});}}else{return new F(function(){return _78(_8F,_8G,B(_8d(_8t,_8u,_8y,_8z,_8A,_8B,_8C,_8H)),_8I);});}}else{return new F(function(){return _6Z(_8t,_8u,_8x);});}}else{return new F(function(){return _7L(_8t,_8u,_8w);});}},_8J=function(_8K,_8L,_8M,_8N){var _8O=E(_8K);if(_8O==1){var _8P=E(_8N);return (_8P._==0)?new T3(0,new T(function(){return new T5(0,1,E(_8L),_8M,E(_6c),E(_6c));}),_Z,_Z):(B(_65(_8L,E(_8P.a).a))==0)?new T3(0,new T(function(){return new T5(0,1,E(_8L),_8M,E(_6c),E(_6c));}),_8P,_Z):new T3(0,new T(function(){return new T5(0,1,E(_8L),_8M,E(_6c),E(_6c));}),_Z,_8P);}else{var _8Q=B(_8J(_8O>>1,_8L,_8M,_8N)),_8R=_8Q.a,_8S=_8Q.c,_8T=E(_8Q.b);if(!_8T._){return new T3(0,_8R,_Z,_8S);}else{var _8U=E(_8T.a),_8V=_8U.a,_8W=_8U.b,_8X=E(_8T.b);if(!_8X._){return new T3(0,new T(function(){return B(_6Z(_8V,_8W,_8R));}),_Z,_8S);}else{var _8Y=E(_8X.a),_8Z=_8Y.a;if(!B(_65(_8V,_8Z))){var _90=B(_8J(_8O>>1,_8Z,_8Y.b,_8X.b));return new T3(0,new T(function(){return B(_8s(_8V,_8W,_8R,_90.a));}),_90.b,_90.c);}else{return new T3(0,_8R,_Z,_8T);}}}}},_91=function(_92,_93,_94){var _95=E(_92),_96=E(_94);if(!_96._){var _97=_96.b,_98=_96.c,_99=_96.d,_9a=_96.e;switch(B(_65(_95,_97))){case 0:return new F(function(){return _78(_97,_98,B(_91(_95,_93,_99)),_9a);});break;case 1:return new T5(0,_96.a,E(_95),_93,E(_99),E(_9a));default:return new F(function(){return _6h(_97,_98,_99,B(_91(_95,_93,_9a)));});}}else{return new T5(0,1,E(_95),_93,E(_6c),E(_6c));}},_9b=function(_9c,_9d){while(1){var _9e=E(_9d);if(!_9e._){return E(_9c);}else{var _9f=E(_9e.a),_9g=B(_91(_9f.a,_9f.b,_9c));_9c=_9g;_9d=_9e.b;continue;}}},_9h=function(_9i,_9j,_9k,_9l){return new F(function(){return _9b(B(_91(_9j,_9k,_9i)),_9l);});},_9m=function(_9n,_9o,_9p){var _9q=E(_9o);return new F(function(){return _9b(B(_91(_9q.a,_9q.b,_9n)),_9p);});},_9r=function(_9s,_9t,_9u){while(1){var _9v=E(_9u);if(!_9v._){return E(_9t);}else{var _9w=E(_9v.a),_9x=_9w.a,_9y=_9w.b,_9z=E(_9v.b);if(!_9z._){return new F(function(){return _6Z(_9x,_9y,_9t);});}else{var _9A=E(_9z.a),_9B=_9A.a;if(!B(_65(_9x,_9B))){var _9C=B(_8J(_9s,_9B,_9A.b,_9z.b)),_9D=_9C.a,_9E=E(_9C.c);if(!_9E._){var _9F=_9s<<1,_9G=B(_8s(_9x,_9y,_9t,_9D));_9s=_9F;_9t=_9G;_9u=_9C.b;continue;}else{return new F(function(){return _9m(B(_8s(_9x,_9y,_9t,_9D)),_9E.a,_9E.b);});}}else{return new F(function(){return _9h(_9t,_9x,_9y,_9z);});}}}}},_9H=function(_9I,_9J,_9K,_9L,_9M){var _9N=E(_9M);if(!_9N._){return new F(function(){return _6Z(_9K,_9L,_9J);});}else{var _9O=E(_9N.a),_9P=_9O.a;if(!B(_65(_9K,_9P))){var _9Q=B(_8J(_9I,_9P,_9O.b,_9N.b)),_9R=_9Q.a,_9S=E(_9Q.c);if(!_9S._){return new F(function(){return _9r(_9I<<1,B(_8s(_9K,_9L,_9J,_9R)),_9Q.b);});}else{return new F(function(){return _9m(B(_8s(_9K,_9L,_9J,_9R)),_9S.a,_9S.b);});}}else{return new F(function(){return _9h(_9J,_9K,_9L,_9N);});}}},_9T=function(_9U){var _9V=E(_9U);if(!_9V._){return new T0(1);}else{var _9W=E(_9V.a),_9X=_9W.a,_9Y=_9W.b,_9Z=E(_9V.b);if(!_9Z._){return new T5(0,1,E(_9X),_9Y,E(_6c),E(_6c));}else{var _a0=_9Z.b,_a1=E(_9Z.a),_a2=_a1.a,_a3=_a1.b;if(!B(_65(_9X,_a2))){return new F(function(){return _9H(1,new T5(0,1,E(_9X),_9Y,E(_6c),E(_6c)),_a2,_a3,_a0);});}else{return new F(function(){return _9h(new T5(0,1,E(_9X),_9Y,E(_6c),E(_6c)),_a2,_a3,_a0);});}}}},_a4=new T(function(){return eval("(function(cv){return cv.getBoundingClientRect().height})");}),_a5=new T(function(){return eval("(function(cv){return cv.getBoundingClientRect().width})");}),_a6=new T(function(){return eval("(function(cv){return cv.height})");}),_a7=new T(function(){return eval("(function(cv){return cv.width})");}),_a8=function(_a9,_){var _aa=__app1(E(_a7),_a9),_ab=__app1(E(_a6),_a9),_ac=__app1(E(_a5),_a9),_ad=__app1(E(_a4),_a9);return new T2(0,new T2(0,_aa,_ab),new T2(0,_ac,_ad));},_ae=function(_af,_ag){while(1){var _ah=E(_af);if(!_ah._){return (E(_ag)._==0)?true:false;}else{var _ai=E(_ag);if(!_ai._){return false;}else{if(E(_ah.a)!=E(_ai.a)){return false;}else{_af=_ah.b;_ag=_ai.b;continue;}}}}},_aj=function(_ak,_al){var _am=E(_al);return (_am._==0)?__Z:new T2(1,new T(function(){return B(A1(_ak,_am.a));}),new T(function(){return B(_aj(_ak,_am.b));}));},_an=function(_ao){return new T1(3,E(B(_aj(_61,_ao))));},_ap="Tried to deserialie a non-array to a list!",_aq=new T1(0,_ap),_ar=new T1(1,_Z),_as=function(_at){var _au=E(_at);if(!_au._){return E(_ar);}else{var _av=B(_as(_au.b));return (_av._==0)?new T1(0,_av.a):new T1(1,new T2(1,_au.a,_av.a));}},_aw=function(_ax){var _ay=E(_ax);if(_ay._==3){return new F(function(){return _as(_ay.a);});}else{return E(_aq);}},_az=function(_aA){return new T1(1,_aA);},_aB=new T4(0,_61,_an,_az,_aw),_aC=function(_aD,_aE,_aF){return new F(function(){return A1(_aD,new T2(1,_2z,new T(function(){return B(A1(_aE,_aF));})));});},_aG=function(_aH){return new F(function(){return _H(0,E(_aH),_Z);});},_aI=34,_aJ=new T2(1,_aI,_Z),_aK=new T(function(){return B(unCStr("!!: negative index"));}),_aL=new T(function(){return B(unCStr("Prelude."));}),_aM=new T(function(){return B(_x(_aL,_aK));}),_aN=new T(function(){return B(err(_aM));}),_aO=new T(function(){return B(unCStr("!!: index too large"));}),_aP=new T(function(){return B(_x(_aL,_aO));}),_aQ=new T(function(){return B(err(_aP));}),_aR=function(_aS,_aT){while(1){var _aU=E(_aS);if(!_aU._){return E(_aQ);}else{var _aV=E(_aT);if(!_aV){return E(_aU.a);}else{_aS=_aU.b;_aT=_aV-1|0;continue;}}}},_aW=function(_aX,_aY){if(_aY>=0){return new F(function(){return _aR(_aX,_aY);});}else{return E(_aN);}},_aZ=new T(function(){return B(unCStr("ACK"));}),_b0=new T(function(){return B(unCStr("BEL"));}),_b1=new T(function(){return B(unCStr("BS"));}),_b2=new T(function(){return B(unCStr("SP"));}),_b3=new T2(1,_b2,_Z),_b4=new T(function(){return B(unCStr("US"));}),_b5=new T2(1,_b4,_b3),_b6=new T(function(){return B(unCStr("RS"));}),_b7=new T2(1,_b6,_b5),_b8=new T(function(){return B(unCStr("GS"));}),_b9=new T2(1,_b8,_b7),_ba=new T(function(){return B(unCStr("FS"));}),_bb=new T2(1,_ba,_b9),_bc=new T(function(){return B(unCStr("ESC"));}),_bd=new T2(1,_bc,_bb),_be=new T(function(){return B(unCStr("SUB"));}),_bf=new T2(1,_be,_bd),_bg=new T(function(){return B(unCStr("EM"));}),_bh=new T2(1,_bg,_bf),_bi=new T(function(){return B(unCStr("CAN"));}),_bj=new T2(1,_bi,_bh),_bk=new T(function(){return B(unCStr("ETB"));}),_bl=new T2(1,_bk,_bj),_bm=new T(function(){return B(unCStr("SYN"));}),_bn=new T2(1,_bm,_bl),_bo=new T(function(){return B(unCStr("NAK"));}),_bp=new T2(1,_bo,_bn),_bq=new T(function(){return B(unCStr("DC4"));}),_br=new T2(1,_bq,_bp),_bs=new T(function(){return B(unCStr("DC3"));}),_bt=new T2(1,_bs,_br),_bu=new T(function(){return B(unCStr("DC2"));}),_bv=new T2(1,_bu,_bt),_bw=new T(function(){return B(unCStr("DC1"));}),_bx=new T2(1,_bw,_bv),_by=new T(function(){return B(unCStr("DLE"));}),_bz=new T2(1,_by,_bx),_bA=new T(function(){return B(unCStr("SI"));}),_bB=new T2(1,_bA,_bz),_bC=new T(function(){return B(unCStr("SO"));}),_bD=new T2(1,_bC,_bB),_bE=new T(function(){return B(unCStr("CR"));}),_bF=new T2(1,_bE,_bD),_bG=new T(function(){return B(unCStr("FF"));}),_bH=new T2(1,_bG,_bF),_bI=new T(function(){return B(unCStr("VT"));}),_bJ=new T2(1,_bI,_bH),_bK=new T(function(){return B(unCStr("LF"));}),_bL=new T2(1,_bK,_bJ),_bM=new T(function(){return B(unCStr("HT"));}),_bN=new T2(1,_bM,_bL),_bO=new T2(1,_b1,_bN),_bP=new T2(1,_b0,_bO),_bQ=new T2(1,_aZ,_bP),_bR=new T(function(){return B(unCStr("ENQ"));}),_bS=new T2(1,_bR,_bQ),_bT=new T(function(){return B(unCStr("EOT"));}),_bU=new T2(1,_bT,_bS),_bV=new T(function(){return B(unCStr("ETX"));}),_bW=new T2(1,_bV,_bU),_bX=new T(function(){return B(unCStr("STX"));}),_bY=new T2(1,_bX,_bW),_bZ=new T(function(){return B(unCStr("SOH"));}),_c0=new T2(1,_bZ,_bY),_c1=new T(function(){return B(unCStr("NUL"));}),_c2=new T2(1,_c1,_c0),_c3=92,_c4=new T(function(){return B(unCStr("\\DEL"));}),_c5=new T(function(){return B(unCStr("\\a"));}),_c6=new T(function(){return B(unCStr("\\\\"));}),_c7=new T(function(){return B(unCStr("\\SO"));}),_c8=new T(function(){return B(unCStr("\\r"));}),_c9=new T(function(){return B(unCStr("\\f"));}),_ca=new T(function(){return B(unCStr("\\v"));}),_cb=new T(function(){return B(unCStr("\\n"));}),_cc=new T(function(){return B(unCStr("\\t"));}),_cd=new T(function(){return B(unCStr("\\b"));}),_ce=function(_cf,_cg){if(_cf<=127){var _ch=E(_cf);switch(_ch){case 92:return new F(function(){return _x(_c6,_cg);});break;case 127:return new F(function(){return _x(_c4,_cg);});break;default:if(_ch<32){var _ci=E(_ch);switch(_ci){case 7:return new F(function(){return _x(_c5,_cg);});break;case 8:return new F(function(){return _x(_cd,_cg);});break;case 9:return new F(function(){return _x(_cc,_cg);});break;case 10:return new F(function(){return _x(_cb,_cg);});break;case 11:return new F(function(){return _x(_ca,_cg);});break;case 12:return new F(function(){return _x(_c9,_cg);});break;case 13:return new F(function(){return _x(_c8,_cg);});break;case 14:return new F(function(){return _x(_c7,new T(function(){var _cj=E(_cg);if(!_cj._){return __Z;}else{if(E(_cj.a)==72){return B(unAppCStr("\\&",_cj));}else{return E(_cj);}}},1));});break;default:return new F(function(){return _x(new T2(1,_c3,new T(function(){return B(_aW(_c2,_ci));})),_cg);});}}else{return new T2(1,_ch,_cg);}}}else{var _ck=new T(function(){var _cl=jsShowI(_cf);return B(_x(fromJSStr(_cl),new T(function(){var _cm=E(_cg);if(!_cm._){return __Z;}else{var _cn=E(_cm.a);if(_cn<48){return E(_cm);}else{if(_cn>57){return E(_cm);}else{return B(unAppCStr("\\&",_cm));}}}},1)));});return new T2(1,_c3,_ck);}},_co=new T(function(){return B(unCStr("\\\""));}),_cp=function(_cq,_cr){var _cs=E(_cq);if(!_cs._){return E(_cr);}else{var _ct=_cs.b,_cu=E(_cs.a);if(_cu==34){return new F(function(){return _x(_co,new T(function(){return B(_cp(_ct,_cr));},1));});}else{return new F(function(){return _ce(_cu,new T(function(){return B(_cp(_ct,_cr));}));});}}},_cv=function(_cw){return new T2(1,_aI,new T(function(){return B(_cp(_cw,_aJ));}));},_cx=function(_cy,_cz){if(_cy<=_cz){var _cA=function(_cB){return new T2(1,_cB,new T(function(){if(_cB!=_cz){return B(_cA(_cB+1|0));}else{return __Z;}}));};return new F(function(){return _cA(_cy);});}else{return __Z;}},_cC=function(_cD){return new F(function(){return _cx(E(_cD),2147483647);});},_cE=function(_cF,_cG,_cH){if(_cH<=_cG){var _cI=new T(function(){var _cJ=_cG-_cF|0,_cK=function(_cL){return (_cL>=(_cH-_cJ|0))?new T2(1,_cL,new T(function(){return B(_cK(_cL+_cJ|0));})):new T2(1,_cL,_Z);};return B(_cK(_cG));});return new T2(1,_cF,_cI);}else{return (_cH<=_cF)?new T2(1,_cF,_Z):__Z;}},_cM=function(_cN,_cO,_cP){if(_cP>=_cO){var _cQ=new T(function(){var _cR=_cO-_cN|0,_cS=function(_cT){return (_cT<=(_cP-_cR|0))?new T2(1,_cT,new T(function(){return B(_cS(_cT+_cR|0));})):new T2(1,_cT,_Z);};return B(_cS(_cO));});return new T2(1,_cN,_cQ);}else{return (_cP>=_cN)?new T2(1,_cN,_Z):__Z;}},_cU=function(_cV,_cW){if(_cW<_cV){return new F(function(){return _cE(_cV,_cW, -2147483648);});}else{return new F(function(){return _cM(_cV,_cW,2147483647);});}},_cX=function(_cY,_cZ){return new F(function(){return _cU(E(_cY),E(_cZ));});},_d0=function(_d1,_d2,_d3){if(_d2<_d1){return new F(function(){return _cE(_d1,_d2,_d3);});}else{return new F(function(){return _cM(_d1,_d2,_d3);});}},_d4=function(_d5,_d6,_d7){return new F(function(){return _d0(E(_d5),E(_d6),E(_d7));});},_d8=function(_d9,_da){return new F(function(){return _cx(E(_d9),E(_da));});},_db=function(_dc){return E(_dc);},_dd=new T(function(){return B(unCStr("Prelude.Enum.pred{Int}: tried to take `pred\' of minBound"));}),_de=new T(function(){return B(err(_dd));}),_df=function(_dg){var _dh=E(_dg);return (_dh==( -2147483648))?E(_de):_dh-1|0;},_di=new T(function(){return B(unCStr("Prelude.Enum.succ{Int}: tried to take `succ\' of maxBound"));}),_dj=new T(function(){return B(err(_di));}),_dk=function(_dl){var _dm=E(_dl);return (_dm==2147483647)?E(_dj):_dm+1|0;},_dn={_:0,a:_dk,b:_df,c:_db,d:_db,e:_cC,f:_cX,g:_d8,h:_d4},_do=function(_dp,_dq){if(_dp<=0){if(_dp>=0){return new F(function(){return quot(_dp,_dq);});}else{if(_dq<=0){return new F(function(){return quot(_dp,_dq);});}else{return quot(_dp+1|0,_dq)-1|0;}}}else{if(_dq>=0){if(_dp>=0){return new F(function(){return quot(_dp,_dq);});}else{if(_dq<=0){return new F(function(){return quot(_dp,_dq);});}else{return quot(_dp+1|0,_dq)-1|0;}}}else{return quot(_dp-1|0,_dq)-1|0;}}},_dr=new T(function(){return B(unCStr("base"));}),_ds=new T(function(){return B(unCStr("GHC.Exception"));}),_dt=new T(function(){return B(unCStr("ArithException"));}),_du=new T5(0,new Long(4194982440,719304104,true),new Long(3110813675,1843557400,true),_dr,_ds,_dt),_dv=new T5(0,new Long(4194982440,719304104,true),new Long(3110813675,1843557400,true),_du,_Z,_Z),_dw=function(_dx){return E(_dv);},_dy=function(_dz){var _dA=E(_dz);return new F(function(){return _1r(B(_1p(_dA.a)),_dw,_dA.b);});},_dB=new T(function(){return B(unCStr("Ratio has zero denominator"));}),_dC=new T(function(){return B(unCStr("denormal"));}),_dD=new T(function(){return B(unCStr("divide by zero"));}),_dE=new T(function(){return B(unCStr("loss of precision"));}),_dF=new T(function(){return B(unCStr("arithmetic underflow"));}),_dG=new T(function(){return B(unCStr("arithmetic overflow"));}),_dH=function(_dI,_dJ){switch(E(_dI)){case 0:return new F(function(){return _x(_dG,_dJ);});break;case 1:return new F(function(){return _x(_dF,_dJ);});break;case 2:return new F(function(){return _x(_dE,_dJ);});break;case 3:return new F(function(){return _x(_dD,_dJ);});break;case 4:return new F(function(){return _x(_dC,_dJ);});break;default:return new F(function(){return _x(_dB,_dJ);});}},_dK=function(_dL){return new F(function(){return _dH(_dL,_Z);});},_dM=function(_dN,_dO,_dP){return new F(function(){return _dH(_dO,_dP);});},_dQ=function(_dR,_dS){return new F(function(){return _2C(_dH,_dR,_dS);});},_dT=new T3(0,_dM,_dK,_dQ),_dU=new T(function(){return new T5(0,_dw,_dT,_dV,_dy,_dK);}),_dV=function(_dW){return new T2(0,_dU,_dW);},_dX=3,_dY=new T(function(){return B(_dV(_dX));}),_dZ=new T(function(){return die(_dY);}),_e0=0,_e1=new T(function(){return B(_dV(_e0));}),_e2=new T(function(){return die(_e1);}),_e3=function(_e4,_e5){var _e6=E(_e5);switch(_e6){case  -1:var _e7=E(_e4);if(_e7==( -2147483648)){return E(_e2);}else{return new F(function(){return _do(_e7, -1);});}break;case 0:return E(_dZ);default:return new F(function(){return _do(_e4,_e6);});}},_e8=function(_e9,_ea){return new F(function(){return _e3(E(_e9),E(_ea));});},_eb=0,_ec=new T2(0,_e2,_eb),_ed=function(_ee,_ef){var _eg=E(_ee),_eh=E(_ef);switch(_eh){case  -1:var _ei=E(_eg);if(_ei==( -2147483648)){return E(_ec);}else{if(_ei<=0){if(_ei>=0){var _ej=quotRemI(_ei, -1);return new T2(0,_ej.a,_ej.b);}else{var _ek=quotRemI(_ei, -1);return new T2(0,_ek.a,_ek.b);}}else{var _el=quotRemI(_ei-1|0, -1);return new T2(0,_el.a-1|0,(_el.b+( -1)|0)+1|0);}}break;case 0:return E(_dZ);default:if(_eg<=0){if(_eg>=0){var _em=quotRemI(_eg,_eh);return new T2(0,_em.a,_em.b);}else{if(_eh<=0){var _en=quotRemI(_eg,_eh);return new T2(0,_en.a,_en.b);}else{var _eo=quotRemI(_eg+1|0,_eh);return new T2(0,_eo.a-1|0,(_eo.b+_eh|0)-1|0);}}}else{if(_eh>=0){if(_eg>=0){var _ep=quotRemI(_eg,_eh);return new T2(0,_ep.a,_ep.b);}else{if(_eh<=0){var _eq=quotRemI(_eg,_eh);return new T2(0,_eq.a,_eq.b);}else{var _er=quotRemI(_eg+1|0,_eh);return new T2(0,_er.a-1|0,(_er.b+_eh|0)-1|0);}}}else{var _es=quotRemI(_eg-1|0,_eh);return new T2(0,_es.a-1|0,(_es.b+_eh|0)+1|0);}}}},_et=function(_eu,_ev){var _ew=_eu%_ev;if(_eu<=0){if(_eu>=0){return E(_ew);}else{if(_ev<=0){return E(_ew);}else{var _ex=E(_ew);return (_ex==0)?0:_ex+_ev|0;}}}else{if(_ev>=0){if(_eu>=0){return E(_ew);}else{if(_ev<=0){return E(_ew);}else{var _ey=E(_ew);return (_ey==0)?0:_ey+_ev|0;}}}else{var _ez=E(_ew);return (_ez==0)?0:_ez+_ev|0;}}},_eA=function(_eB,_eC){var _eD=E(_eC);switch(_eD){case  -1:return E(_eb);case 0:return E(_dZ);default:return new F(function(){return _et(E(_eB),_eD);});}},_eE=function(_eF,_eG){var _eH=E(_eF),_eI=E(_eG);switch(_eI){case  -1:var _eJ=E(_eH);if(_eJ==( -2147483648)){return E(_e2);}else{return new F(function(){return quot(_eJ, -1);});}break;case 0:return E(_dZ);default:return new F(function(){return quot(_eH,_eI);});}},_eK=function(_eL,_eM){var _eN=E(_eL),_eO=E(_eM);switch(_eO){case  -1:var _eP=E(_eN);if(_eP==( -2147483648)){return E(_ec);}else{var _eQ=quotRemI(_eP, -1);return new T2(0,_eQ.a,_eQ.b);}break;case 0:return E(_dZ);default:var _eR=quotRemI(_eN,_eO);return new T2(0,_eR.a,_eR.b);}},_eS=function(_eT,_eU){var _eV=E(_eU);switch(_eV){case  -1:return E(_eb);case 0:return E(_dZ);default:return E(_eT)%_eV;}},_eW=function(_eX){return new T1(0,_eX);},_eY=function(_eZ){return new F(function(){return _eW(E(_eZ));});},_f0=new T1(0,1),_f1=function(_f2){return new T2(0,E(B(_eW(E(_f2)))),E(_f0));},_f3=function(_f4,_f5){return imul(E(_f4),E(_f5))|0;},_f6=function(_f7,_f8){return E(_f7)+E(_f8)|0;},_f9=function(_fa,_fb){return E(_fa)-E(_fb)|0;},_fc=function(_fd){var _fe=E(_fd);return (_fe<0)? -_fe:E(_fe);},_ff=function(_fg){var _fh=E(_fg);if(!_fh._){return E(_fh.a);}else{return new F(function(){return I_toInt(_fh.a);});}},_fi=function(_fj){return new F(function(){return _ff(_fj);});},_fk=function(_fl){return  -E(_fl);},_fm= -1,_fn=0,_fo=1,_fp=function(_fq){var _fr=E(_fq);return (_fr>=0)?(E(_fr)==0)?E(_fn):E(_fo):E(_fm);},_fs={_:0,a:_f6,b:_f9,c:_f3,d:_fk,e:_fc,f:_fp,g:_fi},_ft=function(_fu,_fv){var _fw=E(_fu),_fx=E(_fv);return (_fw>_fx)?E(_fw):E(_fx);},_fy=function(_fz,_fA){var _fB=E(_fz),_fC=E(_fA);return (_fB>_fC)?E(_fC):E(_fB);},_fD=function(_fE,_fF){return (_fE>=_fF)?(_fE!=_fF)?2:1:0;},_fG=function(_fH,_fI){return new F(function(){return _fD(E(_fH),E(_fI));});},_fJ=function(_fK,_fL){return E(_fK)>=E(_fL);},_fM=function(_fN,_fO){return E(_fN)>E(_fO);},_fP=function(_fQ,_fR){return E(_fQ)<=E(_fR);},_fS=function(_fT,_fU){return E(_fT)<E(_fU);},_fV={_:0,a:_3S,b:_fG,c:_fS,d:_fP,e:_fM,f:_fJ,g:_ft,h:_fy},_fW=new T3(0,_fs,_fV,_f1),_fX={_:0,a:_fW,b:_dn,c:_eE,d:_eS,e:_e8,f:_eA,g:_eK,h:_ed,i:_eY},_fY=function(_fZ){var _g0=E(_fZ);return new F(function(){return Math.log(_g0+(_g0+1)*Math.sqrt((_g0-1)/(_g0+1)));});},_g1=function(_g2){var _g3=E(_g2);return new F(function(){return Math.log(_g3+Math.sqrt(1+_g3*_g3));});},_g4=function(_g5){var _g6=E(_g5);return 0.5*Math.log((1+_g6)/(1-_g6));},_g7=function(_g8,_g9){return Math.log(E(_g9))/Math.log(E(_g8));},_ga=3.141592653589793,_gb=new T1(0,1),_gc=function(_gd,_ge){var _gf=E(_gd);if(!_gf._){var _gg=_gf.a,_gh=E(_ge);if(!_gh._){var _gi=_gh.a;return (_gg!=_gi)?(_gg>_gi)?2:0:1;}else{var _gj=I_compareInt(_gh.a,_gg);return (_gj<=0)?(_gj>=0)?1:2:0;}}else{var _gk=_gf.a,_gl=E(_ge);if(!_gl._){var _gm=I_compareInt(_gk,_gl.a);return (_gm>=0)?(_gm<=0)?1:2:0;}else{var _gn=I_compare(_gk,_gl.a);return (_gn>=0)?(_gn<=0)?1:2:0;}}},_go=function(_gp,_gq){var _gr=E(_gp);return (_gr._==0)?_gr.a*Math.pow(2,_gq):I_toNumber(_gr.a)*Math.pow(2,_gq);},_gs=function(_gt,_gu){var _gv=E(_gt);if(!_gv._){var _gw=_gv.a,_gx=E(_gu);return (_gx._==0)?_gw==_gx.a:(I_compareInt(_gx.a,_gw)==0)?true:false;}else{var _gy=_gv.a,_gz=E(_gu);return (_gz._==0)?(I_compareInt(_gy,_gz.a)==0)?true:false:(I_compare(_gy,_gz.a)==0)?true:false;}},_gA=function(_gB,_gC){while(1){var _gD=E(_gB);if(!_gD._){var _gE=_gD.a,_gF=E(_gC);if(!_gF._){var _gG=_gF.a,_gH=addC(_gE,_gG);if(!E(_gH.b)){return new T1(0,_gH.a);}else{_gB=new T1(1,I_fromInt(_gE));_gC=new T1(1,I_fromInt(_gG));continue;}}else{_gB=new T1(1,I_fromInt(_gE));_gC=_gF;continue;}}else{var _gI=E(_gC);if(!_gI._){_gB=_gD;_gC=new T1(1,I_fromInt(_gI.a));continue;}else{return new T1(1,I_add(_gD.a,_gI.a));}}}},_gJ=function(_gK,_gL){while(1){var _gM=E(_gK);if(!_gM._){var _gN=E(_gM.a);if(_gN==( -2147483648)){_gK=new T1(1,I_fromInt( -2147483648));continue;}else{var _gO=E(_gL);if(!_gO._){var _gP=_gO.a;return new T2(0,new T1(0,quot(_gN,_gP)),new T1(0,_gN%_gP));}else{_gK=new T1(1,I_fromInt(_gN));_gL=_gO;continue;}}}else{var _gQ=E(_gL);if(!_gQ._){_gK=_gM;_gL=new T1(1,I_fromInt(_gQ.a));continue;}else{var _gR=I_quotRem(_gM.a,_gQ.a);return new T2(0,new T1(1,_gR.a),new T1(1,_gR.b));}}}},_gS=new T1(0,0),_gT=function(_gU,_gV){while(1){var _gW=E(_gU);if(!_gW._){_gU=new T1(1,I_fromInt(_gW.a));continue;}else{return new T1(1,I_shiftLeft(_gW.a,_gV));}}},_gX=function(_gY,_gZ,_h0){if(!B(_gs(_h0,_gS))){var _h1=B(_gJ(_gZ,_h0)),_h2=_h1.a;switch(B(_gc(B(_gT(_h1.b,1)),_h0))){case 0:return new F(function(){return _go(_h2,_gY);});break;case 1:if(!(B(_ff(_h2))&1)){return new F(function(){return _go(_h2,_gY);});}else{return new F(function(){return _go(B(_gA(_h2,_gb)),_gY);});}break;default:return new F(function(){return _go(B(_gA(_h2,_gb)),_gY);});}}else{return E(_dZ);}},_h3=function(_h4,_h5){var _h6=E(_h4);if(!_h6._){var _h7=_h6.a,_h8=E(_h5);return (_h8._==0)?_h7>_h8.a:I_compareInt(_h8.a,_h7)<0;}else{var _h9=_h6.a,_ha=E(_h5);return (_ha._==0)?I_compareInt(_h9,_ha.a)>0:I_compare(_h9,_ha.a)>0;}},_hb=new T1(0,1),_hc=function(_hd,_he){var _hf=E(_hd);if(!_hf._){var _hg=_hf.a,_hh=E(_he);return (_hh._==0)?_hg<_hh.a:I_compareInt(_hh.a,_hg)>0;}else{var _hi=_hf.a,_hj=E(_he);return (_hj._==0)?I_compareInt(_hi,_hj.a)<0:I_compare(_hi,_hj.a)<0;}},_hk=new T(function(){return B(unCStr("base"));}),_hl=new T(function(){return B(unCStr("Control.Exception.Base"));}),_hm=new T(function(){return B(unCStr("PatternMatchFail"));}),_hn=new T5(0,new Long(18445595,3739165398,true),new Long(52003073,3246954884,true),_hk,_hl,_hm),_ho=new T5(0,new Long(18445595,3739165398,true),new Long(52003073,3246954884,true),_hn,_Z,_Z),_hp=function(_hq){return E(_ho);},_hr=function(_hs){var _ht=E(_hs);return new F(function(){return _1r(B(_1p(_ht.a)),_hp,_ht.b);});},_hu=function(_hv){return E(E(_hv).a);},_hw=function(_hx){return new T2(0,_hy,_hx);},_hz=function(_hA,_hB){return new F(function(){return _x(E(_hA).a,_hB);});},_hC=function(_hD,_hE){return new F(function(){return _2C(_hz,_hD,_hE);});},_hF=function(_hG,_hH,_hI){return new F(function(){return _x(E(_hH).a,_hI);});},_hJ=new T3(0,_hF,_hu,_hC),_hy=new T(function(){return new T5(0,_hp,_hJ,_hw,_hr,_hu);}),_hK=new T(function(){return B(unCStr("Non-exhaustive patterns in"));}),_hL=function(_hM,_hN){return new F(function(){return die(new T(function(){return B(A2(_5L,_hN,_hM));}));});},_hO=function(_hP,_dW){return new F(function(){return _hL(_hP,_dW);});},_hQ=function(_hR,_hS){var _hT=E(_hS);if(!_hT._){return new T2(0,_Z,_Z);}else{var _hU=_hT.a;if(!B(A1(_hR,_hU))){return new T2(0,_Z,_hT);}else{var _hV=new T(function(){var _hW=B(_hQ(_hR,_hT.b));return new T2(0,_hW.a,_hW.b);});return new T2(0,new T2(1,_hU,new T(function(){return E(E(_hV).a);})),new T(function(){return E(E(_hV).b);}));}}},_hX=32,_hY=new T(function(){return B(unCStr("\n"));}),_hZ=function(_i0){return (E(_i0)==124)?false:true;},_i1=function(_i2,_i3){var _i4=B(_hQ(_hZ,B(unCStr(_i2)))),_i5=_i4.a,_i6=function(_i7,_i8){var _i9=new T(function(){var _ia=new T(function(){return B(_x(_i3,new T(function(){return B(_x(_i8,_hY));},1)));});return B(unAppCStr(": ",_ia));},1);return new F(function(){return _x(_i7,_i9);});},_ib=E(_i4.b);if(!_ib._){return new F(function(){return _i6(_i5,_Z);});}else{if(E(_ib.a)==124){return new F(function(){return _i6(_i5,new T2(1,_hX,_ib.b));});}else{return new F(function(){return _i6(_i5,_Z);});}}},_ic=function(_id){return new F(function(){return _hO(new T1(0,new T(function(){return B(_i1(_id,_hK));})),_hy);});},_ie=function(_if){var _ig=function(_ih,_ii){while(1){if(!B(_hc(_ih,_if))){if(!B(_h3(_ih,_if))){if(!B(_gs(_ih,_if))){return new F(function(){return _ic("GHC/Integer/Type.lhs:(553,5)-(555,32)|function l2");});}else{return E(_ii);}}else{return _ii-1|0;}}else{var _ij=B(_gT(_ih,1)),_ik=_ii+1|0;_ih=_ij;_ii=_ik;continue;}}};return new F(function(){return _ig(_hb,0);});},_il=function(_im){var _in=E(_im);if(!_in._){var _io=_in.a>>>0;if(!_io){return  -1;}else{var _ip=function(_iq,_ir){while(1){if(_iq>=_io){if(_iq<=_io){if(_iq!=_io){return new F(function(){return _ic("GHC/Integer/Type.lhs:(609,5)-(611,40)|function l2");});}else{return E(_ir);}}else{return _ir-1|0;}}else{var _is=imul(_iq,2)>>>0,_it=_ir+1|0;_iq=_is;_ir=_it;continue;}}};return new F(function(){return _ip(1,0);});}}else{return new F(function(){return _ie(_in);});}},_iu=function(_iv){var _iw=E(_iv);if(!_iw._){var _ix=_iw.a>>>0;if(!_ix){return new T2(0, -1,0);}else{var _iy=function(_iz,_iA){while(1){if(_iz>=_ix){if(_iz<=_ix){if(_iz!=_ix){return new F(function(){return _ic("GHC/Integer/Type.lhs:(609,5)-(611,40)|function l2");});}else{return E(_iA);}}else{return _iA-1|0;}}else{var _iB=imul(_iz,2)>>>0,_iC=_iA+1|0;_iz=_iB;_iA=_iC;continue;}}};return new T2(0,B(_iy(1,0)),(_ix&_ix-1>>>0)>>>0&4294967295);}}else{var _iD=_iw.a;return new T2(0,B(_il(_iw)),I_compareInt(I_and(_iD,I_sub(_iD,I_fromInt(1))),0));}},_iE=function(_iF,_iG){var _iH=E(_iF);if(!_iH._){var _iI=_iH.a,_iJ=E(_iG);return (_iJ._==0)?_iI<=_iJ.a:I_compareInt(_iJ.a,_iI)>=0;}else{var _iK=_iH.a,_iL=E(_iG);return (_iL._==0)?I_compareInt(_iK,_iL.a)<=0:I_compare(_iK,_iL.a)<=0;}},_iM=function(_iN,_iO){while(1){var _iP=E(_iN);if(!_iP._){var _iQ=_iP.a,_iR=E(_iO);if(!_iR._){return new T1(0,(_iQ>>>0&_iR.a>>>0)>>>0&4294967295);}else{_iN=new T1(1,I_fromInt(_iQ));_iO=_iR;continue;}}else{var _iS=E(_iO);if(!_iS._){_iN=_iP;_iO=new T1(1,I_fromInt(_iS.a));continue;}else{return new T1(1,I_and(_iP.a,_iS.a));}}}},_iT=function(_iU,_iV){while(1){var _iW=E(_iU);if(!_iW._){var _iX=_iW.a,_iY=E(_iV);if(!_iY._){var _iZ=_iY.a,_j0=subC(_iX,_iZ);if(!E(_j0.b)){return new T1(0,_j0.a);}else{_iU=new T1(1,I_fromInt(_iX));_iV=new T1(1,I_fromInt(_iZ));continue;}}else{_iU=new T1(1,I_fromInt(_iX));_iV=_iY;continue;}}else{var _j1=E(_iV);if(!_j1._){_iU=_iW;_iV=new T1(1,I_fromInt(_j1.a));continue;}else{return new T1(1,I_sub(_iW.a,_j1.a));}}}},_j2=new T1(0,2),_j3=function(_j4,_j5){var _j6=E(_j4);if(!_j6._){var _j7=(_j6.a>>>0&(2<<_j5>>>0)-1>>>0)>>>0,_j8=1<<_j5>>>0;return (_j8<=_j7)?(_j8>=_j7)?1:2:0;}else{var _j9=B(_iM(_j6,B(_iT(B(_gT(_j2,_j5)),_hb)))),_ja=B(_gT(_hb,_j5));return (!B(_h3(_ja,_j9)))?(!B(_hc(_ja,_j9)))?1:2:0;}},_jb=function(_jc,_jd){while(1){var _je=E(_jc);if(!_je._){_jc=new T1(1,I_fromInt(_je.a));continue;}else{return new T1(1,I_shiftRight(_je.a,_jd));}}},_jf=function(_jg,_jh,_ji,_jj){var _jk=B(_iu(_jj)),_jl=_jk.a;if(!E(_jk.b)){var _jm=B(_il(_ji));if(_jm<((_jl+_jg|0)-1|0)){var _jn=_jl+(_jg-_jh|0)|0;if(_jn>0){if(_jn>_jm){if(_jn<=(_jm+1|0)){if(!E(B(_iu(_ji)).b)){return 0;}else{return new F(function(){return _go(_gb,_jg-_jh|0);});}}else{return 0;}}else{var _jo=B(_jb(_ji,_jn));switch(B(_j3(_ji,_jn-1|0))){case 0:return new F(function(){return _go(_jo,_jg-_jh|0);});break;case 1:if(!(B(_ff(_jo))&1)){return new F(function(){return _go(_jo,_jg-_jh|0);});}else{return new F(function(){return _go(B(_gA(_jo,_gb)),_jg-_jh|0);});}break;default:return new F(function(){return _go(B(_gA(_jo,_gb)),_jg-_jh|0);});}}}else{return new F(function(){return _go(_ji,(_jg-_jh|0)-_jn|0);});}}else{if(_jm>=_jh){var _jp=B(_jb(_ji,(_jm+1|0)-_jh|0));switch(B(_j3(_ji,_jm-_jh|0))){case 0:return new F(function(){return _go(_jp,((_jm-_jl|0)+1|0)-_jh|0);});break;case 2:return new F(function(){return _go(B(_gA(_jp,_gb)),((_jm-_jl|0)+1|0)-_jh|0);});break;default:if(!(B(_ff(_jp))&1)){return new F(function(){return _go(_jp,((_jm-_jl|0)+1|0)-_jh|0);});}else{return new F(function(){return _go(B(_gA(_jp,_gb)),((_jm-_jl|0)+1|0)-_jh|0);});}}}else{return new F(function(){return _go(_ji, -_jl);});}}}else{var _jq=B(_il(_ji))-_jl|0,_jr=function(_js){var _jt=function(_ju,_jv){if(!B(_iE(B(_gT(_jv,_jh)),_ju))){return new F(function(){return _gX(_js-_jh|0,_ju,_jv);});}else{return new F(function(){return _gX((_js-_jh|0)+1|0,_ju,B(_gT(_jv,1)));});}};if(_js>=_jh){if(_js!=_jh){return new F(function(){return _jt(_ji,new T(function(){return B(_gT(_jj,_js-_jh|0));}));});}else{return new F(function(){return _jt(_ji,_jj);});}}else{return new F(function(){return _jt(new T(function(){return B(_gT(_ji,_jh-_js|0));}),_jj);});}};if(_jg>_jq){return new F(function(){return _jr(_jg);});}else{return new F(function(){return _jr(_jq);});}}},_jw=new T1(0,2147483647),_jx=new T(function(){return B(_gA(_jw,_hb));}),_jy=function(_jz){var _jA=E(_jz);if(!_jA._){var _jB=E(_jA.a);return (_jB==( -2147483648))?E(_jx):new T1(0, -_jB);}else{return new T1(1,I_negate(_jA.a));}},_jC=new T(function(){return 0/0;}),_jD=new T(function(){return  -1/0;}),_jE=new T(function(){return 1/0;}),_jF=0,_jG=function(_jH,_jI){if(!B(_gs(_jI,_gS))){if(!B(_gs(_jH,_gS))){if(!B(_hc(_jH,_gS))){return new F(function(){return _jf( -1021,53,_jH,_jI);});}else{return  -B(_jf( -1021,53,B(_jy(_jH)),_jI));}}else{return E(_jF);}}else{return (!B(_gs(_jH,_gS)))?(!B(_hc(_jH,_gS)))?E(_jE):E(_jD):E(_jC);}},_jJ=function(_jK){var _jL=E(_jK);return new F(function(){return _jG(_jL.a,_jL.b);});},_jM=function(_jN){return 1/E(_jN);},_jO=function(_jP){var _jQ=E(_jP);return (_jQ!=0)?(_jQ<=0)? -_jQ:E(_jQ):E(_jF);},_jR=function(_jS){var _jT=E(_jS);if(!_jT._){return _jT.a;}else{return new F(function(){return I_toNumber(_jT.a);});}},_jU=function(_jV){return new F(function(){return _jR(_jV);});},_jW=1,_jX= -1,_jY=function(_jZ){var _k0=E(_jZ);return (_k0<=0)?(_k0>=0)?E(_k0):E(_jX):E(_jW);},_k1=function(_k2,_k3){return E(_k2)-E(_k3);},_k4=function(_k5){return  -E(_k5);},_k6=function(_k7,_k8){return E(_k7)+E(_k8);},_k9=function(_ka,_kb){return E(_ka)*E(_kb);},_kc={_:0,a:_k6,b:_k1,c:_k9,d:_k4,e:_jO,f:_jY,g:_jU},_kd=function(_ke,_kf){return E(_ke)/E(_kf);},_kg=new T4(0,_kc,_kd,_jM,_jJ),_kh=function(_ki){return new F(function(){return Math.acos(E(_ki));});},_kj=function(_kk){return new F(function(){return Math.asin(E(_kk));});},_kl=function(_km){return new F(function(){return Math.atan(E(_km));});},_kn=function(_ko){return new F(function(){return Math.cos(E(_ko));});},_kp=function(_kq){return new F(function(){return cosh(E(_kq));});},_kr=function(_ks){return new F(function(){return Math.exp(E(_ks));});},_kt=function(_ku){return new F(function(){return Math.log(E(_ku));});},_kv=function(_kw,_kx){return new F(function(){return Math.pow(E(_kw),E(_kx));});},_ky=function(_kz){return new F(function(){return Math.sin(E(_kz));});},_kA=function(_kB){return new F(function(){return sinh(E(_kB));});},_kC=function(_kD){return new F(function(){return Math.sqrt(E(_kD));});},_kE=function(_kF){return new F(function(){return Math.tan(E(_kF));});},_kG=function(_kH){return new F(function(){return tanh(E(_kH));});},_kI={_:0,a:_kg,b:_ga,c:_kr,d:_kt,e:_kC,f:_kv,g:_g7,h:_ky,i:_kn,j:_kE,k:_kj,l:_kh,m:_kl,n:_kA,o:_kp,p:_kG,q:_g1,r:_fY,s:_g4},_kJ=0,_kK=function(_){return _kJ;},_kL=new T(function(){return eval("(function(ctx){ctx.restore();})");}),_kM=new T(function(){return eval("(function(ctx){ctx.save();})");}),_kN=new T(function(){return eval("(function(ctx,rad){ctx.rotate(rad);})");}),_kO=function(_kP,_kQ,_kR,_){var _kS=__app1(E(_kM),_kR),_kT=__app2(E(_kN),_kR,E(_kP)),_kU=B(A2(_kQ,_kR,_)),_kV=__app1(E(_kL),_kR);return new F(function(){return _kK(_);});},_kW=new T(function(){return eval("(function(ctx,x,y){ctx.translate(x,y);})");}),_kX=function(_kY,_kZ,_l0,_l1,_){var _l2=__app1(E(_kM),_l1),_l3=__app3(E(_kW),_l1,E(_kY),E(_kZ)),_l4=B(A2(_l0,_l1,_)),_l5=__app1(E(_kL),_l1);return new F(function(){return _kK(_);});},_l6=function(_l7,_l8){return E(_l7)!=E(_l8);},_l9=function(_la,_lb){return E(_la)==E(_lb);},_lc=new T2(0,_l9,_l6),_ld=function(_le){return E(E(_le).a);},_lf=function(_lg){return E(E(_lg).a);},_lh=function(_li){return E(E(_li).b);},_lj=function(_lk){return E(E(_lk).g);},_ll=new T(function(){return B(unCStr("\u30fc\u301c\u3002\u300c\uff1c\uff1e\uff08\uff09"));}),_lm=0,_ln=3.3333333333333335,_lo=16.666666666666668,_lp=function(_lq){return E(E(_lq).b);},_lr=new T1(0,0),_ls=new T1(0,2),_lt=function(_lu){return E(E(_lu).i);},_lv=function(_lw,_lx,_ly,_lz,_lA,_lB,_lC,_lD){var _lE=new T(function(){var _lF=E(_lD);if(_lF<=31){return B(_4H(_lc,_lF,_ll));}else{if(_lF>=128){return B(_4H(_lc,_lF,_ll));}else{return true;}}}),_lG=new T(function(){if(E(_lz)==8){return new T2(0,new T(function(){return B(_jR(B(A2(_lt,_lx,_lB))))*28+20;}),new T(function(){return B(_jR(B(A2(_lt,_ly,_lC))))*24+8*(E(_lA)-1);}));}else{return new T2(0,new T(function(){return B(_jR(B(A2(_lt,_lx,_lB))))*28;}),new T(function(){return B(_jR(B(A2(_lt,_ly,_lC))))*24;}));}}),_lH=new T(function(){var _lI=B(_ld(_lw));if(!E(_lE)){return B(A2(_lj,B(_lf(_lI)),_lr));}else{return B(A3(_lh,_lI,new T(function(){return B(_lp(_lw));}),new T(function(){return B(A2(_lj,B(_lf(_lI)),_ls));})));}});return new T3(0,new T2(0,new T(function(){return E(E(_lG).a);}),new T(function(){return E(E(_lG).b);})),new T2(0,new T(function(){if(!E(_lE)){return E(_lm);}else{return E(_ln);}}),new T(function(){if(!E(_lE)){return E(_lm);}else{return E(_lo);}})),_lH);},_lJ=new T(function(){return eval("(function(ctx,s,x,y){ctx.fillText(s,x,y);})");}),_lK=function(_lL,_lM,_lN){var _lO=new T(function(){return toJSStr(E(_lN));});return function(_lP,_){var _lQ=__app4(E(_lJ),E(_lP),E(_lO),E(_lL),E(_lM));return new F(function(){return _kK(_);});};},_lR=0,_lS=",",_lT="rgba(",_lU=new T(function(){return toJSStr(_Z);}),_lV="rgb(",_lW=")",_lX=new T2(1,_lW,_Z),_lY=function(_lZ){var _m0=E(_lZ);if(!_m0._){var _m1=jsCat(new T2(1,_lV,new T2(1,new T(function(){return String(_m0.a);}),new T2(1,_lS,new T2(1,new T(function(){return String(_m0.b);}),new T2(1,_lS,new T2(1,new T(function(){return String(_m0.c);}),_lX)))))),E(_lU));return E(_m1);}else{var _m2=jsCat(new T2(1,_lT,new T2(1,new T(function(){return String(_m0.a);}),new T2(1,_lS,new T2(1,new T(function(){return String(_m0.b);}),new T2(1,_lS,new T2(1,new T(function(){return String(_m0.c);}),new T2(1,_lS,new T2(1,new T(function(){return String(_m0.d);}),_lX)))))))),E(_lU));return E(_m2);}},_m3="strokeStyle",_m4="fillStyle",_m5=new T(function(){return eval("(function(e,p){var x = e[p];return typeof x === \'undefined\' ? \'\' : x.toString();})");}),_m6=new T(function(){return eval("(function(e,p,v){e[p] = v;})");}),_m7=function(_m8,_m9){var _ma=new T(function(){return B(_lY(_m8));});return function(_mb,_){var _mc=E(_mb),_md=E(_m4),_me=E(_m5),_mf=__app2(_me,_mc,_md),_mg=E(_m3),_mh=__app2(_me,_mc,_mg),_mi=E(_ma),_mj=E(_m6),_mk=__app3(_mj,_mc,_md,_mi),_ml=__app3(_mj,_mc,_mg,_mi),_mm=B(A2(_m9,_mc,_)),_mn=String(_mf),_mo=__app3(_mj,_mc,_md,_mn),_mp=String(_mh),_mq=__app3(_mj,_mc,_mg,_mp);return new F(function(){return _kK(_);});};},_mr="font",_ms=function(_mt,_mu){var _mv=new T(function(){return toJSStr(E(_mt));});return function(_mw,_){var _mx=E(_mw),_my=E(_mr),_mz=__app2(E(_m5),_mx,_my),_mA=E(_m6),_mB=__app3(_mA,_mx,_my,E(_mv)),_mC=B(A2(_mu,_mx,_)),_mD=String(_mz),_mE=__app3(_mA,_mx,_my,_mD);return new F(function(){return _kK(_);});};},_mF=new T(function(){return B(unCStr("px IPAGothic"));}),_mG=function(_mH,_mI,_mJ,_mK,_mL,_mM,_mN,_){var _mO=new T(function(){var _mP=new T(function(){var _mQ=B(_lv(_kI,_fX,_fX,_mJ,_mK,_mL,_mM,_mN)),_mR=E(_mQ.a),_mS=E(_mQ.b);return new T5(0,_mR.a,_mR.b,_mS.a,_mS.b,_mQ.c);}),_mT=new T(function(){var _mU=E(_mP);return E(_mU.a)+E(_mU.c);}),_mV=new T(function(){var _mW=E(_mP);return E(_mW.b)-E(_mW.d);}),_mX=new T(function(){return E(E(_mP).e);}),_mY=new T(function(){return B(_lK(_lR,_lR,new T2(1,_mN,_Z)));}),_mZ=function(_n0,_){return new F(function(){return _kO(_mX,_mY,E(_n0),_);});};return B(_ms(new T(function(){return B(_x(B(_H(0,E(_mJ),_Z)),_mF));},1),function(_n1,_){return new F(function(){return _kX(_mT,_mV,_mZ,E(_n1),_);});}));});return new F(function(){return A(_m7,[_mI,_mO,_mH,_]);});},_n2=new T3(0,153,255,255),_n3=new T2(1,_n2,_Z),_n4=new T3(0,255,153,204),_n5=new T2(1,_n4,_n3),_n6=new T3(0,255,204,153),_n7=new T2(1,_n6,_n5),_n8=new T3(0,200,255,200),_n9=new T2(1,_n8,_n7),_na=20,_nb=64,_nc=1,_nd=2,_ne=8,_nf=function(_ng,_nh,_ni,_nj,_nk,_nl,_nm,_){while(1){var _nn=B((function(_no,_np,_nq,_nr,_ns,_nt,_nu,_){var _nv=E(_nu);if(!_nv._){return _kJ;}else{var _nw=_nv.b,_nx=E(_nv.a),_ny=E(_nx);switch(_ny){case 10:var _nz=_no,_nA=_np,_nB=_nr,_nC=_nr;_ng=_nz;_nh=_nA;_ni=0;_nj=_nB;_nk=new T(function(){return E(_ns)-1|0;});_nl=_nC;_nm=_nw;return __continue;case 123:return new F(function(){return _nD(_no,_np,_nq,_nr,_ns,_nt,_nw,_);});break;case 65306:var _nE=new T(function(){return B(_aW(_n9,_nq));}),_nF=function(_nG,_nH,_nI,_nJ,_nK,_nL,_){while(1){var _nM=B((function(_nN,_nO,_nP,_nQ,_nR,_nS,_){var _nT=E(_nS);if(!_nT._){return _kJ;}else{var _nU=_nT.b,_nV=E(_nT.a);if(E(_nV)==65306){var _nW=new T(function(){var _nX=E(_nR);if((_nX+1)*24<=E(_np)-10){return new T2(0,_nQ,_nX+1|0);}else{return new T2(0,new T(function(){return E(_nQ)-1|0;}),_nO);}});return new F(function(){return _nf(_nN,_np,_nq,_nO,new T(function(){return E(E(_nW).a);}),new T(function(){return E(E(_nW).b);}),_nU,_);});}else{var _nY=E(_nN),_nZ=B(_mG(_nY.a,_nE,_ne,_nP,_nQ,_nR,_nV,_)),_o0=_nO,_o1=_nP+1,_o2=_nQ,_o3=_nR;_nG=_nY;_nH=_o0;_nI=_o1;_nJ=_o2;_nK=_o3;_nL=_nU;return __continue;}}})(_nG,_nH,_nI,_nJ,_nK,_nL,_));if(_nM!=__continue){return _nM;}}};return new F(function(){return _nF(_no,_nr,0,new T(function(){if(E(_nr)!=E(_nt)){return E(_ns);}else{return E(_ns)+1|0;}}),new T(function(){var _o4=E(_nt);if(E(_nr)!=_o4){return _o4-1|0;}else{var _o5=(E(_np)-10)/24,_o6=_o5&4294967295;if(_o5>=_o6){return _o6;}else{return _o6-1|0;}}}),_nw,_);});break;default:var _o7=function(_o8,_o9){var _oa=new T(function(){switch(E(_ny)){case 42:return E(_nd);break;case 12300:return E(_nc);break;default:return _nq;}}),_ob=new T(function(){var _oc=E(_nt);if((_oc+1)*24<=E(_np)-10){return new T2(0,_ns,_oc+1|0);}else{return new T2(0,new T(function(){return E(_ns)-1|0;}),_nr);}});if(E(_o8)==64){return new F(function(){return _od(_no,_np,_oa,_nr,new T(function(){return E(E(_ob).a);}),new T(function(){return E(E(_ob).b);}),_nw,_);});}else{var _oe=E(_no),_of=B(_mG(_oe.a,new T(function(){return B(_aW(_n9,E(_oa)));},1),_na,_lR,_ns,_nt,_o9,_));return new F(function(){return _od(_oe,_np,_oa,_nr,new T(function(){return E(E(_ob).a);}),new T(function(){return E(E(_ob).b);}),_nw,_);});}},_og=E(_ny);switch(_og){case 42:return new F(function(){return _o7(64,_nb);});break;case 12289:return new F(function(){return _o7(64,_nb);});break;case 12290:return new F(function(){return _o7(64,_nb);});break;default:return new F(function(){return _o7(_og,_nx);});}}}})(_ng,_nh,_ni,_nj,_nk,_nl,_nm,_));if(_nn!=__continue){return _nn;}}},_od=function(_oh,_oi,_oj,_ok,_ol,_om,_on,_){var _oo=E(_on);if(!_oo._){return _kJ;}else{var _op=_oo.b,_oq=E(_oo.a),_or=E(_oq);switch(_or){case 10:return new F(function(){return _nf(_oh,_oi,0,_ok,new T(function(){return E(_ol)-1|0;}),_ok,_op,_);});break;case 123:return new F(function(){return _nD(_oh,_oi,_oj,_ok,_ol,_om,_op,_);});break;case 65306:var _os=new T(function(){return B(_aW(_n9,E(_oj)));}),_ot=function(_ou,_ov,_ow,_ox,_oy,_oz,_){while(1){var _oA=B((function(_oB,_oC,_oD,_oE,_oF,_oG,_){var _oH=E(_oG);if(!_oH._){return _kJ;}else{var _oI=_oH.b,_oJ=E(_oH.a);if(E(_oJ)==65306){var _oK=new T(function(){var _oL=E(_oF);if((_oL+1)*24<=E(_oi)-10){return new T2(0,_oE,_oL+1|0);}else{return new T2(0,new T(function(){return E(_oE)-1|0;}),_oC);}});return new F(function(){return _od(_oB,_oi,_oj,_oC,new T(function(){return E(E(_oK).a);}),new T(function(){return E(E(_oK).b);}),_oI,_);});}else{var _oM=E(_oB),_oN=B(_mG(_oM.a,_os,_ne,_oD,_oE,_oF,_oJ,_)),_oO=_oC,_oP=_oD+1,_oQ=_oE,_oR=_oF;_ou=_oM;_ov=_oO;_ow=_oP;_ox=_oQ;_oy=_oR;_oz=_oI;return __continue;}}})(_ou,_ov,_ow,_ox,_oy,_oz,_));if(_oA!=__continue){return _oA;}}};return new F(function(){return _ot(_oh,_ok,0,new T(function(){if(E(_ok)!=E(_om)){return E(_ol);}else{return E(_ol)+1|0;}}),new T(function(){var _oS=E(_om);if(E(_ok)!=_oS){return _oS-1|0;}else{var _oT=(E(_oi)-10)/24,_oU=_oT&4294967295;if(_oT>=_oU){return _oU;}else{return _oU-1|0;}}}),_op,_);});break;default:var _oV=function(_oW,_oX){var _oY=new T(function(){switch(E(_or)){case 42:return E(_nd);break;case 12300:return E(_nc);break;default:return E(_oj);}}),_oZ=new T(function(){var _p0=E(_om);if((_p0+1)*24<=E(_oi)-10){return new T2(0,_ol,_p0+1|0);}else{return new T2(0,new T(function(){return E(_ol)-1|0;}),_ok);}});if(E(_oW)==64){return new F(function(){return _od(_oh,_oi,_oY,_ok,new T(function(){return E(E(_oZ).a);}),new T(function(){return E(E(_oZ).b);}),_op,_);});}else{var _p1=E(_oh),_p2=B(_mG(_p1.a,new T(function(){return B(_aW(_n9,E(_oY)));},1),_na,_lR,_ol,_om,_oX,_));return new F(function(){return _od(_p1,_oi,_oY,_ok,new T(function(){return E(E(_oZ).a);}),new T(function(){return E(E(_oZ).b);}),_op,_);});}},_p3=E(_or);switch(_p3){case 42:return new F(function(){return _oV(64,_nb);});break;case 12289:return new F(function(){return _oV(64,_nb);});break;case 12290:return new F(function(){return _oV(64,_nb);});break;default:return new F(function(){return _oV(_p3,_oq);});}}}},_nD=function(_p4,_p5,_p6,_p7,_p8,_p9,_pa,_){while(1){var _pb=B((function(_pc,_pd,_pe,_pf,_pg,_ph,_pi,_){var _pj=E(_pi);if(!_pj._){return _kJ;}else{var _pk=_pj.b;if(E(_pj.a)==125){var _pl=new T(function(){var _pm=E(_ph);if((_pm+1)*24<=E(_pd)-10){return new T2(0,_pg,_pm+1|0);}else{return new T2(0,new T(function(){return E(_pg)-1|0;}),_pf);}});return new F(function(){return _od(_pc,_pd,_pe,_pf,new T(function(){return E(E(_pl).a);}),new T(function(){return E(E(_pl).b);}),_pk,_);});}else{var _pn=_pc,_po=_pd,_pp=_pe,_pq=_pf,_pr=_pg,_ps=_ph;_p4=_pn;_p5=_po;_p6=_pp;_p7=_pq;_p8=_pr;_p9=_ps;_pa=_pk;return __continue;}}})(_p4,_p5,_p6,_p7,_p8,_p9,_pa,_));if(_pb!=__continue){return _pb;}}},_pt=function(_pu,_pv,_pw,_px,_py,_pz,_pA,_pB,_){while(1){var _pC=B((function(_pD,_pE,_pF,_pG,_pH,_pI,_pJ,_pK,_){var _pL=E(_pK);if(!_pL._){return _kJ;}else{var _pM=_pL.b,_pN=E(_pL.a),_pO=E(_pN);switch(_pO){case 10:var _pP=_pD,_pQ=_pE,_pR=_pF,_pS=_pH,_pT=_pH;_pu=_pP;_pv=_pQ;_pw=_pR;_px=0;_py=_pS;_pz=new T(function(){return E(_pI)-1|0;});_pA=_pT;_pB=_pM;return __continue;case 123:return new F(function(){return _nD(new T2(0,_pD,_pE),_pF,_pG,_pH,_pI,_pJ,_pM,_);});break;case 65306:var _pU=new T(function(){return B(_aW(_n9,_pG));}),_pV=function(_pW,_pX,_pY,_pZ,_q0,_q1,_q2,_){while(1){var _q3=B((function(_q4,_q5,_q6,_q7,_q8,_q9,_qa,_){var _qb=E(_qa);if(!_qb._){return _kJ;}else{var _qc=_qb.b,_qd=E(_qb.a);if(E(_qd)==65306){var _qe=new T(function(){var _qf=E(_q9);if((_qf+1)*24<=E(_pF)-10){return new T2(0,_q8,_qf+1|0);}else{return new T2(0,new T(function(){return E(_q8)-1|0;}),_q6);}});return new F(function(){return _pt(_q4,_q5,_pF,_pG,_q6,new T(function(){return E(E(_qe).a);}),new T(function(){return E(E(_qe).b);}),_qc,_);});}else{var _qg=B(_mG(_q4,_pU,_ne,_q7,_q8,_q9,_qd,_)),_qh=_q4,_qi=_q5,_qj=_q6,_qk=_q7+1,_ql=_q8,_qm=_q9;_pW=_qh;_pX=_qi;_pY=_qj;_pZ=_qk;_q0=_ql;_q1=_qm;_q2=_qc;return __continue;}}})(_pW,_pX,_pY,_pZ,_q0,_q1,_q2,_));if(_q3!=__continue){return _q3;}}};return new F(function(){return _pV(_pD,_pE,_pH,0,new T(function(){if(E(_pH)!=E(_pJ)){return E(_pI);}else{return E(_pI)+1|0;}}),new T(function(){var _qn=E(_pJ);if(E(_pH)!=_qn){return _qn-1|0;}else{var _qo=(E(_pF)-10)/24,_qp=_qo&4294967295;if(_qo>=_qp){return _qp;}else{return _qp-1|0;}}}),_pM,_);});break;default:var _qq=function(_qr,_qs){var _qt=new T(function(){switch(E(_pO)){case 42:return E(_nd);break;case 12300:return E(_nc);break;default:return _pG;}}),_qu=new T(function(){var _qv=E(_pJ);if((_qv+1)*24<=E(_pF)-10){return new T2(0,_pI,_qv+1|0);}else{return new T2(0,new T(function(){return E(_pI)-1|0;}),_pH);}});if(E(_qr)==64){return new F(function(){return _od(new T2(0,_pD,_pE),_pF,_qt,_pH,new T(function(){return E(E(_qu).a);}),new T(function(){return E(E(_qu).b);}),_pM,_);});}else{var _qw=B(_mG(_pD,new T(function(){return B(_aW(_n9,E(_qt)));},1),_na,_lR,_pI,_pJ,_qs,_));return new F(function(){return _od(new T2(0,_pD,_pE),_pF,_qt,_pH,new T(function(){return E(E(_qu).a);}),new T(function(){return E(E(_qu).b);}),_pM,_);});}},_qx=E(_pO);switch(_qx){case 42:return new F(function(){return _qq(64,_nb);});break;case 12289:return new F(function(){return _qq(64,_nb);});break;case 12290:return new F(function(){return _qq(64,_nb);});break;default:return new F(function(){return _qq(_qx,_pN);});}}}})(_pu,_pv,_pw,_px,_py,_pz,_pA,_pB,_));if(_pC!=__continue){return _pC;}}},_qy=function(_qz,_qA){while(1){var _qB=E(_qz);if(!_qB._){return E(_qA);}else{var _qC=_qA+1|0;_qz=_qB.b;_qA=_qC;continue;}}},_qD=function(_qE,_){return _kJ;},_qF=function(_qG){return E(E(_qG).a);},_qH=function(_qI,_qJ){var _qK=E(_qJ),_qL=new T(function(){var _qM=B(_lf(_qI)),_qN=B(_qH(_qI,B(A3(_qF,_qM,_qK,new T(function(){return B(A2(_lj,_qM,_f0));})))));return new T2(1,_qN.a,_qN.b);});return new T2(0,_qK,_qL);},_qO=new T(function(){var _qP=B(_qH(_kg,_lR));return new T2(1,_qP.a,_qP.b);}),_qQ=new T(function(){return B(_H(0,20,_Z));}),_qR=new T(function(){return B(unCStr("px Courier"));}),_qS=new T(function(){return B(_x(_qQ,_qR));}),_qT=function(_qU,_qV,_qW,_qX,_qY){var _qZ=new T(function(){return E(_qW)*16;}),_r0=new T(function(){return E(_qX)*20;}),_r1=function(_r2,_r3){var _r4=E(_r2);if(!_r4._){return E(_qD);}else{var _r5=E(_r3);if(!_r5._){return E(_qD);}else{var _r6=new T(function(){return B(_r1(_r4.b,_r5.b));}),_r7=new T(function(){var _r8=new T(function(){var _r9=new T(function(){return B(_lK(new T(function(){return E(_qZ)+16*E(_r5.a);}),_r0,new T2(1,_r4.a,_Z)));});return B(_ms(_qS,_r9));});return B(_m7(_qV,_r8));});return function(_ra,_){var _rb=B(A2(_r7,_ra,_));return new F(function(){return A2(_r6,_ra,_);});};}}};return new F(function(){return A3(_r1,_qY,_qO,_qU);});},_rc=45,_rd=new T(function(){return B(unCStr("-"));}),_re=new T2(1,_rc,_rd),_rf=function(_rg){var _rh=E(_rg);return (_rh==1)?E(_re):new T2(1,_rc,new T(function(){return B(_rf(_rh-1|0));}));},_ri=new T(function(){return B(unCStr(": empty list"));}),_rj=function(_rk){return new F(function(){return err(B(_x(_aL,new T(function(){return B(_x(_rk,_ri));},1))));});},_rl=new T(function(){return B(unCStr("head"));}),_rm=new T(function(){return B(_rj(_rl));}),_rn=new T(function(){return eval("(function(e){e.width = e.width;})");}),_ro=new T(function(){return B(_lK(_lR,_lR,_Z));}),_rp=32,_rq=new T(function(){return B(unCStr("|"));}),_rr=function(_rs){var _rt=E(_rs);return (_rt._==0)?E(_rq):new T2(1,new T(function(){var _ru=E(_rt.a);switch(E(_ru.b)){case 7:return E(_rp);break;case 8:return E(_rp);break;default:return E(_ru.a);}}),new T(function(){return B(_rr(_rt.b));}));},_rv=function(_rw,_rx,_ry,_rz,_rA,_){var _rB=__app1(E(_rn),_rx),_rC=B(A2(_ro,_rw,_)),_rD=B(unAppCStr("-",new T(function(){var _rE=E(_rA);if(!_rE._){return E(_rm);}else{var _rF=B(_qy(_rE.a,0));if(0>=_rF){return E(_rd);}else{return B(_rf(_rF));}}}))),_rG=B(A(_qT,[_rw,_n8,_ry,_rz,_rD,_])),_rH=function(_rI,_rJ,_rK,_){while(1){var _rL=B((function(_rM,_rN,_rO,_){var _rP=E(_rO);if(!_rP._){return new F(function(){return A(_qT,[_rw,_n8,_rM,_rN,_rD,_]);});}else{var _rQ=B(A(_qT,[_rw,_n8,_rM,_rN,B(unAppCStr("|",new T(function(){return B(_rr(_rP.a));}))),_])),_rR=_rM;_rI=_rR;_rJ=new T(function(){return E(_rN)+1|0;});_rK=_rP.b;return __continue;}})(_rI,_rJ,_rK,_));if(_rL!=__continue){return _rL;}}};return new F(function(){return _rH(_ry,new T(function(){return E(_rz)+1|0;}),_rA,_);});},_rS=new T(function(){return eval("(function(ctx,x,y){ctx.scale(x,y);})");}),_rT=function(_rU,_rV,_rW,_rX,_){var _rY=__app1(E(_kM),_rX),_rZ=__app3(E(_rS),_rX,E(_rU),E(_rV)),_s0=B(A2(_rW,_rX,_)),_s1=__app1(E(_kL),_rX);return new F(function(){return _kK(_);});},_s2=new T(function(){return eval("(function(ctx,i,x,y){ctx.drawImage(i,x,y);})");}),_s3=function(_s4,_s5,_s6,_s7,_){var _s8=__app4(E(_s2),_s7,_s4,_s5,_s6);return new F(function(){return _kK(_);});},_s9=2,_sa=40,_sb=new T(function(){return B(_aW(_n9,1));}),_sc=new T(function(){return B(_aW(_n9,2));}),_sd=2,_se=function(_sf,_sg,_sh,_si,_sj,_sk,_){var _sl=__app1(E(_rn),_sg),_sm=B(A2(_ro,_sf,_)),_sn=E(_sk),_so=E(_sn.b).a,_sp=E(_sn.a),_sq=_sp.a,_sr=E(_sn.s);if(!E(E(_sn.u).h)){return _kJ;}else{var _ss=B(_rv(_sf,_sg,new T(function(){return B(_f9(_si,_so));}),_sd,_sp.b,_)),_st=B(A(_qT,[_sf,new T(function(){if(E(_sp.e)==32){return E(_sb);}else{return E(_sc);}}),new T(function(){return ((E(E(_sq).a)+1|0)+E(_si)|0)-E(_so)|0;},1),new T(function(){return (E(E(_sq).b)+2|0)+1|0;},1),new T2(1,_sp.d,_Z),_])),_su=function(_sv,_){return new F(function(){return _rT(_s9,_s9,function(_sw,_){return new F(function(){return _s3(B(_aW(E(_sj).b,(imul(E(_sr.a),8)|0)+E(_sr.b)|0)),0,0,E(_sw),_);});},E(_sv),_);});};return new F(function(){return _kX(new T(function(){return E(_sh)-(E(_so)+10|0)*16;},1),_sa,_su,_sf,_);});}},_sx=function(_sy){return E(E(_sy).a);},_sz=function(_sA){return E(E(_sA).a);},_sB=function(_sC,_sD){while(1){var _sE=E(_sC);if(!_sE._){return E(_sD);}else{_sC=_sE.b;_sD=_sE.a;continue;}}},_sF=function(_sG,_sH,_sI){return new F(function(){return _sB(_sH,_sG);});},_sJ=new T1(0,2),_sK=function(_sL,_sM){while(1){var _sN=E(_sL);if(!_sN._){var _sO=_sN.a,_sP=E(_sM);if(!_sP._){var _sQ=_sP.a;if(!(imul(_sO,_sQ)|0)){return new T1(0,imul(_sO,_sQ)|0);}else{_sL=new T1(1,I_fromInt(_sO));_sM=new T1(1,I_fromInt(_sQ));continue;}}else{_sL=new T1(1,I_fromInt(_sO));_sM=_sP;continue;}}else{var _sR=E(_sM);if(!_sR._){_sL=_sN;_sM=new T1(1,I_fromInt(_sR.a));continue;}else{return new T1(1,I_mul(_sN.a,_sR.a));}}}},_sS=function(_sT,_sU,_sV){while(1){if(!(_sU%2)){var _sW=B(_sK(_sT,_sT)),_sX=quot(_sU,2);_sT=_sW;_sU=_sX;continue;}else{var _sY=E(_sU);if(_sY==1){return new F(function(){return _sK(_sT,_sV);});}else{var _sW=B(_sK(_sT,_sT)),_sZ=B(_sK(_sT,_sV));_sT=_sW;_sU=quot(_sY-1|0,2);_sV=_sZ;continue;}}}},_t0=function(_t1,_t2){while(1){if(!(_t2%2)){var _t3=B(_sK(_t1,_t1)),_t4=quot(_t2,2);_t1=_t3;_t2=_t4;continue;}else{var _t5=E(_t2);if(_t5==1){return E(_t1);}else{return new F(function(){return _sS(B(_sK(_t1,_t1)),quot(_t5-1|0,2),_t1);});}}}},_t6=function(_t7){return E(E(_t7).c);},_t8=function(_t9){return E(E(_t9).a);},_ta=function(_tb){return E(E(_tb).b);},_tc=function(_td){return E(E(_td).b);},_te=function(_tf){return E(E(_tf).c);},_tg=new T1(0,0),_th=new T1(0,2),_ti=function(_tj){return E(E(_tj).d);},_tk=function(_tl,_tm){var _tn=B(_sx(_tl)),_to=new T(function(){return B(_sz(_tn));}),_tp=new T(function(){return B(A3(_ti,_tl,_tm,new T(function(){return B(A2(_lj,_to,_th));})));});return new F(function(){return A3(_4F,B(_t8(B(_ta(_tn)))),_tp,new T(function(){return B(A2(_lj,_to,_tg));}));});},_tq=new T(function(){return B(unCStr("Negative exponent"));}),_tr=new T(function(){return B(err(_tq));}),_ts=function(_tt){return E(E(_tt).c);},_tu=function(_tv,_tw,_tx,_ty){var _tz=B(_sx(_tw)),_tA=new T(function(){return B(_sz(_tz));}),_tB=B(_ta(_tz));if(!B(A3(_te,_tB,_ty,new T(function(){return B(A2(_lj,_tA,_tg));})))){if(!B(A3(_4F,B(_t8(_tB)),_ty,new T(function(){return B(A2(_lj,_tA,_tg));})))){var _tC=new T(function(){return B(A2(_lj,_tA,_th));}),_tD=new T(function(){return B(A2(_lj,_tA,_f0));}),_tE=B(_t8(_tB)),_tF=function(_tG,_tH,_tI){while(1){var _tJ=B((function(_tK,_tL,_tM){if(!B(_tk(_tw,_tL))){if(!B(A3(_4F,_tE,_tL,_tD))){var _tN=new T(function(){return B(A3(_ts,_tw,new T(function(){return B(A3(_tc,_tA,_tL,_tD));}),_tC));});_tG=new T(function(){return B(A3(_t6,_tv,_tK,_tK));});_tH=_tN;_tI=new T(function(){return B(A3(_t6,_tv,_tK,_tM));});return __continue;}else{return new F(function(){return A3(_t6,_tv,_tK,_tM);});}}else{var _tO=_tM;_tG=new T(function(){return B(A3(_t6,_tv,_tK,_tK));});_tH=new T(function(){return B(A3(_ts,_tw,_tL,_tC));});_tI=_tO;return __continue;}})(_tG,_tH,_tI));if(_tJ!=__continue){return _tJ;}}},_tP=function(_tQ,_tR){while(1){var _tS=B((function(_tT,_tU){if(!B(_tk(_tw,_tU))){if(!B(A3(_4F,_tE,_tU,_tD))){var _tV=new T(function(){return B(A3(_ts,_tw,new T(function(){return B(A3(_tc,_tA,_tU,_tD));}),_tC));});return new F(function(){return _tF(new T(function(){return B(A3(_t6,_tv,_tT,_tT));}),_tV,_tT);});}else{return E(_tT);}}else{_tQ=new T(function(){return B(A3(_t6,_tv,_tT,_tT));});_tR=new T(function(){return B(A3(_ts,_tw,_tU,_tC));});return __continue;}})(_tQ,_tR));if(_tS!=__continue){return _tS;}}};return new F(function(){return _tP(_tx,_ty);});}else{return new F(function(){return A2(_lj,_tv,_f0);});}}else{return E(_tr);}},_tW=new T(function(){return B(err(_tq));}),_tX=function(_tY){var _tZ=I_decodeDouble(_tY);return new T2(0,new T1(1,_tZ.b),_tZ.a);},_u0=function(_u1,_u2){var _u3=B(_tX(_u2)),_u4=_u3.a,_u5=_u3.b,_u6=new T(function(){return B(_sz(new T(function(){return B(_sx(_u1));})));});if(_u5<0){var _u7= -_u5;if(_u7>=0){var _u8=E(_u7);if(!_u8){var _u9=E(_f0);}else{var _u9=B(_t0(_sJ,_u8));}if(!B(_gs(_u9,_gS))){var _ua=B(_gJ(_u4,_u9));return new T2(0,new T(function(){return B(A2(_lj,_u6,_ua.a));}),new T(function(){return B(_go(_ua.b,_u5));}));}else{return E(_dZ);}}else{return E(_tW);}}else{var _ub=new T(function(){var _uc=new T(function(){return B(_tu(_u6,_fX,new T(function(){return B(A2(_lj,_u6,_sJ));}),_u5));});return B(A3(_t6,_u6,new T(function(){return B(A2(_lj,_u6,_u4));}),_uc));});return new T2(0,_ub,_jF);}},_ud=function(_ue,_uf){while(1){var _ug=E(_uf);if(!_ug._){return __Z;}else{var _uh=_ug.b,_ui=E(_ue);if(_ui==1){return E(_uh);}else{_ue=_ui-1|0;_uf=_uh;continue;}}}},_uj=function(_uk,_ul){var _um=E(_ul);if(!_um._){return __Z;}else{var _un=_um.a,_uo=E(_uk);return (_uo==1)?new T2(1,_un,_Z):new T2(1,_un,new T(function(){return B(_uj(_uo-1|0,_um.b));}));}},_up=function(_uq,_ur,_us,_ut){while(1){if(B(_aW(new T2(1,_us,_ut),_ur))!=_uq){var _uu=_ur+1|0;_ur=_uu;continue;}else{if(0>=_ur){return __Z;}else{return new F(function(){return _uj(_ur,new T2(1,_us,_ut));});}}}},_uv=function(_uw,_ux,_uy){var _uz=E(_uy);if(!_uz._){return __Z;}else{var _uA=E(_uw);if(B(_aW(_uz,_ux))!=_uA){return new F(function(){return _up(_uA,_ux+1|0,_uz.a,_uz.b);});}else{if(0>=_ux){return __Z;}else{return new F(function(){return _uj(_ux,_uz);});}}}},_uB=function(_uC,_uD,_uE){var _uF=_uD+1|0;if(_uF>0){return new F(function(){return _ud(_uF,B(_uv(_uC,_uF,_uE)));});}else{return new F(function(){return _uv(_uC,_uF,_uE);});}},_uG=function(_uH,_uI){return (!B(_ae(_uH,_uI)))?true:false;},_uJ=new T2(0,_ae,_uG),_uK=0,_uL=new T(function(){return B(_ic("Event.hs:(81,1)-(82,68)|function addEvent"));}),_uM=function(_uN,_uO,_uP,_uQ,_uR,_uS,_uT,_uU,_uV,_uW,_uX,_uY,_uZ,_v0,_v1,_v2,_v3,_v4,_v5,_v6,_v7,_v8,_v9){while(1){var _va=E(_uN);if(!_va._){return {_:0,a:_uO,b:_uP,c:_uQ,d:_uR,e:_uS,f:_uT,g:_uU,h:_uV,i:_uW,j:_uX,k:_uY,l:_uZ,m:_v0,n:_v1,o:_v2,p:_v3,q:_v4,r:_v5,s:_v6,t:_v7,u:_v8,v:_v9};}else{var _vb=E(_va.b);if(!_vb._){return E(_uL);}else{var _vc=new T2(1,new T2(0,_va.a,_vb.a),_uS),_vd=new T2(1,_uK,_uT);_uN=_vb.b;_uS=_vc;_uT=_vd;continue;}}}},_ve=function(_vf,_vg,_vh){var _vi=E(_vh);if(!_vi._){return __Z;}else{var _vj=_vi.a,_vk=_vi.b;return (!B(A2(_vf,_vg,_vj)))?new T2(1,_vj,new T(function(){return B(_ve(_vf,_vg,_vk));})):E(_vk);}},_vl=function(_vm,_vn){while(1){var _vo=E(_vm);if(!_vo._){return (E(_vn)._==0)?true:false;}else{var _vp=E(_vn);if(!_vp._){return false;}else{if(E(_vo.a)!=E(_vp.a)){return false;}else{_vm=_vo.b;_vn=_vp.b;continue;}}}}},_vq=function(_vr,_vs){while(1){var _vt=E(_vr);if(!_vt._){return (E(_vs)._==0)?true:false;}else{var _vu=E(_vs);if(!_vu._){return false;}else{if(!B(_ae(_vt.a,_vu.a))){return false;}else{_vr=_vt.b;_vs=_vu.b;continue;}}}}},_vv=function(_vw,_vx){switch(E(_vw)){case 0:return (E(_vx)==0)?true:false;case 1:return (E(_vx)==1)?true:false;case 2:return (E(_vx)==2)?true:false;case 3:return (E(_vx)==3)?true:false;case 4:return (E(_vx)==4)?true:false;case 5:return (E(_vx)==5)?true:false;case 6:return (E(_vx)==6)?true:false;case 7:return (E(_vx)==7)?true:false;default:return (E(_vx)==8)?true:false;}},_vy=function(_vz,_vA,_vB,_vC){if(_vz!=_vB){return false;}else{return new F(function(){return _vv(_vA,_vC);});}},_vD=function(_vE,_vF){var _vG=E(_vE),_vH=E(_vF);return new F(function(){return _vy(E(_vG.a),_vG.b,E(_vH.a),_vH.b);});},_vI=function(_vJ,_vK,_vL,_vM){if(_vJ!=_vL){return true;}else{switch(E(_vK)){case 0:return (E(_vM)==0)?false:true;case 1:return (E(_vM)==1)?false:true;case 2:return (E(_vM)==2)?false:true;case 3:return (E(_vM)==3)?false:true;case 4:return (E(_vM)==4)?false:true;case 5:return (E(_vM)==5)?false:true;case 6:return (E(_vM)==6)?false:true;case 7:return (E(_vM)==7)?false:true;default:return (E(_vM)==8)?false:true;}}},_vN=function(_vO,_vP){var _vQ=E(_vO),_vR=E(_vP);return new F(function(){return _vI(E(_vQ.a),_vQ.b,E(_vR.a),_vR.b);});},_vS=new T2(0,_vD,_vN),_vT=0,_vU=function(_vV,_vW){var _vX=E(_vW);if(!_vX._){return 0;}else{var _vY=_vX.b,_vZ=E(_vV),_w0=E(_vX.a),_w1=_w0.b;if(E(_vZ.a)!=E(_w0.a)){return 1+B(_vU(_vZ,_vY))|0;}else{switch(E(_vZ.b)){case 0:return (E(_w1)==0)?0:1+B(_vU(_vZ,_vY))|0;case 1:return (E(_w1)==1)?0:1+B(_vU(_vZ,_vY))|0;case 2:return (E(_w1)==2)?0:1+B(_vU(_vZ,_vY))|0;case 3:return (E(_w1)==3)?0:1+B(_vU(_vZ,_vY))|0;case 4:return (E(_w1)==4)?0:1+B(_vU(_vZ,_vY))|0;case 5:return (E(_w1)==5)?0:1+B(_vU(_vZ,_vY))|0;case 6:return (E(_w1)==6)?0:1+B(_vU(_vZ,_vY))|0;case 7:return (E(_w1)==7)?0:1+B(_vU(_vZ,_vY))|0;default:return (E(_w1)==8)?0:1+B(_vU(_vZ,_vY))|0;}}}},_w2=function(_w3,_w4){return new F(function(){return _vU(_w3,_w4);});},_w5=function(_w6,_w7){var _w8=E(_w7);if(!_w8._){return new T2(0,_vT,_vT);}else{var _w9=_w8.a,_wa=_w8.b;return (!B(_4H(_vS,_w6,_w9)))?new T2(0,new T(function(){return E(B(_w5(_w6,_wa)).a);}),new T(function(){return 1+E(B(_w5(_w6,_wa)).b)|0;})):new T2(0,new T(function(){return B(_w2(_w6,_w9));}),_vT);}},_wb=function(_wc,_wd){while(1){var _we=E(_wd);if(!_we._){return __Z;}else{var _wf=_we.b,_wg=E(_wc);if(_wg==1){return E(_wf);}else{_wc=_wg-1|0;_wd=_wf;continue;}}}},_wh=new T(function(){return B(unCStr("getch"));}),_wi=new T(function(){return B(unCStr("=="));}),_wj=new T(function(){return B(unCStr("&&"));}),_wk=new T(function(){return B(unCStr("||"));}),_wl=new T(function(){return B(unCStr("getpos"));}),_wm=new T(function(){return B(unCStr("ch"));}),_wn=new T(function(){return B(unCStr("tp"));}),_wo=new T2(1,_wn,_Z),_wp=new T2(1,_wm,_wo),_wq=new T2(0,_wl,_wp),_wr=new T(function(){return B(unCStr("a"));}),_ws=new T(function(){return B(unCStr("b"));}),_wt=new T2(1,_ws,_Z),_wu=new T2(1,_wr,_wt),_wv=new T2(0,_wi,_wu),_ww=new T2(0,_wj,_wu),_wx=new T2(0,_wk,_wu),_wy=new T2(1,_wx,_Z),_wz=new T2(1,_ww,_wy),_wA=new T2(1,_wv,_wz),_wB=new T2(1,_wq,_wA),_wC=new T(function(){return B(unCStr("p"));}),_wD=new T(function(){return B(unCStr("q"));}),_wE=new T2(1,_wD,_Z),_wF=new T2(1,_wC,_wE),_wG=new T2(0,_wh,_wF),_wH=new T2(1,_wG,_wB),_wI=new T(function(){return B(unCStr("foldr1"));}),_wJ=new T(function(){return B(_rj(_wI));}),_wK=function(_wL,_wM){var _wN=E(_wM);if(!_wN._){return E(_wJ);}else{var _wO=_wN.a,_wP=E(_wN.b);if(!_wP._){return E(_wO);}else{return new F(function(){return A2(_wL,_wO,new T(function(){return B(_wK(_wL,_wP));}));});}}},_wQ=function(_wR){return E(E(_wR).a);},_wS=function(_wT,_wU,_wV){while(1){var _wW=E(_wV);if(!_wW._){return __Z;}else{var _wX=E(_wW.a);if(!B(A3(_4F,_wT,_wU,_wX.a))){_wV=_wW.b;continue;}else{return new T1(1,_wX.b);}}}},_wY=new T(function(){return B(unCStr("Prelude.read: no parse"));}),_wZ=new T(function(){return B(err(_wY));}),_x0=new T(function(){return B(unCStr("T"));}),_x1=new T(function(){return B(unCStr("F"));}),_x2=new T(function(){return B(unCStr("Prelude.read: ambiguous parse"));}),_x3=new T(function(){return B(err(_x2));}),_x4=new T(function(){return B(unCStr("empty"));}),_x5=new T2(1,_x4,_Z),_x6=new T(function(){return B(_ic("Text/ParserCombinators/ReadP.hs:(128,3)-(151,52)|function <|>"));}),_x7=function(_x8,_x9){while(1){var _xa=B((function(_xb,_xc){var _xd=E(_xb);switch(_xd._){case 0:var _xe=E(_xc);if(!_xe._){return __Z;}else{_x8=B(A1(_xd.a,_xe.a));_x9=_xe.b;return __continue;}break;case 1:var _xf=B(A1(_xd.a,_xc)),_xg=_xc;_x8=_xf;_x9=_xg;return __continue;case 2:return __Z;case 3:return new T2(1,new T2(0,_xd.a,_xc),new T(function(){return B(_x7(_xd.b,_xc));}));default:return E(_xd.a);}})(_x8,_x9));if(_xa!=__continue){return _xa;}}},_xh=function(_xi,_xj){var _xk=function(_xl){var _xm=E(_xj);if(_xm._==3){return new T2(3,_xm.a,new T(function(){return B(_xh(_xi,_xm.b));}));}else{var _xn=E(_xi);if(_xn._==2){return E(_xm);}else{var _xo=E(_xm);if(_xo._==2){return E(_xn);}else{var _xp=function(_xq){var _xr=E(_xo);if(_xr._==4){var _xs=function(_xt){return new T1(4,new T(function(){return B(_x(B(_x7(_xn,_xt)),_xr.a));}));};return new T1(1,_xs);}else{var _xu=E(_xn);if(_xu._==1){var _xv=_xu.a,_xw=E(_xr);if(!_xw._){return new T1(1,function(_xx){return new F(function(){return _xh(B(A1(_xv,_xx)),_xw);});});}else{var _xy=function(_xz){return new F(function(){return _xh(B(A1(_xv,_xz)),new T(function(){return B(A1(_xw.a,_xz));}));});};return new T1(1,_xy);}}else{var _xA=E(_xr);if(!_xA._){return E(_x6);}else{var _xB=function(_xC){return new F(function(){return _xh(_xu,new T(function(){return B(A1(_xA.a,_xC));}));});};return new T1(1,_xB);}}}},_xD=E(_xn);switch(_xD._){case 1:var _xE=E(_xo);if(_xE._==4){var _xF=function(_xG){return new T1(4,new T(function(){return B(_x(B(_x7(B(A1(_xD.a,_xG)),_xG)),_xE.a));}));};return new T1(1,_xF);}else{return new F(function(){return _xp(_);});}break;case 4:var _xH=_xD.a,_xI=E(_xo);switch(_xI._){case 0:var _xJ=function(_xK){var _xL=new T(function(){return B(_x(_xH,new T(function(){return B(_x7(_xI,_xK));},1)));});return new T1(4,_xL);};return new T1(1,_xJ);case 1:var _xM=function(_xN){var _xO=new T(function(){return B(_x(_xH,new T(function(){return B(_x7(B(A1(_xI.a,_xN)),_xN));},1)));});return new T1(4,_xO);};return new T1(1,_xM);default:return new T1(4,new T(function(){return B(_x(_xH,_xI.a));}));}break;default:return new F(function(){return _xp(_);});}}}}},_xP=E(_xi);switch(_xP._){case 0:var _xQ=E(_xj);if(!_xQ._){var _xR=function(_xS){return new F(function(){return _xh(B(A1(_xP.a,_xS)),new T(function(){return B(A1(_xQ.a,_xS));}));});};return new T1(0,_xR);}else{return new F(function(){return _xk(_);});}break;case 3:return new T2(3,_xP.a,new T(function(){return B(_xh(_xP.b,_xj));}));default:return new F(function(){return _xk(_);});}},_xT=new T(function(){return B(unCStr("("));}),_xU=new T(function(){return B(unCStr(")"));}),_xV=function(_xW,_xX){var _xY=E(_xW);switch(_xY._){case 0:return new T1(0,function(_xZ){return new F(function(){return _xV(B(A1(_xY.a,_xZ)),_xX);});});case 1:return new T1(1,function(_y0){return new F(function(){return _xV(B(A1(_xY.a,_y0)),_xX);});});case 2:return new T0(2);case 3:return new F(function(){return _xh(B(A1(_xX,_xY.a)),new T(function(){return B(_xV(_xY.b,_xX));}));});break;default:var _y1=function(_y2){var _y3=E(_y2);if(!_y3._){return __Z;}else{var _y4=E(_y3.a);return new F(function(){return _x(B(_x7(B(A1(_xX,_y4.a)),_y4.b)),new T(function(){return B(_y1(_y3.b));},1));});}},_y5=B(_y1(_xY.a));return (_y5._==0)?new T0(2):new T1(4,_y5);}},_y6=new T0(2),_y7=function(_y8){return new T2(3,_y8,_y6);},_y9=function(_ya,_yb){var _yc=E(_ya);if(!_yc){return new F(function(){return A1(_yb,_kJ);});}else{var _yd=new T(function(){return B(_y9(_yc-1|0,_yb));});return new T1(0,function(_ye){return E(_yd);});}},_yf=function(_yg,_yh,_yi){var _yj=new T(function(){return B(A1(_yg,_y7));}),_yk=function(_yl,_ym,_yn,_yo){while(1){var _yp=B((function(_yq,_yr,_ys,_yt){var _yu=E(_yq);switch(_yu._){case 0:var _yv=E(_yr);if(!_yv._){return new F(function(){return A1(_yh,_yt);});}else{var _yw=_ys+1|0,_yx=_yt;_yl=B(A1(_yu.a,_yv.a));_ym=_yv.b;_yn=_yw;_yo=_yx;return __continue;}break;case 1:var _yy=B(A1(_yu.a,_yr)),_yz=_yr,_yw=_ys,_yx=_yt;_yl=_yy;_ym=_yz;_yn=_yw;_yo=_yx;return __continue;case 2:return new F(function(){return A1(_yh,_yt);});break;case 3:var _yA=new T(function(){return B(_xV(_yu,_yt));});return new F(function(){return _y9(_ys,function(_yB){return E(_yA);});});break;default:return new F(function(){return _xV(_yu,_yt);});}})(_yl,_ym,_yn,_yo));if(_yp!=__continue){return _yp;}}};return function(_yC){return new F(function(){return _yk(_yj,_yC,0,_yi);});};},_yD=function(_yE){return new F(function(){return A1(_yE,_Z);});},_yF=function(_yG,_yH){var _yI=function(_yJ){var _yK=E(_yJ);if(!_yK._){return E(_yD);}else{var _yL=_yK.a;if(!B(A1(_yG,_yL))){return E(_yD);}else{var _yM=new T(function(){return B(_yI(_yK.b));}),_yN=function(_yO){var _yP=new T(function(){return B(A1(_yM,function(_yQ){return new F(function(){return A1(_yO,new T2(1,_yL,_yQ));});}));});return new T1(0,function(_yR){return E(_yP);});};return E(_yN);}}};return function(_yS){return new F(function(){return A2(_yI,_yS,_yH);});};},_yT=new T0(6),_yU=new T(function(){return B(unCStr("valDig: Bad base"));}),_yV=new T(function(){return B(err(_yU));}),_yW=function(_yX,_yY){var _yZ=function(_z0,_z1){var _z2=E(_z0);if(!_z2._){var _z3=new T(function(){return B(A1(_z1,_Z));});return function(_z4){return new F(function(){return A1(_z4,_z3);});};}else{var _z5=E(_z2.a),_z6=function(_z7){var _z8=new T(function(){return B(_yZ(_z2.b,function(_z9){return new F(function(){return A1(_z1,new T2(1,_z7,_z9));});}));}),_za=function(_zb){var _zc=new T(function(){return B(A1(_z8,_zb));});return new T1(0,function(_zd){return E(_zc);});};return E(_za);};switch(E(_yX)){case 8:if(48>_z5){var _ze=new T(function(){return B(A1(_z1,_Z));});return function(_zf){return new F(function(){return A1(_zf,_ze);});};}else{if(_z5>55){var _zg=new T(function(){return B(A1(_z1,_Z));});return function(_zh){return new F(function(){return A1(_zh,_zg);});};}else{return new F(function(){return _z6(_z5-48|0);});}}break;case 10:if(48>_z5){var _zi=new T(function(){return B(A1(_z1,_Z));});return function(_zj){return new F(function(){return A1(_zj,_zi);});};}else{if(_z5>57){var _zk=new T(function(){return B(A1(_z1,_Z));});return function(_zl){return new F(function(){return A1(_zl,_zk);});};}else{return new F(function(){return _z6(_z5-48|0);});}}break;case 16:if(48>_z5){if(97>_z5){if(65>_z5){var _zm=new T(function(){return B(A1(_z1,_Z));});return function(_zn){return new F(function(){return A1(_zn,_zm);});};}else{if(_z5>70){var _zo=new T(function(){return B(A1(_z1,_Z));});return function(_zp){return new F(function(){return A1(_zp,_zo);});};}else{return new F(function(){return _z6((_z5-65|0)+10|0);});}}}else{if(_z5>102){if(65>_z5){var _zq=new T(function(){return B(A1(_z1,_Z));});return function(_zr){return new F(function(){return A1(_zr,_zq);});};}else{if(_z5>70){var _zs=new T(function(){return B(A1(_z1,_Z));});return function(_zt){return new F(function(){return A1(_zt,_zs);});};}else{return new F(function(){return _z6((_z5-65|0)+10|0);});}}}else{return new F(function(){return _z6((_z5-97|0)+10|0);});}}}else{if(_z5>57){if(97>_z5){if(65>_z5){var _zu=new T(function(){return B(A1(_z1,_Z));});return function(_zv){return new F(function(){return A1(_zv,_zu);});};}else{if(_z5>70){var _zw=new T(function(){return B(A1(_z1,_Z));});return function(_zx){return new F(function(){return A1(_zx,_zw);});};}else{return new F(function(){return _z6((_z5-65|0)+10|0);});}}}else{if(_z5>102){if(65>_z5){var _zy=new T(function(){return B(A1(_z1,_Z));});return function(_zz){return new F(function(){return A1(_zz,_zy);});};}else{if(_z5>70){var _zA=new T(function(){return B(A1(_z1,_Z));});return function(_zB){return new F(function(){return A1(_zB,_zA);});};}else{return new F(function(){return _z6((_z5-65|0)+10|0);});}}}else{return new F(function(){return _z6((_z5-97|0)+10|0);});}}}else{return new F(function(){return _z6(_z5-48|0);});}}break;default:return E(_yV);}}},_zC=function(_zD){var _zE=E(_zD);if(!_zE._){return new T0(2);}else{return new F(function(){return A1(_yY,_zE);});}};return function(_zF){return new F(function(){return A3(_yZ,_zF,_61,_zC);});};},_zG=16,_zH=8,_zI=function(_zJ){var _zK=function(_zL){return new F(function(){return A1(_zJ,new T1(5,new T2(0,_zH,_zL)));});},_zM=function(_zN){return new F(function(){return A1(_zJ,new T1(5,new T2(0,_zG,_zN)));});},_zO=function(_zP){switch(E(_zP)){case 79:return new T1(1,B(_yW(_zH,_zK)));case 88:return new T1(1,B(_yW(_zG,_zM)));case 111:return new T1(1,B(_yW(_zH,_zK)));case 120:return new T1(1,B(_yW(_zG,_zM)));default:return new T0(2);}};return function(_zQ){return (E(_zQ)==48)?E(new T1(0,_zO)):new T0(2);};},_zR=function(_zS){return new T1(0,B(_zI(_zS)));},_zT=function(_zU){return new F(function(){return A1(_zU,_2U);});},_zV=function(_zW){return new F(function(){return A1(_zW,_2U);});},_zX=10,_zY=new T1(0,10),_zZ=function(_A0){return new F(function(){return _eW(E(_A0));});},_A1=new T(function(){return B(unCStr("this should not happen"));}),_A2=new T(function(){return B(err(_A1));}),_A3=function(_A4,_A5){var _A6=E(_A5);if(!_A6._){return __Z;}else{var _A7=E(_A6.b);return (_A7._==0)?E(_A2):new T2(1,B(_gA(B(_sK(_A6.a,_A4)),_A7.a)),new T(function(){return B(_A3(_A4,_A7.b));}));}},_A8=new T1(0,0),_A9=function(_Aa,_Ab,_Ac){while(1){var _Ad=B((function(_Ae,_Af,_Ag){var _Ah=E(_Ag);if(!_Ah._){return E(_A8);}else{if(!E(_Ah.b)._){return E(_Ah.a);}else{var _Ai=E(_Af);if(_Ai<=40){var _Aj=function(_Ak,_Al){while(1){var _Am=E(_Al);if(!_Am._){return E(_Ak);}else{var _An=B(_gA(B(_sK(_Ak,_Ae)),_Am.a));_Ak=_An;_Al=_Am.b;continue;}}};return new F(function(){return _Aj(_A8,_Ah);});}else{var _Ao=B(_sK(_Ae,_Ae));if(!(_Ai%2)){var _Ap=B(_A3(_Ae,_Ah));_Aa=_Ao;_Ab=quot(_Ai+1|0,2);_Ac=_Ap;return __continue;}else{var _Ap=B(_A3(_Ae,new T2(1,_A8,_Ah)));_Aa=_Ao;_Ab=quot(_Ai+1|0,2);_Ac=_Ap;return __continue;}}}}})(_Aa,_Ab,_Ac));if(_Ad!=__continue){return _Ad;}}},_Aq=function(_Ar,_As){return new F(function(){return _A9(_Ar,new T(function(){return B(_qy(_As,0));},1),B(_aj(_zZ,_As)));});},_At=function(_Au){var _Av=new T(function(){var _Aw=new T(function(){var _Ax=function(_Ay){return new F(function(){return A1(_Au,new T1(1,new T(function(){return B(_Aq(_zY,_Ay));})));});};return new T1(1,B(_yW(_zX,_Ax)));}),_Az=function(_AA){if(E(_AA)==43){var _AB=function(_AC){return new F(function(){return A1(_Au,new T1(1,new T(function(){return B(_Aq(_zY,_AC));})));});};return new T1(1,B(_yW(_zX,_AB)));}else{return new T0(2);}},_AD=function(_AE){if(E(_AE)==45){var _AF=function(_AG){return new F(function(){return A1(_Au,new T1(1,new T(function(){return B(_jy(B(_Aq(_zY,_AG))));})));});};return new T1(1,B(_yW(_zX,_AF)));}else{return new T0(2);}};return B(_xh(B(_xh(new T1(0,_AD),new T1(0,_Az))),_Aw));});return new F(function(){return _xh(new T1(0,function(_AH){return (E(_AH)==101)?E(_Av):new T0(2);}),new T1(0,function(_AI){return (E(_AI)==69)?E(_Av):new T0(2);}));});},_AJ=function(_AK){var _AL=function(_AM){return new F(function(){return A1(_AK,new T1(1,_AM));});};return function(_AN){return (E(_AN)==46)?new T1(1,B(_yW(_zX,_AL))):new T0(2);};},_AO=function(_AP){return new T1(0,B(_AJ(_AP)));},_AQ=function(_AR){var _AS=function(_AT){var _AU=function(_AV){return new T1(1,B(_yf(_At,_zT,function(_AW){return new F(function(){return A1(_AR,new T1(5,new T3(1,_AT,_AV,_AW)));});})));};return new T1(1,B(_yf(_AO,_zV,_AU)));};return new F(function(){return _yW(_zX,_AS);});},_AX=function(_AY){return new T1(1,B(_AQ(_AY)));},_AZ=new T(function(){return B(unCStr("!@#$%&*+./<=>?\\^|:-~"));}),_B0=function(_B1){return new F(function(){return _4H(_lc,_B1,_AZ);});},_B2=false,_B3=true,_B4=function(_B5){var _B6=new T(function(){return B(A1(_B5,_zH));}),_B7=new T(function(){return B(A1(_B5,_zG));});return function(_B8){switch(E(_B8)){case 79:return E(_B6);case 88:return E(_B7);case 111:return E(_B6);case 120:return E(_B7);default:return new T0(2);}};},_B9=function(_Ba){return new T1(0,B(_B4(_Ba)));},_Bb=function(_Bc){return new F(function(){return A1(_Bc,_zX);});},_Bd=function(_Be){return new F(function(){return err(B(unAppCStr("Prelude.chr: bad argument: ",new T(function(){return B(_H(9,_Be,_Z));}))));});},_Bf=function(_Bg){return new T0(2);},_Bh=function(_Bi){var _Bj=E(_Bi);if(!_Bj._){return E(_Bf);}else{var _Bk=_Bj.a,_Bl=E(_Bj.b);if(!_Bl._){return E(_Bk);}else{var _Bm=new T(function(){return B(_Bh(_Bl));}),_Bn=function(_Bo){return new F(function(){return _xh(B(A1(_Bk,_Bo)),new T(function(){return B(A1(_Bm,_Bo));}));});};return E(_Bn);}}},_Bp=function(_Bq,_Br){var _Bs=function(_Bt,_Bu,_Bv){var _Bw=E(_Bt);if(!_Bw._){return new F(function(){return A1(_Bv,_Bq);});}else{var _Bx=E(_Bu);if(!_Bx._){return new T0(2);}else{if(E(_Bw.a)!=E(_Bx.a)){return new T0(2);}else{var _By=new T(function(){return B(_Bs(_Bw.b,_Bx.b,_Bv));});return new T1(0,function(_Bz){return E(_By);});}}}};return function(_BA){return new F(function(){return _Bs(_Bq,_BA,_Br);});};},_BB=new T(function(){return B(unCStr("SO"));}),_BC=14,_BD=function(_BE){var _BF=new T(function(){return B(A1(_BE,_BC));});return new T1(1,B(_Bp(_BB,function(_BG){return E(_BF);})));},_BH=new T(function(){return B(unCStr("SOH"));}),_BI=1,_BJ=function(_BK){var _BL=new T(function(){return B(A1(_BK,_BI));});return new T1(1,B(_Bp(_BH,function(_BM){return E(_BL);})));},_BN=function(_BO){return new T1(1,B(_yf(_BJ,_BD,_BO)));},_BP=new T(function(){return B(unCStr("NUL"));}),_BQ=0,_BR=function(_BS){var _BT=new T(function(){return B(A1(_BS,_BQ));});return new T1(1,B(_Bp(_BP,function(_BU){return E(_BT);})));},_BV=new T(function(){return B(unCStr("STX"));}),_BW=2,_BX=function(_BY){var _BZ=new T(function(){return B(A1(_BY,_BW));});return new T1(1,B(_Bp(_BV,function(_C0){return E(_BZ);})));},_C1=new T(function(){return B(unCStr("ETX"));}),_C2=3,_C3=function(_C4){var _C5=new T(function(){return B(A1(_C4,_C2));});return new T1(1,B(_Bp(_C1,function(_C6){return E(_C5);})));},_C7=new T(function(){return B(unCStr("EOT"));}),_C8=4,_C9=function(_Ca){var _Cb=new T(function(){return B(A1(_Ca,_C8));});return new T1(1,B(_Bp(_C7,function(_Cc){return E(_Cb);})));},_Cd=new T(function(){return B(unCStr("ENQ"));}),_Ce=5,_Cf=function(_Cg){var _Ch=new T(function(){return B(A1(_Cg,_Ce));});return new T1(1,B(_Bp(_Cd,function(_Ci){return E(_Ch);})));},_Cj=new T(function(){return B(unCStr("ACK"));}),_Ck=6,_Cl=function(_Cm){var _Cn=new T(function(){return B(A1(_Cm,_Ck));});return new T1(1,B(_Bp(_Cj,function(_Co){return E(_Cn);})));},_Cp=new T(function(){return B(unCStr("BEL"));}),_Cq=7,_Cr=function(_Cs){var _Ct=new T(function(){return B(A1(_Cs,_Cq));});return new T1(1,B(_Bp(_Cp,function(_Cu){return E(_Ct);})));},_Cv=new T(function(){return B(unCStr("BS"));}),_Cw=8,_Cx=function(_Cy){var _Cz=new T(function(){return B(A1(_Cy,_Cw));});return new T1(1,B(_Bp(_Cv,function(_CA){return E(_Cz);})));},_CB=new T(function(){return B(unCStr("HT"));}),_CC=9,_CD=function(_CE){var _CF=new T(function(){return B(A1(_CE,_CC));});return new T1(1,B(_Bp(_CB,function(_CG){return E(_CF);})));},_CH=new T(function(){return B(unCStr("LF"));}),_CI=10,_CJ=function(_CK){var _CL=new T(function(){return B(A1(_CK,_CI));});return new T1(1,B(_Bp(_CH,function(_CM){return E(_CL);})));},_CN=new T(function(){return B(unCStr("VT"));}),_CO=11,_CP=function(_CQ){var _CR=new T(function(){return B(A1(_CQ,_CO));});return new T1(1,B(_Bp(_CN,function(_CS){return E(_CR);})));},_CT=new T(function(){return B(unCStr("FF"));}),_CU=12,_CV=function(_CW){var _CX=new T(function(){return B(A1(_CW,_CU));});return new T1(1,B(_Bp(_CT,function(_CY){return E(_CX);})));},_CZ=new T(function(){return B(unCStr("CR"));}),_D0=13,_D1=function(_D2){var _D3=new T(function(){return B(A1(_D2,_D0));});return new T1(1,B(_Bp(_CZ,function(_D4){return E(_D3);})));},_D5=new T(function(){return B(unCStr("SI"));}),_D6=15,_D7=function(_D8){var _D9=new T(function(){return B(A1(_D8,_D6));});return new T1(1,B(_Bp(_D5,function(_Da){return E(_D9);})));},_Db=new T(function(){return B(unCStr("DLE"));}),_Dc=16,_Dd=function(_De){var _Df=new T(function(){return B(A1(_De,_Dc));});return new T1(1,B(_Bp(_Db,function(_Dg){return E(_Df);})));},_Dh=new T(function(){return B(unCStr("DC1"));}),_Di=17,_Dj=function(_Dk){var _Dl=new T(function(){return B(A1(_Dk,_Di));});return new T1(1,B(_Bp(_Dh,function(_Dm){return E(_Dl);})));},_Dn=new T(function(){return B(unCStr("DC2"));}),_Do=18,_Dp=function(_Dq){var _Dr=new T(function(){return B(A1(_Dq,_Do));});return new T1(1,B(_Bp(_Dn,function(_Ds){return E(_Dr);})));},_Dt=new T(function(){return B(unCStr("DC3"));}),_Du=19,_Dv=function(_Dw){var _Dx=new T(function(){return B(A1(_Dw,_Du));});return new T1(1,B(_Bp(_Dt,function(_Dy){return E(_Dx);})));},_Dz=new T(function(){return B(unCStr("DC4"));}),_DA=20,_DB=function(_DC){var _DD=new T(function(){return B(A1(_DC,_DA));});return new T1(1,B(_Bp(_Dz,function(_DE){return E(_DD);})));},_DF=new T(function(){return B(unCStr("NAK"));}),_DG=21,_DH=function(_DI){var _DJ=new T(function(){return B(A1(_DI,_DG));});return new T1(1,B(_Bp(_DF,function(_DK){return E(_DJ);})));},_DL=new T(function(){return B(unCStr("SYN"));}),_DM=22,_DN=function(_DO){var _DP=new T(function(){return B(A1(_DO,_DM));});return new T1(1,B(_Bp(_DL,function(_DQ){return E(_DP);})));},_DR=new T(function(){return B(unCStr("ETB"));}),_DS=23,_DT=function(_DU){var _DV=new T(function(){return B(A1(_DU,_DS));});return new T1(1,B(_Bp(_DR,function(_DW){return E(_DV);})));},_DX=new T(function(){return B(unCStr("CAN"));}),_DY=24,_DZ=function(_E0){var _E1=new T(function(){return B(A1(_E0,_DY));});return new T1(1,B(_Bp(_DX,function(_E2){return E(_E1);})));},_E3=new T(function(){return B(unCStr("EM"));}),_E4=25,_E5=function(_E6){var _E7=new T(function(){return B(A1(_E6,_E4));});return new T1(1,B(_Bp(_E3,function(_E8){return E(_E7);})));},_E9=new T(function(){return B(unCStr("SUB"));}),_Ea=26,_Eb=function(_Ec){var _Ed=new T(function(){return B(A1(_Ec,_Ea));});return new T1(1,B(_Bp(_E9,function(_Ee){return E(_Ed);})));},_Ef=new T(function(){return B(unCStr("ESC"));}),_Eg=27,_Eh=function(_Ei){var _Ej=new T(function(){return B(A1(_Ei,_Eg));});return new T1(1,B(_Bp(_Ef,function(_Ek){return E(_Ej);})));},_El=new T(function(){return B(unCStr("FS"));}),_Em=28,_En=function(_Eo){var _Ep=new T(function(){return B(A1(_Eo,_Em));});return new T1(1,B(_Bp(_El,function(_Eq){return E(_Ep);})));},_Er=new T(function(){return B(unCStr("GS"));}),_Es=29,_Et=function(_Eu){var _Ev=new T(function(){return B(A1(_Eu,_Es));});return new T1(1,B(_Bp(_Er,function(_Ew){return E(_Ev);})));},_Ex=new T(function(){return B(unCStr("RS"));}),_Ey=30,_Ez=function(_EA){var _EB=new T(function(){return B(A1(_EA,_Ey));});return new T1(1,B(_Bp(_Ex,function(_EC){return E(_EB);})));},_ED=new T(function(){return B(unCStr("US"));}),_EE=31,_EF=function(_EG){var _EH=new T(function(){return B(A1(_EG,_EE));});return new T1(1,B(_Bp(_ED,function(_EI){return E(_EH);})));},_EJ=new T(function(){return B(unCStr("SP"));}),_EK=32,_EL=function(_EM){var _EN=new T(function(){return B(A1(_EM,_EK));});return new T1(1,B(_Bp(_EJ,function(_EO){return E(_EN);})));},_EP=new T(function(){return B(unCStr("DEL"));}),_EQ=127,_ER=function(_ES){var _ET=new T(function(){return B(A1(_ES,_EQ));});return new T1(1,B(_Bp(_EP,function(_EU){return E(_ET);})));},_EV=new T2(1,_ER,_Z),_EW=new T2(1,_EL,_EV),_EX=new T2(1,_EF,_EW),_EY=new T2(1,_Ez,_EX),_EZ=new T2(1,_Et,_EY),_F0=new T2(1,_En,_EZ),_F1=new T2(1,_Eh,_F0),_F2=new T2(1,_Eb,_F1),_F3=new T2(1,_E5,_F2),_F4=new T2(1,_DZ,_F3),_F5=new T2(1,_DT,_F4),_F6=new T2(1,_DN,_F5),_F7=new T2(1,_DH,_F6),_F8=new T2(1,_DB,_F7),_F9=new T2(1,_Dv,_F8),_Fa=new T2(1,_Dp,_F9),_Fb=new T2(1,_Dj,_Fa),_Fc=new T2(1,_Dd,_Fb),_Fd=new T2(1,_D7,_Fc),_Fe=new T2(1,_D1,_Fd),_Ff=new T2(1,_CV,_Fe),_Fg=new T2(1,_CP,_Ff),_Fh=new T2(1,_CJ,_Fg),_Fi=new T2(1,_CD,_Fh),_Fj=new T2(1,_Cx,_Fi),_Fk=new T2(1,_Cr,_Fj),_Fl=new T2(1,_Cl,_Fk),_Fm=new T2(1,_Cf,_Fl),_Fn=new T2(1,_C9,_Fm),_Fo=new T2(1,_C3,_Fn),_Fp=new T2(1,_BX,_Fo),_Fq=new T2(1,_BR,_Fp),_Fr=new T2(1,_BN,_Fq),_Fs=new T(function(){return B(_Bh(_Fr));}),_Ft=34,_Fu=new T1(0,1114111),_Fv=92,_Fw=39,_Fx=function(_Fy){var _Fz=new T(function(){return B(A1(_Fy,_Cq));}),_FA=new T(function(){return B(A1(_Fy,_Cw));}),_FB=new T(function(){return B(A1(_Fy,_CC));}),_FC=new T(function(){return B(A1(_Fy,_CI));}),_FD=new T(function(){return B(A1(_Fy,_CO));}),_FE=new T(function(){return B(A1(_Fy,_CU));}),_FF=new T(function(){return B(A1(_Fy,_D0));}),_FG=new T(function(){return B(A1(_Fy,_Fv));}),_FH=new T(function(){return B(A1(_Fy,_Fw));}),_FI=new T(function(){return B(A1(_Fy,_Ft));}),_FJ=new T(function(){var _FK=function(_FL){var _FM=new T(function(){return B(_eW(E(_FL)));}),_FN=function(_FO){var _FP=B(_Aq(_FM,_FO));if(!B(_iE(_FP,_Fu))){return new T0(2);}else{return new F(function(){return A1(_Fy,new T(function(){var _FQ=B(_ff(_FP));if(_FQ>>>0>1114111){return B(_Bd(_FQ));}else{return _FQ;}}));});}};return new T1(1,B(_yW(_FL,_FN)));},_FR=new T(function(){var _FS=new T(function(){return B(A1(_Fy,_EE));}),_FT=new T(function(){return B(A1(_Fy,_Ey));}),_FU=new T(function(){return B(A1(_Fy,_Es));}),_FV=new T(function(){return B(A1(_Fy,_Em));}),_FW=new T(function(){return B(A1(_Fy,_Eg));}),_FX=new T(function(){return B(A1(_Fy,_Ea));}),_FY=new T(function(){return B(A1(_Fy,_E4));}),_FZ=new T(function(){return B(A1(_Fy,_DY));}),_G0=new T(function(){return B(A1(_Fy,_DS));}),_G1=new T(function(){return B(A1(_Fy,_DM));}),_G2=new T(function(){return B(A1(_Fy,_DG));}),_G3=new T(function(){return B(A1(_Fy,_DA));}),_G4=new T(function(){return B(A1(_Fy,_Du));}),_G5=new T(function(){return B(A1(_Fy,_Do));}),_G6=new T(function(){return B(A1(_Fy,_Di));}),_G7=new T(function(){return B(A1(_Fy,_Dc));}),_G8=new T(function(){return B(A1(_Fy,_D6));}),_G9=new T(function(){return B(A1(_Fy,_BC));}),_Ga=new T(function(){return B(A1(_Fy,_Ck));}),_Gb=new T(function(){return B(A1(_Fy,_Ce));}),_Gc=new T(function(){return B(A1(_Fy,_C8));}),_Gd=new T(function(){return B(A1(_Fy,_C2));}),_Ge=new T(function(){return B(A1(_Fy,_BW));}),_Gf=new T(function(){return B(A1(_Fy,_BI));}),_Gg=new T(function(){return B(A1(_Fy,_BQ));}),_Gh=function(_Gi){switch(E(_Gi)){case 64:return E(_Gg);case 65:return E(_Gf);case 66:return E(_Ge);case 67:return E(_Gd);case 68:return E(_Gc);case 69:return E(_Gb);case 70:return E(_Ga);case 71:return E(_Fz);case 72:return E(_FA);case 73:return E(_FB);case 74:return E(_FC);case 75:return E(_FD);case 76:return E(_FE);case 77:return E(_FF);case 78:return E(_G9);case 79:return E(_G8);case 80:return E(_G7);case 81:return E(_G6);case 82:return E(_G5);case 83:return E(_G4);case 84:return E(_G3);case 85:return E(_G2);case 86:return E(_G1);case 87:return E(_G0);case 88:return E(_FZ);case 89:return E(_FY);case 90:return E(_FX);case 91:return E(_FW);case 92:return E(_FV);case 93:return E(_FU);case 94:return E(_FT);case 95:return E(_FS);default:return new T0(2);}};return B(_xh(new T1(0,function(_Gj){return (E(_Gj)==94)?E(new T1(0,_Gh)):new T0(2);}),new T(function(){return B(A1(_Fs,_Fy));})));});return B(_xh(new T1(1,B(_yf(_B9,_Bb,_FK))),_FR));});return new F(function(){return _xh(new T1(0,function(_Gk){switch(E(_Gk)){case 34:return E(_FI);case 39:return E(_FH);case 92:return E(_FG);case 97:return E(_Fz);case 98:return E(_FA);case 102:return E(_FE);case 110:return E(_FC);case 114:return E(_FF);case 116:return E(_FB);case 118:return E(_FD);default:return new T0(2);}}),_FJ);});},_Gl=function(_Gm){return new F(function(){return A1(_Gm,_kJ);});},_Gn=function(_Go){var _Gp=E(_Go);if(!_Gp._){return E(_Gl);}else{var _Gq=E(_Gp.a),_Gr=_Gq>>>0,_Gs=new T(function(){return B(_Gn(_Gp.b));});if(_Gr>887){var _Gt=u_iswspace(_Gq);if(!E(_Gt)){return E(_Gl);}else{var _Gu=function(_Gv){var _Gw=new T(function(){return B(A1(_Gs,_Gv));});return new T1(0,function(_Gx){return E(_Gw);});};return E(_Gu);}}else{var _Gy=E(_Gr);if(_Gy==32){var _Gz=function(_GA){var _GB=new T(function(){return B(A1(_Gs,_GA));});return new T1(0,function(_GC){return E(_GB);});};return E(_Gz);}else{if(_Gy-9>>>0>4){if(E(_Gy)==160){var _GD=function(_GE){var _GF=new T(function(){return B(A1(_Gs,_GE));});return new T1(0,function(_GG){return E(_GF);});};return E(_GD);}else{return E(_Gl);}}else{var _GH=function(_GI){var _GJ=new T(function(){return B(A1(_Gs,_GI));});return new T1(0,function(_GK){return E(_GJ);});};return E(_GH);}}}}},_GL=function(_GM){var _GN=new T(function(){return B(_GL(_GM));}),_GO=function(_GP){return (E(_GP)==92)?E(_GN):new T0(2);},_GQ=function(_GR){return E(new T1(0,_GO));},_GS=new T1(1,function(_GT){return new F(function(){return A2(_Gn,_GT,_GQ);});}),_GU=new T(function(){return B(_Fx(function(_GV){return new F(function(){return A1(_GM,new T2(0,_GV,_B3));});}));}),_GW=function(_GX){var _GY=E(_GX);if(_GY==38){return E(_GN);}else{var _GZ=_GY>>>0;if(_GZ>887){var _H0=u_iswspace(_GY);return (E(_H0)==0)?new T0(2):E(_GS);}else{var _H1=E(_GZ);return (_H1==32)?E(_GS):(_H1-9>>>0>4)?(E(_H1)==160)?E(_GS):new T0(2):E(_GS);}}};return new F(function(){return _xh(new T1(0,function(_H2){return (E(_H2)==92)?E(new T1(0,_GW)):new T0(2);}),new T1(0,function(_H3){var _H4=E(_H3);if(E(_H4)==92){return E(_GU);}else{return new F(function(){return A1(_GM,new T2(0,_H4,_B2));});}}));});},_H5=function(_H6,_H7){var _H8=new T(function(){return B(A1(_H7,new T1(1,new T(function(){return B(A1(_H6,_Z));}))));}),_H9=function(_Ha){var _Hb=E(_Ha),_Hc=E(_Hb.a);if(E(_Hc)==34){if(!E(_Hb.b)){return E(_H8);}else{return new F(function(){return _H5(function(_Hd){return new F(function(){return A1(_H6,new T2(1,_Hc,_Hd));});},_H7);});}}else{return new F(function(){return _H5(function(_He){return new F(function(){return A1(_H6,new T2(1,_Hc,_He));});},_H7);});}};return new F(function(){return _GL(_H9);});},_Hf=new T(function(){return B(unCStr("_\'"));}),_Hg=function(_Hh){var _Hi=u_iswalnum(_Hh);if(!E(_Hi)){return new F(function(){return _4H(_lc,_Hh,_Hf);});}else{return true;}},_Hj=function(_Hk){return new F(function(){return _Hg(E(_Hk));});},_Hl=new T(function(){return B(unCStr(",;()[]{}`"));}),_Hm=new T(function(){return B(unCStr("=>"));}),_Hn=new T2(1,_Hm,_Z),_Ho=new T(function(){return B(unCStr("~"));}),_Hp=new T2(1,_Ho,_Hn),_Hq=new T(function(){return B(unCStr("@"));}),_Hr=new T2(1,_Hq,_Hp),_Hs=new T(function(){return B(unCStr("->"));}),_Ht=new T2(1,_Hs,_Hr),_Hu=new T(function(){return B(unCStr("<-"));}),_Hv=new T2(1,_Hu,_Ht),_Hw=new T(function(){return B(unCStr("|"));}),_Hx=new T2(1,_Hw,_Hv),_Hy=new T(function(){return B(unCStr("\\"));}),_Hz=new T2(1,_Hy,_Hx),_HA=new T(function(){return B(unCStr("="));}),_HB=new T2(1,_HA,_Hz),_HC=new T(function(){return B(unCStr("::"));}),_HD=new T2(1,_HC,_HB),_HE=new T(function(){return B(unCStr(".."));}),_HF=new T2(1,_HE,_HD),_HG=function(_HH){var _HI=new T(function(){return B(A1(_HH,_yT));}),_HJ=new T(function(){var _HK=new T(function(){var _HL=function(_HM){var _HN=new T(function(){return B(A1(_HH,new T1(0,_HM)));});return new T1(0,function(_HO){return (E(_HO)==39)?E(_HN):new T0(2);});};return B(_Fx(_HL));}),_HP=function(_HQ){var _HR=E(_HQ);switch(E(_HR)){case 39:return new T0(2);case 92:return E(_HK);default:var _HS=new T(function(){return B(A1(_HH,new T1(0,_HR)));});return new T1(0,function(_HT){return (E(_HT)==39)?E(_HS):new T0(2);});}},_HU=new T(function(){var _HV=new T(function(){return B(_H5(_61,_HH));}),_HW=new T(function(){var _HX=new T(function(){var _HY=new T(function(){var _HZ=function(_I0){var _I1=E(_I0),_I2=u_iswalpha(_I1);return (E(_I2)==0)?(E(_I1)==95)?new T1(1,B(_yF(_Hj,function(_I3){return new F(function(){return A1(_HH,new T1(3,new T2(1,_I1,_I3)));});}))):new T0(2):new T1(1,B(_yF(_Hj,function(_I4){return new F(function(){return A1(_HH,new T1(3,new T2(1,_I1,_I4)));});})));};return B(_xh(new T1(0,_HZ),new T(function(){return new T1(1,B(_yf(_zR,_AX,_HH)));})));}),_I5=function(_I6){return (!B(_4H(_lc,_I6,_AZ)))?new T0(2):new T1(1,B(_yF(_B0,function(_I7){var _I8=new T2(1,_I6,_I7);if(!B(_4H(_uJ,_I8,_HF))){return new F(function(){return A1(_HH,new T1(4,_I8));});}else{return new F(function(){return A1(_HH,new T1(2,_I8));});}})));};return B(_xh(new T1(0,_I5),_HY));});return B(_xh(new T1(0,function(_I9){if(!B(_4H(_lc,_I9,_Hl))){return new T0(2);}else{return new F(function(){return A1(_HH,new T1(2,new T2(1,_I9,_Z)));});}}),_HX));});return B(_xh(new T1(0,function(_Ia){return (E(_Ia)==34)?E(_HV):new T0(2);}),_HW));});return B(_xh(new T1(0,function(_Ib){return (E(_Ib)==39)?E(new T1(0,_HP)):new T0(2);}),_HU));});return new F(function(){return _xh(new T1(1,function(_Ic){return (E(_Ic)._==0)?E(_HI):new T0(2);}),_HJ);});},_Id=0,_Ie=function(_If,_Ig){var _Ih=new T(function(){var _Ii=new T(function(){var _Ij=function(_Ik){var _Il=new T(function(){var _Im=new T(function(){return B(A1(_Ig,_Ik));});return B(_HG(function(_In){var _Io=E(_In);return (_Io._==2)?(!B(_vl(_Io.a,_xU)))?new T0(2):E(_Im):new T0(2);}));}),_Ip=function(_Iq){return E(_Il);};return new T1(1,function(_Ir){return new F(function(){return A2(_Gn,_Ir,_Ip);});});};return B(A2(_If,_Id,_Ij));});return B(_HG(function(_Is){var _It=E(_Is);return (_It._==2)?(!B(_vl(_It.a,_xT)))?new T0(2):E(_Ii):new T0(2);}));}),_Iu=function(_Iv){return E(_Ih);};return function(_Iw){return new F(function(){return A2(_Gn,_Iw,_Iu);});};},_Ix=function(_Iy,_Iz){var _IA=function(_IB){var _IC=new T(function(){return B(A1(_Iy,_IB));}),_ID=function(_IE){return new F(function(){return _xh(B(A1(_IC,_IE)),new T(function(){return new T1(1,B(_Ie(_IA,_IE)));}));});};return E(_ID);},_IF=new T(function(){return B(A1(_Iy,_Iz));}),_IG=function(_IH){return new F(function(){return _xh(B(A1(_IF,_IH)),new T(function(){return new T1(1,B(_Ie(_IA,_IH)));}));});};return E(_IG);},_II=0,_IJ=function(_IK,_IL){return new F(function(){return A1(_IL,_II);});},_IM=new T(function(){return B(unCStr("Fr"));}),_IN=new T2(0,_IM,_IJ),_IO=1,_IP=function(_IQ,_IR){return new F(function(){return A1(_IR,_IO);});},_IS=new T(function(){return B(unCStr("Bl"));}),_IT=new T2(0,_IS,_IP),_IU=2,_IV=function(_IW,_IX){return new F(function(){return A1(_IX,_IU);});},_IY=new T(function(){return B(unCStr("Ex"));}),_IZ=new T2(0,_IY,_IV),_J0=3,_J1=function(_J2,_J3){return new F(function(){return A1(_J3,_J0);});},_J4=new T(function(){return B(unCStr("Mv"));}),_J5=new T2(0,_J4,_J1),_J6=4,_J7=function(_J8,_J9){return new F(function(){return A1(_J9,_J6);});},_Ja=new T(function(){return B(unCStr("Pn"));}),_Jb=new T2(0,_Ja,_J7),_Jc=8,_Jd=function(_Je,_Jf){return new F(function(){return A1(_Jf,_Jc);});},_Jg=new T(function(){return B(unCStr("DF"));}),_Jh=new T2(0,_Jg,_Jd),_Ji=new T2(1,_Jh,_Z),_Jj=7,_Jk=function(_Jl,_Jm){return new F(function(){return A1(_Jm,_Jj);});},_Jn=new T(function(){return B(unCStr("DB"));}),_Jo=new T2(0,_Jn,_Jk),_Jp=new T2(1,_Jo,_Ji),_Jq=6,_Jr=function(_Js,_Jt){return new F(function(){return A1(_Jt,_Jq);});},_Ju=new T(function(){return B(unCStr("Cm"));}),_Jv=new T2(0,_Ju,_Jr),_Jw=new T2(1,_Jv,_Jp),_Jx=5,_Jy=function(_Jz,_JA){return new F(function(){return A1(_JA,_Jx);});},_JB=new T(function(){return B(unCStr("Wn"));}),_JC=new T2(0,_JB,_Jy),_JD=new T2(1,_JC,_Jw),_JE=new T2(1,_Jb,_JD),_JF=new T2(1,_J5,_JE),_JG=new T2(1,_IZ,_JF),_JH=new T2(1,_IT,_JG),_JI=new T2(1,_IN,_JH),_JJ=function(_JK,_JL,_JM){var _JN=E(_JK);if(!_JN._){return new T0(2);}else{var _JO=E(_JN.a),_JP=_JO.a,_JQ=new T(function(){return B(A2(_JO.b,_JL,_JM));}),_JR=new T(function(){return B(_HG(function(_JS){var _JT=E(_JS);switch(_JT._){case 3:return (!B(_vl(_JP,_JT.a)))?new T0(2):E(_JQ);case 4:return (!B(_vl(_JP,_JT.a)))?new T0(2):E(_JQ);default:return new T0(2);}}));}),_JU=function(_JV){return E(_JR);};return new F(function(){return _xh(new T1(1,function(_JW){return new F(function(){return A2(_Gn,_JW,_JU);});}),new T(function(){return B(_JJ(_JN.b,_JL,_JM));}));});}},_JX=function(_JY,_JZ){return new F(function(){return _JJ(_JI,_JY,_JZ);});},_K0=function(_K1){var _K2=function(_K3){return E(new T2(3,_K1,_y6));};return new T1(1,function(_K4){return new F(function(){return A2(_Gn,_K4,_K2);});});},_K5=new T(function(){return B(A3(_Ix,_JX,_Id,_K0));}),_K6=new T(function(){return B(err(_wY));}),_K7=new T(function(){return B(err(_x2));}),_K8=function(_K9,_Ka){var _Kb=function(_Kc,_Kd){var _Ke=function(_Kf){return new F(function(){return A1(_Kd,new T(function(){return  -E(_Kf);}));});},_Kg=new T(function(){return B(_HG(function(_Kh){return new F(function(){return A3(_K9,_Kh,_Kc,_Ke);});}));}),_Ki=function(_Kj){return E(_Kg);},_Kk=function(_Kl){return new F(function(){return A2(_Gn,_Kl,_Ki);});},_Km=new T(function(){return B(_HG(function(_Kn){var _Ko=E(_Kn);if(_Ko._==4){var _Kp=E(_Ko.a);if(!_Kp._){return new F(function(){return A3(_K9,_Ko,_Kc,_Kd);});}else{if(E(_Kp.a)==45){if(!E(_Kp.b)._){return E(new T1(1,_Kk));}else{return new F(function(){return A3(_K9,_Ko,_Kc,_Kd);});}}else{return new F(function(){return A3(_K9,_Ko,_Kc,_Kd);});}}}else{return new F(function(){return A3(_K9,_Ko,_Kc,_Kd);});}}));}),_Kq=function(_Kr){return E(_Km);};return new T1(1,function(_Ks){return new F(function(){return A2(_Gn,_Ks,_Kq);});});};return new F(function(){return _Ix(_Kb,_Ka);});},_Kt=function(_Ku){var _Kv=E(_Ku);if(!_Kv._){var _Kw=_Kv.b,_Kx=new T(function(){return B(_A9(new T(function(){return B(_eW(E(_Kv.a)));}),new T(function(){return B(_qy(_Kw,0));},1),B(_aj(_zZ,_Kw))));});return new T1(1,_Kx);}else{return (E(_Kv.b)._==0)?(E(_Kv.c)._==0)?new T1(1,new T(function(){return B(_Aq(_zY,_Kv.a));})):__Z:__Z;}},_Ky=function(_Kz,_KA){return new T0(2);},_KB=function(_KC){var _KD=E(_KC);if(_KD._==5){var _KE=B(_Kt(_KD.a));if(!_KE._){return E(_Ky);}else{var _KF=new T(function(){return B(_ff(_KE.a));});return function(_KG,_KH){return new F(function(){return A1(_KH,_KF);});};}}else{return E(_Ky);}},_KI=new T(function(){return B(A3(_K8,_KB,_Id,_K0));}),_KJ=new T2(1,_F,_Z),_KK=function(_KL){while(1){var _KM=B((function(_KN){var _KO=E(_KN);if(!_KO._){return __Z;}else{var _KP=_KO.b,_KQ=E(_KO.a);if(!E(_KQ.b)._){return new T2(1,_KQ.a,new T(function(){return B(_KK(_KP));}));}else{_KL=_KP;return __continue;}}})(_KL));if(_KM!=__continue){return _KM;}}},_KR=function(_KS,_KT){while(1){var _KU=E(_KS);if(!_KU._){return E(_KT);}else{var _KV=new T2(1,_KU.a,_KT);_KS=_KU.b;_KT=_KV;continue;}}},_KW=function(_KX,_KY){var _KZ=E(_KX);if(!_KZ._){return __Z;}else{var _L0=E(_KY);return (_L0._==0)?__Z:new T2(1,new T2(0,_KZ.a,_L0.a),new T(function(){return B(_KW(_KZ.b,_L0.b));}));}},_L1=function(_L2,_L3,_L4){while(1){var _L5=B((function(_L6,_L7,_L8){var _L9=E(_L8);if(!_L9._){return E(_L7);}else{var _La=_L9.a,_Lb=_L9.b,_Lc=B(_wS(_uJ,_La,_wH));if(!_Lc._){var _Ld=E(_x5);}else{var _Ld=E(_Lc.a);}if(!B(_vq(_Ld,_x5))){var _Le=B(_KR(B(_KW(B(_KR(_L7,_Z)),new T(function(){return B(_KR(_Ld,_Z));},1))),_Z)),_Lf=B(_qy(_Le,0)),_Lg=new T(function(){var _Lh=B(_aj(_wQ,_Le));if(!_Lh._){return __Z;}else{var _Li=_Lh.a,_Lj=E(_Lh.b);if(!_Lj._){return __Z;}else{var _Lk=_Lj.a;if(!E(_Lj.b)._){if(!B(_vl(_La,_wj))){if(!B(_vl(_La,_wi))){if(!B(_vl(_La,_wh))){if(!B(_vl(_La,_wl))){if(!B(_vl(_La,_wk))){return __Z;}else{if(!B(_vl(_Li,_x0))){if(!B(_vl(_Lk,_x0))){return E(_x1);}else{return E(_x0);}}else{return E(_x0);}}}else{var _Ll=B(_w5(new T2(0,new T(function(){var _Lm=E(_Li);if(!_Lm._){return E(_rm);}else{return E(_Lm.a);}}),new T(function(){var _Ln=B(_KK(B(_x7(_K5,_Lk))));if(!_Ln._){return E(_wZ);}else{if(!E(_Ln.b)._){return E(_Ln.a);}else{return E(_x3);}}})),E(E(_L6).a).b)),_Lo=new T(function(){return B(A3(_wK,_aC,new T2(1,function(_Lp){return new F(function(){return _H(0,E(_Ll.a),_Lp);});},new T2(1,function(_Lq){return new F(function(){return _H(0,E(_Ll.b),_Lq);});},_Z)),_KJ));});return new T2(1,_G,_Lo);}}else{return new T2(1,new T(function(){var _Lr=B(_KK(B(_x7(_KI,_Li))));if(!_Lr._){return E(_K6);}else{if(!E(_Lr.b)._){var _Ls=B(_KK(B(_x7(_KI,_Lk))));if(!_Ls._){return E(_K6);}else{if(!E(_Ls.b)._){return E(B(_aW(B(_aW(E(E(_L6).a).b,E(_Ls.a))),E(_Lr.a))).a);}else{return E(_K7);}}}else{return E(_K7);}}}),_Z);}}else{if(!B(_vl(_Li,_Lk))){return E(_x1);}else{return E(_x0);}}}else{if(!B(_vl(_Li,_x0))){return E(_x1);}else{if(!B(_vl(_Lk,_x0))){return E(_x1);}else{return E(_x0);}}}}else{return __Z;}}}});if(_Lf>0){var _Lt=_L6,_Lu=B(_x(B(_KR(B(_wb(_Lf,B(_KR(_L7,_Z)))),_Z)),new T2(1,_Lg,_Z)));_L2=_Lt;_L3=_Lu;_L4=_Lb;return __continue;}else{var _Lt=_L6,_Lu=B(_x(B(_KR(B(_KR(_L7,_Z)),_Z)),new T2(1,_Lg,_Z)));_L2=_Lt;_L3=_Lu;_L4=_Lb;return __continue;}}else{var _Lt=_L6,_Lu=B(_x(_L7,new T2(1,_La,_Z)));_L2=_Lt;_L3=_Lu;_L4=_Lb;return __continue;}}})(_L2,_L3,_L4));if(_L5!=__continue){return _L5;}}},_Lv=new T(function(){return B(_ic("Event.hs:(102,1)-(106,73)|function addMemory"));}),_Lw=function(_Lx,_Ly){var _Lz=E(_Lx),_LA=E(_Ly);if(!B(_vl(_Lz.a,_LA.a))){return false;}else{return new F(function(){return _vl(_Lz.b,_LA.b);});}},_LB=new T2(1,_Z,_Z),_LC=function(_LD,_LE,_LF){var _LG=E(_LF);if(!_LG._){return new T2(0,new T2(1,_LE,_Z),_Z);}else{var _LH=E(_LE),_LI=new T(function(){var _LJ=B(_LC(_LD,_LG.a,_LG.b));return new T2(0,_LJ.a,_LJ.b);});return (_LD!=_LH)?new T2(0,new T2(1,_LH,new T(function(){return E(E(_LI).a);})),new T(function(){return E(E(_LI).b);})):new T2(0,_Z,new T2(1,new T(function(){return E(E(_LI).a);}),new T(function(){return E(E(_LI).b);})));}},_LK=32,_LL=function(_LM){var _LN=E(_LM);if(!_LN._){return __Z;}else{var _LO=new T(function(){return B(_x(_LN.a,new T(function(){return B(_LL(_LN.b));},1)));});return new T2(1,_LK,_LO);}},_LP=function(_LQ,_LR,_LS,_LT,_LU,_LV,_LW,_LX,_LY,_LZ,_M0,_M1,_M2,_M3,_M4,_M5,_M6,_M7,_M8,_M9,_Ma,_Mb,_Mc){while(1){var _Md=B((function(_Me,_Mf,_Mg,_Mh,_Mi,_Mj,_Mk,_Ml,_Mm,_Mn,_Mo,_Mp,_Mq,_Mr,_Ms,_Mt,_Mu,_Mv,_Mw,_Mx,_My,_Mz,_MA){var _MB=E(_Me);if(!_MB._){return {_:0,a:_Mf,b:_Mg,c:_Mh,d:_Mi,e:_Mj,f:_Mk,g:_Ml,h:_Mm,i:_Mn,j:_Mo,k:_Mp,l:_Mq,m:_Mr,n:_Ms,o:_Mt,p:_Mu,q:_Mv,r:_Mw,s:_Mx,t:_My,u:_Mz,v:_MA};}else{var _MC=_MB.a,_MD=E(_MB.b);if(!_MD._){return E(_Lv);}else{var _ME=new T(function(){var _MF=E(_MD.a);if(!_MF._){var _MG=B(_L1({_:0,a:E(_Mf),b:E(_Mg),c:E(_Mh),d:E(_Mi),e:E(_Mj),f:E(_Mk),g:E(_Ml),h:E(_Mm),i:_Mn,j:_Mo,k:_Mp,l:_Mq,m:E(_Mr),n:_Ms,o:E(_Mt),p:E(_Mu),q:_Mv,r:E(_Mw),s:E(_Mx),t:_My,u:E(_Mz),v:E(_MA)},_Z,_LB));if(!_MG._){return __Z;}else{return B(_x(_MG.a,new T(function(){return B(_LL(_MG.b));},1)));}}else{var _MH=_MF.a,_MI=E(_MF.b);if(!_MI._){var _MJ=B(_L1({_:0,a:E(_Mf),b:E(_Mg),c:E(_Mh),d:E(_Mi),e:E(_Mj),f:E(_Mk),g:E(_Ml),h:E(_Mm),i:_Mn,j:_Mo,k:_Mp,l:_Mq,m:E(_Mr),n:_Ms,o:E(_Mt),p:E(_Mu),q:_Mv,r:E(_Mw),s:E(_Mx),t:_My,u:E(_Mz),v:E(_MA)},_Z,new T2(1,new T2(1,_MH,_Z),_Z)));if(!_MJ._){return __Z;}else{return B(_x(_MJ.a,new T(function(){return B(_LL(_MJ.b));},1)));}}else{var _MK=E(_MH),_ML=new T(function(){var _MM=B(_LC(95,_MI.a,_MI.b));return new T2(0,_MM.a,_MM.b);});if(E(_MK)==95){var _MN=B(_L1({_:0,a:E(_Mf),b:E(_Mg),c:E(_Mh),d:E(_Mi),e:E(_Mj),f:E(_Mk),g:E(_Ml),h:E(_Mm),i:_Mn,j:_Mo,k:_Mp,l:_Mq,m:E(_Mr),n:_Ms,o:E(_Mt),p:E(_Mu),q:_Mv,r:E(_Mw),s:E(_Mx),t:_My,u:E(_Mz),v:E(_MA)},_Z,new T2(1,_Z,new T2(1,new T(function(){return E(E(_ML).a);}),new T(function(){return E(E(_ML).b);})))));if(!_MN._){return __Z;}else{return B(_x(_MN.a,new T(function(){return B(_LL(_MN.b));},1)));}}else{var _MO=B(_L1({_:0,a:E(_Mf),b:E(_Mg),c:E(_Mh),d:E(_Mi),e:E(_Mj),f:E(_Mk),g:E(_Ml),h:E(_Mm),i:_Mn,j:_Mo,k:_Mp,l:_Mq,m:E(_Mr),n:_Ms,o:E(_Mt),p:E(_Mu),q:_Mv,r:E(_Mw),s:E(_Mx),t:_My,u:E(_Mz),v:E(_MA)},_Z,new T2(1,new T2(1,_MK,new T(function(){return E(E(_ML).a);})),new T(function(){return E(E(_ML).b);}))));if(!_MO._){return __Z;}else{return B(_x(_MO.a,new T(function(){return B(_LL(_MO.b));},1)));}}}}}),_MP=_Mf,_MQ=_Mg,_MR=_Mh,_MS=_Mi,_MT=_Mj,_MU=_Mk,_MV=_Mm,_MW=_Mn,_MX=_Mo,_MY=_Mp,_MZ=_Mq,_N0=_Mr,_N1=_Ms,_N2=_Mt,_N3=_Mu,_N4=_Mv,_N5=_Mw,_N6=_Mx,_N7=_My,_N8=_Mz,_N9=_MA;_LQ=_MD.b;_LR=_MP;_LS=_MQ;_LT=_MR;_LU=_MS;_LV=_MT;_LW=_MU;_LX=new T2(1,new T2(0,_MC,_ME),new T(function(){var _Na=B(_wS(_uJ,_MC,_Ml));if(!_Na._){var _Nb=__Z;}else{var _Nb=E(_Na.a);}if(!B(_vl(_Nb,_Z))){return B(_ve(_Lw,new T2(0,_MC,_Nb),_Ml));}else{return E(_Ml);}}));_LY=_MV;_LZ=_MW;_M0=_MX;_M1=_MY;_M2=_MZ;_M3=_N0;_M4=_N1;_M5=_N2;_M6=_N3;_M7=_N4;_M8=_N5;_M9=_N6;_Ma=_N7;_Mb=_N8;_Mc=_N9;return __continue;}}})(_LQ,_LR,_LS,_LT,_LU,_LV,_LW,_LX,_LY,_LZ,_M0,_M1,_M2,_M3,_M4,_M5,_M6,_M7,_M8,_M9,_Ma,_Mb,_Mc));if(_Md!=__continue){return _Md;}}},_Nc=function(_Nd){var _Ne=E(_Nd);if(!_Ne._){return new T2(0,_Z,_Z);}else{var _Nf=E(_Ne.a),_Ng=new T(function(){var _Nh=B(_Nc(_Ne.b));return new T2(0,_Nh.a,_Nh.b);});return new T2(0,new T2(1,_Nf.a,new T(function(){return E(E(_Ng).a);})),new T2(1,_Nf.b,new T(function(){return E(E(_Ng).b);})));}},_Ni=function(_Nj,_Nk,_Nl){while(1){var _Nm=B((function(_Nn,_No,_Np){var _Nq=E(_Np);if(!_Nq._){return __Z;}else{var _Nr=_Nq.b;if(_No!=E(_Nq.a)){var _Ns=_Nn+1|0,_Nt=_No;_Nj=_Ns;_Nk=_Nt;_Nl=_Nr;return __continue;}else{return new T2(1,_Nn,new T(function(){return B(_Ni(_Nn+1|0,_No,_Nr));}));}}})(_Nj,_Nk,_Nl));if(_Nm!=__continue){return _Nm;}}},_Nu=function(_Nv,_Nw,_Nx){var _Ny=E(_Nx);if(!_Ny._){return __Z;}else{var _Nz=_Ny.b,_NA=E(_Nw);if(_NA!=E(_Ny.a)){return new F(function(){return _Ni(_Nv+1|0,_NA,_Nz);});}else{return new T2(1,_Nv,new T(function(){return B(_Ni(_Nv+1|0,_NA,_Nz));}));}}},_NB=function(_NC,_ND,_NE,_NF){var _NG=E(_NF);if(!_NG._){return __Z;}else{var _NH=_NG.b;return (!B(_4H(_3S,_NC,_NE)))?new T2(1,_NG.a,new T(function(){return B(_NB(_NC+1|0,_ND,_NE,_NH));})):new T2(1,_ND,new T(function(){return B(_NB(_NC+1|0,_ND,_NE,_NH));}));}},_NI=function(_NJ,_NK,_NL){var _NM=E(_NL);if(!_NM._){return __Z;}else{var _NN=new T(function(){var _NO=B(_Nc(_NM.a)),_NP=_NO.a,_NQ=new T(function(){return B(_NB(0,_NK,new T(function(){return B(_Nu(0,_NJ,_NP));}),_NO.b));},1);return B(_KW(_NP,_NQ));});return new T2(1,_NN,new T(function(){return B(_NI(_NJ,_NK,_NM.b));}));}},_NR=function(_NS){var _NT=E(_NS);return (_NT._==0)?E(_rm):E(_NT.a);},_NU=new T(function(){return B(_ic("Event.hs:(75,1)-(78,93)|function changeType"));}),_NV=new T(function(){return B(_ic("Event.hs:72:16-116|case"));}),_NW=new T(function(){return B(unCStr("Wn"));}),_NX=new T(function(){return B(unCStr("Pn"));}),_NY=new T(function(){return B(unCStr("Mv"));}),_NZ=new T(function(){return B(unCStr("Fr"));}),_O0=new T(function(){return B(unCStr("Ex"));}),_O1=new T(function(){return B(unCStr("DF"));}),_O2=new T(function(){return B(unCStr("DB"));}),_O3=new T(function(){return B(unCStr("Cm"));}),_O4=new T(function(){return B(unCStr("Bl"));}),_O5=function(_O6){return (!B(_vl(_O6,_O4)))?(!B(_vl(_O6,_O3)))?(!B(_vl(_O6,_O2)))?(!B(_vl(_O6,_O1)))?(!B(_vl(_O6,_O0)))?(!B(_vl(_O6,_NZ)))?(!B(_vl(_O6,_NY)))?(!B(_vl(_O6,_NX)))?(!B(_vl(_O6,_NW)))?E(_NV):5:4:3:0:2:8:7:6:1;},_O7=function(_O8,_O9,_Oa,_Ob,_Oc,_Od,_Oe,_Of,_Og,_Oh,_Oi,_Oj,_Ok,_Ol,_Om,_On,_Oo,_Op,_Oq,_Or,_Os,_Ot,_Ou){while(1){var _Ov=B((function(_Ow,_Ox,_Oy,_Oz,_OA,_OB,_OC,_OD,_OE,_OF,_OG,_OH,_OI,_OJ,_OK,_OL,_OM,_ON,_OO,_OP,_OQ,_OR,_OS){var _OT=E(_Ow);if(!_OT._){return {_:0,a:_Ox,b:_Oy,c:_Oz,d:_OA,e:_OB,f:_OC,g:_OD,h:_OE,i:_OF,j:_OG,k:_OH,l:_OI,m:_OJ,n:_OK,o:_OL,p:_OM,q:_ON,r:_OO,s:_OP,t:_OQ,u:_OR,v:_OS};}else{var _OU=E(_OT.b);if(!_OU._){return E(_NU);}else{var _OV=E(_Ox),_OW=_Oy,_OX=_Oz,_OY=_OA,_OZ=_OB,_P0=_OC,_P1=_OD,_P2=_OE,_P3=_OF,_P4=_OG,_P5=_OH,_P6=_OI,_P7=_OJ,_P8=_OK,_P9=_OL,_Pa=_OM,_Pb=_ON,_Pc=_OO,_Pd=_OP,_Pe=_OQ,_Pf=_OR,_Pg=_OS;_O8=_OU.b;_O9={_:0,a:E(_OV.a),b:E(B(_NI(new T(function(){return B(_NR(_OT.a));}),new T(function(){return B(_O5(_OU.a));}),_OV.b))),c:E(_OV.c),d:_OV.d,e:_OV.e,f:_OV.f,g:E(_OV.g),h:_OV.h,i:E(_OV.i),j:E(_OV.j),k:E(_OV.k)};_Oa=_OW;_Ob=_OX;_Oc=_OY;_Od=_OZ;_Oe=_P0;_Of=_P1;_Og=_P2;_Oh=_P3;_Oi=_P4;_Oj=_P5;_Ok=_P6;_Ol=_P7;_Om=_P8;_On=_P9;_Oo=_Pa;_Op=_Pb;_Oq=_Pc;_Or=_Pd;_Os=_Pe;_Ot=_Pf;_Ou=_Pg;return __continue;}}})(_O8,_O9,_Oa,_Ob,_Oc,_Od,_Oe,_Of,_Og,_Oh,_Oi,_Oj,_Ok,_Ol,_Om,_On,_Oo,_Op,_Oq,_Or,_Os,_Ot,_Ou));if(_Ov!=__continue){return _Ov;}}},_Ph=function(_Pi,_Pj){while(1){var _Pk=E(_Pj);if(!_Pk._){return __Z;}else{var _Pl=_Pk.b,_Pm=E(_Pi);if(_Pm==1){return E(_Pl);}else{_Pi=_Pm-1|0;_Pj=_Pl;continue;}}}},_Pn=function(_Po,_Pp){while(1){var _Pq=E(_Pp);if(!_Pq._){return __Z;}else{var _Pr=_Pq.b,_Ps=E(_Po);if(_Ps==1){return E(_Pr);}else{_Po=_Ps-1|0;_Pp=_Pr;continue;}}}},_Pt=function(_Pu,_Pv,_Pw,_Px,_Py){var _Pz=new T(function(){var _PA=E(_Pu),_PB=new T(function(){return B(_aW(_Py,_Pv));}),_PC=new T2(1,new T2(0,_Pw,_Px),new T(function(){var _PD=_PA+1|0;if(_PD>0){return B(_Pn(_PD,_PB));}else{return E(_PB);}}));if(0>=_PA){return E(_PC);}else{var _PE=function(_PF,_PG){var _PH=E(_PF);if(!_PH._){return E(_PC);}else{var _PI=_PH.a,_PJ=E(_PG);return (_PJ==1)?new T2(1,_PI,_PC):new T2(1,_PI,new T(function(){return B(_PE(_PH.b,_PJ-1|0));}));}};return B(_PE(_PB,_PA));}}),_PK=new T2(1,_Pz,new T(function(){var _PL=_Pv+1|0;if(_PL>0){return B(_Ph(_PL,_Py));}else{return E(_Py);}}));if(0>=_Pv){return E(_PK);}else{var _PM=function(_PN,_PO){var _PP=E(_PN);if(!_PP._){return E(_PK);}else{var _PQ=_PP.a,_PR=E(_PO);return (_PR==1)?new T2(1,_PQ,_PK):new T2(1,_PQ,new T(function(){return B(_PM(_PP.b,_PR-1|0));}));}};return new F(function(){return _PM(_Py,_Pv);});}},_PS=32,_PT=new T(function(){return B(unCStr("Irrefutable pattern failed for pattern"));}),_PU=function(_PV){return new F(function(){return _hO(new T1(0,new T(function(){return B(_i1(_PV,_PT));})),_hy);});},_PW=function(_PX){return new F(function(){return _PU("Event.hs:58:27-53|(x\' : y\' : _)");});},_PY=new T(function(){return B(_PW(_));}),_PZ=function(_Q0,_Q1,_Q2,_Q3,_Q4,_Q5,_Q6,_Q7,_Q8,_Q9,_Qa,_Qb,_Qc,_Qd,_Qe,_Qf,_Qg,_Qh,_Qi,_Qj,_Qk,_Ql,_Qm){while(1){var _Qn=B((function(_Qo,_Qp,_Qq,_Qr,_Qs,_Qt,_Qu,_Qv,_Qw,_Qx,_Qy,_Qz,_QA,_QB,_QC,_QD,_QE,_QF,_QG,_QH,_QI,_QJ,_QK){var _QL=E(_Qo);if(!_QL._){return {_:0,a:_Qp,b:_Qq,c:_Qr,d:_Qs,e:_Qt,f:_Qu,g:_Qv,h:_Qw,i:_Qx,j:_Qy,k:_Qz,l:_QA,m:_QB,n:_QC,o:_QD,p:_QE,q:_QF,r:_QG,s:_QH,t:_QI,u:_QJ,v:_QK};}else{var _QM=E(_Qp),_QN=new T(function(){var _QO=E(_QL.a);if(!_QO._){return E(_PY);}else{var _QP=E(_QO.b);if(!_QP._){return E(_PY);}else{var _QQ=_QP.a,_QR=_QP.b,_QS=E(_QO.a);if(E(_QS)==44){return new T2(0,_Z,new T(function(){return E(B(_LC(44,_QQ,_QR)).a);}));}else{var _QT=B(_LC(44,_QQ,_QR)),_QU=E(_QT.b);if(!_QU._){return E(_PY);}else{return new T2(0,new T2(1,_QS,_QT.a),_QU.a);}}}}}),_QV=B(_KK(B(_x7(_KI,new T(function(){return E(E(_QN).b);})))));if(!_QV._){return E(_K6);}else{if(!E(_QV.b)._){var _QW=new T(function(){var _QX=B(_KK(B(_x7(_KI,new T(function(){return E(E(_QN).a);})))));if(!_QX._){return E(_K6);}else{if(!E(_QX.b)._){return E(_QX.a);}else{return E(_K7);}}},1),_QY=_Qq,_QZ=_Qr,_R0=_Qs,_R1=_Qt,_R2=_Qu,_R3=_Qv,_R4=_Qw,_R5=_Qx,_R6=_Qy,_R7=_Qz,_R8=_QA,_R9=_QB,_Ra=_QC,_Rb=_QD,_Rc=_QE,_Rd=_QF,_Re=_QG,_Rf=_QH,_Rg=_QI,_Rh=_QJ,_Ri=_QK;_Q0=_QL.b;_Q1={_:0,a:E(_QM.a),b:E(B(_Pt(_QW,E(_QV.a),_PS,_II,_QM.b))),c:E(_QM.c),d:_QM.d,e:_QM.e,f:_QM.f,g:E(_QM.g),h:_QM.h,i:E(_QM.i),j:E(_QM.j),k:E(_QM.k)};_Q2=_QY;_Q3=_QZ;_Q4=_R0;_Q5=_R1;_Q6=_R2;_Q7=_R3;_Q8=_R4;_Q9=_R5;_Qa=_R6;_Qb=_R7;_Qc=_R8;_Qd=_R9;_Qe=_Ra;_Qf=_Rb;_Qg=_Rc;_Qh=_Rd;_Qi=_Re;_Qj=_Rf;_Qk=_Rg;_Ql=_Rh;_Qm=_Ri;return __continue;}else{return E(_K7);}}}})(_Q0,_Q1,_Q2,_Q3,_Q4,_Q5,_Q6,_Q7,_Q8,_Q9,_Qa,_Qb,_Qc,_Qd,_Qe,_Qf,_Qg,_Qh,_Qi,_Qj,_Qk,_Ql,_Qm));if(_Qn!=__continue){return _Qn;}}},_Rj=function(_Rk,_Rl,_Rm){var _Rn=E(_Rm);return (_Rn._==0)?0:(!B(A3(_4F,_Rk,_Rl,_Rn.a)))?1+B(_Rj(_Rk,_Rl,_Rn.b))|0:0;},_Ro=function(_Rp,_Rq){while(1){var _Rr=E(_Rq);if(!_Rr._){return __Z;}else{var _Rs=_Rr.b,_Rt=E(_Rp);if(_Rt==1){return E(_Rs);}else{_Rp=_Rt-1|0;_Rq=_Rs;continue;}}}},_Ru=function(_Rv,_Rw){var _Rx=new T(function(){var _Ry=_Rv+1|0;if(_Ry>0){return B(_Ro(_Ry,_Rw));}else{return E(_Rw);}});if(0>=_Rv){return E(_Rx);}else{var _Rz=function(_RA,_RB){var _RC=E(_RA);if(!_RC._){return E(_Rx);}else{var _RD=_RC.a,_RE=E(_RB);return (_RE==1)?new T2(1,_RD,_Rx):new T2(1,_RD,new T(function(){return B(_Rz(_RC.b,_RE-1|0));}));}};return new F(function(){return _Rz(_Rw,_Rv);});}},_RF=function(_RG,_RH){return new F(function(){return _Ru(E(_RG),_RH);});},_RI= -1,_RJ=function(_RK,_RL,_RM,_RN,_RO,_RP,_RQ,_RR,_RS,_RT,_RU,_RV,_RW,_RX,_RY,_RZ,_S0,_S1,_S2,_S3,_S4,_S5,_S6){while(1){var _S7=B((function(_S8,_S9,_Sa,_Sb,_Sc,_Sd,_Se,_Sf,_Sg,_Sh,_Si,_Sj,_Sk,_Sl,_Sm,_Sn,_So,_Sp,_Sq,_Sr,_Ss,_St,_Su){var _Sv=E(_S8);if(!_Sv._){return {_:0,a:_S9,b:_Sa,c:_Sb,d:_Sc,e:_Sd,f:_Se,g:_Sf,h:_Sg,i:_Sh,j:_Si,k:_Sj,l:_Sk,m:_Sl,n:_Sm,o:_Sn,p:_So,q:_Sp,r:_Sq,s:_Sr,t:_Ss,u:_St,v:_Su};}else{var _Sw=_Sv.a,_Sx=B(_aj(_wQ,_Sd)),_Sy=B(_4H(_uJ,_Sw,_Sx)),_Sz=new T(function(){if(!E(_Sy)){return E(_RI);}else{return B(_Rj(_uJ,_Sw,_Sx));}});if(!E(_Sy)){var _SA=E(_Sd);}else{var _SA=B(_RF(_Sz,_Sd));}if(!E(_Sy)){var _SB=E(_Se);}else{var _SB=B(_RF(_Sz,_Se));}var _SC=_S9,_SD=_Sa,_SE=_Sb,_SF=_Sc,_SG=_Sf,_SH=_Sg,_SI=_Sh,_SJ=_Si,_SK=_Sj,_SL=_Sk,_SM=_Sl,_SN=_Sm,_SO=_Sn,_SP=_So,_SQ=_Sp,_SR=_Sq,_SS=_Sr,_ST=_Ss,_SU=_St,_SV=_Su;_RK=_Sv.b;_RL=_SC;_RM=_SD;_RN=_SE;_RO=_SF;_RP=_SA;_RQ=_SB;_RR=_SG;_RS=_SH;_RT=_SI;_RU=_SJ;_RV=_SK;_RW=_SL;_RX=_SM;_RY=_SN;_RZ=_SO;_S0=_SP;_S1=_SQ;_S2=_SR;_S3=_SS;_S4=_ST;_S5=_SU;_S6=_SV;return __continue;}})(_RK,_RL,_RM,_RN,_RO,_RP,_RQ,_RR,_RS,_RT,_RU,_RV,_RW,_RX,_RY,_RZ,_S0,_S1,_S2,_S3,_S4,_S5,_S6));if(_S7!=__continue){return _S7;}}},_SW=function(_SX){var _SY=E(_SX);if(!_SY._){return new T2(0,_Z,_Z);}else{var _SZ=E(_SY.a),_T0=new T(function(){var _T1=B(_SW(_SY.b));return new T2(0,_T1.a,_T1.b);});return new T2(0,new T2(1,_SZ.a,new T(function(){return E(E(_T0).a);})),new T2(1,_SZ.b,new T(function(){return E(E(_T0).b);})));}},_T2=function(_T3,_T4){while(1){var _T5=E(_T3);if(!_T5._){return E(_T4);}else{var _T6=_T4+E(_T5.a)|0;_T3=_T5.b;_T4=_T6;continue;}}},_T7=function(_T8,_T9){while(1){var _Ta=E(_T9);if(!_Ta._){return __Z;}else{var _Tb=_Ta.b,_Tc=E(_T8);if(_Tc==1){return E(_Tb);}else{_T8=_Tc-1|0;_T9=_Tb;continue;}}}},_Td=function(_Te,_Tf,_Tg,_Th,_Ti,_Tj,_Tk,_Tl,_Tm,_Tn,_To,_Tp,_Tq,_Tr,_Ts,_Tt,_Tu,_Tv,_Tw,_Tx,_Ty,_Tz,_TA){while(1){var _TB=B((function(_TC,_TD,_TE,_TF,_TG,_TH,_TI,_TJ,_TK,_TL,_TM,_TN,_TO,_TP,_TQ,_TR,_TS,_TT,_TU,_TV,_TW,_TX,_TY){var _TZ=E(_TC);if(!_TZ._){return {_:0,a:_TD,b:_TE,c:_TF,d:_TG,e:_TH,f:_TI,g:_TJ,h:_TK,i:_TL,j:_TM,k:_TN,l:_TO,m:_TP,n:_TQ,o:_TR,p:_TS,q:_TT,r:_TU,s:_TV,t:_TW,u:_TX,v:_TY};}else{var _U0=new T(function(){var _U1=B(_KK(B(_x7(_KI,_TZ.a))));if(!_U1._){return E(_K6);}else{if(!E(_U1.b)._){return B(_x(B(_H(0,B(_aW(_TU,E(_U1.a))),_Z)),new T(function(){if(_TL>0){return B(_T7(_TL,_TF));}else{return E(_TF);}},1)));}else{return E(_K7);}}});if(0>=_TL){var _U2=E(_U0);}else{var _U3=function(_U4,_U5){var _U6=E(_U4);if(!_U6._){return E(_U0);}else{var _U7=_U6.a,_U8=E(_U5);return (_U8==1)?new T2(1,_U7,_U0):new T2(1,_U7,new T(function(){return B(_U3(_U6.b,_U8-1|0));}));}},_U2=B(_U3(_TF,_TL));}var _U9=_TD,_Ua=_TE,_Ub=_TG,_Uc=_TH,_Ud=_TI,_Ue=_TJ,_Uf=_TK,_Ug=_TL,_Uh=_TM,_Ui=_TN,_Uj=_TO,_Uk=_TP,_Ul=_TQ,_Um=_TR,_Un=_TS,_Uo=_TT,_Up=_TU,_Uq=_TV,_Ur=_TW,_Us=_TX,_Ut=_TY;_Te=_TZ.b;_Tf=_U9;_Tg=_Ua;_Th=_U2;_Ti=_Ub;_Tj=_Uc;_Tk=_Ud;_Tl=_Ue;_Tm=_Uf;_Tn=_Ug;_To=_Uh;_Tp=_Ui;_Tq=_Uj;_Tr=_Uk;_Ts=_Ul;_Tt=_Um;_Tu=_Un;_Tv=_Uo;_Tw=_Up;_Tx=_Uq;_Ty=_Ur;_Tz=_Us;_TA=_Ut;return __continue;}})(_Te,_Tf,_Tg,_Th,_Ti,_Tj,_Tk,_Tl,_Tm,_Tn,_To,_Tp,_Tq,_Tr,_Ts,_Tt,_Tu,_Tv,_Tw,_Tx,_Ty,_Tz,_TA));if(_TB!=__continue){return _TB;}}},_Uu=function(_Uv){return new F(function(){return _PU("Event.hs:119:28-52|(c : d : _)");});},_Uw=new T(function(){return B(_Uu(_));}),_Ux=function(_Uy,_Uz,_UA,_UB,_UC,_UD,_UE,_UF,_UG,_UH,_UI,_UJ,_UK,_UL,_UM,_UN,_UO,_UP,_UQ,_UR,_US,_UT,_UU,_UV,_UW,_UX,_UY,_UZ,_V0,_V1,_V2){while(1){var _V3=B((function(_V4,_V5,_V6,_V7,_V8,_V9,_Va,_Vb,_Vc,_Vd,_Ve,_Vf,_Vg,_Vh,_Vi,_Vj,_Vk,_Vl,_Vm,_Vn,_Vo,_Vp,_Vq,_Vr,_Vs,_Vt,_Vu,_Vv,_Vw,_Vx,_Vy){var _Vz=E(_V4);if(!_Vz._){return {_:0,a:E(_V5),b:E(_V6),c:E(_V7),d:E(_V8),e:E(_V9),f:E(_Va),g:E(_Vb),h:E(_Vc),i:_Vd,j:_Ve,k:_Vf,l:_Vg,m:E(_Vh),n:_Vi,o:E(_Vj),p:E(_Vk),q:_Vl,r:E(_Vm),s:E(_Vn),t:_Vo,u:E({_:0,a:E(_Vp),b:E(_Vq),c:E(_Vr),d:E(_B3),e:E(_Vt),f:E(_Vu),g:E(_B3),h:E(_Vw),i:E(_Vx)}),v:E(_Vy)};}else{var _VA=new T(function(){var _VB=E(_Vz.a);if(!_VB._){return E(_Uw);}else{var _VC=E(_VB.b);if(!_VC._){return E(_Uw);}else{var _VD=_VC.a,_VE=_VC.b,_VF=E(_VB.a);if(E(_VF)==44){return new T2(0,_Z,new T(function(){return E(B(_LC(44,_VD,_VE)).a);}));}else{var _VG=B(_LC(44,_VD,_VE)),_VH=E(_VG.b);if(!_VH._){return E(_Uw);}else{return new T2(0,new T2(1,_VF,_VG.a),_VH.a);}}}}}),_VI=_V5,_VJ=_V6,_VK=_V7,_VL=_V8,_VM=_V9,_VN=_Va,_VO=_Vb,_VP=_Vc,_VQ=_Vd,_VR=_Ve,_VS=_Vf,_VT=_Vg,_VU=B(_x(_Vh,new T2(1,new T2(0,new T(function(){return E(E(_VA).a);}),new T(function(){return E(E(_VA).b);})),_Z))),_VV=_Vi,_VW=_Vj,_VX=_Vk,_VY=_Vl,_VZ=_Vm,_W0=_Vn,_W1=_Vo,_W2=_Vp,_W3=_Vq,_W4=_Vr,_W5=_Vs,_W6=_Vt,_W7=_Vu,_W8=_Vv,_W9=_Vw,_Wa=_Vx,_Wb=_Vy;_Uy=_Vz.b;_Uz=_VI;_UA=_VJ;_UB=_VK;_UC=_VL;_UD=_VM;_UE=_VN;_UF=_VO;_UG=_VP;_UH=_VQ;_UI=_VR;_UJ=_VS;_UK=_VT;_UL=_VU;_UM=_VV;_UN=_VW;_UO=_VX;_UP=_VY;_UQ=_VZ;_UR=_W0;_US=_W1;_UT=_W2;_UU=_W3;_UV=_W4;_UW=_W5;_UX=_W6;_UY=_W7;_UZ=_W8;_V0=_W9;_V1=_Wa;_V2=_Wb;return __continue;}})(_Uy,_Uz,_UA,_UB,_UC,_UD,_UE,_UF,_UG,_UH,_UI,_UJ,_UK,_UL,_UM,_UN,_UO,_UP,_UQ,_UR,_US,_UT,_UU,_UV,_UW,_UX,_UY,_UZ,_V0,_V1,_V2));if(_V3!=__continue){return _V3;}}},_Wc=function(_Wd){return new F(function(){return _PU("Event.hs:65:27-53|(x\' : y\' : _)");});},_We=new T(function(){return B(_Wc(_));}),_Wf=function(_Wg){return new F(function(){return _PU("Event.hs:66:27-55|(chs : tps : _)");});},_Wh=new T(function(){return B(_Wf(_));}),_Wi=new T(function(){return B(_ic("Event.hs:(63,1)-(69,83)|function putCell"));}),_Wj=function(_Wk,_Wl,_Wm,_Wn,_Wo,_Wp,_Wq,_Wr,_Ws,_Wt,_Wu,_Wv,_Ww,_Wx,_Wy,_Wz,_WA,_WB,_WC,_WD,_WE,_WF,_WG){while(1){var _WH=B((function(_WI,_WJ,_WK,_WL,_WM,_WN,_WO,_WP,_WQ,_WR,_WS,_WT,_WU,_WV,_WW,_WX,_WY,_WZ,_X0,_X1,_X2,_X3,_X4){var _X5=E(_WI);if(!_X5._){return {_:0,a:_WJ,b:_WK,c:_WL,d:_WM,e:_WN,f:_WO,g:_WP,h:_WQ,i:_WR,j:_WS,k:_WT,l:_WU,m:_WV,n:_WW,o:_WX,p:_WY,q:_WZ,r:_X0,s:_X1,t:_X2,u:_X3,v:_X4};}else{var _X6=E(_X5.b);if(!_X6._){return E(_Wi);}else{var _X7=E(_WJ),_X8=new T(function(){var _X9=E(_X5.a);if(!_X9._){return E(_We);}else{var _Xa=E(_X9.b);if(!_Xa._){return E(_We);}else{var _Xb=_Xa.a,_Xc=_Xa.b,_Xd=E(_X9.a);if(E(_Xd)==44){return new T2(0,_Z,new T(function(){return E(B(_LC(44,_Xb,_Xc)).a);}));}else{var _Xe=B(_LC(44,_Xb,_Xc)),_Xf=E(_Xe.b);if(!_Xf._){return E(_We);}else{return new T2(0,new T2(1,_Xd,_Xe.a),_Xf.a);}}}}}),_Xg=B(_KK(B(_x7(_KI,new T(function(){return E(E(_X8).b);})))));if(!_Xg._){return E(_K6);}else{if(!E(_Xg.b)._){var _Xh=new T(function(){var _Xi=E(_X6.a);if(!_Xi._){return E(_Wh);}else{var _Xj=E(_Xi.b);if(!_Xj._){return E(_Wh);}else{var _Xk=_Xj.a,_Xl=_Xj.b,_Xm=E(_Xi.a);if(E(_Xm)==44){return new T2(0,_Z,new T(function(){return E(B(_LC(44,_Xk,_Xl)).a);}));}else{var _Xn=B(_LC(44,_Xk,_Xl)),_Xo=E(_Xn.b);if(!_Xo._){return E(_Wh);}else{return new T2(0,new T2(1,_Xm,_Xn.a),_Xo.a);}}}}}),_Xp=new T(function(){var _Xq=B(_KK(B(_x7(_KI,new T(function(){return E(E(_X8).a);})))));if(!_Xq._){return E(_K6);}else{if(!E(_Xq.b)._){return E(_Xq.a);}else{return E(_K7);}}},1),_Xr=_WK,_Xs=_WL,_Xt=_WM,_Xu=_WN,_Xv=_WO,_Xw=_WP,_Xx=_WQ,_Xy=_WR,_Xz=_WS,_XA=_WT,_XB=_WU,_XC=_WV,_XD=_WW,_XE=_WX,_XF=_WY,_XG=_WZ,_XH=_X0,_XI=_X1,_XJ=_X2,_XK=_X3,_XL=_X4;_Wk=_X6.b;_Wl={_:0,a:E(_X7.a),b:E(B(_Pt(_Xp,E(_Xg.a),new T(function(){return B(_NR(E(_Xh).a));}),new T(function(){return B(_O5(E(_Xh).b));}),_X7.b))),c:E(_X7.c),d:_X7.d,e:_X7.e,f:_X7.f,g:E(_X7.g),h:_X7.h,i:E(_X7.i),j:E(_X7.j),k:E(_X7.k)};_Wm=_Xr;_Wn=_Xs;_Wo=_Xt;_Wp=_Xu;_Wq=_Xv;_Wr=_Xw;_Ws=_Xx;_Wt=_Xy;_Wu=_Xz;_Wv=_XA;_Ww=_XB;_Wx=_XC;_Wy=_XD;_Wz=_XE;_WA=_XF;_WB=_XG;_WC=_XH;_WD=_XI;_WE=_XJ;_WF=_XK;_WG=_XL;return __continue;}else{return E(_K7);}}}}})(_Wk,_Wl,_Wm,_Wn,_Wo,_Wp,_Wq,_Wr,_Ws,_Wt,_Wu,_Wv,_Ww,_Wx,_Wy,_Wz,_WA,_WB,_WC,_WD,_WE,_WF,_WG));if(_WH!=__continue){return _WH;}}},_XM=function(_XN,_XO){while(1){var _XP=E(_XO);if(!_XP._){return __Z;}else{var _XQ=_XP.b,_XR=E(_XN);if(_XR==1){return E(_XQ);}else{_XN=_XR-1|0;_XO=_XQ;continue;}}}},_XS=function(_XT){var _XU=E(_XT);if(!_XU._){return new T2(0,_Z,_Z);}else{var _XV=E(_XU.a),_XW=new T(function(){var _XX=B(_XS(_XU.b));return new T2(0,_XX.a,_XX.b);});return new T2(0,new T2(1,_XV.a,new T(function(){return E(E(_XW).a);})),new T2(1,_XV.b,new T(function(){return E(E(_XW).b);})));}},_XY=32,_XZ=function(_Y0,_Y1,_Y2,_Y3){var _Y4=E(_Y3);if(!_Y4._){return __Z;}else{var _Y5=_Y4.b;if(!B(_4H(_3S,_Y0,_Y2))){var _Y6=new T(function(){return B(_XZ(new T(function(){return E(_Y0)+1|0;}),_Y1,_Y2,_Y5));});return new T2(1,_Y4.a,_Y6);}else{var _Y7=new T(function(){return B(_XZ(new T(function(){return E(_Y0)+1|0;}),_Y1,_Y2,_Y5));});return new T2(1,_Y1,_Y7);}}},_Y8=function(_Y9,_Ya){var _Yb=E(_Ya);if(!_Yb._){return __Z;}else{var _Yc=new T(function(){var _Yd=B(_XS(_Yb.a)),_Ye=_Yd.a,_Yf=new T(function(){return B(_Nu(0,_Y9,_Ye));});return B(_KW(B(_XZ(_vT,_XY,_Yf,_Ye)),new T(function(){return B(_NB(0,_II,_Yf,_Yd.b));},1)));});return new T2(1,_Yc,new T(function(){return B(_Y8(_Y9,_Yb.b));}));}},_Yg=function(_Yh,_Yi){var _Yj=E(_Yi);return (_Yj._==0)?__Z:new T2(1,_Yh,new T(function(){return B(_Yg(_Yj.a,_Yj.b));}));},_Yk=new T(function(){return B(unCStr("init"));}),_Yl=new T(function(){return B(_rj(_Yk));}),_Ym=function(_Yn,_Yo){var _Yp=function(_Yq){var _Yr=E(_Yq);if(!_Yr._){return __Z;}else{var _Ys=new T(function(){return B(_x(new T2(1,_Yn,_Z),new T(function(){return B(_Yp(_Yr.b));},1)));},1);return new F(function(){return _x(_Yr.a,_Ys);});}},_Yt=B(_Yp(_Yo));if(!_Yt._){return E(_Yl);}else{return new F(function(){return _Yg(_Yt.a,_Yt.b);});}},_Yu=61,_Yv=46,_Yw=new T(function(){return B(_ic("Event.hs:(109,1)-(115,61)|function makeDecision"));}),_Yx=new T(function(){return B(unCStr("sm"));}),_Yy=new T(function(){return B(unCStr("rt"));}),_Yz=new T(function(){return B(unCStr("rs"));}),_YA=new T(function(){return B(unCStr("rk"));}),_YB=new T(function(){return B(unCStr("if"));}),_YC=new T(function(){return B(unCStr("hm"));}),_YD=new T(function(){return B(unCStr("cleq"));}),_YE=new T(function(){return B(unCStr("da"));}),_YF=new T(function(){return B(unCStr("ct"));}),_YG=function(_YH,_YI,_YJ,_YK,_YL,_YM,_YN,_YO,_YP,_YQ,_YR,_YS,_YT,_YU,_YV,_YW,_YX,_YY,_YZ,_Z0,_Z1,_Z2,_Z3){var _Z4=function(_Z5,_Z6){var _Z7=function(_Z8){if(!B(_vl(_Z5,_YF))){if(!B(_vl(_Z5,_YE))){var _Z9=function(_Za){if(!B(_vl(_Z5,_YD))){var _Zb=function(_Zc){if(!B(_vl(_Z5,_wm))){if(!B(_vl(_Z5,_YC))){if(!B(_vl(_Z5,_YB))){if(!B(_vl(_Z5,_YA))){if(!B(_vl(_Z5,_Yz))){if(!B(_vl(_Z5,_Yy))){if(!B(_vl(_Z5,_Yx))){return {_:0,a:E(_YI),b:E(_YJ),c:E(_YK),d:E(_YL),e:E(_YM),f:E(_YN),g:E(_YO),h:E(_YP),i:_YQ,j:_YR,k:_YS,l:_YT,m:E(_YU),n:_YV,o:E(_YW),p:E(_YX),q:_YY,r:E(_YZ),s:E(_Z0),t:_Z1,u:E(_Z2),v:E(_Z3)};}else{var _Zd=E(_Z2);return {_:0,a:E(_YI),b:E(_YJ),c:E(_YK),d:E(_YL),e:E(_YM),f:E(_YN),g:E(_YO),h:E(_YP),i:_YQ,j:_YR,k:_YS,l:_YT,m:E(_YU),n:_YV,o:E(_YW),p:E(_YX),q:_YY,r:E(_YZ),s:E(_Z0),t:_Z1,u:E({_:0,a:E(_Zd.a),b:E(_Zd.b),c:E(_Zd.c),d:E(_Zd.d),e:E(_Zd.e),f:E(_Zd.f),g:E(_Zd.g),h:E(_B3),i:E(_Zd.i)}),v:E(_Z3)};}}else{var _Ze=B(_Td(_Z6,_YI,_YJ,_YK,_YL,_YM,_YN,_YO,_YP,_YQ,_YR,_YS,_YT,_YU,_YV,_YW,_YX,_YY,_YZ,_Z0,_Z1,_Z2,_Z3));return {_:0,a:E(_Ze.a),b:E(_Ze.b),c:E(_Ze.c),d:E(_Ze.d),e:E(_Ze.e),f:E(_Ze.f),g:E(_Ze.g),h:E(_Ze.h),i:_Ze.i,j:_Ze.j,k:_Ze.k,l:_Ze.l,m:E(_Ze.m),n:_Ze.n,o:E(_Ze.o),p:E(_Ze.p),q:_Ze.q,r:E(_Ze.r),s:E(_Ze.s),t:_Ze.t,u:E(_Ze.u),v:E(_Ze.v)};}}else{var _Zf=new T(function(){return B(_x(B(_H(0,600-B(_T2(_YZ,0))|0,_Z)),new T(function(){if(_YQ>0){return B(_XM(_YQ,_YK));}else{return E(_YK);}},1)));});if(0>=_YQ){var _Zg=E(_Zf);}else{var _Zh=function(_Zi,_Zj){var _Zk=E(_Zi);if(!_Zk._){return E(_Zf);}else{var _Zl=_Zk.a,_Zm=E(_Zj);return (_Zm==1)?new T2(1,_Zl,_Zf):new T2(1,_Zl,new T(function(){return B(_Zh(_Zk.b,_Zm-1|0));}));}},_Zg=B(_Zh(_YK,_YQ));}return {_:0,a:E(_YI),b:E(_YJ),c:E(_Zg),d:E(_YL),e:E(_YM),f:E(_YN),g:E(_YO),h:E(_YP),i:_YQ,j:_YR,k:_YS,l:_YT,m:E(_YU),n:_YV,o:E(_YW),p:E(_YX),q:_YY,r:E(_YZ),s:E(_Z0),t:_Z1,u:E(_Z2),v:E(_Z3)};}}else{return {_:0,a:E(_YI),b:E(_YJ),c:E(_YK),d:E(_YL),e:E(_YM),f:E(_YN),g:E(_YO),h:E(_YP),i:_YQ,j:_YR,k:_YS,l:_YT,m:E(_YU),n:_YV,o:E(_Z6),p:E(_YX),q:_YY,r:E(_YZ),s:E(_Z0),t:_Z1,u:E(_Z2),v:E(_Z3)};}}else{var _Zn=E(_Z6);if(!_Zn._){return {_:0,a:E(_YI),b:E(_YJ),c:E(_YK),d:E(_YL),e:E(_YM),f:E(_YN),g:E(_YO),h:E(_YP),i:_YQ,j:_YR,k:_YS,l:_YT,m:E(_YU),n:_YV,o:E(_YW),p:E(_YX),q:_YY,r:E(_YZ),s:E(_Z0),t:_Z1,u:E(_Z2),v:E(_Z3)};}else{var _Zo=_Zn.a,_Zp=E(_Zn.b);if(!_Zp._){return E(_Yw);}else{var _Zq=_Zp.a,_Zr=B(_SW(_YO)),_Zs=_Zr.a,_Zt=_Zr.b,_Zu=function(_Zv){if(!B(_4H(_uJ,_Zo,_Zs))){return {_:0,a:E(_YI),b:E(_YJ),c:E(_YK),d:E(_YL),e:E(_YM),f:E(_YN),g:E(_YO),h:E(_YP),i:_YQ,j:_YR,k:_YS,l:_YT,m:E(_YU),n:_YV,o:E(_YW),p:E(_YX),q:_YY,r:E(_YZ),s:E(_Z0),t:_Z1,u:E(_Z2),v:E(_Z3)};}else{if(!B(_vl(_Zq,B(_aW(_Zt,B(_Rj(_uJ,_Zo,_Zs))))))){return {_:0,a:E(_YI),b:E(_YJ),c:E(_YK),d:E(_YL),e:E(_YM),f:E(_YN),g:E(_YO),h:E(_YP),i:_YQ,j:_YR,k:_YS,l:_YT,m:E(_YU),n:_YV,o:E(_YW),p:E(_YX),q:_YY,r:E(_YZ),s:E(_Z0),t:_Z1,u:E(_Z2),v:E(_Z3)};}else{return new F(function(){return _YG(_Zv,_YI,_YJ,_YK,_YL,_YM,_YN,_YO,_YP,_YQ,_YR,_YS,_YT,_YU,_YV,_YW,_YX,_YY,_YZ,_Z0,_Z1,_Z2,_Z3);});}}},_Zw=B(_Ym(_Yv,_Zp.b));if(!_Zw._){return new F(function(){return _Zu(_Z);});}else{var _Zx=_Zw.a,_Zy=E(_Zw.b);if(!_Zy._){return new F(function(){return _Zu(new T2(1,_Zx,_Z));});}else{var _Zz=_Zy.a,_ZA=_Zy.b,_ZB=E(_Zx);if(E(_ZB)==47){if(!B(_4H(_uJ,_Zo,_Zs))){return new F(function(){return _YG(B(_LC(47,_Zz,_ZA)).a,_YI,_YJ,_YK,_YL,_YM,_YN,_YO,_YP,_YQ,_YR,_YS,_YT,_YU,_YV,_YW,_YX,_YY,_YZ,_Z0,_Z1,_Z2,_Z3);});}else{if(!B(_vl(_Zq,B(_aW(_Zt,B(_Rj(_uJ,_Zo,_Zs))))))){return new F(function(){return _YG(B(_LC(47,_Zz,_ZA)).a,_YI,_YJ,_YK,_YL,_YM,_YN,_YO,_YP,_YQ,_YR,_YS,_YT,_YU,_YV,_YW,_YX,_YY,_YZ,_Z0,_Z1,_Z2,_Z3);});}else{return new F(function(){return _YG(_Z,_YI,_YJ,_YK,_YL,_YM,_YN,_YO,_YP,_YQ,_YR,_YS,_YT,_YU,_YV,_YW,_YX,_YY,_YZ,_Z0,_Z1,_Z2,_Z3);});}}}else{if(!B(_4H(_uJ,_Zo,_Zs))){var _ZC=E(B(_LC(47,_Zz,_ZA)).b);if(!_ZC._){return {_:0,a:E(_YI),b:E(_YJ),c:E(_YK),d:E(_YL),e:E(_YM),f:E(_YN),g:E(_YO),h:E(_YP),i:_YQ,j:_YR,k:_YS,l:_YT,m:E(_YU),n:_YV,o:E(_YW),p:E(_YX),q:_YY,r:E(_YZ),s:E(_Z0),t:_Z1,u:E(_Z2),v:E(_Z3)};}else{return new F(function(){return _YG(_ZC.a,_YI,_YJ,_YK,_YL,_YM,_YN,_YO,_YP,_YQ,_YR,_YS,_YT,_YU,_YV,_YW,_YX,_YY,_YZ,_Z0,_Z1,_Z2,_Z3);});}}else{if(!B(_vl(_Zq,B(_aW(_Zt,B(_Rj(_uJ,_Zo,_Zs))))))){var _ZD=E(B(_LC(47,_Zz,_ZA)).b);if(!_ZD._){return {_:0,a:E(_YI),b:E(_YJ),c:E(_YK),d:E(_YL),e:E(_YM),f:E(_YN),g:E(_YO),h:E(_YP),i:_YQ,j:_YR,k:_YS,l:_YT,m:E(_YU),n:_YV,o:E(_YW),p:E(_YX),q:_YY,r:E(_YZ),s:E(_Z0),t:_Z1,u:E(_Z2),v:E(_Z3)};}else{return new F(function(){return _YG(_ZD.a,_YI,_YJ,_YK,_YL,_YM,_YN,_YO,_YP,_YQ,_YR,_YS,_YT,_YU,_YV,_YW,_YX,_YY,_YZ,_Z0,_Z1,_Z2,_Z3);});}}else{return new F(function(){return _YG(new T2(1,_ZB,new T(function(){return E(B(_LC(47,_Zz,_ZA)).a);})),_YI,_YJ,_YK,_YL,_YM,_YN,_YO,_YP,_YQ,_YR,_YS,_YT,_YU,_YV,_YW,_YX,_YY,_YZ,_Z0,_Z1,_Z2,_Z3);});}}}}}}}}}else{var _ZE=E(_Z2);return {_:0,a:E(_YI),b:E(_YJ),c:E(_YK),d:E(_YL),e:E(_YM),f:E(_YN),g:E(_YO),h:E(_YP),i:_YQ,j:_YR,k:_YS,l:_YT,m:E(_YU),n:_YV,o:E(_YW),p:E(_YX),q:_YY,r:E(_YZ),s:E(_Z0),t:_Z1,u:E({_:0,a:E(_ZE.a),b:E(_ZE.b),c:E(_ZE.c),d:E(_ZE.d),e:E(_ZE.e),f:E(_ZE.f),g:E(_ZE.g),h:E(_B2),i:E(_ZE.i)}),v:E(_Z3)};}}else{var _ZF=E(_Z2);return new F(function(){return _Ux(_Z6,_YI,_YJ,_YK,_YL,_YM,_YN,_YO,_YP,_YQ,_YR,_YS,_YT,_Z,_YV,_YW,_YX,_YY,_YZ,_Z0,_Z1,_ZF.a,_ZF.b,_ZF.c,_ZF.d,_ZF.e,_ZF.f,_ZF.g,_ZF.h,_ZF.i,_Z3);});}},_ZG=E(_Z5);if(!_ZG._){return new F(function(){return _Zb(_);});}else{if(E(_ZG.a)==109){if(!E(_ZG.b)._){var _ZH=B(_LP(_Z6,_YI,_YJ,_YK,_YL,_YM,_YN,_YO,_YP,_YQ,_YR,_YS,_YT,_YU,_YV,_YW,_YX,_YY,_YZ,_Z0,_Z1,_Z2,_Z3));return {_:0,a:E(_ZH.a),b:E(_ZH.b),c:E(_ZH.c),d:E(_ZH.d),e:E(_ZH.e),f:E(_ZH.f),g:E(_ZH.g),h:E(_ZH.h),i:_ZH.i,j:_ZH.j,k:_ZH.k,l:_ZH.l,m:E(_ZH.m),n:_ZH.n,o:E(_ZH.o),p:E(_ZH.p),q:_ZH.q,r:E(_ZH.r),s:E(_ZH.s),t:_ZH.t,u:E(_ZH.u),v:E(_ZH.v)};}else{return new F(function(){return _Zb(_);});}}else{return new F(function(){return _Zb(_);});}}}else{var _ZI=E(_YI);return {_:0,a:E({_:0,a:E(_ZI.a),b:E(B(_Y8(_Yu,_ZI.b))),c:E(_ZI.c),d:_ZI.d,e:_ZI.e,f:_ZI.f,g:E(_ZI.g),h:_ZI.h,i:E(_ZI.i),j:E(_ZI.j),k:E(_ZI.k)}),b:E(_YJ),c:E(_YK),d:E(_YL),e:E(_YM),f:E(_YN),g:E(_YO),h:E(_YP),i:_YQ,j:_YR,k:_YS,l:_YT,m:E(_YU),n:_YV,o:E(_YW),p:E(_YX),q:_YY,r:E(_YZ),s:E(_Z0),t:_Z1,u:E(_Z2),v:E(_Z3)};}},_ZJ=E(_Z5);if(!_ZJ._){return new F(function(){return _Z9(_);});}else{var _ZK=_ZJ.b;switch(E(_ZJ.a)){case 99:if(!E(_ZK)._){var _ZL=B(_PZ(_Z6,_YI,_YJ,_YK,_YL,_YM,_YN,_YO,_YP,_YQ,_YR,_YS,_YT,_YU,_YV,_YW,_YX,_YY,_YZ,_Z0,_Z1,_Z2,_Z3));return {_:0,a:E(_ZL.a),b:E(_ZL.b),c:E(_ZL.c),d:E(_ZL.d),e:E(_ZL.e),f:E(_ZL.f),g:E(_ZL.g),h:E(_ZL.h),i:_ZL.i,j:_ZL.j,k:_ZL.k,l:_ZL.l,m:E(_ZL.m),n:_ZL.n,o:E(_ZL.o),p:E(_ZL.p),q:_ZL.q,r:E(_ZL.r),s:E(_ZL.s),t:_ZL.t,u:E(_ZL.u),v:E(_ZL.v)};}else{return new F(function(){return _Z9(_);});}break;case 112:if(!E(_ZK)._){var _ZM=B(_Wj(_Z6,_YI,_YJ,_YK,_YL,_YM,_YN,_YO,_YP,_YQ,_YR,_YS,_YT,_YU,_YV,_YW,_YX,_YY,_YZ,_Z0,_Z1,_Z2,_Z3));return {_:0,a:E(_ZM.a),b:E(_ZM.b),c:E(_ZM.c),d:E(_ZM.d),e:E(_ZM.e),f:E(_ZM.f),g:E(_ZM.g),h:E(_ZM.h),i:_ZM.i,j:_ZM.j,k:_ZM.k,l:_ZM.l,m:E(_ZM.m),n:_ZM.n,o:E(_ZM.o),p:E(_ZM.p),q:_ZM.q,r:E(_ZM.r),s:E(_ZM.s),t:_ZM.t,u:E(_ZM.u),v:E(_ZM.v)};}else{return new F(function(){return _Z9(_);});}break;default:return new F(function(){return _Z9(_);});}}}else{return {_:0,a:E(_YI),b:E(_YJ),c:E(_YK),d:E(_YL),e:E(_Z),f:E(_YN),g:E(_YO),h:E(_YP),i:_YQ,j:_YR,k:_YS,l:_YT,m:E(_YU),n:_YV,o:E(_YW),p:E(_YX),q:_YY,r:E(_YZ),s:E(_Z0),t:_Z1,u:E(_Z2),v:E(_Z3)};}}else{var _ZN=B(_O7(_Z6,_YI,_YJ,_YK,_YL,_YM,_YN,_YO,_YP,_YQ,_YR,_YS,_YT,_YU,_YV,_YW,_YX,_YY,_YZ,_Z0,_Z1,_Z2,_Z3));return {_:0,a:E(_ZN.a),b:E(_ZN.b),c:E(_ZN.c),d:E(_ZN.d),e:E(_ZN.e),f:E(_ZN.f),g:E(_ZN.g),h:E(_ZN.h),i:_ZN.i,j:_ZN.j,k:_ZN.k,l:_ZN.l,m:E(_ZN.m),n:_ZN.n,o:E(_ZN.o),p:E(_ZN.p),q:_ZN.q,r:E(_ZN.r),s:E(_ZN.s),t:_ZN.t,u:E(_ZN.u),v:E(_ZN.v)};}},_ZO=E(_Z5);if(!_ZO._){return new F(function(){return _Z7(_);});}else{var _ZP=_ZO.b;switch(E(_ZO.a)){case 100:if(!E(_ZP)._){var _ZQ=B(_RJ(_Z6,_YI,_YJ,_YK,_YL,_YM,_YN,_YO,_YP,_YQ,_YR,_YS,_YT,_YU,_YV,_YW,_YX,_YY,_YZ,_Z0,_Z1,_Z2,_Z3));return {_:0,a:E(_ZQ.a),b:E(_ZQ.b),c:E(_ZQ.c),d:E(_ZQ.d),e:E(_ZQ.e),f:E(_ZQ.f),g:E(_ZQ.g),h:E(_ZQ.h),i:_ZQ.i,j:_ZQ.j,k:_ZQ.k,l:_ZQ.l,m:E(_ZQ.m),n:_ZQ.n,o:E(_ZQ.o),p:E(_ZQ.p),q:_ZQ.q,r:E(_ZQ.r),s:E(_ZQ.s),t:_ZQ.t,u:E(_ZQ.u),v:E(_ZQ.v)};}else{return new F(function(){return _Z7(_);});}break;case 101:if(!E(_ZP)._){var _ZR=B(_uM(_Z6,_YI,_YJ,_YK,_YL,_YM,_YN,_YO,_YP,_YQ,_YR,_YS,_YT,_YU,_YV,_YW,_YX,_YY,_YZ,_Z0,_Z1,_Z2,_Z3));return {_:0,a:E(_ZR.a),b:E(_ZR.b),c:E(_ZR.c),d:E(_ZR.d),e:E(_ZR.e),f:E(_ZR.f),g:E(_ZR.g),h:E(_ZR.h),i:_ZR.i,j:_ZR.j,k:_ZR.k,l:_ZR.l,m:E(_ZR.m),n:_ZR.n,o:E(_ZR.o),p:E(_ZR.p),q:_ZR.q,r:E(_ZR.r),s:E(_ZR.s),t:_ZR.t,u:E(_ZR.u),v:E(_ZR.v)};}else{return new F(function(){return _Z7(_);});}break;default:return new F(function(){return _Z7(_);});}}},_ZS=E(_YH);if(!_ZS._){return new F(function(){return _Z4(_Z,_Z);});}else{var _ZT=_ZS.a,_ZU=E(_ZS.b);if(!_ZU._){return new F(function(){return _Z4(new T2(1,_ZT,_Z),_Z);});}else{var _ZV=E(_ZT),_ZW=new T(function(){var _ZX=B(_LC(46,_ZU.a,_ZU.b));return new T2(0,_ZX.a,_ZX.b);});if(E(_ZV)==46){return new F(function(){return _Z4(_Z,new T2(1,new T(function(){return E(E(_ZW).a);}),new T(function(){return E(E(_ZW).b);})));});}else{return new F(function(){return _Z4(new T2(1,_ZV,new T(function(){return E(E(_ZW).a);})),new T(function(){return E(E(_ZW).b);}));});}}}},_ZY=new T(function(){return B(unCStr("last"));}),_ZZ=new T(function(){return B(_rj(_ZY));}),_100=32,_101=0,_102=65306,_103=125,_104=new T1(0,1),_105=function(_106,_107,_108,_109,_10a){var _10b=new T(function(){return E(_10a).i;}),_10c=new T(function(){var _10d=E(_107)/28,_10e=_10d&4294967295;if(_10d>=_10e){return _10e-1|0;}else{return (_10e-1|0)-1|0;}}),_10f=new T(function(){if(!E(E(_109).h)){return E(_nd);}else{return 2+(E(E(E(_10a).b).b)+2|0)|0;}}),_10g=new T(function(){if(!E(_10b)){return new T2(0,_10c,_10f);}else{return E(E(_10a).h);}}),_10h=new T(function(){return E(E(_10a).c);}),_10i=new T(function(){var _10j=E(_10b)+1|0;if(0>=_10j){return E(_100);}else{var _10k=B(_uj(_10j,_10h));if(!_10k._){return E(_100);}else{return B(_sF(_10k.a,_10k.b,_ZZ));}}}),_10l=new T(function(){var _10m=E(_10i);switch(E(_10m)){case 125:return E(_100);break;case 12289:return E(_100);break;case 12290:return E(_100);break;default:return E(_10m);}}),_10n=new T(function(){if(E(_10l)==10){return true;}else{return false;}}),_10o=new T(function(){return E(E(_10g).b);}),_10p=new T(function(){if(!E(_10n)){if(E(_10l)==12300){return E(_nc);}else{return E(_10a).j;}}else{return E(_101);}}),_10q=new T(function(){return E(E(_10g).a);}),_10r=new T(function(){if(E(_10l)==65306){return true;}else{return false;}}),_10s=new T(function(){if(!E(_10r)){if(!E(_10n)){var _10t=E(_10o);if((_10t+1)*24<=E(_108)-10){return new T2(0,_10q,_10t+1|0);}else{return new T2(0,new T(function(){return E(_10q)-1|0;}),_10f);}}else{return new T2(0,new T(function(){return E(_10q)-1|0;}),_10f);}}else{return new T2(0,_10q,_10o);}}),_10u=new T(function(){if(E(E(_10s).a)==1){if(E(_10q)==1){return false;}else{return true;}}else{return false;}}),_10v=new T(function(){return B(_qy(_10h,0))-1|0;}),_10w=new T(function(){if(!E(_10r)){return __Z;}else{return B(_uB(_102,E(_10b),_10h));}}),_10x=new T(function(){if(E(_10l)==123){return true;}else{return false;}}),_10y=new T(function(){if(!E(_10x)){return __Z;}else{return B(_uB(_103,E(_10b),_10h));}}),_10z=new T(function(){if(!E(_10r)){if(!E(_10x)){return E(_nc);}else{return B(_qy(_10y,0))+2|0;}}else{return B(_qy(_10w,0))+2|0;}}),_10A=new T(function(){var _10B=E(_10a),_10C=_10B.a,_10D=_10B.b,_10E=_10B.c,_10F=_10B.d,_10G=_10B.e,_10H=_10B.f,_10I=_10B.g,_10J=_10B.h,_10K=_10B.j,_10L=_10B.k,_10M=_10B.l,_10N=_10B.m,_10O=_10B.n,_10P=_10B.o,_10Q=_10B.p,_10R=_10B.q,_10S=_10B.r,_10T=_10B.s,_10U=_10B.t,_10V=_10B.v,_10W=E(_10b),_10X=E(_10z);if((_10W+_10X|0)<=E(_10v)){var _10Y=E(_109),_10Z=_10Y.a,_110=_10Y.b,_111=_10Y.c,_112=_10Y.e,_113=_10Y.f,_114=_10Y.g,_115=_10Y.h,_116=_10Y.i;if(E(_10i)==12290){var _117=true;}else{var _117=false;}if(!E(_10x)){return {_:0,a:E(_10C),b:E(_10D),c:E(_10E),d:E(_10F),e:E(_10G),f:E(_10H),g:E(_10I),h:E(_10J),i:_10W+_10X|0,j:_10K,k:_10L,l:_10M,m:E(_10N),n:_10O,o:E(_10P),p:E(_10Q),q:_10R,r:E(_10S),s:E(_10T),t:_10U,u:E({_:0,a:E(_10Z),b:E(_110),c:E(_111),d:E(_117),e:E(_112),f:E(_113),g:E(_114),h:E(_115),i:E(_116)}),v:E(_10V)};}else{return B(_YG(_10y,_10C,_10D,_10E,_10F,_10G,_10H,_10I,_10J,_10W+_10X|0,_10K,_10L,_10M,_10N,_10O,_10P,_10Q,_10R,_10S,_10T,_10U,{_:0,a:E(_10Z),b:E(_110),c:E(_111),d:E(_117),e:E(_112),f:E(_113),g:E(_114),h:E(_115),i:E(_116)},_10V));}}else{var _118=E(_109),_119=_118.a,_11a=_118.b,_11b=_118.c,_11c=_118.e,_11d=_118.f,_11e=_118.g,_11f=_118.h,_11g=_118.i;if(E(_10i)==12290){var _11h=true;}else{var _11h=false;}if(!E(_10x)){return {_:0,a:E(_10C),b:E(_10D),c:E(_10E),d:E(_10F),e:E(_10G),f:E(_10H),g:E(_10I),h:E(_10J),i:0,j:_10K,k:_10L,l:_10M,m:E(_10N),n:_10O,o:E(_10P),p:E(_10Q),q:_10R,r:E(_10S),s:E(_10T),t:_10U,u:E({_:0,a:E(_119),b:E(_11a),c:E(_11b),d:E(_11h),e:E(_11c),f:E(_11d),g:E(_11e),h:E(_11f),i:E(_11g)}),v:E(_10V)};}else{return B(_YG(_10y,_10C,_10D,_10E,_10F,_10G,_10H,_10I,_10J,0,_10K,_10L,_10M,_10N,_10O,_10P,_10Q,_10R,_10S,_10T,_10U,{_:0,a:E(_119),b:E(_11a),c:E(_11b),d:E(_11h),e:E(_11c),f:E(_11d),g:E(_11e),h:E(_11f),i:E(_11g)},_10V));}}}),_11i=new T(function(){return E(E(_10A).u);}),_11j=new T(function(){if(!E(_10b)){return E(_101);}else{return E(_10A).k;}}),_11k=new T(function(){var _11l=B(_sz(B(_sx(_106)))),_11m=new T(function(){var _11n=B(_u0(_106,E(_107)/16)),_11o=_11n.a;if(E(_11n.b)>=0){return E(_11o);}else{return B(A3(_tc,_11l,_11o,new T(function(){return B(A2(_lj,_11l,_104));})));}});return B(A3(_tc,_11l,_11m,new T(function(){return B(A2(_lj,_11l,_ls));})));});return {_:0,a:_10l,b:_10q,c:_10o,d:new T(function(){if(E(_10f)!=E(_10o)){return E(_10q);}else{return E(_10q)+1|0;}}),e:new T(function(){var _11p=E(_10o);if(E(_10f)!=_11p){return _11p-1|0;}else{var _11q=(E(_108)-10)/24,_11r=_11q&4294967295;if(_11q>=_11r){return _11r;}else{return _11r-1|0;}}}),f:_10f,g:_10b,h:_10h,i:new T(function(){return B(_aW(_n9,E(_10p)));}),j:_10w,k:_10c,l:_11k,m:_11j,n:_ne,o:_10r,p:_10x,q:_10u,r:_11i,s:_10A,t:new T(function(){var _11s=E(_10A),_11t=_11s.a,_11u=_11s.b,_11v=_11s.c,_11w=_11s.d,_11x=_11s.e,_11y=_11s.f,_11z=_11s.g,_11A=_11s.i,_11B=_11s.l,_11C=_11s.m,_11D=_11s.n,_11E=_11s.o,_11F=_11s.p,_11G=_11s.q,_11H=_11s.r,_11I=_11s.s,_11J=_11s.t,_11K=_11s.v;if(!E(_10u)){var _11L=E(_10s);}else{var _11L=new T2(0,_10q,_10f);}var _11M=E(_10p);if(!E(_10u)){var _11N=E(_11i);return {_:0,a:E(_11t),b:E(_11u),c:E(_11v),d:E(_11w),e:E(_11x),f:E(_11y),g:E(_11z),h:E(_11L),i:_11A,j:_11M,k:E(_11j),l:_11B,m:E(_11C),n:_11D,o:E(_11E),p:E(_11F),q:_11G,r:E(_11H),s:E(_11I),t:_11J,u:E({_:0,a:E(_11N.a),b:E(_11N.b),c:(E(_10b)+E(_10z)|0)<=E(_10v),d:E(_11N.d),e:E(_11N.e),f:E(_11N.f),g:E(_11N.g),h:E(_11N.h),i:E(_11N.i)}),v:E(_11K)};}else{var _11O=E(_11i);return {_:0,a:E(_11t),b:E(_11u),c:E(_11v),d:E(_11w),e:E(_11x),f:E(_11y),g:E(_11z),h:E(_11L),i:_11A,j:_11M,k:E(_11j)+1|0,l:_11B,m:E(_11C),n:_11D,o:E(_11E),p:E(_11F),q:_11G,r:E(_11H),s:E(_11I),t:_11J,u:E({_:0,a:E(_11O.a),b:E(_11O.b),c:(E(_10b)+E(_10z)|0)<=E(_10v),d:E(_11O.d),e:E(_11O.e),f:E(_11O.f),g:E(_11O.g),h:E(_11O.h),i:E(_11O.i)}),v:E(_11K)};}})};},_11P=function(_11Q){var _11R=E(_11Q);if(!_11R._){return new T2(0,_Z,_Z);}else{var _11S=E(_11R.a),_11T=new T(function(){var _11U=B(_11P(_11R.b));return new T2(0,_11U.a,_11U.b);});return new T2(0,new T2(1,_11S.a,new T(function(){return E(E(_11T).a);})),new T2(1,_11S.b,new T(function(){return E(E(_11T).b);})));}},_11V=42,_11W=32,_11X=function(_11Y,_11Z,_120){var _121=E(_11Y);if(!_121._){return __Z;}else{var _122=_121.a,_123=_121.b;if(_11Z!=_120){var _124=E(_122);return (_124._==0)?E(_rm):(E(_124.a)==42)?new T2(1,new T2(1,_11W,_124.b),new T(function(){return B(_11X(_123,_11Z,_120+1|0));})):new T2(1,new T2(1,_11W,_124),new T(function(){return B(_11X(_123,_11Z,_120+1|0));}));}else{var _125=E(_122);return (_125._==0)?E(_rm):(E(_125.a)==42)?new T2(1,new T2(1,_11W,_125),new T(function(){return B(_11X(_123,_11Z,_120+1|0));})):new T2(1,new T2(1,_11V,_125),new T(function(){return B(_11X(_123,_11Z,_120+1|0));}));}}},_126=new T(function(){return B(unCStr("\n\n"));}),_127=function(_128){var _129=E(_128);if(!_129._){return __Z;}else{var _12a=new T(function(){return B(_x(_126,new T(function(){return B(_127(_129.b));},1)));},1);return new F(function(){return _x(_129.a,_12a);});}},_12b=function(_12c,_12d,_12e){var _12f=new T(function(){var _12g=new T(function(){var _12h=E(_12d);if(!_12h._){return B(_127(_Z));}else{var _12i=_12h.a,_12j=_12h.b,_12k=E(_12e);if(!_12k){var _12l=E(_12i);if(!_12l._){return E(_rm);}else{if(E(_12l.a)==42){return B(_127(new T2(1,new T2(1,_11W,_12l),new T(function(){return B(_11X(_12j,0,1));}))));}else{return B(_127(new T2(1,new T2(1,_11V,_12l),new T(function(){return B(_11X(_12j,0,1));}))));}}}else{var _12m=E(_12i);if(!_12m._){return E(_rm);}else{if(E(_12m.a)==42){return B(_127(new T2(1,new T2(1,_11W,_12m.b),new T(function(){return B(_11X(_12j,_12k,1));}))));}else{return B(_127(new T2(1,new T2(1,_11W,_12m),new T(function(){return B(_11X(_12j,_12k,1));}))));}}}}});return B(unAppCStr("\n\n",_12g));},1);return new F(function(){return _x(_12c,_12f);});},_12n=function(_12o){return E(E(_12o).c);},_12p=function(_12q,_12r,_12s,_12t,_12u,_12v,_12w,_12x,_12y){var _12z=new T(function(){if(!E(_12r)){return E(_12s);}else{return false;}}),_12A=new T(function(){if(!E(_12r)){return false;}else{return E(E(_12x).g);}}),_12B=new T(function(){if(!E(_12A)){if(!E(_12z)){return B(A2(_lj,_12q,_lr));}else{return B(A3(_qF,_12q,new T(function(){return B(A3(_qF,_12q,_12v,_12w));}),new T(function(){return B(A2(_lj,_12q,_104));})));}}else{return B(A3(_qF,_12q,_12v,_12w));}}),_12C=new T(function(){if(!E(_12A)){if(!E(_12z)){return __Z;}else{var _12D=E(_12t)+1|0;if(0>=_12D){return __Z;}else{return B(_uj(_12D,_12u));}}}else{return B(_12b(B(_12n(_12y)),new T(function(){return E(B(_11P(E(_12y).m)).a);},1),new T(function(){return E(_12y).n;},1)));}});return new T4(0,_12A,_12z,_12C,_12B);},_12E=function(_12F,_12G,_12H){var _12I=E(_12G),_12J=E(_12H),_12K=new T(function(){var _12L=B(_lf(_12F)),_12M=B(_12E(_12F,_12J,B(A3(_tc,_12L,new T(function(){return B(A3(_qF,_12L,_12J,_12J));}),_12I))));return new T2(1,_12M.a,_12M.b);});return new T2(0,_12I,_12K);},_12N=1,_12O=new T(function(){var _12P=B(_12E(_kg,_lR,_12N));return new T2(1,_12P.a,_12P.b);}),_12Q=function(_12R,_12S,_12T,_12U,_12V,_12W,_12X,_12Y,_12Z,_130,_131,_132,_133,_134,_135,_136,_137,_138,_139,_13a,_13b,_13c,_13d,_13e,_13f,_13g,_13h,_13i,_13j,_13k,_13l,_13m,_13n,_13o,_13p,_13q,_){var _13r={_:0,a:E(_13h),b:E(_13i),c:E(_13j),d:E(_13k),e:E(_13l),f:E(_13m),g:E(_13n),h:E(_13o),i:E(_13p)};if(!E(_13j)){return {_:0,a:E(_12V),b:E(new T2(0,_12W,_12X)),c:E(_12Y),d:E(_12Z),e:E(_130),f:E(_131),g:E(_132),h:E(new T2(0,_133,_134)),i:_135,j:_136,k:_137,l:_138,m:E(_139),n:_13a,o:E(_13b),p:E(_13c),q:_13d,r:E(_13e),s:E(_13f),t:_13g,u:E(_13r),v:E(_13q)};}else{if(!E(_13k)){var _13s=B(_105(_fX,_12S,_12T,_13r,{_:0,a:E(_12V),b:E(new T2(0,_12W,_12X)),c:E(_12Y),d:E(_12Z),e:E(_130),f:E(_131),g:E(_132),h:E(new T2(0,_133,_134)),i:_135,j:_136,k:_137,l:_138,m:E(_139),n:_13a,o:E(_13b),p:E(_13c),q:_13d,r:E(_13e),s:E(_13f),t:_13g,u:E(_13r),v:E(_13q)})),_13t=_13s.d,_13u=_13s.e,_13v=_13s.f,_13w=_13s.i,_13x=_13s.n,_13y=_13s.p,_13z=_13s.q,_13A=_13s.s,_13B=_13s.t;if(!E(_13s.o)){var _13C=B(_12p(_fs,_13y,_13z,_13s.g,_13s.h,_13s.k,_13s.m,_13s.r,_13A)),_13D=_13C.c,_13E=_13C.d,_13F=function(_){var _13G=function(_){if(!E(_13y)){if(!E(_13z)){var _13H=B(_mG(E(_12R).a,_13w,_na,_lR,_13s.b,_13s.c,_13s.a,_));return _13B;}else{return _13B;}}else{return _13B;}};if(!E(_13C.b)){return new F(function(){return _13G(_);});}else{var _13I=E(_12R),_13J=_13I.a,_13K=_13I.b,_13L=B(_se(_13J,_13K,_12S,_13s.l,_12U,_13A,_)),_13M=B(_pt(_13J,_13K,_12T,0,_13v,_13E,_13v,_13D,_));return new F(function(){return _13G(_);});}};if(!E(_13C.a)){return new F(function(){return _13F(_);});}else{var _13N=B(_nf(_12R,_12T,0,_13v,_13E,_13v,_13D,_));return new F(function(){return _13F(_);});}}else{var _13O=E(_13s.j);if(!_13O._){return _13B;}else{var _13P=E(_12O);if(!_13P._){return _13B;}else{var _13Q=E(_12R).a,_13R=B(_mG(_13Q,_13w,_13x,_13P.a,_13t,_13u,_13O.a,_)),_13S=function(_13T,_13U,_){while(1){var _13V=E(_13T);if(!_13V._){return _kJ;}else{var _13W=E(_13U);if(!_13W._){return _kJ;}else{var _13X=B(_mG(_13Q,_13w,_13x,_13W.a,_13t,_13u,_13V.a,_));_13T=_13V.b;_13U=_13W.b;continue;}}}},_13Y=B(_13S(_13O.b,_13P.b,_));return _13B;}}}}else{return {_:0,a:E(_12V),b:E(new T2(0,_12W,_12X)),c:E(_12Y),d:E(_12Z),e:E(_130),f:E(_131),g:E(_132),h:E(new T2(0,_133,_134)),i:_135,j:_136,k:_137,l:_138,m:E(_139),n:_13a,o:E(_13b),p:E(_13c),q:_13d,r:E(_13e),s:E(_13f),t:_13g,u:E(_13r),v:E(_13q)};}}},_13Z=function(_140,_141,_142,_143,_144,_145,_146,_147,_148,_149,_14a,_14b,_14c,_14d,_14e,_14f,_14g,_14h,_14i,_14j,_14k,_14l,_14m,_14n,_14o,_14p,_14q,_14r,_14s,_14t,_14u,_14v,_14w,_14x,_14y,_14z,_){while(1){var _14A=B(_12Q(_140,_141,_142,_143,_144,_145,_146,_147,_148,_149,_14a,_14b,_14c,_14d,_14e,_14f,_14g,_14h,_14i,_14j,_14k,_14l,_14m,_14n,_14o,_14p,_14q,_14r,_14s,_14t,_14u,_14v,_14w,_14x,_14y,_14z,_)),_14B=E(_14A),_14C=_14B.a,_14D=_14B.c,_14E=_14B.d,_14F=_14B.e,_14G=_14B.f,_14H=_14B.g,_14I=_14B.i,_14J=_14B.j,_14K=_14B.k,_14L=_14B.l,_14M=_14B.m,_14N=_14B.n,_14O=_14B.o,_14P=_14B.p,_14Q=_14B.q,_14R=_14B.r,_14S=_14B.s,_14T=_14B.t,_14U=_14B.v,_14V=E(_14B.u),_14W=_14V.a,_14X=_14V.b,_14Y=_14V.c,_14Z=_14V.e,_150=_14V.g,_151=_14V.h,_152=_14V.i,_153=E(_14B.b),_154=E(_14B.h);if(!E(_14V.d)){if(!E(_14s)){return {_:0,a:E(_14C),b:E(_153),c:E(_14D),d:E(_14E),e:E(_14F),f:E(_14G),g:E(_14H),h:E(_154),i:_14I,j:_14J,k:_14K,l:_14L,m:E(_14M),n:_14N,o:E(_14O),p:E(_14P),q:_14Q,r:E(_14R),s:E(_14S),t:_14T,u:E({_:0,a:E(_14W),b:E(_14X),c:E(_14Y),d:E(_B2),e:E(_14Z),f:E(_B2),g:E(_150),h:E(_151),i:E(_152)}),v:E(_14U)};}else{_144=_14C;_145=_153.a;_146=_153.b;_147=_14D;_148=_14E;_149=_14F;_14a=_14G;_14b=_14H;_14c=_154.a;_14d=_154.b;_14e=_14I;_14f=_14J;_14g=_14K;_14h=_14L;_14i=_14M;_14j=_14N;_14k=_14O;_14l=_14P;_14m=_14Q;_14n=_14R;_14o=_14S;_14p=_14T;_14q=_14W;_14r=_14X;_14s=_14Y;_14t=_B2;_14u=_14Z;_14v=_14V.f;_14w=_150;_14x=_151;_14y=_152;_14z=_14U;continue;}}else{return {_:0,a:E(_14C),b:E(_153),c:E(_14D),d:E(_14E),e:E(_14F),f:E(_14G),g:E(_14H),h:E(_154),i:_14I,j:_14J,k:_14K,l:_14L,m:E(_14M),n:_14N,o:E(_14O),p:E(_14P),q:_14Q,r:E(_14R),s:E(_14S),t:_14T,u:E({_:0,a:E(_14W),b:E(_14X),c:E(_14Y),d:E(_B3),e:E(_14Z),f:E(_B2),g:E(_150),h:E(_151),i:E(_152)}),v:E(_14U)};}}},_155=function(_156,_157,_158,_159,_15a,_15b,_15c,_15d,_15e,_15f,_15g,_15h,_15i,_15j,_15k,_15l,_15m,_15n,_15o,_15p,_15q,_15r,_15s,_15t,_15u,_15v,_15w,_15x,_15y,_15z,_15A,_15B,_15C,_15D,_15E,_){var _15F=B(_12Q(_156,_157,_158,_159,_15a,_15b,_15c,_15d,_15e,_15f,_15g,_15h,_15i,_15j,_15k,_15l,_15m,_15n,_15o,_15p,_15q,_15r,_15s,_15t,_15u,_15v,_15w,_15x,_B3,_15y,_15z,_15A,_15B,_15C,_15D,_15E,_)),_15G=E(_15F),_15H=_15G.a,_15I=_15G.c,_15J=_15G.d,_15K=_15G.e,_15L=_15G.f,_15M=_15G.g,_15N=_15G.i,_15O=_15G.j,_15P=_15G.k,_15Q=_15G.l,_15R=_15G.m,_15S=_15G.n,_15T=_15G.o,_15U=_15G.p,_15V=_15G.q,_15W=_15G.r,_15X=_15G.s,_15Y=_15G.t,_15Z=_15G.v,_160=E(_15G.u),_161=_160.a,_162=_160.b,_163=_160.c,_164=_160.e,_165=_160.g,_166=_160.h,_167=_160.i,_168=E(_15G.b),_169=E(_15G.h);if(!E(_160.d)){return new F(function(){return _13Z(_156,_157,_158,_159,_15H,_168.a,_168.b,_15I,_15J,_15K,_15L,_15M,_169.a,_169.b,_15N,_15O,_15P,_15Q,_15R,_15S,_15T,_15U,_15V,_15W,_15X,_15Y,_161,_162,_163,_B2,_164,_160.f,_165,_166,_167,_15Z,_);});}else{return {_:0,a:E(_15H),b:E(_168),c:E(_15I),d:E(_15J),e:E(_15K),f:E(_15L),g:E(_15M),h:E(_169),i:_15N,j:_15O,k:_15P,l:_15Q,m:E(_15R),n:_15S,o:E(_15T),p:E(_15U),q:_15V,r:E(_15W),s:E(_15X),t:_15Y,u:E({_:0,a:E(_161),b:E(_162),c:E(_163),d:E(_B3),e:E(_164),f:E(_B2),g:E(_165),h:E(_166),i:E(_167)}),v:E(_15Z)};}},_16a=function(_16b){var _16c=E(_16b);if(!_16c._){return __Z;}else{var _16d=E(_16c.b);return (_16d._==0)?__Z:new T2(1,new T2(0,_16c.a,_16d.a),new T(function(){return B(_16a(_16d.b));}));}},_16e=function(_16f,_16g,_16h){return new T2(1,new T2(0,_16f,_16g),new T(function(){return B(_16a(_16h));}));},_16i=function(_16j,_16k){var _16l=E(_16k);return (_16l._==0)?__Z:new T2(1,new T2(0,_16j,_16l.a),new T(function(){return B(_16a(_16l.b));}));},_16m="Invalid JSON!",_16n=new T1(0,_16m),_16o="No such value",_16p=new T1(0,_16o),_16q=new T(function(){return eval("(function(k) {return localStorage.getItem(k);})");}),_16r=function(_16s){return E(E(_16s).c);},_16t=function(_16u,_16v,_){var _16w=__app1(E(_16q),_16v),_16x=__eq(_16w,E(_3h));if(!E(_16x)){var _16y=__isUndef(_16w);return (E(_16y)==0)?new T(function(){var _16z=String(_16w),_16A=jsParseJSON(_16z);if(!_16A._){return E(_16n);}else{return B(A2(_16r,_16u,_16A.a));}}):_16p;}else{return _16p;}},_16B=new T1(0,0),_16C=function(_16D,_16E){while(1){var _16F=E(_16D);if(!_16F._){var _16G=_16F.a,_16H=E(_16E);if(!_16H._){return new T1(0,(_16G>>>0|_16H.a>>>0)>>>0&4294967295);}else{_16D=new T1(1,I_fromInt(_16G));_16E=_16H;continue;}}else{var _16I=E(_16E);if(!_16I._){_16D=_16F;_16E=new T1(1,I_fromInt(_16I.a));continue;}else{return new T1(1,I_or(_16F.a,_16I.a));}}}},_16J=function(_16K){var _16L=E(_16K);if(!_16L._){return E(_16B);}else{return new F(function(){return _16C(new T1(0,E(_16L.a)),B(_gT(B(_16J(_16L.b)),31)));});}},_16M=function(_16N,_16O){if(!E(_16N)){return new F(function(){return _jy(B(_16J(_16O)));});}else{return new F(function(){return _16J(_16O);});}},_16P=1420103680,_16Q=465,_16R=new T2(1,_16Q,_Z),_16S=new T2(1,_16P,_16R),_16T=new T(function(){return B(_16M(_B3,_16S));}),_16U=function(_16V){return E(_16T);},_16W=new T(function(){return B(unCStr("s"));}),_16X=function(_16Y,_16Z){while(1){var _170=E(_16Y);if(!_170._){return E(_16Z);}else{_16Y=_170.b;_16Z=_170.a;continue;}}},_171=function(_172,_173,_174){return new F(function(){return _16X(_173,_172);});},_175=new T1(0,1),_176=function(_177,_178){var _179=E(_177);return new T2(0,_179,new T(function(){var _17a=B(_176(B(_gA(_179,_178)),_178));return new T2(1,_17a.a,_17a.b);}));},_17b=function(_17c){var _17d=B(_176(_17c,_175));return new T2(1,_17d.a,_17d.b);},_17e=function(_17f,_17g){var _17h=B(_176(_17f,new T(function(){return B(_iT(_17g,_17f));})));return new T2(1,_17h.a,_17h.b);},_17i=new T1(0,0),_17j=function(_17k,_17l){var _17m=E(_17k);if(!_17m._){var _17n=_17m.a,_17o=E(_17l);return (_17o._==0)?_17n>=_17o.a:I_compareInt(_17o.a,_17n)<=0;}else{var _17p=_17m.a,_17q=E(_17l);return (_17q._==0)?I_compareInt(_17p,_17q.a)>=0:I_compare(_17p,_17q.a)>=0;}},_17r=function(_17s,_17t,_17u){if(!B(_17j(_17t,_17i))){var _17v=function(_17w){return (!B(_hc(_17w,_17u)))?new T2(1,_17w,new T(function(){return B(_17v(B(_gA(_17w,_17t))));})):__Z;};return new F(function(){return _17v(_17s);});}else{var _17x=function(_17y){return (!B(_h3(_17y,_17u)))?new T2(1,_17y,new T(function(){return B(_17x(B(_gA(_17y,_17t))));})):__Z;};return new F(function(){return _17x(_17s);});}},_17z=function(_17A,_17B,_17C){return new F(function(){return _17r(_17A,B(_iT(_17B,_17A)),_17C);});},_17D=function(_17E,_17F){return new F(function(){return _17r(_17E,_175,_17F);});},_17G=function(_17H){return new F(function(){return _ff(_17H);});},_17I=function(_17J){return new F(function(){return _iT(_17J,_175);});},_17K=function(_17L){return new F(function(){return _gA(_17L,_175);});},_17M=function(_17N){return new F(function(){return _eW(E(_17N));});},_17O={_:0,a:_17K,b:_17I,c:_17M,d:_17G,e:_17b,f:_17e,g:_17D,h:_17z},_17P=function(_17Q,_17R){while(1){var _17S=E(_17Q);if(!_17S._){var _17T=E(_17S.a);if(_17T==( -2147483648)){_17Q=new T1(1,I_fromInt( -2147483648));continue;}else{var _17U=E(_17R);if(!_17U._){return new T1(0,B(_do(_17T,_17U.a)));}else{_17Q=new T1(1,I_fromInt(_17T));_17R=_17U;continue;}}}else{var _17V=_17S.a,_17W=E(_17R);return (_17W._==0)?new T1(1,I_div(_17V,I_fromInt(_17W.a))):new T1(1,I_div(_17V,_17W.a));}}},_17X=function(_17Y,_17Z){if(!B(_gs(_17Z,_tg))){return new F(function(){return _17P(_17Y,_17Z);});}else{return E(_dZ);}},_180=function(_181,_182){while(1){var _183=E(_181);if(!_183._){var _184=E(_183.a);if(_184==( -2147483648)){_181=new T1(1,I_fromInt( -2147483648));continue;}else{var _185=E(_182);if(!_185._){var _186=_185.a;return new T2(0,new T1(0,B(_do(_184,_186))),new T1(0,B(_et(_184,_186))));}else{_181=new T1(1,I_fromInt(_184));_182=_185;continue;}}}else{var _187=E(_182);if(!_187._){_181=_183;_182=new T1(1,I_fromInt(_187.a));continue;}else{var _188=I_divMod(_183.a,_187.a);return new T2(0,new T1(1,_188.a),new T1(1,_188.b));}}}},_189=function(_18a,_18b){if(!B(_gs(_18b,_tg))){var _18c=B(_180(_18a,_18b));return new T2(0,_18c.a,_18c.b);}else{return E(_dZ);}},_18d=function(_18e,_18f){while(1){var _18g=E(_18e);if(!_18g._){var _18h=E(_18g.a);if(_18h==( -2147483648)){_18e=new T1(1,I_fromInt( -2147483648));continue;}else{var _18i=E(_18f);if(!_18i._){return new T1(0,B(_et(_18h,_18i.a)));}else{_18e=new T1(1,I_fromInt(_18h));_18f=_18i;continue;}}}else{var _18j=_18g.a,_18k=E(_18f);return (_18k._==0)?new T1(1,I_mod(_18j,I_fromInt(_18k.a))):new T1(1,I_mod(_18j,_18k.a));}}},_18l=function(_18m,_18n){if(!B(_gs(_18n,_tg))){return new F(function(){return _18d(_18m,_18n);});}else{return E(_dZ);}},_18o=function(_18p,_18q){while(1){var _18r=E(_18p);if(!_18r._){var _18s=E(_18r.a);if(_18s==( -2147483648)){_18p=new T1(1,I_fromInt( -2147483648));continue;}else{var _18t=E(_18q);if(!_18t._){return new T1(0,quot(_18s,_18t.a));}else{_18p=new T1(1,I_fromInt(_18s));_18q=_18t;continue;}}}else{var _18u=_18r.a,_18v=E(_18q);return (_18v._==0)?new T1(0,I_toInt(I_quot(_18u,I_fromInt(_18v.a)))):new T1(1,I_quot(_18u,_18v.a));}}},_18w=function(_18x,_18y){if(!B(_gs(_18y,_tg))){return new F(function(){return _18o(_18x,_18y);});}else{return E(_dZ);}},_18z=function(_18A,_18B){if(!B(_gs(_18B,_tg))){var _18C=B(_gJ(_18A,_18B));return new T2(0,_18C.a,_18C.b);}else{return E(_dZ);}},_18D=function(_18E,_18F){while(1){var _18G=E(_18E);if(!_18G._){var _18H=E(_18G.a);if(_18H==( -2147483648)){_18E=new T1(1,I_fromInt( -2147483648));continue;}else{var _18I=E(_18F);if(!_18I._){return new T1(0,_18H%_18I.a);}else{_18E=new T1(1,I_fromInt(_18H));_18F=_18I;continue;}}}else{var _18J=_18G.a,_18K=E(_18F);return (_18K._==0)?new T1(1,I_rem(_18J,I_fromInt(_18K.a))):new T1(1,I_rem(_18J,_18K.a));}}},_18L=function(_18M,_18N){if(!B(_gs(_18N,_tg))){return new F(function(){return _18D(_18M,_18N);});}else{return E(_dZ);}},_18O=function(_18P){return E(_18P);},_18Q=function(_18R){return E(_18R);},_18S=function(_18T){var _18U=E(_18T);if(!_18U._){var _18V=E(_18U.a);return (_18V==( -2147483648))?E(_jx):(_18V<0)?new T1(0, -_18V):E(_18U);}else{var _18W=_18U.a;return (I_compareInt(_18W,0)>=0)?E(_18U):new T1(1,I_negate(_18W));}},_18X=new T1(0, -1),_18Y=function(_18Z){var _190=E(_18Z);if(!_190._){var _191=_190.a;return (_191>=0)?(E(_191)==0)?E(_16B):E(_hb):E(_18X);}else{var _192=I_compareInt(_190.a,0);return (_192<=0)?(E(_192)==0)?E(_16B):E(_18X):E(_hb);}},_193={_:0,a:_gA,b:_iT,c:_sK,d:_jy,e:_18S,f:_18Y,g:_18Q},_194=function(_195,_196){var _197=E(_195);if(!_197._){var _198=_197.a,_199=E(_196);return (_199._==0)?_198!=_199.a:(I_compareInt(_199.a,_198)==0)?false:true;}else{var _19a=_197.a,_19b=E(_196);return (_19b._==0)?(I_compareInt(_19a,_19b.a)==0)?false:true:(I_compare(_19a,_19b.a)==0)?false:true;}},_19c=new T2(0,_gs,_194),_19d=function(_19e,_19f){return (!B(_iE(_19e,_19f)))?E(_19e):E(_19f);},_19g=function(_19h,_19i){return (!B(_iE(_19h,_19i)))?E(_19i):E(_19h);},_19j={_:0,a:_19c,b:_gc,c:_hc,d:_iE,e:_h3,f:_17j,g:_19d,h:_19g},_19k=function(_19l){return new T2(0,E(_19l),E(_f0));},_19m=new T3(0,_193,_19j,_19k),_19n={_:0,a:_19m,b:_17O,c:_18w,d:_18L,e:_17X,f:_18l,g:_18z,h:_189,i:_18O},_19o=new T1(0,0),_19p=function(_19q,_19r,_19s){var _19t=B(A1(_19q,_19r));if(!B(_gs(_19t,_19o))){return new F(function(){return _17P(B(_sK(_19r,_19s)),_19t);});}else{return E(_dZ);}},_19u=function(_19v,_19w){while(1){if(!B(_gs(_19w,_tg))){var _19x=_19w,_19y=B(_18L(_19v,_19w));_19v=_19x;_19w=_19y;continue;}else{return E(_19v);}}},_19z=5,_19A=new T(function(){return B(_dV(_19z));}),_19B=new T(function(){return die(_19A);}),_19C=function(_19D,_19E){if(!B(_gs(_19E,_tg))){var _19F=B(_19u(B(_18S(_19D)),B(_18S(_19E))));return (!B(_gs(_19F,_tg)))?new T2(0,B(_18o(_19D,_19F)),B(_18o(_19E,_19F))):E(_dZ);}else{return E(_19B);}},_19G=function(_19H,_19I,_19J,_19K){var _19L=B(_sK(_19I,_19J));return new F(function(){return _19C(B(_sK(B(_sK(_19H,_19K)),B(_18Y(_19L)))),B(_18S(_19L)));});},_19M=function(_19N,_19O,_19P){var _19Q=new T(function(){if(!B(_gs(_19P,_tg))){var _19R=B(_gJ(_19O,_19P));return new T2(0,_19R.a,_19R.b);}else{return E(_dZ);}}),_19S=new T(function(){return B(A2(_lj,B(_sz(B(_sx(_19N)))),new T(function(){return E(E(_19Q).a);})));});return new T2(0,_19S,new T(function(){return new T2(0,E(E(_19Q).b),E(_19P));}));},_19T=function(_19U,_19V,_19W){var _19X=B(_19M(_19U,_19V,_19W)),_19Y=_19X.a,_19Z=E(_19X.b);if(!B(_hc(B(_sK(_19Z.a,_f0)),B(_sK(_tg,_19Z.b))))){return E(_19Y);}else{var _1a0=B(_sz(B(_sx(_19U))));return new F(function(){return A3(_tc,_1a0,_19Y,new T(function(){return B(A2(_lj,_1a0,_f0));}));});}},_1a1=479723520,_1a2=40233135,_1a3=new T2(1,_1a2,_Z),_1a4=new T2(1,_1a1,_1a3),_1a5=new T(function(){return B(_16M(_B3,_1a4));}),_1a6=new T1(0,40587),_1a7=function(_1a8){var _1a9=new T(function(){var _1aa=B(_19G(_1a8,_f0,_16T,_f0)),_1ab=B(_19G(_1a5,_f0,_16T,_f0)),_1ac=B(_19G(_1aa.a,_1aa.b,_1ab.a,_1ab.b));return B(_19T(_19n,_1ac.a,_1ac.b));});return new T2(0,new T(function(){return B(_gA(_1a6,_1a9));}),new T(function(){return B(_iT(_1a8,B(_19p(_16U,B(_sK(_1a9,_16T)),_1a5))));}));},_1ad=function(_1ae,_){var _1af=__get(_1ae,0),_1ag=__get(_1ae,1),_1ah=Number(_1af),_1ai=jsTrunc(_1ah),_1aj=Number(_1ag),_1ak=jsTrunc(_1aj);return new T2(0,_1ai,_1ak);},_1al=new T(function(){return eval("(function(){var ms = new Date().getTime();                   return [(ms/1000)|0, ((ms % 1000)*1000)|0];})");}),_1am=660865024,_1an=465661287,_1ao=new T2(1,_1an,_Z),_1ap=new T2(1,_1am,_1ao),_1aq=new T(function(){return B(_16M(_B3,_1ap));}),_1ar=function(_){var _1as=__app0(E(_1al)),_1at=B(_1ad(_1as,_));return new T(function(){var _1au=E(_1at);if(!B(_gs(_1aq,_19o))){return B(_gA(B(_sK(B(_eW(E(_1au.a))),_16T)),B(_17P(B(_sK(B(_sK(B(_eW(E(_1au.b))),_16T)),_16T)),_1aq))));}else{return E(_dZ);}});},_1av=new T(function(){return B(err(_x2));}),_1aw=new T(function(){return B(err(_wY));}),_1ax=new T(function(){return B(A3(_K8,_KB,_Id,_K0));}),_1ay=new T1(0,1),_1az=new T1(0,10),_1aA=function(_1aB){while(1){var _1aC=E(_1aB);if(!_1aC._){_1aB=new T1(1,I_fromInt(_1aC.a));continue;}else{return new F(function(){return I_toString(_1aC.a);});}}},_1aD=function(_1aE,_1aF){return new F(function(){return _x(fromJSStr(B(_1aA(_1aE))),_1aF);});},_1aG=new T1(0,0),_1aH=function(_1aI,_1aJ,_1aK){if(_1aI<=6){return new F(function(){return _1aD(_1aJ,_1aK);});}else{if(!B(_hc(_1aJ,_1aG))){return new F(function(){return _1aD(_1aJ,_1aK);});}else{return new T2(1,_G,new T(function(){return B(_x(fromJSStr(B(_1aA(_1aJ))),new T2(1,_F,_1aK)));}));}}},_1aL=function(_1aM){return new F(function(){return _1aH(0,_1aM,_Z);});},_1aN=new T(function(){return B(_gs(_1az,_19o));}),_1aO=function(_1aP){while(1){if(!B(_gs(_1aP,_19o))){if(!E(_1aN)){if(!B(_gs(B(_18d(_1aP,_1az)),_19o))){return new F(function(){return _1aL(_1aP);});}else{var _1aQ=B(_17P(_1aP,_1az));_1aP=_1aQ;continue;}}else{return E(_dZ);}}else{return __Z;}}},_1aR=46,_1aS=48,_1aT=function(_1aU,_1aV,_1aW){if(!B(_hc(_1aW,_19o))){var _1aX=B(A1(_1aU,_1aW));if(!B(_gs(_1aX,_19o))){var _1aY=B(_180(_1aW,_1aX)),_1aZ=_1aY.b,_1b0=new T(function(){var _1b1=Math.log(B(_jR(_1aX)))/Math.log(10),_1b2=_1b1&4294967295,_1b3=function(_1b4){if(_1b4>=0){var _1b5=E(_1b4);if(!_1b5){var _1b6=B(_17P(B(_iT(B(_gA(B(_sK(_1aZ,_f0)),_1aX)),_1ay)),_1aX));}else{var _1b6=B(_17P(B(_iT(B(_gA(B(_sK(_1aZ,B(_t0(_1az,_1b5)))),_1aX)),_1ay)),_1aX));}var _1b7=function(_1b8){var _1b9=B(_1aH(0,_1b6,_Z)),_1ba=_1b4-B(_qy(_1b9,0))|0;if(0>=_1ba){if(!E(_1aV)){return E(_1b9);}else{return new F(function(){return _1aO(_1b6);});}}else{var _1bb=new T(function(){if(!E(_1aV)){return E(_1b9);}else{return B(_1aO(_1b6));}}),_1bc=function(_1bd){var _1be=E(_1bd);return (_1be==1)?E(new T2(1,_1aS,_1bb)):new T2(1,_1aS,new T(function(){return B(_1bc(_1be-1|0));}));};return new F(function(){return _1bc(_1ba);});}};if(!E(_1aV)){var _1bf=B(_1b7(_));return (_1bf._==0)?__Z:new T2(1,_1aR,_1bf);}else{if(!B(_gs(_1b6,_19o))){var _1bg=B(_1b7(_));return (_1bg._==0)?__Z:new T2(1,_1aR,_1bg);}else{return __Z;}}}else{return E(_tW);}};if(_1b2>=_1b1){return B(_1b3(_1b2));}else{return B(_1b3(_1b2+1|0));}},1);return new F(function(){return _x(B(_1aH(0,_1aY.a,_Z)),_1b0);});}else{return E(_dZ);}}else{return new F(function(){return unAppCStr("-",new T(function(){return B(_1aT(_1aU,_1aV,B(_jy(_1aW))));}));});}},_1bh=function(_1bi,_1bj,_){var _1bk=B(_1ar(_)),_1bl=new T(function(){var _1bm=new T(function(){var _1bn=new T(function(){var _1bo=B(_x(B(_1aT(_16U,_B3,B(_1a7(_1bk)).b)),_16W));if(!_1bo._){return E(_Yl);}else{var _1bp=B(_Yg(_1bo.a,_1bo.b));if(!_1bp._){return B(_171(_Z,_Z,_ZZ));}else{var _1bq=_1bp.a,_1br=E(_1bp.b);if(!_1br._){return B(_171(new T2(1,_1bq,_Z),_Z,_ZZ));}else{var _1bs=E(_1bq),_1bt=new T(function(){var _1bu=B(_LC(46,_1br.a,_1br.b));return new T2(0,_1bu.a,_1bu.b);});if(E(_1bs)==46){return B(_171(_Z,new T2(1,new T(function(){return E(E(_1bt).a);}),new T(function(){return E(E(_1bt).b);})),_ZZ));}else{return B(_171(new T2(1,_1bs,new T(function(){return E(E(_1bt).a);})),new T(function(){return E(E(_1bt).b);}),_ZZ));}}}}}),_1bv=B(_KK(B(_x7(_1ax,_1bn))));if(!_1bv._){return E(_1aw);}else{if(!E(_1bv.b)._){return B(_uj(3,B(_H(0,E(_1bv.a)+(imul(E(_1bj),E(_1bi)-1|0)|0)|0,_Z))));}else{return E(_1av);}}}),_1bw=B(_KK(B(_x7(_1ax,_1bm))));if(!_1bw._){return E(_1aw);}else{if(!E(_1bw.b)._){return E(_1bw.a);}else{return E(_1av);}}});return new T2(0,new T(function(){return B(_eA(_1bl,_1bi));}),_1bl);},_1bx=function(_1by,_1bz,_1bA,_1bB,_1bC,_1bD,_){var _1bE=function(_1bF,_){return new F(function(){return _rT(_s9,_s9,function(_1bG,_){return new F(function(){return _s3(B(_aW(_1bz,E(_1bD))),0,0,E(_1bG),_);});},E(_1bF),_);});};return new F(function(){return _kX(new T(function(){return E(_1bA)-E(_1bB)*16;},1),new T(function(){return E(_1bC)*20;},1),_1bE,_1by,_);});},_1bH=1,_1bI=new T(function(){return B(_aW(_n9,1));}),_1bJ=function(_1bK){return E(_1bK).d;},_1bL=function(_1bM,_1bN,_1bO,_1bP,_1bQ,_1bR,_){var _1bS=new T(function(){return E(E(_1bR).s);}),_1bT=new T(function(){return E(E(_1bS).a);}),_1bU=new T(function(){if(!B(_et(E(_1bR).t,10))){var _1bV=E(E(_1bS).b);if(!(_1bV%2)){return _1bV+1|0;}else{return _1bV-1|0;}}else{return E(E(_1bS).b);}}),_1bW=new T(function(){var _1bX=E(_1bR);return {_:0,a:E(_1bX.a),b:E(_1bX.b),c:E(_1bX.c),d:E(_1bX.d),e:E(_1bX.e),f:E(_1bX.f),g:E(_1bX.g),h:E(_1bX.h),i:_1bX.i,j:_1bX.j,k:_1bX.k,l:_1bX.l,m:E(_1bX.m),n:_1bX.n,o:E(_1bX.o),p:E(_1bX.p),q:_1bX.q,r:E(_1bX.r),s:E(new T2(0,_1bT,_1bU)),t:_1bX.t,u:E(_1bX.u),v:E(_1bX.v)};}),_1bY=new T(function(){return E(E(_1bW).a);}),_1bZ=new T(function(){return E(E(_1bW).b);}),_1c0=new T(function(){return E(E(_1bZ).a);}),_1c1=new T(function(){var _1c2=E(_1bO)/16,_1c3=_1c2&4294967295;if(_1c2>=_1c3){return _1c3-2|0;}else{return (_1c3-1|0)-2|0;}}),_1c4=B(_rv(_1bM,_1bN,new T(function(){return B(_f9(_1c1,_1c0));}),_sd,new T(function(){return E(E(_1bY).b);}),_)),_1c5=new T(function(){return E(E(E(_1bW).a).a);}),_1c6=B(A(_qT,[_1bM,new T(function(){if(E(E(_1bY).e)==32){return E(_sb);}else{return E(_sc);}}),new T(function(){return ((E(E(_1c5).a)+E(_1c1)|0)-E(_1c0)|0)+1|0;},1),new T(function(){return (E(E(_1c5).b)+2|0)+1|0;},1),new T2(1,new T(function(){return B(_1bJ(_1bY));}),_Z),_])),_1c7=E(_1bW),_1c8=_1c7.c,_1c9=_1c7.k,_1ca=E(_1c7.u),_1cb=new T(function(){var _1cc=E(_1bO)/28,_1cd=_1cc&4294967295;if(_1cc>=_1cd){return (_1cd-1|0)+_1c9|0;}else{return ((_1cd-1|0)-1|0)+_1c9|0;}}),_1ce=new T(function(){return (2+E(E(_1bZ).b)|0)+2|0;}),_1cf=new T2(0,_1bM,_1bN),_1cg=function(_){var _1ch=function(_){var _1ci=function(_){var _1cj=B(_1bx(_1bM,new T(function(){return E(E(_1bQ).b);},1),_1bO,new T(function(){return E(_1c0)+10|0;},1),_sd,new T(function(){return (imul(E(_1bT),8)|0)+E(_1bU)|0;},1),_));return _1c7;};if(!E(_1c7.p)._){return new F(function(){return _1ci(_);});}else{var _1ck=B(A(_qT,[_1bM,_1bI,_1bH,_1bH,B(_H(0,_1c7.q,_Z)),_]));return new F(function(){return _1ci(_);});}};if(!E(_1ca.g)){return new F(function(){return _1ch(_);});}else{var _1cl=B(_nf(_1cf,_1bP,0,_1ce,_1cb,_1ce,B(_12b(_1c8,new T(function(){return B(_aj(_wQ,_1c7.m));},1),_1c7.n)),_));return new F(function(){return _1ch(_);});}};if(!E(_1ca.c)){var _1cm=B(_nf(_1cf,_1bP,0,_1ce,_1cb,_1ce,_1c8,_));return new F(function(){return _1cg(_);});}else{return new F(function(){return _1cg(_);});}},_1cn=function(_1co,_1cp){while(1){var _1cq=E(_1cp);if(!_1cq._){return __Z;}else{var _1cr=_1cq.b,_1cs=E(_1co);if(_1cs==1){return E(_1cr);}else{_1co=_1cs-1|0;_1cp=_1cr;continue;}}}},_1ct=new T(function(){return B(unCStr("(Array.!): undefined array element"));}),_1cu=new T(function(){return B(err(_1ct));}),_1cv=0,_1cw=function(_1cx,_1cy,_1cz){return new F(function(){return _H(E(_1cx),E(_1cy),_1cz);});},_1cA=function(_1cB,_1cC){return new F(function(){return _H(0,E(_1cB),_1cC);});},_1cD=function(_1cE,_1cF){return new F(function(){return _2C(_1cA,_1cE,_1cF);});},_1cG=new T3(0,_1cw,_aG,_1cD),_1cH=0,_1cI=new T(function(){return B(unCStr(" out of range "));}),_1cJ=new T(function(){return B(unCStr("}.index: Index "));}),_1cK=new T(function(){return B(unCStr("Ix{"));}),_1cL=new T2(1,_F,_Z),_1cM=new T2(1,_F,_1cL),_1cN=0,_1cO=function(_1cP){return E(E(_1cP).a);},_1cQ=function(_1cR,_1cS,_1cT,_1cU,_1cV){var _1cW=new T(function(){var _1cX=new T(function(){var _1cY=new T(function(){var _1cZ=new T(function(){var _1d0=new T(function(){return B(A3(_wK,_aC,new T2(1,new T(function(){return B(A3(_1cO,_1cT,_1cN,_1cU));}),new T2(1,new T(function(){return B(A3(_1cO,_1cT,_1cN,_1cV));}),_Z)),_1cM));});return B(_x(_1cI,new T2(1,_G,new T2(1,_G,_1d0))));});return B(A(_1cO,[_1cT,_1cH,_1cS,new T2(1,_F,_1cZ)]));});return B(_x(_1cJ,new T2(1,_G,_1cY)));},1);return B(_x(_1cR,_1cX));},1);return new F(function(){return err(B(_x(_1cK,_1cW)));});},_1d1=function(_1d2,_1d3,_1d4,_1d5,_1d6){return new F(function(){return _1cQ(_1d2,_1d3,_1d6,_1d4,_1d5);});},_1d7=function(_1d8,_1d9,_1da,_1db){var _1dc=E(_1da);return new F(function(){return _1d1(_1d8,_1d9,_1dc.a,_1dc.b,_1db);});},_1dd=function(_1de,_1df,_1dg,_1dh){return new F(function(){return _1d7(_1dh,_1dg,_1df,_1de);});},_1di=new T(function(){return B(unCStr("Int"));}),_1dj=function(_1dk,_1dl,_1dm){return new F(function(){return _1dd(_1cG,new T2(0,_1dl,_1dm),_1dk,_1di);});},_1dn=new T(function(){return B(unCStr("Negative range size"));}),_1do=new T(function(){return B(err(_1dn));}),_1dp=function(_1dq){var _1dr=B(A1(_1dq,_));return E(_1dr);},_1ds=function(_1dt,_1du,_1dv,_){var _1dw=E(_1dt);if(!_1dw){return new T2(0,_Z,_1du);}else{var _1dx=new T(function(){return B(_qy(_1dv,0))-1|0;}),_1dy=B(_1bh(new T(function(){return E(_1dx)+1|0;}),_1du,_)),_1dz=E(_1dy),_1dA=_1dz.a,_1dB=_1dz.b,_1dC=new T(function(){var _1dD=E(_1dA);if(B(_qy(_1dv,0))>=(_1dD+1|0)){var _1dE=new T(function(){var _1dF=_1dD+1|0;if(_1dF>0){return B(_1cn(_1dF,_1dv));}else{return E(_1dv);}});if(0>=_1dD){return E(_1dE);}else{var _1dG=function(_1dH,_1dI){var _1dJ=E(_1dH);if(!_1dJ._){return E(_1dE);}else{var _1dK=_1dJ.a,_1dL=E(_1dI);return (_1dL==1)?new T2(1,_1dK,_1dE):new T2(1,_1dK,new T(function(){return B(_1dG(_1dJ.b,_1dL-1|0));}));}};return B(_1dG(_1dv,_1dD));}}else{return E(_1dv);}}),_1dM=B(_1ds(_1dw-1|0,_1dB,_1dC,_)),_1dN=new T(function(){var _1dO=function(_){var _1dP=E(_1dx),_1dQ=function(_1dR){if(_1dR>=0){var _1dS=newArr(_1dR,_1cu),_1dT=_1dS,_1dU=E(_1dR);if(!_1dU){return new T4(0,E(_1cv),E(_1dP),0,_1dT);}else{var _1dV=function(_1dW,_1dX,_){while(1){var _1dY=E(_1dW);if(!_1dY._){return E(_);}else{var _=_1dT[_1dX]=_1dY.a;if(_1dX!=(_1dU-1|0)){var _1dZ=_1dX+1|0;_1dW=_1dY.b;_1dX=_1dZ;continue;}else{return E(_);}}}},_=B(_1dV(_1dv,0,_));return new T4(0,E(_1cv),E(_1dP),_1dU,_1dT);}}else{return E(_1do);}};if(0>_1dP){return new F(function(){return _1dQ(0);});}else{return new F(function(){return _1dQ(_1dP+1|0);});}},_1e0=B(_1dp(_1dO)),_1e1=E(_1e0.a),_1e2=E(_1e0.b),_1e3=E(_1dA);if(_1e1>_1e3){return B(_1dj(_1e3,_1e1,_1e2));}else{if(_1e3>_1e2){return B(_1dj(_1e3,_1e1,_1e2));}else{return E(_1e0.d[_1e3-_1e1|0]);}}});return new T2(0,new T2(1,_1dN,new T(function(){return B(_wQ(_1dM));})),_1dB);}},_1e4=function(_1e5,_1e6){while(1){var _1e7=E(_1e5);if(!_1e7._){return E(_1e6);}else{_1e5=_1e7.b;_1e6=_1e7.a;continue;}}},_1e8=function(_1e9,_1ea,_1eb){return new F(function(){return _1e4(_1ea,_1e9);});},_1ec=function(_1ed,_1ee){while(1){var _1ef=E(_1ed);if(!_1ef._){return E(_1ee);}else{_1ed=_1ef.b;_1ee=_1ef.a;continue;}}},_1eg=function(_1eh,_1ei,_1ej){return new F(function(){return _1ec(_1ei,_1eh);});},_1ek=function(_1el,_1em){while(1){var _1en=E(_1em);if(!_1en._){return __Z;}else{var _1eo=_1en.b,_1ep=E(_1el);if(_1ep==1){return E(_1eo);}else{_1el=_1ep-1|0;_1em=_1eo;continue;}}}},_1eq=function(_1er,_1es){var _1et=new T(function(){var _1eu=_1er+1|0;if(_1eu>0){return B(_1ek(_1eu,_1es));}else{return E(_1es);}});if(0>=_1er){return E(_1et);}else{var _1ev=function(_1ew,_1ex){var _1ey=E(_1ew);if(!_1ey._){return E(_1et);}else{var _1ez=_1ey.a,_1eA=E(_1ex);return (_1eA==1)?new T2(1,_1ez,_1et):new T2(1,_1ez,new T(function(){return B(_1ev(_1ey.b,_1eA-1|0));}));}};return new F(function(){return _1ev(_1es,_1er);});}},_1eB=new T(function(){return B(unCStr(":"));}),_1eC=function(_1eD){var _1eE=E(_1eD);if(!_1eE._){return __Z;}else{var _1eF=new T(function(){return B(_x(_1eB,new T(function(){return B(_1eC(_1eE.b));},1)));},1);return new F(function(){return _x(_1eE.a,_1eF);});}},_1eG=function(_1eH,_1eI){var _1eJ=new T(function(){return B(_x(_1eB,new T(function(){return B(_1eC(_1eI));},1)));},1);return new F(function(){return _x(_1eH,_1eJ);});},_1eK=function(_1eL){return new F(function(){return _PU("Check.hs:173:7-35|(co : na : xs)");});},_1eM=new T(function(){return B(_1eK(_));}),_1eN=new T(function(){return B(err(_wY));}),_1eO=new T(function(){return B(err(_x2));}),_1eP=new T(function(){return B(A3(_K8,_KB,_Id,_K0));}),_1eQ=0,_1eR=new T(function(){return B(unCStr("!"));}),_1eS=function(_1eT,_1eU){var _1eV=E(_1eU);if(!_1eV._){return E(_1eM);}else{var _1eW=E(_1eV.b);if(!_1eW._){return E(_1eM);}else{var _1eX=E(_1eV.a),_1eY=new T(function(){var _1eZ=B(_LC(58,_1eW.a,_1eW.b));return new T2(0,_1eZ.a,_1eZ.b);}),_1f0=function(_1f1,_1f2,_1f3){var _1f4=function(_1f5){if((_1eT+1|0)!=_1f5){return new T3(0,_1eT+1|0,_1f2,_1eV);}else{var _1f6=E(_1f3);return (_1f6._==0)?new T3(0,_1eQ,_1f2,_Z):new T3(0,_1eQ,_1f2,new T(function(){var _1f7=B(_1eG(_1f6.a,_1f6.b));if(!_1f7._){return E(_Yl);}else{return B(_Yg(_1f7.a,_1f7.b));}}));}};if(!B(_vl(_1f1,_1eR))){var _1f8=B(_KK(B(_x7(_1eP,_1f1))));if(!_1f8._){return E(_1eN);}else{if(!E(_1f8.b)._){return new F(function(){return _1f4(E(_1f8.a));});}else{return E(_1eO);}}}else{return new F(function(){return _1f4( -1);});}};if(E(_1eX)==58){return new F(function(){return _1f0(_Z,new T(function(){return E(E(_1eY).a);}),new T(function(){return E(E(_1eY).b);}));});}else{var _1f9=E(_1eY),_1fa=E(_1f9.b);if(!_1fa._){return E(_1eM);}else{return new F(function(){return _1f0(new T2(1,_1eX,_1f9.a),_1fa.a,_1fa.b);});}}}}},_1fb=function(_1fc,_1fd){while(1){var _1fe=E(_1fd);if(!_1fe._){return __Z;}else{var _1ff=_1fe.b,_1fg=E(_1fc);if(_1fg==1){return E(_1ff);}else{_1fc=_1fg-1|0;_1fd=_1ff;continue;}}}},_1fh=function(_1fi,_1fj,_1fk){var _1fl=new T2(1,_1fj,new T(function(){var _1fm=_1fi+1|0;if(_1fm>0){return B(_1fb(_1fm,_1fk));}else{return E(_1fk);}}));if(0>=_1fi){return E(_1fl);}else{var _1fn=function(_1fo,_1fp){var _1fq=E(_1fo);if(!_1fq._){return E(_1fl);}else{var _1fr=_1fq.a,_1fs=E(_1fp);return (_1fs==1)?new T2(1,_1fr,_1fl):new T2(1,_1fr,new T(function(){return B(_1fn(_1fq.b,_1fs-1|0));}));}};return new F(function(){return _1fn(_1fk,_1fi);});}},_1ft=new T2(0,_XY,_II),_1fu=function(_1fv,_1fw,_1fx){while(1){var _1fy=E(_1fx);if(!_1fy._){return E(_1ft);}else{var _1fz=_1fy.b,_1fA=E(_1fy.a),_1fB=E(_1fA.a);if(_1fv!=E(_1fB.a)){_1fx=_1fz;continue;}else{if(_1fw!=E(_1fB.b)){_1fx=_1fz;continue;}else{return E(_1fA.b);}}}}},_1fC=function(_1fD,_1fE){while(1){var _1fF=E(_1fE);if(!_1fF._){return __Z;}else{var _1fG=_1fF.b,_1fH=E(_1fD);if(_1fH==1){return E(_1fG);}else{_1fD=_1fH-1|0;_1fE=_1fG;continue;}}}},_1fI=function(_1fJ,_1fK,_1fL){var _1fM=E(_1fJ);if(_1fM==1){return E(_1fL);}else{return new F(function(){return _1fC(_1fM-1|0,_1fL);});}},_1fN=function(_1fO,_1fP,_1fQ){return new T2(1,new T(function(){if(0>=_1fO){return __Z;}else{return B(_uj(_1fO,new T2(1,_1fP,_1fQ)));}}),new T(function(){if(_1fO>0){return B(_1fR(_1fO,B(_1fI(_1fO,_1fP,_1fQ))));}else{return B(_1fN(_1fO,_1fP,_1fQ));}}));},_1fR=function(_1fS,_1fT){var _1fU=E(_1fT);if(!_1fU._){return __Z;}else{var _1fV=_1fU.a,_1fW=_1fU.b;return new T2(1,new T(function(){if(0>=_1fS){return __Z;}else{return B(_uj(_1fS,_1fU));}}),new T(function(){if(_1fS>0){return B(_1fR(_1fS,B(_1fI(_1fS,_1fV,_1fW))));}else{return B(_1fN(_1fS,_1fV,_1fW));}}));}},_1fX=function(_1fY,_1fZ,_1g0){var _1g1=_1fZ-1|0;if(0<=_1g1){var _1g2=E(_1fY),_1g3=function(_1g4){var _1g5=new T(function(){if(_1g4!=_1g1){return B(_1g3(_1g4+1|0));}else{return __Z;}}),_1g6=function(_1g7){var _1g8=E(_1g7);return (_1g8._==0)?E(_1g5):new T2(1,new T(function(){var _1g9=E(_1g0);if(!_1g9._){return E(_1ft);}else{var _1ga=_1g9.b,_1gb=E(_1g9.a),_1gc=E(_1gb.a),_1gd=E(_1g8.a);if(_1gd!=E(_1gc.a)){return B(_1fu(_1gd,_1g4,_1ga));}else{if(_1g4!=E(_1gc.b)){return B(_1fu(_1gd,_1g4,_1ga));}else{return E(_1gb.b);}}}}),new T(function(){return B(_1g6(_1g8.b));}));};return new F(function(){return _1g6(B(_cx(0,_1g2-1|0)));});};return new F(function(){return _1fR(_1g2,B(_1g3(0)));});}else{return __Z;}},_1ge=function(_1gf){return new F(function(){return _PU("Check.hs:72:21-47|(l : r : _)");});},_1gg=new T(function(){return B(_1ge(_));}),_1gh=61,_1gi=function(_1gj,_1gk){while(1){var _1gl=E(_1gj);if(!_1gl._){return E(_1gk);}else{_1gj=_1gl.b;_1gk=_1gl.a;continue;}}},_1gm=function(_1gn,_1go,_1gp){return new F(function(){return _1gi(_1go,_1gn);});},_1gq=function(_1gr,_1gs){var _1gt=E(_1gs);if(!_1gt._){return new T2(0,_Z,_Z);}else{var _1gu=_1gt.a;if(!B(A1(_1gr,_1gu))){var _1gv=new T(function(){var _1gw=B(_1gq(_1gr,_1gt.b));return new T2(0,_1gw.a,_1gw.b);});return new T2(0,new T2(1,_1gu,new T(function(){return E(E(_1gv).a);})),new T(function(){return E(E(_1gv).b);}));}else{return new T2(0,_Z,_1gt);}}},_1gx=function(_1gy,_1gz){while(1){var _1gA=E(_1gz);if(!_1gA._){return __Z;}else{if(!B(A1(_1gy,_1gA.a))){return E(_1gA);}else{_1gz=_1gA.b;continue;}}}},_1gB=function(_1gC){var _1gD=_1gC>>>0;if(_1gD>887){var _1gE=u_iswspace(_1gC);return (E(_1gE)==0)?false:true;}else{var _1gF=E(_1gD);return (_1gF==32)?true:(_1gF-9>>>0>4)?(E(_1gF)==160)?true:false:true;}},_1gG=function(_1gH){return new F(function(){return _1gB(E(_1gH));});},_1gI=function(_1gJ){var _1gK=B(_1gx(_1gG,_1gJ));if(!_1gK._){return __Z;}else{var _1gL=new T(function(){var _1gM=B(_1gq(_1gG,_1gK));return new T2(0,_1gM.a,_1gM.b);});return new T2(1,new T(function(){return E(E(_1gL).a);}),new T(function(){return B(_1gI(E(_1gL).b));}));}},_1gN=function(_1gO){if(!B(_4H(_lc,_1gh,_1gO))){return new T2(0,_1gO,_Z);}else{var _1gP=new T(function(){var _1gQ=E(_1gO);if(!_1gQ._){return E(_1gg);}else{var _1gR=E(_1gQ.b);if(!_1gR._){return E(_1gg);}else{var _1gS=_1gR.a,_1gT=_1gR.b,_1gU=E(_1gQ.a);if(E(_1gU)==61){return new T2(0,_Z,new T(function(){return E(B(_LC(61,_1gS,_1gT)).a);}));}else{var _1gV=B(_LC(61,_1gS,_1gT)),_1gW=E(_1gV.b);if(!_1gW._){return E(_1gg);}else{return new T2(0,new T2(1,_1gU,_1gV.a),_1gW.a);}}}}});return new T2(0,new T(function(){var _1gX=B(_1gI(E(_1gP).a));if(!_1gX._){return __Z;}else{return B(_1gm(_1gX.a,_1gX.b,_ZZ));}}),new T(function(){var _1gY=B(_1gI(E(_1gP).b));if(!_1gY._){return __Z;}else{return E(_1gY.a);}}));}},_1gZ=function(_1h0,_1h1){return new F(function(){return _1eq(E(_1h0),_1h1);});},_1h2=function(_1h3){var _1h4=E(_1h3);if(!_1h4._){return new T2(0,_Z,_Z);}else{var _1h5=E(_1h4.a),_1h6=new T(function(){var _1h7=B(_1h2(_1h4.b));return new T2(0,_1h7.a,_1h7.b);});return new T2(0,new T2(1,_1h5.a,new T(function(){return E(E(_1h6).a);})),new T2(1,_1h5.b,new T(function(){return E(E(_1h6).b);})));}},_1h8=new T(function(){return B(unCStr("\u570b\uff1a\u3053\u304f\uff1a\u53f2\uff1a\u3057\uff1a\u4e26\uff1a\u306a\u3089\uff1a\u3079\u66ff\uff1a\u304b\uff1a\u3078\u554f\uff1a\u3082\u3093\uff1a\u984c\uff1a\u3060\u3044\uff1a\u3067\u3059\u3002\n{sm}{ch.\u554f\u984c\u3078,s0.\u30c1\u30e5\u30fc\u30c8\u30ea\u30a2\u30eb,t0}"));}),_1h9=new T(function(){return B(unCStr("t1"));}),_1ha=new T(function(){return B(unCStr("\n\u3053\u308c\u3089\u306e\u6587\uff1a\u3082\uff1a\u5b57\uff1a\u3058\uff1a\u306e\u65b9\u5411\u3078\u884c\uff1a\u3044\uff1a\u304f\u3068 \u3042\u306a\u305f\u306f \u3053\u308c\u3089\u306e\u6587\u5b57\u3092 <\u6301\uff1a\u3082\uff1a\u3063\u305f> \u72b6\uff1a\u3058\u3083\u3046\uff1a\u614b\uff1a\u305f\u3044\uff1a\u306b\u306a\u308a\u307e\u3059\u3002\n\u3053\u306e\u3068\u304d\uff20\u306e\u8272\uff1a\u3044\u308d\uff1a\u304c\u6fc3\uff1a\u3053\uff1a\u304f\u306a\u3063\u3066\u3090\u307e\u3059\u3002\n\u305d\u308c\u3067\u306f \uff20\u3092\u3069\u3053\u304b \u5225\uff1a\u3079\u3064\uff1a\u306e\u3068\u3053\u308d\u3078\u6301\u3063\u3066\u3044\u304d \u753b\u9762\u306e\u4e2d\uff1a\u3061\u3085\u3046\uff1a\u5fc3\uff1a\u3057\u3093\uff1a\u90e8\uff1a\u3076\uff1a\u3092\u30bf\u30c3\u30d7\u3057\u3066\u304f\u3060\u3055\u3044\u3002\n{da}{e.oa.m1:t2}{e.ob.m1:t2}{e.oc.m1:t2}"));}),_1hb=new T2(0,_1h9,_1ha),_1hc=new T(function(){return B(unCStr("t2"));}),_1hd=new T(function(){return B(unCStr("\n{da}\n\u3053\u306e\u3068\u304d \u6301\u3063\u3066\u3090\u305f\u6587\u5b57\u304c\u958b\uff1a\u304b\u3044\uff1a\u653e\uff1a\u306f\u3046\uff1a\u3055\u308c \u30de\u30c3\u30d7\u4e0a\u306b \u7f6e\uff1a\u304a\uff1a\u304b\u308c\u305f\u72b6\u614b\u306b\u306a\u308a\u307e\u3059\u3002\n\u554f\u984c\u3092\u89e3\uff1a\u3068\uff1a\u304f\u3068\u304d \u3053\u308c\u3089\u306e\u6587\u5b57\u3092 \u30a4\u30b3\u30fc\u30eb <\uff1d>\u306e\u53f3\uff1a\u307f\u304e\uff1a\u306b \u5de6\uff1a\u3072\u3060\u308a\uff1a\u304b\u3089\u9806\uff1a\u3058\u3085\u3093\uff1a\u756a\uff1a\u3070\u3093\uff1a\u306b\u4e26\uff1a\u306a\u3089\uff1a\u3079\u308b\u5fc5\uff1a\u3072\u3064\uff1a\u8981\uff1a\u3048\u3046\uff1a\u304c\u3042\u308a\u307e\u3059\u3002\n\u305d\u308c\u3067\u306f\u554f\u984c\u3092\u59cb\uff1a\u306f\u3058\uff1a\u3081\u307e\u3059\u3002{e.X.m1:t3}"));}),_1he=new T2(0,_1hc,_1hd),_1hf=new T(function(){return B(unCStr("t3"));}),_1hg=new T(function(){return B(unCStr("\n\u3088\u308d\u3057\u3044\u3067\u3059\u304b\uff1f{ch.\u306f\u3044,t4.\u6700\uff1a\u3055\u3044\uff1a\u521d\uff1a\u3057\u3087\uff1a\u304b\u3089,t0}"));}),_1hh=new T2(0,_1hf,_1hg),_1hi=new T(function(){return B(unCStr("t4"));}),_1hj=new T(function(){return B(unCStr("\n\u305d\u308c\u3067\u306f\u59cb\u3081\u307e\u3059 {e.X.jl0}\n{e.X.m1:s0}"));}),_1hk=new T2(0,_1hi,_1hj),_1hl=new T(function(){return B(unCStr("s0"));}),_1hm=new T(function(){return B(unCStr("\n\u3069\u3061\u3089\u306b\u3057\u307e\u3059\u304b\uff1f{ch.\u901a\u53f2,s01.\u8fd1\u73fe\u4ee3\u53f2,s02}"));}),_1hn=new T2(0,_1hl,_1hm),_1ho=new T(function(){return B(unCStr("s01"));}),_1hp=new T(function(){return B(unCStr("\n\u53e4\uff1a\u3075\u308b\uff1a\u3044\u9806\uff1a\u3058\u3085\u3093\uff1a\u306b\u4e26\uff1a\u306a\u3089\uff1a\u3079\u3066\u304f\u3060\u3055\u3044\n{rk.1.z.abc.s0c1}{e.b=0.m0:s0eq}"));}),_1hq=new T2(0,_1ho,_1hp),_1hr=new T(function(){return B(unCStr("s02"));}),_1hs=new T(function(){return B(unCStr("\n\u53e4\uff1a\u3075\u308b\uff1a\u3044\u9806\uff1a\u3058\u3085\u3093\uff1a\u306b\u4e26\uff1a\u306a\u3089\uff1a\u3079\u3066\u304f\u3060\u3055\u3044\n{rk.2.z.abc.s0c2}{e.b=0.m0:s0eq}"));}),_1ht=new T2(0,_1hr,_1hs),_1hu=new T(function(){return B(unCStr("s1eq"));}),_1hv=new T(function(){return B(unCStr("\n\u53e4\u3044\u9806\u306b\u4e26\u3079\u3066\u304f\u3060\u3055\u3044\u3002"));}),_1hw=new T2(0,_1hu,_1hv),_1hx=new T(function(){return B(unCStr("s1c1"));}),_1hy=new T(function(){return B(unCStr("\n\u305b\u3044\u304b\u3044\uff01\u3002\n\u304b\u304b\u3063\u305f\u6642\u9593\u306f{rt.1}\n\u79d2\u3067\u3057\u305f\u3002\n\u6b21\u3078\u9032\u307f\u307e\u305b\u3046\u3002\n{d.b=0}{p.3,3.n,Ex}{e.un.l}{e.c1.m1:s21}"));}),_1hz=new T2(0,_1hx,_1hy),_1hA=new T(function(){return B(unCStr("s1c2"));}),_1hB=new T(function(){return B(unCStr("\n\u305b\u3044\u304b\u3044\uff01\u3002\n\u304b\u304b\u3063\u305f\u6642\u9593\u306f{rt.1}\n\u79d2\u3067\u3057\u305f\u3002\n\u6b21\u3078\u9032\u307f\u307e\u305b\u3046\u3002\n{d.b=0}{p.3,3.n,Ex}{e.un.l}{e.c1.m1:s22}"));}),_1hC=new T2(0,_1hA,_1hB),_1hD=new T(function(){return B(unCStr("s21"));}),_1hE=new T(function(){return B(unCStr("\n\u3060\u308c\u304b \u3090\u308b\u307f\u305f\u3044\u3067\u3059\u3002{da}{e.bA.m1:s2A0}{e.bB.m0:s2B0}{e.bC.m0:s2C0}{e.bD.m0:s2D0}{e.un.m0:s2n1}"));}),_1hF=new T2(0,_1hD,_1hE),_1hG=new T(function(){return B(unCStr("s22"));}),_1hH=new T(function(){return B(unCStr("\n\u3060\u308c\u304b \u3090\u308b\u307f\u305f\u3044\u3067\u3059\u3002{da}{e.bA.m1:s2A0}{e.bB.m0:s2B0}{e.bC.m0:s2C0}{e.bD.m0:s2D0}{e.un.m0:s2n2}"));}),_1hI=new T2(0,_1hG,_1hH),_1hJ=new T(function(){return B(unCStr("s2A0"));}),_1hK=new T(function(){return B(unCStr("\n\u3042\u306a\u305f\u306f \u81ea\uff1a\u3058\uff1a\u5206\uff1a\u3076\u3093\uff1a\u306e\u570b\uff1a\u304f\u306b\uff1a\u306e\u6b74\uff1a\u308c\u304d\uff1a\u53f2\uff1a\u3057\uff1a\u3092\u77e5\uff1a\u3057\uff1a\u308a\u305f\u3044\u3067\u3059\u304b\uff1f\u3002\n{ch.\u306f\u3044,s2A1_0.\u3044\u3044\u3048,s2A1_1}"));}),_1hL=new T2(0,_1hJ,_1hK),_1hM=new T(function(){return B(unCStr("s2A1_0"));}),_1hN=new T(function(){return B(unCStr("\n\u3055\u3046\u3067\u3059\u304b\u30fb\u30fb\u30fb\u3002\n\u3061\u306a\u307f\u306b <\u81ea\u5206\u306e\u570b> \u3068\u306f\u4f55\uff1a\u306a\u3093\uff1a\u3067\u305b\u3046\u304b\u3002\n<\u6b74\u53f2>\u3068\u306f\u4f55\u3067\u305b\u3046\u304b\u3002\n\u305d\u306e\u6b74\u53f2\u3092<\u77e5\u308b>\u3068\u306f\u4f55\u3067\u305b\u3046\u304b\u3002\n{e.bA.m0:s2A1_2}"));}),_1hO=new T2(0,_1hM,_1hN),_1hP=new T(function(){return B(unCStr("s2A1_1"));}),_1hQ=new T(function(){return B(unCStr("\n\u77e5\u308a\u305f\u304f\u3082\u306a\u3044\u3053\u3068\u3092 \u7121\uff1a\u3080\uff1a\u7406\uff1a\u308a\uff1a\u306b\u77e5\u308b\u5fc5\uff1a\u3072\u3064\uff1a\u8981\uff1a\u3048\u3046\uff1a\u306f\u3042\u308a\u307e\u305b\u3093\u3088\u306d\u3002 {e.bA.m1:s2A1_1}"));}),_1hR=new T2(0,_1hP,_1hQ),_1hS=new T(function(){return B(unCStr("s2A1_2"));}),_1hT=new T(function(){return B(unCStr("\n<\u81ea\u5206\u306e\u570b> \u3068\u306f\u4f55\u3067\u305b\u3046\u304b\u3002\n<\u6b74\u53f2>\u3068\u306f\u4f55\u3067\u305b\u3046\u304b\u3002\n\u305d\u306e\u6b74\u53f2\u3092<\u77e5\u308b>\u3068\u306f\u4f55\u3067\u305b\u3046\u304b\u3002"));}),_1hU=new T2(0,_1hS,_1hT),_1hV=new T(function(){return B(unCStr("s2B0"));}),_1hW=new T(function(){return B(unCStr("\n\u79c1\uff1a\u308f\u305f\u3057\uff1a\u306e\u6301\uff1a\u3082\uff1a\u3063\u3066\u3090\u308b\u60c5\uff1a\u3058\u3083\u3046\uff1a\u5831\uff1a\u307b\u3046\uff1a\u306b\u3088\u308b\u3068\u3002\n\u30d4\u30e9\u30df\u30c3\u30c9\u3092\u9020\uff1a\u3064\u304f\uff1a\u308b\u306e\u306b\u4f7f\uff1a\u3064\u304b\uff1a\u306f\u308c\u305f\u77f3\uff1a\u3044\u3057\uff1a\u306f \u7a7a\uff1a\u304f\u3046\uff1a\u4e2d\uff1a\u3061\u3085\u3046\uff1a\u306b\u6301\uff1a\u3082\uff1a\u3061\u4e0a\uff1a\u3042\uff1a\u3052\u3089\u308c\u3066 \u7d44\uff1a\u304f\uff1a\u307f\u4e0a\u3052\u3089\u308c\u3066\u3090\u307e\u3057\u305f\u3002"));}),_1hX=new T2(0,_1hV,_1hW),_1hY=new T(function(){return B(unCStr("s2C0"));}),_1hZ=new T(function(){return B(unCStr("\n\u30a4\u30a8\u30b9\u30fb\u30ad\u30ea\u30b9\u30c8\u306f \u30a4\u30f3\u30c9\u3084\u65e5\uff1a\u306b\uff1a\u672c\uff1a\u307b\u3093\uff1a\u3092\u8a2a\uff1a\u304a\u3068\u3065\uff1a\u308c\u3066\u3090\u305f\u3055\u3046\u3067\u3059\u3002\n\u3053\u308c\u3089\u306e\u5834\uff1a\u3070\uff1a\u6240\uff1a\u3057\u3087\uff1a\u306b\u306f \u305d\u306e\u5f62\uff1a\u3051\u3044\uff1a\u8de1\uff1a\u305b\u304d\uff1a\u304c \u3044\u304f\u3064\u3082\u6b98\uff1a\u306e\u3053\uff1a\u3063\u3066\u3090\u307e\u3059\u3002\n\u307e\u305f\u5f7c\uff1a\u304b\u308c\uff1a\u306f \u30a8\u30b8\u30d7\u30c8\u306e\u30d4\u30e9\u30df\u30c3\u30c8\u3067 \u79d8\uff1a\u3072\uff1a\u6280\uff1a\u304e\uff1a\u3092\u6388\uff1a\u3055\u3065\uff1a\u304b\u3063\u305f \u3068\u3044\u3075\u8a18\uff1a\u304d\uff1a\u9332\uff1a\u308d\u304f\uff1a\u304c\u3042\u308a\u307e\u3059\u3002"));}),_1i0=new T2(0,_1hY,_1hZ),_1i1=new T(function(){return B(unCStr("s2D0"));}),_1i2=new T(function(){return B(unCStr("\n\u6b74\uff1a\u308c\u304d\uff1a\u53f2\uff1a\u3057\uff1a\u3068\u3044\u3075\u3082\u306e\u306f \u305d\u308c\u3092\u50b3\uff1a\u3064\u305f\uff1a\u3078\u308b\u76ee\uff1a\u3082\u304f\uff1a\u7684\uff1a\u3066\u304d\uff1a\u3084 \u50b3\u3078\u308b\u4eba\uff1a\u3072\u3068\uff1a\u3005\uff1a\u3073\u3068\uff1a\u306e\u4e16\uff1a\u305b\uff1a\u754c\uff1a\u304b\u3044\uff1a\u89c0\uff1a\u304b\u3093\uff1a \u50b3\u3078\u305f\u7576\uff1a\u305f\u3046\uff1a\u6642\uff1a\u3058\uff1a\u306b\u6b98\uff1a\u306e\u3053\uff1a\u3063\u3066\u3090\u305f\u8cc7\uff1a\u3057\uff1a\u6599\uff1a\u308c\u3046\uff1a\u306e\u7a2e\uff1a\u3057\u3085\uff1a\u985e\uff1a\u308b\u3044\uff1a\u306a\u3069\u306b\u3088\u3063\u3066 \u540c\uff1a\u304a\u306a\uff1a\u3058\u6642\uff1a\u3058\uff1a\u4ee3\uff1a\u3060\u3044\uff1a\u306b\u95dc\uff1a\u304b\u3093\uff1a\u3059\u308b\u3082\u306e\u3067\u3082 \u76f8\uff1a\u3055\u3046\uff1a\u7576\uff1a\u305f\u3046\uff1a\u7570\uff1a\u3053\u3068\uff1a\u306a\u3063\u305f\u50b3\uff1a\u3064\u305f\uff1a\u3078\u65b9\uff1a\u304b\u305f\uff1a\u304c\u70ba\uff1a\u306a\uff1a\u3055\u308c\u308b\u3082\u306e\u3067\u3059\u3002\n\u3057\u304b\u3057 \u305d\u308c\u306f \u78ba\uff1a\u304b\u304f\uff1a\u5be6\uff1a\u3058\u3064\uff1a\u306a\u6b74\u53f2\u306f\u5b58\uff1a\u305d\u3093\uff1a\u5728\uff1a\u3056\u3044\uff1a\u305b\u305a \u6b74\u53f2\u3092\u5b78\uff1a\u307e\u306a\uff1a\u3076\u610f\uff1a\u3044\uff1a\u7fa9\uff1a\u304e\uff1a\u3082\u306a\u3044 \u3068\u3044\u3075\u3053\u3068\u306b\u306f\u306a\u308a\u307e\u305b\u3093\u3002\n\u3042\u306a\u305f\u304c\u7d0d\uff1a\u306a\u3063\uff1a\u5f97\uff1a\u3068\u304f\uff1a\u3057 \u4ed6\uff1a\u307b\u304b\uff1a\u306e\u4eba\uff1a\u3072\u3068\uff1a\u9054\uff1a\u305f\u3061\uff1a\u3068\u5171\uff1a\u304d\u3087\u3046\uff1a\u6709\uff1a\u3044\u3046\n\uff1a\u3067\u304d\u308b \u5171\u6709\u3057\u305f\u3044\u6b74\u53f2\u3092 \u3042\u306a\u305f\u81ea\uff1a\u3058\uff1a\u8eab\uff1a\u3057\u3093\uff1a\u304c\u898b\uff1a\u307f\uff1a\u51fa\uff1a\u3044\u3060\uff1a\u3057 \u7d21\uff1a\u3064\u3080\uff1a\u304c\u306a\u3051\u308c\u3070\u306a\u3089\u306a\u3044\u4ed5\uff1a\u3057\uff1a\u7d44\uff1a\u304f\uff1a\u307f\u306b\u306a\u3063\u3066\u3090\u308b\u304b\u3089\u3053\u305d \u6b74\u53f2\u306b\u306f\u4fa1\uff1a\u304b\uff1a\u5024\uff1a\u3061\uff1a\u304c\u3042\u308a \u3042\u306a\u305f\u306e\u751f\uff1a\u3044\uff1a\u304d\u308b\u610f\uff1a\u3044\uff1a\u5473\uff1a\u307f\uff1a\u306b\u3082 \u7e4b\uff1a\u3064\u306a\uff1a\u304c\u3063\u3066\u304f\u308b\u306e\u3067\u306f\u306a\u3044\u3067\u305b\u3046\u304b\u3002"));}),_1i3=new T2(0,_1i1,_1i2),_1i4=new T(function(){return B(unCStr("s2n1"));}),_1i5=new T(function(){return B(unCStr("\n\u6b21\u3078\u9032\uff1a\u3059\u3059\uff1a\u307f\u307e\u3059\u304b\uff1f\n{ch.\u9032\u3080,s2n1c.\u9032\u307e\u306a\u3044,s2n0}"));}),_1i6=new T2(0,_1i4,_1i5),_1i7=new T(function(){return B(unCStr("s2n2"));}),_1i8=new T(function(){return B(unCStr("\n\u6b21\u3078\u9032\uff1a\u3059\u3059\uff1a\u307f\u307e\u3059\u304b\uff1f\n{ch.\u9032\u3080,s2n2c.\u9032\u307e\u306a\u3044,s2n0}"));}),_1i9=new T2(0,_1i7,_1i8),_1ia=new T(function(){return B(unCStr("s2n0"));}),_1ib=new T(function(){return B(unCStr("\n\u884c\u304f\u306e\u3092\u3084\u3081\u307e\u3057\u305f\u3002"));}),_1ic=new T2(0,_1ia,_1ib),_1id=new T(function(){return B(unCStr("s2n1c"));}),_1ie=new T(function(){return B(unCStr("\n\u3067\u306f\u6b21\u3078\u884c\u304d\u307e\u305b\u3046\u3002{e.X.l}{e.c2.m1:s31}"));}),_1if=new T2(0,_1id,_1ie),_1ig=new T(function(){return B(unCStr("s2n2c"));}),_1ih=new T(function(){return B(unCStr("\n\u3067\u306f\u6b21\u3078\u884c\u304d\u307e\u305b\u3046\u3002{e.X.l}{e.c2.m1:s32}"));}),_1ii=new T2(0,_1ig,_1ih),_1ij=new T(function(){return B(unCStr("s31"));}),_1ik=new T(function(){return B(unCStr("\n\u53e4\u3044\u9806\u306b\u4e26\u3079\u3066\u304f\u3060\u3055\u3044\n{da}{rk.1.z.abcd.s3c1}{e.b=0.m0:s3eq}"));}),_1il=new T2(0,_1ij,_1ik),_1im=new T(function(){return B(unCStr("s32"));}),_1in=new T(function(){return B(unCStr("\n\u53e4\u3044\u9806\u306b\u4e26\u3079\u3066\u304f\u3060\u3055\u3044\n{da}{rk.2.z.abcd.s3c2}{e.b=0.m0:s3eq}"));}),_1io=new T2(0,_1im,_1in),_1ip=new T(function(){return B(unCStr("s3eq"));}),_1iq=new T2(0,_1ip,_1hv),_1ir=new T(function(){return B(unCStr("s3c1"));}),_1is=new T(function(){return B(unCStr("\n\u305b\u3044\u304b\u3044\u3067\u3059\uff01\u3002\n\u304b\u304b\u3063\u305f\u6642\u9593\u306f{rt.2}\n\u79d2\u3067\u3057\u305f\u3002\n\u6b21\u3078\u884c\u304d\u307e\u305b\u3046\u3002\n{d.b=0}{p.3,3.%,Ex}{e.u%.l}{e.c3.m1:s41}"));}),_1it=new T2(0,_1ir,_1is),_1iu=new T(function(){return B(unCStr("s3c2"));}),_1iv=new T(function(){return B(unCStr("\n\u305b\u3044\u304b\u3044\u3067\u3059\uff01\u3002\n\u304b\u304b\u3063\u305f\u6642\u9593\u306f{rt.2}\n\u79d2\u3067\u3057\u305f\u3002\n\u6b21\u3078\u884c\u304d\u307e\u305b\u3046\u3002\n{d.b=0}{p.3,3.%,Ex}{e.u%.l}{e.c3.m1:s42}"));}),_1iw=new T2(0,_1iu,_1iv),_1ix=new T(function(){return B(unCStr("s41"));}),_1iy=new T(function(){return B(unCStr("\n\u53e4\u3044\u9806\u306b\u4e26\u3079\u3066\u304f\u3060\u3055\u3044\n{da}{rk.1.z.abcd.s4c1}{e.b=0.m0:s4eq}"));}),_1iz=new T2(0,_1ix,_1iy),_1iA=new T(function(){return B(unCStr("s42"));}),_1iB=new T(function(){return B(unCStr("\n\u53e4\u3044\u9806\u306b\u4e26\u3079\u3066\u304f\u3060\u3055\u3044\n{da}{rk.2.z.abcd.s4c2}{e.b=0.m0:s4eq}"));}),_1iC=new T2(0,_1iA,_1iB),_1iD=new T(function(){return B(unCStr("s4eq"));}),_1iE=new T2(0,_1iD,_1hv),_1iF=new T(function(){return B(unCStr("s4c1"));}),_1iG=new T(function(){return B(unCStr("\n\u305b\u3044\u304b\u3044\uff01\u3002\n\u304b\u304b\u3063\u305f\u6642\u9593\u306f{rt.3}\n\u79d2\u3067\u3057\u305f\u3002\n\u6b21\u306b\u9032\u307f\u307e\u305b\u3046\u3002\n{d.b=0}{p.3,3.%,Ex}{e.u%.l}{e.c4.m1:s51}"));}),_1iH=new T2(0,_1iF,_1iG),_1iI=new T(function(){return B(unCStr("s4c2"));}),_1iJ=new T(function(){return B(unCStr("\n\u305b\u3044\u304b\u3044\uff01\u3002\n\u304b\u304b\u3063\u305f\u6642\u9593\u306f{rt.3}\n\u79d2\u3067\u3057\u305f\u3002\n\u6b21\u306b\u9032\u307f\u307e\u305b\u3046\u3002\n{d.b=0}{p.3,3.%,Ex}{e.u%.l}{e.c4.m1:s52}"));}),_1iK=new T2(0,_1iI,_1iJ),_1iL=new T(function(){return B(unCStr("s51"));}),_1iM=new T(function(){return B(unCStr("\n\u3060\u308c\u304b \u3090\u308b\u307f\u305f\u3044\u3067\u3059\u3002{da}{e.bE.m0:s5E0}{e.bF.m0:s5F0}{e.bG.m0:s5G0}{e.bH.m0:s5H0}{e.un.m0:s5n1}"));}),_1iN=new T2(0,_1iL,_1iM),_1iO=new T(function(){return B(unCStr("s52"));}),_1iP=new T(function(){return B(unCStr("\n\u3060\u308c\u304b \u3090\u308b\u307f\u305f\u3044\u3067\u3059\u3002{da}{e.bE.m0:s5E0}{e.bF.m0:s5F0}{e.bG.m0:s5G0}{e.bH.m0:s5H0}{e.un.m0:s5n2}"));}),_1iQ=new T2(0,_1iO,_1iP),_1iR=new T(function(){return B(unCStr("s5E0"));}),_1iS=new T(function(){return B(unCStr("\n\u904e\uff1a\u304b\uff1a\u53bb\uff1a\u3053\uff1a\u3082\u672a\uff1a\u307f\uff1a\u4f86\uff1a\u3089\u3044\uff1a\u3082 \u305d\u3057\u3066\u5225\uff1a\u3079\u3064\uff1a\u306e\u4e26\uff1a\u3078\u3044\uff1a\u884c\uff1a\u304b\u3046\uff1a\u4e16\uff1a\u305b\uff1a\u754c\uff1a\u304b\u3044\uff1a\u3082 \u3059\u3079\u3066\u306f \u4eca\uff1a\u3044\u307e\uff1a \u3053\u3053\u306b\u3042\u308a\u307e\u3059\u3002"));}),_1iT=new T2(0,_1iR,_1iS),_1iU=new T(function(){return B(unCStr("s5F0"));}),_1iV=new T(function(){return B(unCStr("\n\u672a\uff1a\u307f\uff1a\u4f86\uff1a\u3089\u3044\uff1a\u306f\u7576\uff1a\u305f\u3046\uff1a\u7136\uff1a\u305c\u3093\uff1a\u3055\u3046\u3067\u3059\u304c \u904e\uff1a\u304b\uff1a\u53bb\uff1a\u3053\uff1a\u3092\u6c7a\uff1a\u304d\uff1a\u3081\u308b\u306e\u3082 \u4eca\uff1a\u3044\u307e\uff1a\u306e\u3042\u306a\u305f\u6b21\uff1a\u3057\uff1a\u7b2c\uff1a\u3060\u3044\uff1a\u3067\u3059\u3002"));}),_1iW=new T2(0,_1iU,_1iV),_1iX=new T(function(){return B(unCStr("s5G0"));}),_1iY=new T(function(){return B(unCStr("\n\u540c\uff1a\u304a\u306a\uff1a\u3058\u6642\uff1a\u3058\uff1a\u4ee3\uff1a\u3060\u3044\uff1a\u306e \u540c\u3058\u5834\uff1a\u3070\uff1a\u6240\uff1a\u3057\u3087\uff1a\u306b\u95dc\uff1a\u304b\u3093\uff1a\u3059\u308b\u898b\uff1a\u307f\uff1a\u65b9\uff1a\u304b\u305f\uff1a\u304c \u308f\u305f\u3057\u3068 \u3042\u306a\u305f\u3067\u9055\uff1a\u3061\u304c\uff1a\u3075\u306e\u306f\n\u4eca\uff1a\u3044\u307e\uff1a \u79c1\u3068 \u3042\u306a\u305f\u304c\u540c\u3058\u5834\u6240\u306b\u3090\u3066 \u305d\u3053\u306b\u5c45\uff1a\u3090\uff1a\u308b\u5225\uff1a\u3079\u3064\uff1a\u306e\u8ab0\uff1a\u3060\u308c\uff1a\u304b\u306b\u5c0d\uff1a\u305f\u3044\uff1a\u3059\u308b\u5370\uff1a\u3044\u3093\uff1a\u8c61\uff1a\u3057\u3083\u3046\uff1a\u304c \u308f\u305f\u3057\u3068 \u3042\u306a\u305f\u3067\u7570\uff1a\u3053\u3068\uff1a\u306a\u3063\u3066\u3090\u308b\u3053\u3068\u3068 \u4f3c\uff1a\u306b\uff1a\u3066\u3090\u307e\u3059\u3002\n\u305d\u308c\u306f \u81ea\uff1a\u3057\uff1a\u7136\uff1a\u305c\u3093\uff1a\u306a\u3053\u3068\u3067 \u308f\u305f\u3057\u3068 \u3042\u306a\u305f\u306e\u898b\u65b9\u304c\u9055\u3075\u306e\u306f \u5168\uff1a\u307e\u3063\u305f\uff1a\u304f\u554f\uff1a\u3082\u3093\uff1a\u984c\uff1a\u3060\u3044\uff1a\u3042\u308a\u307e\u305b\u3093\u3002\n\u898b\u65b9\u304c\u5168\uff1a\u305c\u3093\uff1a\u7136\uff1a\u305c\u3093\uff1a\u7570\u306a\u3063\u3066\u3090\u3066\u3082 \u308f\u305f\u3057\u3068 \u3042\u306a\u305f\u306f \u5171\uff1a\u304d\u3087\u3046\uff1a\u611f\uff1a\u304b\u3093\uff1a\u3059\u308b\u559c\uff1a\u3088\u308d\u3053\uff1a\u3073\u3092\u5473\uff1a\u3042\u3058\uff1a\u306f\u3046\u3053\u3068\u304c\u3067\u304d\u307e\u3059\u3002"));}),_1iZ=new T2(0,_1iX,_1iY),_1j0=new T(function(){return B(unCStr("s5H0"));}),_1j1=new T(function(){return B(unCStr("\n\u6211\uff1a\u308f\uff1a\u304c\u570b\uff1a\u304f\u306b\uff1a\u306e\u6557\uff1a\u306f\u3044\uff1a\u6230\uff1a\u305b\u3093\uff1a\u5f8c\uff1a\u3054\uff1a \u7279\uff1a\u3068\u304f\uff1a\u306b\u5f37\uff1a\u3064\u3088\uff1a\u307e\u3063\u305f \u65e5\uff1a\u306b\uff1a\u672c\uff1a\u307b\u3093\uff1a\u8a9e\uff1a\u3054\uff1a\u306e\u7834\uff1a\u306f\uff1a\u58ca\uff1a\u304b\u3044\uff1a\u5de5\uff1a\u3053\u3046\uff1a\u4f5c\uff1a\u3055\u304f\uff1a\u306f \u305d\u308c\u3092\u4ed5\uff1a\u3057\uff1a\u639b\uff1a\u304b\uff1a\u3051\u305f\u4eba\uff1a\u3072\u3068\uff1a\u306e\u610f\uff1a\u3044\uff1a\u5716\uff1a\u3068\uff1a\u3068\u9006\uff1a\u304e\u3083\u304f\uff1a\u306b \u65e5\u672c\u8a9e\u3092\u5f37\uff1a\u304d\u3083\u3046\uff1a\u5316\uff1a\u304f\u308f\uff1a\u3057 \u305d\u306e\u67d4\uff1a\u3058\u3046\uff1a\u8edf\uff1a\u306a\u3093\uff1a\u3055\u3092 \u3088\u308a\u4e16\uff1a\u305b\uff1a\u754c\uff1a\u304b\u3044\uff1a\u306b\u767c\uff1a\u306f\u3063\uff1a\u4fe1\uff1a\u3057\u3093\uff1a\u3059\u308b\u571f\uff1a\u3069\uff1a\u58cc\uff1a\u3058\u3083\u3046\uff1a\u3092\u4f5c\uff1a\u3064\u304f\uff1a\u3063\u305f\u306e\u3067\u306f\u306a\u3044\u304b\u3068 \u79c1\u306f\u8003\uff1a\u304b\u3093\u304c\uff1a\u3078\u3066\u3090\u307e\u3059\u3002\n\u3067\u3059\u304b\u3089 \u304b\u306a\u9063\uff1a\u3065\u304b\uff1a\u3072\u3092\u6df7\uff1a\u3053\u3093\uff1a\u4e82\uff1a\u3089\u3093\uff1a\u3055\u305b\u305f\u308a \u6f22\uff1a\u304b\u3093\uff1a\u5b57\uff1a\u3058\uff1a\u3092\u3068\u3063\u305f\u308a\u3064\u3051\u305f\u308a\u3057\u305f\u3053\u3068\u304c \u9006\u306b\u65e5\u672c\u8a9e\u306e\u5f37\u3055 \u67d4\u8edf\u3055\u306e\u8a3c\uff1a\u3057\u3087\u3046\uff1a\u660e\uff1a\u3081\u3044\uff1a\u3092\u3082\u305f\u3089\u3057\u305f\u3068\u3082\u3044\u3078\u308b\u306e\u3067 \u65e5\u672c\u8a9e\u3092\u6df7\u4e82\u3055\u305b\u305f\u4eba\u3005\u306b \u79c1\u306f\u611f\uff1a\u304b\u3093\uff1a\u8b1d\uff1a\u3057\u3083\uff1a\u3057\u3066\u3090\u308b\u306e\u3067\u3059\u3002"));}),_1j2=new T2(0,_1j0,_1j1),_1j3=new T(function(){return B(unCStr("s5n1"));}),_1j4=new T(function(){return B(unCStr("\n\u6b21\u3078\u9032\u307f\u307e\u3059\u304b\uff1f\n{ch.\u9032\u3080,s5n1c.\u9032\u307e\u306a\u3044,s5n0}"));}),_1j5=new T2(0,_1j3,_1j4),_1j6=new T(function(){return B(unCStr("s5n2"));}),_1j7=new T(function(){return B(unCStr("\n\u6b21\u3078\u9032\u307f\u307e\u3059\u304b\uff1f\n{ch.\u9032\u3080,s5n2c.\u9032\u307e\u306a\u3044,s5n0}"));}),_1j8=new T2(0,_1j6,_1j7),_1j9=new T(function(){return B(unCStr("s5n0"));}),_1ja=new T2(0,_1j9,_1ib),_1jb=new T(function(){return B(unCStr("s5n1c"));}),_1jc=new T(function(){return B(unCStr("\n\u3067\u306f\u6b21\u3078\u884c\u304d\u307e\u305b\u3046\u3002{e.X.l}{e.c5.m1:s61}"));}),_1jd=new T2(0,_1jb,_1jc),_1je=new T(function(){return B(unCStr("s5n2c"));}),_1jf=new T(function(){return B(unCStr("\n\u3067\u306f\u6b21\u3078\u884c\u304d\u307e\u305b\u3046\u3002{e.X.l}{e.c5.m1:s62}"));}),_1jg=new T2(0,_1je,_1jf),_1jh=new T(function(){return B(unCStr("s8I2"));}),_1ji=new T(function(){return B(unCStr("\n\u3067\u306f \u3088\u3044\u4e00\uff1a\u3044\u3061\uff1a\u65e5\uff1a\u306b\u3061\uff1a\u3092\u30fb\u30fb\u30fb\u3002{e.X.l}"));}),_1jj=new T2(0,_1jh,_1ji),_1jk=new T2(1,_1jj,_Z),_1jl=new T(function(){return B(unCStr("s8I1"));}),_1jm=new T(function(){return B(unCStr("\n\u305d\u308c\u3067\u306f \u59cb\u3081\u307e\u305b\u3046\u3002{da}{e.c8.m1:s0}{e.X.jl0}"));}),_1jn=new T2(0,_1jl,_1jm),_1jo=new T2(1,_1jn,_1jk),_1jp=new T(function(){return B(unCStr("s8I0"));}),_1jq=new T(function(){return B(unCStr("\n\u304a\u3064\u304b\u308c\u3055\u307e\u3067\u3059\u3002\n\u3042\u306a\u305f\u306e\u9ede\uff1a\u3066\u3093\uff1a\u6578\uff1a\u3059\u3046\uff1a\u306f{rs}\n\u9ede\uff1a\u3066\u3093\uff1a\u3067\u3059\u3002\n\u307e\u3046\u3044\u3061\u3069 \u3084\u308a\u307e\u3059\u304b\uff1f{ch.\u3084\u308b,s8I1.\u3084\u3081\u308b,s8I2}"));}),_1jr=new T2(0,_1jp,_1jq),_1js=new T2(1,_1jr,_1jo),_1jt=new T(function(){return B(unCStr("s82"));}),_1ju=new T(function(){return B(unCStr("\n\u3060\u308c\u304b\u3090\u307e\u3059\u3002{da}{e.bI.m0:s8I0}"));}),_1jv=new T2(0,_1jt,_1ju),_1jw=new T2(1,_1jv,_1js),_1jx=new T(function(){return B(unCStr("s81"));}),_1jy=new T2(0,_1jx,_1ju),_1jz=new T2(1,_1jy,_1jw),_1jA=new T(function(){return B(unCStr("s7c2"));}),_1jB=new T(function(){return B(unCStr("\n\u305b\u3044\u304b\u3044\uff01\u3002\n\u304b\u304b\u3063\u305f\u6642\u9593\u306f{rt.5}\n\u79d2\u3067\u3057\u305f\u3002\n\u6b21\u306b\u9032\u307f\u307e\u305b\u3046\u3002\n{d.b=0}{p.3,3.%,Ex}{e.u%.l}{e.c7.m1:s82}"));}),_1jC=new T2(0,_1jA,_1jB),_1jD=new T2(1,_1jC,_1jz),_1jE=new T(function(){return B(unCStr("s7c1"));}),_1jF=new T(function(){return B(unCStr("\n\u305b\u3044\u304b\u3044\uff01\u3002\n\u304b\u304b\u3063\u305f\u6642\u9593\u306f{rt.5}\n\u79d2\u3067\u3057\u305f\u3002\n\u6b21\u306b\u9032\u307f\u307e\u305b\u3046\u3002\n{d.b=0}{p.3,3.%,Ex}{e.u%.l}{e.c7.m1:s81}"));}),_1jG=new T2(0,_1jE,_1jF),_1jH=new T2(1,_1jG,_1jD),_1jI=new T(function(){return B(unCStr("s7eq"));}),_1jJ=new T2(0,_1jI,_1hv),_1jK=new T2(1,_1jJ,_1jH),_1jL=new T(function(){return B(unCStr("s72"));}),_1jM=new T(function(){return B(unCStr("\n\u53e4\u3044\u9806\u306b\u4e26\u3079\u3066\u304f\u3060\u3055\u3044\n{da}{rk.2.z.abcde.s7c2}{e.b=0.m0:s7eq}"));}),_1jN=new T2(0,_1jL,_1jM),_1jO=new T2(1,_1jN,_1jK),_1jP=new T(function(){return B(unCStr("s71"));}),_1jQ=new T(function(){return B(unCStr("\n\u53e4\u3044\u9806\u306b\u4e26\u3079\u3066\u304f\u3060\u3055\u3044\n{da}{rk.1.z.abcde.s7c1}{e.b=0.m0:s7eq}"));}),_1jR=new T2(0,_1jP,_1jQ),_1jS=new T2(1,_1jR,_1jO),_1jT=new T(function(){return B(unCStr("s6c2"));}),_1jU=new T(function(){return B(unCStr("\n\u305b\u3044\u304b\u3044\u3067\u3059\uff01\u3002\n\u304b\u304b\u3063\u305f\u6642\u9593\u306f{rt.4}\n\u79d2\u3067\u3057\u305f\u3002\n\u6b21\u306b\u9032\u307f\u307e\u305b\u3046\u3002\n{d.b=0}{p.3,3.%,Ex}{e.u%.l}{e.c6.m1:s72}"));}),_1jV=new T2(0,_1jT,_1jU),_1jW=new T2(1,_1jV,_1jS),_1jX=new T(function(){return B(unCStr("s6c1"));}),_1jY=new T(function(){return B(unCStr("\n\u305b\u3044\u304b\u3044\u3067\u3059\uff01\u3002\n\u304b\u304b\u3063\u305f\u6642\u9593\u306f{rt.4}\n\u79d2\u3067\u3057\u305f\u3002\n\u6b21\u306b\u9032\u307f\u307e\u305b\u3046\u3002\n{d.b=0}{p.3,3.%,Ex}{e.u%.l}{e.c6.m1:s71}"));}),_1jZ=new T2(0,_1jX,_1jY),_1k0=new T2(1,_1jZ,_1jW),_1k1=new T(function(){return B(unCStr("s6eq"));}),_1k2=new T2(0,_1k1,_1hv),_1k3=new T2(1,_1k2,_1k0),_1k4=new T(function(){return B(unCStr("s62"));}),_1k5=new T(function(){return B(unCStr("\n\u53e4\u3044\u9806\u306b\u4e26\u3079\u3066\u304f\u3060\u3055\u3044\n{rk.2.z.abcde.s6c2}{e.b=0.m0:s6eq}"));}),_1k6=new T2(0,_1k4,_1k5),_1k7=new T2(1,_1k6,_1k3),_1k8=new T(function(){return B(unCStr("s61"));}),_1k9=new T(function(){return B(unCStr("\n\u53e4\u3044\u9806\u306b\u4e26\u3079\u3066\u304f\u3060\u3055\u3044\n{rk.1.z.abcde.s6c1}{e.b=0.m0:s6eq}"));}),_1ka=new T2(0,_1k8,_1k9),_1kb=new T2(1,_1ka,_1k7),_1kc=new T2(1,_1jg,_1kb),_1kd=new T2(1,_1jd,_1kc),_1ke=new T2(1,_1ja,_1kd),_1kf=new T2(1,_1j8,_1ke),_1kg=new T2(1,_1j5,_1kf),_1kh=new T2(1,_1j2,_1kg),_1ki=new T2(1,_1iZ,_1kh),_1kj=new T2(1,_1iW,_1ki),_1kk=new T2(1,_1iT,_1kj),_1kl=new T2(1,_1iQ,_1kk),_1km=new T2(1,_1iN,_1kl),_1kn=new T2(1,_1iK,_1km),_1ko=new T2(1,_1iH,_1kn),_1kp=new T2(1,_1iE,_1ko),_1kq=new T2(1,_1iC,_1kp),_1kr=new T2(1,_1iz,_1kq),_1ks=new T2(1,_1iw,_1kr),_1kt=new T2(1,_1it,_1ks),_1ku=new T2(1,_1iq,_1kt),_1kv=new T2(1,_1io,_1ku),_1kw=new T2(1,_1il,_1kv),_1kx=new T2(1,_1ii,_1kw),_1ky=new T2(1,_1if,_1kx),_1kz=new T2(1,_1ic,_1ky),_1kA=new T2(1,_1i9,_1kz),_1kB=new T2(1,_1i6,_1kA),_1kC=new T2(1,_1i3,_1kB),_1kD=new T2(1,_1i0,_1kC),_1kE=new T2(1,_1hX,_1kD),_1kF=new T2(1,_1hU,_1kE),_1kG=new T2(1,_1hR,_1kF),_1kH=new T2(1,_1hO,_1kG),_1kI=new T2(1,_1hL,_1kH),_1kJ=new T2(1,_1hI,_1kI),_1kK=new T2(1,_1hF,_1kJ),_1kL=new T2(1,_1hC,_1kK),_1kM=new T2(1,_1hz,_1kL),_1kN=new T2(1,_1hw,_1kM),_1kO=new T(function(){return B(unCStr("s12"));}),_1kP=new T(function(){return B(unCStr("\n\u53e4\u3044\u9806\u306b\u4e26\u3079\u307e\u305b\u3046\u3002\n{da}{rk.2.z.abc.s1c2}{e.b=0.m0:s1eq}"));}),_1kQ=new T2(0,_1kO,_1kP),_1kR=new T2(1,_1kQ,_1kN),_1kS=new T(function(){return B(unCStr("s11"));}),_1kT=new T(function(){return B(unCStr("\n\u53e4\u3044\u9806\u306b\u4e26\u3079\u307e\u305b\u3046\u3002\n{da}{rk.1.z.abc.s1c1}{e.b=0.m0:s1eq}"));}),_1kU=new T2(0,_1kS,_1kT),_1kV=new T2(1,_1kU,_1kR),_1kW=new T(function(){return B(unCStr("nubatama"));}),_1kX=new T(function(){return B(unCStr("\n\u306c\u3070\u305f\u307e\u306e \u4e16\u306f\u96e3\u3057\u304f \u601d\u3078\u308c\u3069\u3002   \n\u660e\u3051\u3066\u898b\u3086\u308b\u306f \u552f\u5927\u6cb3\u306a\u308a"));}),_1kY=new T2(0,_1kW,_1kX),_1kZ=new T2(1,_1kY,_1kV),_1l0=new T(function(){return B(unCStr("\n\u4f55\u304c\u8d77\uff1a\u304a\uff1a\u3053\u3063\u305f\uff1f"));}),_1l1=new T(function(){return B(unCStr("msgW"));}),_1l2=new T2(0,_1l1,_1l0),_1l3=new T2(1,_1l2,_1kZ),_1l4=new T(function(){return B(unCStr("\n\u307e\u3046\u4e00\u5ea6 \u3084\u3063\u3066\u307f\u3084\u3046"));}),_1l5=new T(function(){return B(unCStr("msgR"));}),_1l6=new T2(0,_1l5,_1l4),_1l7=new T2(1,_1l6,_1l3),_1l8=new T(function(){return B(unCStr("s0c2"));}),_1l9=new T(function(){return B(unCStr("\n\u305b\u3044\u304b\u3044\u3067\u3059\uff01\u3002\n\u304b\u304b\u3063\u305f\u6642\uff1a\u3058\uff1a\u9593\uff1a\u304b\u3093\uff1a\u306f{rt.0}\n\u79d2\uff1a\u3079\u3046\uff1a\u3067\u3057\u305f\u3002\n\u8a73\uff1a\u304f\u306f\uff1a\u3057\u3044\u8aac\uff1a\u305b\u3064\uff1a\u660e\uff1a\u3081\u3044\uff1a\u306f \u554f\uff1a\u3082\u3093\uff1a\u984c\uff1a\u3060\u3044\uff1a\u3060\u3063\u305f\u6587\uff1a\u3082\uff1a\u5b57\uff1a\u3058\uff1a\u3092<\u6301\uff1a\u3082\uff1a\u3064>\u3068\u898b\uff1a\u307f\uff1a\u308b\u3053\u3068\u304c\u3067\u304d\u307e\u3059\u3002\n\u6e96\uff1a\u3058\u3085\u3093\uff1a\u5099\uff1a\u3073\uff1a\u304c\u3067\u304d\u305f\u3089 \u6b21\uff1a\u3064\u304e\uff1a\u306e\u554f\u984c\u3078\u884c\uff1a\u3044\uff1a\u304d\u307e\u305b\u3046\u3002\n\u65b0\uff1a\u3042\u3089\uff1a\u305f\u306b\u51fa\uff1a\u3057\u3085\u3064\uff1a\u73fe\uff1a\u3052\u3093\uff1a\u3057\u305f\u6587\u5b57\u3078\u79fb\uff1a\u3044\uff1a\u52d5\uff1a\u3069\u3046\uff1a\u3057\u3066\u304f\u3060\u3055\u3044\n{d.b=0}{p.3,3.n,Ex}{e.un.l}{e.c0.m1:s12}"));}),_1la=new T2(0,_1l8,_1l9),_1lb=new T2(1,_1la,_1l7),_1lc=new T(function(){return B(unCStr("s0c1"));}),_1ld=new T(function(){return B(unCStr("\n\u305b\u3044\u304b\u3044\u3067\u3059\uff01\u3002\n\u304b\u304b\u3063\u305f\u6642\uff1a\u3058\uff1a\u9593\uff1a\u304b\u3093\uff1a\u306f{rt.0}\n\u79d2\uff1a\u3079\u3046\uff1a\u3067\u3057\u305f\u3002\n\u8a73\uff1a\u304f\u306f\uff1a\u3057\u3044\u8aac\uff1a\u305b\u3064\uff1a\u660e\uff1a\u3081\u3044\uff1a\u306f \u554f\uff1a\u3082\u3093\uff1a\u984c\uff1a\u3060\u3044\uff1a\u3060\u3063\u305f\u6587\uff1a\u3082\uff1a\u5b57\uff1a\u3058\uff1a\u3092<\u6301\uff1a\u3082\uff1a\u3064>\u3068\u898b\uff1a\u307f\uff1a\u308b\u3053\u3068\u304c\u3067\u304d\u307e\u3059\u3002\n\u6e96\uff1a\u3058\u3085\u3093\uff1a\u5099\uff1a\u3073\uff1a\u304c\u3067\u304d\u305f\u3089 \u6b21\uff1a\u3064\u304e\uff1a\u306e\u554f\u984c\u3078\u884c\uff1a\u3044\uff1a\u304d\u307e\u305b\u3046\u3002\n\u65b0\uff1a\u3042\u3089\uff1a\u305f\u306b\u51fa\uff1a\u3057\u3085\u3064\uff1a\u73fe\uff1a\u3052\u3093\uff1a\u3057\u305f\u6587\u5b57\u3078\u79fb\uff1a\u3044\uff1a\u52d5\uff1a\u3069\u3046\uff1a\u3057\u3066\u304f\u3060\u3055\u3044\n{d.b=0}{p.3,3.n,Ex}{e.un.l}{e.c0.m1:s11}"));}),_1le=new T2(0,_1lc,_1ld),_1lf=new T2(1,_1le,_1lb),_1lg=new T(function(){return B(unCStr("s0eq"));}),_1lh=new T2(0,_1lg,_1hv),_1li=new T2(1,_1lh,_1lf),_1lj=new T2(1,_1ht,_1li),_1lk=new T2(1,_1hq,_1lj),_1ll=new T2(1,_1hn,_1lk),_1lm=new T2(1,_1hk,_1ll),_1ln=new T2(1,_1hh,_1lm),_1lo=new T2(1,_1he,_1ln),_1lp=new T2(1,_1hb,_1lo),_1lq=new T(function(){return B(unCStr("t0"));}),_1lr=new T(function(){return B(unCStr("\n\u3042\u306a\u305f\u306f \u30de\u30c3\u30d7\u4e0a\u306e\uff20\u3092\u52d5\uff1a\u3046\u3054\uff1a\u304b\u3057\u307e\u3059\u3002\n\u753b\uff1a\u304c\uff1a\u9762\uff1a\u3081\u3093\uff1a\u306e\u4e0a\uff1a\u3058\u3087\u3046\uff1a\u7aef\uff1a\u305f\u3093\uff1a\u30fb\u4e0b\uff1a\u304b\uff1a\u7aef\uff1a\u305f\u3093\uff1a\u30fb\u5de6\uff1a\u3072\u3060\u308a\uff1a\u7aef\uff1a\u306f\u3057\uff1a\u30fb\u53f3\uff1a\u307f\u304e\uff1a\u7aef\uff1a\u306f\u3057\uff1a\u306a\u3069\u3092\u30bf\u30c3\u30d7\u3059\u308b\u3068\uff20\u306f\u305d\u306e\u65b9\uff1a\u306f\u3046\uff1a\u5411\uff1a\u304b\u3046\uff1a\u3078\u52d5\u304d\u307e\u3059\u3002\n{e.ea.m1:t1}{e.eb.m1:t1}{e.ec.m1:t1}"));}),_1ls=new T2(0,_1lq,_1lr),_1lt=new T2(1,_1ls,_1lp),_1lu=new T(function(){return B(unCStr("initMsg"));}),_1lv=function(_1lw,_1lx){var _1ly=new T(function(){var _1lz=B(_1h2(_1lw));return new T2(0,_1lz.a,_1lz.b);}),_1lA=function(_1lB){var _1lC=E(_1lB);if(!_1lC._){return E(_1ly);}else{var _1lD=E(_1lC.a),_1lE=new T(function(){return B(_1lA(_1lC.b));});return new T2(0,new T2(1,_1lD.a,new T(function(){return E(E(_1lE).a);})),new T2(1,_1lD.b,new T(function(){return E(E(_1lE).b);})));}},_1lF=function(_1lG,_1lH,_1lI){var _1lJ=new T(function(){return B(_1lA(_1lI));});return new T2(0,new T2(1,_1lG,new T(function(){return E(E(_1lJ).a);})),new T2(1,_1lH,new T(function(){return E(E(_1lJ).b);})));},_1lK=B(_1lF(_1lu,_1h8,_1lt)),_1lL=_1lK.a;if(!B(_4H(_uJ,_1lx,_1lL))){return __Z;}else{return new F(function(){return _aW(_1lK.b,B(_Rj(_uJ,_1lx,_1lL)));});}},_1lM=5,_1lN=new T2(0,_1lM,_1lM),_1lO=7,_1lP=new T2(0,_1lO,_1lM),_1lQ=6,_1lR=new T2(0,_1lM,_1lQ),_1lS=new T2(1,_1lR,_Z),_1lT=new T2(1,_1lP,_1lS),_1lU=new T2(1,_1lP,_1lT),_1lV=new T2(1,_1lR,_1lU),_1lW=new T2(1,_1lP,_1lV),_1lX=new T2(1,_1lP,_1lW),_1lY=new T2(1,_1lR,_1lX),_1lZ=new T2(1,_1lN,_1lY),_1m0=new T2(1,_1lN,_1lZ),_1m1=2,_1m2=new T2(0,_1m1,_1m1),_1m3=new T2(1,_1m2,_Z),_1m4=new T2(1,_1m2,_1m3),_1m5=new T2(1,_1m2,_1m4),_1m6=new T2(1,_1m2,_1m5),_1m7=new T2(1,_1m2,_1m6),_1m8=new T2(1,_1m2,_1m7),_1m9=new T2(1,_1m2,_1m8),_1ma=new T2(1,_1m2,_1m9),_1mb=new T2(1,_1m2,_1ma),_1mc=new T(function(){return B(unCStr("Int"));}),_1md=function(_1me,_1mf,_1mg){return new F(function(){return _1dd(_1cG,new T2(0,_1mf,_1mg),_1me,_1mc);});},_1mh=new T(function(){return B(unCStr("msgR"));}),_1mi=new T(function(){return B(_1lv(_Z,_1mh));}),_1mj=new T(function(){return B(unCStr("msgW"));}),_1mk=new T(function(){return B(_1lv(_Z,_1mj));}),_1ml=function(_1mm){var _1mn=E(_1mm);return 0;},_1mo=new T(function(){return B(unCStr("@@@@@@@@@"));}),_1mp=new T(function(){var _1mq=E(_1mo);if(!_1mq._){return E(_rm);}else{return E(_1mq.a);}}),_1mr=122,_1ms=new T2(0,_1mr,_IO),_1mt=0,_1mu=new T2(0,_1mt,_1mt),_1mv=new T2(0,_1mu,_1ms),_1mw=61,_1mx=new T2(0,_1mw,_IO),_1my=1,_1mz=new T2(0,_1my,_1mt),_1mA=new T2(0,_1mz,_1mx),_1mB=97,_1mC=new T2(0,_1mB,_II),_1mD=4,_1mE=new T2(0,_1mt,_1mD),_1mF=new T2(0,_1mE,_1mC),_1mG=98,_1mH=new T2(0,_1mG,_II),_1mI=new T2(0,_1m1,_1mD),_1mJ=new T2(0,_1mI,_1mH),_1mK=99,_1mL=new T2(0,_1mK,_II),_1mM=new T2(0,_1mD,_1mD),_1mN=new T2(0,_1mM,_1mL),_1mO=new T2(1,_1mN,_Z),_1mP=new T2(1,_1mJ,_1mO),_1mQ=new T2(1,_1mF,_1mP),_1mR=new T2(1,_1mA,_1mQ),_1mS=new T2(1,_1mv,_1mR),_1mT=new T(function(){return B(_1fX(_1lM,5,_1mS));}),_1mU=new T(function(){return B(_PU("Check.hs:142:22-33|(ch : po)"));}),_1mV=new T(function(){return B(_ic("Check.hs:(108,1)-(163,19)|function trEvent"));}),_1mW=110,_1mX=new T2(0,_1mW,_IU),_1mY=new T2(0,_1mD,_1lM),_1mZ=new T2(0,_1mY,_1mX),_1n0=new T2(1,_1mZ,_Z),_1n1=new T2(0,_1m1,_1lM),_1n2=66,_1n3=new T2(0,_1n2,_IO),_1n4=new T2(0,_1n1,_1n3),_1n5=new T2(1,_1n4,_1n0),_1n6=3,_1n7=new T2(0,_1mt,_1n6),_1n8=67,_1n9=new T2(0,_1n8,_IO),_1na=new T2(0,_1n7,_1n9),_1nb=new T2(1,_1na,_1n5),_1nc=new T2(0,_1mD,_1my),_1nd=65,_1ne=new T2(0,_1nd,_IO),_1nf=new T2(0,_1nc,_1ne),_1ng=new T2(1,_1nf,_1nb),_1nh=68,_1ni=new T2(0,_1nh,_IO),_1nj=new T2(0,_1mz,_1ni),_1nk=new T2(1,_1nj,_1ng),_1nl=100,_1nm=new T2(0,_1nl,_II),_1nn=new T2(0,_1lQ,_1mD),_1no=new T2(0,_1nn,_1nm),_1np=new T2(1,_1no,_Z),_1nq=new T2(1,_1mN,_1np),_1nr=new T2(1,_1mJ,_1nq),_1ns=new T2(1,_1mF,_1nr),_1nt=new T2(1,_1mA,_1ns),_1nu=new T2(1,_1mv,_1nt),_1nv=70,_1nw=new T2(0,_1nv,_IO),_1nx=new T2(0,_1n1,_1nw),_1ny=new T2(1,_1nx,_1n0),_1nz=72,_1nA=new T2(0,_1nz,_IO),_1nB=new T2(0,_1n7,_1nA),_1nC=new T2(1,_1nB,_1ny),_1nD=69,_1nE=new T2(0,_1nD,_IO),_1nF=new T2(0,_1nc,_1nE),_1nG=new T2(1,_1nF,_1nC),_1nH=71,_1nI=new T2(0,_1nH,_IO),_1nJ=new T2(0,_1mz,_1nI),_1nK=new T2(1,_1nJ,_1nG),_1nL=101,_1nM=new T2(0,_1nL,_II),_1nN=new T2(0,_1mD,_1m1),_1nO=new T2(0,_1nN,_1nM),_1nP=new T2(1,_1nO,_1ns),_1nQ=new T2(1,_1mA,_1nP),_1nR=new T2(1,_1mv,_1nQ),_1nS=73,_1nT=new T2(0,_1nS,_IO),_1nU=new T2(0,_1m1,_1mt),_1nV=new T2(0,_1nU,_1nT),_1nW=new T2(1,_1nV,_Z),_1nX=new T2(1,_1nW,_Z),_1nY=new T2(1,_1nR,_1nX),_1nZ=new T2(1,_1nR,_1nY),_1o0=new T2(1,_1nK,_1nZ),_1o1=new T2(1,_1nu,_1o0),_1o2=new T2(1,_1nu,_1o1),_1o3=new T2(1,_1nk,_1o2),_1o4=new T2(1,_1mS,_1o3),_1o5=new T2(1,_1mS,_1o4),_1o6=function(_1o7){var _1o8=E(_1o7);if(!_1o8._){return __Z;}else{var _1o9=_1o8.b,_1oa=E(_1o8.a),_1ob=_1oa.b,_1oc=E(_1oa.a),_1od=function(_1oe){if(E(_1oc)==32){return new T2(1,_1oa,new T(function(){return B(_1o6(_1o9));}));}else{switch(E(_1ob)){case 0:return new T2(1,new T2(0,_1oc,_II),new T(function(){return B(_1o6(_1o9));}));case 1:return new T2(1,new T2(0,_1oc,_Jj),new T(function(){return B(_1o6(_1o9));}));case 2:return new T2(1,new T2(0,_1oc,_IU),new T(function(){return B(_1o6(_1o9));}));case 3:return new T2(1,new T2(0,_1oc,_J0),new T(function(){return B(_1o6(_1o9));}));case 4:return new T2(1,new T2(0,_1oc,_J6),new T(function(){return B(_1o6(_1o9));}));case 5:return new T2(1,new T2(0,_1oc,_Jx),new T(function(){return B(_1o6(_1o9));}));case 6:return new T2(1,new T2(0,_1oc,_Jq),new T(function(){return B(_1o6(_1o9));}));case 7:return new T2(1,new T2(0,_1oc,_Jj),new T(function(){return B(_1o6(_1o9));}));default:return new T2(1,new T2(0,_1oc,_Jc),new T(function(){return B(_1o6(_1o9));}));}}};if(E(_1oc)==32){return new F(function(){return _1od(_);});}else{switch(E(_1ob)){case 0:return new T2(1,new T2(0,_1oc,_Jc),new T(function(){return B(_1o6(_1o9));}));case 1:return new F(function(){return _1od(_);});break;case 2:return new F(function(){return _1od(_);});break;case 3:return new F(function(){return _1od(_);});break;case 4:return new F(function(){return _1od(_);});break;case 5:return new F(function(){return _1od(_);});break;case 6:return new F(function(){return _1od(_);});break;case 7:return new F(function(){return _1od(_);});break;default:return new F(function(){return _1od(_);});}}}},_1of=function(_1og){var _1oh=E(_1og);return (_1oh._==0)?__Z:new T2(1,new T(function(){return B(_1o6(_1oh.a));}),new T(function(){return B(_1of(_1oh.b));}));},_1oi=function(_1oj){var _1ok=E(_1oj);if(!_1ok._){return __Z;}else{var _1ol=_1ok.b,_1om=E(_1ok.a),_1on=_1om.b,_1oo=E(_1om.a),_1op=function(_1oq){if(E(_1oo)==32){return new T2(1,_1om,new T(function(){return B(_1oi(_1ol));}));}else{switch(E(_1on)){case 0:return new T2(1,new T2(0,_1oo,_II),new T(function(){return B(_1oi(_1ol));}));case 1:return new T2(1,new T2(0,_1oo,_IO),new T(function(){return B(_1oi(_1ol));}));case 2:return new T2(1,new T2(0,_1oo,_IU),new T(function(){return B(_1oi(_1ol));}));case 3:return new T2(1,new T2(0,_1oo,_J0),new T(function(){return B(_1oi(_1ol));}));case 4:return new T2(1,new T2(0,_1oo,_J6),new T(function(){return B(_1oi(_1ol));}));case 5:return new T2(1,new T2(0,_1oo,_Jx),new T(function(){return B(_1oi(_1ol));}));case 6:return new T2(1,new T2(0,_1oo,_Jq),new T(function(){return B(_1oi(_1ol));}));case 7:return new T2(1,new T2(0,_1oo,_IO),new T(function(){return B(_1oi(_1ol));}));default:return new T2(1,new T2(0,_1oo,_Jc),new T(function(){return B(_1oi(_1ol));}));}}};if(E(_1oo)==32){return new F(function(){return _1op(_);});}else{if(E(_1on)==8){return new T2(1,new T2(0,_1oo,_II),new T(function(){return B(_1oi(_1ol));}));}else{return new F(function(){return _1op(_);});}}}},_1or=function(_1os){var _1ot=E(_1os);return (_1ot._==0)?__Z:new T2(1,new T(function(){return B(_1oi(_1ot.a));}),new T(function(){return B(_1or(_1ot.b));}));},_1ou=function(_1ov,_1ow,_1ox,_1oy,_1oz,_1oA,_1oB,_1oC,_1oD,_1oE,_1oF,_1oG,_1oH,_1oI,_1oJ,_1oK,_1oL,_1oM,_1oN,_1oO,_1oP,_1oQ,_1oR,_1oS,_1oT,_1oU,_1oV,_1oW,_1oX,_1oY,_1oZ,_1p0,_1p1,_1p2,_1p3,_1p4,_1p5,_1p6,_1p7,_1p8,_1p9,_1pa){var _1pb=E(_1ow);if(!_1pb._){return E(_1mV);}else{var _1pc=_1pb.b,_1pd=E(_1pb.a),_1pe=new T(function(){var _1pf=function(_){var _1pg=B(_qy(_1oM,0))-1|0,_1ph=function(_1pi){if(_1pi>=0){var _1pj=newArr(_1pi,_1cu),_1pk=_1pj,_1pl=E(_1pi);if(!_1pl){return new T4(0,E(_1eQ),E(_1pg),0,_1pk);}else{var _1pm=function(_1pn,_1po,_){while(1){var _1pp=E(_1pn);if(!_1pp._){return E(_);}else{var _=_1pk[_1po]=_1pp.a;if(_1po!=(_1pl-1|0)){var _1pq=_1po+1|0;_1pn=_1pp.b;_1po=_1pq;continue;}else{return E(_);}}}},_=B(_1pm(_1oM,0,_));return new T4(0,E(_1eQ),E(_1pg),_1pl,_1pk);}}else{return E(_1do);}};if(0>_1pg){return new F(function(){return _1ph(0);});}else{return new F(function(){return _1ph(_1pg+1|0);});}},_1pr=B(_1dp(_1pf)),_1ps=E(_1pr.a),_1pt=E(_1pr.b),_1pu=E(_1ov);if(_1ps>_1pu){return B(_1md(_1pu,_1ps,_1pt));}else{if(_1pu>_1pt){return B(_1md(_1pu,_1ps,_1pt));}else{return E(_1pr.d[_1pu-_1ps|0]);}}});switch(E(_1pd)){case 97:var _1pv=new T(function(){var _1pw=E(_1pc);if(!_1pw._){return E(_1mU);}else{return new T2(0,_1pw.a,_1pw.b);}}),_1px=new T(function(){var _1py=B(_1gN(E(_1pv).b));return new T2(0,_1py.a,_1py.b);}),_1pz=B(_KK(B(_x7(_1eP,new T(function(){return E(E(_1px).b);})))));if(!_1pz._){return E(_1eN);}else{if(!E(_1pz.b)._){var _1pA=new T(function(){var _1pB=B(_KK(B(_x7(_1eP,new T(function(){return E(E(_1px).a);})))));if(!_1pB._){return E(_1eN);}else{if(!E(_1pB.b)._){return E(_1pB.a);}else{return E(_1eO);}}},1);return {_:0,a:E({_:0,a:E(_1ox),b:E(B(_Pt(_1pA,E(_1pz.a),new T(function(){return E(E(_1pv).a);}),_II,_1oy))),c:E(_1oz),d:_1oA,e:_1oB,f:_1oC,g:E(_1oD),h:_1oE,i:E(B(_x(_1oF,_1pb))),j:E(_1oG),k:E(_1oH)}),b:E(_1oI),c:E(_1oJ),d:E(_1oK),e:E(_1oL),f:E(_1oM),g:E(_1oN),h:E(_1oO),i:_1oP,j:_1oQ,k:_1oR,l:_1oS,m:E(_1oT),n:_1oU,o:E(_1oV),p:E(_1oW),q:_1oX,r:E(_1oY),s:E(_1oZ),t:_1p0,u:E({_:0,a:E(_1p1),b:E(_1p2),c:E(_1p3),d:E(_1p4),e:E(_1p5),f:E(_1p6),g:E(_1p7),h:E(_1p8),i:E(_1p9)}),v:E(_1pa)};}else{return E(_1eO);}}break;case 104:return {_:0,a:E({_:0,a:E(_1ox),b:E(B(_1of(_1oy))),c:E(_1oz),d:_1oA,e:_1oB,f:_1oC,g:E(_1oD),h:_1oE,i:E(B(_x(_1oF,_1pb))),j:E(_1oG),k:E(_1oH)}),b:E(_1oI),c:E(_1oJ),d:E(_1oK),e:E(_1oL),f:E(_1oM),g:E(_1oN),h:E(_1oO),i:_1oP,j:_1oQ,k:_1oR,l:_1oS,m:E(_1oT),n:_1oU,o:E(_1oV),p:E(_1oW),q:_1oX,r:E(_1oY),s:E(_1oZ),t:_1p0,u:E({_:0,a:E(_1p1),b:E(_1p2),c:E(_1p3),d:E(_1p4),e:E(_1p5),f:E(_1p6),g:E(_1p7),h:E(_1p8),i:E(_1p9)}),v:E(_1pa)};case 106:var _1pC=E(_1pc);if(!_1pC._){return {_:0,a:E({_:0,a:E(_1ox),b:E(_1oy),c:E(_1oz),d:_1oA,e:_1oB,f:_1oC,g:E(_1oD),h:_1oE,i:E(B(_x(_1oF,_1pb))),j:E(_1oG),k:E(_1oH)}),b:E(_1oI),c:E(_1oJ),d:E(_1oK),e:E(_1oL),f:E(_1oM),g:E(_1oN),h:E(_1oO),i:_1oP,j:_1oQ,k:_1oR,l: -1,m:E(_1oT),n:_1oU,o:E(_1oV),p:E(_1oW),q:_1oX,r:E(_1oY),s:E(_1oZ),t:_1p0,u:E({_:0,a:E(_1p1),b:E(_1p2),c:E(_1p3),d:E(_1p4),e:E(_1p5),f:E(_1p6),g:E(_1p7),h:E(_1p8),i:E(_1p9)}),v:E(_1pa)};}else{if(E(_1pC.a)==108){var _1pD=E(_1ov),_1pE=B(_KK(B(_x7(_1eP,_1pC.b))));return (_1pE._==0)?E(_1eN):(E(_1pE.b)._==0)?{_:0,a:E({_:0,a:E(_1ox),b:E(_1oy),c:E(_1oz),d:_1oA,e:_1oB,f:_1oC,g:E(_1oD),h:_1oE,i:E(B(_x(_1oF,_1pb))),j:E(_1oG),k:E(_1oH)}),b:E(_1oI),c:E(_1oJ),d:E(_1oK),e:E(B(_1eq(_1pD,_1oL))),f:E(B(_1eq(_1pD,_1oM))),g:E(_1oN),h:E(_1oO),i:_1oP,j:_1oQ,k:_1oR,l:E(_1pE.a),m:E(_1oT),n:_1oU,o:E(_1oV),p:E(_1oW),q:_1oX,r:E(_1oY),s:E(_1oZ),t:_1p0,u:E({_:0,a:E(_B3),b:E(_1p2),c:E(_1p3),d:E(_1p4),e:E(_1p5),f:E(_1p6),g:E(_1p7),h:E(_1p8),i:E(_1p9)}),v:E(_1pa)}:E(_1eO);}else{var _1pF=B(_KK(B(_x7(_1eP,_1pC))));return (_1pF._==0)?E(_1eN):(E(_1pF.b)._==0)?{_:0,a:E({_:0,a:E(_1ox),b:E(_1oy),c:E(_1oz),d:_1oA,e:_1oB,f:_1oC,g:E(_1oD),h:_1oE,i:E(B(_x(_1oF,_1pb))),j:E(_1oG),k:E(_1oH)}),b:E(_1oI),c:E(_1oJ),d:E(_1oK),e:E(_1oL),f:E(_1oM),g:E(_1oN),h:E(_1oO),i:_1oP,j:_1oQ,k:_1oR,l:E(_1pF.a),m:E(_1oT),n:_1oU,o:E(_1oV),p:E(_1oW),q:_1oX,r:E(_1oY),s:E(_1oZ),t:_1p0,u:E({_:0,a:E(_1p1),b:E(_1p2),c:E(_1p3),d:E(_1p4),e:E(_1p5),f:E(_1p6),g:E(_1p7),h:E(_1p8),i:E(_1p9)}),v:E(_1pa)}:E(_1eO);}}break;case 108:var _1pG=E(_1ov);return {_:0,a:E({_:0,a:E(_1ox),b:E(_1oy),c:E(_1oz),d:_1oA,e:_1oB,f:_1oC,g:E(_1oD),h:_1oE,i:E(B(_x(_1oF,_1pb))),j:E(_1oG),k:E(_1oH)}),b:E(_1oI),c:E(_1oJ),d:E(_1oK),e:E(B(_1eq(_1pG,_1oL))),f:E(B(_1eq(_1pG,_1oM))),g:E(_1oN),h:E(_1oO),i:_1oP,j:_1oQ,k:_1oR,l:_1oS,m:E(_1oT),n:_1oU,o:E(_1oV),p:E(_1oW),q:_1oX,r:E(_1oY),s:E(_1oZ),t:_1p0,u:E({_:0,a:E(_B3),b:E(_1p2),c:E(_1p3),d:E(_1p4),e:E(_1p5),f:E(_1p6),g:E(_1p7),h:E(_1p8),i:E(_1p9)}),v:E(_1pa)};case 109:var _1pH=B(_1eS(E(_1pe),_1pc)),_1pI=_1pH.c,_1pJ=B(_vl(_1pI,_Z));if(!E(_1pJ)){var _1pK=E(_1ov),_1pL=new T(function(){var _1pM=function(_){var _1pN=B(_qy(_1oL,0))-1|0,_1pO=function(_1pP){if(_1pP>=0){var _1pQ=newArr(_1pP,_1cu),_1pR=_1pQ,_1pS=E(_1pP);if(!_1pS){return new T4(0,E(_1eQ),E(_1pN),0,_1pR);}else{var _1pT=function(_1pU,_1pV,_){while(1){var _1pW=E(_1pU);if(!_1pW._){return E(_);}else{var _=_1pR[_1pV]=_1pW.a;if(_1pV!=(_1pS-1|0)){var _1pX=_1pV+1|0;_1pU=_1pW.b;_1pV=_1pX;continue;}else{return E(_);}}}},_=B(_1pT(_1oL,0,_));return new T4(0,E(_1eQ),E(_1pN),_1pS,_1pR);}}else{return E(_1do);}};if(0>_1pN){return new F(function(){return _1pO(0);});}else{return new F(function(){return _1pO(_1pN+1|0);});}},_1pY=B(_1dp(_1pM)),_1pZ=E(_1pY.a),_1q0=E(_1pY.b);if(_1pZ>_1pK){return B(_1md(_1pK,_1pZ,_1q0));}else{if(_1pK>_1q0){return B(_1md(_1pK,_1pZ,_1q0));}else{return E(E(_1pY.d[_1pK-_1pZ|0]).a);}}}),_1q1=B(_1fh(_1pK,new T2(0,_1pL,new T2(1,_1pd,_1pI)),_1oL));}else{var _1q1=B(_1gZ(_1ov,_1oL));}if(!E(_1pJ)){var _1q2=B(_1fh(E(_1ov),_1pH.a,_1oM));}else{var _1q2=B(_1gZ(_1ov,_1oM));}return {_:0,a:E({_:0,a:E(_1ox),b:E(_1oy),c:E(_1oz),d:_1oA,e:_1oB,f:_1oC,g:E(_1oD),h:_1oE,i:E(B(_x(_1oF,_1pb))),j:E(_1oG),k:E(_1oH)}),b:E(_1oI),c:E(B(_1lv(_1oK,_1pH.b))),d:E(_1oK),e:E(_1q1),f:E(_1q2),g:E(_1oN),h:E(_1oO),i:_1oP,j:_1oQ,k:_1oR,l:_1oS,m:E(_1oT),n:_1oU,o:E(_1oV),p:E(_1oW),q:_1oX,r:E(_1oY),s:E(_1oZ),t:_1p0,u:E({_:0,a:E(_1p1),b:E(_1p2),c:E(_B3),d:E(_1p4),e:E(_1p5),f:E(_1p6),g:E(_1p7),h:E(_1p8),i:E(_1p9)}),v:E(_1pa)};case 114:var _1q3=B(_aW(_1m0,_1oC));return {_:0,a:E({_:0,a:E(B(_aW(_1mb,_1oC))),b:E(B(_1fX(_1q3.a,E(_1q3.b),new T(function(){return B(_aW(_1o5,_1oC));})))),c:E(_1oz),d:B(_aW(_1mo,_1oC)),e:32,f:_1oC,g:E(_1oD),h:_1oE,i:E(B(_x(_1oF,_1pb))),j:E(_1oG),k:E(_1oH)}),b:E(_1q3),c:E(_1mi),d:E(_1oK),e:E(_1oL),f:E(B(_aj(_1ml,_1oM))),g:E(_1oN),h:E(_1oO),i:_1oP,j:_1oQ,k:_1oR,l:_1oS,m:E(_1oT),n:_1oU,o:E(_1oV),p:E(_1oW),q:_1oX,r:E(_1oY),s:E(_1oZ),t:_1p0,u:E({_:0,a:E(_1p1),b:E(_1p2),c:E(_B3),d:E(_1p4),e:E(_1p5),f:E(_1p6),g:E(_1p7),h:E(_1p8),i:E(_1p9)}),v:E(_1pa)};case 115:return {_:0,a:E({_:0,a:E(_1ox),b:E(B(_1or(_1oy))),c:E(_1oz),d:_1oA,e:_1oB,f:_1oC,g:E(_1oD),h:_1oE,i:E(B(_x(_1oF,_1pb))),j:E(_1oG),k:E(_1oH)}),b:E(_1oI),c:E(_1oJ),d:E(_1oK),e:E(_1oL),f:E(_1oM),g:E(_1oN),h:E(_1oO),i:_1oP,j:_1oQ,k:_1oR,l:_1oS,m:E(_1oT),n:_1oU,o:E(_1oV),p:E(_1oW),q:_1oX,r:E(_1oY),s:E(_1oZ),t:_1p0,u:E({_:0,a:E(_1p1),b:E(_1p2),c:E(_1p3),d:E(_1p4),e:E(_1p5),f:E(_1p6),g:E(_1p7),h:E(_1p8),i:E(_1p9)}),v:E(_1pa)};case 116:var _1q4=E(_1pe),_1q5=B(_1eS(_1q4,_1pc)),_1q6=E(_1q5.a);if(!E(_1q6)){var _1q7=true;}else{var _1q7=false;}if(!E(_1q7)){var _1q8=B(_1fh(E(_1ov),_1q6,_1oM));}else{var _1q8=B(_1fh(E(_1ov),_1q4+1|0,_1oM));}if(!E(_1q7)){var _1q9=__Z;}else{var _1q9=E(_1q5.b);}if(!B(_vl(_1q9,_Z))){var _1qa=B(_1ou(_1ov,_1q9,_1ox,_1oy,_1oz,_1oA,_1oB,_1oC,_1oD,_1oE,_1oF,_1oG,_1oH,_1oI,_1oJ,_1oK,_1oL,_1q8,_1oN,_1oO,_1oP,_1oQ,_1oR,_1oS,_1oT,_1oU,_1oV,_1oW,_1oX,_1oY,_1oZ,_1p0,_1p1,_1p2,_1p3,_1p4,_1p5,_1p6,_1p7,_1p8,_1p9,_1pa)),_1qb=E(_1qa.a);return {_:0,a:E({_:0,a:E(_1qb.a),b:E(_1qb.b),c:E(_1qb.c),d:_1qb.d,e:_1qb.e,f:_1qb.f,g:E(_1qb.g),h:_1qb.h,i:E(B(_x(_1oF,_1pb))),j:E(_1qb.j),k:E(_1qb.k)}),b:E(_1qa.b),c:E(_1qa.c),d:E(_1qa.d),e:E(_1qa.e),f:E(_1qa.f),g:E(_1qa.g),h:E(_1qa.h),i:_1qa.i,j:_1qa.j,k:_1qa.k,l:_1qa.l,m:E(_1qa.m),n:_1qa.n,o:E(_1qa.o),p:E(_1qa.p),q:_1qa.q,r:E(_1qa.r),s:E(_1qa.s),t:_1qa.t,u:E(_1qa.u),v:E(_1qa.v)};}else{return {_:0,a:E({_:0,a:E(_1ox),b:E(_1oy),c:E(_1oz),d:_1oA,e:_1oB,f:_1oC,g:E(_1oD),h:_1oE,i:E(B(_x(_1oF,_1pb))),j:E(_1oG),k:E(_1oH)}),b:E(_1oI),c:E(_1oJ),d:E(_1oK),e:E(_1oL),f:E(_1q8),g:E(_1oN),h:E(_1oO),i:_1oP,j:_1oQ,k:_1oR,l:_1oS,m:E(_1oT),n:_1oU,o:E(_1oV),p:E(_1oW),q:_1oX,r:E(_1oY),s:E(_1oZ),t:_1p0,u:E({_:0,a:E(_1p1),b:E(_1p2),c:E(_1p3),d:E(_1p4),e:E(_1p5),f:E(_1p6),g:E(_1p7),h:E(_1p8),i:E(_1p9)}),v:E(_1pa)};}break;case 119:return {_:0,a:E({_:0,a:E(_1m2),b:E(_1mT),c:E(_1oz),d:E(_1mp),e:32,f:0,g:E(_1oD),h:_1oE,i:E(B(_x(_1oF,_1pb))),j:E(_1oG),k:E(_1oH)}),b:E(_1lN),c:E(_1mk),d:E(_1oK),e:E(_1oL),f:E(B(_aj(_1ml,_1oM))),g:E(_1oN),h:E(_1oO),i:_1oP,j:_1oQ,k:_1oR,l:_1oS,m:E(_1oT),n:_1oU,o:E(_1oV),p:E(_1oW),q:_1oX,r:E(_1oY),s:E(_1oZ),t:_1p0,u:E({_:0,a:E(_1p1),b:E(_1p2),c:E(_B3),d:E(_1p4),e:E(_1p5),f:E(_1p6),g:E(_1p7),h:E(_1p8),i:E(_1p9)}),v:E(_1pa)};default:return {_:0,a:E({_:0,a:E(_1ox),b:E(_1oy),c:E(_1oz),d:_1oA,e:_1oB,f:_1oC,g:E(_1oD),h:_1oE,i:E(B(_x(_1oF,_1pb))),j:E(_1oG),k:E(_1oH)}),b:E(_1oI),c:E(_1oJ),d:E(_1oK),e:E(_1oL),f:E(_1oM),g:E(_1oN),h:E(_1oO),i:_1oP,j:_1oQ,k:_1oR,l:_1oS,m:E(_1oT),n:_1oU,o:E(_1oV),p:E(_1oW),q:_1oX,r:E(_1oY),s:E(_1oZ),t:_1p0,u:E({_:0,a:E(_1p1),b:E(_1p2),c:E(_1p3),d:E(_1p4),e:E(_1p5),f:E(_1p6),g:E(_1p7),h:E(_1p8),i:E(_1p9)}),v:E(_1pa)};}}},_1qc=function(_1qd,_1qe){while(1){var _1qf=E(_1qe);if(!_1qf._){return __Z;}else{var _1qg=_1qf.b,_1qh=E(_1qd);if(_1qh==1){return E(_1qg);}else{_1qd=_1qh-1|0;_1qe=_1qg;continue;}}}},_1qi=new T(function(){return B(unCStr("X"));}),_1qj=new T(function(){return B(_ic("Check.hs:(87,7)-(92,39)|function chAnd"));}),_1qk=38,_1ql=function(_1qm,_1qn,_1qo,_1qp,_1qq,_1qr,_1qs,_1qt,_1qu,_1qv,_1qw,_1qx,_1qy,_1qz,_1qA,_1qB,_1qC,_1qD,_1qE,_1qF,_1qG,_1qH,_1qI,_1qJ,_1qK){var _1qL=E(_1qo);if(!_1qL._){return {_:0,a:_1qp,b:_1qq,c:_1qr,d:_1qs,e:_1qt,f:_1qu,g:_1qv,h:_1qw,i:_1qx,j:_1qy,k:_1qz,l:_1qA,m:_1qB,n:_1qC,o:_1qD,p:_1qE,q:_1qF,r:_1qG,s:_1qH,t:_1qI,u:_1qJ,v:_1qK};}else{var _1qM=_1qL.b,_1qN=E(_1qL.a),_1qO=_1qN.a,_1qP=_1qN.b,_1qQ=function(_1qR,_1qS,_1qT){var _1qU=function(_1qV,_1qW){if(!B(_vl(_1qV,_Z))){var _1qX=E(_1qp),_1qY=E(_1qJ),_1qZ=B(_1ou(_1qW,_1qV,_1qX.a,_1qX.b,_1qX.c,_1qX.d,_1qX.e,_1qX.f,_1qX.g,_1qX.h,_1qX.i,_1qX.j,_1qX.k,_1qq,_1qr,_1qs,_1qt,_1qu,_1qv,_1qw,_1qx,_1qy,_1qz,_1qA,_1qB,_1qC,_1qD,_1qE,_1qF,_1qG,_1qH,_1qI,_1qY.a,_1qY.b,_1qY.c,_1qY.d,_1qY.e,_1qY.f,_1qY.g,_1qY.h,_1qY.i,_1qK)),_1r0=_1qZ.a,_1r1=_1qZ.b,_1r2=_1qZ.c,_1r3=_1qZ.d,_1r4=_1qZ.e,_1r5=_1qZ.f,_1r6=_1qZ.g,_1r7=_1qZ.h,_1r8=_1qZ.i,_1r9=_1qZ.j,_1ra=_1qZ.k,_1rb=_1qZ.l,_1rc=_1qZ.m,_1rd=_1qZ.n,_1re=_1qZ.o,_1rf=_1qZ.p,_1rg=_1qZ.q,_1rh=_1qZ.r,_1ri=_1qZ.s,_1rj=_1qZ.t,_1rk=_1qZ.u,_1rl=_1qZ.v;if(B(_qy(_1r5,0))!=B(_qy(_1qu,0))){return {_:0,a:_1r0,b:_1r1,c:_1r2,d:_1r3,e:_1r4,f:_1r5,g:_1r6,h:_1r7,i:_1r8,j:_1r9,k:_1ra,l:_1rb,m:_1rc,n:_1rd,o:_1re,p:_1rf,q:_1rg,r:_1rh,s:_1ri,t:_1rj,u:_1rk,v:_1rl};}else{return new F(function(){return _1ql(new T(function(){return E(_1qm)+1|0;}),_1qn,_1qM,_1r0,_1r1,_1r2,_1r3,_1r4,_1r5,_1r6,_1r7,_1r8,_1r9,_1ra,_1rb,_1rc,_1rd,_1re,_1rf,_1rg,_1rh,_1ri,_1rj,_1rk,_1rl);});}}else{return new F(function(){return _1ql(new T(function(){return E(_1qm)+1|0;}),_1qn,_1qM,_1qp,_1qq,_1qr,_1qs,_1qt,_1qu,_1qv,_1qw,_1qx,_1qy,_1qz,_1qA,_1qB,_1qC,_1qD,_1qE,_1qF,_1qG,_1qH,_1qI,_1qJ,_1qK);});}},_1rm=B(_qy(_1qn,0))-B(_qy(new T2(1,_1qR,_1qS),0))|0;if(_1rm>0){var _1rn=B(_1qc(_1rm,_1qn));}else{var _1rn=E(_1qn);}if(E(B(_1e8(_1qR,_1qS,_ZZ)))==63){var _1ro=B(_Yg(_1qR,_1qS));}else{var _1ro=new T2(1,_1qR,_1qS);}var _1rp=function(_1rq){if(!B(_4H(_lc,_1qk,_1qO))){return new T2(0,_1qP,_1qm);}else{var _1rr=function(_1rs){while(1){var _1rt=B((function(_1ru){var _1rv=E(_1ru);if(!_1rv._){return true;}else{var _1rw=_1rv.b,_1rx=E(_1rv.a);if(!_1rx._){return E(_1qj);}else{switch(E(_1rx.a)){case 99:var _1ry=E(_1qp);if(!E(_1ry.k)){return false;}else{var _1rz=function(_1rA){while(1){var _1rB=E(_1rA);if(!_1rB._){return true;}else{var _1rC=_1rB.b,_1rD=E(_1rB.a);if(!_1rD._){return E(_1qj);}else{if(E(_1rD.a)==115){var _1rE=B(_KK(B(_x7(_1eP,_1rD.b))));if(!_1rE._){return E(_1eN);}else{if(!E(_1rE.b)._){if(_1ry.f!=E(_1rE.a)){return false;}else{_1rA=_1rC;continue;}}else{return E(_1eO);}}}else{_1rA=_1rC;continue;}}}}};return new F(function(){return _1rz(_1rw);});}break;case 115:var _1rF=E(_1qp),_1rG=_1rF.f,_1rH=B(_KK(B(_x7(_1eP,_1rx.b))));if(!_1rH._){return E(_1eN);}else{if(!E(_1rH.b)._){if(_1rG!=E(_1rH.a)){return false;}else{var _1rI=function(_1rJ){while(1){var _1rK=E(_1rJ);if(!_1rK._){return true;}else{var _1rL=_1rK.b,_1rM=E(_1rK.a);if(!_1rM._){return E(_1qj);}else{switch(E(_1rM.a)){case 99:if(!E(_1rF.k)){return false;}else{_1rJ=_1rL;continue;}break;case 115:var _1rN=B(_KK(B(_x7(_1eP,_1rM.b))));if(!_1rN._){return E(_1eN);}else{if(!E(_1rN.b)._){if(_1rG!=E(_1rN.a)){return false;}else{_1rJ=_1rL;continue;}}else{return E(_1eO);}}break;default:_1rJ=_1rL;continue;}}}}};return new F(function(){return _1rI(_1rw);});}}else{return E(_1eO);}}break;default:_1rs=_1rw;return __continue;}}}})(_1rs));if(_1rt!=__continue){return _1rt;}}};return (!B(_1rr(_1qT)))?(!B(_vl(_1ro,_1qi)))?new T2(0,_Z,_1qm):new T2(0,_1qP,_1qm):new T2(0,_1qP,_1qm);}};if(E(B(_1eg(_1qR,_1qS,_ZZ)))==63){if(!B(_ae(_1rn,_Z))){var _1rO=E(_1rn);if(!_1rO._){return E(_Yl);}else{if(!B(_vl(_1ro,B(_Yg(_1rO.a,_1rO.b))))){if(!B(_vl(_1ro,_1qi))){return new F(function(){return _1qU(_Z,_1qm);});}else{return new F(function(){return _1qU(_1qP,_1qm);});}}else{var _1rP=B(_1rp(_));return new F(function(){return _1qU(_1rP.a,_1rP.b);});}}}else{if(!B(_vl(_1ro,_1rn))){if(!B(_vl(_1ro,_1qi))){return new F(function(){return _1qU(_Z,_1qm);});}else{return new F(function(){return _1qU(_1qP,_1qm);});}}else{var _1rQ=B(_1rp(_));return new F(function(){return _1qU(_1rQ.a,_1rQ.b);});}}}else{if(!B(_vl(_1ro,_1rn))){if(!B(_vl(_1ro,_1qi))){return new F(function(){return _1qU(_Z,_1qm);});}else{return new F(function(){return _1qU(_1qP,_1qm);});}}else{var _1rR=B(_1rp(_));return new F(function(){return _1qU(_1rR.a,_1rR.b);});}}},_1rS=E(_1qO);if(!_1rS._){return E(_ZZ);}else{var _1rT=_1rS.a,_1rU=E(_1rS.b);if(!_1rU._){return new F(function(){return _1qQ(_1rT,_Z,_Z);});}else{var _1rV=E(_1rT),_1rW=new T(function(){var _1rX=B(_LC(38,_1rU.a,_1rU.b));return new T2(0,_1rX.a,_1rX.b);});if(E(_1rV)==38){return E(_ZZ);}else{return new F(function(){return _1qQ(_1rV,new T(function(){return E(E(_1rW).a);}),new T(function(){return E(E(_1rW).b);}));});}}}}},_1rY="]",_1rZ="}",_1s0=":",_1s1=",",_1s2=new T(function(){return eval("JSON.stringify");}),_1s3="false",_1s4="null",_1s5="[",_1s6="{",_1s7="\"",_1s8="true",_1s9=function(_1sa,_1sb){var _1sc=E(_1sb);switch(_1sc._){case 0:return new T2(0,new T(function(){return jsShow(_1sc.a);}),_1sa);case 1:return new T2(0,new T(function(){var _1sd=__app1(E(_1s2),_1sc.a);return String(_1sd);}),_1sa);case 2:return (!E(_1sc.a))?new T2(0,_1s3,_1sa):new T2(0,_1s8,_1sa);case 3:var _1se=E(_1sc.a);if(!_1se._){return new T2(0,_1s5,new T2(1,_1rY,_1sa));}else{var _1sf=new T(function(){var _1sg=new T(function(){var _1sh=function(_1si){var _1sj=E(_1si);if(!_1sj._){return E(new T2(1,_1rY,_1sa));}else{var _1sk=new T(function(){var _1sl=B(_1s9(new T(function(){return B(_1sh(_1sj.b));}),_1sj.a));return new T2(1,_1sl.a,_1sl.b);});return new T2(1,_1s1,_1sk);}};return B(_1sh(_1se.b));}),_1sm=B(_1s9(_1sg,_1se.a));return new T2(1,_1sm.a,_1sm.b);});return new T2(0,_1s5,_1sf);}break;case 4:var _1sn=E(_1sc.a);if(!_1sn._){return new T2(0,_1s6,new T2(1,_1rZ,_1sa));}else{var _1so=E(_1sn.a),_1sp=new T(function(){var _1sq=new T(function(){var _1sr=function(_1ss){var _1st=E(_1ss);if(!_1st._){return E(new T2(1,_1rZ,_1sa));}else{var _1su=E(_1st.a),_1sv=new T(function(){var _1sw=B(_1s9(new T(function(){return B(_1sr(_1st.b));}),_1su.b));return new T2(1,_1sw.a,_1sw.b);});return new T2(1,_1s1,new T2(1,_1s7,new T2(1,_1su.a,new T2(1,_1s7,new T2(1,_1s0,_1sv)))));}};return B(_1sr(_1sn.b));}),_1sx=B(_1s9(_1sq,_1so.b));return new T2(1,_1sx.a,_1sx.b);});return new T2(0,_1s6,new T2(1,new T(function(){var _1sy=__app1(E(_1s2),E(_1so.a));return String(_1sy);}),new T2(1,_1s0,_1sp)));}break;default:return new T2(0,_1s4,_1sa);}},_1sz=new T(function(){return toJSStr(_Z);}),_1sA=function(_1sB){var _1sC=B(_1s9(_Z,_1sB)),_1sD=jsCat(new T2(1,_1sC.a,_1sC.b),E(_1sz));return E(_1sD);},_1sE=function(_1sF){var _1sG=E(_1sF);if(!_1sG._){return new T2(0,_Z,_Z);}else{var _1sH=E(_1sG.a),_1sI=new T(function(){var _1sJ=B(_1sE(_1sG.b));return new T2(0,_1sJ.a,_1sJ.b);});return new T2(0,new T2(1,_1sH.a,new T(function(){return E(E(_1sI).a);})),new T2(1,_1sH.b,new T(function(){return E(E(_1sI).b);})));}},_1sK=new T(function(){return B(unCStr("Rk"));}),_1sL=function(_1sM,_1sN,_1sO,_1sP,_1sQ,_1sR,_1sS,_1sT,_1sU,_1sV,_1sW,_1sX,_1sY,_1sZ,_1t0,_1t1,_1t2,_1t3,_1t4,_1t5,_1t6,_1t7,_1t8){while(1){var _1t9=B((function(_1ta,_1tb,_1tc,_1td,_1te,_1tf,_1tg,_1th,_1ti,_1tj,_1tk,_1tl,_1tm,_1tn,_1to,_1tp,_1tq,_1tr,_1ts,_1tt,_1tu,_1tv,_1tw){var _1tx=E(_1ta);if(!_1tx._){return {_:0,a:_1tb,b:_1tc,c:_1td,d:_1te,e:_1tf,f:_1tg,g:_1th,h:_1ti,i:_1tj,j:_1tk,k:_1tl,l:_1tm,m:_1tn,n:_1to,o:_1tp,p:_1tq,q:_1tr,r:_1ts,s:_1tt,t:_1tu,u:_1tv,v:_1tw};}else{var _1ty=_1tx.a,_1tz=B(_YG(B(unAppCStr("e.e",new T2(1,_1ty,new T(function(){return B(unAppCStr(".m0:",new T2(1,_1ty,_1sK)));})))),_1tb,_1tc,_1td,_1te,_1tf,_1tg,_1th,_1ti,_1tj,_1tk,_1tl,_1tm,_1tn,_1to,_1tp,_1tq,_1tr,_1ts,_1tt,_1tu,_1tv,_1tw));_1sM=_1tx.b;_1sN=_1tz.a;_1sO=_1tz.b;_1sP=_1tz.c;_1sQ=_1tz.d;_1sR=_1tz.e;_1sS=_1tz.f;_1sT=_1tz.g;_1sU=_1tz.h;_1sV=_1tz.i;_1sW=_1tz.j;_1sX=_1tz.k;_1sY=_1tz.l;_1sZ=_1tz.m;_1t0=_1tz.n;_1t1=_1tz.o;_1t2=_1tz.p;_1t3=_1tz.q;_1t4=_1tz.r;_1t5=_1tz.s;_1t6=_1tz.t;_1t7=_1tz.u;_1t8=_1tz.v;return __continue;}})(_1sM,_1sN,_1sO,_1sP,_1sQ,_1sR,_1sS,_1sT,_1sU,_1sV,_1sW,_1sX,_1sY,_1sZ,_1t0,_1t1,_1t2,_1t3,_1t4,_1t5,_1t6,_1t7,_1t8));if(_1t9!=__continue){return _1t9;}}},_1tA=function(_1tB){var _1tC=E(_1tB);switch(_1tC){case 68:return 100;case 72:return 104;case 74:return 106;case 75:return 107;case 76:return 108;case 78:return 110;case 82:return 114;case 83:return 115;default:if(_1tC>>>0>1114111){return new F(function(){return _Bd(_1tC);});}else{return _1tC;}}},_1tD=function(_1tE,_1tF,_1tG){while(1){var _1tH=E(_1tF);if(!_1tH._){return (E(_1tG)._==0)?true:false;}else{var _1tI=E(_1tG);if(!_1tI._){return false;}else{if(!B(A3(_4F,_1tE,_1tH.a,_1tI.a))){return false;}else{_1tF=_1tH.b;_1tG=_1tI.b;continue;}}}}},_1tJ=function(_1tK,_1tL){return (!B(_1tD(_vS,_1tK,_1tL)))?true:false;},_1tM=function(_1tN,_1tO){return new F(function(){return _1tD(_vS,_1tN,_1tO);});},_1tP=new T2(0,_1tM,_1tJ),_1tQ=function(_1tR){var _1tS=E(_1tR);if(!_1tS._){return new T2(0,_Z,_Z);}else{var _1tT=E(_1tS.a),_1tU=new T(function(){var _1tV=B(_1tQ(_1tS.b));return new T2(0,_1tV.a,_1tV.b);});return new T2(0,new T2(1,_1tT.a,new T(function(){return E(E(_1tU).a);})),new T2(1,_1tT.b,new T(function(){return E(E(_1tU).b);})));}},_1tW=function(_1tX,_1tY){while(1){var _1tZ=E(_1tY);if(!_1tZ._){return __Z;}else{var _1u0=_1tZ.b,_1u1=E(_1tX);if(_1u1==1){return E(_1u0);}else{_1tX=_1u1-1|0;_1tY=_1u0;continue;}}}},_1u2=function(_1u3,_1u4){while(1){var _1u5=E(_1u4);if(!_1u5._){return __Z;}else{var _1u6=_1u5.b,_1u7=E(_1u3);if(_1u7==1){return E(_1u6);}else{_1u3=_1u7-1|0;_1u4=_1u6;continue;}}}},_1u8=function(_1u9){return new F(function(){return _KR(_1u9,_Z);});},_1ua=function(_1ub,_1uc,_1ud,_1ue){var _1uf=new T(function(){return B(_Rj(_lc,_1uc,_1ud));}),_1ug=new T(function(){var _1uh=E(_1uf),_1ui=new T(function(){var _1uj=_1uh+1|0;if(_1uj>0){return B(_1u2(_1uj,_1ud));}else{return E(_1ud);}});if(0>=_1uh){return E(_1ui);}else{var _1uk=function(_1ul,_1um){var _1un=E(_1ul);if(!_1un._){return E(_1ui);}else{var _1uo=_1un.a,_1up=E(_1um);return (_1up==1)?new T2(1,_1uo,_1ui):new T2(1,_1uo,new T(function(){return B(_1uk(_1un.b,_1up-1|0));}));}};return B(_1uk(_1ud,_1uh));}}),_1uq=new T(function(){var _1ur=E(_1uf),_1us=new T(function(){if(E(_1uc)==94){return B(A2(_1ub,new T(function(){return B(_aW(_1ue,_1ur+1|0));}),new T(function(){return B(_aW(_1ue,_1ur));})));}else{return B(A2(_1ub,new T(function(){return B(_aW(_1ue,_1ur));}),new T(function(){return B(_aW(_1ue,_1ur+1|0));})));}}),_1ut=new T2(1,_1us,new T(function(){var _1uu=_1ur+2|0;if(_1uu>0){return B(_1tW(_1uu,_1ue));}else{return E(_1ue);}}));if(0>=_1ur){return E(_1ut);}else{var _1uv=function(_1uw,_1ux){var _1uy=E(_1uw);if(!_1uy._){return E(_1ut);}else{var _1uz=_1uy.a,_1uA=E(_1ux);return (_1uA==1)?new T2(1,_1uz,_1ut):new T2(1,_1uz,new T(function(){return B(_1uv(_1uy.b,_1uA-1|0));}));}};return B(_1uv(_1ue,_1ur));}});return (E(_1uc)==94)?new T2(0,new T(function(){return B(_1u8(_1ug));}),new T(function(){return B(_1u8(_1uq));})):new T2(0,_1ug,_1uq);},_1uB=new T(function(){return B(_gs(_th,_tg));}),_1uC=function(_1uD,_1uE,_1uF){while(1){if(!E(_1uB)){if(!B(_gs(B(_18D(_1uE,_th)),_tg))){if(!B(_gs(_1uE,_f0))){var _1uG=B(_sK(_1uD,_1uD)),_1uH=B(_18o(B(_iT(_1uE,_f0)),_th)),_1uI=B(_sK(_1uD,_1uF));_1uD=_1uG;_1uE=_1uH;_1uF=_1uI;continue;}else{return new F(function(){return _sK(_1uD,_1uF);});}}else{var _1uG=B(_sK(_1uD,_1uD)),_1uH=B(_18o(_1uE,_th));_1uD=_1uG;_1uE=_1uH;continue;}}else{return E(_dZ);}}},_1uJ=function(_1uK,_1uL){while(1){if(!E(_1uB)){if(!B(_gs(B(_18D(_1uL,_th)),_tg))){if(!B(_gs(_1uL,_f0))){return new F(function(){return _1uC(B(_sK(_1uK,_1uK)),B(_18o(B(_iT(_1uL,_f0)),_th)),_1uK);});}else{return E(_1uK);}}else{var _1uM=B(_sK(_1uK,_1uK)),_1uN=B(_18o(_1uL,_th));_1uK=_1uM;_1uL=_1uN;continue;}}else{return E(_dZ);}}},_1uO=function(_1uP,_1uQ){if(!B(_hc(_1uQ,_tg))){if(!B(_gs(_1uQ,_tg))){return new F(function(){return _1uJ(_1uP,_1uQ);});}else{return E(_f0);}}else{return E(_tW);}},_1uR=94,_1uS=45,_1uT=43,_1uU=42,_1uV=function(_1uW,_1uX){while(1){var _1uY=B((function(_1uZ,_1v0){var _1v1=E(_1v0);if(!_1v1._){return __Z;}else{if((B(_qy(_1uZ,0))+1|0)==B(_qy(_1v1,0))){if(!B(_4H(_lc,_1uR,_1uZ))){if(!B(_4H(_lc,_1uU,_1uZ))){if(!B(_4H(_lc,_1uT,_1uZ))){if(!B(_4H(_lc,_1uS,_1uZ))){return E(_1v1);}else{var _1v2=B(_1ua(_iT,45,_1uZ,_1v1));_1uW=_1v2.a;_1uX=_1v2.b;return __continue;}}else{var _1v3=B(_1ua(_gA,43,_1uZ,_1v1));_1uW=_1v3.a;_1uX=_1v3.b;return __continue;}}else{var _1v4=B(_1ua(_sK,42,_1uZ,_1v1));_1uW=_1v4.a;_1uX=_1v4.b;return __continue;}}else{var _1v5=B(_1ua(_1uO,94,new T(function(){return B(_1u8(_1uZ));}),new T(function(){return B(_KR(_1v1,_Z));})));_1uW=_1v5.a;_1uX=_1v5.b;return __continue;}}else{return __Z;}}})(_1uW,_1uX));if(_1uY!=__continue){return _1uY;}}},_1v6=function(_1v7){var _1v8=E(_1v7);if(!_1v8._){return new T2(0,_Z,_Z);}else{var _1v9=E(_1v8.a),_1va=new T(function(){var _1vb=B(_1v6(_1v8.b));return new T2(0,_1vb.a,_1vb.b);});return new T2(0,new T2(1,_1v9.a,new T(function(){return E(E(_1va).a);})),new T2(1,_1v9.b,new T(function(){return E(E(_1va).b);})));}},_1vc=new T(function(){return B(unCStr("0123456789+-"));}),_1vd=function(_1ve){while(1){var _1vf=E(_1ve);if(!_1vf._){return true;}else{if(!B(_4H(_lc,_1vf.a,_1vc))){return false;}else{_1ve=_1vf.b;continue;}}}},_1vg=new T(function(){return B(err(_wY));}),_1vh=new T(function(){return B(err(_x2));}),_1vi=function(_1vj,_1vk){var _1vl=function(_1vm,_1vn){var _1vo=function(_1vp){return new F(function(){return A1(_1vn,new T(function(){return B(_jy(_1vp));}));});},_1vq=new T(function(){return B(_HG(function(_1vr){return new F(function(){return A3(_1vj,_1vr,_1vm,_1vo);});}));}),_1vs=function(_1vt){return E(_1vq);},_1vu=function(_1vv){return new F(function(){return A2(_Gn,_1vv,_1vs);});},_1vw=new T(function(){return B(_HG(function(_1vx){var _1vy=E(_1vx);if(_1vy._==4){var _1vz=E(_1vy.a);if(!_1vz._){return new F(function(){return A3(_1vj,_1vy,_1vm,_1vn);});}else{if(E(_1vz.a)==45){if(!E(_1vz.b)._){return E(new T1(1,_1vu));}else{return new F(function(){return A3(_1vj,_1vy,_1vm,_1vn);});}}else{return new F(function(){return A3(_1vj,_1vy,_1vm,_1vn);});}}}else{return new F(function(){return A3(_1vj,_1vy,_1vm,_1vn);});}}));}),_1vA=function(_1vB){return E(_1vw);};return new T1(1,function(_1vC){return new F(function(){return A2(_Gn,_1vC,_1vA);});});};return new F(function(){return _Ix(_1vl,_1vk);});},_1vD=function(_1vE){var _1vF=E(_1vE);if(_1vF._==5){var _1vG=B(_Kt(_1vF.a));return (_1vG._==0)?E(_Ky):function(_1vH,_1vI){return new F(function(){return A1(_1vI,_1vG.a);});};}else{return E(_Ky);}},_1vJ=new T(function(){return B(A3(_1vi,_1vD,_Id,_K0));}),_1vK=function(_1vL,_1vM){var _1vN=E(_1vM);if(!_1vN._){return __Z;}else{var _1vO=_1vN.a,_1vP=_1vN.b,_1vQ=function(_1vR){var _1vS=B(_1v6(_1vL)),_1vT=_1vS.a;return (!B(_4H(_uJ,_1vO,_1vT)))?__Z:new T2(1,new T(function(){return B(_aW(_1vS.b,B(_Rj(_uJ,_1vO,_1vT))));}),new T(function(){return B(_1vK(_1vL,_1vP));}));};if(!B(_ae(_1vO,_Z))){if(!B(_1vd(_1vO))){return new F(function(){return _1vQ(_);});}else{return new T2(1,new T(function(){var _1vU=B(_KK(B(_x7(_1vJ,_1vO))));if(!_1vU._){return E(_1vg);}else{if(!E(_1vU.b)._){return E(_1vU.a);}else{return E(_1vh);}}}),new T(function(){return B(_1vK(_1vL,_1vP));}));}}else{return new F(function(){return _1vQ(_);});}}},_1vV=new T(function(){return B(unCStr("+-*^"));}),_1vW=new T(function(){return B(unCStr("0123456789"));}),_1vX=new T(function(){return B(_PU("Siki.hs:12:9-28|(hn : ns, cs)"));}),_1vY=new T2(1,_Z,_Z),_1vZ=function(_1w0){var _1w1=E(_1w0);if(!_1w1._){return new T2(0,_1vY,_Z);}else{var _1w2=_1w1.a,_1w3=new T(function(){var _1w4=B(_1vZ(_1w1.b)),_1w5=E(_1w4.a);if(!_1w5._){return E(_1vX);}else{return new T3(0,_1w5.a,_1w5.b,_1w4.b);}});return (!B(_4H(_lc,_1w2,_1vW)))?(!B(_4H(_lc,_1w2,_1vV)))?new T2(0,new T2(1,new T2(1,_1w2,new T(function(){return E(E(_1w3).a);})),new T(function(){return E(E(_1w3).b);})),new T(function(){return E(E(_1w3).c);})):new T2(0,new T2(1,_Z,new T2(1,new T(function(){return E(E(_1w3).a);}),new T(function(){return E(E(_1w3).b);}))),new T2(1,_1w2,new T(function(){return E(E(_1w3).c);}))):new T2(0,new T2(1,new T2(1,_1w2,new T(function(){return E(E(_1w3).a);})),new T(function(){return E(E(_1w3).b);})),new T(function(){return E(E(_1w3).c);}));}},_1w6=function(_1w7,_1w8){var _1w9=new T(function(){var _1wa=B(_1vZ(_1w8)),_1wb=E(_1wa.a);if(!_1wb._){return E(_1vX);}else{return new T3(0,_1wb.a,_1wb.b,_1wa.b);}});return (!B(_4H(_lc,_1w7,_1vW)))?(!B(_4H(_lc,_1w7,_1vV)))?new T2(0,new T2(1,new T2(1,_1w7,new T(function(){return E(E(_1w9).a);})),new T(function(){return E(E(_1w9).b);})),new T(function(){return E(E(_1w9).c);})):new T2(0,new T2(1,_Z,new T2(1,new T(function(){return E(E(_1w9).a);}),new T(function(){return E(E(_1w9).b);}))),new T2(1,_1w7,new T(function(){return E(E(_1w9).c);}))):new T2(0,new T2(1,new T2(1,_1w7,new T(function(){return E(E(_1w9).a);})),new T(function(){return E(E(_1w9).b);})),new T(function(){return E(E(_1w9).c);}));},_1wc=function(_1wd,_1we){while(1){var _1wf=E(_1wd);if(!_1wf._){return E(_1we);}else{_1wd=_1wf.b;_1we=_1wf.a;continue;}}},_1wg=function(_1wh,_1wi,_1wj){return new F(function(){return _1wc(_1wi,_1wh);});},_1wk=function(_1wl,_1wm){var _1wn=E(_1wm);if(!_1wn._){return __Z;}else{var _1wo=B(_1w6(_1wn.a,_1wn.b)),_1wp=B(_1uV(_1wo.b,B(_1vK(_1wl,_1wo.a))));if(!_1wp._){return E(_1wn);}else{return new F(function(){return _1aH(0,B(_1wg(_1wp.a,_1wp.b,_ZZ)),_Z);});}}},_1wq=function(_1wr,_1ws){var _1wt=function(_1wu,_1wv){while(1){var _1ww=B((function(_1wx,_1wy){var _1wz=E(_1wy);if(!_1wz._){return (!B(_vl(_1wx,_Z)))?new T2(0,_B3,_1wx):new T2(0,_B2,_Z);}else{var _1wA=_1wz.b,_1wB=B(_1tQ(_1wz.a)).a;if(!B(_4H(_lc,_1gh,_1wB))){var _1wC=_1wx;_1wu=_1wC;_1wv=_1wA;return __continue;}else{var _1wD=B(_1gN(_1wB)),_1wE=_1wD.a,_1wF=_1wD.b;if(!B(_ae(_1wF,_Z))){if(!B(_vl(B(_1wk(_1wr,_1wE)),B(_1wk(_1wr,_1wF))))){return new T2(0,_B2,_Z);}else{var _1wG=new T(function(){if(!B(_vl(_1wx,_Z))){return B(_x(_1wx,new T(function(){return B(unAppCStr(" ",_1wE));},1)));}else{return E(_1wE);}});_1wu=_1wG;_1wv=_1wA;return __continue;}}else{return new T2(0,_B2,_Z);}}}})(_1wu,_1wv));if(_1ww!=__continue){return _1ww;}}};return new F(function(){return _1wt(_Z,_1ws);});},_1wH=function(_1wI,_1wJ){var _1wK=new T(function(){var _1wL=B(_KK(B(_x7(_1ax,new T(function(){return B(_uj(3,B(_H(0,imul(E(_1wJ),E(_1wI)-1|0)|0,_Z))));})))));if(!_1wL._){return E(_1aw);}else{if(!E(_1wL.b)._){return E(_1wL.a);}else{return E(_1av);}}});return new T2(0,new T(function(){return B(_eA(_1wK,_1wI));}),_1wK);},_1wM=function(_1wN,_1wO){while(1){var _1wP=E(_1wO);if(!_1wP._){return __Z;}else{var _1wQ=_1wP.b,_1wR=E(_1wN);if(_1wR==1){return E(_1wQ);}else{_1wN=_1wR-1|0;_1wO=_1wQ;continue;}}}},_1wS=function(_1wT,_1wU){while(1){var _1wV=E(_1wU);if(!_1wV._){return __Z;}else{var _1wW=_1wV.b,_1wX=E(_1wT);if(_1wX==1){return E(_1wW);}else{_1wT=_1wX-1|0;_1wU=_1wW;continue;}}}},_1wY=64,_1wZ=new T2(1,_1wY,_Z),_1x0=function(_1x1,_1x2,_1x3,_1x4){return (!B(_vl(_1x1,_1x3)))?true:(!B(_gs(_1x2,_1x4)))?true:false;},_1x5=function(_1x6,_1x7){var _1x8=E(_1x6),_1x9=E(_1x7);return new F(function(){return _1x0(_1x8.a,_1x8.b,_1x9.a,_1x9.b);});},_1xa=function(_1xb,_1xc,_1xd,_1xe){if(!B(_vl(_1xb,_1xd))){return false;}else{return new F(function(){return _gs(_1xc,_1xe);});}},_1xf=function(_1xg,_1xh){var _1xi=E(_1xg),_1xj=E(_1xh);return new F(function(){return _1xa(_1xi.a,_1xi.b,_1xj.a,_1xj.b);});},_1xk=new T2(0,_1xf,_1x5),_1xl=function(_1xm){var _1xn=E(_1xm);if(!_1xn._){return new T2(0,_Z,_Z);}else{var _1xo=E(_1xn.a),_1xp=new T(function(){var _1xq=B(_1xl(_1xn.b));return new T2(0,_1xq.a,_1xq.b);});return new T2(0,new T2(1,_1xo.a,new T(function(){return E(E(_1xp).a);})),new T2(1,_1xo.b,new T(function(){return E(E(_1xp).b);})));}},_1xr=function(_1xs){var _1xt=E(_1xs);if(!_1xt._){return new T2(0,_Z,_Z);}else{var _1xu=E(_1xt.a),_1xv=new T(function(){var _1xw=B(_1xr(_1xt.b));return new T2(0,_1xw.a,_1xw.b);});return new T2(0,new T2(1,_1xu.a,new T(function(){return E(E(_1xv).a);})),new T2(1,_1xu.b,new T(function(){return E(E(_1xv).b);})));}},_1xx=function(_1xy){var _1xz=E(_1xy);if(!_1xz._){return new T2(0,_Z,_Z);}else{var _1xA=E(_1xz.a),_1xB=new T(function(){var _1xC=B(_1xx(_1xz.b));return new T2(0,_1xC.a,_1xC.b);});return new T2(0,new T2(1,_1xA.a,new T(function(){return E(E(_1xB).a);})),new T2(1,_1xA.b,new T(function(){return E(E(_1xB).b);})));}},_1xD=function(_1xE,_1xF){return (_1xE<=_1xF)?new T2(1,_1xE,new T(function(){return B(_1xD(_1xE+1|0,_1xF));})):__Z;},_1xG=new T(function(){return B(_1xD(65,90));}),_1xH=function(_1xI){return (_1xI<=122)?new T2(1,_1xI,new T(function(){return B(_1xH(_1xI+1|0));})):E(_1xG);},_1xJ=new T(function(){return B(_1xH(97));}),_1xK=function(_1xL){while(1){var _1xM=E(_1xL);if(!_1xM._){return true;}else{if(!B(_4H(_lc,_1xM.a,_1xJ))){return false;}else{_1xL=_1xM.b;continue;}}}},_1xN=new T2(0,_Z,_Z),_1xO=new T(function(){return B(err(_wY));}),_1xP=new T(function(){return B(err(_x2));}),_1xQ=new T(function(){return B(A3(_1vi,_1vD,_Id,_K0));}),_1xR=function(_1xS,_1xT,_1xU){while(1){var _1xV=B((function(_1xW,_1xX,_1xY){var _1xZ=E(_1xY);if(!_1xZ._){return __Z;}else{var _1y0=_1xZ.b,_1y1=B(_1xr(_1xX)),_1y2=_1y1.a,_1y3=B(_1xl(_1y2)),_1y4=_1y3.a,_1y5=new T(function(){return E(B(_1xx(_1xZ.a)).a);}),_1y6=new T(function(){return B(_4H(_lc,_1gh,_1y5));}),_1y7=new T(function(){if(!E(_1y6)){return E(_1xN);}else{var _1y8=B(_1gN(_1y5));return new T2(0,_1y8.a,_1y8.b);}}),_1y9=new T(function(){return E(E(_1y7).a);}),_1ya=new T(function(){return B(_Rj(_uJ,_1y9,_1y4));}),_1yb=new T(function(){var _1yc=function(_){var _1yd=B(_qy(_1xX,0))-1|0,_1ye=function(_1yf){if(_1yf>=0){var _1yg=newArr(_1yf,_1cu),_1yh=_1yg,_1yi=E(_1yf);if(!_1yi){return new T4(0,E(_1eQ),E(_1yd),0,_1yh);}else{var _1yj=function(_1yk,_1yl,_){while(1){var _1ym=E(_1yk);if(!_1ym._){return E(_);}else{var _=_1yh[_1yl]=_1ym.a;if(_1yl!=(_1yi-1|0)){var _1yn=_1yl+1|0;_1yk=_1ym.b;_1yl=_1yn;continue;}else{return E(_);}}}},_=B(_1yj(_1y1.b,0,_));return new T4(0,E(_1eQ),E(_1yd),_1yi,_1yh);}}else{return E(_1do);}};if(0>_1yd){return new F(function(){return _1ye(0);});}else{return new F(function(){return _1ye(_1yd+1|0);});}};return B(_1dp(_1yc));});if(!B(_4H(_uJ,_1y9,_1y4))){var _1yo=false;}else{var _1yp=E(_1yb),_1yq=E(_1yp.a),_1yr=E(_1yp.b),_1ys=E(_1ya);if(_1yq>_1ys){var _1yt=B(_1md(_1ys,_1yq,_1yr));}else{if(_1ys>_1yr){var _1yu=B(_1md(_1ys,_1yq,_1yr));}else{var _1yu=E(_1yp.d[_1ys-_1yq|0])==E(_1xW);}var _1yt=_1yu;}var _1yo=_1yt;}var _1yv=new T(function(){return E(E(_1y7).b);}),_1yw=new T(function(){return B(_Rj(_uJ,_1yv,_1y4));}),_1yx=new T(function(){if(!B(_4H(_uJ,_1yv,_1y4))){return false;}else{var _1yy=E(_1yb),_1yz=E(_1yy.a),_1yA=E(_1yy.b),_1yB=E(_1yw);if(_1yz>_1yB){return B(_1md(_1yB,_1yz,_1yA));}else{if(_1yB>_1yA){return B(_1md(_1yB,_1yz,_1yA));}else{return E(_1yy.d[_1yB-_1yz|0])==E(_1xW);}}}}),_1yC=new T(function(){var _1yD=function(_){var _1yE=B(_qy(_1y2,0))-1|0,_1yF=function(_1yG){if(_1yG>=0){var _1yH=newArr(_1yG,_1cu),_1yI=_1yH,_1yJ=E(_1yG);if(!_1yJ){return new T4(0,E(_1eQ),E(_1yE),0,_1yI);}else{var _1yK=function(_1yL,_1yM,_){while(1){var _1yN=E(_1yL);if(!_1yN._){return E(_);}else{var _=_1yI[_1yM]=_1yN.a;if(_1yM!=(_1yJ-1|0)){var _1yO=_1yM+1|0;_1yL=_1yN.b;_1yM=_1yO;continue;}else{return E(_);}}}},_=B(_1yK(_1y3.b,0,_));return new T4(0,E(_1eQ),E(_1yE),_1yJ,_1yI);}}else{return E(_1do);}};if(0>_1yE){return new F(function(){return _1yF(0);});}else{return new F(function(){return _1yF(_1yE+1|0);});}};return B(_1dp(_1yD));}),_1yP=function(_1yQ){var _1yR=function(_1yS){return (!E(_1yo))?__Z:(!E(_1yx))?__Z:new T2(1,new T2(0,_1y9,new T(function(){var _1yT=E(_1yC),_1yU=E(_1yT.a),_1yV=E(_1yT.b),_1yW=E(_1ya);if(_1yU>_1yW){return B(_1md(_1yW,_1yU,_1yV));}else{if(_1yW>_1yV){return B(_1md(_1yW,_1yU,_1yV));}else{return E(_1yT.d[_1yW-_1yU|0]);}}})),new T2(1,new T2(0,_1yv,new T(function(){var _1yX=E(_1yC),_1yY=E(_1yX.a),_1yZ=E(_1yX.b),_1z0=E(_1yw);if(_1yY>_1z0){return B(_1md(_1z0,_1yY,_1yZ));}else{if(_1z0>_1yZ){return B(_1md(_1z0,_1yY,_1yZ));}else{return E(_1yX.d[_1z0-_1yY|0]);}}})),_Z));};if(!E(_1yo)){if(!E(_1yx)){return new F(function(){return _1yR(_);});}else{return new T2(1,new T2(0,_1yv,new T(function(){var _1z1=E(_1yC),_1z2=E(_1z1.a),_1z3=E(_1z1.b),_1z4=E(_1yw);if(_1z2>_1z4){return B(_1md(_1z4,_1z2,_1z3));}else{if(_1z4>_1z3){return B(_1md(_1z4,_1z2,_1z3));}else{return E(_1z1.d[_1z4-_1z2|0]);}}})),_Z);}}else{return new F(function(){return _1yR(_);});}};if(!E(_1yo)){var _1z5=B(_1yP(_));}else{if(!E(_1yx)){var _1z6=new T2(1,new T2(0,_1y9,new T(function(){var _1z7=E(_1yC),_1z8=E(_1z7.a),_1z9=E(_1z7.b),_1za=E(_1ya);if(_1z8>_1za){return B(_1md(_1za,_1z8,_1z9));}else{if(_1za>_1z9){return B(_1md(_1za,_1z8,_1z9));}else{return E(_1z7.d[_1za-_1z8|0]);}}})),_Z);}else{var _1z6=B(_1yP(_));}var _1z5=_1z6;}if(!B(_1tD(_1xk,_1z5,_Z))){return new F(function(){return _x(_1z5,new T(function(){return B(_1xR(_1xW,_1xX,_1y0));},1));});}else{if(!E(_1y6)){var _1zb=_1xW,_1zc=_1xX;_1xS=_1zb;_1xT=_1zc;_1xU=_1y0;return __continue;}else{if(!B(_1xK(_1y9))){if(!B(_1xK(_1yv))){var _1zb=_1xW,_1zc=_1xX;_1xS=_1zb;_1xT=_1zc;_1xU=_1y0;return __continue;}else{if(!E(_1yo)){if(!E(_1yx)){if(!B(_ae(_1y9,_Z))){if(!B(_1vd(_1y9))){var _1zb=_1xW,_1zc=_1xX;_1xS=_1zb;_1xT=_1zc;_1xU=_1y0;return __continue;}else{return new T2(1,new T2(0,_1yv,new T(function(){var _1zd=B(_KK(B(_x7(_1xQ,_1y9))));if(!_1zd._){return E(_1xO);}else{if(!E(_1zd.b)._){return E(_1zd.a);}else{return E(_1xP);}}})),new T(function(){return B(_1xR(_1xW,_1xX,_1y0));}));}}else{var _1zb=_1xW,_1zc=_1xX;_1xS=_1zb;_1xT=_1zc;_1xU=_1y0;return __continue;}}else{var _1zb=_1xW,_1zc=_1xX;_1xS=_1zb;_1xT=_1zc;_1xU=_1y0;return __continue;}}else{var _1zb=_1xW,_1zc=_1xX;_1xS=_1zb;_1xT=_1zc;_1xU=_1y0;return __continue;}}}else{if(!E(_1yo)){if(!E(_1yx)){if(!B(_ae(_1yv,_Z))){if(!B(_1vd(_1yv))){if(!B(_1xK(_1yv))){var _1zb=_1xW,_1zc=_1xX;_1xS=_1zb;_1xT=_1zc;_1xU=_1y0;return __continue;}else{if(!B(_ae(_1y9,_Z))){if(!B(_1vd(_1y9))){var _1zb=_1xW,_1zc=_1xX;_1xS=_1zb;_1xT=_1zc;_1xU=_1y0;return __continue;}else{return new T2(1,new T2(0,_1yv,new T(function(){var _1ze=B(_KK(B(_x7(_1xQ,_1y9))));if(!_1ze._){return E(_1xO);}else{if(!E(_1ze.b)._){return E(_1ze.a);}else{return E(_1xP);}}})),new T(function(){return B(_1xR(_1xW,_1xX,_1y0));}));}}else{var _1zb=_1xW,_1zc=_1xX;_1xS=_1zb;_1xT=_1zc;_1xU=_1y0;return __continue;}}}else{return new T2(1,new T2(0,_1y9,new T(function(){var _1zf=B(_KK(B(_x7(_1xQ,_1yv))));if(!_1zf._){return E(_1xO);}else{if(!E(_1zf.b)._){return E(_1zf.a);}else{return E(_1xP);}}})),new T(function(){return B(_1xR(_1xW,_1xX,_1y0));}));}}else{if(!B(_1xK(_1yv))){var _1zb=_1xW,_1zc=_1xX;_1xS=_1zb;_1xT=_1zc;_1xU=_1y0;return __continue;}else{if(!B(_ae(_1y9,_Z))){if(!B(_1vd(_1y9))){var _1zb=_1xW,_1zc=_1xX;_1xS=_1zb;_1xT=_1zc;_1xU=_1y0;return __continue;}else{return new T2(1,new T2(0,_1yv,new T(function(){var _1zg=B(_KK(B(_x7(_1xQ,_1y9))));if(!_1zg._){return E(_1xO);}else{if(!E(_1zg.b)._){return E(_1zg.a);}else{return E(_1xP);}}})),new T(function(){return B(_1xR(_1xW,_1xX,_1y0));}));}}else{var _1zb=_1xW,_1zc=_1xX;_1xS=_1zb;_1xT=_1zc;_1xU=_1y0;return __continue;}}}}else{var _1zh=B(_1xK(_1yv)),_1zb=_1xW,_1zc=_1xX;_1xS=_1zb;_1xT=_1zc;_1xU=_1y0;return __continue;}}else{var _1zi=B(_1xK(_1yv)),_1zb=_1xW,_1zc=_1xX;_1xS=_1zb;_1xT=_1zc;_1xU=_1y0;return __continue;}}}}}})(_1xS,_1xT,_1xU));if(_1xV!=__continue){return _1xV;}}},_1zj=102,_1zk=101,_1zl=new T(function(){return B(unCStr("=="));}),_1zm=new T(function(){return B(_ic("Action.hs:(103,17)-(107,70)|case"));}),_1zn=new T(function(){return B(_ic("Action.hs:(118,9)-(133,75)|function wnMove\'"));}),_1zo=5,_1zp=117,_1zq=98,_1zr=110,_1zs=118,_1zt=function(_1zu,_1zv,_1zw,_1zx,_1zy,_1zz,_1zA,_1zB,_1zC,_1zD,_1zE,_1zF,_1zG,_1zH){var _1zI=B(_aW(B(_aW(_1zy,_1zv)),_1zu)),_1zJ=_1zI.a,_1zK=_1zI.b;if(E(_1zB)==32){if(!B(_4H(_lc,_1zJ,_1wZ))){var _1zL=false;}else{switch(E(_1zK)){case 0:var _1zM=true;break;case 1:var _1zM=false;break;case 2:var _1zM=false;break;case 3:var _1zM=false;break;case 4:var _1zM=false;break;case 5:var _1zM=false;break;case 6:var _1zM=false;break;case 7:var _1zM=false;break;default:var _1zM=false;}var _1zL=_1zM;}var _1zN=_1zL;}else{var _1zN=false;}if(E(_1zB)==32){if(E(_1zJ)==32){var _1zO=false;}else{switch(E(_1zK)){case 0:if(!E(_1zN)){var _1zP=true;}else{var _1zP=false;}var _1zQ=_1zP;break;case 1:var _1zQ=false;break;case 2:var _1zQ=false;break;case 3:var _1zQ=false;break;case 4:var _1zQ=false;break;case 5:var _1zQ=false;break;case 6:var _1zQ=false;break;case 7:var _1zQ=false;break;default:if(!E(_1zN)){var _1zR=true;}else{var _1zR=false;}var _1zQ=_1zR;}var _1zO=_1zQ;}var _1zS=_1zO;}else{var _1zS=false;}var _1zT=new T(function(){return B(_Pt(_1zu,_1zv,new T(function(){if(!E(_1zS)){if(!E(_1zN)){return E(_1zJ);}else{return _1zA;}}else{return E(_11W);}}),_1zK,_1zy));});switch(E(_1zK)){case 3:var _1zU=true;break;case 4:if(E(_1zB)==32){var _1zV=true;}else{var _1zV=false;}var _1zU=_1zV;break;default:var _1zU=false;}if(!E(_1zU)){var _1zW=E(_1zT);}else{var _1zX=E(_1zw),_1zY=new T(function(){return B(_aW(_1zT,_1zv));}),_1zZ=function(_1A0,_1A1){var _1A2=E(_1A0);if(_1A2==( -1)){return E(_1zT);}else{var _1A3=new T(function(){return B(_Pt(_1zu,_1zv,_11W,_II,_1zT));}),_1A4=E(_1A1);if(_1A4==( -1)){var _1A5=__Z;}else{var _1A5=B(_aW(_1A3,_1A4));}if(E(B(_aW(_1A5,_1A2)).a)==32){var _1A6=new T(function(){var _1A7=new T(function(){return B(_aW(_1zY,_1zu));}),_1A8=new T2(1,new T2(0,new T(function(){return E(E(_1A7).a);}),new T(function(){return E(E(_1A7).b);})),new T(function(){var _1A9=_1A2+1|0;if(_1A9>0){return B(_1wS(_1A9,_1A5));}else{return E(_1A5);}}));if(0>=_1A2){return E(_1A8);}else{var _1Aa=function(_1Ab,_1Ac){var _1Ad=E(_1Ab);if(!_1Ad._){return E(_1A8);}else{var _1Ae=_1Ad.a,_1Af=E(_1Ac);return (_1Af==1)?new T2(1,_1Ae,_1A8):new T2(1,_1Ae,new T(function(){return B(_1Aa(_1Ad.b,_1Af-1|0));}));}};return B(_1Aa(_1A5,_1A2));}}),_1Ag=new T2(1,_1A6,new T(function(){var _1Ah=_1A1+1|0;if(_1Ah>0){return B(_1wM(_1Ah,_1A3));}else{return E(_1A3);}}));if(0>=_1A1){return E(_1Ag);}else{var _1Ai=function(_1Aj,_1Ak){var _1Al=E(_1Aj);if(!_1Al._){return E(_1Ag);}else{var _1Am=_1Al.a,_1An=E(_1Ak);return (_1An==1)?new T2(1,_1Am,_1Ag):new T2(1,_1Am,new T(function(){return B(_1Ai(_1Al.b,_1An-1|0));}));}};return new F(function(){return _1Ai(_1A3,_1A1);});}}else{return E(_1zT);}}};if(_1zu<=_1zX){if(_1zX<=_1zu){var _1Ao=E(_1zx);if(_1zv<=_1Ao){if(_1Ao<=_1zv){var _1Ap=E(_1zm);}else{var _1Aq=E(_1zv);if(!_1Aq){var _1Ar=B(_1zZ( -1, -1));}else{var _1Ar=B(_1zZ(_1zu,_1Aq-1|0));}var _1Ap=_1Ar;}var _1As=_1Ap;}else{if(_1zv!=(B(_qy(_1zT,0))-1|0)){var _1At=B(_1zZ(_1zu,_1zv+1|0));}else{var _1At=B(_1zZ( -1, -1));}var _1As=_1At;}var _1Au=_1As;}else{var _1Av=E(_1zu);if(!_1Av){var _1Aw=B(_1zZ( -1, -1));}else{var _1Aw=B(_1zZ(_1Av-1|0,_1zv));}var _1Au=_1Aw;}var _1Ax=_1Au;}else{if(_1zu!=(B(_qy(_1zY,0))-1|0)){var _1Ay=B(_1zZ(_1zu+1|0,_1zv));}else{var _1Ay=B(_1zZ( -1, -1));}var _1Ax=_1Ay;}var _1zW=_1Ax;}if(!E(_1zG)){var _1Az=E(_1zW);}else{var _1AA=new T(function(){var _1AB=E(_1zW);if(!_1AB._){return E(_rm);}else{return B(_qy(_1AB.a,0));}}),_1AC=new T(function(){return B(_qy(_1zW,0));}),_1AD=function(_1AE,_1AF,_1AG,_1AH,_1AI,_1AJ,_1AK){while(1){var _1AL=B((function(_1AM,_1AN,_1AO,_1AP,_1AQ,_1AR,_1AS){var _1AT=E(_1AS);if(!_1AT._){return E(_1AP);}else{var _1AU=_1AT.b,_1AV=E(_1AT.a);if(!_1AV._){return E(_1zn);}else{var _1AW=_1AV.b,_1AX=E(_1AV.a);if(E(_1AX.b)==5){var _1AY=new T(function(){var _1AZ=B(_1wH(_1zo,_1AM));return new T2(0,_1AZ.a,_1AZ.b);}),_1B0=new T(function(){var _1B1=function(_1B2,_1B3){var _1B4=function(_1B5){return new F(function(){return _Pt(_1AN,_1AO,_11W,_II,new T(function(){return B(_Pt(_1B2,_1B3,_1AX.a,_Jx,_1AP));}));});};if(_1B2!=_1AN){return new F(function(){return _1B4(_);});}else{if(_1B3!=_1AO){return new F(function(){return _1B4(_);});}else{return E(_1AP);}}};switch(E(E(_1AY).a)){case 1:var _1B6=_1AN-1|0;if(_1B6<0){return B(_1B1(_1AN,_1AO));}else{if(_1B6>=E(_1AA)){return B(_1B1(_1AN,_1AO));}else{if(_1AO<0){return B(_1B1(_1AN,_1AO));}else{if(_1AO>=E(_1AC)){return B(_1B1(_1AN,_1AO));}else{if(_1B6!=_1AQ){if(E(B(_aW(B(_aW(_1AP,_1AO)),_1B6)).a)==32){return B(_1B1(_1B6,_1AO));}else{return B(_1B1(_1AN,_1AO));}}else{if(_1AO!=_1AR){if(E(B(_aW(B(_aW(_1AP,_1AO)),_1B6)).a)==32){return B(_1B1(_1B6,_1AO));}else{return B(_1B1(_1AN,_1AO));}}else{return B(_1B1(_1AN,_1AO));}}}}}}break;case 2:if(_1AN<0){return B(_1B1(_1AN,_1AO));}else{if(_1AN>=E(_1AA)){return B(_1B1(_1AN,_1AO));}else{var _1B7=_1AO-1|0;if(_1B7<0){return B(_1B1(_1AN,_1AO));}else{if(_1B7>=E(_1AC)){return B(_1B1(_1AN,_1AO));}else{if(_1AN!=_1AQ){if(E(B(_aW(B(_aW(_1AP,_1B7)),_1AN)).a)==32){return B(_1B1(_1AN,_1B7));}else{return B(_1B1(_1AN,_1AO));}}else{if(_1B7!=_1AR){if(E(B(_aW(B(_aW(_1AP,_1B7)),_1AN)).a)==32){return B(_1B1(_1AN,_1B7));}else{return B(_1B1(_1AN,_1AO));}}else{return B(_1B1(_1AN,_1AO));}}}}}}break;case 3:var _1B8=_1AN+1|0;if(_1B8<0){return B(_1B1(_1AN,_1AO));}else{if(_1B8>=E(_1AA)){return B(_1B1(_1AN,_1AO));}else{if(_1AO<0){return B(_1B1(_1AN,_1AO));}else{if(_1AO>=E(_1AC)){return B(_1B1(_1AN,_1AO));}else{if(_1B8!=_1AQ){if(E(B(_aW(B(_aW(_1AP,_1AO)),_1B8)).a)==32){return B(_1B1(_1B8,_1AO));}else{return B(_1B1(_1AN,_1AO));}}else{if(_1AO!=_1AR){if(E(B(_aW(B(_aW(_1AP,_1AO)),_1B8)).a)==32){return B(_1B1(_1B8,_1AO));}else{return B(_1B1(_1AN,_1AO));}}else{return B(_1B1(_1AN,_1AO));}}}}}}break;case 4:if(_1AN<0){return B(_1B1(_1AN,_1AO));}else{if(_1AN>=E(_1AA)){return B(_1B1(_1AN,_1AO));}else{var _1B9=_1AO+1|0;if(_1B9<0){return B(_1B1(_1AN,_1AO));}else{if(_1B9>=E(_1AC)){return B(_1B1(_1AN,_1AO));}else{if(_1AN!=_1AQ){if(E(B(_aW(B(_aW(_1AP,_1B9)),_1AN)).a)==32){return B(_1B1(_1AN,_1B9));}else{return B(_1B1(_1AN,_1AO));}}else{if(_1B9!=_1AR){if(E(B(_aW(B(_aW(_1AP,_1B9)),_1AN)).a)==32){return B(_1B1(_1AN,_1B9));}else{return B(_1B1(_1AN,_1AO));}}else{return B(_1B1(_1AN,_1AO));}}}}}}break;default:if(_1AN<0){return B(_1B1(_1AN,_1AO));}else{if(_1AN>=E(_1AA)){return B(_1B1(_1AN,_1AO));}else{if(_1AO<0){return B(_1B1(_1AN,_1AO));}else{if(_1AO>=E(_1AC)){return B(_1B1(_1AN,_1AO));}else{if(_1AN!=_1AQ){var _1Ba=E(B(_aW(B(_aW(_1AP,_1AO)),_1AN)).a);return B(_1B1(_1AN,_1AO));}else{if(_1AO!=_1AR){var _1Bb=E(B(_aW(B(_aW(_1AP,_1AO)),_1AN)).a);return B(_1B1(_1AN,_1AO));}else{return B(_1B1(_1AN,_1AO));}}}}}}}}),_1Bc=E(_1AW);if(!_1Bc._){var _1Bd=_1AO+1|0,_1Be=_1AQ,_1Bf=_1AR;_1AE=new T(function(){return E(E(_1AY).b);},1);_1AF=0;_1AG=_1Bd;_1AH=_1B0;_1AI=_1Be;_1AJ=_1Bf;_1AK=_1AU;return __continue;}else{return new F(function(){return _1Bg(new T(function(){return E(E(_1AY).b);},1),_1AN+1|0,_1AO,_1B0,_1AQ,_1AR,_1Bc.a,_1Bc.b,_1AU);});}}else{var _1Bh=E(_1AW);if(!_1Bh._){var _1Bi=_1AM,_1Bd=_1AO+1|0,_1Bj=_1AP,_1Be=_1AQ,_1Bf=_1AR;_1AE=_1Bi;_1AF=0;_1AG=_1Bd;_1AH=_1Bj;_1AI=_1Be;_1AJ=_1Bf;_1AK=_1AU;return __continue;}else{return new F(function(){return _1Bg(_1AM,_1AN+1|0,_1AO,_1AP,_1AQ,_1AR,_1Bh.a,_1Bh.b,_1AU);});}}}}})(_1AE,_1AF,_1AG,_1AH,_1AI,_1AJ,_1AK));if(_1AL!=__continue){return _1AL;}}},_1Bg=function(_1Bk,_1Bl,_1Bm,_1Bn,_1Bo,_1Bp,_1Bq,_1Br,_1Bs){while(1){var _1Bt=B((function(_1Bu,_1Bv,_1Bw,_1Bx,_1By,_1Bz,_1BA,_1BB,_1BC){var _1BD=E(_1BA);if(E(_1BD.b)==5){var _1BE=new T(function(){var _1BF=B(_1wH(_1zo,_1Bu));return new T2(0,_1BF.a,_1BF.b);}),_1BG=new T(function(){var _1BH=function(_1BI,_1BJ){var _1BK=function(_1BL){return new F(function(){return _Pt(_1Bv,_1Bw,_11W,_II,new T(function(){return B(_Pt(_1BI,_1BJ,_1BD.a,_Jx,_1Bx));}));});};if(_1BI!=_1Bv){return new F(function(){return _1BK(_);});}else{if(_1BJ!=_1Bw){return new F(function(){return _1BK(_);});}else{return E(_1Bx);}}};switch(E(E(_1BE).a)){case 1:var _1BM=_1Bv-1|0;if(_1BM<0){return B(_1BH(_1Bv,_1Bw));}else{if(_1BM>=E(_1AA)){return B(_1BH(_1Bv,_1Bw));}else{if(_1Bw<0){return B(_1BH(_1Bv,_1Bw));}else{if(_1Bw>=E(_1AC)){return B(_1BH(_1Bv,_1Bw));}else{if(_1BM!=_1By){if(E(B(_aW(B(_aW(_1Bx,_1Bw)),_1BM)).a)==32){return B(_1BH(_1BM,_1Bw));}else{return B(_1BH(_1Bv,_1Bw));}}else{if(_1Bw!=_1Bz){if(E(B(_aW(B(_aW(_1Bx,_1Bw)),_1BM)).a)==32){return B(_1BH(_1BM,_1Bw));}else{return B(_1BH(_1Bv,_1Bw));}}else{return B(_1BH(_1Bv,_1Bw));}}}}}}break;case 2:if(_1Bv<0){return B(_1BH(_1Bv,_1Bw));}else{if(_1Bv>=E(_1AA)){return B(_1BH(_1Bv,_1Bw));}else{var _1BN=_1Bw-1|0;if(_1BN<0){return B(_1BH(_1Bv,_1Bw));}else{if(_1BN>=E(_1AC)){return B(_1BH(_1Bv,_1Bw));}else{if(_1Bv!=_1By){if(E(B(_aW(B(_aW(_1Bx,_1BN)),_1Bv)).a)==32){return B(_1BH(_1Bv,_1BN));}else{return B(_1BH(_1Bv,_1Bw));}}else{if(_1BN!=_1Bz){if(E(B(_aW(B(_aW(_1Bx,_1BN)),_1Bv)).a)==32){return B(_1BH(_1Bv,_1BN));}else{return B(_1BH(_1Bv,_1Bw));}}else{return B(_1BH(_1Bv,_1Bw));}}}}}}break;case 3:var _1BO=_1Bv+1|0;if(_1BO<0){return B(_1BH(_1Bv,_1Bw));}else{if(_1BO>=E(_1AA)){return B(_1BH(_1Bv,_1Bw));}else{if(_1Bw<0){return B(_1BH(_1Bv,_1Bw));}else{if(_1Bw>=E(_1AC)){return B(_1BH(_1Bv,_1Bw));}else{if(_1BO!=_1By){if(E(B(_aW(B(_aW(_1Bx,_1Bw)),_1BO)).a)==32){return B(_1BH(_1BO,_1Bw));}else{return B(_1BH(_1Bv,_1Bw));}}else{if(_1Bw!=_1Bz){if(E(B(_aW(B(_aW(_1Bx,_1Bw)),_1BO)).a)==32){return B(_1BH(_1BO,_1Bw));}else{return B(_1BH(_1Bv,_1Bw));}}else{return B(_1BH(_1Bv,_1Bw));}}}}}}break;case 4:if(_1Bv<0){return B(_1BH(_1Bv,_1Bw));}else{if(_1Bv>=E(_1AA)){return B(_1BH(_1Bv,_1Bw));}else{var _1BP=_1Bw+1|0;if(_1BP<0){return B(_1BH(_1Bv,_1Bw));}else{if(_1BP>=E(_1AC)){return B(_1BH(_1Bv,_1Bw));}else{if(_1Bv!=_1By){if(E(B(_aW(B(_aW(_1Bx,_1BP)),_1Bv)).a)==32){return B(_1BH(_1Bv,_1BP));}else{return B(_1BH(_1Bv,_1Bw));}}else{if(_1BP!=_1Bz){if(E(B(_aW(B(_aW(_1Bx,_1BP)),_1Bv)).a)==32){return B(_1BH(_1Bv,_1BP));}else{return B(_1BH(_1Bv,_1Bw));}}else{return B(_1BH(_1Bv,_1Bw));}}}}}}break;default:if(_1Bv<0){return B(_1BH(_1Bv,_1Bw));}else{if(_1Bv>=E(_1AA)){return B(_1BH(_1Bv,_1Bw));}else{if(_1Bw<0){return B(_1BH(_1Bv,_1Bw));}else{if(_1Bw>=E(_1AC)){return B(_1BH(_1Bv,_1Bw));}else{if(_1Bv!=_1By){var _1BQ=E(B(_aW(B(_aW(_1Bx,_1Bw)),_1Bv)).a);return B(_1BH(_1Bv,_1Bw));}else{if(_1Bw!=_1Bz){var _1BR=E(B(_aW(B(_aW(_1Bx,_1Bw)),_1Bv)).a);return B(_1BH(_1Bv,_1Bw));}else{return B(_1BH(_1Bv,_1Bw));}}}}}}}}),_1BS=E(_1BB);if(!_1BS._){return new F(function(){return _1AD(new T(function(){return E(E(_1BE).b);},1),0,_1Bw+1|0,_1BG,_1By,_1Bz,_1BC);});}else{var _1BT=_1Bv+1|0,_1BU=_1Bw,_1BV=_1By,_1BW=_1Bz,_1BX=_1BC;_1Bk=new T(function(){return E(E(_1BE).b);},1);_1Bl=_1BT;_1Bm=_1BU;_1Bn=_1BG;_1Bo=_1BV;_1Bp=_1BW;_1Bq=_1BS.a;_1Br=_1BS.b;_1Bs=_1BX;return __continue;}}else{var _1BY=E(_1BB);if(!_1BY._){return new F(function(){return _1AD(_1Bu,0,_1Bw+1|0,_1Bx,_1By,_1Bz,_1BC);});}else{var _1BZ=_1Bu,_1BT=_1Bv+1|0,_1BU=_1Bw,_1C0=_1Bx,_1BV=_1By,_1BW=_1Bz,_1BX=_1BC;_1Bk=_1BZ;_1Bl=_1BT;_1Bm=_1BU;_1Bn=_1C0;_1Bo=_1BV;_1Bp=_1BW;_1Bq=_1BY.a;_1Br=_1BY.b;_1Bs=_1BX;return __continue;}}})(_1Bk,_1Bl,_1Bm,_1Bn,_1Bo,_1Bp,_1Bq,_1Br,_1Bs));if(_1Bt!=__continue){return _1Bt;}}},_1Az=B(_1AD(_1zE,0,0,_1zW,_1zu,_1zv,_1zW));}var _1C1=function(_1C2){var _1C3=function(_1C4){var _1C5=new T(function(){switch(E(_1zK)){case 1:return true;break;case 5:return true;break;case 7:return true;break;default:return false;}}),_1C6=new T(function(){if(!E(_1zU)){if(!E(_1C5)){return new T2(0,_1zu,_1zv);}else{return new T2(0,_1zw,_1zx);}}else{if(!B(_1tD(_1tP,_1Az,_1zT))){if(!E(_1C5)){return new T2(0,_1zu,_1zv);}else{return new T2(0,_1zw,_1zx);}}else{return new T2(0,_1zw,_1zx);}}}),_1C7=new T(function(){return E(E(_1C6).b);}),_1C8=new T(function(){return E(E(_1C6).a);});if(!E(_1zU)){var _1C9=E(_1zH);}else{var _1C9=E(B(_1wq(new T(function(){return B(_1xR(_1zC,_1zD,_1Az));}),_1Az)).a);}var _1Ca=new T(function(){if(!E(_1zS)){if(!E(_1zN)){var _1Cb=function(_1Cc){var _1Cd=function(_1Ce){var _1Cf=E(_1zK);if(_1Cf==4){return new T2(1,_1zr,new T2(1,_1zJ,_Z));}else{if(!E(_1C5)){return (E(_1Cf)==2)?new T2(1,_1zp,new T2(1,_1zJ,_Z)):__Z;}else{var _1Cg=E(_1zJ);return (E(_1Cg)==61)?new T2(1,_1zq,new T2(1,_1Cg,new T(function(){return B(_H(0,_1zv,_Z));}))):new T2(1,_1zq,new T2(1,_1Cg,_Z));}}};if(!E(_1zU)){return new F(function(){return _1Cd(_);});}else{if(E(_1zw)!=E(_1C8)){return new T2(1,_1zs,new T2(1,_1zJ,_Z));}else{if(E(_1zx)!=E(_1C7)){return new T2(1,_1zs,new T2(1,_1zJ,_Z));}else{return new F(function(){return _1Cd(_);});}}}};if(!E(_1zU)){return B(_1Cb(_));}else{if(!E(_1C9)){return B(_1Cb(_));}else{return E(_1zl);}}}else{return new T2(1,_1zj,new T2(1,_1zJ,_Z));}}else{return new T2(1,_1zk,new T2(1,_1zJ,_Z));}},1);return {_:0,a:E(new T2(0,_1C8,_1C7)),b:E(_1Az),c:E(_1zz),d:_1C2,e:_1C4,f:_1zC,g:E(_1zD),h:_1zE,i:E(B(_x(_1zF,_1Ca))),j:E(_1zG),k:E(_1C9)};};if(!E(_1zS)){return new F(function(){return _1C3(_1zB);});}else{return new F(function(){return _1C3(E(_1zJ));});}};if(!E(_1zN)){return new F(function(){return _1C1(_1zA);});}else{return new F(function(){return _1C1(E(_1zJ));});}},_1Ch=new T2(1,_61,_Z),_1Ci=5,_1Cj=new T2(1,_1Ci,_Z),_1Ck=function(_1Cl,_1Cm){while(1){var _1Cn=E(_1Cl);if(!_1Cn._){return E(_1Cm);}else{_1Cl=_1Cn.b;_1Cm=_1Cn.a;continue;}}},_1Co=57,_1Cp=48,_1Cq=new T2(1,_1wY,_Z),_1Cr=new T(function(){return B(err(_x2));}),_1Cs=new T(function(){return B(err(_wY));}),_1Ct=new T(function(){return B(A3(_K8,_KB,_Id,_K0));}),_1Cu=function(_1Cv,_1Cw){if((_1Cw-48|0)>>>0>9){var _1Cx=_1Cw+_1Cv|0,_1Cy=function(_1Cz){if(!B(_4H(_lc,_1Cz,_1Cq))){return E(_1Cz);}else{return new F(function(){return _1Cu(_1Cv,_1Cz);});}};if(_1Cx<=122){if(_1Cx>=97){if(_1Cx>>>0>1114111){return new F(function(){return _Bd(_1Cx);});}else{return new F(function(){return _1Cy(_1Cx);});}}else{if(_1Cx<=90){if(_1Cx>>>0>1114111){return new F(function(){return _Bd(_1Cx);});}else{return new F(function(){return _1Cy(_1Cx);});}}else{var _1CA=65+(_1Cx-90|0)|0;if(_1CA>>>0>1114111){return new F(function(){return _Bd(_1CA);});}else{return new F(function(){return _1Cy(_1CA);});}}}}else{var _1CB=97+(_1Cx-122|0)|0;if(_1CB>>>0>1114111){return new F(function(){return _Bd(_1CB);});}else{return new F(function(){return _1Cy(_1CB);});}}}else{var _1CC=B(_KK(B(_x7(_1Ct,new T2(1,_1Cw,_Z)))));if(!_1CC._){return E(_1Cs);}else{if(!E(_1CC.b)._){var _1CD=E(_1CC.a)+_1Cv|0;switch(_1CD){case  -1:return E(_1Cp);case 10:return E(_1Co);default:return new F(function(){return _1Ck(B(_H(0,_1CD,_Z)),_ZZ);});}}else{return E(_1Cr);}}}},_1CE=function(_1CF,_1CG){if((_1CF-48|0)>>>0>9){return _1CG;}else{var _1CH=B(_KK(B(_x7(_1Ct,new T2(1,_1CF,_Z)))));if(!_1CH._){return E(_1Cs);}else{if(!E(_1CH.b)._){return new F(function(){return _1Cu(E(_1CH.a),_1CG);});}else{return E(_1Cr);}}}},_1CI=function(_1CJ,_1CK){return new F(function(){return _1CE(E(_1CJ),E(_1CK));});},_1CL=new T2(1,_1CI,_Z),_1CM=112,_1CN=111,_1CO=function(_1CP,_1CQ,_1CR,_1CS,_1CT,_1CU,_1CV,_1CW,_1CX,_1CY,_1CZ,_1D0){var _1D1=new T(function(){return B(_aW(B(_aW(_1CR,_1CQ)),E(_1CP)));}),_1D2=new T(function(){return E(E(_1D1).b);}),_1D3=new T(function(){if(E(_1D2)==4){return true;}else{return false;}}),_1D4=new T(function(){return E(E(_1D1).a);});if(E(_1CU)==32){var _1D5=false;}else{if(E(_1D4)==32){var _1D6=true;}else{var _1D6=false;}var _1D5=_1D6;}var _1D7=new T(function(){var _1D8=new T(function(){return B(A3(_aW,_1Ch,B(_Rj(_lc,_1CT,_1wZ)),_1CU));});if(!E(_1D5)){if(!E(_1D3)){return E(_1D4);}else{if(!B(_4H(_3S,_1CV,_1Cj))){return E(_1D4);}else{return B(A(_aW,[_1CL,B(_Rj(_3S,_1CV,_1Cj)),_1D8,_1D4]));}}}else{return E(_1D8);}}),_1D9=B(_Pt(_1CP,_1CQ,_1D7,_1D2,_1CR)),_1Da=function(_1Db){var _1Dc=B(_1wq(new T(function(){return B(_1xR(_1CV,_1CW,_1D9));}),_1D9)).a;return {_:0,a:E(new T2(0,_1CP,_1CQ)),b:E(_1D9),c:E(_1CS),d:_1CT,e:_1Db,f:_1CV,g:E(_1CW),h:_1CX,i:E(B(_x(_1CY,new T(function(){if(!E(_1Dc)){if(!E(_1D5)){if(!E(_1D3)){return __Z;}else{return new T2(1,_1CM,new T2(1,_1D7,_Z));}}else{return new T2(1,_1CN,new T2(1,_1D7,_Z));}}else{return E(_1zl);}},1)))),j:E(_1CZ),k:E(_1Dc)};};if(!E(_1D5)){return new F(function(){return _1Da(_1CU);});}else{return new F(function(){return _1Da(32);});}},_1Dd=function(_1De,_1Df){while(1){var _1Dg=E(_1Df);if(!_1Dg._){return __Z;}else{var _1Dh=_1Dg.b,_1Di=E(_1De);if(_1Di==1){return E(_1Dh);}else{_1De=_1Di-1|0;_1Df=_1Dh;continue;}}}},_1Dj=4,_1Dk=new T(function(){return B(unCStr("\u5e74 "));}),_1Dl=function(_1Dm,_1Dn,_1Do,_1Dp,_1Dq){var _1Dr=new T(function(){var _1Ds=new T(function(){var _1Dt=new T(function(){var _1Du=new T(function(){var _1Dv=new T(function(){return B(_x(_1Do,new T(function(){return B(unAppCStr(" >>",_1Dp));},1)));});return B(unAppCStr(" >>",_1Dv));},1);return B(_x(_1Dn,_1Du));},1);return B(_x(_1Dk,_1Dt));},1);return B(_x(B(_H(0,_1Dm,_Z)),_1Ds));});return new T2(0,new T2(1,_1Dq,_1sK),_1Dr);},_1Dw=function(_1Dx){var _1Dy=E(_1Dx),_1Dz=E(_1Dy.a),_1DA=B(_1Dl(_1Dz.a,_1Dz.b,_1Dz.c,_1Dz.d,_1Dy.b));return new T2(0,_1DA.a,_1DA.b);},_1DB=function(_1DC){var _1DD=E(_1DC);return new T2(0,new T2(1,_1DD.b,_1sK),E(_1DD.a).b);},_1DE=new T(function(){return B(_ic("Grid.hs:(31,1)-(38,56)|function checkGrid"));}),_1DF=function(_1DG,_1DH){while(1){var _1DI=E(_1DH);if(!_1DI._){return false;}else{var _1DJ=_1DI.b,_1DK=E(_1DG),_1DL=_1DK.a,_1DM=_1DK.b,_1DN=E(_1DI.a);if(!_1DN._){return E(_1DE);}else{var _1DO=E(_1DN.a),_1DP=_1DO.a,_1DQ=_1DO.b,_1DR=E(_1DN.b);if(!_1DR._){var _1DS=E(_1DL),_1DT=E(_1DS);if(_1DT==32){switch(E(_1DM)){case 0:if(!E(_1DQ)){return true;}else{_1DG=new T2(0,_1DS,_II);_1DH=_1DJ;continue;}break;case 1:if(E(_1DQ)==1){return true;}else{_1DG=new T2(0,_1DS,_IO);_1DH=_1DJ;continue;}break;case 2:if(E(_1DQ)==2){return true;}else{_1DG=new T2(0,_1DS,_IU);_1DH=_1DJ;continue;}break;case 3:if(E(_1DQ)==3){return true;}else{_1DG=new T2(0,_1DS,_J0);_1DH=_1DJ;continue;}break;case 4:if(E(_1DQ)==4){return true;}else{_1DG=new T2(0,_1DS,_J6);_1DH=_1DJ;continue;}break;case 5:if(E(_1DQ)==5){return true;}else{_1DG=new T2(0,_1DS,_Jx);_1DH=_1DJ;continue;}break;case 6:if(E(_1DQ)==6){return true;}else{_1DG=new T2(0,_1DS,_Jq);_1DH=_1DJ;continue;}break;case 7:if(E(_1DQ)==7){return true;}else{_1DG=new T2(0,_1DS,_Jj);_1DH=_1DJ;continue;}break;default:if(E(_1DQ)==8){return true;}else{_1DG=new T2(0,_1DS,_Jc);_1DH=_1DJ;continue;}}}else{if(_1DT!=E(_1DP)){_1DG=_1DK;_1DH=_1DJ;continue;}else{switch(E(_1DM)){case 0:if(!E(_1DQ)){return true;}else{_1DG=new T2(0,_1DS,_II);_1DH=_1DJ;continue;}break;case 1:if(E(_1DQ)==1){return true;}else{_1DG=new T2(0,_1DS,_IO);_1DH=_1DJ;continue;}break;case 2:if(E(_1DQ)==2){return true;}else{_1DG=new T2(0,_1DS,_IU);_1DH=_1DJ;continue;}break;case 3:if(E(_1DQ)==3){return true;}else{_1DG=new T2(0,_1DS,_J0);_1DH=_1DJ;continue;}break;case 4:if(E(_1DQ)==4){return true;}else{_1DG=new T2(0,_1DS,_J6);_1DH=_1DJ;continue;}break;case 5:if(E(_1DQ)==5){return true;}else{_1DG=new T2(0,_1DS,_Jx);_1DH=_1DJ;continue;}break;case 6:if(E(_1DQ)==6){return true;}else{_1DG=new T2(0,_1DS,_Jq);_1DH=_1DJ;continue;}break;case 7:if(E(_1DQ)==7){return true;}else{_1DG=new T2(0,_1DS,_Jj);_1DH=_1DJ;continue;}break;default:if(E(_1DQ)==8){return true;}else{_1DG=new T2(0,_1DS,_Jc);_1DH=_1DJ;continue;}}}}}else{var _1DU=E(_1DL),_1DV=E(_1DU);if(_1DV==32){switch(E(_1DM)){case 0:if(!E(_1DQ)){return true;}else{_1DG=new T2(0,_1DU,_II);_1DH=new T2(1,_1DR,_1DJ);continue;}break;case 1:if(E(_1DQ)==1){return true;}else{_1DG=new T2(0,_1DU,_IO);_1DH=new T2(1,_1DR,_1DJ);continue;}break;case 2:if(E(_1DQ)==2){return true;}else{_1DG=new T2(0,_1DU,_IU);_1DH=new T2(1,_1DR,_1DJ);continue;}break;case 3:if(E(_1DQ)==3){return true;}else{_1DG=new T2(0,_1DU,_J0);_1DH=new T2(1,_1DR,_1DJ);continue;}break;case 4:if(E(_1DQ)==4){return true;}else{_1DG=new T2(0,_1DU,_J6);_1DH=new T2(1,_1DR,_1DJ);continue;}break;case 5:if(E(_1DQ)==5){return true;}else{_1DG=new T2(0,_1DU,_Jx);_1DH=new T2(1,_1DR,_1DJ);continue;}break;case 6:if(E(_1DQ)==6){return true;}else{_1DG=new T2(0,_1DU,_Jq);_1DH=new T2(1,_1DR,_1DJ);continue;}break;case 7:if(E(_1DQ)==7){return true;}else{_1DG=new T2(0,_1DU,_Jj);_1DH=new T2(1,_1DR,_1DJ);continue;}break;default:if(E(_1DQ)==8){return true;}else{_1DG=new T2(0,_1DU,_Jc);_1DH=new T2(1,_1DR,_1DJ);continue;}}}else{if(_1DV!=E(_1DP)){_1DG=_1DK;_1DH=new T2(1,_1DR,_1DJ);continue;}else{switch(E(_1DM)){case 0:if(!E(_1DQ)){return true;}else{_1DG=new T2(0,_1DU,_II);_1DH=new T2(1,_1DR,_1DJ);continue;}break;case 1:if(E(_1DQ)==1){return true;}else{_1DG=new T2(0,_1DU,_IO);_1DH=new T2(1,_1DR,_1DJ);continue;}break;case 2:if(E(_1DQ)==2){return true;}else{_1DG=new T2(0,_1DU,_IU);_1DH=new T2(1,_1DR,_1DJ);continue;}break;case 3:if(E(_1DQ)==3){return true;}else{_1DG=new T2(0,_1DU,_J0);_1DH=new T2(1,_1DR,_1DJ);continue;}break;case 4:if(E(_1DQ)==4){return true;}else{_1DG=new T2(0,_1DU,_J6);_1DH=new T2(1,_1DR,_1DJ);continue;}break;case 5:if(E(_1DQ)==5){return true;}else{_1DG=new T2(0,_1DU,_Jx);_1DH=new T2(1,_1DR,_1DJ);continue;}break;case 6:if(E(_1DQ)==6){return true;}else{_1DG=new T2(0,_1DU,_Jq);_1DH=new T2(1,_1DR,_1DJ);continue;}break;case 7:if(E(_1DQ)==7){return true;}else{_1DG=new T2(0,_1DU,_Jj);_1DH=new T2(1,_1DR,_1DJ);continue;}break;default:if(E(_1DQ)==8){return true;}else{_1DG=new T2(0,_1DU,_Jc);_1DH=new T2(1,_1DR,_1DJ);continue;}}}}}}}}},_1DW=new T(function(){return B(unCStr("\n"));}),_1DX=function(_1DY,_1DZ,_){var _1E0=jsWriteHandle(E(_1DY),toJSStr(E(_1DZ)));return _kJ;},_1E1=function(_1E2,_1E3,_){var _1E4=E(_1E2),_1E5=jsWriteHandle(_1E4,toJSStr(E(_1E3)));return new F(function(){return _1DX(_1E4,_1DW,_);});},_1E6=function(_1E7){var _1E8=E(_1E7);if(!_1E8._){return __Z;}else{return new F(function(){return _x(_1E8.a,new T(function(){return B(_1E6(_1E8.b));},1));});}},_1E9=new T(function(){return B(unCStr("removed"));}),_1Ea=new T(function(){return B(unCStr("loadError"));}),_1Eb=new T(function(){return B(unCStr("saved"));}),_1Ec=new T(function(){return B(err(_wY));}),_1Ed=new T(function(){return B(err(_x2));}),_1Ee=12,_1Ef=3,_1Eg=new T(function(){return B(unCStr("Coding : yokoP"));}),_1Eh=8,_1Ei=32,_1Ej=new T2(0,_1Ei,_Jx),_1Ek=99,_1El=64,_1Em=new T(function(){return B(_qy(_1o5,0));}),_1En=new T(function(){return B(unCStr("loadError"));}),_1Eo=new T(function(){return B(A3(_K8,_KB,_Id,_K0));}),_1Ep=new T(function(){return B(unCStr(","));}),_1Eq=new T(function(){return B(unCStr("~"));}),_1Er=new T(function(){return B(unCStr("savedata"));}),_1Es=new T(function(){return B(unCStr("---"));}),_1Et=new T(function(){return B(unCStr("=="));}),_1Eu=4,_1Ev=6,_1Ew=5,_1Ex=new T1(0,333),_1Ey=new T(function(){return B(_cx(1,2147483647));}),_1Ez=function(_1EA){var _1EB=B(_KK(B(_x7(_1Eo,_1EA))));return (_1EB._==0)?E(_1Ec):(E(_1EB.b)._==0)?E(_1EB.a):E(_1Ed);},_1EC=new T(function(){var _1ED=E(_1mo);if(!_1ED._){return E(_rm);}else{return E(_1ED.a);}}),_1EE=new T(function(){return B(unAppCStr("[]",_Z));}),_1EF=new T(function(){return B(unCStr("\""));}),_1EG=new T2(1,_Z,_Z),_1EH=new T(function(){return B(_aj(_1Ez,_1EG));}),_1EI=function(_1EJ,_1EK){return new T2(1,_aI,new T(function(){return B(_cp(_1EJ,new T2(1,_aI,_1EK)));}));},_1EL=function(_1EM,_1EN){var _1EO=E(_1EM),_1EP=new T(function(){var _1EQ=function(_1ER){var _1ES=E(_1EO.a),_1ET=new T(function(){return B(A3(_wK,_aC,new T2(1,function(_1EU){return new F(function(){return _1EI(_1ES.a,_1EU);});},new T2(1,function(_1EV){return new F(function(){return _1aH(0,_1ES.b,_1EV);});},_Z)),new T2(1,_F,_1ER)));});return new T2(1,_G,_1ET);};return B(A3(_wK,_aC,new T2(1,_1EQ,new T2(1,function(_1EW){return new F(function(){return _H(0,E(_1EO.b),_1EW);});},_Z)),new T2(1,_F,_1EN)));});return new T2(1,_G,_1EP);},_1EX=new T2(1,_aI,_Z),_1EY=new T(function(){return B(_1fX(_1lM,5,_1mS));}),_1EZ=new T(function(){return B(unCStr("Thank you!"));}),_1F0=17,_1F1=2,_1F2=new T(function(){return B(unCStr("First Up : 2024 12 24"));}),_1F3=function(_1F4,_1F5){var _1F6=E(_1F5);return (_1F6._==0)?__Z:new T2(1,_1F4,new T2(1,_1F6.a,new T(function(){return B(_1F3(_1F4,_1F6.b));})));},_1F7=new T(function(){return B(unCStr("noContent"));}),_1F8=new T(function(){return B(unCStr("noHint"));}),_1F9=new T(function(){return B(err(_x2));}),_1Fa=new T(function(){return B(err(_wY));}),_1Fb=new T(function(){return B(A3(_K8,_KB,_Id,_K0));}),_1Fc=function(_1Fd,_1Fe){var _1Ff=E(_1Fe);if(!_1Ff._){var _1Fg=B(_KK(B(_x7(_1Fb,_1Fd))));return (_1Fg._==0)?E(_1Fa):(E(_1Fg.b)._==0)?new T4(0,E(_1Fg.a),_Z,_Z,_Z):E(_1F9);}else{var _1Fh=_1Ff.a,_1Fi=E(_1Ff.b);if(!_1Fi._){var _1Fj=B(_KK(B(_x7(_1Fb,_1Fd))));return (_1Fj._==0)?E(_1Fa):(E(_1Fj.b)._==0)?new T4(0,E(_1Fj.a),E(_1Fh),E(_1F8),E(_1F7)):E(_1F9);}else{var _1Fk=_1Fi.a,_1Fl=E(_1Fi.b);if(!_1Fl._){var _1Fm=B(_KK(B(_x7(_1Fb,_1Fd))));return (_1Fm._==0)?E(_1Fa):(E(_1Fm.b)._==0)?new T4(0,E(_1Fm.a),E(_1Fh),E(_1Fk),E(_1F7)):E(_1F9);}else{if(!E(_1Fl.b)._){var _1Fn=B(_KK(B(_x7(_1Fb,_1Fd))));return (_1Fn._==0)?E(_1Fa):(E(_1Fn.b)._==0)?new T4(0,E(_1Fn.a),E(_1Fh),E(_1Fk),E(_1Fl.a)):E(_1F9);}else{return new T4(0,0,_Z,_Z,_Z);}}}}},_1Fo=function(_1Fp){var _1Fq=E(_1Fp);if(!_1Fq._){return new F(function(){return _1Fc(_Z,_Z);});}else{var _1Fr=_1Fq.a,_1Fs=E(_1Fq.b);if(!_1Fs._){return new F(function(){return _1Fc(new T2(1,_1Fr,_Z),_Z);});}else{var _1Ft=E(_1Fr),_1Fu=new T(function(){var _1Fv=B(_LC(44,_1Fs.a,_1Fs.b));return new T2(0,_1Fv.a,_1Fv.b);});if(E(_1Ft)==44){return new F(function(){return _1Fc(_Z,new T2(1,new T(function(){return E(E(_1Fu).a);}),new T(function(){return E(E(_1Fu).b);})));});}else{var _1Fw=E(_1Fu);return new F(function(){return _1Fc(new T2(1,_1Ft,_1Fw.a),_1Fw.b);});}}}},_1Fx=function(_1Fy){var _1Fz=B(_1Fo(_1Fy));return new T4(0,_1Fz.a,E(_1Fz.b),E(_1Fz.c),E(_1Fz.d));},_1FA=function(_1FB){return (E(_1FB)==10)?true:false;},_1FC=function(_1FD){var _1FE=E(_1FD);if(!_1FE._){return __Z;}else{var _1FF=new T(function(){var _1FG=B(_1gq(_1FA,_1FE));return new T2(0,_1FG.a,new T(function(){var _1FH=E(_1FG.b);if(!_1FH._){return __Z;}else{return B(_1FC(_1FH.b));}}));});return new T2(1,new T(function(){return E(E(_1FF).a);}),new T(function(){return E(E(_1FF).b);}));}},_1FI=new T(function(){return B(unCStr("57,\u5974\uff1a\u306a\uff1a\u570b\uff1a\u3053\u304f\uff1a\u738b\uff1a\u304a\u3046\uff1a\u304c\u5f8c\uff1a\u3053\u3046\uff1a\u6f22\uff1a\u304b\u3093\uff1a\u304b\u3089\u91d1\uff1a\u304d\u3093\uff1a\u5370\uff1a\u3044\u3093\uff1a,<\u5f8c\uff1a\u3054\uff1a\u6f22\uff1a\u304b\u3093\uff1a\u66f8\uff1a\u3057\u3087\uff1a>\u306b\u8a18\uff1a\u304d\uff1a\u8f09\uff1a\u3055\u3044\uff1a\u304c\u3042\u308a \u6c5f\uff1a\u3048\uff1a\u6238\uff1a\u3069\uff1a\u671f\uff1a\u304d\uff1a\u306b\u305d\u308c\u3089\u3057\u304d\u91d1\u5370\u304c\u767a\u898b\u3055\u308c\u308b,\u798f\uff1a\u3075\u304f\uff1a\u5ca1\uff1a\u304a\u304b\uff1a\u770c\uff1a\u3051\u3093\uff1a\u5fd7\uff1a\u3057\uff1a\u8cc0\uff1a\u304b\u306e\uff1a\u5cf6\uff1a\u3057\u307e\uff1a\u306b\u3066<\u6f22\uff1a\u304b\u3093\u306e\uff1a\u59d4\uff1a\u308f\u306e\uff1a\u5974\uff1a\u306a\u306e\uff1a\u570b\uff1a\u3053\u304f\uff1a\u738b\uff1a\u304a\u3046\uff1a>\u3068\u523b\uff1a\u304d\u3056\uff1a\u307e\u308c\u305f\u91d1\u5370\u304c\u6c5f\u6238\u6642\u4ee3\u306b\u767c\uff1a\u306f\u3063\uff1a\u898b\uff1a\u3051\u3093\uff1a\u3055\u308c\u308b >>\u5927\uff1a\u3084\uff1a\u548c\uff1a\u307e\u3068\uff1a\u671d\uff1a\u3061\u3087\u3046\uff1a\u5ef7\uff1a\u3066\u3044\uff1a\u3068\u306e\u95dc\uff1a\u304b\u3093\uff1a\u4fc2\uff1a\u3051\u3044\uff1a\u4e0d\uff1a\u3075\uff1a\u660e\uff1a\u3081\u3044\uff1a\u306f\n239,<\u5351\uff1a\u3072\uff1a\u5f25\uff1a\u307f\uff1a\u547c\uff1a\u3053\uff1a>\u304c\u9b4f\uff1a\u304e\uff1a\u306b\u9063\uff1a\u3051\u3093\uff1a\u4f7f\uff1a\u3057\uff1a,\u652f\uff1a\u3057\uff1a\u90a3\uff1a\u306a\uff1a\u306e\u6b74\uff1a\u308c\u304d\uff1a\u53f2\uff1a\u3057\uff1a\u66f8\uff1a\u3057\u3087\uff1a<\u9b4f\uff1a\u304e\uff1a\u5fd7\uff1a\u3057\uff1a>\u306b\u8a18\uff1a\u304d\uff1a\u8f09\uff1a\u3055\u3044\uff1a\u3055\u308c\u3066\u3090\u308b\u5deb\uff1a\u307f\uff1a\u5973\uff1a\u3053\uff1a,<\u9b4f\uff1a\u304e\uff1a\u5fd7\uff1a\u3057\uff1a>\u502d\uff1a\u308f\uff1a\u4eba\uff1a\u3058\u3093\uff1a\u4f1d\uff1a\u3067\u3093\uff1a\u306b\u8a18\uff1a\u3057\u308b\uff1a\u3055\u308c\u3066\u3090\u308b<\u90aa\u99ac\u58f9\u570b(\u3084\u307e\u3044\u3061\u3053\u304f)>\u3082<\u5351\u5f25\u547c>\u3082\u65e5\u672c\u306b\u6b98\uff1a\u306e\u3053\uff1a\u308b\u8cc7\uff1a\u3057\uff1a\u6599\uff1a\u308c\u3044\uff1a\u3067\u306f\u4e00\uff1a\u3044\u3063\uff1a\u5207\uff1a\u3055\u3044\uff1a\u78ba\uff1a\u304b\u304f\uff1a\u8a8d\uff1a\u306b\u3093\uff1a\u3067\u304d\u306a\u3044\n316,\u4ec1\uff1a\u306b\u3093\uff1a\u5fb3\uff1a\u3068\u304f\uff1a\u5929\u7687 \u7a0e\uff1a\u305c\u3044\uff1a\u3092\u514d\uff1a\u3081\u3093\uff1a\u9664\uff1a\u3058\u3087\uff1a,<\u53e4\uff1a\u3053\uff1a\u4e8b\uff1a\u3058\uff1a\u8a18\uff1a\u304d\uff1a><\u65e5\uff1a\u306b\uff1a\u672c\uff1a\u307b\u3093\uff1a\u66f8\uff1a\u3057\u3087\uff1a\u7d00\uff1a\u304d\uff1a>\u306b\u8a18\uff1a\u304d\uff1a\u8f09\uff1a\u3055\u3044\uff1a\u304c\u3042\u308b,16\u4ee3\u4ec1\uff1a\u306b\u3093\uff1a\u5fb3\uff1a\u3068\u304f\uff1a\u5929\u7687\u304c<\u6c11\uff1a\u305f\u307f\uff1a\u306e\u304b\u307e\u3069\u3088\u308a\u7159\uff1a\u3051\u3080\u308a\uff1a\u304c\u305f\u3061\u306e\u307c\u3089\u306a\u3044\u306e\u306f \u8ca7\uff1a\u307e\u3065\uff1a\u3057\u304f\u3066\u708a\uff1a\u305f\uff1a\u304f\u3082\u306e\u304c\u306a\u3044\u304b\u3089\u3067\u306f\u306a\u3044\u304b>\u3068\u3057\u3066 \u5bae\uff1a\u304d\u3085\u3046\uff1a\u4e2d\uff1a\u3061\u3085\u3046\uff1a\u306e\u4fee\uff1a\u3057\u3085\u3046\uff1a\u7e55\uff1a\u305c\u3093\uff1a\u3092\u5f8c\uff1a\u3042\u3068\uff1a\u307e\u306f\u3057\u306b\u3057 \u6c11\u306e\u751f\u6d3b\u3092\u8c4a\uff1a\u3086\u305f\uff1a\u304b\u306b\u3059\u308b\u8a71\u304c<\u65e5\u672c\u66f8\u7d00>\u306b\u3042\u308b\n478,<\u502d\uff1a\u308f\uff1a>\u306e\u6b66\uff1a\u3076\uff1a\u738b\uff1a\u304a\u3046\uff1a \u5357\uff1a\u306a\u3093\uff1a\u671d\uff1a\u3061\u3087\u3046\uff1a\u306e\u5b8b\uff1a\u305d\u3046\uff1a\u3078\u9063\uff1a\u3051\u3093\uff1a\u4f7f\uff1a\u3057\uff1a,\u96c4\uff1a\u3086\u3046\uff1a\u7565\uff1a\u308a\u3083\u304f\uff1a\u5929\u7687\u3092\u6307\u3059\u3068\u3044\u3075\u306e\u304c\u5b9a\uff1a\u3066\u3044\uff1a\u8aac\uff1a\u305b\u3064\uff1a,<\u5b8b\uff1a\u305d\u3046\uff1a\u66f8\uff1a\u3057\u3087\uff1a>\u502d\uff1a\u308f\uff1a\u570b\uff1a\u3053\u304f\uff1a\u50b3\uff1a\u3067\u3093\uff1a\u306b\u8a18\uff1a\u304d\uff1a\u8f09\uff1a\u3055\u3044\uff1a\u304c\u3042\u308b >> \u96c4\u7565\u5929\u7687\u306f\u7b2c21\u4ee3\u5929\u7687\n538,\u4ecf\uff1a\u3076\u3063\uff1a\u6559\uff1a\u304d\u3087\u3046\uff1a\u516c\uff1a\u3053\u3046\uff1a\u4f1d\uff1a\u3067\u3093\uff1a,\u6b3d\uff1a\u304d\u3093\uff1a\u660e\uff1a\u3081\u3044\uff1a\u5929\u7687\u5fa1\uff1a\u307f\uff1a\u4ee3\uff1a\u3088\uff1a\u306b\u767e\uff1a\u304f\uff1a\u6e08\uff1a\u3060\u3089\uff1a\u306e\u8056\uff1a\u305b\u3044\uff1a\u660e\uff1a\u3081\u3044\uff1a\u738b\uff1a\u304a\u3046\uff1a\u304b\u3089\u50b3\uff1a\u3067\u3093\uff1a\u4f86\uff1a\u3089\u3044\uff1a\u3057\u305f\u3068\u306e\u6587\uff1a\u3076\u3093\uff1a\u732e\uff1a\u3051\u3093\uff1a\u3042\u308a,\u6b63\u78ba\u306a\u5e74\u4ee3\u306b\u3064\u3044\u3066\u306f\u8af8\uff1a\u3057\u3087\uff1a\u8aac\uff1a\u305b\u3064\uff1a\u3042\u308b\n604,\u5341\uff1a\u3058\u3085\u3046\uff1a\u4e03\uff1a\u3057\u3061\uff1a\u6761\uff1a\u3058\u3087\u3046\uff1a\u61b2\uff1a\u3051\u3093\uff1a\u6cd5\uff1a\u307d\u3046\uff1a\u5236\uff1a\u305b\u3044\uff1a\u5b9a\uff1a\u3066\u3044\uff1a,\u8056\uff1a\u3057\u3087\u3046\uff1a\u5fb3\uff1a\u3068\u304f\uff1a\u592a\uff1a\u305f\u3044\uff1a\u5b50\uff1a\u3057\uff1a\u304c\u5236\uff1a\u305b\u3044\uff1a\u5b9a\uff1a\u3066\u3044\uff1a\u3057\u305f\u3068\u3055\u308c\u308b,<\u548c\uff1a\u308f\uff1a\u3092\u4ee5\uff1a\u3082\u3063\uff1a\u3066\u8cb4\uff1a\u305f\u3075\u3068\uff1a\u3057\u3068\u70ba\uff1a\u306a\uff1a\u3057 \u5fe4(\u3055\u304b)\u3075\u308b\u3053\u3068\u7121\uff1a\u306a\uff1a\u304d\u3092\u5b97\uff1a\u3080\u306d\uff1a\u3068\u305b\u3088>\n607,\u6cd5\uff1a\u307b\u3046\uff1a\u9686\uff1a\u308a\u3085\u3046\uff1a\u5bfa\uff1a\u3058\uff1a\u304c\u5275\uff1a\u305d\u3046\uff1a\u5efa\uff1a\u3051\u3093\uff1a\u3055\u308c\u308b,\u8056\uff1a\u3057\u3087\u3046\uff1a\u5fb3\uff1a\u3068\u304f\uff1a\u592a\uff1a\u305f\u3044\uff1a\u5b50\uff1a\u3057\uff1a\u3086\u304b\u308a\u306e\u5bfa\uff1a\u3058\uff1a\u9662\uff1a\u3044\u3093\uff1a,\u897f\uff1a\u3055\u3044\uff1a\u9662\uff1a\u3044\u3093\uff1a\u4f3d\uff1a\u304c\uff1a\u85cd\uff1a\u3089\u3093\uff1a\u306f\u73fe\uff1a\u3052\u3093\uff1a\u5b58\uff1a\u305e\u3093\uff1a\u3059\u308b\u4e16\u754c\u6700\uff1a\u3055\u3044\uff1a\u53e4\uff1a\u3053\uff1a\u306e\u6728\uff1a\u3082\u304f\uff1a\u9020\uff1a\u305e\u3046\uff1a\u5efa\uff1a\u3051\u3093\uff1a\u7bc9\uff1a\u3061\u304f\uff1a\u7269\uff1a\u3076\u3064\uff1a\u3068\u3055\u308c\u3066\u3090\u308b\n645,\u4e59\uff1a\u3044\u3063\uff1a\u5df3\uff1a\u3057\uff1a\u306e\u8b8a\uff1a\u3078\u3093\uff1a,\u3053\u306e\u5f8c\u3059\u3050\u5927\uff1a\u305f\u3044\uff1a\u5316\uff1a\u304b\uff1a\u306e\u6539\uff1a\u304b\u3044\uff1a\u65b0\uff1a\u3057\u3093\uff1a\u306a\u308b,\u4e2d\uff1a\u306a\u304b\u306e\uff1a\u5927\uff1a\u304a\u304a\uff1a\u5144\uff1a\u3048\u306e\uff1a\u7687\uff1a\u304a\u3046\uff1a\u5b50\uff1a\u3058\uff1a(\u5f8c\u306e38\u4ee3\u5929\uff1a\u3066\u3093\uff1a\u667a\uff1a\u3062\uff1a\u5929\u7687)\u304c\u8607\uff1a\u305d\uff1a\u6211\uff1a\u304c\uff1a\u6c0f\uff1a\u3057\uff1a\u3092\u4ea1\uff1a\u307b\u308d\uff1a\u307c\u3059\n663,\u767d\uff1a\u306f\u304f\uff1a\u6751\uff1a\u3059\u304d\u306e\uff1a\u6c5f\uff1a\u3048\uff1a\u306e\u6230\uff1a\u305f\u305f\u304b\u3072\uff1a,\u5510\uff1a\u3068\u3046\uff1a\u3068\u65b0\uff1a\u3057\u3089\uff1a\u7f85\uff1a\u304e\uff1a\u306b\u6ec5\uff1a\u307b\u308d\uff1a\u307c\u3055\u308c\u305f\u767e\uff1a\u304f\u3060\uff1a\u6e08\uff1a\u3089\uff1a\u3092\u518d\uff1a\u3055\u3044\uff1a\u8208\uff1a\u3053\u3046\uff1a\u3059\u308b\u76ee\uff1a\u3082\u304f\uff1a\u7684\uff1a\u3066\u304d\uff1a,\u5510\uff1a\u3068\u3046\uff1a\u30fb\u65b0\uff1a\u3057\u3089\uff1a\u7f85\uff1a\u304e\uff1a\u9023\uff1a\u308c\u3093\uff1a\u5408\uff1a\u3054\u3046\uff1a\u8ecd\uff1a\u3050\u3093\uff1a\u306b\u6557\uff1a\u3084\u3076\uff1a\u308c\u308b\n672,\u58ec\uff1a\u3058\u3093\uff1a\u7533\uff1a\u3057\u3093\uff1a\u306e\u4e82\uff1a\u3089\u3093\uff1a,\u5929\uff1a\u3066\u3093\uff1a\u667a\uff1a\u3062\uff1a\u5929\u7687\u304a\u304b\u304f\u308c\u5f8c\u306e\u5f8c\uff1a\u3053\u3046\uff1a\u7d99\uff1a\u3051\u3044\uff1a\u8005\uff1a\u3057\u3083\uff1a\u4e89\uff1a\u3042\u3089\u305d\uff1a\u3072,\u5f8c\uff1a\u3053\u3046\uff1a\u7d99\uff1a\u3051\u3044\uff1a\u8005\uff1a\u3057\u3083\uff1a\u3067\u3042\u3063\u305f\u5927\uff1a\u304a\u304a\uff1a\u53cb\uff1a\u3068\u3082\u306e\uff1a\u7687\uff1a\u304a\u3046\uff1a\u5b50\uff1a\u3058\uff1a\u306b\u53d4\uff1a\u304a\uff1a\u7236\uff1a\u3058\uff1a\u306e\u5927\uff1a\u304a\u304a\uff1a\u6d77\uff1a\u3042\uff1a\u4eba\uff1a\u307e\u306e\uff1a\u7687\uff1a\u304a\u3046\uff1a\u5b50\uff1a\u3058\uff1a\u304c\u53cd\uff1a\u306f\u3093\uff1a\u65d7\uff1a\u304d\uff1a\u3092\u7ffb\uff1a\u3072\u308b\u304c\u3078\uff1a\u3057 \u5927\uff1a\u304a\u304a\uff1a\u53cb\uff1a\u3068\u3082\u306e\uff1a\u7687\uff1a\u304a\u3046\uff1a\u5b50\uff1a\u3058\uff1a\u3092\u5012\uff1a\u305f\u304a\uff1a\u3057\u3066\u5929\uff1a\u3066\u3093\uff1a\u6b66\uff1a\u3080\uff1a\u5929\u7687\u3068\u306a\u308b\n710,\u5e73\uff1a\u3078\u3044\uff1a\u57ce\uff1a\u3058\u3087\u3046\uff1a\u4eac\uff1a\u304d\u3087\u3046\uff1a\u9077\uff1a\u305b\u3093\uff1a\u90fd\uff1a\u3068\uff1a,\u5e73\u57ce\u3068\u3044\u3075\u6f22\u5b57\u306f<\u306a\u3089>\u3068\u3082\u8b80\uff1a\u3088\uff1a\u3080,\u548c\uff1a\u308f\uff1a\u9285\uff1a\u3069\u3046\uff1a3\u5e74 \u7b2c43\u4ee3\u5143\uff1a\u3052\u3093\uff1a\u660e\uff1a\u3081\u3044\uff1a\u5929\u7687\u306b\u3088\u308b \u5148\uff1a\u305b\u3093\uff1a\u4ee3\uff1a\u3060\u3044\uff1a\u306e\u6587\uff1a\u3082\u3093\uff1a\u6b66\uff1a\u3080\uff1a\u5929\u7687\u304c\u75ab\uff1a\u3048\u304d\uff1a\u75c5\uff1a\u3073\u3087\u3046\uff1a\u3067\u5d29\uff1a\u307b\u3046\uff1a\u5fa1\uff1a\u304e\u3087\uff1a\u3055\u308c\u305f\u3053\u3068\u304c \u9077\u90fd\u306e\u539f\uff1a\u3052\u3093\uff1a\u56e0\uff1a\u3044\u3093\uff1a\u306e\u3072\u3068\u3064\u3067\u3082\u3042\u3063\u305f\u3068\u3055\u308c\u308b\n794,\u5e73\uff1a\u3078\u3044\uff1a\u5b89\uff1a\u3042\u3093\uff1a\u4eac\uff1a\u304d\u3087\u3046\uff1a\u9077\uff1a\u305b\u3093\uff1a\u90fd\uff1a\u3068\uff1a,\u5ef6\uff1a\u3048\u3093\uff1a\u66a6\uff1a\u308a\u3083\u304f\uff1a13\u5e74 \u7b2c50\u4ee3\u6853\uff1a\u304b\u3093\uff1a\u6b66\uff1a\u3080\uff1a\u5929\u7687 \u9577\uff1a\u306a\u304c\uff1a\u5ca1\uff1a\u304a\u304b\uff1a\u4eac\uff1a\u304d\u3087\u3046\uff1a\u304b\u3089\u9077\u90fd\u3055\u308c\u308b,\u3053\u306e\u5f8c\u5e73\uff1a\u305f\u3044\u3089\uff1a\u6e05\uff1a\u306e\u304d\u3088\uff1a\u76db\uff1a\u3082\u308a\uff1a\u306b\u3088\u308b\u798f\uff1a\u3075\u304f\uff1a\u539f\uff1a\u306f\u3089\uff1a\u4eac\uff1a\u304d\u3087\u3046\uff1a\u9077\u90fd\u3084\u5357\uff1a\u306a\u3093\uff1a\u5317\uff1a\u307c\u304f\uff1a\u671d\uff1a\u3061\u3087\u3046\uff1a\u6642\u4ee3\u306e\u5409\uff1a\u3088\u3057\uff1a\u91ce\uff1a\u306e\uff1a\u306a\u3069\u306e\u4f8b\uff1a\u308c\u3044\uff1a\u5916\uff1a\u304c\u3044\uff1a\u306f\u3042\u308b\u3082\u306e\u306e \u660e\uff1a\u3081\u3044\uff1a\u6cbb\uff1a\u3058\uff1a\u7dad\uff1a\u3044\uff1a\u65b0\uff1a\u3057\u3093\uff1a\u307e\u3067\u5343\u5e74\u4ee5\u4e0a\u7e8c\uff1a\u3064\u3065\uff1a\u304f\n806,\u6700\uff1a\u3055\u3044\uff1a\u6f84\uff1a\u3061\u3087\u3046\uff1a\u304c\u5929\uff1a\u3066\u3093\uff1a\u53f0\uff1a\u3060\u3044\uff1a\u5b97\uff1a\u3057\u3085\u3046\uff1a \u7a7a\uff1a\u304f\u3046\uff1a\u6d77\uff1a\u304b\u3044\uff1a\u304c\u771f\uff1a\u3057\u3093\uff1a\u8a00\uff1a\u3054\u3093\uff1a\u5b97\uff1a\u3057\u3085\u3046\uff1a,\u5e73\uff1a\u3078\u3044\uff1a\u5b89\uff1a\u3042\u3093\uff1a\u6642\uff1a\u3058\uff1a\u4ee3\uff1a\u3060\u3044\uff1a\u521d\uff1a\u3057\u3087\uff1a\u671f\uff1a\u304d\uff1a \u3069\u3061\u3089\u3082\u5510\uff1a\u3068\u3046\uff1a\u3067\u4fee\uff1a\u3057\u3085\uff1a\u884c\uff1a\u304e\u3087\u3046\uff1a\u3057\u5e30\uff1a\u304d\uff1a\u570b\uff1a\u3053\u304f\uff1a\u5f8c\uff1a\u3054\uff1a \u4ecf\uff1a\u3076\u3064\uff1a\u6559\uff1a\u304d\u3087\u3046\uff1a\u3092\u50b3\uff1a\u3064\u305f\uff1a\u3078\u308b,\u6700\uff1a\u3055\u3044\uff1a\u6f84\uff1a\u3061\u3087\u3046\uff1a\u306f\u5929\uff1a\u3066\u3093\uff1a\u53f0\uff1a\u3060\u3044\uff1a\u5b97\uff1a\u3057\u3085\u3046\uff1a\u3092\u958b\uff1a\u3072\u3089\uff1a\u304d \u6bd4\uff1a\u3072\uff1a\u53e1\uff1a\u3048\u3044\uff1a\u5c71\uff1a\u3056\u3093\uff1a\u306b\u5ef6\uff1a\u3048\u3093\uff1a\u66a6\uff1a\u308a\u3083\u304f\uff1a\u5bfa\uff1a\u3058\uff1a\u3092 \u7a7a\uff1a\u304f\u3046\uff1a\u6d77\uff1a\u304b\u3044\uff1a\u306f\u771f\uff1a\u3057\u3093\uff1a\u8a00\uff1a\u3054\u3093\uff1a\u5b97\uff1a\u3057\u3085\u3046\uff1a\u3092\u958b\u304d \u9ad8\uff1a\u3053\u3046\uff1a\u91ce\uff1a\u3084\uff1a\u5c71\uff1a\u3055\u3093\uff1a\u306b\u91d1\uff1a\u3053\u3093\uff1a\u525b\uff1a\u3054\u3046\uff1a\u5cf0\uff1a\u3076\uff1a\u5bfa\uff1a\u3058\uff1a\u3092\u5efa\uff1a\u3053\u3093\uff1a\u7acb\uff1a\u308a\u3085\u3046\uff1a\n857,\u85e4\uff1a\u3075\u3058\uff1a\u539f\uff1a\u308f\u3089\u306e\uff1a\u826f\uff1a\u3088\u3057\uff1a\u623f\uff1a\u3075\u3055\uff1a\u304c\u592a\uff1a\u3060\uff1a\u653f\uff1a\u3058\u3087\u3046\uff1a\u5927\uff1a\u3060\u3044\uff1a\u81e3\uff1a\u3058\u3093\uff1a\u306b,56\u4ee3\u6e05\uff1a\u305b\u3044\uff1a\u548c\uff1a\u308f\uff1a\u5929\u7687\u306e\u6442\uff1a\u305b\u3063\uff1a\u653f\uff1a\u3057\u3087\u3046\uff1a,\u81e3\uff1a\u3057\u3093\uff1a\u4e0b\uff1a\u304b\uff1a\u306e\u8eab\uff1a\u307f\uff1a\u5206\uff1a\u3076\u3093\uff1a\u3067\u521d\u3081\u3066\u6442\uff1a\u305b\u3063\uff1a\u653f\uff1a\u3057\u3087\u3046\uff1a\u306b\u306a\u3063\u305f\n894,\u9063\uff1a\u3051\u3093\uff1a\u5510\uff1a\u3068\u3046\uff1a\u4f7f\uff1a\u3057\uff1a\u304c\u5ec3\uff1a\u306f\u3044\uff1a\u6b62\uff1a\u3057\uff1a\u3055\u308c\u308b,\u83c5\uff1a\u3059\u304c\uff1a\u539f\uff1a\u308f\u3089\u306e\uff1a\u9053\uff1a\u307f\u3061\uff1a\u771f\uff1a\u3056\u306d\uff1a\u306e\u5efa\uff1a\u3051\u3093\uff1a\u8b70\uff1a\u304e\uff1a\u306b\u3088\u308b,\u3053\u306e\u5f8c904\u5e74\u306b\u5510\uff1a\u3068\u3046\uff1a\u306f\u6ec5\uff1a\u307b\u308d\uff1a\u3073\u5c0f\uff1a\u3057\u3087\u3046\uff1a\u570b\uff1a\u3053\u304f\uff1a\u304c\u5206\uff1a\u3076\u3093\uff1a\u7acb\uff1a\u308a\u3064\uff1a\u3057\u305f\u5f8c \u5b8b\uff1a\u305d\u3046\uff1a(\u5317\uff1a\u307b\u304f\uff1a\u5b8b\uff1a\u305d\u3046\uff1a)\u304c\u652f\uff1a\u3057\uff1a\u90a3\uff1a\u306a\uff1a\u5927\uff1a\u305f\u3044\uff1a\u9678\uff1a\u308a\u304f\uff1a\u3092\u7d71\uff1a\u3068\u3046\uff1a\u4e00\uff1a\u3044\u3064\uff1a\u3059\u308b\n935,\u627f\uff1a\u3057\u3087\u3046\uff1a\u5e73\uff1a\u3078\u3044\uff1a\u5929\uff1a\u3066\u3093\uff1a\u6176\uff1a\u304e\u3087\u3046\uff1a\u306e\u4e82\uff1a\u3089\u3093\uff1a,\u5e73\uff1a\u305f\u3044\u3089\uff1a\u5c06\uff1a\u306e\u307e\u3055\uff1a\u9580\uff1a\u304b\u3069\uff1a\u3084\u85e4\uff1a\u3075\u3058\uff1a\u539f\uff1a\u308f\u3089\u306e\uff1a\u7d14\uff1a\u3059\u307f\uff1a\u53cb\uff1a\u3068\u3082\uff1a\u3068\u3044\u3064\u305f\u6b66\uff1a\u3076\uff1a\u58eb\uff1a\u3057\uff1a\u306e\u53cd\uff1a\u306f\u3093\uff1a\u4e82\uff1a\u3089\u3093\uff1a,\u6442\uff1a\u305b\u3063\uff1a\u95a2\uff1a\u304b\u3093\uff1a\u653f\uff1a\u305b\u3044\uff1a\u6cbb\uff1a\u3058\uff1a\u3078\u306e\u4e0d\uff1a\u3075\uff1a\u6e80\uff1a\u307e\u3093\uff1a\u304c\u6839\uff1a\u3053\u3093\uff1a\u5e95\uff1a\u3066\u3044\uff1a\u306b\u3042\u3063\u305f\u3068\u3055\u308c\u308b\n1016,\u85e4\uff1a\u3075\u3058\uff1a\u539f\uff1a\u308f\u3089\u306e\uff1a\u9053\uff1a\u307f\u3061\uff1a\u9577\uff1a\u306a\u304c\uff1a\u304c\u6442\uff1a\u305b\u3063\uff1a\u653f\uff1a\u3057\u3087\u3046\uff1a\u306b,\u85e4\uff1a\u3075\u3058\uff1a\u539f\uff1a\u308f\u3089\uff1a\u6c0f\uff1a\u3057\uff1a\u5168\uff1a\u305c\u3093\uff1a\u76db\uff1a\u305b\u3044\uff1a\u6642\u4ee3\u3068\u3044\u306f\u308c\u308b,\u9053\uff1a\u307f\u3061\uff1a\u9577\uff1a\u306a\u304c\uff1a\u306f\u9577\uff1a\u3061\u3087\u3046\uff1a\u5973\uff1a\u3058\u3087\uff1a\u3092\u4e00\uff1a\u3044\u3061\uff1a\u6761\uff1a\u3058\u3087\u3046\uff1a\u5929\u7687(66\u4ee3)\u306e\u540e\uff1a\u304d\u3055\u304d\uff1a\u306b \u6b21\uff1a\u3058\uff1a\u5973\uff1a\u3058\u3087\uff1a\u3092\u4e09\uff1a\u3055\u3093\uff1a\u6761\uff1a\u3058\u3087\u3046\uff1a\u5929\u7687(67\u4ee3)\u306e\u540e\u306b \u4e09\uff1a\u3055\u3093\uff1a\u5973\uff1a\u3058\u3087\uff1a\u3092\u5f8c\uff1a\u3054\uff1a\u4e00\uff1a\u3044\u3061\uff1a\u6761\uff1a\u3058\u3087\u3046\uff1a\u5929\u7687(68\u4ee3)\u306e\u540e\u306b\u3059\u308b\n1086,\u9662\uff1a\u3044\u3093\uff1a\u653f\uff1a\u305b\u3044\uff1a\u958b\uff1a\u304b\u3044\uff1a\u59cb\uff1a\u3057\uff1a,\u6442\uff1a\u305b\u3063\uff1a\u653f\uff1a\u3057\u3087\u3046\uff1a\u3084\u95a2\uff1a\u304b\u3093\uff1a\u767d\uff1a\u3071\u304f\uff1a\u306e\u529b\uff1a\u3061\u304b\u3089\uff1a\u3092\u6291\uff1a\u304a\u3055\uff1a\u3078\u308b,72\u4ee3\u767d\uff1a\u3057\u3089\uff1a\u6cb3\uff1a\u304b\u306f\uff1a\u5929\u7687\u304c\u8b72\uff1a\u3058\u3087\u3046\uff1a\u4f4d\uff1a\u3044\uff1a\u5f8c \u4e0a\uff1a\u3058\u3087\u3046\uff1a\u7687\uff1a\u3053\u3046\uff1a\u3068\u306a\u308a \u653f\uff1a\u305b\u3044\uff1a\u6cbb\uff1a\u3062\uff1a\u306e\u5b9f\uff1a\u3058\u3063\uff1a\u6a29\uff1a\u3051\u3093\uff1a\u3092\u63e1\uff1a\u306b\u304e\uff1a\u308b\n1167,\u5e73\uff1a\u305f\u3044\u3089\uff1a\u6e05\uff1a\u306e\u304d\u3088\uff1a\u76db\uff1a\u3082\u308a\uff1a\u304c\u592a\uff1a\u3060\uff1a\u653f\uff1a\u3058\u3087\u3046\uff1a\u5927\uff1a\u3060\u3044\uff1a\u81e3\uff1a\u3058\u3093\uff1a\u306b,\u5a18\uff1a\u3080\u3059\u3081\uff1a\u3092\u5929\u7687\u306e\u540e\uff1a\u304d\u3055\u304d\uff1a\u306b\u3057 81\u4ee3\u5b89\uff1a\u3042\u3093\uff1a\u5fb3\uff1a\u3068\u304f\uff1a\u5929\u7687\u304c\u8a95\uff1a\u305f\u3093\uff1a\u751f\uff1a\u3058\u3087\u3046\uff1a,\u6b66\uff1a\u3076\uff1a\u58eb\uff1a\u3057\uff1a\u3068\u3057\u3066\u521d\uff1a\u306f\u3058\uff1a\u3081\u3066\u592a\uff1a\u3060\uff1a\u653f\uff1a\u3058\u3087\u3046\uff1a\u5927\uff1a\u3060\u3044\uff1a\u81e3\uff1a\u3058\u3093\uff1a\u306b\u4efb\uff1a\u306b\u3093\uff1a\u547d\uff1a\u3081\u3044\uff1a\u3055\u308c\u308b\n1185,\u5e73\uff1a\u3078\u3044\uff1a\u5bb6\uff1a\u3051\uff1a\u6ec5\uff1a\u3081\u3064\uff1a\u4ea1\uff1a\u307c\u3046\uff1a,\u58c7\uff1a\u3060\u3093\uff1a\u30ce\uff1a\u306e\uff1a\u6d66\uff1a\u3046\u3089\uff1a\u306e\u6230\uff1a\u305f\u305f\u304b\uff1a\u3072,\u6e90\uff1a\u307f\u306a\u3082\uff1a\u983c\uff1a\u3068\u306e\u3088\uff1a\u671d\uff1a\u308a\u3068\u3082\uff1a\u306e\u547d\uff1a\u3081\u3044\uff1a\u3092\u53d7\uff1a\u3046\uff1a\u3051\u305f \u5f1f\uff1a\u304a\u3068\u3046\u3068\uff1a\u306e\u7fa9\uff1a\u3088\u3057\uff1a\u7d4c\uff1a\u3064\u306d\uff1a\u3089\u306e\u6d3b\uff1a\u304b\u3064\uff1a\u8e8d\uff1a\u3084\u304f\uff1a\u304c\u3042\u3063\u305f \u3053\u306e\u3068\u304d\u5b89\uff1a\u3042\u3093\uff1a\u5fb3\uff1a\u3068\u304f\uff1a\u5929\u7687\u306f\u6578\uff1a\u304b\u305e\uff1a\u3078\u5e74\u4e03\u6b73\uff1a\u3055\u3044\uff1a\u3067\u5165\uff1a\u306b\u3085\u3046\uff1a\u6c34\uff1a\u3059\u3044\uff1a\u3057\u5d29\uff1a\u307b\u3046\uff1a\u5fa1\uff1a\u304e\u3087\uff1a\u3055\u308c\u308b\n1192,\u6e90\uff1a\u307f\u306a\u3082\uff1a\u983c\uff1a\u3068\u306e\u3088\uff1a\u671d\uff1a\u308a\u3068\u3082\uff1a\u304c\u5f81\uff1a\u305b\u3044\uff1a\u5937\uff1a\u3044\uff1a\u5927\uff1a\u305f\u3044\uff1a\u5c06\uff1a\u3057\u3087\u3046\uff1a\u8ecd\uff1a\u3050\u3093\uff1a\u306b,\u6b66\uff1a\u3076\uff1a\u5bb6\uff1a\u3051\uff1a\u653f\uff1a\u305b\u3044\uff1a\u6a29\uff1a\u3051\u3093\uff1a\u304c\u672c\uff1a\u307b\u3093\uff1a\u683c\uff1a\u304b\u304f\uff1a\u7684\uff1a\u3066\u304d\uff1a\u306b\u59cb\uff1a\u306f\u3058\uff1a\u307e\u308b\u938c\uff1a\u304b\u307e\uff1a\u5009\uff1a\u304f\u3089\uff1a\u5e55\uff1a\u3070\u304f\uff1a\u5e9c\uff1a\u3075\uff1a\u6210\uff1a\u305b\u3044\uff1a\u7acb\uff1a\u308a\u3064\uff1a\n1221,\u627f\uff1a\u3058\u3087\u3046\uff1a\u4e45\uff1a\u304d\u3085\u3046\uff1a\u306e\u8b8a\uff1a\u3078\u3093\uff1a,\u5168\uff1a\u305c\u3093\uff1a\u570b\uff1a\u3053\u304f\uff1a\u306e\u6b66\uff1a\u3076\uff1a\u58eb\uff1a\u3057\uff1a\u306b \u57f7\uff1a\u3057\u3063\uff1a\u6a29\uff1a\u3051\u3093\uff1a\u5317\uff1a\u307b\u3046\uff1a\u6761\uff1a\u3058\u3087\u3046\uff1a\u7fa9\uff1a\u3088\u3057\uff1a\u6642\uff1a\u3068\u304d\uff1a\u306e\u8a0e\uff1a\u3068\u3046\uff1a\u4f10\uff1a\u3070\u3064\uff1a\u3092\u547d\uff1a\u3081\u3044\uff1a\u305a\u308b\u5f8c\uff1a\u3054\uff1a\u9ce5\uff1a\u3068\uff1a\u7fbd\uff1a\u3070\uff1a\u4e0a\uff1a\u3058\u3087\u3046\uff1a\u7687\uff1a\u3053\u3046\uff1a\u306e\u9662\uff1a\u3044\u3093\uff1a\u5ba3\uff1a\u305b\u3093\uff1a\u304c\u767c\uff1a\u306f\u3063\uff1a\u305b\u3089\u308c\u308b,\u4eac\uff1a\u304d\u3087\u3046\uff1a\u90fd\uff1a\u3068\uff1a\u306f\u5e55\uff1a\u3070\u304f\uff1a\u5e9c\uff1a\u3075\uff1a\u8ecd\uff1a\u3050\u3093\uff1a\u306b\u5360\uff1a\u305b\u3093\uff1a\u9818\uff1a\u308a\u3087\u3046\uff1a\u3055\u308c\u5931\uff1a\u3057\u3063\uff1a\u6557\uff1a\u3071\u3044\uff1a \n1274,\u6587\uff1a\u3076\u3093\uff1a\u6c38\uff1a\u3048\u3044\uff1a\u306e\u5f79\uff1a\u3048\u304d\uff1a,1281\u5e74\u306e\u5f18\uff1a\u3053\u3046\uff1a\u5b89\uff1a\u3042\u3093\uff1a\u306e\u5f79\uff1a\u3048\u304d\uff1a\u3068\u5408\uff1a\u3042\uff1a\u306f\u305b\u3066 \u5143\uff1a\u3052\u3093\uff1a\u5bc7\uff1a\u3053\u3046\uff1a\u3068\u547c\uff1a\u3088\uff1a\u3076,\u7d04\u4e09\u4e07\u306e\u5143\uff1a\u3052\u3093\uff1a\u8ecd\uff1a\u3050\u3093\uff1a\u304c\u7d04\uff1a\u3084\u304f\uff1a900\u96bb\uff1a\u305b\u304d\uff1a\u306e\u8ecd\uff1a\u3050\u3093\uff1a\u8239\uff1a\u305b\u3093\uff1a\u3067\u5317\uff1a\u304d\u305f\uff1a\u4e5d\uff1a\u304d\u3085\u3046\uff1a\u5dde\uff1a\u3057\u3085\u3046\uff1a\u3078\u9032\uff1a\u3057\u3093\uff1a\u653b\uff1a\u3053\u3046\uff1a\u3059\u308b\u3082\u65e5\uff1a\u306b\uff1a\u672c\uff1a\u307b\u3093\uff1a\u8ecd\uff1a\u3050\u3093\uff1a\u306b\u6483\uff1a\u3052\u304d\uff1a\u9000\uff1a\u305f\u3044\uff1a\u3055\u308c\u308b\n1334,\u5efa\uff1a\u3051\u3093\uff1a\u6b66\uff1a\u3080\uff1a\u306e\u65b0\uff1a\u3057\u3093\uff1a\u653f\uff1a\u305b\u3044\uff1a,\u5f8c\uff1a\u3054\uff1a\u918d\uff1a\u3060\u3044\uff1a\u9190\uff1a\u3054\uff1a\u5929\u7687\u304c\u938c\uff1a\u304b\u307e\uff1a\u5009\uff1a\u304f\u3089\uff1a\u5e55\uff1a\u3070\u304f\uff1a\u5e9c\uff1a\u3075\uff1a\u3092\u5012\uff1a\u305f\u304a\uff1a\u3057\u5929\u7687\u4e2d\u5fc3\u306e\u653f\uff1a\u305b\u3044\uff1a\u6cbb\uff1a\u3062\uff1a\u3092\u5fd7\uff1a\u3053\u3053\u308d\u3056\uff1a\u3059,\u4e8c\u5e74\u3042\u307e\u308a\u3067\u6b66\u58eb\u304c\u96e2\uff1a\u308a\uff1a\u53cd\uff1a\u306f\u3093\uff1a\u3057 \u5f8c\uff1a\u3054\uff1a\u918d\uff1a\u3060\u3044\uff1a\u9190\uff1a\u3054\uff1a\u5929\u7687\u306f\u5409\uff1a\u3088\u3057\uff1a\u91ce\uff1a\u306e\uff1a\u306b\u9003\uff1a\u306e\u304c\uff1a\u308c \u5357\uff1a\u306a\u3093\uff1a\u671d\uff1a\u3061\u3087\u3046\uff1a\u3092\u958b\uff1a\u3072\u3089\uff1a\u304d \u8db3\uff1a\u3042\u3057\uff1a\u5229\uff1a\u304b\u304c\uff1a\u5c0a\uff1a\u305f\u304b\uff1a\u6c0f\uff1a\u3046\u3058\uff1a\u306f\u5149\uff1a\u3053\u3046\uff1a\u660e\uff1a\u3081\u3044\uff1a\u5929\u7687\u3092\u64c1\uff1a\u3088\u3046\uff1a\u3057\u305f\u5317\uff1a\u307b\u304f\uff1a\u671d\uff1a\u3061\u3087\u3046\uff1a\u3092\u958b\u304f\n1338,\u5ba4\uff1a\u3080\u308d\uff1a\u753a\uff1a\u307e\u3061\uff1a\u5e55\uff1a\u3070\u304f\uff1a\u5e9c\uff1a\u3075\uff1a\u6210\uff1a\u305b\u3044\uff1a\u7acb\uff1a\u308a\u3064\uff1a,\u8db3\uff1a\u3042\u3057\uff1a\u5229\uff1a\u304b\u304c\uff1a\u5c0a\uff1a\u305f\u304b\uff1a\u6c0f\uff1a\u3046\u3058\uff1a\u304c\u5317\uff1a\u307b\u304f\uff1a\u671d\uff1a\u3061\u3087\u3046\uff1a\u306e\u5149\uff1a\u3053\u3046\uff1a\u660e\uff1a\u3081\u3044\uff1a\u5929\u7687\u3088\u308a\u5f81\uff1a\u305b\u3044\uff1a\u5937\uff1a\u3044\uff1a\u5927\uff1a\u305f\u3044\uff1a\u5c06\uff1a\u3057\u3087\u3046\uff1a\u8ecd\uff1a\u3050\u3093\uff1a\u306b\u4efb\uff1a\u306b\u3093\uff1a\u3058\u3089\u308c\u308b\u3053\u3068\u306b\u3088\u308a\u6210\uff1a\u305b\u3044\uff1a\u7acb\uff1a\u308a\u3064\uff1a,\u8db3\uff1a\u3042\u3057\uff1a\u5229\uff1a\u304b\u304c\uff1a\u7fa9\uff1a\u3088\u3057\uff1a\u6e80\uff1a\u307f\u3064\uff1a(3\u4ee3)\u304c\u4eac\uff1a\u304d\u3087\u3046\uff1a\u90fd\uff1a\u3068\uff1a\u306e\u5ba4\uff1a\u3080\u308d\uff1a\u753a\uff1a\u307e\u3061\uff1a\u306b<\u82b1\uff1a\u306f\u306a\uff1a\u306e\u5fa1\uff1a\u3054\uff1a\u6240\uff1a\u3057\u3087\uff1a>\u3092\u69cb\uff1a\u304b\u307e\uff1a\u3078\u653f\u6cbb\u3092\u884c\uff1a\u304a\u3053\u306a\uff1a\u3063\u305f\u3053\u3068\u304b\u3089<\u5ba4\u753a\u5e55\u5e9c>\u3068\u79f0\uff1a\u3057\u3087\u3046\uff1a\u3055\u308c\u308b\n1429,\u7409\uff1a\u308a\u3085\u3046\uff1a\u7403\uff1a\u304d\u3085\u3046\uff1a\u7d71\uff1a\u3068\u3046\uff1a\u4e00\uff1a\u3044\u3064\uff1a,\u4e09\u3064\u306e\u52e2\uff1a\u305b\u3044\uff1a\u529b\uff1a\u308a\u3087\u304f\uff1a\u304c\u5341\u4e94\u4e16\uff1a\u305b\u3044\uff1a\u7d00\uff1a\u304d\uff1a\u306b\u7d71\uff1a\u3068\u3046\uff1a\u4e00\uff1a\u3044\u3064\uff1a\u3055\u308c\u308b,\u660e\uff1a\u307f\u3093\uff1a\u306e\u518a\uff1a\u3055\u304f\uff1a\u5c01\uff1a\u307b\u3046\uff1a\u3092\u53d7\uff1a\u3046\uff1a\u3051 \u671d\uff1a\u3061\u3087\u3046\uff1a\u8ca2\uff1a\u3053\u3046\uff1a\u8cbf\uff1a\u307c\u3046\uff1a\u6613\uff1a\u3048\u304d\uff1a\u3092\u884c\uff1a\u304a\u3053\u306a\uff1a\u3075\n1467,\u61c9\uff1a\u304a\u3046\uff1a\u4ec1\uff1a\u306b\u3093\uff1a\u306e\u4e82\uff1a\u3089\u3093\uff1a,\u6230\uff1a\u305b\u3093\uff1a\u570b\uff1a\u3054\u304f\uff1a\u6642\uff1a\u3058\uff1a\u4ee3\uff1a\u3060\u3044\uff1a\u306e\u5e55\uff1a\u307e\u304f\uff1a\u958b\uff1a\u3042\uff1a\u3051,\u5c06\uff1a\u3057\u3087\u3046\uff1a\u8ecd\uff1a\u3050\u3093\uff1a\u5bb6\uff1a\u3051\uff1a\u3068\u7ba1\uff1a\u304b\u3093\uff1a\u9818\uff1a\u308c\u3044\uff1a\u5bb6\uff1a\u3051\uff1a\u306e\u8de1\uff1a\u3042\u3068\uff1a\u7d99\uff1a\u3064\u304e\uff1a\u304e\u722d\uff1a\u3042\u3089\u305d\uff1a\u3072\u304c11\u5e74\u7e8c\uff1a\u3064\u3065\uff1a\u304d\u4eac\uff1a\u304d\u3087\u3046\uff1a\u90fd\uff1a\u3068\uff1a\u306e\u753a\uff1a\u307e\u3061\uff1a\u306f\u7126\uff1a\u3057\u3087\u3046\uff1a\u571f\uff1a\u3069\uff1a\u3068\u5316\uff1a\u304b\uff1a\u3059\n1495,\u5317\uff1a\u307b\u3046\uff1a\u6761\uff1a\u3067\u3046\uff1a\u65e9\uff1a\u3055\u3046\uff1a\u96f2\uff1a\u3046\u3093\uff1a\u304c\u5c0f\uff1a\u304a\uff1a\u7530\uff1a\u3060\uff1a\u539f\uff1a\u306f\u3089\uff1a\u5165\uff1a\u306b\u3075\uff1a\u57ce\uff1a\u3058\u3083\u3046\uff1a,\u5317\uff1a\u307b\u3046\uff1a\u6761\uff1a\u3067\u3046\uff1a\u65e9\uff1a\u3055\u3046\uff1a\u96f2\uff1a\u3046\u3093\uff1a\u306f\u6230\uff1a\u305b\u3093\uff1a\u570b\uff1a\u3054\u304f\uff1a\u5927\uff1a\u3060\u3044\uff1a\u540d\uff1a\u307f\u3084\u3046\uff1a\u306e\u5148\uff1a\u3055\u304d\uff1a\u99c6\uff1a\u304c\uff1a\u3051\u3068\u8a00\u306f\u308c\u308b,\u65e9\u96f2\u304c\u95a2\uff1a\u304f\u308f\u3093\uff1a\u6771\uff1a\u3068\u3046\uff1a\u4e00\uff1a\u3044\u3061\uff1a\u5186\uff1a\u3048\u3093\uff1a\u3092\u652f\uff1a\u3057\uff1a\u914d\uff1a\u306f\u3044\uff1a\u3059\u308b\u5927\u540d\u306b\u306a\u3063\u305f\u904e\uff1a\u304b\uff1a\u7a0b\uff1a\u3066\u3044\uff1a\u306f \u5bb6\uff1a\u304b\uff1a\u81e3\uff1a\u3057\u3093\uff1a\u304c\u4e3b\uff1a\u3057\u3085\uff1a\u541b\uff1a\u304f\u3093\uff1a\u304b\u3089\u6a29\uff1a\u3051\u3093\uff1a\u529b\uff1a\u308a\u3087\u304f\uff1a\u3092\u596a\uff1a\u3046\u3070\uff1a\u3063\u3066\u306e\u3057\u4e0a\uff1a\u3042\u304c\uff1a\u308b\u3068\u3044\u3075<\u4e0b\uff1a\u3052\uff1a\u524b\uff1a\u3053\u304f\uff1a\u4e0a\uff1a\u3058\u3083\u3046\uff1a>\u3067\u3042\u308a \u65e9\u96f2\u306f\u6230\u570b\u5927\u540d\u306e\u5686\uff1a\u304b\u3046\uff1a\u77e2\uff1a\u3057\uff1a\u3068\u3044\u3078\u308b\n1542,\u658e\uff1a\u3055\u3044\uff1a\u85e4\uff1a\u3068\u3046\uff1a\u9053\uff1a\u3069\u3046\uff1a\u4e09\uff1a\u3056\u3093\uff1a\u304c\u7f8e\uff1a\u307f\uff1a\u6fc3\uff1a\u306e\uff1a\u3092\u596a\uff1a\u3046\u3070\uff1a\u3046,\u6230\uff1a\u305b\u3093\uff1a\u570b\uff1a\u3054\u304f\uff1a\u6b66\uff1a\u3076\uff1a\u5c06\uff1a\u3057\u3083\u3046\uff1a\u306e\u4e00\uff1a\u3044\u3061\uff1a,\u4ed6\uff1a\u307b\u304b\uff1a\u306b\u3082\u95a2\uff1a\u304f\u308f\u3093\uff1a\u6771\uff1a\u3068\u3046\uff1a\u4e00\uff1a\u3044\u3061\uff1a\u5186\uff1a\u3048\u3093\uff1a\u3092\u652f\uff1a\u3057\uff1a\u914d\uff1a\u306f\u3044\uff1a\u3057\u305f\u5317\uff1a\u307b\u3046\uff1a\u6761\uff1a\u3067\u3046\uff1a\u6c0f\uff1a\u3046\u3058\uff1a\u5eb7\uff1a\u3084\u3059\uff1a \u7532\uff1a\u304b\uff1a\u6590\uff1a\u3072\uff1a\u306e\u6b66\uff1a\u305f\u3051\uff1a\u7530\uff1a\u3060\uff1a\u4fe1\uff1a\u3057\u3093\uff1a\u7384\uff1a\u3052\u3093\uff1a \u8d8a\uff1a\u3048\u3061\uff1a\u5f8c\uff1a\u3054\uff1a\u306e\u4e0a\uff1a\u3046\u3048\uff1a\u6749\uff1a\u3059\u304e\uff1a\u8b19\uff1a\u3051\u3093\uff1a\u4fe1\uff1a\u3057\u3093\uff1a \u51fa\uff1a\u3067\uff1a\u7fbd\uff1a\u306f\uff1a\u3068\u9678\uff1a\u3080\uff1a\u5965\uff1a\u3064\uff1a\u306e\u4f0a\uff1a\u3060\uff1a\u9054\uff1a\u3066\uff1a\u6b63\uff1a\u307e\u3055\uff1a\u5b97\uff1a\u3080\u306d\uff1a \u5b89\uff1a\u3042\uff1a\u82b8\uff1a\u304d\uff1a\u306e\u6bdb\uff1a\u3082\u3046\uff1a\u5229\uff1a\u308a\uff1a\u5143\uff1a\u3082\u3068\uff1a\u5c31\uff1a\u306a\u308a\uff1a \u571f\uff1a\u3068\uff1a\u4f50\uff1a\u3055\uff1a\u306e\u9577\uff1a\u3061\u3083\u3046\uff1a\u5b97\uff1a\u305d\uff1a\u6211\uff1a\u304b\uff1a\u90e8\uff1a\u3079\uff1a\u5143\uff1a\u3082\u3068\uff1a\u89aa\uff1a\u3061\u304b\uff1a \u85a9\uff1a\u3055\u3064\uff1a\u6469\uff1a\u307e\uff1a\u306e\u5cf6\uff1a\u3057\u307e\uff1a\u6d25\uff1a\u3065\uff1a\u8cb4\uff1a\u3088\u3057\uff1a\u4e45\uff1a\u3072\u3055\uff1a\u306a\u3069\u304c\u3090\u305f\n1553,\u5ddd\uff1a\u304b\u306f\uff1a\u4e2d\uff1a\u306a\u304b\uff1a\u5cf6\uff1a\u3058\u307e\uff1a\u306e\u6230\uff1a\u305f\u305f\u304b\u3072\uff1a,\u7532\uff1a\u304b\uff1a\u6590\uff1a\u3072\uff1a\u306e\u6b66\uff1a\u305f\u3051\uff1a\u7530\uff1a\u3060\uff1a\u4fe1\uff1a\u3057\u3093\uff1a\u7384\uff1a\u3052\u3093\uff1a\u3068\u8d8a\uff1a\u3048\u3061\uff1a\u5f8c\uff1a\u3054\uff1a\u306e\u4e0a\uff1a\u3046\u3078\uff1a\u6749\uff1a\u3059\u304e\uff1a\u8b19\uff1a\u3051\u3093\uff1a\u4fe1\uff1a\u3057\u3093\uff1a,\u6230\uff1a\u305b\u3093\uff1a\u570b\uff1a\u3054\u304f\uff1a\u6642\uff1a\u3058\uff1a\u4ee3\uff1a\u3060\u3044\uff1a\u306e\u975e\uff1a\u3072\uff1a\u5e38\uff1a\u3058\u3083\u3046\uff1a\u306b\u6709\uff1a\u3044\u3046\uff1a\u540d\uff1a\u3081\u3044\uff1a\u306a\u6230\uff1a\u305f\u305f\u304b\uff1a\u3072\u3067\u52dd\uff1a\u3057\u3087\u3046\uff1a\u6557\uff1a\u306f\u3044\uff1a\u306f\u8af8\uff1a\u3057\u3087\uff1a\u8aac\uff1a\u305b\u3064\uff1a\u3042\u308b\u3082\u5b9a\uff1a\u3055\u3060\uff1a\u307e\u3063\u3066\u3090\u306a\u3044\n1560,\u6876\uff1a\u304a\u3051\uff1a\u72ed\uff1a\u306f\u3056\uff1a\u9593\uff1a\u307e\uff1a\u306e\u6230\uff1a\u305f\u305f\u304b\u3072\uff1a,\u5c3e\uff1a\u3092\uff1a\u5f35\uff1a\u306f\u308a\uff1a\u306e\u7e54\uff1a\u304a\uff1a\u7530\uff1a\u3060\uff1a\u4fe1\uff1a\u306e\u3076\uff1a\u9577\uff1a\u306a\u304c\uff1a\u304c\u99ff\uff1a\u3059\u308b\uff1a\u6cb3\uff1a\u304c\uff1a\u306e\u4eca\uff1a\u3044\u307e\uff1a\u5ddd\uff1a\u304c\u306f\uff1a\u7fa9\uff1a\u3088\u3057\uff1a\u5143\uff1a\u3082\u3068\uff1a\u3092\u7834\uff1a\u3084\u3076\uff1a\u308b,\u4fe1\uff1a\u306e\u3076\uff1a\u9577\uff1a\u306a\u304c\uff1a\u306f\u5c3e\uff1a\u3092\uff1a\u5f35\uff1a\u306f\u308a\uff1a\u3068\u7f8e\uff1a\u307f\uff1a\u6fc3\uff1a\u306e\uff1a\u3092\u652f\uff1a\u3057\uff1a\u914d\uff1a\u306f\u3044\uff1a\u4e0b\uff1a\u304b\uff1a\u306b\u304a\u304d <\u5929\uff1a\u3066\u3093\uff1a\u4e0b\uff1a\u304b\uff1a\u5e03\uff1a\u3075\uff1a\u6b66\uff1a\u3076\uff1a>\u3092\u304b\u304b\u3052 \u5f8c\uff1a\u306e\u3061\uff1a\u306b\u8db3\uff1a\u3042\u3057\uff1a\u5229\uff1a\u304b\u304c\uff1a\u7fa9\uff1a\u3088\u3057\uff1a\u662d\uff1a\u3042\u304d\uff1a\u3092\u4eac\uff1a\u304d\u3083\u3046\uff1a\u90fd\uff1a\u3068\uff1a\u304b\u3089\u8ffd\uff1a\u3064\u3044\uff1a\u653e\uff1a\u306f\u3046\uff1a\u3057\u3066\u5ba4\uff1a\u3080\u308d\uff1a\u753a\uff1a\u307e\u3061\uff1a\u5e55\uff1a\u3070\u304f\uff1a\u5e9c\uff1a\u3075\uff1a\u3092\u6ec5\uff1a\u3081\u3064\uff1a\u4ea1\uff1a\u3070\u3046\uff1a\u3055\u305b\u308b\n1590,\u8c4a\uff1a\u3068\u3088\uff1a\u81e3\uff1a\u3068\u307f\uff1a\u79c0\uff1a\u3072\u3067\uff1a\u5409\uff1a\u3088\u3057\uff1a\u306e\u5929\uff1a\u3066\u3093\uff1a\u4e0b\uff1a\u304b\uff1a\u7d71\uff1a\u3068\u3046\uff1a\u4e00\uff1a\u3044\u3064\uff1a,106\u4ee3\u6b63\uff1a\u304a\u307b\uff1a\u89aa\uff1a\u304e\uff1a\u753a\uff1a\u307e\u3061\uff1a\u5929\u7687\u304b\u3089\u95a2\uff1a\u304b\u3093\uff1a\u767d\uff1a\u3071\u304f\uff1a\u306e\u4f4d\uff1a\u304f\u3089\u3090\uff1a\u3092\u6388\uff1a\u3055\u3065\uff1a\u3051\u3089\u308c \u5929\uff1a\u3066\u3093\uff1a\u4e0b\uff1a\u304b\uff1a\u7d71\uff1a\u3068\u3046\uff1a\u4e00\uff1a\u3044\u3064\uff1a\u3078\u306e\u5f8c\uff1a\u3042\u3068\uff1a\u62bc\uff1a\u304a\uff1a\u3057\u3092\u3082\u3089\u3075,\u60e3\uff1a\u3055\u3046\uff1a\u7121\uff1a\u3076\uff1a\u4e8b\uff1a\u3058\uff1a\u4ee4\uff1a\u308c\u3044\uff1a\u3092\u51fa\uff1a\u3060\uff1a\u3057\u3066\u5927\uff1a\u3060\u3044\uff1a\u540d\uff1a\u307f\u3084\u3046\uff1a\u9593\uff1a\u304b\u3093\uff1a\u306e\u79c1\uff1a\u3057\uff1a\u95d8\uff1a\u305f\u3046\uff1a\u3092\u7981\uff1a\u304d\u3093\uff1a\u3058 \u5929\uff1a\u3066\u3093\uff1a\u7687\uff1a\u308f\u3046\uff1a\u3088\u308a\u8c4a\uff1a\u3068\u3088\uff1a\u81e3\uff1a\u3068\u307f\uff1a\u306e\u59d3\uff1a\u305b\u3044\uff1a\u3092\u8cdc\uff1a\u305f\u307e\u306f\uff1a\u308a \u592a\uff1a\u3060\uff1a\u653f\uff1a\u3058\u3083\u3046\uff1a\u5927\uff1a\u3060\u3044\uff1a\u81e3\uff1a\u3058\u3093\uff1a\u306b\u4efb\uff1a\u306b\u3093\uff1a\u547d\uff1a\u3081\u3044\uff1a\u3055\u308c \u5cf6\uff1a\u3057\u307e\uff1a\u6d25\uff1a\u3065\uff1a\u7fa9\uff1a\u3088\u3057\uff1a\u4e45\uff1a\u3072\u3055\uff1a \u5317\uff1a\u307b\u3046\uff1a\u6761\uff1a\u3067\u3046\uff1a\u6c0f\uff1a\u3046\u3058\uff1a\u653f\uff1a\u307e\u3055\uff1a \u4f0a\uff1a\u3060\uff1a\u9054\uff1a\u3066\uff1a\u653f\uff1a\u307e\u3055\uff1a\u5b97\uff1a\u3080\u306d\uff1a\u3089\u8af8\uff1a\u3057\u3087\uff1a\u5927\uff1a\u3060\u3044\uff1a\u540d\uff1a\u307f\u3083\u3046\uff1a\u3092\u5e73\uff1a\u3078\u3044\uff1a\u5b9a\uff1a\u3066\u3044\uff1a\u3057\u3066 \u5929\u4e0b\u7d71\u4e00\n1592,\u6587\uff1a\u3076\u3093\uff1a\u7984\uff1a\u308d\u304f\uff1a\u306e\u5f79\uff1a\u3048\u304d\uff1a,\u79c0\uff1a\u3072\u3067\uff1a\u5409\uff1a\u3088\u3057\uff1a\u306e\u671d\uff1a\u3066\u3046\uff1a\u9bae\uff1a\u305b\u3093\uff1a\u51fa\uff1a\u3057\u3085\u3063\uff1a\u5175\uff1a\u307a\u3044\uff1a,\u4e8c\uff1a\u306b\uff1a\u5ea6\uff1a\u3069\uff1a\u76ee\uff1a\u3081\uff1a\u306e\u6176\uff1a\u3051\u3044\uff1a\u9577\uff1a\u3061\u3083\u3046\uff1a\u306e\u5f79\uff1a\u3048\u304d\uff1a\u3067\u79c0\uff1a\u3072\u3067\uff1a\u5409\uff1a\u3088\u3057\uff1a\u304c\u6ca1\uff1a\u307c\u3063\uff1a\u3057 \u65e5\uff1a\u306b\uff1a\u672c\uff1a\u307b\u3093\uff1a\u8ecd\uff1a\u3050\u3093\uff1a\u306f\u671d\uff1a\u3066\u3046\uff1a\u9bae\uff1a\u305b\u3093\uff1a\u304b\u3089\u64a4\uff1a\u3066\u3063\uff1a\u9000\uff1a\u305f\u3044\uff1a\n1600,\u95a2\uff1a\u305b\u304d\uff1a\u30f6\uff1a\u304c\uff1a\u539f\uff1a\u306f\u3089\uff1a\u306e\u6230\uff1a\u305f\u305f\u304b\u3072\uff1a,\u3053\u306e\u6230\uff1a\u305f\u305f\u304b\uff1a\u3072\u306b\u52dd\uff1a\u3057\u3087\u3046\uff1a\u5229\uff1a\u308a\uff1a\u3057\u305f\u5fb3\uff1a\u3068\u304f\uff1a\u5ddd\uff1a\u304c\u306f\uff1a\u5bb6\uff1a\u3044\u3078\uff1a\u5eb7\uff1a\u3084\u3059\uff1a\u304c \u5f8c\uff1a\u3054\uff1a\u967d\uff1a\u3084\u3046\uff1a\u6210\uff1a\u305c\u3044\uff1a\u5929\u7687\u306b\u3088\u308a\u5f81\uff1a\u305b\u3044\uff1a\u5937\uff1a\u3044\uff1a\u5927\uff1a\u305f\u3044\uff1a\u5c06\uff1a\u3057\u3083\u3046\uff1a\u8ecd\uff1a\u3050\u3093\uff1a\u306b\u4efb\uff1a\u306b\u3093\uff1a\u547d\uff1a\u3081\u3044\uff1a\u3055\u308c \u6c5f\uff1a\u3048\uff1a\u6238\uff1a\u3069\uff1a\u5e55\uff1a\u3070\u304f\uff1a\u5e9c\uff1a\u3075\u304c\uff1a\u6210\uff1a\u305b\u3044\uff1a\u7acb\uff1a\u308a\u3064\uff1a,\u8c4a\uff1a\u3068\u3088\uff1a\u81e3\uff1a\u3068\u307f\uff1a\u653f\uff1a\u305b\u3044\uff1a\u6a29\uff1a\u3051\u3093\uff1a\u306b\u304a\u3051\u308b\u4e94\uff1a\u3054\uff1a\u5927\uff1a\u305f\u3044\uff1a\u8001\uff1a\u3089\u3046\uff1a\u306e\u7b46\uff1a\u3072\u3063\uff1a\u982d\uff1a\u3068\u3046\uff1a\u3067\u3042\u3063\u305f\u5fb3\uff1a\u3068\u304f\uff1a\u5ddd\uff1a\u304c\u306f\uff1a\u5bb6\uff1a\u3044\u3078\uff1a\u5eb7\uff1a\u3084\u3059\uff1a\u304c \u8c4a\uff1a\u3068\u3088\uff1a\u81e3\uff1a\u3068\u307f\uff1a\u6c0f\uff1a\u3057\uff1a\u306e\u652f\uff1a\u3057\uff1a\u914d\uff1a\u306f\u3044\uff1a\u614b\uff1a\u305f\u3044\uff1a\u52e2\uff1a\u305b\u3044\uff1a\u3092\u7dad\uff1a\u3090\uff1a\u6301\uff1a\u3062\uff1a\u3057\u3084\u3046\u3068\u3059\u308b\u77f3\uff1a\u3044\u3057\uff1a\u7530\uff1a\u3060\uff1a\u4e09\uff1a\u307f\u3064\uff1a\u6210\uff1a\u306a\u308a\uff1a\u3068\u95a2\uff1a\u305b\u304d\uff1a\u30f6\uff1a\u304c\uff1a\u539f\uff1a\u306f\u3089\uff1a\u3067\u5c0d\uff1a\u305f\u3044\uff1a\u6c7a\uff1a\u3051\u3064\uff1a\u30fc\u5929\uff1a\u3066\u3093\uff1a\u4e0b\uff1a\u304b\uff1a\u5206\uff1a\u308f\uff1a\u3051\u76ee\uff1a\u3081\uff1a\u306e\u6230\uff1a\u305f\u305f\u304b\uff1a\u3072\u3068\u3044\u306f\u308c \u6771\uff1a\u3068\u3046\uff1a\u8ecd\uff1a\u3050\u3093\uff1a\u3067\u3042\u308b\u5fb3\u5ddd\u5bb6\u5eb7\u304c\u52dd\uff1a\u3057\u3087\u3046\uff1a\u5229\uff1a\u308a\uff1a\u3057\u305f\n1637,\u5cf6\uff1a\u3057\u307e\uff1a\u539f\uff1a\u3070\u3089\uff1a\u306e\u4e82\uff1a\u3089\u3093\uff1a,\u3044\u306f\u3086\u308b<\u9396\uff1a\u3055\uff1a\u570b\uff1a\u3053\u304f\uff1a>\u653f\uff1a\u305b\u3044\uff1a\u7b56\uff1a\u3055\u304f\uff1a\u306e\u5f15\uff1a\u3072\uff1a\u304d\u91d1\uff1a\u304c\u306d\uff1a\u3068\u3082\u306a\u3064\u305f,\u30ad\u30ea\u30b9\u30c8\u6559\uff1a\u3051\u3046\uff1a\u5f92\uff1a\u3068\uff1a\u3089\u304c\u5bfa\uff1a\u3058\uff1a\u793e\uff1a\u3057\u3083\uff1a\u306b\u653e\uff1a\u306f\u3046\uff1a\u706b\uff1a\u304f\u308f\uff1a\u3057\u50e7\uff1a\u305d\u3046\uff1a\u4fb6\uff1a\u308a\u3087\uff1a\u3092\u6bba\uff1a\u3055\u3064\uff1a\u5bb3\uff1a\u304c\u3044\uff1a\u3059\u308b\u306a\u3069\u3057\u305f\u305f\u3081 \u5e55\uff1a\u3070\u304f\uff1a\u5e9c\uff1a\u3075\uff1a\u306f\u5927\uff1a\u305f\u3044\uff1a\u8ecd\uff1a\u3050\u3093\uff1a\u3092\u9001\uff1a\u304a\u304f\uff1a\u308a\u93ae\uff1a\u3061\u3093\uff1a\u58d3\uff1a\u3042\u3064\uff1a\u3059\u308b\n1685,\u751f\uff1a\u3057\u3083\u3046\uff1a\u985e\uff1a\u308b\uff1a\u6190\uff1a\u3042\u306f\u308c\uff1a\u307f\u306e\u4ee4\uff1a\u308c\u3044\uff1a,\u4e94\uff1a\u3054\uff1a\u4ee3\uff1a\u3060\u3044\uff1a\u5c06\uff1a\u3057\u3083\u3046\uff1a\u8ecd\uff1a\u3050\u3093\uff1a \u5fb3\uff1a\u3068\u304f\uff1a\u5ddd\uff1a\u304c\u306f\uff1a\u7db1\uff1a\u3064\u306a\uff1a\u5409\uff1a\u3088\u3057\uff1a,\u75c5\uff1a\u3073\u3083\u3046\uff1a\u4eba\uff1a\u306b\u3093\uff1a\u907a\uff1a\u3090\uff1a\u68c4\uff1a\u304d\uff1a\u3084\u6368\uff1a\u3059\uff1a\u3066\u5b50\uff1a\u3054\uff1a\u3092\u7981\uff1a\u304d\u3093\uff1a\u6b62\uff1a\u3057\uff1a \u4eba\uff1a\u306b\u3093\uff1a\u9593\uff1a\u3052\u3093\uff1a\u4ee5\uff1a\u3044\uff1a\u5916\uff1a\u3050\u308f\u3044\uff1a\u306e\u3042\u3089\u3086\u308b\u751f\uff1a\u305b\u3044\uff1a\u7269\uff1a\u3076\u3064\uff1a\u3078\u306e\u8650\uff1a\u304e\u3083\u304f\uff1a\u5f85\uff1a\u305f\u3044\uff1a\u3084\u6bba\uff1a\u305b\u3063\uff1a\u751f\uff1a\u3057\u3083\u3046\uff1a\u3092\u3082\u7f70\uff1a\u3070\u3064\uff1a\u3059\u308b\u3053\u3068\u3067 \u9053\uff1a\u3060\u3046\uff1a\u5fb3\uff1a\u3068\u304f\uff1a\u5fc3\uff1a\u3057\u3093\uff1a\u3092\u559a\uff1a\u304b\u3093\uff1a\u8d77\uff1a\u304d\uff1a\u3057\u3084\u3046\u3068\u3057\u305f\u3068\u3055\u308c\u308b\n1716,\u4eab\uff1a\u304d\u3084\u3046\uff1a\u4fdd\uff1a\u307b\u3046\uff1a\u306e\u6539\uff1a\u304b\u3044\uff1a\u9769\uff1a\u304b\u304f\uff1a,\u516b\uff1a\u306f\u3061\uff1a\u4ee3\uff1a\u3060\u3044\uff1a\u5c06\uff1a\u3057\u3083\u3046\uff1a\u8ecd\uff1a\u3050\u3093\uff1a \u5fb3\uff1a\u3068\u304f\uff1a\u5ddd\uff1a\u304c\u306f\uff1a\u5409\uff1a\u3088\u3057\uff1a\u5b97\uff1a\u3080\u306d\uff1a,\u8cea\uff1a\u3057\u3063\uff1a\u7d20\uff1a\u305d\uff1a\u5039\uff1a\u3051\u3093\uff1a\u7d04\uff1a\u3084\u304f\uff1a \u7c73\uff1a\u3053\u3081\uff1a\u306e\u5897\uff1a\u305e\u3046\uff1a\u53ce\uff1a\u3057\u3046\uff1a \u516c\uff1a\u304f\uff1a\u4e8b\uff1a\u3058\uff1a\u65b9\uff1a\u304b\u305f\uff1a\u5fa1\uff1a\u304a\uff1a\u5b9a\uff1a\u3055\u3060\u3081\uff1a\u66f8\uff1a\u304c\u304d\uff1a \u5be6\uff1a\u3058\u3064\uff1a\u5b78\uff1a\u304c\u304f\uff1a\u306e\u5968\uff1a\u3057\u3084\u3046\uff1a\u52b1\uff1a\u308c\u3044\uff1a \u76ee\uff1a\u3081\uff1a\u5b89\uff1a\u3084\u3059\uff1a\u7bb1\uff1a\u3070\u3053\uff1a\u306a\u3069\n1767,\u7530\uff1a\u305f\uff1a\u6cbc\uff1a\u306c\u307e\uff1a\u610f\uff1a\u304a\u304d\uff1a\u6b21\uff1a\u3064\u3050\uff1a\u306e\u653f\uff1a\u305b\u3044\uff1a\u6cbb\uff1a\u3058\uff1a,\u5341\uff1a\u3058\u3085\u3046\uff1a\u4ee3\uff1a\u3060\u3044\uff1a\u5c06\uff1a\u3057\u3083\u3046\uff1a\u8ecd\uff1a\u3050\u3093\uff1a \u5fb3\uff1a\u3068\u304f\uff1a\u5ddd\uff1a\u304c\u306f\uff1a\u5bb6\uff1a\u3044\u3078\uff1a\u6cbb\uff1a\u306f\u308b\uff1a\u306e\u6642\uff1a\u3058\uff1a\u4ee3\uff1a\u3060\u3044\uff1a,\u682a\uff1a\u304b\u3076\uff1a\u4ef2\uff1a\u306a\u304b\uff1a\u9593\uff1a\u307e\uff1a\u3092\u516c\uff1a\u3053\u3046\uff1a\u8a8d\uff1a\u306b\u3093\uff1a \u7a0e\uff1a\u305c\u3044\uff1a\u5236\uff1a\u305b\u3044\uff1a\u6539\uff1a\u304b\u3044\uff1a\u9769\uff1a\u304b\u304f\uff1a \u7d4c\uff1a\u3051\u3044\uff1a\u6e08\uff1a\u3056\u3044\uff1a\u3092\u6d3b\uff1a\u304b\u3063\uff1a\u6027\uff1a\u305b\u3044\uff1a\u5316\uff1a\u304b\uff1a\u3055\u305b\u308b\n1787,\u5bdb\uff1a\u304b\u3093\uff1a\u653f\uff1a\u305b\u3044\uff1a\u306e\u6539\uff1a\u304b\u3044\uff1a\u9769\uff1a\u304b\u304f\uff1a,\u5341\uff1a\u3058\u3085\u3046\uff1a\u4e00\uff1a\u3044\u3061\uff1a\u4ee3\uff1a\u3060\u3044\uff1a\u5c06\uff1a\u3057\u3083\u3046\uff1a\u8ecd\uff1a\u3050\u3093\uff1a \u5fb3\uff1a\u3068\u304f\uff1a\u5ddd\uff1a\u304c\u306f\uff1a\u5bb6\uff1a\u3044\u3078\uff1a\u6589\uff1a\u306a\u308a\uff1a\u304c \u767d\uff1a\u3057\u3089\uff1a\u6cb3\uff1a\u304b\u306f\uff1a\u85e9\uff1a\u306f\u3093\uff1a\u4e3b\uff1a\u3057\u3085\uff1a \u677e\uff1a\u307e\u3064\uff1a\u5e73\uff1a\u3060\u3044\u3089\uff1a\u5b9a\uff1a\u3055\u3060\uff1a\u4fe1\uff1a\u306e\u3076\uff1a\u3092\u767b\uff1a\u3068\u3046\uff1a\u7528\uff1a\u3088\u3046\uff1a,\u56f2\u7c73(\u304b\u3053\u3044\u307e\u3044) \u501f\uff1a\u3057\u3083\u3063\uff1a\u91d1\uff1a\u304d\u3093\uff1a\u306e\u5e33\uff1a\u3061\u3083\u3046\uff1a\u6d88\uff1a\u3051\uff1a\u3057 \u8fb2\uff1a\u306e\u3046\uff1a\u6c11\uff1a\u307f\u3093\uff1a\u306e\u5e30\uff1a\u304d\uff1a\u90f7\uff1a\u304d\u3083\u3046\uff1a\u3092\u4fc3\uff1a\u3046\u306a\u304c\uff1a\u3059 \u6e6f\uff1a\u3086\uff1a\u5cf6\uff1a\u3057\u307e\uff1a\u306b\u660c\uff1a\u3057\u3083\u3046\uff1a\u5e73\uff1a\u3078\u3044\uff1a\u5742\uff1a\u3056\u304b\uff1a\u5b78\uff1a\u304c\u304f\uff1a\u554f\uff1a\u3082\u3093\uff1a\u6240\uff1a\u3058\u3087\uff1a\u3092\u3064\u304f\u308a\u5b78\uff1a\u304c\u304f\uff1a\u554f\uff1a\u3082\u3093\uff1a\u30fb\u6b66\uff1a\u3076\uff1a\u8853\uff1a\u3058\u3085\u3064\uff1a\u3092\u5968\uff1a\u3057\u3083\u3046\uff1a\u52b1\uff1a\u308c\u3044\uff1a \u53b3\uff1a\u304d\u3073\uff1a\u3057\u3044\u7dca\uff1a\u304d\u3093\uff1a\u7e2e\uff1a\u3057\u3085\u304f\uff1a\u8ca1\uff1a\u3056\u3044\uff1a\u653f\uff1a\u305b\u3044\uff1a\u3067\u7d4c\uff1a\u3051\u3044\uff1a\u6e08\uff1a\u3056\u3044\uff1a\u306f\u505c\uff1a\u3066\u3044\uff1a\u6ede\uff1a\u305f\u3044\uff1a\n1837,\u5927\uff1a\u304a\u307b\uff1a\u5869\uff1a\u3057\u307b\uff1a\u5e73\uff1a\u3078\u3044\uff1a\u516b\uff1a\u306f\u3061\uff1a\u90ce\uff1a\u3089\u3046\uff1a\u306e\u4e82\uff1a\u3089\u3093\uff1a,\u5929\uff1a\u3066\u3093\uff1a\u4fdd\uff1a\u307d\u3046\uff1a\u306e\u98e2\uff1a\u304d\uff1a\u9949\uff1a\u304d\u3093\uff1a\u304c\u6839\uff1a\u3053\u3093\uff1a\u672c\uff1a\u307d\u3093\uff1a\u539f\uff1a\u3052\u3093\uff1a\u56e0\uff1a\u3044\u3093\uff1a\u306e\u3072\u3068\u3064,\u5e55\uff1a\u3070\u304f\uff1a\u5e9c\uff1a\u3075\uff1a\u306e\u5143\uff1a\u3082\u3068\uff1a\u5f79\uff1a\u3084\u304f\uff1a\u4eba\uff1a\u306b\u3093\uff1a\u306e\u53cd\uff1a\u306f\u3093\uff1a\u4e82\uff1a\u3089\u3093\uff1a\u306f\u5e55\u5e9c\u306b\u885d\uff1a\u3057\u3087\u3046\uff1a\u6483\uff1a\u3052\u304d\uff1a\u3092\u8207\uff1a\u3042\u305f\uff1a\u3078\u308b\n1854,\u65e5\uff1a\u306b\u3061\uff1a\u7c73\uff1a\u3079\u3044\uff1a\u548c\uff1a\u308f\uff1a\u89aa\uff1a\u3057\u3093\uff1a\u6761\uff1a\u3067\u3046\uff1a\u7d04\uff1a\u3084\u304f\uff1a,\u30de\u30b7\u30e5\u30fc\u30fb\u30da\u30ea\u30fc\u304c\u6d66\uff1a\u3046\u3089\uff1a\u8cc0\uff1a\u304c\uff1a\u306b\u8ecd\uff1a\u3050\u3093\uff1a\u8266\uff1a\u304b\u3093\uff1a\u56db\uff1a\u3088\u3093\uff1a\u96bb\uff1a\u305b\u304d\uff1a\u3067\u4f86\uff1a\u3089\u3044\uff1a\u822a\uff1a\u304b\u3046\uff1a,\u4e0b\uff1a\u3057\u3082\uff1a\u7530\uff1a\u3060\uff1a(\u9759\uff1a\u3057\u3065\uff1a\u5ca1\uff1a\u304a\u304b\uff1a\u770c\uff1a\u3051\u3093\uff1a)\u30fb\u7bb1\uff1a\u306f\u3053\uff1a\u9928\uff1a\u3060\u3066\uff1a(\u5317\uff1a\u307b\u3063\uff1a\u6d77\uff1a\u304b\u3044\uff1a\u9053\uff1a\u3060\u3046\uff1a)\u306e\u4e8c\uff1a\u306b\uff1a\u6e2f\uff1a\u304b\u3046\uff1a\u3092\u958b\uff1a\u3072\u3089\uff1a\u304f\n1860,\u685c\uff1a\u3055\u304f\u3089\uff1a\u7530\uff1a\u3060\uff1a\u9580\uff1a\u3082\u3093\uff1a\u5916\uff1a\u3050\u308f\u3044\uff1a\u306e\u8b8a\uff1a\u3078\u3093\uff1a,121\u4ee3\uff1a\u3060\u3044\uff1a\u5b5d\uff1a\u304b\u3046\uff1a\u660e\uff1a\u3081\u3044\uff1a\u5929\u7687\u306e\u52c5\uff1a\u3061\u3087\u304f\uff1a\u8a31\uff1a\u304d\u3087\uff1a\u3092\u5f97\u305a \u65e5\uff1a\u306b\u3061\uff1a\u7c73\uff1a\u3079\u3044\uff1a\u4fee\uff1a\u3057\u3046\uff1a\u4ea4\uff1a\u304b\u3046\uff1a\u901a\uff1a\u3064\u3046\uff1a\u5546\uff1a\u3057\u3083\u3046\uff1a\u6761\uff1a\u3067\u3046\uff1a\u7d04\uff1a\u3084\u304f\uff1a\u3092\u7d50\uff1a\u3080\u3059\uff1a\u3093\u3060 \u3068\u3044\u3075\u6279\uff1a\u3072\uff1a\u5224\uff1a\u306f\u3093\uff1a\u306b \u4e95\uff1a\u3090\uff1a\u4f0a\uff1a\u3044\uff1a\u76f4\uff1a\u306a\u307b\uff1a\u5f3c\uff1a\u3059\u3051\uff1a\u304c \u5b89\uff1a\u3042\u3093\uff1a\u653f\uff1a\u305b\u3044\uff1a\u306e\u5927\uff1a\u305f\u3044\uff1a\u7344\uff1a\u3054\u304f\uff1a\u3067\u591a\uff1a\u304a\u307b\uff1a\u304f\u306e\u5fd7\uff1a\u3057\uff1a\u58eb\uff1a\u3057\uff1a\u3092\u51e6\uff1a\u3057\u3087\uff1a\u5211\uff1a\u3051\u3044\uff1a\u3057\u305f\u3053\u3068\u304c\u539f\uff1a\u3052\u3093\uff1a\u56e0\uff1a\u3044\u3093\uff1a\u3068\u3055\u308c\u308b,\u4e95\uff1a\u3090\uff1a\u4f0a\uff1a\u3044\uff1a\u76f4\uff1a\u306a\u307b\uff1a\u5f3c\uff1a\u3059\u3051\uff1a\u304c\u6c34\uff1a\u307f\uff1a\u6238\uff1a\u3068\uff1a\u85e9\uff1a\u306f\u3093\uff1a\u306e\u6d6a\uff1a\u3089\u3046\uff1a\u58eb\uff1a\u3057\uff1a\u3089\u306b\u6697\uff1a\u3042\u3093\uff1a\u6bba\uff1a\u3055\u3064\uff1a\u3055\u308c\u308b\n1868,\u660e\uff1a\u3081\u3044\uff1a\u6cbb\uff1a\u3062\uff1a\u7dad\uff1a\u3090\uff1a\u65b0\uff1a\u3057\u3093\uff1a,\u524d\uff1a\u305c\u3093\uff1a\u5e74\uff1a\u306d\u3093\uff1a\u306e\u5927\uff1a\u305f\u3044\uff1a\u653f\uff1a\u305b\u3044\uff1a\u5949\uff1a\u307b\u3046\uff1a\u9084\uff1a\u304f\u308f\u3093\uff1a\u3092\u53d7\uff1a\u3046\uff1a\u3051 \u671d\uff1a\u3066\u3046\uff1a\u5ef7\uff1a\u3066\u3044\uff1a\u304c<\u738b\uff1a\u308f\u3046\uff1a\u653f\uff1a\u305b\u3044\uff1a\u5fa9\uff1a\u3075\u3063\uff1a\u53e4\uff1a\u3053\uff1a\u306e\u5927\uff1a\u3060\u3044\uff1a\u53f7\uff1a\u304c\u3046\uff1a\u4ee4\uff1a\u308c\u3044\uff1a>\u3092\u51fa\uff1a\u3060\uff1a\u3059,\u660e\uff1a\u3081\u3044\uff1a\u6cbb\uff1a\u3062\uff1a\u5929\u7687\u304c \u4e94\uff1a\u3054\uff1a\u7b87\uff1a\u304b\uff1a\u6761\uff1a\u3067\u3046\uff1a\u306e\u5fa1\uff1a\u3054\uff1a\u8a93\uff1a\u305b\u3044\uff1a\u6587\uff1a\u3082\u3093\uff1a\u3092\u767c\uff1a\u306f\u3063\uff1a\u5e03\uff1a\u3077\uff1a\u3055\u308c\u308b\n1875,\u6c5f\uff1a\u304b\u3046\uff1a\u83ef\uff1a\u304f\u308f\uff1a\u5cf6\uff1a\u305f\u3046\uff1a\u4e8b\uff1a\u3058\uff1a\u4ef6\uff1a\u3051\u3093\uff1a,\u3053\u306e\u4e8b\uff1a\u3058\uff1a\u4ef6\uff1a\u3051\u3093\uff1a\u306e\u7d50\uff1a\u3051\u3064\uff1a\u679c\uff1a\u304b\uff1a \u65e5\uff1a\u306b\u3063\uff1a\u9bae\uff1a\u305b\u3093\uff1a\u4fee\uff1a\u3057\u3046\uff1a\u4ea4\uff1a\u304b\u3046\uff1a\u6761\uff1a\u3067\u3046\uff1a\u898f\uff1a\u304d\uff1a(\u4e0d\uff1a\u3075\uff1a\u5e73\uff1a\u3073\u3084\u3046\uff1a\u7b49\uff1a\u3069\u3046\uff1a\u6761\uff1a\u3067\u3046\uff1a\u7d04\uff1a\u3084\u304f\uff1a\u3068\u3055\u308c\u308b)\u3092\u7de0\uff1a\u3066\u3044\uff1a\u7d50\uff1a\u3051\u3064\uff1a,\u8ecd\uff1a\u3050\u3093\uff1a\u8266\uff1a\u304b\u3093\uff1a\u96f2\uff1a\u3046\u3093\uff1a\u63da\uff1a\u3084\u3046\uff1a\u53f7\uff1a\u3054\u3046\uff1a\u304c\u98f2\uff1a\u3044\u3093\uff1a\u6599\uff1a\u308c\u3046\uff1a\u6c34\uff1a\u3059\u3044\uff1a\u78ba\uff1a\u304b\u304f\uff1a\u4fdd\uff1a\u307b\uff1a\u306e\u305f\u3081\u6c5f\uff1a\u304b\u3046\uff1a\u83ef\uff1a\u304f\u308f\uff1a\u5cf6\uff1a\u305f\u3046\uff1a\u306b\u63a5\uff1a\u305b\u3063\uff1a\u8fd1\uff1a\u304d\u3093\uff1a\u3057\u305f\u969b\uff1a\u3055\u3044\uff1a \u7a81\uff1a\u3068\u3064\uff1a\u5982\uff1a\u3058\u3087\uff1a\u540c\uff1a\u3069\u3046\uff1a\u5cf6\uff1a\u3068\u3046\uff1a\u306e\u7832\uff1a\u306f\u3046\uff1a\u53f0\uff1a\u3060\u3044\uff1a\u3088\u308a\u5f37\uff1a\u304d\u3083\u3046\uff1a\u70c8\uff1a\u308c\u3064\uff1a\u306a\u7832\uff1a\u306f\u3046\uff1a\u6483\uff1a\u3052\u304d\uff1a\u3092\u53d7\uff1a\u3046\uff1a\u3051\u308b >>\u96f2\uff1a\u3046\u3093\uff1a\u63da\uff1a\u3084\u3046\uff1a\u306f\u53cd\uff1a\u306f\u3093\uff1a\u6483\uff1a\u3052\u304d\uff1a\u3057\u9678\uff1a\u308a\u304f\uff1a\u6230\uff1a\u305b\u3093\uff1a\u968a\uff1a\u305f\u3044\uff1a\u3092\u4e0a\uff1a\u3058\u3083\u3046\uff1a\u9678\uff1a\u308a\u304f\uff1a\u3055\u305b\u7832\uff1a\u306f\u3046\uff1a\u53f0\uff1a\u3060\u3044\uff1a\u3092\u5360\uff1a\u305b\u3093\uff1a\u62e0\uff1a\u304d\u3087\uff1a \u6b66\uff1a\u3076\uff1a\u5668\uff1a\u304d\uff1a\u3092\u6355\uff1a\u307b\uff1a\u7372\uff1a\u304b\u304f\uff1a\u3057\u3066\u9577\uff1a\u306a\u304c\uff1a\u5d0e\uff1a\u3055\u304d\uff1a\u3078\u5e30\uff1a\u304d\uff1a\u7740\uff1a\u3061\u3083\u304f\uff1a\n1877,\u897f\uff1a\u305b\u3044\uff1a\u5357\uff1a\u306a\u3093\uff1a\u6230\uff1a\u305b\u3093\uff1a\u722d\uff1a\u3055\u3046\uff1a,\u620a\uff1a\u307c\uff1a\u8fb0\uff1a\u3057\u3093\uff1a\u6230\uff1a\u305b\u3093\uff1a\u722d\uff1a\u3055\u3046\uff1a\u3092\u6230\uff1a\u305f\u305f\u304b\uff1a\u3063\u305f\u58eb\uff1a\u3057\uff1a\u65cf\uff1a\u305e\u304f\uff1a\u305f\u3061\u304c \u660e\uff1a\u3081\u3044\uff1a\u6cbb\uff1a\u3062\uff1a\u7dad\uff1a\u3090\uff1a\u65b0\uff1a\u3057\u3093\uff1a\u306b\u4e0d\uff1a\u3075\uff1a\u6e80\uff1a\u307e\u3093\uff1a\u3092\u62b1\uff1a\u3044\u3060\uff1a\u304d \u897f\uff1a\u3055\u3044\uff1a\u90f7\uff1a\u304c\u3046\uff1a\u9686\uff1a\u305f\u304b\uff1a\u76db\uff1a\u3082\u308a\uff1a\u3092\u62c5\uff1a\u304b\u3064\uff1a\u3044\u3067\u8702\uff1a\u307b\u3046\uff1a\u8d77\uff1a\u304d\uff1a,\u897f\uff1a\u3055\u3044\uff1a\u90f7\uff1a\u304c\u3046\uff1a\u9686\uff1a\u305f\u304b\uff1a\u76db\uff1a\u3082\u308a\uff1a\u3092\u7dcf\uff1a\u305d\u3046\uff1a\u5927\uff1a\u3060\u3044\uff1a\u5c06\uff1a\u3057\u3083\u3046\uff1a\u3068\u3059\u308b\u53cd\uff1a\u306f\u3093\uff1a\u4e82\uff1a\u3089\u3093\uff1a\u8ecd\uff1a\u3050\u3093\uff1a\u306f\u653f\uff1a\u305b\u3044\uff1a\u5e9c\uff1a\u3075\uff1a\u8ecd\uff1a\u3050\u3093\uff1a\u306b\u93ae\uff1a\u3061\u3093\uff1a\u58d3\uff1a\u3042\u3064\uff1a\u3055\u308c \u897f\u90f7\u306f\u81ea\uff1a\u3058\uff1a\u6c7a\uff1a\u3051\u3064\uff1a \u4ee5\uff1a\u3044\uff1a\u5f8c\uff1a\u3054\uff1a\u58eb\uff1a\u3057\uff1a\u65cf\uff1a\u305e\u304f\uff1a\u306e\u53cd\u4e82\u306f\u9014\uff1a\u3068\uff1a\u7d76\uff1a\u3060\uff1a\u3078 \u620a\uff1a\u307c\uff1a\u8fb0\uff1a\u3057\u3093\uff1a\u6230\uff1a\u305b\u3093\uff1a\u722d\uff1a\u3055\u3046\uff1a\u304b\u3089\u5341\u5e74\u7e8c\uff1a\u3064\u3065\uff1a\u3044\u3066\u3090\u305f\u52d5\uff1a\u3069\u3046\uff1a\u4e82\uff1a\u3089\u3093\uff1a\u306f\u53ce\uff1a\u3057\u3046\uff1a\u675f\uff1a\u305d\u304f\uff1a\u3057\u305f\n1894,\u65e5\uff1a\u306b\u3063\uff1a\u6e05\uff1a\u3057\u3093\uff1a\u6230\uff1a\u305b\u3093\uff1a\u722d\uff1a\u3055\u3046\uff1a,\u671d\uff1a\u3066\u3046\uff1a\u9bae\uff1a\u305b\u3093\uff1a\u3067\u8fb2\uff1a\u306e\u3046\uff1a\u6c11\uff1a\u307f\u3093\uff1a\u4e00\uff1a\u3044\u3063\uff1a\u63c6\uff1a\u304d\uff1a\u304c\u653f\uff1a\u305b\u3044\uff1a\u6cbb\uff1a\u3058\uff1a\u66b4\uff1a\u307c\u3046\uff1a\u52d5\uff1a\u3069\u3046\uff1a\u5316\uff1a\u304b\uff1a(\u6771\uff1a\u3068\u3046\uff1a\u5b78\uff1a\u304c\u304f\uff1a\u9ee8\uff1a\u305f\u3046\uff1a\u306e\u4e82\uff1a\u3089\u3093\uff1a) \u304c\u8d77\uff1a\u304d\uff1a\u7206\uff1a\u3070\u304f\uff1a\u5264\uff1a\u3056\u3044\uff1a\u3068\u306a\u308b,\u8c4a\uff1a\u3068\uff1a\u5cf6\uff1a\u3057\u307e\uff1a\u6c96\uff1a\u304a\u304d\uff1a\u6d77\uff1a\u304b\u3044\uff1a\u6230\uff1a\u305b\u3093\uff1a\u306f \u6211\uff1a\u308f\uff1a\u304c\u9023\uff1a\u308c\u3093\uff1a\u5408\uff1a\u304c\u3075\uff1a\u8266\uff1a\u304b\u3093\uff1a\u968a\uff1a\u305f\u3044\uff1a\u7b2c\uff1a\u3060\u3044\uff1a\u4e00\uff1a\u3044\u3061\uff1a\u904a\uff1a\u3044\u3046\uff1a\u6483\uff1a\u3052\u304d\uff1a\u968a\uff1a\u305f\u3044\uff1a\u5409\uff1a\u3088\u3057\uff1a\u91ce\uff1a\u306e\uff1a\u304c\u793c\uff1a\u308c\u3044\uff1a\u7832\uff1a\u306f\u3046\uff1a\u4ea4\uff1a\u304b\u3046\uff1a\u63db\uff1a\u304f\u308f\u3093\uff1a\u306e\u7528\uff1a\u3088\u3046\uff1a\u610f\uff1a\u3044\uff1a\u3092\u3057\u3066\u8fd1\uff1a\u304d\u3093\uff1a\u63a5\uff1a\u305b\u3064\uff1a\u3057\u305f\u306e\u306b\u5c0d\uff1a\u305f\u3044\uff1a\u3057 \u6e05\uff1a\u3057\u3093\uff1a\u570b\uff1a\u3053\u304f\uff1a\u8ecd\uff1a\u3050\u3093\uff1a\u8266\uff1a\u304b\u3093\uff1a\u6e08\uff1a\u305b\u3044\uff1a\u9060\uff1a\u3048\u3093\uff1a\u306e\u6230\uff1a\u305b\u3093\uff1a\u95d8\uff1a\u305f\u3046\uff1a\u6e96\uff1a\u3058\u3085\u3093\uff1a\u5099\uff1a\u3073\uff1a\u304a\u3088\u3073\u767c\uff1a\u306f\u3063\uff1a\u7832\uff1a\u3071\u3046\uff1a\u3088\u308a\u306f\u3058\u307e\u308b\n1895,\u4e0b\uff1a\u3057\u3082\u306e\uff1a\u95a2\uff1a\u305b\u304d\uff1a\u6761\uff1a\u3067\u3046\uff1a\u7d04\uff1a\u3084\u304f\uff1a,\u65e5\uff1a\u306b\u3063\uff1a\u6e05\uff1a\u3057\u3093\uff1a\u6230\uff1a\u305b\u3093\uff1a\u722d\uff1a\u3055\u3046\uff1a\u306b\u6211\uff1a\u308f\u304c\uff1a\u570b\uff1a\u304f\u306b\uff1a\u304c\u52dd\uff1a\u3057\u3087\u3046\uff1a\u5229\uff1a\u308a\uff1a\u3057\u3066\u7d50\uff1a\u3080\u3059\uff1a\u3070\u308c\u305f\u6761\uff1a\u3067\u3046\uff1a\u7d04\uff1a\u3084\u304f\uff1a >> \u4e09\uff1a\u3055\u3093\uff1a\u570b\uff1a\u3054\u304f\uff1a\u5e72\uff1a\u304b\u3093\uff1a\u6e09\uff1a\u305b\u3075\uff1a\u3092\u53d7\uff1a\u3046\uff1a\u3051\u308b,\u4e00 \u6e05\uff1a\u3057\u3093\uff1a\u570b\uff1a\u3053\u304f\uff1a\u306f\u671d\uff1a\u3066\u3046\uff1a\u9bae\uff1a\u305b\u3093\uff1a\u570b\uff1a\u3053\u304f\uff1a\u304c\u5b8c\uff1a\u304b\u3093\uff1a\u5168\uff1a\u305c\u3093\uff1a\u7121\uff1a\u3080\uff1a\u6b20\uff1a\u3051\u3064\uff1a\u306e\u72ec\uff1a\u3069\u304f\uff1a\u7acb\uff1a\u308a\u3064\uff1a\u81ea\uff1a\u3058\uff1a\u4e3b\uff1a\u3057\u3085\uff1a\u306e\u570b\uff1a\u304f\u306b\uff1a\u3067\u3042\u308b\u3053\u3068\u3092\u627f\uff1a\u3057\u3087\u3046\uff1a\u8a8d\uff1a\u306b\u3093\uff1a\u3059\u308b \u4e8c \u6e05\uff1a\u3057\u3093\uff1a\u570b\uff1a\u3053\u304f\uff1a\u306f\u907c\uff1a\u308a\u3087\u3046\uff1a\u6771\uff1a\u3068\u3046\uff1a\u534a\uff1a\u306f\u3093\uff1a\u5cf6\uff1a\u305f\u3046\uff1a \u53f0\uff1a\u305f\u3044\uff1a\u6e7e\uff1a\u308f\u3093\uff1a\u5168\uff1a\u305c\u3093\uff1a\u5cf6\uff1a\u305f\u3046\uff1a\u53ca\uff1a\u304a\u3088\uff1a\u3073\u6f8e\uff1a\u307b\u3046\uff1a\u6e56\uff1a\u3053\uff1a\u5217\uff1a\u308c\u3063\uff1a\u5cf6\uff1a\u305f\u3046\uff1a\u3092\u6c38\uff1a\u3048\u3044\uff1a\u9060\uff1a\u3048\u3093\uff1a\u306b\u65e5\uff1a\u306b\uff1a\u672c\uff1a\u307b\u3093\uff1a\u306b\u5272\uff1a\u304b\u3064\uff1a\u8b72\uff1a\u3058\u3083\u3046\uff1a\u3059\u308b \u4e09 \u6e05\uff1a\u3057\u3093\uff1a\u570b\uff1a\u3053\u304f\uff1a\u306f\u8ecd\uff1a\u3050\u3093\uff1a\u8cbb\uff1a\u3074\uff1a\u8ce0\uff1a\u3070\u3044\uff1a\u511f\uff1a\u3057\u3083\u3046\uff1a\u91d1\uff1a\u304d\u3093\uff1a\u4e8c\uff1a\u306b\uff1a\u5104\uff1a\u304a\u304f\uff1a\u4e21\uff1a\u30c6\u30fc\u30eb\uff1a\u3092\u652f\uff1a\u3057\uff1a\u6255\uff1a\u306f\u3089\uff1a\u3075 \u56db \u65e5\uff1a\u306b\u3063\uff1a\u6e05\uff1a\u3057\u3093\uff1a\u9593\uff1a\u304b\u3093\uff1a\u306e\u4e00\uff1a\u3044\u3063\uff1a\u5207\uff1a\u3055\u3044\uff1a\u306e\u6761\uff1a\u3067\u3046\uff1a\u7d04\uff1a\u3084\u304f\uff1a\u306f\u4ea4\uff1a\u304b\u3046\uff1a\u6230\uff1a\u305b\u3093\uff1a\u306e\u305f\u3081\u6d88\uff1a\u3057\u3087\u3046\uff1a\u6ec5\uff1a\u3081\u3064\uff1a\u3057\u305f\u306e\u3067\u65b0\uff1a\u3042\u3089\uff1a\u305f\u306b\u901a\uff1a\u3064\u3046\uff1a\u5546\uff1a\u3057\u3083\u3046\uff1a\u822a\uff1a\u304b\u3046\uff1a\u6d77\uff1a\u304b\u3044\uff1a\u6761\uff1a\u3067\u3046\uff1a\u7d04\uff1a\u3084\u304f\uff1a\u3092\u7d50\uff1a\u3080\u3059\uff1a\u3076 \u4e94 \u672c\uff1a\u307b\u3093\uff1a\u6761\uff1a\u3067\u3046\uff1a\u7d04\uff1a\u3084\u304f\uff1a\u6279\uff1a\u3072\uff1a\u51c6\uff1a\u3058\u3085\u3093\uff1a\u5f8c\uff1a\u3054\uff1a \u76f4\uff1a\u305f\u3060\uff1a\u3061\u306b\u4fd8\uff1a\u3075\uff1a\u865c\uff1a\u308a\u3087\uff1a\u3092\u8fd4\uff1a\u3078\u3093\uff1a\u9084\uff1a\u304b\u3093\uff1a\u3059\u308b \u6e05\uff1a\u3057\u3093\uff1a\u570b\uff1a\u3053\u304f\uff1a\u306f\u9001\uff1a\u305d\u3046\uff1a\u9084\uff1a\u304f\u308f\u3093\uff1a\u3055\u308c\u305f\u4fd8\u865c\u3092\u8650\uff1a\u304e\u3083\u304f\uff1a\u5f85\uff1a\u305f\u3044\uff1a\u3042\u308b\u3044\u306f\u51e6\uff1a\u3057\u3087\uff1a\u5211\uff1a\u3051\u3044\uff1a\u305b\u306c\u3053\u3068\n1899,\u7fa9\uff1a\u304e\uff1a\u548c\uff1a\u308f\uff1a\u5718\uff1a\u3060\u3093\uff1a\u4e8b\uff1a\u3058\uff1a\u8b8a\uff1a\u3078\u3093\uff1a,\u65e5\uff1a\u306b\u3061\uff1a\u9732\uff1a\u308d\uff1a\u6230\uff1a\u305b\u3093\uff1a\u722d\uff1a\u3055\u3046\uff1a\u306e\u539f\uff1a\u3052\u3093\uff1a\u56e0\uff1a\u3044\u3093\uff1a\u306e\u3072\u3068\u3064\u3068\u8a00\uff1a\u3044\uff1a\u3078\u308b,\u5b97\uff1a\u3057\u3085\u3046\uff1a\u6559\uff1a\u3051\u3046\uff1a\u7684\uff1a\u3066\u304d\uff1a\u79d8\uff1a\u3072\uff1a\u5bc6\uff1a\u307f\u3064\uff1a\u7d50\uff1a\u3051\u3063\uff1a\u793e\uff1a\u3057\u3083\uff1a\u3067\u3042\u308b\u7fa9\uff1a\u304e\uff1a\u548c\uff1a\u308f\uff1a\u5718\uff1a\u3060\u3093\uff1a\u304c<\u6276\uff1a\u3075\uff1a\u6e05\uff1a\u3057\u3093\uff1a\u6ec5\uff1a\u3081\u3064\uff1a\u6d0b\uff1a\u3084\u3046\uff1a>\u3092\u304b\u304b\u3052 \u5c71\uff1a\u3055\u3093\uff1a\u6771\uff1a\u3068\u3046\uff1a\u7701\uff1a\u3057\u3083\u3046\uff1a\u3067 \u30ad\u30ea\u30b9\u30c8\u6559\uff1a\u3051\u3046\uff1a\u5f92\uff1a\u3068\uff1a\u306e\u6bba\uff1a\u3055\u3064\uff1a\u5bb3\uff1a\u304c\u3044\uff1a \u9244\uff1a\u3066\u3064\uff1a\u9053\uff1a\u3060\u3046\uff1a\u7834\uff1a\u306f\uff1a\u58ca\uff1a\u304b\u3044\uff1a\u306a\u3069\u3092\u884c\uff1a\u304a\u3053\uff1a\u306a\u3044 \u6e05\uff1a\u3057\u3093\uff1a\u8ecd\uff1a\u3050\u3093\uff1a\u3068\u7d50\uff1a\u3051\u3063\uff1a\u8a17\uff1a\u305f\u304f\uff1a\u3057\u3066 \u5317\uff1a\u307a\uff1a\u4eac\uff1a\u304d\u3093\uff1a\u306e\u516c\uff1a\u3053\u3046\uff1a\u4f7f\uff1a\u3057\uff1a\u9928\uff1a\u304f\u308f\u3093\uff1a\u5340\uff1a\u304f\uff1a\u57df\uff1a\u3044\u304d\uff1a\u3092\u5305\uff1a\u306f\u3046\uff1a\u56f2\uff1a\u3090\uff1a \u6e05\uff1a\u3057\u3093\uff1a\u5e1d\uff1a\u3066\u3044\uff1a\u306f\u5217\uff1a\u308c\u3063\uff1a\u570b\uff1a\u3053\u304f\uff1a\u306b\u5c0d\uff1a\u305f\u3044\uff1a\u3057 \u5ba3\uff1a\u305b\u3093\uff1a\u6230\uff1a\u305b\u3093\uff1a\u306e\u4e0a\uff1a\u3058\u3083\u3046\uff1a\u8aed\uff1a\u3086\uff1a\u3092\u767c\uff1a\u306f\u3064\uff1a\u3059\u308b\u3082 \u65e5\uff1a\u306b\uff1a\u672c\uff1a\u307b\u3093\uff1a\u570b\uff1a\u3053\u304f\uff1a\u3092\u4e3b\uff1a\u3057\u3085\uff1a\u529b\uff1a\u308a\u3087\u304f\uff1a\u3068\u3059\u308b\u516b\uff1a\u306f\u3061\uff1a\u30f6\uff1a\u304b\uff1a\u570b\uff1a\u3053\u304f\uff1a\u9023\uff1a\u308c\u3093\uff1a\u5408\uff1a\u304c\u3046\uff1a\u8ecd\uff1a\u3050\u3093\uff1a\u306f\u5317\uff1a\u307a\uff1a\u4eac\uff1a\u304d\u3093\uff1a\u516c\uff1a\u3053\u3046\uff1a\u4f7f\uff1a\u3057\uff1a\u9928\uff1a\u304f\u308f\u3093\uff1a\u5340\uff1a\u304f\uff1a\u57df\uff1a\u3044\u304d\uff1a\u3092\u7fa9\uff1a\u304e\uff1a\u548c\uff1a\u308f\uff1a\u5718\uff1a\u3060\u3093\uff1a\u30fb\u6e05\uff1a\u3057\u3093\uff1a\u5175\uff1a\u307a\u3044\uff1a\u306e\u5305\uff1a\u306f\u3046\uff1a\u56f2\uff1a\u3090\uff1a\u304b\u3089\u6551\uff1a\u304d\u3046\uff1a\u51fa\uff1a\u3057\u3085\u3064\uff1a\n1902,\u65e5\uff1a\u306b\u3061\uff1a\u82f1\uff1a\u3048\u3044\uff1a\u540c\uff1a\u3069\u3046\uff1a\u76df\uff1a\u3081\u3044\uff1a,\u65e5\uff1a\u306b\u3061\uff1a\u9732\uff1a\u308d\uff1a\u6230\uff1a\u305b\u3093\uff1a\u722d\uff1a\u3055\u3046\uff1a\u306e\u52dd\uff1a\u3057\u3083\u3046\uff1a\u5229\uff1a\u308a\uff1a\u306b\u852d\uff1a\u304b\u3052\uff1a\u306e\u529b\uff1a\u3061\u304b\u3089\uff1a\u3068\u306a\u308b,\u4e00 \u65e5\uff1a\u306b\u3061\uff1a\u82f1\uff1a\u3048\u3044\uff1a\u4e21\uff1a\u308a\u3083\u3046\uff1a\u570b\uff1a\u3053\u304f\uff1a\u306f\u6e05\uff1a\u3057\u3093\uff1a\u97d3\uff1a\u304b\u3093\uff1a\u4e21\uff1a\u308a\u3083\u3046\uff1a\u570b\uff1a\u3053\u304f\uff1a\u306e\u72ec\uff1a\u3069\u304f\uff1a\u7acb\uff1a\u308a\u3064\uff1a\u3092\u627f\uff1a\u3057\u3087\u3046\uff1a\u8a8d\uff1a\u306b\u3093\uff1a\u3059\u308b \u3057\u304b\u3057\u82f1\uff1a\u3048\u3044\uff1a\u570b\uff1a\u3053\u304f\uff1a\u306f\u6e05\uff1a\u3057\u3093\uff1a\u570b\uff1a\u3053\u304f\uff1a\u3067 \u65e5\uff1a\u306b\uff1a\u672c\uff1a\u307b\u3093\uff1a\u306f\u6e05\uff1a\u3057\u3093\uff1a\u97d3\uff1a\u304b\u3093\uff1a\u4e21\uff1a\u308a\u3083\u3046\uff1a\u570b\uff1a\u3053\u304f\uff1a\u3067\u653f\uff1a\u305b\u3044\uff1a\u6cbb\uff1a\u3058\uff1a\u30fb\u7d4c\uff1a\u3051\u3044\uff1a\u6e08\uff1a\u3056\u3044\uff1a\u4e0a\uff1a\u3058\u3083\u3046\uff1a\u683c\uff1a\u304b\u304f\uff1a\u6bb5\uff1a\u3060\u3093\uff1a\u306e\u5229\uff1a\u308a\uff1a\u76ca\uff1a\u3048\u304d\uff1a\u3092\u6709\uff1a\u3044\u3046\uff1a\u3059\u308b\u306e\u3067 \u305d\u308c\u3089\u306e\u5229\uff1a\u308a\uff1a\u76ca\uff1a\u3048\u304d\uff1a\u304c\u7b2c\uff1a\u3060\u3044\uff1a\u4e09\uff1a\u3055\u3093\uff1a\u570b\uff1a\u3054\u304f\uff1a\u306e\u4fb5\uff1a\u3057\u3093\uff1a\u7565\uff1a\u308a\u3083\u304f\uff1a\u3084\u5185\uff1a\u306a\u3044\uff1a\u4e82\uff1a\u3089\u3093\uff1a\u3067\u4fb5\uff1a\u3057\u3093\uff1a\u8feb\uff1a\u3071\u304f\uff1a\u3055\u308c\u305f\u6642\uff1a\u3068\u304d\uff1a\u306f\u5fc5\uff1a\u3072\u3064\uff1a\u8981\uff1a\u3048\u3046\uff1a\u306a\u63aa\uff1a\u305d\uff1a\u7f6e\uff1a\u3061\uff1a\u3092\u3068\u308b \u4e8c \u65e5\uff1a\u306b\u3061\uff1a\u82f1\uff1a\u3048\u3044\uff1a\u306e\u4e00\uff1a\u3044\u3063\uff1a\u65b9\uff1a\u3071\u3046\uff1a\u304c\u3053\u306e\u5229\uff1a\u308a\uff1a\u76ca\uff1a\u3048\u304d\uff1a\u3092\u8b77\uff1a\u307e\u3082\uff1a\u308b\u305f\u3081\u7b2c\uff1a\u3060\u3044\uff1a\u4e09\uff1a\u3055\u3093\uff1a\u570b\uff1a\u3054\u304f\uff1a\u3068\u6230\uff1a\u305f\u305f\u304b\uff1a\u3075\u6642\uff1a\u3068\u304d\uff1a\u306f\u4ed6\uff1a\u305f\uff1a\u306e\u4e00\uff1a\u3044\u3063\uff1a\u65b9\uff1a\u3071\u3046\uff1a\u306f\u53b3\uff1a\u3052\u3093\uff1a\u6b63\uff1a\u305b\u3044\uff1a\u4e2d\uff1a\u3061\u3085\u3046\uff1a\u7acb\uff1a\u308a\u3064\uff1a\u3092\u5b88\uff1a\u307e\u3082\uff1a\u308a \u4ed6\uff1a\u305f\uff1a\u570b\uff1a\u3053\u304f\uff1a\u304c\u6575\uff1a\u3066\u304d\uff1a\u5074\uff1a\u304c\u306f\uff1a\u306b\u53c2\uff1a\u3055\u3093\uff1a\u6230\uff1a\u305b\u3093\uff1a\u3059\u308b\u306e\u3092\u9632\uff1a\u3075\u305b\uff1a\u3050 \u4e09 \u4ed6\uff1a\u305f\uff1a\u570b\uff1a\u3053\u304f\uff1a\u304c\u540c\uff1a\u3069\u3046\uff1a\u76df\uff1a\u3081\u3044\uff1a\u570b\uff1a\u3053\u304f\uff1a\u3068\u306e\u4ea4\uff1a\u304b\u3046\uff1a\u6230\uff1a\u305b\u3093\uff1a\u306b\u52a0\uff1a\u304f\u306f\uff1a\u306f\u308b\u6642\uff1a\u3068\u304d\uff1a\u306f \u4ed6\uff1a\u305f\uff1a\u306e\u540c\uff1a\u3069\u3046\uff1a\u76df\uff1a\u3081\u3044\uff1a\u570b\uff1a\u3053\u304f\uff1a\u306f \u63f4\uff1a\u3048\u3093\uff1a\u52a9\uff1a\u3058\u3087\uff1a\u3092\u8207\uff1a\u3042\u305f\uff1a\u3078\u308b\n1904,\u65e5\uff1a\u306b\u3061\uff1a\u9732\uff1a\u308d\uff1a\u6230\uff1a\u305b\u3093\uff1a\u722d\uff1a\u3055\u3046\uff1a,\u6975\uff1a\u304d\u3087\u304f\uff1a\u6771\uff1a\u3068\u3046\uff1a\u306e\u30ed\u30b7\u30a2\u8ecd\uff1a\u3050\u3093\uff1a\u306b\u52d5\uff1a\u3069\u3046\uff1a\u54e1\uff1a\u3090\u3093\uff1a\u4ee4\uff1a\u308c\u3044\uff1a\u304c \u6e80\uff1a\u307e\u3093\uff1a\u6d32\uff1a\u3057\u3046\uff1a\u306b\u306f\u6212\uff1a\u304b\u3044\uff1a\u53b3\uff1a\u3052\u3093\uff1a\u4ee4\uff1a\u308c\u3044\uff1a\u304c\u4e0b\uff1a\u304f\u3060\uff1a\u3055\u308c \u5bfe\uff1a\u305f\u3044\uff1a\u9732\uff1a\u308d\uff1a\u4ea4\uff1a\u304b\u3046\uff1a\u6e09\uff1a\u305b\u3075\uff1a\u306f\u6c7a\uff1a\u3051\u3064\uff1a\u88c2\uff1a\u308c\u3064\uff1a \u6211\uff1a\u308f\u304c\uff1a\u570b\uff1a\u304f\u306b\uff1a\u306f\u570b\uff1a\u3053\u3063\uff1a\u4ea4\uff1a\u304b\u3046\uff1a\u65ad\uff1a\u3060\u3093\uff1a\u7d76\uff1a\u305c\u3064\uff1a\u3092\u9732\uff1a\u308d\uff1a\u570b\uff1a\u3053\u304f\uff1a\u306b\u901a\uff1a\u3064\u3046\uff1a\u544a\uff1a\u3053\u304f\uff1a,\u6211\uff1a\u308f\u304c\uff1a\u570b\uff1a\u304f\u306b\uff1a\u806f\uff1a\u308c\u3093\uff1a\u5408\uff1a\u304c\u3075\uff1a\u8266\uff1a\u304b\u3093\uff1a\u968a\uff1a\u305f\u3044\uff1a\u306b\u3088\u308b \u65c5\uff1a\u308a\u3087\uff1a\u9806\uff1a\u3058\u3085\u3093\uff1a\u6e2f\uff1a\u304b\u3046\uff1a\u5916\uff1a\u3050\u308f\u3044\uff1a\u306e\u653b\uff1a\u3053\u3046\uff1a\u6483\uff1a\u3052\u304d\uff1a \u4ec1\uff1a\u3058\u3093\uff1a\u5ddd\uff1a\u305b\u3093\uff1a\u6c96\uff1a\u304a\u304d\uff1a\u306b\u3066\u6575\uff1a\u3066\u304d\uff1a\u8266\uff1a\u304b\u3093\uff1a\u306e\u6483\uff1a\u3052\u304d\uff1a\u6c88\uff1a\u3061\u3093\uff1a\u304c\u3042\u308a \u6b21\uff1a\u3064\u304e\uff1a\u306e\u65e5\uff1a\u3072\uff1a\u306b\u5ba3\u6226 >> \u907c\uff1a\u308a\u3083\u3046\uff1a\u967d\uff1a\u3084\u3046\uff1a\u30fb\u6c99\uff1a\u3057\u3083\uff1a\u6cb3\uff1a\u304b\uff1a\u306e\u6703\uff1a\u304f\u308f\u3044\uff1a\u6230\uff1a\u305b\u3093\uff1a\u306b\u52dd\uff1a\u3057\u3087\u3046\uff1a\u5229\uff1a\u308a\uff1a \u6d77\uff1a\u304b\u3044\uff1a\u4e0a\uff1a\u3058\u3083\u3046\uff1a\u6a29\uff1a\u3051\u3093\uff1a\u306e\u7372\uff1a\u304b\u304f\uff1a\u5f97\uff1a\u3068\u304f\uff1a \u65c5\uff1a\u308a\u3087\uff1a\u9806\uff1a\u3058\u3085\u3093\uff1a\u9665\uff1a\u304b\u3093\uff1a\u843d\uff1a\u3089\u304f\uff1a \u5949\uff1a\u307b\u3046\uff1a\u5929\uff1a\u3066\u3093\uff1a\u5360\uff1a\u305b\u3093\uff1a\u9818\uff1a\u308a\u3087\u3046\uff1a\u3092\u7d4c\uff1a\u3078\uff1a\u3066 \u65e5\uff1a\u306b\uff1a\u672c\uff1a\u307b\u3093\uff1a\u6d77\uff1a\u304b\u3044\uff1a\u6d77\uff1a\u304b\u3044\uff1a\u6230\uff1a\u305b\u3093\uff1a\u306b\u3066\u30d0\u30eb\u30c1\u30c3\u30af\u8266\uff1a\u304b\u3093\uff1a\u968a\uff1a\u305f\u3044\uff1a\u3092\u5168\uff1a\u305c\u3093\uff1a\u6ec5\uff1a\u3081\u3064\uff1a\u3055\u305b \u6a3a\uff1a\u304b\u3089\uff1a\u592a\uff1a\u3075\u3068\uff1a\u5168\uff1a\u305c\u3093\uff1a\u5cf6\uff1a\u305f\u3046\uff1a\u3092\u5360\uff1a\u305b\u3093\uff1a\u9818\uff1a\u308a\u3083\u3046\uff1a\n1931,\u6e80\uff1a\u307e\u3093\uff1a\u6d32\uff1a\u3057\u3046\uff1a\u4e8b\uff1a\u3058\uff1a\u8b8a\uff1a\u3078\u3093\uff1a,\u30bd\u9023\uff1a\u308c\u3093\uff1a\u306e\u5916\uff1a\u304c\u3044\uff1a\u8499\uff1a\u3082\u3046\uff1a\u9032\uff1a\u3057\u3093\uff1a\u51fa\uff1a\u3057\u3085\u3064\uff1a \u4e8b\uff1a\u3058\uff1a\u5be6\uff1a\u3058\u3064\uff1a\u4e0a\uff1a\u3058\u3083\u3046\uff1a\u4e09\u3064\u306e\u653f\uff1a\u305b\u3044\uff1a\u5e9c\uff1a\u3075\uff1a\u3092\u6301\uff1a\u3082\uff1a\u3064\u4e0d\uff1a\u3075\uff1a\u5b89\uff1a\u3042\u3093\uff1a\u5b9a\uff1a\u3066\u3044\uff1a\u306a\u652f\uff1a\u3057\uff1a\u90a3\uff1a\u306a\uff1a \u65e5\uff1a\u306b\uff1a\u672c\uff1a\u307b\u3093\uff1a\u4eba\uff1a\u3058\u3093\uff1a\u306e\u8650\uff1a\u304e\u3083\u304f\uff1a\u6bba\uff1a\u3055\u3064\uff1a \u5f35\uff1a\u3061\u3087\u3046\uff1a\u4f5c\uff1a\u3055\u304f\uff1a\u9716\uff1a\u308a\u3093\uff1a\u30fb\u5f35\uff1a\u3061\u3087\u3046\uff1a\u5b78\uff1a\u304c\u304f\uff1a\u826f\uff1a\u308a\u3087\u3046\uff1a\u306e\u79d5\uff1a\u3072\uff1a\u653f\uff1a\u305b\u3044\uff1a\u306b\u3088\u308b\u6e80\uff1a\u307e\u3093\uff1a\u6d32\uff1a\u3057\u3046\uff1a\u4eba\uff1a\u3058\u3093\uff1a\u306e\u7aae\uff1a\u304d\u3085\u3046\uff1a\u4e4f\uff1a\u307c\u3075\uff1a \u6e80\uff1a\u307e\u3093\uff1a\u6d32\uff1a\u3057\u3046\uff1a\u72ec\uff1a\u3069\u304f\uff1a\u7acb\uff1a\u308a\u3064\uff1a\u904b\uff1a\u3046\u3093\uff1a\u52d5\uff1a\u3069\u3046\uff1a\u306a\u3069 \u6e80\u6d32\u306b\u306f\u3044\u3064\u7206\uff1a\u3070\u304f\uff1a\u767c\uff1a\u306f\u3064\uff1a\u3057\u3066\u3082\u304a\u304b\u3057\u304f\u306a\u3044 \u7dca\uff1a\u304d\u3093\uff1a\u5f35\uff1a\u3061\u3083\u3046\uff1a\u72b6\uff1a\u3058\u3083\u3046\uff1a\u614b\uff1a\u305f\u3044\uff1a\u304c\u3042\u3063\u305f,\u77f3\uff1a\u3044\u3057\uff1a\u539f\uff1a\u306f\u3089\uff1a\u839e\uff1a\u304b\u3093\uff1a\u723e\uff1a\u3058\uff1a\u4e2d\uff1a\u3061\u3085\u3046\uff1a\u4f50\uff1a\u3055\uff1a\u306e\u7dbf\uff1a\u3081\u3093\uff1a\u5bc6\uff1a\u307f\u3064\uff1a\u306a\u8a08\uff1a\u3051\u3044\uff1a\u753b\uff1a\u304b\u304f\uff1a\u306b\u3088\u308a \u67f3\uff1a\u308a\u3046\uff1a\u6761\uff1a\u3067\u3046\uff1a\u6e9d\uff1a\u3053\u3046\uff1a\u306b\u304a\u3051\u308b\u6e80\uff1a\u307e\u3093\uff1a\u6d32\uff1a\u3057\u3046\uff1a\u9244\uff1a\u3066\u3064\uff1a\u9053\uff1a\u3060\u3046\uff1a\u306e\u7dda\uff1a\u305b\u3093\uff1a\u8def\uff1a\u308d\uff1a\u304c\u5c0f\uff1a\u305b\u3046\uff1a\u898f\uff1a\u304d\uff1a\u6a21\uff1a\u307c\uff1a\u306b\u7206\uff1a\u3070\u304f\uff1a\u7834\uff1a\u306f\uff1a\u3055\u308c \u305d\u308c\u3092\u5f35\uff1a\u3061\u3087\u3046\uff1a\u5b78\uff1a\u304b\u304f\uff1a\u826f\uff1a\u308a\u3087\u3046\uff1a\u306e\u4ed5\uff1a\u3057\uff1a\u696d\uff1a\u308f\u3056\uff1a\u3068\u3057\u305f\u95a2\uff1a\u304b\u3093\uff1a\u6771\uff1a\u3068\u3046\uff1a\u8ecd\uff1a\u3050\u3093\uff1a\u306f \u5317\uff1a\u307b\u304f\uff1a\u5927\uff1a\u305f\u3044\uff1a\u55b6\uff1a\u3048\u3044\uff1a\u306e\u652f\uff1a\u3057\uff1a\u90a3\uff1a\u306a\uff1a\u8ecd\uff1a\u3050\u3093\uff1a\u3092\u6557\uff1a\u306f\u3044\uff1a\u8d70\uff1a\u305d\u3046\uff1a\u305b\u3057\u3081 \u3053\u308c\u3092\u5360\uff1a\u305b\u3093\uff1a\u9818\uff1a\u308a\u3083\u3046\uff1a\u3057\u305f\n1937,\u652f\uff1a\u3057\uff1a\u90a3\uff1a\u306a\uff1a\u4e8b\uff1a\u3058\uff1a\u8b8a\uff1a\u3078\u3093\uff1a,\u76e7\uff1a\u308d\uff1a\u6e9d\uff1a\u3053\u3046\uff1a\u6a4b\uff1a\u3051\u3046\uff1a\u4e8b\uff1a\u3058\uff1a\u4ef6\uff1a\u3051\u3093\uff1a\u3092\u5951\uff1a\u3051\u3044\uff1a\u6a5f\uff1a\u304d\uff1a\u3068\u3057 \u4e0a\uff1a\u3057\u3083\u3093\uff1a\u6d77\uff1a\u306f\u3044\uff1a\u4e8b\uff1a\u3058\uff1a\u8b8a\uff1a\u306f\u3093\uff1a\u3078 \u305d\u3057\u3066\u65e5\uff1a\u306b\u3063\uff1a\u652f\uff1a\u3057\uff1a\u4e21\uff1a\u308a\u3083\u3046\uff1a\u570b\uff1a\u3053\u304f\uff1a\u304c\u5168\uff1a\u305c\u3093\uff1a\u9762\uff1a\u3081\u3093\uff1a\u6230\uff1a\u305b\u3093\uff1a\u722d\uff1a\u3055\u3046\uff1a\u306e\u6bb5\uff1a\u3060\u3093\uff1a\u968e\uff1a\u304b\u3044\uff1a\u306b\u7a81\uff1a\u3068\u3064\uff1a\u5165\uff1a\u306b\u3075\uff1a\u3057\u305f,\u8ecd\uff1a\u3050\u3093\uff1a\u4e8b\uff1a\u3058\uff1a\u6f14\uff1a\u3048\u3093\uff1a\u7fd2\uff1a\u3057\u3075\uff1a\u3092\u7d42\uff1a\u3057\u3085\u3046\uff1a\u4e86\uff1a\u308c\u3046\uff1a\u3057\u305f\u652f\uff1a\u3057\uff1a\u90a3\uff1a\u306a\uff1a\u99d0\uff1a\u3061\u3085\u3046\uff1a\u5c6f\uff1a\u3068\u3093\uff1a\u6b69\uff1a\u307b\uff1a\u5175\uff1a\u3078\u3044\uff1a\u306b\u5c0d\uff1a\u305f\u3044\uff1a\u3057\u9283\uff1a\u3058\u3085\u3046\uff1a\u6483\uff1a\u3052\u304d\uff1a\u304c\u6d74\uff1a\u3042\uff1a\u3073\u305b\u3089\u308c \u6211\uff1a\u308f\u304c\uff1a\u8ecd\uff1a\u3050\u3093\uff1a\u306f\u61c9\uff1a\u304a\u3046\uff1a\u5c04\uff1a\u3057\u3083\uff1a\u305b\u305a\u306b\u72b6\uff1a\u3058\u3083\u3046\uff1a\u6cc1\uff1a\u304d\u3083\u3046\uff1a\u306e\u628a\uff1a\u306f\uff1a\u63e1\uff1a\u3042\u304f\uff1a \u652f\uff1a\u3057\uff1a\u90a3\uff1a\u306a\uff1a\u8ecd\uff1a\u3050\u3093\uff1a\u3068\u306e\u4ea4\uff1a\u304b\u3046\uff1a\u6e09\uff1a\u305b\u3075\uff1a\u3092\u9032\uff1a\u3059\u3059\uff1a\u3081\u305f\u304c \u6211\uff1a\u308f\u304c\uff1a\u8ecd\uff1a\u3050\u3093\uff1a\u306e\u6230\uff1a\u305b\u3093\uff1a\u95d8\uff1a\u3068\u3046\uff1a\u614b\uff1a\u305f\u3044\uff1a\u52e2\uff1a\u305b\u3044\uff1a\u3092\u307f\u305f\u652f\uff1a\u3057\uff1a\u90a3\uff1a\u306a\uff1a\u5175\uff1a\u3078\u3044\uff1a\u306f\u731b\uff1a\u307e\u3046\uff1a\u5c04\uff1a\u3057\u3083\uff1a\u3057 \u4e03\u6642\uff1a\u3058\uff1a\u9593\uff1a\u304b\u3093\uff1a\u306e\u81ea\uff1a\u3058\uff1a\u91cd\uff1a\u3061\u3087\u3046\uff1a\u3082\u865a\uff1a\u3080\u306a\uff1a\u3057\u304f\u6211\u8ecd\u306f\u53cd\uff1a\u306f\u3093\uff1a\u6483\uff1a\u3052\u304d\uff1a \u7adc\uff1a\u308a\u3085\u3046\uff1a\u738b\uff1a\u308f\u3046\uff1a\u5ef3\uff1a\u3061\u3087\u3046\uff1a\u306e\u6575\uff1a\u3066\u304d\uff1a\u3092\u6483\uff1a\u3052\u304d\uff1a\u6ec5\uff1a\u3081\u3064\uff1a\u3057\u6c38\uff1a\u3048\u3044\uff1a\u5b9a\uff1a\u3066\u3044\uff1a\u6cb3\uff1a\u304c\uff1a\u306e\u53f3\uff1a\u3046\uff1a\u5cb8\uff1a\u304c\u3093\uff1a\u3078\u9032\uff1a\u3057\u3093\uff1a\u51fa\uff1a\u3057\u3085\u3064\uff1a\n1941,\u5927\uff1a\u3060\u3044\uff1a\u6771\uff1a\u3068\u3046\uff1a\u4e9e\uff1a\u3042\uff1a\u6230\uff1a\u305b\u3093\uff1a\u722d\uff1a\u3055\u3046\uff1a,\u6557\uff1a\u306f\u3044\uff1a\u6230\uff1a\u305b\u3093\uff1a\u5f8c\uff1a\u3054\uff1a\u306e\u6211\uff1a\u308f\u304c\uff1a\u570b\uff1a\u304f\u306b\uff1a\u306f \u3053\u306e\u6230\uff1a\u305b\u3093\uff1a\u722d\uff1a\u3055\u3046\uff1a\u3092<\u592a\uff1a\u305f\u3044\uff1a\u5e73\uff1a\u3078\u3044\uff1a\u6d0b\uff1a\u3084\u3046\uff1a\u6230\u722d>\u3068\u547c\uff1a\u3053\uff1a\u7a31\uff1a\u305b\u3046\uff1a\u3057\u3066\u3090\u308b,\u3053\u306e\u6230\u722d\u306b\u6557\uff1a\u3084\u3076\uff1a\u308c\u305f\u6211\u570b\u306f\u5360\uff1a\u305b\u3093\uff1a\u9818\uff1a\u308a\u3083\u3046\uff1a\u7d71\uff1a\u3068\u3046\uff1a\u6cbb\uff1a\u3061\uff1a\u3055\u308c \u52dd\uff1a\u3057\u3087\u3046\uff1a\u8005\uff1a\u3057\u3083\uff1a\u306b\u90fd\uff1a\u3064\uff1a\u5408\uff1a\u304c\u3075\uff1a\u306e\u60e1\uff1a\u308f\u308b\uff1a\u3044\u6b74\uff1a\u308c\u304d\uff1a\u53f2\uff1a\u3057\uff1a\u306e\u6559\uff1a\u3051\u3046\uff1a\u80b2\uff1a\u3044\u304f\uff1a\u3092\u4e00\uff1a\u3044\u3063\uff1a\u5207\uff1a\u3055\u3044\uff1a\u6392\uff1a\u306f\u3044\uff1a\u9664\uff1a\u3058\u3087\uff1a\u3055\u308c\u4eca\uff1a\u3044\u307e\uff1a\u306b\u81f3\uff1a\u3044\u305f\uff1a\u308b\n1945,\u30dd\u30c4\u30c0\u30e0\u5ba3\uff1a\u305b\u3093\uff1a\u8a00\uff1a\u3052\u3093\uff1a,\u6b63\uff1a\u305b\u3044\uff1a\u5f0f\uff1a\u3057\u304d\uff1a\u540d\uff1a\u3081\u3044\uff1a\u7a31\uff1a\u305b\u3046\uff1a\u306f<\u65e5\uff1a\u306b\uff1a\u672c\uff1a\u307b\u3093\uff1a\u3078\u306e\u964d\uff1a\u304b\u3046\uff1a\u4f0f\uff1a\u3075\u304f\uff1a\u8981\uff1a\u3048\u3046\uff1a\u6c42\uff1a\u304d\u3046\uff1a\u306e\u6700\uff1a\u3055\u3044\uff1a\u7d42\uff1a\u3057\u3085\u3046\uff1a\u5ba3\uff1a\u305b\u3093\uff1a\u8a00\uff1a\u3052\u3093\uff1a>,\u5168\uff1a\u305c\u3093\uff1a13\u30f6\uff1a\u304b\uff1a\u6761\uff1a\u3067\u3046\uff1a\u304b\u3089\u306a\u308a \u30a4\u30ae\u30ea\u30b9\u30fb\u30a2\u30e1\u30ea\u30ab\u5408\uff1a\u304c\u3063\uff1a\u8846\uff1a\u3057\u3085\u3046\uff1a\u570b\uff1a\u3053\u304f\uff1a\u30fb\u4e2d\uff1a\u3061\u3085\u3046\uff1a\u83ef\uff1a\u304f\u308f\uff1a\u6c11\uff1a\u307f\u3093\uff1a\u570b\uff1a\u3053\u304f\uff1a\u306e\u653f\uff1a\u305b\u3044\uff1a\u5e9c\uff1a\u3075\uff1a\u9996\uff1a\u3057\u3085\uff1a\u8133\uff1a\u306e\u3046\uff1a\u306e\u9023\uff1a\u308c\u3093\uff1a\u540d\uff1a\u3081\u3044\uff1a\u306b\u304a\u3044\u3066\u767c\uff1a\u306f\u3063\uff1a\u305b\u3089\u308c \u30bd\u30d3\u30a8\u30c8\u9023\uff1a\u308c\u3093\uff1a\u90a6\uff1a\u3071\u3046\uff1a\u306f \u5f8c\uff1a\u3042\u3068\uff1a\u304b\u3089\u52a0\uff1a\u304f\u306f\uff1a\u306f\u308a\u8ffd\uff1a\u3064\u3044\uff1a\u8a8d\uff1a\u306b\u3093\uff1a\u3057\u305f\n1951,\u30b5\u30f3\u30d5\u30e9\u30f3\u30b7\u30b9\u30b3\u5e73\uff1a\u3078\u3044\uff1a\u548c\uff1a\u308f\uff1a\u6761\uff1a\u3067\u3046\uff1a\u7d04\uff1a\u3084\u304f\uff1a,\u6b63\uff1a\u305b\u3044\uff1a\u5f0f\uff1a\u3057\u304d\uff1a\u540d\uff1a\u3081\u3044\uff1a\u306f<\u65e5\uff1a\u306b\uff1a\u672c\uff1a\u307b\u3093\uff1a\u570b\uff1a\u3053\u304f\uff1a\u3068\u306e\u5e73\uff1a\u3078\u3044\uff1a\u548c\uff1a\u308f\uff1a\u6761\uff1a\u3067\u3046\uff1a\u7d04\uff1a\u3084\u304f\uff1a>,\u5927\uff1a\u3060\u3044\uff1a\u6771\uff1a\u3068\u3046\uff1a\u4e9e\uff1a\u3042\uff1a\u6230\uff1a\u305b\u3093\uff1a\u722d\uff1a\u3055\u3046\uff1a\u306e\u6557\uff1a\u306f\u3044\uff1a\u6230\uff1a\u305b\u3093\uff1a\u570b\uff1a\u3053\u304f\uff1a\u3067\u3042\u308a \u5360\uff1a\u305b\u3093\uff1a\u9818\uff1a\u308a\u3083\u3046\uff1a\u7d71\uff1a\u3068\u3046\uff1a\u6cbb\uff1a\u3061\uff1a\u3055\u308c\u3066\u3090\u305f\u6211\uff1a\u308f\u304c\uff1a\u570b\uff1a\u304f\u306b\uff1a\u304c \u3053\u306e\u6761\uff1a\u3067\u3046\uff1a\u7d04\uff1a\u3084\u304f\uff1a\u3092\u6279\uff1a\u3072\uff1a\u51c6\uff1a\u3058\u3085\u3093\uff1a\u3057\u305f\u9023\uff1a\u308c\u3093\uff1a\u5408\uff1a\u304c\u3075\uff1a\u570b\uff1a\u3053\u304f\uff1a\u306b\u3088\u308a\u4e3b\uff1a\u3057\u3085\uff1a\u6a29\uff1a\u3051\u3093\uff1a\u3092\u627f\uff1a\u3057\u3087\u3046\uff1a\u8a8d\uff1a\u306b\u3093\uff1a\u3055\u308c \u570b\uff1a\u3053\u304f\uff1a\u969b\uff1a\u3055\u3044\uff1a\u6cd5\uff1a\u306f\u3046\uff1a\u4e0a\uff1a\u3058\u3083\u3046\uff1a \u6211\u570b\u3068\u591a\uff1a\u304a\u307b\uff1a\u304f\u306e\u9023\u5408\u570b\u3068\u306e\u9593\uff1a\u3042\u3072\u3060\uff1a\u306e<\u6230\uff1a\u305b\u3093\uff1a\u722d\uff1a\u3055\u3046\uff1a\u72b6\uff1a\u3058\u3083\u3046\uff1a\u614b\uff1a\u305f\u3044\uff1a>\u304c\u7d42\uff1a\u3057\u3085\u3046\uff1a\u7d50\uff1a\u3051\u3064\uff1a\u3057\u305f \u3053\u306e\u6761\u7d04\u3067\u6211\u570b\u306f1875\u5e74\u306b\u5168\uff1a\u305c\u3093\uff1a\u57df\uff1a\u3044\u304d\uff1a\u3092\u9818\uff1a\u308a\u3083\u3046\uff1a\u6709\uff1a\u3044\u3046\uff1a\u3057\u305f\u5343\uff1a\u3061\uff1a\u5cf6\uff1a\u3057\u307e\uff1a\u5217\uff1a\u308c\u3063\uff1a\u5cf6\uff1a\u305f\u3046\uff1a\u3092\u653e\uff1a\u306f\u3046\uff1a\u68c4\uff1a\u304d\uff1a\u3057\u3066\u3090\u308b \u306a\u307b \u3053\u306e\u6761\u7d04\u306e\u767c\uff1a\u306f\u3063\uff1a\u52b9\uff1a\u304b\u3046\uff1a\u65e5\uff1a\u3073\uff1a\u306f1952\u5e74<\u662d\u548c27\u5e74>4\u670828\u65e5\u3067\u3042\u308a \u6211\u570b\u306e\u4e3b\uff1a\u3057\u3085\uff1a\u6a29\uff1a\u3051\u3093\uff1a\u304c\u56de\uff1a\u304b\u3044\uff1a\u5fa9\uff1a\u3075\u304f\uff1a\u3057 \u5360\uff1a\u305b\u3093\uff1a\u9818\uff1a\u308a\u3083\u3046\uff1a\u72b6\uff1a\u3058\u3083\u3046\uff1a\u614b\uff1a\u305f\u3044\uff1a\u3082\u89e3\uff1a\u304b\u3044\uff1a\u9664\uff1a\u3058\u3087\uff1a\u3055\u308c\u305f"));}),_1FJ=new T(function(){return B(_1FC(_1FI));}),_1FK=new T(function(){return B(_aj(_1Fx,_1FJ));}),_1FL=new T(function(){return B(_cU(1,2));}),_1FM=new T(function(){return B(unCStr("1871,\u65e5\u6e05\u4fee\u597d\u6761\u898f,\u3053\u306e\u6642\u306e\u4e21\u56fd\u306f \u5bfe\u7b49\u306a\u6761\u7d04\u3092\u7de0\u7d50\u3057\u305f,\u3053\u306e\u5f8c\u65e5\u6e05\u6226\u4e89\u306b\u3088\u3063\u3066 \u65e5\u6e05\u9593\u306e\u6761\u7d04\u306f \u3044\u306f\u3086\u308b<\u4e0d\u5e73\u7b49>\u306a\u3082\u306e\u3068\u306a\u3063\u305f(\u65e5\u672c\u306b\u306e\u307f\u6cbb\u5916\u6cd5\u6a29\u3092\u8a8d\u3081 \u6e05\u570b\u306b\u95a2\u7a0e\u81ea\u4e3b\u6a29\u304c\u306a\u3044)\n1875,\u6c5f\u83ef\u5cf6\u4e8b\u4ef6,\u3053\u306e\u4e8b\u4ef6\u306e\u7d50\u679c \u65e5\u9bae\u4fee\u4ea4\u6761\u898f(\u4e0d\u5e73\u7b49\u6761\u7d04\u3068\u3055\u308c\u308b)\u3092\u7de0\u7d50,\u8ecd\u8266\u96f2\u63da\u53f7\u304c\u98f2\u6599\u6c34\u78ba\u4fdd\u306e\u305f\u3081\u6c5f\u83ef\u5cf6\u306b\u63a5\u8fd1\u3057\u305f\u969b \u7a81\u5982\u540c\u5cf6\u306e\u7832\u53f0\u3088\u308a\u5f37\u70c8\u306a\u7832\u6483\u3092\u53d7\u3051\u308b>>>\u96f2\u63da\u306f\u53cd\u6483\u3057\u9678\u6226\u968a\u3092\u4e0a\u9678\u3055\u305b\u7832\u53f0\u3092\u5360\u62e0 \u6b66\u5668\u3092\u6355\u7372\u3057\u3066\u9577\u5d0e\u3078\u5e30\u7740\n1877,\u897f\u5357\u6226\u4e89,\u620a\u8fb0\u6230\u722d\u3092\u6230\u3063\u305f\u58eb\u65cf\u305f\u3061\u304c \u660e\u6cbb\u7dad\u65b0\u306b\u4e0d\u6e80\u3092\u62b1\u304d \u897f\u90f7\u9686\u76db\u3092\u62c5\u3044\u3067\u8702\u8d77,\u897f\u90f7\u9686\u76db\u3092\u7dcf\u5927\u5c06\u3068\u3059\u308b\u53cd\u4e71\u8ecd\u306f\u653f\u5e9c\u8ecd\u306b\u93ae\u5727\u3055\u308c \u897f\u90f7\u306f\u81ea\u6c7a \u4ee5\u5f8c\u58eb\u65cf\u306e\u53cd\u4e71\u306f\u9014\u7d76\u3078 \u620a\u8fb0\u6226\u4e89\u304b\u3089\u5341\u5e74\u7d9a\u3044\u3066\u3090\u305f\u52d5\u4e71\u306f\u53ce\u675f\u3057\u305f\n1882,\u58ec\u5348\u306e\u5909,\u4ff8\u7d66\u306e\u9045\u914d\u3092\u304d\u3063\u304b\u3051\u3068\u3057\u305f\u65e7\u5175\u306e\u66b4\u52d5\u3092\u5927\u9662\u541b\u304c\u717d\u52d5(\u5927\u9662\u541b\u306f\u65e7\u5b88\u6d3e \u9594\u5983\u4e00\u65cf\u306f\u958b\u5316\u6d3e),\u65e5\u97d3\u4fee\u4ea4\u4ee5\u964d \u9594\u5983\u4e00\u65cf\u306e\u958b\u5316\u6d3e\u304c\u529b\u3092\u306e\u3070\u3057 \u65e5\u672c\u306e\u8fd1\u4ee3\u5316\u306b\u5023\u306f\u3093\u3068 \u5927\u898f\u6a21\u306a\u8996\u5bdf\u56e3\u3092\u6d3e\u9063\u3057\u305f\u308a \u65e5\u672c\u304b\u3089\u5800\u672c\u793c\u9020\u3092\u62db\u3044\u3066\u65b0\u5f0f\u8ecd\u968a\u3092\u7de8\u6210\u3059\u308b\u306a\u3069\u8ecd\u653f\u6539\u9769\u3092\u65ad\u884c\u3057\u3066\u3090\u305f\u304c \u65e7\u5175\u3068\u5927\u9662\u541b\u306e\u53cd\u4e71\u306b\u3088\u308a \u591a\u6570\u306e\u65e5\u672c\u4eba\u304c\u8650\u6bba\u3055\u308c\u65e5\u672c\u516c\u4f7f\u9928\u304c\u8972\u6483\u3055\u308c\u305f(\u5800\u672c\u793c\u9020\u3082\u6bba\u3055\u308c\u308b) \u6e05\u570b\u306f\u7d04\u4e94\u5343\u306e\u5175\u3092\u304a\u304f\u308a\u4e71\u306e\u93ae\u5727\u306b\u5f53\u308b\u3068\u3068\u3082\u306b \u9996\u9b41\u3067\u3042\u308b\u5927\u9662\u541b\u3092\u6e05\u570b\u306b\u62c9\u81f4\u3057\u6291\u7559>>\u3053\u306e\u4e8b\u5909\u306e\u5584\u5f8c\u7d04\u5b9a\u3068\u3057\u3066 \u65e5\u672c\u30fb\u671d\u9bae\u9593\u306b\u6e08\u7269\u6d66\u6761\u7d04\u304c\u7d50\u3070\u308c \u671d\u9bae\u5074\u306f\u72af\u4eba\u306e\u53b3\u7f70 \u8ce0\u511f\u91d1 \u516c\u4f7f\u9928\u8b66\u5099\u306e\u305f\u3081\u4eac\u57ce\u306b\u65e5\u672c\u8ecd\u82e5\u5e72\u3092\u7f6e\u304f \u65e5\u672c\u306b\u8b1d\u7f6a\u4f7f\u3092\u6d3e\u9063\u3059\u308b\u3053\u3068\u3092\u7d04\u3057\u305f\n1885,\u5929\u6d25\u6761\u7d04,\u65e5\u672c\u304c\u652f\u63f4\u3057\u671d\u9bae\u306e\u72ec\u7acb\u3092\u3081\u3056\u3059\u52e2\u529b\u3068 \u6e05\u306e\u5f8c\u62bc\u3057\u3067\u305d\u308c\u3092\u963b\u3080\u52e2\u529b\u304c\u885d\u7a81\u3057 \u591a\u6570\u306e\u72a0\u7272\u304c\u51fa\u305f\u304c \u4e00\u61c9\u3053\u306e\u6761\u7d04\u3067\u7d50\u7740\u3059\u308b,\u65e5\u6e05\u4e21\u56fd\u306e\u671d\u9bae\u304b\u3089\u306e\u64a4\u5175 \u4eca\u5f8c\u65e5\u6e05\u4e21\u56fd\u304c\u3084\u3080\u306a\u304f\u51fa\u5175\u3059\u308b\u3068\u304d\u306f\u4e8b\u524d\u901a\u544a\u3059\u308b \u306a\u3069\u304c\u5b9a\u3081\u3089\u308c\u305f\n1894,\u65e5\u6e05\u6226\u4e89,\u671d\u9bae\u3067\u8fb2\u6c11\u4e00\u63c6\u304c\u653f\u6cbb\u66b4\u52d5\u5316(\u6771\u5b66\u515a\u306e\u4e71)\u304c\u8d77\u7206\u5264\u3068\u306a\u308b,\u8c4a\u5cf6\u6c96\u6d77\u6226\u306f \u6211\u304c\u9023\u5408\u8266\u968a\u7b2c\u4e00\u904a\u6483\u968a\u5409\u91ce\u304c\u793c\u7832\u4ea4\u63db\u306e\u7528\u610f\u3092\u3057\u3066\u8fd1\u63a5\u3057\u305f\u306e\u306b\u5c0d\u3057 \u6e05\u570b\u8ecd\u8266\u6e08\u9060\u306e\u6226\u95d8\u6e96\u5099\u304a\u3088\u3073\u767a\u7832\u3088\u308a\u306f\u3058\u307e\u308b\n1895,\u4e0b\u95a2\u6761\u7d04,\u65e5\u6e05\u6226\u4e89\u306b\u6211\u570b\u304c\u52dd\u5229\u3057\u3066\u7d50\u3070\u308c\u305f\u6761\u7d04>>>\u4e09\u56fd\u5e72\u6e09\u3092\u53d7\u3051\u308b,\u4e00 \u6e05\u570b\u306f\u671d\u9bae\u570b\u304c\u5b8c\u5168\u7121\u6b20\u306e\u72ec\u7acb\u81ea\u4e3b\u306e\u570b\u3067\u3042\u308b\u3053\u3068\u3092\u627f\u8a8d\u3059\u308b \u4e8c \u6e05\u570b\u306f\u907c\u6771\u534a\u5cf6 \u53f0\u6e7e\u5168\u5cf6\u53ca\u3073\u6f8e\u6e56\u5217\u5cf6\u3092\u6c38\u9060\u306b\u65e5\u672c\u306b\u5272\u8b72\u3059\u308b \u4e09 \u6e05\u570b\u306f\u8ecd\u8cbb\u8ce0\u511f\u91d1\u4e8c\u5104\u4e21\u3092\u652f\u6255\u3075 \u56db \u65e5\u6e05\u9593\u306e\u4e00\u5207\u306e\u6761\u7d04\u306f\u4ea4\u6230\u306e\u305f\u3081\u6d88\u6ec5\u3057\u305f\u306e\u3067\u65b0\u305f\u306b\u901a\u5546\u822a\u6d77\u6761\u7d04\u3092\u7d50\u3076 \u4e94 \u672c\u6761\u7d04\u6279\u51c6\u5f8c \u76f4\u3061\u306b\u4fd8\u865c\u3092\u8fd4\u9084\u3059\u308b \u6e05\u570b\u306f\u9001\u9084\u3055\u308c\u305f\u4fd8\u865c\u3092\u8650\u5f85\u3042\u308b\u3044\u306f\u51e6\u5211\u305b\u306c\u3053\u3068\n1899,\u7fa9\u548c\u56e3\u4e8b\u5909,\u65e5\u9732\u6226\u4e89\u306e\u539f\u56e0\u306e\u3072\u3068\u3064\u3068\u8a00\u3078\u308b,<\u6276\u6e05\u6ec5\u6d0b>\u3092\u9ad8\u5531\u3057\u3066\u6392\u5916\u904b\u52d5\u3092\u8d77\u3057 \u30ad\u30ea\u30b9\u30c8\u6559\u5f92\u6bba\u5bb3 \u6559\u4f1a \u9244\u9053 \u96fb\u7dda\u306a\u3069\u3092\u7834\u58ca\u3059\u308b \u5b97\u6559\u7684\u79d8\u5bc6\u7d50\u793e\u3067\u3042\u308b\u7fa9\u548c\u56e3\u306b\u6e05\u5175\u304c\u52a0\u306f\u308a \u5404\u570b\u516c\u4f7f\u9928\u304c\u5305\u56f2\u3055\u308c\u308b\u306b\u53ca\u3073 \u82f1\u56fd\u304b\u3089\u56db\u56de\u306b\u308f\u305f\u308a\u51fa\u5175\u8981\u8acb\u304c\u3055\u308c\u305f\u65e5\u672c\u3092\u4e3b\u529b\u3068\u3059\u308b\u516b\u30f6\u56fd\u9023\u5408\u8ecd\u304c \u5317\u4eac\u516c\u4f7f\u9928\u533a\u57df\u3092\u7fa9\u548c\u56e3\u30fb\u6e05\u5175\u306e\u5305\u56f2\u304b\u3089\u6551\u51fa \u7fa9\u548c\u56e3\u4e8b\u5909\u6700\u7d42\u8b70\u5b9a\u66f8\u306f1901\u5e74\u9023\u5408\u5341\u4e00\u30f6\u56fd\u3068\u6e05\u570b\u306e\u9593\u3067\u8abf\u5370\u3055\u308c \u6e05\u306f\u8ce0\u511f\u91d1\u306e\u652f\u6255\u3072\u306e\u4ed6 \u5404\u570b\u304c\u5341\u4e8c\u30f6\u6240\u306e\u5730\u70b9\u3092\u5360\u9818\u3059\u308b\u6a29\u5229\u3092\u627f\u8a8d \u3053\u306e\u99d0\u5175\u6a29\u306b\u3088\u3063\u3066\u6211\u570b\u306f\u8af8\u5916\u56fd\u3068\u3068\u3082\u306b\u652f\u90a3\u99d0\u5c6f\u8ecd\u3092\u7f6e\u304f\u3053\u3068\u306b\u306a\u3063\u305f(\u76e7\u6e9d\u6a4b\u3067\u4e2d\u56fd\u5074\u304b\u3089\u4e0d\u6cd5\u5c04\u6483\u3092\u53d7\u3051\u305f\u90e8\u968a\u3082 \u3053\u306e\u6761\u7d04\u306b\u3088\u308b\u99d0\u5175\u6a29\u306b\u57fa\u3065\u304d\u99d0\u5c6f\u3057\u3066\u3090\u305f)\n1900,\u30ed\u30b7\u30a2\u6e80\u6d32\u5360\u9818,\u7fa9\u548c\u56e3\u306e\u4e71\u306b\u4e57\u3058\u3066\u30ed\u30b7\u30a2\u306f\u30b7\u30d9\u30ea\u30a2\u65b9\u9762\u3068\u65c5\u9806\u304b\u3089\u5927\u5175\u3092\u6e80\u6d32\u306b\u9001\u308b>>><\u9ed2\u7adc\u6c5f\u4e0a\u306e\u60b2\u5287>\u304c\u3053\u306e\u6642\u8d77\u3053\u308b,\u30ed\u30b7\u30a2\u306f\u7fa9\u548c\u56e3\u4e8b\u5909\u93ae\u5b9a\u5f8c\u3082\u7d04\u306b\u9055\u80cc\u3057\u3066\u64a4\u5175\u305b\u305a \u3084\u3046\u3084\u304f\u9732\u6e05\u9593\u306b\u6e80\u6d32\u9084\u4ed8\u5354\u7d04\u304c\u8abf\u5370\u3055\u308c\u308b\u3082 \u4e0d\u5c65\u884c\n1902,\u65e5\u82f1\u540c\u76df,\u65e5\u9732\u6226\u4e89\u306e\u52dd\u5229\u306b\u852d\u306e\u529b\u3068\u306a\u308b,\u4e00 \u65e5\u82f1\u4e21\u56fd\u306f\u6e05\u97d3\u4e21\u56fd\u306e\u72ec\u7acb\u3092\u627f\u8a8d\u3059\u308b \u3057\u304b\u3057\u82f1\u56fd\u306f\u6e05\u56fd\u3067 \u65e5\u672c\u306f\u6e05\u97d3\u4e21\u56fd\u3067\u653f\u6cbb\u30fb\u7d4c\u6e08\u4e0a\u683c\u6bb5\u306e\u5229\u76ca\u3092\u6709\u3059\u308b\u306e\u3067 \u305d\u308c\u3089\u306e\u5229\u76ca\u304c\u7b2c\u4e09\u56fd\u306e\u4fb5\u7565\u3084\u5185\u4e71\u3067\u4fb5\u8feb\u3055\u308c\u305f\u6642\u306f\u5fc5\u8981\u306a\u63aa\u7f6e\u3092\u3068\u308b \u4e8c \u65e5\u82f1\u306e\u4e00\u65b9\u304c\u3053\u306e\u5229\u76ca\u3092\u8b77\u308b\u305f\u3081\u7b2c\u4e09\u56fd\u3068\u6230\u3075\u6642\u306f\u4ed6\u306e\u4e00\u65b9\u306f\u53b3\u6b63\u4e2d\u7acb\u3092\u5b88\u308a \u4ed6\u56fd\u304c\u6575\u5074\u306b\u53c2\u6226\u3059\u308b\u306e\u3092\u9632\u3050 \u4e09 \u4ed6\u56fd\u304c\u540c\u76df\u56fd\u3068\u306e\u4ea4\u6230\u306b\u52a0\u306f\u308b\u6642\u306f \u4ed6\u306e\u540c\u76df\u56fd\u306f \u63f4\u52a9\u3092\u8207\u3078\u308b\n1904,\u65e5\u9732\u6226\u4e89,\u6975\u6771\u306e\u30ed\u30b7\u30a2\u8ecd\u306b\u52d5\u54e1\u4ee4\u304c \u6e80\u6d32\u306b\u306f\u6212\u53b3\u4ee4\u304c\u4e0b\u3055\u308c \u5bfe\u9732\u4ea4\u6e09\u306f\u6c7a\u88c2 \u6211\u570b\u306f\u570b\u4ea4\u65ad\u7d76\u3092\u9732\u570b\u306b\u901a\u544a,\u6211\u570b\u806f\u5408\u8266\u968a\u306b\u3088\u308b \u65c5\u9806\u6e2f\u5916\u306e\u653b\u6483 \u4ec1\u5ddd\u6c96\u306b\u3066\u6575\u8266\u306e\u6483\u6c88\u304c\u3042\u308a \u6b21\u306e\u65e5\u306b\u5ba3\u6226>>>\u907c\u967d\u30fb\u6c99\u6cb3\u306e\u4f1a\u6226\u306b\u52dd\u5229 \u6d77\u4e0a\u6a29\u306e\u7372\u5f97 \u65c5\u9806\u9665\u843d \u5949\u5929\u5360\u9818\u3092\u7d4c\u3066 \u65e5\u672c\u6d77\u6d77\u6226\u306b\u3066\u30d0\u30eb\u30c1\u30c3\u30af\u8266\u968a\u3092\u5168\u6ec5\u3055\u305b \u6a3a\u592a\u5168\u5cf6\u3092\u5360\u9818\n1905,\u30dd\u30fc\u30c4\u30de\u30b9\u6761\u7d04,\u7c73\u56fd\u30cb\u30e5\u30fc\u30fb\u30cf\u30f3\u30d7\u30b7\u30e3\u30fc\u5dde \u6211\u570b\u5168\u6a29\u306f\u5916\u76f8\u5c0f\u6751\u5bff\u592a\u90ce \u9732\u570b\u5168\u6a29\u306f\u524d\u8535\u76f8\u30a6\u30a3\u30c3\u30c6,\u4e00 \u9732\u570b\u306f \u65e5\u672c\u304c\u97d3\u570b\u3067\u653f\u6cbb \u8ecd\u4e8b \u7d4c\u6e08\u4e0a\u306e\u5353\u7d76\u3057\u305f\u5229\u76ca\u3092\u6709\u3057 \u304b\u3064\u5fc5\u8981\u306a\u6307\u5c0e \u4fdd\u8b77 \u76e3\u7406\u3092\u884c\u3075\u6a29\u5229\u3092\u627f\u8a8d\u3059 \u4e8c \u4e21\u570b\u306f\u5341\u516b\u30f6\u6708\u4ee5\u5185\u306b\u6e80\u6d32\u3088\u308a\u64a4\u5175\u3059 \u4e09 \u9732\u570b\u306f\u907c\u6771\u534a\u5cf6\u79df\u501f\u6a29\u3092\u65e5\u672c\u306b\u8b72\u6e21\u3059 \u3053\u308c\u306b\u3064\u304d\u4e21\u56fd\u306f\u6e05\u570b\u306e\u627f\u8afe\u3092\u5f97\u308b\u3053\u3068 \u56db \u9732\u570b\u306f\u6771\u652f\u9244\u9053\u5357\u6e80\u6d32\u652f\u7dda(\u9577\u6625\u30fb\u65c5\u9806\u9593)\u3092\u4ed8\u5c5e\u306e\u70ad\u9271\u3068\u5171\u306b\u65e5\u672c\u306b\u8b72\u6e21\u3059 \u4e94 \u9732\u570b\u306f\u5317\u7def\u4e94\u5341\u5ea6\u4ee5\u5357\u306e\u6a3a\u592a\u3092\u65e5\u672c\u306b\u8b72\u6e21\u3059 (\u6211\u570b\u306f\u8ce0\u511f\u91d1\u8981\u6c42\u3092\u653e\u68c4)\n1910,\u65e5\u97d3\u4f75\u5408,\u674e\u6c0f\u671d\u9bae\u304c\u4e94\u767e\u6709\u4f59\u5e74\u306e\u6b74\u53f2\u3092\u9589\u3058\u308b,\u65e5\u9732\u6226\u4e89\u5f8c \u97d3\u570b\u306f\u65e5\u672c\u306b\u4fdd\u8b77\u5316\u3055\u308c\u308b\u9053\u3092\u9032\u3080\u304c \u4f0a\u85e4\u535a\u6587\u304c\u6697\u6bba\u3055\u308c\u308b\u3084 \u97d3\u570b\u4f75\u5408\u8ad6\u304c\u9ad8\u307e\u308b\n1911,\u8f9b\u4ea5\u9769\u547d,\u660e\u6cbb44\u5e74 \u6e05\u671d\u306e\u6ec5\u4ea1,\u848b\u4ecb\u77f3\u306f\u5357\u4eac\u306b\u570b\u6c11\u653f\u5e9c\u3092\u7acb\u3066 \u5f35\u4f5c\u9716\u306e\u5317\u4eac\u653f\u5e9c\u3092\u8a0e\u4f10\u3059\u308b\u305f\u3081\u5317\u3078\n1914,\u7b2c\u4e00\u6b21\u4e16\u754c\u5927\u6230,\u5927\u6b633\u5e74,\u30dc\u30b9\u30cb\u30a2\u306e\u9996\u90fd\u30b5\u30e9\u30a8\u30dc\u3067\u30aa\u30fc\u30b9\u30c8\u30ea\u30a2\u7687\u592a\u5b50\u592b\u59bb\u304c\u30bb\u30eb\u30d3\u30a2\u306e\u4e00\u9752\u5e74\u306b\u6697\u6bba\u3055\u308c\u308b\u3068 \u30aa\u30fc\u30b9\u30c8\u30ea\u30a2\u304c\u30bb\u30eb\u30d3\u30a2\u306b\u5ba3\u6226 \u30c9\u30a4\u30c4\u304c\u30ed\u30b7\u30a2\u306b\u5ba3\u6230 \u4ecf\u30fb\u82f1\u3082\u5c0d\u72ec\u5ba3\u6230\n1915,\u65e5\u83ef\u6761\u7d04,\u3044\u306f\u3086\u308b<\u4e8c\u5341\u4e00\u30f6\u6761\u306e\u8981\u6c42>,\u3082\u3068\u3082\u3068\u652f\u90a3\u3068\u4ea4\u306f\u3055\u308c\u3066\u3090\u305f\u7d04\u5b9a\u3092\u6b50\u6d32\u5217\u56fd\u306e\u5e72\u6e09\u306a\u3069\u3067\u7834\u58ca\u3055\u308c\u306a\u3044\u3084\u3046\u306b \u62d8\u675f\u529b\u306e\u3042\u308b\u6761\u7d04\u306b\u3059\u308b\u305f\u3081\u306e\u3082\u306e\u3067 \u3082\u3068\u3082\u3068\u306e\u4e03\u30f6\u6761\u306f\u5e0c\u671b\u6761\u9805\u3067\u3042\u308a \u7d50\u5c40\u6761\u7d04\u3068\u3057\u3066\u7d50\u3070\u308c\u305f\u306e\u306f\u5341\u516d\u30f6\u6761\u3067\u3042\u3063\u305f\u304c \u6761\u7d04\u3092\u7d50\u3093\u3060\u4e2d\u83ef\u6c11\u56fd\u306f \u65e5\u672c\u306b\u5f37\u8feb\u3055\u308c\u3066\u7d50\u3093\u3060\u306e\u3060\u3068\u5185\u5916\u306b\u5ba3\u4f1d\u3057 1922\u5e74\u306b\u306f\u6761\u7d04\u3068\u3057\u3066\u5341\u30f6\u6761\u304c\u6b98\u5b58\u3059\u308b\u3060\u3051\u3068\u306a\u308b\u4e2d \u4e2d\u83ef\u6c11\u56fd\u56fd\u4f1a\u306f \u6761\u7d04\u306e\u7121\u52b9\u3092\u5ba3\u8a00 \u6fc0\u70c8\u306a\u53cd\u65e5\u306e\u4e2d\u3067 \u305d\u308c\u3089\u306e\u6761\u7d04\u3082\u4e8b\u5b9f\u4e0a \u7a7a\u6587\u5316\u3057\u305f\n1917,\u77f3\u4e95\u30fb\u30e9\u30f3\u30b7\u30f3\u30b0\u5354\u5b9a,\u7b2c\u4e00\u6b21\u4e16\u754c\u5927\u6226\u4e2d\u65e5\u7c73\u9593\u306b\u7d50\u3070\u308c\u305f\u5354\u5b9a,\u7c73\u56fd\u304c\u57f7\u62d7\u306b\u9580\u6238\u958b\u653e\u4e3b\u7fa9\u3092\u5531\u9053\u3057 \u65e5\u672c\u306e\u6e80\u8499\u9032\u51fa\u3092\u63a3\u8098\u305b\u3093\u3068\u3059\u308b\u52d5\u304d\u304c\u3042\u3063\u305f\u305f\u3081 \u3042\u3089\u305f\u3081\u3066\u652f\u90a3\u306b\u304a\u3051\u308b\u65e5\u672c\u306e\u7279\u6b8a\u5730\u4f4d\u306b\u95a2\u3057\u3066 \u7c73\u56fd\u306e\u627f\u8a8d\u3092\u78ba\u4fdd\u305b\u3093\u3068\u3044\u3075\u8981\u8acb\u304c\u3042\u3063\u305f>>>\u5ba3\u8a00\u306e\u524d\u6bb5\u306f<\u65e5\u672c\u56fd\u53ca\u5317\u7c73\u5408\u8846\u56fd\u4e21\u56fd\u653f\u5e9c\u306f \u9818\u571f\u76f8\u63a5\u8fd1\u3059\u308b\u56fd\u5bb6\u306e\u9593\u306b\u306f\u7279\u6b8a\u306e\u95dc\u4fc2\u3092\u751f\u305a\u308b\u3053\u3068\u3092\u627f\u8a8d\u3059 \u5f93\u3066\u5408\u8846\u56fd\u653f\u5e9c\u306f\u65e5\u672c\u304c\u652f\u90a3\u306b\u65bc\u3066\u7279\u6b8a\u306e\u5229\u76ca\u3092\u6709\u3059\u308b\u3053\u3068\u3092\u627f\u8a8d\u3059 \u65e5\u672c\u306e\u6240\u9818\u306b\u63a5\u58cc\u3059\u308b\u5730\u65b9\u306b\u65bc\u3066\u7279\u306b\u7136\u308a\u3068\u3059>>>>\u5f8c\u6bb5\u306f<\u65e5\u672c\u56fd\u53ca\u5408\u8846\u56fd\u4e21\u56fd\u653f\u5e9c\u306f\u6beb\u3082\u652f\u90a3\u306e\u72ec\u7acb\u53c8\u306f\u9818\u571f\u4fdd\u5168\u3092\u4fb5\u5bb3\u3059\u308b\u306e\u76ee\u7684\u3092\u6709\u3059\u308b\u3082\u306e\u306b\u975e\u3056\u308b\u3053\u3068\u3092\u58f0\u660e\u3059 \u304b\u3064\u4e21\u56fd\u653f\u5e9c\u306f\u5e38\u306b\u652f\u90a3\u306b\u65bc\u3066\u6240\u8b02\u9580\u6238\u958b\u653e\u53c8\u306f\u5546\u5de5\u696d\u306b\u5c0d\u3059\u308b\u6a5f\u4f1a\u5747\u7b49\u306e\u4e3b\u7fa9\u3092\u652f\u6301\u3059\u308b\u3053\u3068\u3092\u58f0\u660e\u3059>"));}),_1FN=new T(function(){return B(_1FC(_1FM));}),_1FO=new T(function(){return B(_aj(_1Fx,_1FN));}),_1FP=function(_1FQ,_1FR){var _1FS=E(_1FQ);if(!_1FS._){return __Z;}else{var _1FT=E(_1FR);return (_1FT._==0)?__Z:new T2(1,new T2(0,new T(function(){return E(_1FS.a).a;}),_1FT.a),new T(function(){return B(_1FP(_1FS.b,_1FT.b));}));}},_1FU=new T(function(){return eval("(function(k) {localStorage.removeItem(k);})");}),_1FV=new T(function(){return B(unCStr("tail"));}),_1FW=new T(function(){return B(_rj(_1FV));}),_1FX=new T(function(){return eval("(function(k,v) {localStorage.setItem(k,v);})");}),_1FY=new T2(1,_2A,_Z),_1FZ=function(_1G0){var _1G1=E(_1G0);if(!_1G1._){return E(_1FY);}else{var _1G2=new T(function(){return B(_H(0,E(_1G1.a),new T(function(){return B(_1FZ(_1G1.b));})));});return new T2(1,_2z,_1G2);}},_1G3=function(_1G4){var _1G5=E(_1G4);if(!_1G5._){return E(_1FY);}else{var _1G6=new T(function(){var _1G7=E(_1G5.a),_1G8=new T(function(){return B(A3(_wK,_aC,new T2(1,function(_1G9){return new F(function(){return _1EI(_1G7.a,_1G9);});},new T2(1,function(_1Ga){return new F(function(){return _1EI(_1G7.b,_1Ga);});},_Z)),new T2(1,_F,new T(function(){return B(_1G3(_1G5.b));}))));});return new T2(1,_G,_1G8);});return new T2(1,_2z,_1G6);}},_1Gb=function(_1Gc){var _1Gd=E(_1Gc);if(!_1Gd._){return E(_1FY);}else{var _1Ge=new T(function(){return B(_H(0,E(_1Gd.a),new T(function(){return B(_1Gb(_1Gd.b));})));});return new T2(1,_2z,_1Ge);}},_1Gf=function(_1Gg){var _1Gh=E(_1Gg);if(!_1Gh._){return E(_1FY);}else{var _1Gi=new T(function(){var _1Gj=E(_1Gh.a),_1Gk=new T(function(){return B(A3(_wK,_aC,new T2(1,function(_1Gl){return new F(function(){return _1EI(_1Gj.a,_1Gl);});},new T2(1,function(_1Gm){return new F(function(){return _1EI(_1Gj.b,_1Gm);});},_Z)),new T2(1,_F,new T(function(){return B(_1Gf(_1Gh.b));}))));});return new T2(1,_G,_1Gk);});return new T2(1,_2z,_1Gi);}},_1Gn=new T(function(){return B(unCStr("True"));}),_1Go=new T(function(){return B(unCStr("False"));}),_1Gp=function(_1Gq){return E(E(_1Gq).b);},_1Gr=function(_1Gs,_1Gt,_1Gu){var _1Gv=new T(function(){var _1Gw=E(_1Gu);if(!_1Gw._){return __Z;}else{var _1Gx=_1Gw.b,_1Gy=E(_1Gw.a),_1Gz=E(_1Gy.a);if(_1Gz<_1Gs){var _1GA=function(_1GB){while(1){var _1GC=B((function(_1GD){var _1GE=E(_1GD);if(!_1GE._){return __Z;}else{var _1GF=_1GE.b,_1GG=E(_1GE.a);if(E(_1GG.a)<_1Gs){_1GB=_1GF;return __continue;}else{return new T2(1,_1GG,new T(function(){return B(_1GA(_1GF));}));}}})(_1GB));if(_1GC!=__continue){return _1GC;}}};return B(_1GH(B(_1GA(_1Gx))));}else{var _1GI=new T(function(){var _1GJ=function(_1GK){while(1){var _1GL=B((function(_1GM){var _1GN=E(_1GM);if(!_1GN._){return __Z;}else{var _1GO=_1GN.b,_1GP=E(_1GN.a);if(E(_1GP.a)<_1Gs){_1GK=_1GO;return __continue;}else{return new T2(1,_1GP,new T(function(){return B(_1GJ(_1GO));}));}}})(_1GK));if(_1GL!=__continue){return _1GL;}}};return B(_1GJ(_1Gx));});return B(_1Gr(_1Gz,_1Gy.b,_1GI));}}}),_1GQ=E(_1Gu);if(!_1GQ._){return new F(function(){return _x(_Z,new T2(1,new T2(0,_1Gs,_1Gt),_1Gv));});}else{var _1GR=_1GQ.b,_1GS=E(_1GQ.a),_1GT=E(_1GS.a);if(_1GT>=_1Gs){var _1GU=function(_1GV){while(1){var _1GW=B((function(_1GX){var _1GY=E(_1GX);if(!_1GY._){return __Z;}else{var _1GZ=_1GY.b,_1H0=E(_1GY.a);if(E(_1H0.a)>=_1Gs){_1GV=_1GZ;return __continue;}else{return new T2(1,_1H0,new T(function(){return B(_1GU(_1GZ));}));}}})(_1GV));if(_1GW!=__continue){return _1GW;}}};return new F(function(){return _x(B(_1GH(B(_1GU(_1GR)))),new T2(1,new T2(0,_1Gs,_1Gt),_1Gv));});}else{var _1H1=new T(function(){var _1H2=function(_1H3){while(1){var _1H4=B((function(_1H5){var _1H6=E(_1H5);if(!_1H6._){return __Z;}else{var _1H7=_1H6.b,_1H8=E(_1H6.a);if(E(_1H8.a)>=_1Gs){_1H3=_1H7;return __continue;}else{return new T2(1,_1H8,new T(function(){return B(_1H2(_1H7));}));}}})(_1H3));if(_1H4!=__continue){return _1H4;}}};return B(_1H2(_1GR));});return new F(function(){return _x(B(_1Gr(_1GT,_1GS.b,_1H1)),new T2(1,new T2(0,_1Gs,_1Gt),_1Gv));});}}},_1GH=function(_1H9){var _1Ha=E(_1H9);if(!_1Ha._){return __Z;}else{var _1Hb=_1Ha.b,_1Hc=E(_1Ha.a),_1Hd=_1Hc.a,_1He=new T(function(){var _1Hf=E(_1Hb);if(!_1Hf._){return __Z;}else{var _1Hg=_1Hf.b,_1Hh=E(_1Hf.a),_1Hi=E(_1Hh.a),_1Hj=E(_1Hd);if(_1Hi<_1Hj){var _1Hk=function(_1Hl){while(1){var _1Hm=B((function(_1Hn){var _1Ho=E(_1Hn);if(!_1Ho._){return __Z;}else{var _1Hp=_1Ho.b,_1Hq=E(_1Ho.a);if(E(_1Hq.a)<_1Hj){_1Hl=_1Hp;return __continue;}else{return new T2(1,_1Hq,new T(function(){return B(_1Hk(_1Hp));}));}}})(_1Hl));if(_1Hm!=__continue){return _1Hm;}}};return B(_1GH(B(_1Hk(_1Hg))));}else{var _1Hr=new T(function(){var _1Hs=function(_1Ht){while(1){var _1Hu=B((function(_1Hv){var _1Hw=E(_1Hv);if(!_1Hw._){return __Z;}else{var _1Hx=_1Hw.b,_1Hy=E(_1Hw.a);if(E(_1Hy.a)<_1Hj){_1Ht=_1Hx;return __continue;}else{return new T2(1,_1Hy,new T(function(){return B(_1Hs(_1Hx));}));}}})(_1Ht));if(_1Hu!=__continue){return _1Hu;}}};return B(_1Hs(_1Hg));});return B(_1Gr(_1Hi,_1Hh.b,_1Hr));}}}),_1Hz=E(_1Hb);if(!_1Hz._){return new F(function(){return _x(_Z,new T2(1,_1Hc,_1He));});}else{var _1HA=_1Hz.b,_1HB=E(_1Hz.a),_1HC=E(_1HB.a),_1HD=E(_1Hd);if(_1HC>=_1HD){var _1HE=function(_1HF){while(1){var _1HG=B((function(_1HH){var _1HI=E(_1HH);if(!_1HI._){return __Z;}else{var _1HJ=_1HI.b,_1HK=E(_1HI.a);if(E(_1HK.a)>=_1HD){_1HF=_1HJ;return __continue;}else{return new T2(1,_1HK,new T(function(){return B(_1HE(_1HJ));}));}}})(_1HF));if(_1HG!=__continue){return _1HG;}}};return new F(function(){return _x(B(_1GH(B(_1HE(_1HA)))),new T2(1,_1Hc,_1He));});}else{var _1HL=new T(function(){var _1HM=function(_1HN){while(1){var _1HO=B((function(_1HP){var _1HQ=E(_1HP);if(!_1HQ._){return __Z;}else{var _1HR=_1HQ.b,_1HS=E(_1HQ.a);if(E(_1HS.a)>=_1HD){_1HN=_1HR;return __continue;}else{return new T2(1,_1HS,new T(function(){return B(_1HM(_1HR));}));}}})(_1HN));if(_1HO!=__continue){return _1HO;}}};return B(_1HM(_1HA));});return new F(function(){return _x(B(_1Gr(_1HC,_1HB.b,_1HL)),new T2(1,_1Hc,_1He));});}}}},_1HT=function(_){return new F(function(){return jsMkStdout();});},_1HU=new T(function(){return B(_3d(_1HT));}),_1HV=new T(function(){return B(_PU("Browser.hs:84:24-56|(Right j)"));}),_1HW=function(_1HX){var _1HY=jsParseJSON(toJSStr(E(_1HX)));return (_1HY._==0)?E(_1HV):E(_1HY.a);},_1HZ=0,_1I0=function(_1I1,_1I2,_1I3,_1I4,_1I5){var _1I6=E(_1I5);if(!_1I6._){var _1I7=new T(function(){var _1I8=B(_1I0(_1I6.a,_1I6.b,_1I6.c,_1I6.d,_1I6.e));return new T2(0,_1I8.a,_1I8.b);});return new T2(0,new T(function(){return E(E(_1I7).a);}),new T(function(){return B(_78(_1I2,_1I3,_1I4,E(_1I7).b));}));}else{return new T2(0,new T2(0,_1I2,_1I3),_1I4);}},_1I9=function(_1Ia,_1Ib,_1Ic,_1Id,_1Ie){var _1If=E(_1Id);if(!_1If._){var _1Ig=new T(function(){var _1Ih=B(_1I9(_1If.a,_1If.b,_1If.c,_1If.d,_1If.e));return new T2(0,_1Ih.a,_1Ih.b);});return new T2(0,new T(function(){return E(E(_1Ig).a);}),new T(function(){return B(_6h(_1Ib,_1Ic,E(_1Ig).b,_1Ie));}));}else{return new T2(0,new T2(0,_1Ib,_1Ic),_1Ie);}},_1Ii=function(_1Ij,_1Ik){var _1Il=E(_1Ij);if(!_1Il._){var _1Im=_1Il.a,_1In=E(_1Ik);if(!_1In._){var _1Io=_1In.a;if(_1Im<=_1Io){var _1Ip=B(_1I9(_1Io,_1In.b,_1In.c,_1In.d,_1In.e)),_1Iq=E(_1Ip.a);return new F(function(){return _78(_1Iq.a,_1Iq.b,_1Il,_1Ip.b);});}else{var _1Ir=B(_1I0(_1Im,_1Il.b,_1Il.c,_1Il.d,_1Il.e)),_1Is=E(_1Ir.a);return new F(function(){return _6h(_1Is.a,_1Is.b,_1Ir.b,_1In);});}}else{return E(_1Il);}}else{return E(_1Ik);}},_1It=function(_1Iu,_1Iv){var _1Iw=E(_1Iu),_1Ix=E(_1Iv);if(!_1Ix._){var _1Iy=_1Ix.b,_1Iz=_1Ix.c,_1IA=_1Ix.d,_1IB=_1Ix.e;switch(B(_65(_1Iw,_1Iy))){case 0:return new F(function(){return _6h(_1Iy,_1Iz,B(_1It(_1Iw,_1IA)),_1IB);});break;case 1:return new F(function(){return _1Ii(_1IA,_1IB);});break;default:return new F(function(){return _78(_1Iy,_1Iz,_1IA,B(_1It(_1Iw,_1IB)));});}}else{return new T0(1);}},_1IC=function(_1ID,_1IE){while(1){var _1IF=E(_1ID);if(!_1IF._){return E(_1IE);}else{var _1IG=B(_1It(new T2(1,_1IF.a,_1sK),_1IE));_1ID=_1IF.b;_1IE=_1IG;continue;}}},_1IH=function(_1II,_1IJ,_1IK,_1IL,_1IM,_1IN,_1IO,_1IP,_1IQ,_1IR,_1IS,_1IT,_1IU,_1IV,_1IW,_1IX,_1IY,_1IZ,_1J0,_1J1,_1J2,_1J3,_1J4,_1J5,_1J6,_1J7,_1J8,_1J9,_1Ja,_1Jb,_1Jc,_1Jd,_1Je,_1Jf,_1Jg,_1Jh,_1Ji,_1Jj,_1Jk,_1Jl,_1Jm,_1Jn,_1Jo,_1Jp,_1Jq,_1Jr,_1Js,_1Jt,_){var _1Ju={_:0,a:E(_1Jk),b:E(_1Jl),c:E(_1Jm),d:E(_1Jn),e:E(_1Jo),f:E(_1Jp),g:E(_1Jq),h:E(_1Jr),i:E(_1Js)},_1Jv=new T2(0,_1Jh,_1Ji),_1Jw=new T2(0,_1J5,_1J6),_1Jx=new T2(0,_1IY,_1IZ),_1Jy={_:0,a:E(_1IN),b:E(_1IO),c:E(_1IP),d:_1IQ,e:_1IR,f:_1IS,g:E(_1IT),h:_1IU,i:E(_1IV),j:E(_1IW),k:E(_1IX)},_1Jz={_:0,a:E(_1Jy),b:E(_1Jx),c:E(_1J0),d:E(_1J1),e:E(_1J2),f:E(_1J3),g:E(_1J4),h:E(_1Jw),i:_1J7,j:_1J8,k:_1J9,l:_1Ja,m:E(_1Jb),n:_1Jc,o:E(_1Jd),p:E(_1Je),q:_1Jf,r:E(_1Jg),s:E(_1Jv),t:_1Jj,u:E(_1Ju),v:E(_1Jt)};if(!E(_1Jp)){if(!E(_1Jl)){var _1JA=function(_1JB){if(!E(_1Jn)){if(!E(_1Jr)){return _1Jz;}else{var _1JC=function(_,_1JD,_1JE,_1JF,_1JG,_1JH,_1JI,_1JJ,_1JK,_1JL,_1JM,_1JN,_1JO,_1JP,_1JQ,_1JR,_1JS,_1JT,_1JU,_1JV,_1JW,_1JX,_1JY,_1JZ,_1K0,_1K1,_1K2,_1K3,_1K4,_1K5,_1K6,_1K7,_1K8,_1K9){var _1Ka=function(_){var _1Kb=function(_){var _1Kc=function(_){var _1Kd=B(_1E1(_1HU,new T2(1,_aI,new T(function(){return B(_cp(_1JL,_1EX));})),_)),_1Ke=function(_){var _1Kf=B(_1E1(_1HU,B(_H(0,_1Ja,_Z)),_)),_1Kg=B(_1E1(_1HU,B(_2C(_1EL,_1JJ,_Z)),_)),_1Kh=function(_){var _1Ki=B(_1bh(_1Ew,_1JK,_)),_1Kj=_1Ki,_1Kk=E(_1II),_1Kl=_1Kk.a,_1Km=_1Kk.b,_1Kn=new T(function(){return B(_1tA(E(_1IM)));}),_1Ko=new T(function(){var _1Kp=E(_1Kn),_1Kq=E(_1JD),_1Kr=_1Kq.a,_1Ks=_1Kq.b,_1Kt=function(_1Ku,_1Kv){var _1Kw=E(_1Ku),_1Kx=E(_1Kv),_1Ky=E(_1Kr);if(_1Kw<=_1Ky){if(_1Ky<=_1Kw){var _1Kz=E(_1Ks);if(_1Kx<=_1Kz){if(_1Kz<=_1Kx){var _1KA=4;}else{var _1KA=0;}var _1KB=_1KA;}else{var _1KB=1;}var _1KC=_1KB;}else{var _1KC=2;}var _1KD=_1KC;}else{var _1KD=3;}var _1KE=function(_1KF,_1KG,_1KH,_1KI,_1KJ,_1KK,_1KL,_1KM,_1KN,_1KO){switch(E(_1KD)){case 0:if(!E(_1JF)){var _1KP=new T2(0,_1K5,_1K6);}else{var _1KP=new T2(0,_1K5,_1F1);}var _1KQ=_1KP;break;case 1:if(E(_1JF)==1){var _1KR=new T2(0,_1K5,_1K6);}else{var _1KR=new T2(0,_1K5,_1HZ);}var _1KQ=_1KR;break;case 2:if(E(_1JF)==2){var _1KS=new T2(0,_1K5,_1K6);}else{var _1KS=new T2(0,_1K5,_1Ev);}var _1KQ=_1KS;break;case 3:if(E(_1JF)==3){var _1KT=new T2(0,_1K5,_1K6);}else{var _1KT=new T2(0,_1K5,_1Eu);}var _1KQ=_1KT;break;default:if(E(_1JF)==4){var _1KU=new T2(0,_1K5,_1K6);}else{var _1KU=new T2(0,_1K5,_1HZ);}var _1KQ=_1KU;}var _1KV=B(_1ql(_1HZ,_1KM,_1JR,{_:0,a:E(_1KF),b:E(_1KG),c:E(_1KH),d:_1KI,e:_1KJ,f:_1KK,g:E(_1KL),h:E(E(_1Kj).b),i:E(_1KM),j:E(_1KN),k:E(_1KO)},_1JO,_1JP,_1JQ,_1JR,_1JS,_1JT,_1JU,_1JV,_1JW,_1JX,_1JY,_1JZ,_1K0,_1K1,_1K2,_1K3,_1K4,_1KQ,_1K7,_1K8,_1K9)),_1KW=_1KV.a,_1KX=_1KV.b,_1KY=_1KV.c,_1KZ=_1KV.d,_1L0=_1KV.e,_1L1=_1KV.f,_1L2=_1KV.g,_1L3=_1KV.h,_1L4=_1KV.i,_1L5=_1KV.j,_1L6=_1KV.k,_1L7=_1KV.l,_1L8=_1KV.m,_1L9=_1KV.n,_1La=_1KV.o,_1Lb=_1KV.q,_1Lc=_1KV.r,_1Ld=_1KV.s,_1Le=_1KV.t,_1Lf=_1KV.u,_1Lg=_1KV.v,_1Lh=E(_1KV.p);if(!_1Lh._){return {_:0,a:E(_1KW),b:E(_1KX),c:E(_1KY),d:E(_1KZ),e:E(_1L0),f:E(_1L1),g:E(_1L2),h:E(_1L3),i:_1L4,j:_1L5,k:_1L6,l:_1L7,m:E(_1L8),n:_1L9,o:E(_1La),p:E(_Z),q:_1Lb,r:E(_1Lc),s:E(_1Ld),t:_1Le,u:E(_1Lf),v:E(_1Lg)};}else{var _1Li=B(_qy(_1KM,0))-2|0,_1Lj=function(_1Lk){var _1Ll=E(_1KW);return {_:0,a:E({_:0,a:E(_1Ll.a),b:E(_1Ll.b),c:E(_1Ll.c),d:_1Ll.d,e:_1Ll.e,f:_1Ll.f,g:E(_Z),h:_1Ll.h,i:E(_1Ll.i),j:E(_1Ll.j),k:E(_1Ll.k)}),b:E(_1KX),c:E(_1KY),d:E(B(_x(B(_0(_Z,B(_1IC(B(_aj(_1Gp,_1Lh)),B(_9T(_1KZ)))))),new T(function(){return B(_aj(_1Dw,_1Lh));},1)))),e:E(_1L0),f:E(_1L1),g:E(_1L2),h:E(_1L3),i:_1L4,j:_1L5,k:_1L6,l:_1L7,m:E(_1L8),n:_1L9,o:E(_1La),p:E(_Z),q:_1Lb,r:E(B(_x(_1Lc,new T2(1,_1Lb,_Z)))),s:E(_1Ld),t:_1Le,u:E(_1Lf),v:E(_1Lg)};};if(_1Li>0){if(!B(_vl(B(_1Dd(_1Li,_1KM)),_1Et))){return {_:0,a:E(_1KW),b:E(_1KX),c:E(_1KY),d:E(_1KZ),e:E(_1L0),f:E(_1L1),g:E(_1L2),h:E(_1L3),i:_1L4,j:_1L5,k:_1L6,l:_1L7,m:E(_1L8),n:_1L9,o:E(_1La),p:E(_1Lh),q:_1Lb,r:E(_1Lc),s:E(_1Ld),t:_1Le,u:E(_1Lf),v:E(_1Lg)};}else{return new F(function(){return _1Lj(_);});}}else{if(!B(_vl(_1KM,_1Et))){return {_:0,a:E(_1KW),b:E(_1KX),c:E(_1KY),d:E(_1KZ),e:E(_1L0),f:E(_1L1),g:E(_1L2),h:E(_1L3),i:_1L4,j:_1L5,k:_1L6,l:_1L7,m:E(_1L8),n:_1L9,o:E(_1La),p:E(_1Lh),q:_1Lb,r:E(_1Lc),s:E(_1Ld),t:_1Le,u:E(_1Lf),v:E(_1Lg)};}else{return new F(function(){return _1Lj(_);});}}}};if(E(_1Kp)==32){var _1Lm=B(_1zt(_1Kw,_1Kx,_1Ky,_1Ks,_1JE,_1KD,_1JG,_1JH,_1JI,_1JJ,_1JK,_1JL,_1JM,_1JN)),_1Ln=E(_1Lm.a),_1Lo=B(_1CO(_1Ln.a,E(_1Ln.b),_1Lm.b,_1Lm.c,_1Lm.d,_1Lm.e,_1Lm.f,_1Lm.g,_1Lm.h,_1Lm.i,_1Lm.j,_1Lm.k));return new F(function(){return _1KE(_1Lo.a,_1Lo.b,_1Lo.c,_1Lo.d,_1Lo.e,_1Lo.f,_1Lo.g,_1Lo.i,_1Lo.j,_1Lo.k);});}else{var _1Lp=B(_1zt(_1Kw,_1Kx,_1Ky,_1Ks,_1JE,_1KD,_1JG,_1JH,_1JI,_1JJ,_1JK,_1JL,_1JM,_1JN));return new F(function(){return _1KE(_1Lp.a,_1Lp.b,_1Lp.c,_1Lp.d,_1Lp.e,_1Lp.f,_1Lp.g,_1Lp.i,_1Lp.j,_1Lp.k);});}};switch(E(_1Kp)){case 72:var _1Lq=E(_1Ks);if(0<=(_1Lq-1|0)){return B(_1Kt(_1Kr,_1Lq-1|0));}else{return B(_1Kt(_1Kr,_1Lq));}break;case 75:var _1Lr=E(_1Kr);if(0<=(_1Lr-1|0)){return B(_1Kt(_1Lr-1|0,_1Ks));}else{return B(_1Kt(_1Lr,_1Ks));}break;case 77:var _1Ls=E(_1Kr);if(E(_1IY)!=(_1Ls+1|0)){return B(_1Kt(_1Ls+1|0,_1Ks));}else{return B(_1Kt(_1Ls,_1Ks));}break;case 80:var _1Lt=E(_1Ks);if(E(_1IZ)!=(_1Lt+1|0)){return B(_1Kt(_1Kr,_1Lt+1|0));}else{return B(_1Kt(_1Kr,_1Lt));}break;case 104:var _1Lu=E(_1Kr);if(0<=(_1Lu-1|0)){return B(_1Kt(_1Lu-1|0,_1Ks));}else{return B(_1Kt(_1Lu,_1Ks));}break;case 106:var _1Lv=E(_1Ks);if(E(_1IZ)!=(_1Lv+1|0)){return B(_1Kt(_1Kr,_1Lv+1|0));}else{return B(_1Kt(_1Kr,_1Lv));}break;case 107:var _1Lw=E(_1Ks);if(0<=(_1Lw-1|0)){return B(_1Kt(_1Kr,_1Lw-1|0));}else{return B(_1Kt(_1Kr,_1Lw));}break;case 108:var _1Lx=E(_1Kr);if(E(_1IY)!=(_1Lx+1|0)){return B(_1Kt(_1Lx+1|0,_1Ks));}else{return B(_1Kt(_1Lx,_1Ks));}break;default:return B(_1Kt(_1Kr,_1Ks));}}),_1Ly=B(_1bL(_1Kl,_1Km,_1IJ,_1IK,_1IL,_1Ko,_)),_1Lz=_1Ly,_1LA=E(_1Kn),_1LB=function(_,_1LC){var _1LD=function(_1LE){var _1LF=B(_1E1(_1HU,B(_cv(_1LC)),_)),_1LG=E(_1Lz),_1LH=_1LG.d,_1LI=_1LG.e,_1LJ=_1LG.f,_1LK=_1LG.g,_1LL=_1LG.i,_1LM=_1LG.j,_1LN=_1LG.k,_1LO=_1LG.l,_1LP=_1LG.m,_1LQ=_1LG.n,_1LR=_1LG.o,_1LS=_1LG.p,_1LT=_1LG.q,_1LU=_1LG.r,_1LV=_1LG.t,_1LW=_1LG.v,_1LX=E(_1LG.u),_1LY=_1LX.a,_1LZ=_1LX.d,_1M0=_1LX.e,_1M1=_1LX.f,_1M2=_1LX.g,_1M3=_1LX.h,_1M4=_1LX.i,_1M5=E(_1LG.a),_1M6=_1M5.c,_1M7=_1M5.f,_1M8=_1M5.g,_1M9=_1M5.h,_1Ma=E(_1LG.h),_1Mb=E(_1LG.s),_1Mc=function(_1Md){var _1Me=function(_1Mf){if(_1Mf!=E(_1Em)){var _1Mg=B(_aW(_1m0,_1Mf)),_1Mh=_1Mg.a,_1Mi=E(_1Mg.b),_1Mj=B(_1fX(_1Mh,_1Mi,new T(function(){return B(_aW(_1o5,_1Mf));})));return new F(function(){return _1IH(_1Kk,_1IJ,_1IK,_1IL,_1El,B(_aW(_1mb,_1Mf)),_1Mj,_1M6,B(_aW(_1mo,_1Mf)),32,_1Mf,_1M8,_1M9,B(_x(_1M5.i,new T2(1,_1Ek,new T(function(){return B(_H(0,_1M7,_Z));})))),B(_1DF(_1Ej,_1Mj)),_B2,_1Mh,_1Mi,_Z,_1LH,_1LI,_1LJ,_1LK,_1Ma.a,_1Ma.b,_1LL,_1LM,_1LN, -1,_1LP,_1LQ,_1LR,_1LS,_1LT,_1LU,_1Mb.a,_1Mb.b,_1LV,_B2,_B2,_B2,_1LZ,_1M0,_1M1,_1M2,_1M3,_1M4,_1LW,_);});}else{var _1Mk=__app1(E(_rn),_1Km),_1Ml=B(A2(_ro,_1Kl,_)),_1Mm=B(A(_qT,[_1Kl,_n8,_1Ef,_1Eh,_1Eg,_])),_1Mn=B(A(_qT,[_1Kl,_n8,_1Ef,_1Ee,_1F2,_])),_1Mo=B(A(_qT,[_1Kl,_n8,_1F1,_1F0,_1EZ,_]));return new T(function(){return {_:0,a:E({_:0,a:E(_1m2),b:E(_1EY),c:E(_1M6),d:E(_1EC),e:32,f:0,g:E(_1M8),h:_1M9,i:E(_Z),j:E(_1M5.j),k:E(_B2)}),b:E(_1lN),c:E(_1LG.c),d:E(_1LH),e:E(_1LI),f:E(_1LJ),g:E(_1LK),h:E(_1Ma),i:_1LL,j:_1LM,k:_1LN,l:_1LO,m:E(_1LP),n:_1LQ,o:E(_1LR),p:E(_1LS),q:_1LT,r:E(_1LU),s:E(_1Mb),t:_1LV,u:E({_:0,a:E(_1LY),b:E(_B3),c:E(_B2),d:E(_1LZ),e:E(_1M0),f:E(_1M1),g:E(_1M2),h:E(_1M3),i:E(_1M4)}),v:E(_1LW)};});}};if(_1LO>=0){return new F(function(){return _1Me(_1LO);});}else{return new F(function(){return _1Me(_1M7+1|0);});}};if(!E(_1LY)){if(E(_1LA)==110){return new F(function(){return _1Mc(_);});}else{return _1LG;}}else{return new F(function(){return _1Mc(_);});}};if(E(_1LA)==114){if(!B(_ae(_1LC,_1En))){var _1Mp=E(_1LC);if(!_1Mp._){return _1Lz;}else{var _1Mq=_1Mp.b;return new T(function(){var _1Mr=E(_1Lz),_1Ms=E(_1Mr.a),_1Mt=E(_1Mp.a),_1Mu=E(_1Mt);if(_1Mu==34){var _1Mv=B(_Yg(_1Mt,_1Mq));if(!_1Mv._){var _1Mw=E(_1FW);}else{var _1Mx=E(_1Mv.b);if(!_1Mx._){var _1My=E(_1EG);}else{var _1Mz=_1Mx.a,_1MA=E(_1Mx.b);if(!_1MA._){var _1MB=new T2(1,new T2(1,_1Mz,_Z),_Z);}else{var _1MC=E(_1Mz),_1MD=new T(function(){var _1ME=B(_LC(126,_1MA.a,_1MA.b));return new T2(0,_1ME.a,_1ME.b);});if(E(_1MC)==126){var _1MF=new T2(1,_Z,new T2(1,new T(function(){return E(E(_1MD).a);}),new T(function(){return E(E(_1MD).b);})));}else{var _1MF=new T2(1,new T2(1,_1MC,new T(function(){return E(E(_1MD).a);})),new T(function(){return E(E(_1MD).b);}));}var _1MB=_1MF;}var _1My=_1MB;}var _1Mw=_1My;}var _1MG=_1Mw;}else{var _1MH=E(_1Mq);if(!_1MH._){var _1MI=new T2(1,new T2(1,_1Mt,_Z),_Z);}else{var _1MJ=new T(function(){var _1MK=B(_LC(126,_1MH.a,_1MH.b));return new T2(0,_1MK.a,_1MK.b);});if(E(_1Mu)==126){var _1ML=new T2(1,_Z,new T2(1,new T(function(){return E(E(_1MJ).a);}),new T(function(){return E(E(_1MJ).b);})));}else{var _1ML=new T2(1,new T2(1,_1Mt,new T(function(){return E(E(_1MJ).a);})),new T(function(){return E(E(_1MJ).b);}));}var _1MI=_1ML;}var _1MG=_1MI;}var _1MM=B(_KK(B(_x7(_1Eo,new T(function(){return B(_NR(_1MG));})))));if(!_1MM._){return E(_1Ec);}else{if(!E(_1MM.b)._){var _1MN=E(_1MM.a),_1MO=B(_aW(_1m0,_1MN)),_1MP=B(_aW(_1MG,1));if(!_1MP._){var _1MQ=__Z;}else{var _1MR=E(_1MP.b);if(!_1MR._){var _1MS=__Z;}else{var _1MT=E(_1MP.a),_1MU=new T(function(){var _1MV=B(_LC(44,_1MR.a,_1MR.b));return new T2(0,_1MV.a,_1MV.b);});if(E(_1MT)==44){var _1MW=B(_16e(_Z,new T(function(){return E(E(_1MU).a);}),new T(function(){return E(E(_1MU).b);})));}else{var _1MW=B(_16i(new T2(1,_1MT,new T(function(){return E(E(_1MU).a);})),new T(function(){return E(E(_1MU).b);})));}var _1MS=_1MW;}var _1MQ=_1MS;}var _1MX=B(_aW(_1MG,2));if(!_1MX._){var _1MY=E(_1EH);}else{var _1MZ=_1MX.a,_1N0=E(_1MX.b);if(!_1N0._){var _1N1=B(_aj(_1Ez,new T2(1,new T2(1,_1MZ,_Z),_Z)));}else{var _1N2=E(_1MZ),_1N3=new T(function(){var _1N4=B(_LC(44,_1N0.a,_1N0.b));return new T2(0,_1N4.a,_1N4.b);});if(E(_1N2)==44){var _1N5=B(_aj(_1Ez,new T2(1,_Z,new T2(1,new T(function(){return E(E(_1N3).a);}),new T(function(){return E(E(_1N3).b);})))));}else{var _1N5=B(_aj(_1Ez,new T2(1,new T2(1,_1N2,new T(function(){return E(E(_1N3).a);})),new T(function(){return E(E(_1N3).b);}))));}var _1N1=_1N5;}var _1MY=_1N1;}return {_:0,a:E({_:0,a:E(B(_aW(_1mb,_1MN))),b:E(B(_1fX(_1MO.a,E(_1MO.b),new T(function(){return B(_aW(_1o5,_1MN));})))),c:E(_1Ms.c),d:B(_aW(_1mo,_1MN)),e:32,f:_1MN,g:E(_1Ms.g),h:_1Ms.h,i:E(_1Ms.i),j:E(_1Ms.j),k:E(_1Ms.k)}),b:E(_1MO),c:E(_1Mr.c),d:E(_1Mr.d),e:E(_1MQ),f:E(_1MY),g:E(_1Mr.g),h:E(_1Mr.h),i:_1Mr.i,j:_1Mr.j,k:_1Mr.k,l:_1Mr.l,m:E(_1Mr.m),n:_1Mr.n,o:E(_1Mr.o),p:E(_1Mr.p),q:_1Mr.q,r:E(_1Mr.r),s:E(_1Mr.s),t:_1Mr.t,u:E(_1Mr.u),v:E(_1Mr.v)};}else{return E(_1Ed);}}});}}else{return new F(function(){return _1LD(_);});}}else{return new F(function(){return _1LD(_);});}};switch(E(_1LA)){case 100:var _1N6=__app1(E(_1FU),toJSStr(E(_1Er)));return new F(function(){return _1LB(_,_1E9);});break;case 114:var _1N7=B(_16t(_aB,toJSStr(E(_1Er)),_));return new F(function(){return _1LB(_,new T(function(){var _1N8=E(_1N7);if(!_1N8._){return E(_1Ea);}else{return fromJSStr(B(_1sA(_1N8.a)));}}));});break;case 115:var _1N9=new T(function(){var _1Na=new T(function(){var _1Nb=new T(function(){var _1Nc=B(_aj(_aG,_1J3));if(!_1Nc._){return __Z;}else{return B(_1E6(new T2(1,_1Nc.a,new T(function(){return B(_1F3(_1Ep,_1Nc.b));}))));}}),_1Nd=new T(function(){var _1Ne=function(_1Nf){var _1Ng=E(_1Nf);if(!_1Ng._){return __Z;}else{var _1Nh=E(_1Ng.a);return new T2(1,_1Nh.a,new T2(1,_1Nh.b,new T(function(){return B(_1Ne(_1Ng.b));})));}},_1Ni=B(_1Ne(_1J2));if(!_1Ni._){return __Z;}else{return B(_1E6(new T2(1,_1Ni.a,new T(function(){return B(_1F3(_1Ep,_1Ni.b));}))));}});return B(_1F3(_1Eq,new T2(1,_1Nd,new T2(1,_1Nb,_Z))));});return B(_x(B(_1E6(new T2(1,new T(function(){return B(_H(0,_1IS,_Z));}),_1Na))),_1EF));}),_1Nj=__app2(E(_1FX),toJSStr(E(_1Er)),B(_1sA(B(_1HW(B(unAppCStr("\"",_1N9)))))));return new F(function(){return _1LB(_,_1Eb);});break;default:return new F(function(){return _1LB(_,_1Es);});}},_1Nk=E(_1Jg);if(!_1Nk._){var _1Nl=B(_1E1(_1HU,_1EE,_));return new F(function(){return _1Kh(_);});}else{var _1Nm=new T(function(){return B(_H(0,E(_1Nk.a),new T(function(){return B(_1FZ(_1Nk.b));})));}),_1Nn=B(_1E1(_1HU,new T2(1,_2B,_1Nm),_));return new F(function(){return _1Kh(_);});}};if(!E(_1JN)){var _1No=B(_1E1(_1HU,_1Go,_));return new F(function(){return _1Ke(_);});}else{var _1Np=B(_1E1(_1HU,_1Gn,_));return new F(function(){return _1Ke(_);});}},_1Nq=E(_1J4);if(!_1Nq._){var _1Nr=B(_1E1(_1HU,_1EE,_));return new F(function(){return _1Kc(_);});}else{var _1Ns=new T(function(){var _1Nt=E(_1Nq.a),_1Nu=new T(function(){return B(A3(_wK,_aC,new T2(1,function(_1Nv){return new F(function(){return _1EI(_1Nt.a,_1Nv);});},new T2(1,function(_1Nw){return new F(function(){return _1EI(_1Nt.b,_1Nw);});},_Z)),new T2(1,_F,new T(function(){return B(_1G3(_1Nq.b));}))));});return new T2(1,_G,_1Nu);}),_1Nx=B(_1E1(_1HU,new T2(1,_2B,_1Ns),_));return new F(function(){return _1Kc(_);});}},_1Ny=E(_1J3);if(!_1Ny._){var _1Nz=B(_1E1(_1HU,_1EE,_));return new F(function(){return _1Kb(_);});}else{var _1NA=new T(function(){return B(_H(0,E(_1Ny.a),new T(function(){return B(_1Gb(_1Ny.b));})));}),_1NB=B(_1E1(_1HU,new T2(1,_2B,_1NA),_));return new F(function(){return _1Kb(_);});}},_1NC=E(_1J2);if(!_1NC._){var _1ND=B(_1E1(_1HU,_1EE,_));return new F(function(){return _1Ka(_);});}else{var _1NE=new T(function(){var _1NF=E(_1NC.a),_1NG=new T(function(){return B(A3(_wK,_aC,new T2(1,function(_1NH){return new F(function(){return _1EI(_1NF.a,_1NH);});},new T2(1,function(_1NI){return new F(function(){return _1EI(_1NF.b,_1NI);});},_Z)),new T2(1,_F,new T(function(){return B(_1Gf(_1NC.b));}))));});return new T2(1,_G,_1NG);}),_1NJ=B(_1E1(_1HU,new T2(1,_2B,_1NE),_));return new F(function(){return _1Ka(_);});}},_1NK=E(_1Jd);if(!_1NK._){return new F(function(){return _1JC(_,_1IN,_1IO,_1IP,_1IQ,_1IR,_1IS,_1IT,_1IU,_1IV,_1IW,_1IX,_1Jx,_1J0,_1J1,_1J2,_1J3,_1J4,_1Jw,_1J7,_1J8,_1J9,_1Ja,_1Jb,_1Jc,_Z,_1Je,_1Jf,_1Jg,_1Jh,_1Ji,_1Jj,_1Ju,_1Jt);});}else{var _1NL=E(_1NK.b);if(!_1NL._){return new F(function(){return _1JC(_,_1IN,_1IO,_1IP,_1IQ,_1IR,_1IS,_1IT,_1IU,_1IV,_1IW,_1IX,_1Jx,_1J0,_1J1,_1J2,_1J3,_1J4,_1Jw,_1J7,_1J8,_1J9,_1Ja,_1Jb,_1Jc,_Z,_1Je,_1Jf,_1Jg,_1Jh,_1Ji,_1Jj,_1Ju,_1Jt);});}else{var _1NM=E(_1NL.b);if(!_1NM._){return new F(function(){return _1JC(_,_1IN,_1IO,_1IP,_1IQ,_1IR,_1IS,_1IT,_1IU,_1IV,_1IW,_1IX,_1Jx,_1J0,_1J1,_1J2,_1J3,_1J4,_1Jw,_1J7,_1J8,_1J9,_1Ja,_1Jb,_1Jc,_Z,_1Je,_1Jf,_1Jg,_1Jh,_1Ji,_1Jj,_1Ju,_1Jt);});}else{var _1NN=_1NM.a,_1NO=E(_1NM.b);if(!_1NO._){return new F(function(){return _1JC(_,_1IN,_1IO,_1IP,_1IQ,_1IR,_1IS,_1IT,_1IU,_1IV,_1IW,_1IX,_1Jx,_1J0,_1J1,_1J2,_1J3,_1J4,_1Jw,_1J7,_1J8,_1J9,_1Ja,_1Jb,_1Jc,_Z,_1Je,_1Jf,_1Jg,_1Jh,_1Ji,_1Jj,_1Ju,_1Jt);});}else{if(!E(_1NO.b)._){var _1NP=B(_1ds(B(_qy(_1NN,0)),_1IU,new T(function(){var _1NQ=B(_KK(B(_x7(_1Eo,_1NK.a))));if(!_1NQ._){return E(_1FK);}else{if(!E(_1NQ.b)._){if(E(_1NQ.a)==2){return E(_1FO);}else{return E(_1FK);}}else{return E(_1FK);}}}),_)),_1NR=E(_1NP),_1NS=_1NR.a,_1NT=new T(function(){var _1NU=new T(function(){return B(_aj(function(_1NV){var _1NW=B(_wS(_3S,_1NV,B(_KW(_1Ey,_1NN))));return (_1NW._==0)?E(_1Ei):E(_1NW.a);},B(_aj(_1Gp,B(_1GH(B(_1FP(_1NS,_1FL))))))));}),_1NX=B(_KW(_1NS,_1NN)),_1NY=B(_YG(B(unAppCStr("e.==.m1:",_1NO.a)),{_:0,a:E(_1IN),b:E(_1IO),c:E(_1IP),d:_1IQ,e:_1IR,f:_1IS,g:E(B(_x(_1IT,new T2(1,new T2(0,new T2(0,_1NL.a,_1Ex),_1IS),new T2(1,new T2(0,new T2(0,_1NU,_1Ex),_1IS),_Z))))),h:E(_1NR.b),i:E(_1IV),j:E(_1IW),k:E(_1IX)},_1Jx,_1J0,B(_x(B(_0(_Z,B(_1IC(_1NN,B(_9T(_1J1)))))),new T(function(){return B(_aj(_1DB,_1NX));},1))),_1J2,_1J3,_1J4,_1Jw,_1J7,_1J8,_1J9,_1Ja,_1Jb,_1Jc,_Z,E(_1NX),0,_1Jg,_1Jv,_1Jj,_1Ju,_1Jt)),_1NZ=B(_1sL(_1NN,_1NY.a,_1NY.b,_1NY.c,_1NY.d,_1NY.e,_1NY.f,_1NY.g,_1NY.h,_1NY.i,_1NY.j,_1NY.k,_1NY.l,_1NY.m,_1NY.n,_1NY.o,_1NY.p,_1NY.q,_1NY.r,_1NY.s,_1NY.t,_1NY.u,_1NY.v));return {_:0,a:E(_1NZ.a),b:E(_1NZ.b),c:E(_1NZ.c),d:E(_1NZ.d),e:E(_1NZ.e),f:E(_1NZ.f),g:E(_1NZ.g),h:E(_1NZ.h),i:_1NZ.i,j:_1NZ.j,k:_1NZ.k,l:_1NZ.l,m:E(_1NZ.m),n:_1NZ.n,o:E(_1NZ.o),p:E(_1NZ.p),q:_1NZ.q,r:E(_1NZ.r),s:E(_1NZ.s),t:_1NZ.t,u:E(_1NZ.u),v:E(_1NZ.v)};}),_1O0=function(_){var _1O1=function(_){var _1O2=function(_){var _1O3=new T(function(){var _1O4=E(E(_1NT).a);return new T6(0,_1O4,_1O4.a,_1O4.g,_1O4.h,_1O4.i,_1O4.k);}),_1O5=B(_1E1(_1HU,new T2(1,_aI,new T(function(){return B(_cp(E(_1O3).e,_1EX));})),_)),_1O6=E(_1O3),_1O7=_1O6.a,_1O8=function(_){var _1O9=B(_1E1(_1HU,B(_H(0,_1Ja,_Z)),_)),_1Oa=B(_1E1(_1HU,B(_2C(_1EL,_1O6.c,_Z)),_)),_1Ob=function(_){var _1Oc=B(_1bh(_1Ew,_1O6.d,_)),_1Od=E(_1Oc).b,_1Oe=E(_1II),_1Of=_1Oe.a,_1Og=_1Oe.b,_1Oh=new T(function(){return B(_1tA(E(_1IM)));}),_1Oi=new T(function(){var _1Oj=E(_1NT),_1Ok=_1Oj.b,_1Ol=_1Oj.c,_1Om=_1Oj.d,_1On=_1Oj.e,_1Oo=_1Oj.f,_1Op=_1Oj.g,_1Oq=_1Oj.h,_1Or=_1Oj.i,_1Os=_1Oj.j,_1Ot=_1Oj.k,_1Ou=_1Oj.l,_1Ov=_1Oj.m,_1Ow=_1Oj.n,_1Ox=_1Oj.o,_1Oy=_1Oj.p,_1Oz=_1Oj.q,_1OA=_1Oj.r,_1OB=_1Oj.t,_1OC=_1Oj.u,_1OD=_1Oj.v,_1OE=E(_1Oj.s),_1OF=_1OE.a,_1OG=_1OE.b,_1OH=E(_1Oh),_1OI=E(_1O6.b),_1OJ=_1OI.a,_1OK=_1OI.b,_1OL=function(_1OM,_1ON){var _1OO=E(_1OM),_1OP=E(_1OJ);if(_1OO<=_1OP){if(_1OP<=_1OO){var _1OQ=E(_1OK);if(_1ON<=_1OQ){if(_1OQ<=_1ON){var _1OR=4;}else{var _1OR=0;}var _1OS=_1OR;}else{var _1OS=1;}var _1OT=_1OS;}else{var _1OT=2;}var _1OU=_1OT;}else{var _1OU=3;}var _1OV=function(_1OW,_1OX,_1OY,_1OZ,_1P0,_1P1,_1P2,_1P3,_1P4,_1P5){switch(E(_1OU)){case 0:if(!E(E(_1O7).c)){var _1P6=new T2(0,_1OF,_1OG);}else{var _1P6=new T2(0,_1OF,_1F1);}var _1P7=_1P6;break;case 1:if(E(E(_1O7).c)==1){var _1P8=new T2(0,_1OF,_1OG);}else{var _1P8=new T2(0,_1OF,_1HZ);}var _1P7=_1P8;break;case 2:if(E(E(_1O7).c)==2){var _1P9=new T2(0,_1OF,_1OG);}else{var _1P9=new T2(0,_1OF,_1Ev);}var _1P7=_1P9;break;case 3:if(E(E(_1O7).c)==3){var _1Pa=new T2(0,_1OF,_1OG);}else{var _1Pa=new T2(0,_1OF,_1Eu);}var _1P7=_1Pa;break;default:if(E(E(_1O7).c)==4){var _1Pb=new T2(0,_1OF,_1OG);}else{var _1Pb=new T2(0,_1OF,_1HZ);}var _1P7=_1Pb;}var _1Pc=B(_1ql(_1HZ,_1P3,_1On,{_:0,a:E(_1OW),b:E(_1OX),c:E(_1OY),d:_1OZ,e:_1P0,f:_1P1,g:E(_1P2),h:E(_1Od),i:E(_1P3),j:E(_1P4),k:E(_1P5)},_1Ok,_1Ol,_1Om,_1On,_1Oo,_1Op,_1Oq,_1Or,_1Os,_1Ot,_1Ou,_1Ov,_1Ow,_1Ox,_1Oy,_1Oz,_1OA,_1P7,_1OB,_1OC,_1OD)),_1Pd=_1Pc.a,_1Pe=_1Pc.b,_1Pf=_1Pc.c,_1Pg=_1Pc.d,_1Ph=_1Pc.e,_1Pi=_1Pc.f,_1Pj=_1Pc.g,_1Pk=_1Pc.h,_1Pl=_1Pc.i,_1Pm=_1Pc.j,_1Pn=_1Pc.k,_1Po=_1Pc.l,_1Pp=_1Pc.m,_1Pq=_1Pc.n,_1Pr=_1Pc.o,_1Ps=_1Pc.q,_1Pt=_1Pc.r,_1Pu=_1Pc.s,_1Pv=_1Pc.t,_1Pw=_1Pc.u,_1Px=_1Pc.v,_1Py=E(_1Pc.p);if(!_1Py._){return {_:0,a:E(_1Pd),b:E(_1Pe),c:E(_1Pf),d:E(_1Pg),e:E(_1Ph),f:E(_1Pi),g:E(_1Pj),h:E(_1Pk),i:_1Pl,j:_1Pm,k:_1Pn,l:_1Po,m:E(_1Pp),n:_1Pq,o:E(_1Pr),p:E(_Z),q:_1Ps,r:E(_1Pt),s:E(_1Pu),t:_1Pv,u:E(_1Pw),v:E(_1Px)};}else{var _1Pz=B(_qy(_1P3,0))-2|0,_1PA=function(_1PB){var _1PC=E(_1Pd);return {_:0,a:E({_:0,a:E(_1PC.a),b:E(_1PC.b),c:E(_1PC.c),d:_1PC.d,e:_1PC.e,f:_1PC.f,g:E(_Z),h:_1PC.h,i:E(_1PC.i),j:E(_1PC.j),k:E(_1PC.k)}),b:E(_1Pe),c:E(_1Pf),d:E(B(_x(B(_0(_Z,B(_1IC(B(_aj(_1Gp,_1Py)),B(_9T(_1Pg)))))),new T(function(){return B(_aj(_1Dw,_1Py));},1)))),e:E(_1Ph),f:E(_1Pi),g:E(_1Pj),h:E(_1Pk),i:_1Pl,j:_1Pm,k:_1Pn,l:_1Po,m:E(_1Pp),n:_1Pq,o:E(_1Pr),p:E(_Z),q:_1Ps,r:E(B(_x(_1Pt,new T2(1,_1Ps,_Z)))),s:E(_1Pu),t:_1Pv,u:E(_1Pw),v:E(_1Px)};};if(_1Pz>0){if(!B(_vl(B(_1Dd(_1Pz,_1P3)),_1Et))){return {_:0,a:E(_1Pd),b:E(_1Pe),c:E(_1Pf),d:E(_1Pg),e:E(_1Ph),f:E(_1Pi),g:E(_1Pj),h:E(_1Pk),i:_1Pl,j:_1Pm,k:_1Pn,l:_1Po,m:E(_1Pp),n:_1Pq,o:E(_1Pr),p:E(_1Py),q:_1Ps,r:E(_1Pt),s:E(_1Pu),t:_1Pv,u:E(_1Pw),v:E(_1Px)};}else{return new F(function(){return _1PA(_);});}}else{if(!B(_vl(_1P3,_1Et))){return {_:0,a:E(_1Pd),b:E(_1Pe),c:E(_1Pf),d:E(_1Pg),e:E(_1Ph),f:E(_1Pi),g:E(_1Pj),h:E(_1Pk),i:_1Pl,j:_1Pm,k:_1Pn,l:_1Po,m:E(_1Pp),n:_1Pq,o:E(_1Pr),p:E(_1Py),q:_1Ps,r:E(_1Pt),s:E(_1Pu),t:_1Pv,u:E(_1Pw),v:E(_1Px)};}else{return new F(function(){return _1PA(_);});}}}};if(E(_1OH)==32){var _1PD=E(_1O7),_1PE=E(_1PD.a),_1PF=B(_1zt(_1OO,_1ON,_1PE.a,_1PE.b,_1PD.b,_1OU,_1PD.d,_1PD.e,_1PD.f,_1PD.g,_1PD.h,_1PD.i,_1PD.j,_1PD.k)),_1PG=E(_1PF.a),_1PH=B(_1CO(_1PG.a,E(_1PG.b),_1PF.b,_1PF.c,_1PF.d,_1PF.e,_1PF.f,_1PF.g,_1PF.h,_1PF.i,_1PF.j,_1PF.k));return new F(function(){return _1OV(_1PH.a,_1PH.b,_1PH.c,_1PH.d,_1PH.e,_1PH.f,_1PH.g,_1PH.i,_1PH.j,_1PH.k);});}else{var _1PI=E(_1O7),_1PJ=E(_1PI.a),_1PK=B(_1zt(_1OO,_1ON,_1PJ.a,_1PJ.b,_1PI.b,_1OU,_1PI.d,_1PI.e,_1PI.f,_1PI.g,_1PI.h,_1PI.i,_1PI.j,_1PI.k));return new F(function(){return _1OV(_1PK.a,_1PK.b,_1PK.c,_1PK.d,_1PK.e,_1PK.f,_1PK.g,_1PK.i,_1PK.j,_1PK.k);});}},_1PL=function(_1PM,_1PN){var _1PO=E(_1PN),_1PP=E(_1OJ);if(_1PM<=_1PP){if(_1PP<=_1PM){var _1PQ=E(_1OK);if(_1PO<=_1PQ){if(_1PQ<=_1PO){var _1PR=4;}else{var _1PR=0;}var _1PS=_1PR;}else{var _1PS=1;}var _1PT=_1PS;}else{var _1PT=2;}var _1PU=_1PT;}else{var _1PU=3;}var _1PV=function(_1PW,_1PX,_1PY,_1PZ,_1Q0,_1Q1,_1Q2,_1Q3,_1Q4,_1Q5){switch(E(_1PU)){case 0:if(!E(E(_1O7).c)){var _1Q6=new T2(0,_1OF,_1OG);}else{var _1Q6=new T2(0,_1OF,_1F1);}var _1Q7=_1Q6;break;case 1:if(E(E(_1O7).c)==1){var _1Q8=new T2(0,_1OF,_1OG);}else{var _1Q8=new T2(0,_1OF,_1HZ);}var _1Q7=_1Q8;break;case 2:if(E(E(_1O7).c)==2){var _1Q9=new T2(0,_1OF,_1OG);}else{var _1Q9=new T2(0,_1OF,_1Ev);}var _1Q7=_1Q9;break;case 3:if(E(E(_1O7).c)==3){var _1Qa=new T2(0,_1OF,_1OG);}else{var _1Qa=new T2(0,_1OF,_1Eu);}var _1Q7=_1Qa;break;default:if(E(E(_1O7).c)==4){var _1Qb=new T2(0,_1OF,_1OG);}else{var _1Qb=new T2(0,_1OF,_1HZ);}var _1Q7=_1Qb;}var _1Qc=B(_1ql(_1HZ,_1Q3,_1On,{_:0,a:E(_1PW),b:E(_1PX),c:E(_1PY),d:_1PZ,e:_1Q0,f:_1Q1,g:E(_1Q2),h:E(_1Od),i:E(_1Q3),j:E(_1Q4),k:E(_1Q5)},_1Ok,_1Ol,_1Om,_1On,_1Oo,_1Op,_1Oq,_1Or,_1Os,_1Ot,_1Ou,_1Ov,_1Ow,_1Ox,_1Oy,_1Oz,_1OA,_1Q7,_1OB,_1OC,_1OD)),_1Qd=_1Qc.a,_1Qe=_1Qc.b,_1Qf=_1Qc.c,_1Qg=_1Qc.d,_1Qh=_1Qc.e,_1Qi=_1Qc.f,_1Qj=_1Qc.g,_1Qk=_1Qc.h,_1Ql=_1Qc.i,_1Qm=_1Qc.j,_1Qn=_1Qc.k,_1Qo=_1Qc.l,_1Qp=_1Qc.m,_1Qq=_1Qc.n,_1Qr=_1Qc.o,_1Qs=_1Qc.q,_1Qt=_1Qc.r,_1Qu=_1Qc.s,_1Qv=_1Qc.t,_1Qw=_1Qc.u,_1Qx=_1Qc.v,_1Qy=E(_1Qc.p);if(!_1Qy._){return {_:0,a:E(_1Qd),b:E(_1Qe),c:E(_1Qf),d:E(_1Qg),e:E(_1Qh),f:E(_1Qi),g:E(_1Qj),h:E(_1Qk),i:_1Ql,j:_1Qm,k:_1Qn,l:_1Qo,m:E(_1Qp),n:_1Qq,o:E(_1Qr),p:E(_Z),q:_1Qs,r:E(_1Qt),s:E(_1Qu),t:_1Qv,u:E(_1Qw),v:E(_1Qx)};}else{var _1Qz=B(_qy(_1Q3,0))-2|0,_1QA=function(_1QB){var _1QC=E(_1Qd);return {_:0,a:E({_:0,a:E(_1QC.a),b:E(_1QC.b),c:E(_1QC.c),d:_1QC.d,e:_1QC.e,f:_1QC.f,g:E(_Z),h:_1QC.h,i:E(_1QC.i),j:E(_1QC.j),k:E(_1QC.k)}),b:E(_1Qe),c:E(_1Qf),d:E(B(_x(B(_0(_Z,B(_1IC(B(_aj(_1Gp,_1Qy)),B(_9T(_1Qg)))))),new T(function(){return B(_aj(_1Dw,_1Qy));},1)))),e:E(_1Qh),f:E(_1Qi),g:E(_1Qj),h:E(_1Qk),i:_1Ql,j:_1Qm,k:_1Qn,l:_1Qo,m:E(_1Qp),n:_1Qq,o:E(_1Qr),p:E(_Z),q:_1Qs,r:E(B(_x(_1Qt,new T2(1,_1Qs,_Z)))),s:E(_1Qu),t:_1Qv,u:E(_1Qw),v:E(_1Qx)};};if(_1Qz>0){if(!B(_vl(B(_1Dd(_1Qz,_1Q3)),_1Et))){return {_:0,a:E(_1Qd),b:E(_1Qe),c:E(_1Qf),d:E(_1Qg),e:E(_1Qh),f:E(_1Qi),g:E(_1Qj),h:E(_1Qk),i:_1Ql,j:_1Qm,k:_1Qn,l:_1Qo,m:E(_1Qp),n:_1Qq,o:E(_1Qr),p:E(_1Qy),q:_1Qs,r:E(_1Qt),s:E(_1Qu),t:_1Qv,u:E(_1Qw),v:E(_1Qx)};}else{return new F(function(){return _1QA(_);});}}else{if(!B(_vl(_1Q3,_1Et))){return {_:0,a:E(_1Qd),b:E(_1Qe),c:E(_1Qf),d:E(_1Qg),e:E(_1Qh),f:E(_1Qi),g:E(_1Qj),h:E(_1Qk),i:_1Ql,j:_1Qm,k:_1Qn,l:_1Qo,m:E(_1Qp),n:_1Qq,o:E(_1Qr),p:E(_1Qy),q:_1Qs,r:E(_1Qt),s:E(_1Qu),t:_1Qv,u:E(_1Qw),v:E(_1Qx)};}else{return new F(function(){return _1QA(_);});}}}};if(E(_1OH)==32){var _1QD=E(_1O7),_1QE=E(_1QD.a),_1QF=B(_1zt(_1PM,_1PO,_1QE.a,_1QE.b,_1QD.b,_1PU,_1QD.d,_1QD.e,_1QD.f,_1QD.g,_1QD.h,_1QD.i,_1QD.j,_1QD.k)),_1QG=E(_1QF.a),_1QH=B(_1CO(_1QG.a,E(_1QG.b),_1QF.b,_1QF.c,_1QF.d,_1QF.e,_1QF.f,_1QF.g,_1QF.h,_1QF.i,_1QF.j,_1QF.k));return new F(function(){return _1PV(_1QH.a,_1QH.b,_1QH.c,_1QH.d,_1QH.e,_1QH.f,_1QH.g,_1QH.i,_1QH.j,_1QH.k);});}else{var _1QI=E(_1O7),_1QJ=E(_1QI.a),_1QK=B(_1zt(_1PM,_1PO,_1QJ.a,_1QJ.b,_1QI.b,_1PU,_1QI.d,_1QI.e,_1QI.f,_1QI.g,_1QI.h,_1QI.i,_1QI.j,_1QI.k));return new F(function(){return _1PV(_1QK.a,_1QK.b,_1QK.c,_1QK.d,_1QK.e,_1QK.f,_1QK.g,_1QK.i,_1QK.j,_1QK.k);});}},_1QL=E(_1OH);switch(_1QL){case 72:var _1QM=E(_1OK);if(0<=(_1QM-1|0)){return B(_1OL(_1OJ,_1QM-1|0));}else{return B(_1OL(_1OJ,_1QM));}break;case 75:var _1QN=E(_1OJ);if(0<=(_1QN-1|0)){return B(_1PL(_1QN-1|0,_1OK));}else{return B(_1PL(_1QN,_1OK));}break;case 77:var _1QO=E(_1OJ);if(E(_1IY)!=(_1QO+1|0)){return B(_1PL(_1QO+1|0,_1OK));}else{return B(_1PL(_1QO,_1OK));}break;case 80:var _1QP=E(_1OK);if(E(_1IZ)!=(_1QP+1|0)){return B(_1OL(_1OJ,_1QP+1|0));}else{return B(_1OL(_1OJ,_1QP));}break;case 104:var _1QQ=E(_1OJ);if(0<=(_1QQ-1|0)){return B(_1PL(_1QQ-1|0,_1OK));}else{return B(_1PL(_1QQ,_1OK));}break;case 106:var _1QR=E(_1OK);if(E(_1IZ)!=(_1QR+1|0)){return B(_1OL(_1OJ,_1QR+1|0));}else{return B(_1OL(_1OJ,_1QR));}break;case 107:var _1QS=E(_1OK);if(0<=(_1QS-1|0)){return B(_1OL(_1OJ,_1QS-1|0));}else{return B(_1OL(_1OJ,_1QS));}break;case 108:var _1QT=E(_1OJ);if(E(_1IY)!=(_1QT+1|0)){return B(_1PL(_1QT+1|0,_1OK));}else{return B(_1PL(_1QT,_1OK));}break;default:var _1QU=E(_1OJ),_1QV=E(_1OK),_1QW=function(_1QX,_1QY,_1QZ,_1R0,_1R1,_1R2,_1R3,_1R4,_1R5,_1R6){if(E(E(_1O7).c)==4){var _1R7=new T2(0,_1OF,_1OG);}else{var _1R7=new T2(0,_1OF,_1HZ);}var _1R8=B(_1ql(_1HZ,_1R4,_1On,{_:0,a:E(_1QX),b:E(_1QY),c:E(_1QZ),d:_1R0,e:_1R1,f:_1R2,g:E(_1R3),h:E(_1Od),i:E(_1R4),j:E(_1R5),k:E(_1R6)},_1Ok,_1Ol,_1Om,_1On,_1Oo,_1Op,_1Oq,_1Or,_1Os,_1Ot,_1Ou,_1Ov,_1Ow,_1Ox,_1Oy,_1Oz,_1OA,_1R7,_1OB,_1OC,_1OD)),_1R9=_1R8.a,_1Ra=_1R8.b,_1Rb=_1R8.c,_1Rc=_1R8.d,_1Rd=_1R8.e,_1Re=_1R8.f,_1Rf=_1R8.g,_1Rg=_1R8.h,_1Rh=_1R8.i,_1Ri=_1R8.j,_1Rj=_1R8.k,_1Rk=_1R8.l,_1Rl=_1R8.m,_1Rm=_1R8.n,_1Rn=_1R8.o,_1Ro=_1R8.q,_1Rp=_1R8.r,_1Rq=_1R8.s,_1Rr=_1R8.t,_1Rs=_1R8.u,_1Rt=_1R8.v,_1Ru=E(_1R8.p);if(!_1Ru._){return {_:0,a:E(_1R9),b:E(_1Ra),c:E(_1Rb),d:E(_1Rc),e:E(_1Rd),f:E(_1Re),g:E(_1Rf),h:E(_1Rg),i:_1Rh,j:_1Ri,k:_1Rj,l:_1Rk,m:E(_1Rl),n:_1Rm,o:E(_1Rn),p:E(_Z),q:_1Ro,r:E(_1Rp),s:E(_1Rq),t:_1Rr,u:E(_1Rs),v:E(_1Rt)};}else{var _1Rv=B(_qy(_1R4,0))-2|0,_1Rw=function(_1Rx){var _1Ry=E(_1R9);return {_:0,a:E({_:0,a:E(_1Ry.a),b:E(_1Ry.b),c:E(_1Ry.c),d:_1Ry.d,e:_1Ry.e,f:_1Ry.f,g:E(_Z),h:_1Ry.h,i:E(_1Ry.i),j:E(_1Ry.j),k:E(_1Ry.k)}),b:E(_1Ra),c:E(_1Rb),d:E(B(_x(B(_0(_Z,B(_1IC(B(_aj(_1Gp,_1Ru)),B(_9T(_1Rc)))))),new T(function(){return B(_aj(_1Dw,_1Ru));},1)))),e:E(_1Rd),f:E(_1Re),g:E(_1Rf),h:E(_1Rg),i:_1Rh,j:_1Ri,k:_1Rj,l:_1Rk,m:E(_1Rl),n:_1Rm,o:E(_1Rn),p:E(_Z),q:_1Ro,r:E(B(_x(_1Rp,new T2(1,_1Ro,_Z)))),s:E(_1Rq),t:_1Rr,u:E(_1Rs),v:E(_1Rt)};};if(_1Rv>0){if(!B(_vl(B(_1Dd(_1Rv,_1R4)),_1Et))){return {_:0,a:E(_1R9),b:E(_1Ra),c:E(_1Rb),d:E(_1Rc),e:E(_1Rd),f:E(_1Re),g:E(_1Rf),h:E(_1Rg),i:_1Rh,j:_1Ri,k:_1Rj,l:_1Rk,m:E(_1Rl),n:_1Rm,o:E(_1Rn),p:E(_1Ru),q:_1Ro,r:E(_1Rp),s:E(_1Rq),t:_1Rr,u:E(_1Rs),v:E(_1Rt)};}else{return new F(function(){return _1Rw(_);});}}else{if(!B(_vl(_1R4,_1Et))){return {_:0,a:E(_1R9),b:E(_1Ra),c:E(_1Rb),d:E(_1Rc),e:E(_1Rd),f:E(_1Re),g:E(_1Rf),h:E(_1Rg),i:_1Rh,j:_1Ri,k:_1Rj,l:_1Rk,m:E(_1Rl),n:_1Rm,o:E(_1Rn),p:E(_1Ru),q:_1Ro,r:E(_1Rp),s:E(_1Rq),t:_1Rr,u:E(_1Rs),v:E(_1Rt)};}else{return new F(function(){return _1Rw(_);});}}}};if(E(_1QL)==32){var _1Rz=E(_1O7),_1RA=E(_1Rz.a),_1RB=B(_1zt(_1QU,_1QV,_1RA.a,_1RA.b,_1Rz.b,_1Dj,_1Rz.d,_1Rz.e,_1Rz.f,_1Rz.g,_1Rz.h,_1Rz.i,_1Rz.j,_1Rz.k)),_1RC=E(_1RB.a),_1RD=B(_1CO(_1RC.a,E(_1RC.b),_1RB.b,_1RB.c,_1RB.d,_1RB.e,_1RB.f,_1RB.g,_1RB.h,_1RB.i,_1RB.j,_1RB.k));return B(_1QW(_1RD.a,_1RD.b,_1RD.c,_1RD.d,_1RD.e,_1RD.f,_1RD.g,_1RD.i,_1RD.j,_1RD.k));}else{var _1RE=E(_1O7),_1RF=E(_1RE.a),_1RG=B(_1zt(_1QU,_1QV,_1RF.a,_1RF.b,_1RE.b,_1Dj,_1RE.d,_1RE.e,_1RE.f,_1RE.g,_1RE.h,_1RE.i,_1RE.j,_1RE.k));return B(_1QW(_1RG.a,_1RG.b,_1RG.c,_1RG.d,_1RG.e,_1RG.f,_1RG.g,_1RG.i,_1RG.j,_1RG.k));}}}),_1RH=B(_1bL(_1Of,_1Og,_1IJ,_1IK,_1IL,_1Oi,_)),_1RI=_1RH,_1RJ=E(_1Oh),_1RK=function(_,_1RL){var _1RM=function(_1RN){var _1RO=B(_1E1(_1HU,B(_cv(_1RL)),_)),_1RP=E(_1RI),_1RQ=_1RP.d,_1RR=_1RP.e,_1RS=_1RP.f,_1RT=_1RP.g,_1RU=_1RP.i,_1RV=_1RP.j,_1RW=_1RP.k,_1RX=_1RP.l,_1RY=_1RP.m,_1RZ=_1RP.n,_1S0=_1RP.o,_1S1=_1RP.p,_1S2=_1RP.q,_1S3=_1RP.r,_1S4=_1RP.t,_1S5=_1RP.v,_1S6=E(_1RP.u),_1S7=_1S6.a,_1S8=_1S6.d,_1S9=_1S6.e,_1Sa=_1S6.f,_1Sb=_1S6.g,_1Sc=_1S6.h,_1Sd=_1S6.i,_1Se=E(_1RP.a),_1Sf=_1Se.c,_1Sg=_1Se.f,_1Sh=_1Se.g,_1Si=_1Se.h,_1Sj=E(_1RP.h),_1Sk=E(_1RP.s),_1Sl=function(_1Sm){var _1Sn=function(_1So){if(_1So!=E(_1Em)){var _1Sp=B(_aW(_1m0,_1So)),_1Sq=_1Sp.a,_1Sr=E(_1Sp.b),_1Ss=B(_1fX(_1Sq,_1Sr,new T(function(){return B(_aW(_1o5,_1So));})));return new F(function(){return _1IH(_1Oe,_1IJ,_1IK,_1IL,_1El,B(_aW(_1mb,_1So)),_1Ss,_1Sf,B(_aW(_1mo,_1So)),32,_1So,_1Sh,_1Si,B(_x(_1Se.i,new T2(1,_1Ek,new T(function(){return B(_H(0,_1Sg,_Z));})))),B(_1DF(_1Ej,_1Ss)),_B2,_1Sq,_1Sr,_Z,_1RQ,_1RR,_1RS,_1RT,_1Sj.a,_1Sj.b,_1RU,_1RV,_1RW, -1,_1RY,_1RZ,_1S0,_1S1,_1S2,_1S3,_1Sk.a,_1Sk.b,_1S4,_B2,_B2,_B2,_1S8,_1S9,_1Sa,_1Sb,_1Sc,_1Sd,_1S5,_);});}else{var _1St=__app1(E(_rn),_1Og),_1Su=B(A2(_ro,_1Of,_)),_1Sv=B(A(_qT,[_1Of,_n8,_1Ef,_1Eh,_1Eg,_])),_1Sw=B(A(_qT,[_1Of,_n8,_1Ef,_1Ee,_1F2,_])),_1Sx=B(A(_qT,[_1Of,_n8,_1F1,_1F0,_1EZ,_]));return new T(function(){return {_:0,a:E({_:0,a:E(_1m2),b:E(_1EY),c:E(_1Sf),d:E(_1EC),e:32,f:0,g:E(_1Sh),h:_1Si,i:E(_Z),j:E(_1Se.j),k:E(_B2)}),b:E(_1lN),c:E(_1RP.c),d:E(_1RQ),e:E(_1RR),f:E(_1RS),g:E(_1RT),h:E(_1Sj),i:_1RU,j:_1RV,k:_1RW,l:_1RX,m:E(_1RY),n:_1RZ,o:E(_1S0),p:E(_1S1),q:_1S2,r:E(_1S3),s:E(_1Sk),t:_1S4,u:E({_:0,a:E(_1S7),b:E(_B3),c:E(_B2),d:E(_1S8),e:E(_1S9),f:E(_1Sa),g:E(_1Sb),h:E(_1Sc),i:E(_1Sd)}),v:E(_1S5)};});}};if(_1RX>=0){return new F(function(){return _1Sn(_1RX);});}else{return new F(function(){return _1Sn(_1Sg+1|0);});}};if(!E(_1S7)){if(E(_1RJ)==110){return new F(function(){return _1Sl(_);});}else{return _1RP;}}else{return new F(function(){return _1Sl(_);});}};if(E(_1RJ)==114){if(!B(_ae(_1RL,_1En))){var _1Sy=E(_1RL);if(!_1Sy._){return _1RI;}else{var _1Sz=_1Sy.b;return new T(function(){var _1SA=E(_1RI),_1SB=E(_1SA.a),_1SC=E(_1Sy.a),_1SD=E(_1SC);if(_1SD==34){var _1SE=B(_Yg(_1SC,_1Sz));if(!_1SE._){var _1SF=E(_1FW);}else{var _1SG=E(_1SE.b);if(!_1SG._){var _1SH=E(_1EG);}else{var _1SI=_1SG.a,_1SJ=E(_1SG.b);if(!_1SJ._){var _1SK=new T2(1,new T2(1,_1SI,_Z),_Z);}else{var _1SL=E(_1SI),_1SM=new T(function(){var _1SN=B(_LC(126,_1SJ.a,_1SJ.b));return new T2(0,_1SN.a,_1SN.b);});if(E(_1SL)==126){var _1SO=new T2(1,_Z,new T2(1,new T(function(){return E(E(_1SM).a);}),new T(function(){return E(E(_1SM).b);})));}else{var _1SO=new T2(1,new T2(1,_1SL,new T(function(){return E(E(_1SM).a);})),new T(function(){return E(E(_1SM).b);}));}var _1SK=_1SO;}var _1SH=_1SK;}var _1SF=_1SH;}var _1SP=_1SF;}else{var _1SQ=E(_1Sz);if(!_1SQ._){var _1SR=new T2(1,new T2(1,_1SC,_Z),_Z);}else{var _1SS=new T(function(){var _1ST=B(_LC(126,_1SQ.a,_1SQ.b));return new T2(0,_1ST.a,_1ST.b);});if(E(_1SD)==126){var _1SU=new T2(1,_Z,new T2(1,new T(function(){return E(E(_1SS).a);}),new T(function(){return E(E(_1SS).b);})));}else{var _1SU=new T2(1,new T2(1,_1SC,new T(function(){return E(E(_1SS).a);})),new T(function(){return E(E(_1SS).b);}));}var _1SR=_1SU;}var _1SP=_1SR;}var _1SV=B(_KK(B(_x7(_1Eo,new T(function(){return B(_NR(_1SP));})))));if(!_1SV._){return E(_1Ec);}else{if(!E(_1SV.b)._){var _1SW=E(_1SV.a),_1SX=B(_aW(_1m0,_1SW)),_1SY=B(_aW(_1SP,1));if(!_1SY._){var _1SZ=__Z;}else{var _1T0=E(_1SY.b);if(!_1T0._){var _1T1=__Z;}else{var _1T2=E(_1SY.a),_1T3=new T(function(){var _1T4=B(_LC(44,_1T0.a,_1T0.b));return new T2(0,_1T4.a,_1T4.b);});if(E(_1T2)==44){var _1T5=B(_16e(_Z,new T(function(){return E(E(_1T3).a);}),new T(function(){return E(E(_1T3).b);})));}else{var _1T5=B(_16i(new T2(1,_1T2,new T(function(){return E(E(_1T3).a);})),new T(function(){return E(E(_1T3).b);})));}var _1T1=_1T5;}var _1SZ=_1T1;}var _1T6=B(_aW(_1SP,2));if(!_1T6._){var _1T7=E(_1EH);}else{var _1T8=_1T6.a,_1T9=E(_1T6.b);if(!_1T9._){var _1Ta=B(_aj(_1Ez,new T2(1,new T2(1,_1T8,_Z),_Z)));}else{var _1Tb=E(_1T8),_1Tc=new T(function(){var _1Td=B(_LC(44,_1T9.a,_1T9.b));return new T2(0,_1Td.a,_1Td.b);});if(E(_1Tb)==44){var _1Te=B(_aj(_1Ez,new T2(1,_Z,new T2(1,new T(function(){return E(E(_1Tc).a);}),new T(function(){return E(E(_1Tc).b);})))));}else{var _1Te=B(_aj(_1Ez,new T2(1,new T2(1,_1Tb,new T(function(){return E(E(_1Tc).a);})),new T(function(){return E(E(_1Tc).b);}))));}var _1Ta=_1Te;}var _1T7=_1Ta;}return {_:0,a:E({_:0,a:E(B(_aW(_1mb,_1SW))),b:E(B(_1fX(_1SX.a,E(_1SX.b),new T(function(){return B(_aW(_1o5,_1SW));})))),c:E(_1SB.c),d:B(_aW(_1mo,_1SW)),e:32,f:_1SW,g:E(_1SB.g),h:_1SB.h,i:E(_1SB.i),j:E(_1SB.j),k:E(_1SB.k)}),b:E(_1SX),c:E(_1SA.c),d:E(_1SA.d),e:E(_1SZ),f:E(_1T7),g:E(_1SA.g),h:E(_1SA.h),i:_1SA.i,j:_1SA.j,k:_1SA.k,l:_1SA.l,m:E(_1SA.m),n:_1SA.n,o:E(_1SA.o),p:E(_1SA.p),q:_1SA.q,r:E(_1SA.r),s:E(_1SA.s),t:_1SA.t,u:E(_1SA.u),v:E(_1SA.v)};}else{return E(_1Ed);}}});}}else{return new F(function(){return _1RM(_);});}}else{return new F(function(){return _1RM(_);});}};switch(E(_1RJ)){case 100:var _1Tf=__app1(E(_1FU),toJSStr(E(_1Er)));return new F(function(){return _1RK(_,_1E9);});break;case 114:var _1Tg=B(_16t(_aB,toJSStr(E(_1Er)),_));return new F(function(){return _1RK(_,new T(function(){var _1Th=E(_1Tg);if(!_1Th._){return E(_1Ea);}else{return fromJSStr(B(_1sA(_1Th.a)));}}));});break;case 115:var _1Ti=new T(function(){var _1Tj=new T(function(){var _1Tk=new T(function(){var _1Tl=B(_aj(_aG,_1J3));if(!_1Tl._){return __Z;}else{return B(_1E6(new T2(1,_1Tl.a,new T(function(){return B(_1F3(_1Ep,_1Tl.b));}))));}}),_1Tm=new T(function(){var _1Tn=function(_1To){var _1Tp=E(_1To);if(!_1Tp._){return __Z;}else{var _1Tq=E(_1Tp.a);return new T2(1,_1Tq.a,new T2(1,_1Tq.b,new T(function(){return B(_1Tn(_1Tp.b));})));}},_1Tr=B(_1Tn(_1J2));if(!_1Tr._){return __Z;}else{return B(_1E6(new T2(1,_1Tr.a,new T(function(){return B(_1F3(_1Ep,_1Tr.b));}))));}});return B(_1F3(_1Eq,new T2(1,_1Tm,new T2(1,_1Tk,_Z))));});return B(_x(B(_1E6(new T2(1,new T(function(){return B(_H(0,_1IS,_Z));}),_1Tj))),_1EF));}),_1Ts=__app2(E(_1FX),toJSStr(E(_1Er)),B(_1sA(B(_1HW(B(unAppCStr("\"",_1Ti)))))));return new F(function(){return _1RK(_,_1Eb);});break;default:return new F(function(){return _1RK(_,_1Es);});}},_1Tt=E(_1Jg);if(!_1Tt._){var _1Tu=B(_1E1(_1HU,_1EE,_));return new F(function(){return _1Ob(_);});}else{var _1Tv=new T(function(){return B(_H(0,E(_1Tt.a),new T(function(){return B(_1FZ(_1Tt.b));})));}),_1Tw=B(_1E1(_1HU,new T2(1,_2B,_1Tv),_));return new F(function(){return _1Ob(_);});}};if(!E(_1O6.f)){var _1Tx=B(_1E1(_1HU,_1Go,_));return new F(function(){return _1O8(_);});}else{var _1Ty=B(_1E1(_1HU,_1Gn,_));return new F(function(){return _1O8(_);});}},_1Tz=E(_1J4);if(!_1Tz._){var _1TA=B(_1E1(_1HU,_1EE,_));return new F(function(){return _1O2(_);});}else{var _1TB=new T(function(){var _1TC=E(_1Tz.a),_1TD=new T(function(){return B(A3(_wK,_aC,new T2(1,function(_1TE){return new F(function(){return _1EI(_1TC.a,_1TE);});},new T2(1,function(_1TF){return new F(function(){return _1EI(_1TC.b,_1TF);});},_Z)),new T2(1,_F,new T(function(){return B(_1G3(_1Tz.b));}))));});return new T2(1,_G,_1TD);}),_1TG=B(_1E1(_1HU,new T2(1,_2B,_1TB),_));return new F(function(){return _1O2(_);});}},_1TH=E(_1J3);if(!_1TH._){var _1TI=B(_1E1(_1HU,_1EE,_));return new F(function(){return _1O1(_);});}else{var _1TJ=new T(function(){return B(_H(0,E(_1TH.a),new T(function(){return B(_1Gb(_1TH.b));})));}),_1TK=B(_1E1(_1HU,new T2(1,_2B,_1TJ),_));return new F(function(){return _1O1(_);});}},_1TL=E(_1J2);if(!_1TL._){var _1TM=B(_1E1(_1HU,_1EE,_));return new F(function(){return _1O0(_);});}else{var _1TN=new T(function(){var _1TO=E(_1TL.a),_1TP=new T(function(){return B(A3(_wK,_aC,new T2(1,function(_1TQ){return new F(function(){return _1EI(_1TO.a,_1TQ);});},new T2(1,function(_1TR){return new F(function(){return _1EI(_1TO.b,_1TR);});},_Z)),new T2(1,_F,new T(function(){return B(_1Gf(_1TL.b));}))));});return new T2(1,_G,_1TP);}),_1TS=B(_1E1(_1HU,new T2(1,_2B,_1TN),_));return new F(function(){return _1O0(_);});}}else{return new F(function(){return _1JC(_,_1IN,_1IO,_1IP,_1IQ,_1IR,_1IS,_1IT,_1IU,_1IV,_1IW,_1IX,_1Jx,_1J0,_1J1,_1J2,_1J3,_1J4,_1Jw,_1J7,_1J8,_1J9,_1Ja,_1Jb,_1Jc,_Z,_1Je,_1Jf,_1Jg,_1Jh,_1Ji,_1Jj,_1Ju,_1Jt);});}}}}}}}else{if(!E(_1Jq)){return {_:0,a:E(_1Jy),b:E(_1Jx),c:E(_1J0),d:E(_1J1),e:E(_1J2),f:E(_1J3),g:E(_1J4),h:E(_1Jw),i:_1J7,j:_1J8,k:_1J9,l:_1Ja,m:E(_1Jb),n:_1Jc,o:E(_1Jd),p:E(_1Je),q:_1Jf,r:E(_1Jg),s:E(_1Jv),t:_1Jj,u:E({_:0,a:E(_1Jk),b:E(_B2),c:E(_1Jm),d:E(_B2),e:E(_1Jo),f:E(_B2),g:E(_B2),h:E(_1Jr),i:E(_1Js)}),v:E(_1Jt)};}else{var _1TT=E(_1II),_1TU=new T(function(){var _1TV=new T(function(){var _1TW=B(_1sE(_1Jb));return new T2(0,_1TW.a,_1TW.b);}),_1TX=new T(function(){return B(_qy(E(_1TV).a,0))-1|0;}),_1TY=function(_1TZ){var _1U0=E(_1TZ);switch(_1U0){case  -2:return E(_1Jz);case  -1:return {_:0,a:E(_1Jy),b:E(_1Jx),c:E(B(_1lv(_Z,new T(function(){return B(_aW(E(_1TV).b,_1Jc));})))),d:E(_1J1),e:E(_1J2),f:E(_1J3),g:E(_1J4),h:E(_1Jw),i:_1J7,j:_1J8,k:_1J9,l:_1Ja,m:E(_1Jb),n:_1Jc,o:E(_1Jd),p:E(_1Je),q:_1Jf,r:E(_1Jg),s:E(_1Jv),t:_1Jj,u:E({_:0,a:E(_1Jk),b:E(_B2),c:E(_B3),d:E(_B2),e:E(_1Jo),f:E(_B2),g:E(_B2),h:E(_1Jr),i:E(_1Js)}),v:E(_1Jt)};default:return {_:0,a:E(_1Jy),b:E(_1Jx),c:E(_1J0),d:E(_1J1),e:E(_1J2),f:E(_1J3),g:E(_1J4),h:E(_1Jw),i:_1J7,j:_1J8,k:_1J9,l:_1Ja,m:E(_1Jb),n:_1U0,o:E(_1Jd),p:E(_1Je),q:_1Jf,r:E(_1Jg),s:E(_1Jv),t:_1Jj,u:E(_1Ju),v:E(_1Jt)};}};switch(E(B(_1tA(E(_1IM))))){case 32:return {_:0,a:E(_1Jy),b:E(_1Jx),c:E(B(_1lv(_Z,new T(function(){return B(_aW(E(_1TV).b,_1Jc));})))),d:E(_1J1),e:E(_1J2),f:E(_1J3),g:E(_1J4),h:E(_1Jw),i:_1J7,j:_1J8,k:_1J9,l:_1Ja,m:E(_1Jb),n:_1Jc,o:E(_1Jd),p:E(_1Je),q:_1Jf,r:E(_1Jg),s:E(_1Jv),t:_1Jj,u:E({_:0,a:E(_1Jk),b:E(_B2),c:E(_B3),d:E(_B2),e:E(_1Jo),f:E(_B2),g:E(_B2),h:E(_1Jr),i:E(_1Js)}),v:E(_1Jt)};break;case 72:var _1U1=E(_1Jc);if(!_1U1){return B(_1TY(E(_1TX)));}else{return B(_1TY(_1U1-1|0));}break;case 75:if(_1Jc!=E(_1TX)){return B(_1TY(_1Jc+1|0));}else{return {_:0,a:E(_1Jy),b:E(_1Jx),c:E(_1J0),d:E(_1J1),e:E(_1J2),f:E(_1J3),g:E(_1J4),h:E(_1Jw),i:_1J7,j:_1J8,k:_1J9,l:_1Ja,m:E(_1Jb),n:0,o:E(_1Jd),p:E(_1Je),q:_1Jf,r:E(_1Jg),s:E(_1Jv),t:_1Jj,u:E(_1Ju),v:E(_1Jt)};}break;case 77:var _1U2=E(_1Jc);if(!_1U2){return B(_1TY(E(_1TX)));}else{return B(_1TY(_1U2-1|0));}break;case 80:if(_1Jc!=E(_1TX)){return B(_1TY(_1Jc+1|0));}else{return {_:0,a:E(_1Jy),b:E(_1Jx),c:E(_1J0),d:E(_1J1),e:E(_1J2),f:E(_1J3),g:E(_1J4),h:E(_1Jw),i:_1J7,j:_1J8,k:_1J9,l:_1Ja,m:E(_1Jb),n:0,o:E(_1Jd),p:E(_1Je),q:_1Jf,r:E(_1Jg),s:E(_1Jv),t:_1Jj,u:E(_1Ju),v:E(_1Jt)};}break;case 104:if(_1Jc!=E(_1TX)){return B(_1TY(_1Jc+1|0));}else{return {_:0,a:E(_1Jy),b:E(_1Jx),c:E(_1J0),d:E(_1J1),e:E(_1J2),f:E(_1J3),g:E(_1J4),h:E(_1Jw),i:_1J7,j:_1J8,k:_1J9,l:_1Ja,m:E(_1Jb),n:0,o:E(_1Jd),p:E(_1Je),q:_1Jf,r:E(_1Jg),s:E(_1Jv),t:_1Jj,u:E(_1Ju),v:E(_1Jt)};}break;case 106:if(_1Jc!=E(_1TX)){return B(_1TY(_1Jc+1|0));}else{return {_:0,a:E(_1Jy),b:E(_1Jx),c:E(_1J0),d:E(_1J1),e:E(_1J2),f:E(_1J3),g:E(_1J4),h:E(_1Jw),i:_1J7,j:_1J8,k:_1J9,l:_1Ja,m:E(_1Jb),n:0,o:E(_1Jd),p:E(_1Je),q:_1Jf,r:E(_1Jg),s:E(_1Jv),t:_1Jj,u:E(_1Ju),v:E(_1Jt)};}break;case 107:var _1U3=E(_1Jc);if(!_1U3){return B(_1TY(E(_1TX)));}else{return B(_1TY(_1U3-1|0));}break;case 108:var _1U4=E(_1Jc);if(!_1U4){return B(_1TY(E(_1TX)));}else{return B(_1TY(_1U4-1|0));}break;default:return E(_1Jz);}});return new F(function(){return _1bL(_1TT.a,_1TT.b,_1IJ,_1IK,_1IL,_1TU,_);});}}};if(!E(_1Jm)){return new F(function(){return _1JA(_);});}else{if(!E(_1Jn)){return new F(function(){return _155(_1II,_1IJ,_1IK,_1IL,_1Jy,_1IY,_1IZ,_1J0,_1J1,_1J2,_1J3,_1J4,_1J5,_1J6,_1J7,_1J8,_1J9,_1Ja,_1Jb,_1Jc,_1Jd,_1Je,_1Jf,_1Jg,_1Jv,_1Jj,_1Jk,_B2,_B2,_1Jo,_B3,_1Jq,_1Jr,_1Js,_1Jt,_);});}else{return new F(function(){return _1JA(_);});}}}else{return _1Jz;}}else{return _1Jz;}},_1U5=function(_1U6,_1U7,_1U8){var _1U9=E(_1U8);if(!_1U9._){return 0;}else{var _1Ua=_1U9.b,_1Ub=E(_1U9.a),_1Uc=_1Ub.a,_1Ud=_1Ub.b;return (_1U6<=_1Uc)?1+B(_1U5(_1U6,_1U7,_1Ua))|0:(_1U6>=_1Uc+_1Ub.c)?1+B(_1U5(_1U6,_1U7,_1Ua))|0:(_1U7<=_1Ud)?1+B(_1U5(_1U6,_1U7,_1Ua))|0:(_1U7>=_1Ud+_1Ub.d)?1+B(_1U5(_1U6,_1U7,_1Ua))|0:1;}},_1Ue=function(_1Uf,_1Ug,_1Uh){var _1Ui=E(_1Uh);if(!_1Ui._){return 0;}else{var _1Uj=_1Ui.b,_1Uk=E(_1Ui.a),_1Ul=_1Uk.a,_1Um=_1Uk.b;if(_1Uf<=_1Ul){return 1+B(_1Ue(_1Uf,_1Ug,_1Uj))|0;}else{if(_1Uf>=_1Ul+_1Uk.c){return 1+B(_1Ue(_1Uf,_1Ug,_1Uj))|0;}else{var _1Un=E(_1Ug);return (_1Un<=_1Um)?1+B(_1U5(_1Uf,_1Un,_1Uj))|0:(_1Un>=_1Um+_1Uk.d)?1+B(_1U5(_1Uf,_1Un,_1Uj))|0:1;}}}},_1Uo=function(_1Up,_1Uq,_1Ur){var _1Us=E(_1Ur);if(!_1Us._){return 0;}else{var _1Ut=_1Us.b,_1Uu=E(_1Us.a),_1Uv=_1Uu.a,_1Uw=_1Uu.b,_1Ux=E(_1Up);if(_1Ux<=_1Uv){return 1+B(_1Ue(_1Ux,_1Uq,_1Ut))|0;}else{if(_1Ux>=_1Uv+_1Uu.c){return 1+B(_1Ue(_1Ux,_1Uq,_1Ut))|0;}else{var _1Uy=E(_1Uq);return (_1Uy<=_1Uw)?1+B(_1U5(_1Ux,_1Uy,_1Ut))|0:(_1Uy>=_1Uw+_1Uu.d)?1+B(_1U5(_1Ux,_1Uy,_1Ut))|0:1;}}}},_1Uz=function(_1UA,_1UB){return new T2(0,new T(function(){return new T4(0,0,100,100,E(_1UB)-100);}),new T2(1,new T(function(){return new T4(0,0,E(_1UB)-100,E(_1UA),100);}),new T2(1,new T(function(){return new T4(0,0,0,E(_1UA),100);}),new T2(1,new T(function(){return new T4(0,E(_1UA)-100,100,100,E(_1UB)-100);}),new T2(1,new T(function(){return new T4(0,100,100,E(_1UA)-200,E(_1UB)-200);}),_Z)))));},_1UC=32,_1UD=76,_1UE=75,_1UF=74,_1UG=72,_1UH=64,_1UI=function(_1UJ,_1UK,_1UL,_1UM,_1UN){var _1UO=new T(function(){var _1UP=E(_1UK),_1UQ=E(_1UP.a),_1UR=_1UQ.a,_1US=_1UQ.b,_1UT=B(_1Uz(_1UR,_1US)),_1UU=new T(function(){var _1UV=E(_1UP.b);return new T2(0,new T(function(){return B(_kd(_1UR,_1UV.a));}),new T(function(){return B(_kd(_1US,_1UV.b));}));});switch(B(_1Uo(new T(function(){return E(_1UM)*E(E(_1UU).a);},1),new T(function(){return E(_1UN)*E(E(_1UU).b);},1),new T2(1,_1UT.a,_1UT.b)))){case 1:return E(_1UG);break;case 2:return E(_1UF);break;case 3:return E(_1UE);break;case 4:return E(_1UD);break;case 5:return E(_1UC);break;default:return E(_1UH);}});return function(_1UW,_){var _1UX=E(E(_1UK).a),_1UY=E(_1UW),_1UZ=E(_1UY.a),_1V0=E(_1UY.b),_1V1=E(_1UY.h),_1V2=E(_1UY.s),_1V3=E(_1UY.u);return new F(function(){return _1IH(_1UJ,_1UX.a,_1UX.b,_1UL,_1UO,_1UZ.a,_1UZ.b,_1UZ.c,_1UZ.d,_1UZ.e,_1UZ.f,_1UZ.g,_1UZ.h,_1UZ.i,_1UZ.j,_1UZ.k,_1V0.a,_1V0.b,_1UY.c,_1UY.d,_1UY.e,_1UY.f,_1UY.g,_1V1.a,_1V1.b,_1UY.i,_1UY.j,_1UY.k,_1UY.l,_1UY.m,_1UY.n,_1UY.o,_1UY.p,_1UY.q,_1UY.r,_1V2.a,_1V2.b,_1UY.t,_1V3.a,_1V3.b,_1V3.c,_1V3.d,_1V3.e,_1V3.f,_1V3.g,_1V3.h,_1V3.i,_1UY.v,_);});};},_1V4=function(_1V5){return E(E(_1V5).a);},_1V6=function(_1V7){return E(E(_1V7).a);},_1V8=new T1(1,_B2),_1V9="false",_1Va=new T1(1,_B3),_1Vb="true",_1Vc=function(_1Vd){var _1Ve=strEq(_1Vd,E(_1Vb));if(!E(_1Ve)){var _1Vf=strEq(_1Vd,E(_1V9));return (E(_1Vf)==0)?__Z:E(_1V8);}else{return E(_1Va);}},_1Vg=2,_1Vh="paused",_1Vi="ended",_1Vj=function(_1Vk){return E(E(_1Vk).b);},_1Vl=function(_1Vm,_1Vn){var _1Vo=function(_){var _1Vp=E(_1Vn),_1Vq=E(_m5),_1Vr=__app2(_1Vq,_1Vp,E(_1Vi)),_1Vs=String(_1Vr),_1Vt=function(_1Vu){var _1Vv=__app2(_1Vq,_1Vp,E(_1Vh));return new T(function(){var _1Vw=String(_1Vv),_1Vx=B(_1Vc(_1Vw));if(!_1Vx._){return 0;}else{if(!E(_1Vx.a)){return 0;}else{return 1;}}});},_1Vy=B(_1Vc(_1Vs));if(!_1Vy._){return new F(function(){return _1Vt(_);});}else{if(!E(_1Vy.a)){return new F(function(){return _1Vt(_);});}else{return _1Vg;}}};return new F(function(){return A2(_1Vj,_1Vm,_1Vo);});},_1Vz="duration",_1VA=new T(function(){return eval("(function(e,t) {e.currentTime = t;})");}),_1VB=function(_1VC,_1VD,_1VE){var _1VF=new T(function(){var _1VG=E(_1VE);switch(_1VG._){case 0:return function(_){var _1VH=__app2(E(_1VA),E(_1VD),0);return new F(function(){return _kK(_);});};break;case 1:return function(_){var _1VI=E(_1VD),_1VJ=__app2(E(_m5),_1VI,E(_1Vz)),_1VK=String(_1VJ),_1VL=Number(_1VK),_1VM=isDoubleNaN(_1VL);if(!E(_1VM)){var _1VN=__app2(E(_1VA),_1VI,_1VL);return new F(function(){return _kK(_);});}else{var _1VO=__app2(E(_1VA),_1VI,0);return new F(function(){return _kK(_);});}};break;default:return function(_){var _1VP=__app2(E(_1VA),E(_1VD),E(_1VG.a));return new F(function(){return _kK(_);});};}});return new F(function(){return A2(_1Vj,_1VC,_1VF);});},_1VQ=function(_1VR){return E(E(_1VR).c);},_1VS=function(_1VT){return E(E(_1VT).b);},_1VU=__Z,_1VV=new T(function(){return eval("(function(x){x.play();})");}),_1VW=function(_1VX){return E(E(_1VX).b);},_1VY=function(_1VZ,_1W0){var _1W1=new T(function(){return B(_1VB(_1VZ,_1W0,_1VU));}),_1W2=B(_1V6(_1VZ)),_1W3=new T(function(){return B(A2(_1VW,B(_1V4(_1W2)),_kJ));}),_1W4=new T(function(){var _1W5=function(_){var _1W6=__app1(E(_1VV),E(_1W0));return new F(function(){return _kK(_);});};return B(A2(_1Vj,_1VZ,_1W5));}),_1W7=function(_1W8){return new F(function(){return A3(_1VQ,_1W2,new T(function(){if(E(_1W8)==2){return E(_1W1);}else{return E(_1W3);}}),_1W4);});};return new F(function(){return A3(_1VS,_1W2,new T(function(){return B(_1Vl(_1VZ,_1W0));}),_1W7);});},_1W9=0,_1Wa=2,_1Wb=2,_1Wc=0,_1Wd=new T2(1,_F,_Z),_1We=new T(function(){return B(_ic("Main.hs:(15,1)-(20,14)|function showTouch"));}),_1Wf=function(_1Wg,_){while(1){var _1Wh=B((function(_1Wi,_){var _1Wj=E(_1Wi);if(!_1Wj._){return E(_1We);}else{var _1Wk=E(_1Wj.a),_1Wl=E(_1Wk.c),_1Wm=E(_1Wk.d),_1Wn=E(_1Wk.e),_1Wo=new T(function(){var _1Wp=new T(function(){var _1Wq=new T(function(){var _1Wr=new T(function(){var _1Ws=new T(function(){var _1Wt=new T(function(){var _1Wu=new T(function(){var _1Wv=new T(function(){var _1Ww=new T(function(){return B(A3(_wK,_aC,new T2(1,function(_1Wx){return new F(function(){return _H(0,E(_1Wn.a),_1Wx);});},new T2(1,function(_1Wy){return new F(function(){return _H(0,E(_1Wn.b),_1Wy);});},_Z)),_1Wd));});return B(unAppCStr("screenCoords:",new T2(1,_G,_1Ww)));},1),_1Wz=new T(function(){return B(A3(_wK,_aC,new T2(1,function(_1WA){return new F(function(){return _H(0,E(_1Wm.a),_1WA);});},new T2(1,function(_1WB){return new F(function(){return _H(0,E(_1Wm.b),_1WB);});},_Z)),_1Wd));});return B(_x(new T2(1,_G,_1Wz),_1Wv));});return B(unAppCStr("clientCoords:",_1Wu));},1),_1WC=new T(function(){return B(A3(_wK,_aC,new T2(1,function(_1WD){return new F(function(){return _H(0,E(_1Wl.a),_1WD);});},new T2(1,function(_1WE){return new F(function(){return _H(0,E(_1Wl.b),_1WE);});},_Z)),_1Wd));});return B(_x(new T2(1,_G,_1WC),_1Wt));});return B(unAppCStr(" pageCoords:",_1Ws));});return B(unAppCStr(" ",_1Wr));});return B(unAppCStr(" target:",_1Wq));},1);return B(_x(B(_H(0,_1Wk.a,_Z)),_1Wp));}),_1WF=B(_1E1(_1HU,B(unAppCStr("idintifier:",_1Wo)),_));_1Wg=_1Wj.b;return __continue;}})(_1Wg,_));if(_1Wh!=__continue){return _1Wh;}}},_1WG=new T(function(){return eval("document");}),_1WH=new T(function(){return eval("(function(id){return document.getElementById(id);})");}),_1WI=new T(function(){return eval("(function(e){return e.getContext(\'2d\');})");}),_1WJ=new T(function(){return eval("(function(e){return !!e.getContext;})");}),_1WK=function(_1WL,_1WM){return new F(function(){return A2(_1Vj,_1WL,function(_){var _1WN=E(_1WM),_1WO=__app1(E(_1WJ),_1WN);if(!_1WO){return _2U;}else{var _1WP=__app1(E(_1WI),_1WN);return new T1(1,new T2(0,_1WP,_1WN));}});});},_1WQ=1,_1WR=new T(function(){var _1WS=E(_1mo);if(!_1WS._){return E(_rm);}else{return {_:0,a:E(_1m2),b:E(B(_1fX(_1lM,5,_1mS))),c:E(_1WQ),d:E(_1WS.a),e:32,f:0,g:E(_Z),h:0,i:E(_Z),j:E(_B2),k:E(_B2)};}}),_1WT=0,_1WU=4,_1WV=new T2(0,_1WU,_1WT),_1WW=new T2(0,_1WT,_1WT),_1WX={_:0,a:E(_B2),b:E(_B2),c:E(_B3),d:E(_B2),e:E(_B2),f:E(_B2),g:E(_B2),h:E(_B2),i:E(_B2)},_1WY=new T(function(){return {_:0,a:E(_1WR),b:E(_1lN),c:E(_1h8),d:E(_Z),e:E(_Z),f:E(_Z),g:E(_Z),h:E(_1WW),i:0,j:0,k:0,l: -1,m:E(_Z),n:0,o:E(_Z),p:E(_Z),q:0,r:E(_Z),s:E(_1WV),t:0,u:E(_1WX),v:E(_Z)};}),_1WZ=new T1(0,100),_1X0=new T(function(){return B(unCStr("Pattern match failure in do expression at Main.hs:34:3-9"));}),_1X1=new T6(0,_2U,_2V,_Z,_1X0,_2U,_2U),_1X2=new T(function(){return B(_2S(_1X1));}),_1X3=new T(function(){return B(unCStr("Pattern match failure in do expression at Main.hs:35:3-8"));}),_1X4=new T6(0,_2U,_2V,_Z,_1X3,_2U,_2U),_1X5=new T(function(){return B(_2S(_1X4));}),_1X6=new T1(1,50),_1X7=function(_1X8){return E(E(_1X8).a);},_1X9=function(_1Xa){return E(E(_1Xa).b);},_1Xb=function(_1Xc){return E(E(_1Xc).a);},_1Xd=function(_){return new F(function(){return nMV(_2U);});},_1Xe=new T(function(){return B(_3d(_1Xd));}),_1Xf=function(_1Xg){return E(E(_1Xg).b);},_1Xh=new T(function(){return eval("(function(e,name,f){e.addEventListener(name,f,false);return [f];})");}),_1Xi=function(_1Xj){return E(E(_1Xj).d);},_1Xk=function(_1Xl,_1Xm,_1Xn,_1Xo,_1Xp,_1Xq){var _1Xr=B(_1X7(_1Xl)),_1Xs=B(_1V6(_1Xr)),_1Xt=new T(function(){return B(_1Vj(_1Xr));}),_1Xu=new T(function(){return B(_1Xi(_1Xs));}),_1Xv=new T(function(){return B(A1(_1Xm,_1Xo));}),_1Xw=new T(function(){return B(A2(_1Xb,_1Xn,_1Xp));}),_1Xx=function(_1Xy){return new F(function(){return A1(_1Xu,new T3(0,_1Xw,_1Xv,_1Xy));});},_1Xz=function(_1XA){var _1XB=new T(function(){var _1XC=new T(function(){var _1XD=__createJSFunc(2,function(_1XE,_){var _1XF=B(A2(E(_1XA),_1XE,_));return _3h;}),_1XG=_1XD;return function(_){return new F(function(){return __app3(E(_1Xh),E(_1Xv),E(_1Xw),_1XG);});};});return B(A1(_1Xt,_1XC));});return new F(function(){return A3(_1VS,_1Xs,_1XB,_1Xx);});},_1XH=new T(function(){var _1XI=new T(function(){return B(_1Vj(_1Xr));}),_1XJ=function(_1XK){var _1XL=new T(function(){return B(A1(_1XI,function(_){var _=wMV(E(_1Xe),new T1(1,_1XK));return new F(function(){return A(_1X9,[_1Xn,_1Xp,_1XK,_]);});}));});return new F(function(){return A3(_1VS,_1Xs,_1XL,_1Xq);});};return B(A2(_1Xf,_1Xl,_1XJ));});return new F(function(){return A3(_1VS,_1Xs,_1XH,_1Xz);});},_1XM=new T(function(){return eval("(function(e){if(e){e.preventDefault();}})");}),_1XN=function(_){var _1XO=rMV(E(_1Xe)),_1XP=E(_1XO);if(!_1XP._){var _1XQ=__app1(E(_1XM),E(_3h));return new F(function(){return _kK(_);});}else{var _1XR=__app1(E(_1XM),E(_1XP.a));return new F(function(){return _kK(_);});}},_1XS=function(_1XT){return new T1(1,E(_1XT));},_1XU=function(_1XV,_1XW){return new F(function(){return A2(_1Xi,B(_1V6(_1XV)),new T1(1,_1XW));});},_1XX=new T2(0,_61,_1XU),_1XY="auto",_1XZ="metadata",_1Y0="none",_1Y1=new T(function(){return new T1(0,"preload");}),_1Y2=new T(function(){return eval("(function(t){return document.createElement(t);})");}),_1Y3=function(_){return new F(function(){return __app1(E(_1Y2),"source");});},_1Y4=new T(function(){return new T1(0,"src");}),_1Y5="audio/wav",_1Y6="audio/ogg",_1Y7="audio/mpeg",_1Y8=new T(function(){return new T1(0,"type");}),_1Y9=new T(function(){return eval("(function(c,p){p.appendChild(c);})");}),_1Ya=function(_1Yb){return E(E(_1Yb).a);},_1Yc=new T(function(){return eval("(function(e,p,v){e.setAttribute(p, v);})");}),_1Yd=new T(function(){return eval("(function(e,p,v){e.style[p] = v;})");}),_1Ye=function(_1Yf,_1Yg,_1Yh,_1Yi){var _1Yj=new T(function(){return B(A2(_1Ya,_1Yf,_1Yh));}),_1Yk=function(_1Yl,_){var _1Ym=E(_1Yl);if(!_1Ym._){return _kJ;}else{var _1Yn=E(_1Yj),_1Yo=E(_1Y9),_1Yp=__app2(_1Yo,E(_1Ym.a),_1Yn),_1Yq=function(_1Yr,_){while(1){var _1Ys=E(_1Yr);if(!_1Ys._){return _kJ;}else{var _1Yt=__app2(_1Yo,E(_1Ys.a),_1Yn);_1Yr=_1Ys.b;continue;}}};return new F(function(){return _1Yq(_1Ym.b,_);});}},_1Yu=function(_1Yv,_){while(1){var _1Yw=B((function(_1Yx,_){var _1Yy=E(_1Yx);if(!_1Yy._){return _kJ;}else{var _1Yz=_1Yy.b,_1YA=E(_1Yy.a);if(!_1YA._){var _1YB=_1YA.b,_1YC=E(_1YA.a);switch(_1YC._){case 0:var _1YD=E(_1Yj),_1YE=E(_m6),_1YF=__app3(_1YE,_1YD,_1YC.a,_1YB),_1YG=function(_1YH,_){while(1){var _1YI=E(_1YH);if(!_1YI._){return _kJ;}else{var _1YJ=_1YI.b,_1YK=E(_1YI.a);if(!_1YK._){var _1YL=_1YK.b,_1YM=E(_1YK.a);switch(_1YM._){case 0:var _1YN=__app3(_1YE,_1YD,_1YM.a,_1YL);_1YH=_1YJ;continue;case 1:var _1YO=__app3(E(_1Yd),_1YD,_1YM.a,_1YL);_1YH=_1YJ;continue;default:var _1YP=__app3(E(_1Yc),_1YD,_1YM.a,_1YL);_1YH=_1YJ;continue;}}else{var _1YQ=B(_1Yk(_1YK.a,_));_1YH=_1YJ;continue;}}}};return new F(function(){return _1YG(_1Yz,_);});break;case 1:var _1YR=E(_1Yj),_1YS=E(_1Yd),_1YT=__app3(_1YS,_1YR,_1YC.a,_1YB),_1YU=function(_1YV,_){while(1){var _1YW=E(_1YV);if(!_1YW._){return _kJ;}else{var _1YX=_1YW.b,_1YY=E(_1YW.a);if(!_1YY._){var _1YZ=_1YY.b,_1Z0=E(_1YY.a);switch(_1Z0._){case 0:var _1Z1=__app3(E(_m6),_1YR,_1Z0.a,_1YZ);_1YV=_1YX;continue;case 1:var _1Z2=__app3(_1YS,_1YR,_1Z0.a,_1YZ);_1YV=_1YX;continue;default:var _1Z3=__app3(E(_1Yc),_1YR,_1Z0.a,_1YZ);_1YV=_1YX;continue;}}else{var _1Z4=B(_1Yk(_1YY.a,_));_1YV=_1YX;continue;}}}};return new F(function(){return _1YU(_1Yz,_);});break;default:var _1Z5=E(_1Yj),_1Z6=E(_1Yc),_1Z7=__app3(_1Z6,_1Z5,_1YC.a,_1YB),_1Z8=function(_1Z9,_){while(1){var _1Za=E(_1Z9);if(!_1Za._){return _kJ;}else{var _1Zb=_1Za.b,_1Zc=E(_1Za.a);if(!_1Zc._){var _1Zd=_1Zc.b,_1Ze=E(_1Zc.a);switch(_1Ze._){case 0:var _1Zf=__app3(E(_m6),_1Z5,_1Ze.a,_1Zd);_1Z9=_1Zb;continue;case 1:var _1Zg=__app3(E(_1Yd),_1Z5,_1Ze.a,_1Zd);_1Z9=_1Zb;continue;default:var _1Zh=__app3(_1Z6,_1Z5,_1Ze.a,_1Zd);_1Z9=_1Zb;continue;}}else{var _1Zi=B(_1Yk(_1Zc.a,_));_1Z9=_1Zb;continue;}}}};return new F(function(){return _1Z8(_1Yz,_);});}}else{var _1Zj=B(_1Yk(_1YA.a,_));_1Yv=_1Yz;return __continue;}}})(_1Yv,_));if(_1Yw!=__continue){return _1Yw;}}};return new F(function(){return A2(_1Vj,_1Yg,function(_){return new F(function(){return _1Yu(_1Yi,_);});});});},_1Zk=function(_1Zl,_1Zm,_1Zn,_1Zo){var _1Zp=B(_1V6(_1Zm)),_1Zq=function(_1Zr){return new F(function(){return A3(_1VQ,_1Zp,new T(function(){return B(_1Ye(_1Zl,_1Zm,_1Zr,_1Zo));}),new T(function(){return B(A2(_1Xi,_1Zp,_1Zr));}));});};return new F(function(){return A3(_1VS,_1Zp,_1Zn,_1Zq);});},_1Zs=function(_1Zt,_){var _1Zu=E(_1Zt);if(!_1Zu._){return _Z;}else{var _1Zv=E(_1Zu.a),_1Zw=B(A(_1Zk,[_1XX,_63,_1Y3,new T2(1,new T(function(){var _1Zx=E(_1Y8);switch(E(_1Zv.a)){case 0:return new T2(0,E(_1Zx),E(_1Y7));break;case 1:return new T2(0,E(_1Zx),E(_1Y6));break;default:return new T2(0,E(_1Zx),E(_1Y5));}}),new T2(1,new T(function(){return new T2(0,E(_1Y4),_1Zv.b);}),_Z)),_])),_1Zy=B(_1Zs(_1Zu.b,_));return new T2(1,_1Zw,_1Zy);}},_1Zz=new T(function(){return new T1(0,"volume");}),_1ZA=new T(function(){return new T1(0,"muted");}),_1ZB=new T(function(){return new T1(0,"loop");}),_1ZC=new T(function(){return new T1(0,"autoplay");}),_1ZD="true",_1ZE=new T(function(){return toJSStr(_Z);}),_1ZF=new T(function(){return new T1(0,"controls");}),_1ZG=function(_){return new F(function(){return __app1(E(_1Y2),"audio");});},_1ZH=function(_1ZI,_1ZJ,_1ZK){var _1ZL=function(_){var _1ZM=B(_1Zs(_1ZK,_)),_1ZN=B(A(_1Zk,[_1XX,_63,_1ZG,new T2(1,new T(function(){var _1ZO=E(_1ZF);if(!E(E(_1ZJ).a)){return new T2(0,E(_1ZO),E(_1ZE));}else{return new T2(0,E(_1ZO),E(_1ZD));}}),new T2(1,new T(function(){var _1ZP=E(_1ZC);if(!E(E(_1ZJ).b)){return new T2(0,E(_1ZP),E(_1ZE));}else{return new T2(0,E(_1ZP),E(_1ZD));}}),new T2(1,new T(function(){var _1ZQ=E(_1ZB);if(!E(E(_1ZJ).c)){return new T2(0,E(_1ZQ),E(_1ZE));}else{return new T2(0,E(_1ZQ),E(_1ZD));}}),new T2(1,new T(function(){var _1ZR=E(_1ZA);if(!E(E(_1ZJ).e)){return new T2(0,E(_1ZR),E(_1ZE));}else{return new T2(0,E(_1ZR),E(_1ZD));}}),new T2(1,new T(function(){var _1ZS=String(E(_1ZJ).f);return new T2(0,E(_1Zz),_1ZS);}),new T2(1,new T(function(){var _1ZT=E(_1Y1);switch(E(E(_1ZJ).d)){case 0:return new T2(0,E(_1ZT),E(_1Y0));break;case 1:return new T2(0,E(_1ZT),E(_1XZ));break;default:return new T2(0,E(_1ZT),E(_1XY));}}),new T2(1,new T(function(){return B(_1XS(_1ZM));}),_Z))))))),_]));return new T1(0,_1ZN);};return new F(function(){return A2(_1Vj,_1ZI,_1ZL);});},_1ZU=new T(function(){return B(unCStr("vaw"));}),_1ZV=new T(function(){return B(unCStr("ggo"));}),_1ZW=new T(function(){return B(unCStr("3pm"));}),_1ZX=0,_1ZY=1,_1ZZ=2,_200=function(_201){var _202=B(_uj(3,B(_KR(fromJSStr(_201),_Z))));return (!B(_vl(_202,_1ZW)))?(!B(_vl(_202,_1ZV)))?(!B(_vl(_202,_1ZU)))?__Z:new T1(1,new T2(0,E(_1ZZ),_201)):new T1(1,new T2(0,E(_1ZY),_201)):new T1(1,new T2(0,E(_1ZX),_201));},_203="Audio/test.mp3",_204=new T(function(){var _205=B(_200(E(_203)));if(!_205._){return B(_PU("Browser.hs:99:7-37|Just adSrc"));}else{return E(_205.a);}}),_206=new T2(1,_204,_Z),_207=2,_208=new T6(0,E(_B2),E(_B2),E(_B3),E(_207),E(_B2),1),_209=new T(function(){return B(_1ZH(_63,_208,_206));}),_20a="src",_20b=new T(function(){return B(unCStr("img"));}),_20c=function(_20d,_20e){return new F(function(){return A2(_1Vj,_20d,function(_){var _20f=__app1(E(_1Y2),toJSStr(E(_20b))),_20g=__app3(E(_m6),_20f,E(_20a),E(_20e));return _20f;});});},_20h=new T(function(){return B(unCStr(".png"));}),_20i=function(_20j,_20k){var _20l=E(_20j);if(_20l==( -1)){return __Z;}else{var _20m=new T(function(){var _20n=new T(function(){return toJSStr(B(_x(_20k,new T(function(){return B(_x(B(_H(0,_20l,_Z)),_20h));},1))));});return B(_20c(_63,_20n));});return new F(function(){return _x(B(_20i(_20l-1|0,_20k)),new T2(1,_20m,_Z));});}},_20o=new T(function(){return B(unCStr("Images/Wst/wst"));}),_20p=new T(function(){return B(_20i(120,_20o));}),_20q=function(_20r,_){var _20s=E(_20r);if(!_20s._){return _Z;}else{var _20t=B(A1(_20s.a,_)),_20u=B(_20q(_20s.b,_));return new T2(1,_20t,_20u);}},_20v=new T(function(){return B(unCStr("Images/Chara/ch"));}),_20w=new T(function(){return B(_20i(56,_20v));}),_20x=function(_20y,_){var _20z=E(_20y);if(!_20z._){return _Z;}else{var _20A=B(A1(_20z.a,_)),_20B=B(_20x(_20z.b,_));return new T2(1,_20A,_20B);}},_20C=new T(function(){return B(unCStr("Images/img"));}),_20D=new T(function(){return B(_20i(5,_20C));}),_20E=function(_20F,_){var _20G=E(_20F);if(!_20G._){return _Z;}else{var _20H=B(A1(_20G.a,_)),_20I=B(_20E(_20G.b,_));return new T2(1,_20H,_20I);}},_20J=new T(function(){return eval("(function(t,f){return window.setInterval(f,t);})");}),_20K=new T(function(){return eval("(function(t,f){return window.setTimeout(f,t);})");}),_20L=function(_20M,_20N,_20O){var _20P=B(_1X7(_20M)),_20Q=new T(function(){return B(_1Vj(_20P));}),_20R=function(_20S){var _20T=function(_){var _20U=E(_20N);if(!_20U._){var _20V=B(A1(_20S,_kJ)),_20W=__createJSFunc(0,function(_){var _20X=B(A1(_20V,_));return _3h;}),_20Y=__app2(E(_20K),_20U.a,_20W);return new T(function(){var _20Z=Number(_20Y),_210=jsTrunc(_20Z);return new T2(0,_210,E(_20U));});}else{var _211=B(A1(_20S,_kJ)),_212=__createJSFunc(0,function(_){var _213=B(A1(_211,_));return _3h;}),_214=__app2(E(_20J),_20U.a,_212);return new T(function(){var _215=Number(_214),_216=jsTrunc(_215);return new T2(0,_216,E(_20U));});}};return new F(function(){return A1(_20Q,_20T);});},_217=new T(function(){return B(A2(_1Xf,_20M,function(_218){return E(_20O);}));});return new F(function(){return A3(_1VS,B(_1V6(_20P)),_217,_20R);});},_219=function(_21a){var _21b=E(_21a),_21c=E(_21b.a),_21d=new T(function(){return B(_x(_21c.b,new T(function(){return B(unAppCStr(" >>",_21c.c));},1)));});return new T2(0,new T2(1,_21b.b,_1sK),_21d);},_21e=function(_){var _21f=B(_20E(_20D,_)),_21g=B(_20x(_20w,_)),_21h=B(_20q(_20p,_)),_21i=B(A1(_209,_)),_21j=_21i,_21k=__app1(E(_1WH),"canvas"),_21l=__eq(_21k,E(_3h));if(!E(_21l)){var _21m=__isUndef(_21k);if(!E(_21m)){var _21n=B(A3(_1WK,_63,_21k,_)),_21o=E(_21n);if(!_21o._){return new F(function(){return die(_1X5);});}else{var _21p=E(_21o.a),_21q=_21p.b,_21r=B(_a8(_21q,_)),_21s=_21r,_21t=nMV(_1WY),_21u=_21t,_21v=new T3(0,_21f,_21g,_21h),_21w=B(A(_1Xk,[_64,_3K,_t,_1WG,_1Wa,function(_21x,_){var _21y=B(_1XN(_)),_21z=rMV(_21u),_21A=E(E(_21s).a),_21B=E(_21z),_21C=E(_21B.a),_21D=E(_21B.b),_21E=E(_21B.h),_21F=E(_21B.s),_21G=E(_21B.u),_21H=B(_1IH(_21p,_21A.a,_21A.b,_21v,E(_21x).a,_21C.a,_21C.b,_21C.c,_21C.d,_21C.e,_21C.f,_21C.g,_21C.h,_21C.i,_21C.j,_21C.k,_21D.a,_21D.b,_21B.c,_21B.d,_21B.e,_21B.f,_21B.g,_21E.a,_21E.b,_21B.i,_21B.j,_21B.k,_21B.l,_21B.m,_21B.n,_21B.o,_21B.p,_21B.q,_21B.r,_21F.a,_21F.b,_21B.t,_21G.a,_21G.b,_21G.c,_21G.d,_21G.e,_21G.f,_21G.g,_21G.h,_21G.i,_21B.v,_)),_=wMV(_21u,_21H);return _kJ;},_])),_21I=B(A(_1Xk,[_64,_3K,_3J,_21k,_1W9,function(_21J,_){var _21K=E(E(_21J).a),_21L=_21K.a,_21M=_21K.b,_21N=rMV(_21u),_21O=E(_21N),_21P=E(_21O.u);if(!E(_21P.i)){var _21Q=B(A3(_1VY,_63,E(_21j).a,_)),_21R=B(A(_1UI,[_21p,_21s,_21v,_21L,_21M,{_:0,a:E(_21O.a),b:E(_21O.b),c:E(_21O.c),d:E(_21O.d),e:E(_21O.e),f:E(_21O.f),g:E(_21O.g),h:E(_21O.h),i:_21O.i,j:_21O.j,k:_21O.k,l:_21O.l,m:E(_21O.m),n:_21O.n,o:E(_21O.o),p:E(_21O.p),q:_21O.q,r:E(_21O.r),s:E(_21O.s),t:_21O.t,u:E({_:0,a:E(_21P.a),b:E(_21P.b),c:E(_21P.c),d:E(_21P.d),e:E(_21P.e),f:E(_21P.f),g:E(_21P.g),h:E(_21P.h),i:E(_B3)}),v:E(_21O.v)},_])),_=wMV(_21u,_21R);return _kJ;}else{var _21S=B(A(_1UI,[_21p,_21s,_21v,_21L,_21M,_21O,_])),_=wMV(_21u,_21S);return _kJ;}},_])),_21T=B(A(_1Xk,[_64,_3K,_5j,_21k,_1Wc,function(_21U,_){var _21V=E(_21U),_21W=B(_1Wf(_21V.a,_)),_21X=B(_1Wf(_21V.b,_)),_21Y=B(_1Wf(_21V.c,_)),_21Z=rMV(_21u),_220=E(_21Z);if(!E(E(_220.u).e)){var _=wMV(_21u,_220);return _kJ;}else{var _221=B(_1XN(_)),_=wMV(_21u,_220);return _kJ;}},_])),_222=function(_){var _223=rMV(_21u),_=wMV(_21u,new T(function(){var _224=E(_223),_225=E(_224.u);return {_:0,a:E(_224.a),b:E(_224.b),c:E(_224.c),d:E(_224.d),e:E(_224.e),f:E(_224.f),g:E(_224.g),h:E(_224.h),i:_224.i,j:_224.j,k:_224.k,l:_224.l,m:E(_224.m),n:_224.n,o:E(_224.o),p:E(_224.p),q:_224.q,r:E(_224.r),s:E(_224.s),t:_224.t,u:E({_:0,a:E(_225.a),b:E(_225.b),c:E(_225.c),d:E(_225.d),e:E(_B2),f:E(_225.f),g:E(_225.g),h:E(_225.h),i:E(_225.i)}),v:E(_224.v)};}));return _kJ;},_226=function(_227,_){var _228=E(_227),_229=rMV(_21u),_=wMV(_21u,new T(function(){var _22a=E(_229),_22b=E(_22a.u);return {_:0,a:E(_22a.a),b:E(_22a.b),c:E(_22a.c),d:E(_22a.d),e:E(_22a.e),f:E(_22a.f),g:E(_22a.g),h:E(_22a.h),i:_22a.i,j:_22a.j,k:_22a.k,l:_22a.l,m:E(_22a.m),n:_22a.n,o:E(_22a.o),p:E(_22a.p),q:_22a.q,r:E(_22a.r),s:E(_22a.s),t:_22a.t,u:E({_:0,a:E(_22b.a),b:E(_22b.b),c:E(_22b.c),d:E(_22b.d),e:E(_B3),f:E(_22b.f),g:E(_22b.g),h:E(_22b.h),i:E(_22b.i)}),v:E(_22a.v)};})),_22c=B(A(_20L,[_64,_1WZ,_222,_]));return _kJ;},_22d=B(A(_1Xk,[_64,_3K,_5j,_21k,_1Wb,_226,_])),_22e=function(_){var _22f=rMV(_21u),_22g=E(_22f),_22h=_22g.a,_22i=_22g.b,_22j=_22g.c,_22k=_22g.d,_22l=_22g.e,_22m=_22g.f,_22n=_22g.g,_22o=_22g.h,_22p=_22g.i,_22q=_22g.j,_22r=_22g.k,_22s=_22g.l,_22t=_22g.m,_22u=_22g.n,_22v=_22g.o,_22w=_22g.p,_22x=_22g.q,_22y=_22g.r,_22z=_22g.s,_22A=_22g.t,_22B=_22g.v,_22C=E(_22g.u),_22D=new T(function(){if(_22A<=298){return _22A+1|0;}else{return E(_1HZ);}}),_22E=new T(function(){var _22F=function(_22G){var _22H=E(_22G);return (_22H==30)?{_:0,a:E(_22h),b:E(_22i),c:E(_22j),d:E(B(_x(B(_0(_Z,B(_1IC(B(_aj(_1Gp,_22w)),B(_9T(_22k)))))),new T(function(){return B(_aj(_219,_22w));},1)))),e:E(_22l),f:E(_22m),g:E(_22n),h:E(_22o),i:_22p,j:_22q,k:_22r,l:_22s,m:E(_22t),n:_22u,o:E(_22v),p:E(_22w),q:30,r:E(_22y),s:E(_22z),t:E(_22D),u:E(_22C),v:E(_22B)}:{_:0,a:E(_22h),b:E(_22i),c:E(_22j),d:E(_22k),e:E(_22l),f:E(_22m),g:E(_22n),h:E(_22o),i:_22p,j:_22q,k:_22r,l:_22s,m:E(_22t),n:_22u,o:E(_22v),p:E(_22w),q:_22H,r:E(_22y),s:E(_22z),t:E(_22D),u:E(_22C),v:E(_22B)};};if(!E(_22w)._){return B(_22F(_22x));}else{if(!B(_et(E(_22D),20))){return B(_22F(_22x+1|0));}else{return B(_22F(_22x));}}});if(!E(_22C.b)){if(!E(_22C.h)){var _22I=E(E(_21s).a),_22J=E(_22E),_22K=E(_22J.b),_22L=E(_22J.h),_22M=E(_22J.u),_22N=B(_12Q(_21p,_22I.a,_22I.b,_21v,_22J.a,_22K.a,_22K.b,_22J.c,_22J.d,_22J.e,_22J.f,_22J.g,_22L.a,_22L.b,_22J.i,_22J.j,_22J.k,_22J.l,_22J.m,_22J.n,_22J.o,_22J.p,_22J.q,_22J.r,_22J.s,_22J.t,_22M.a,_22M.b,_22M.c,_22M.d,_22M.e,_22M.f,_22M.g,_22M.h,_22M.i,_22J.v,_)),_=wMV(_21u,_22N);return _kJ;}else{if(!B(_et(E(_22D),10))){if(!E(_22C.c)){var _22O=E(E(_21s).a),_22P=B(_1bL(_21p.a,_21q,_22O.a,_22O.b,_21v,_22E,_)),_=wMV(_21u,_22P);return _kJ;}else{var _22Q=E(E(_21s).a),_22R=E(_22E),_22S=E(_22R.b),_22T=E(_22R.h),_22U=E(_22R.u),_22V=B(_12Q(_21p,_22Q.a,_22Q.b,_21v,_22R.a,_22S.a,_22S.b,_22R.c,_22R.d,_22R.e,_22R.f,_22R.g,_22T.a,_22T.b,_22R.i,_22R.j,_22R.k,_22R.l,_22R.m,_22R.n,_22R.o,_22R.p,_22R.q,_22R.r,_22R.s,_22R.t,_22U.a,_22U.b,_22U.c,_22U.d,_22U.e,_22U.f,_22U.g,_22U.h,_22U.i,_22R.v,_)),_=wMV(_21u,_22V);return _kJ;}}else{var _22W=E(E(_21s).a),_22X=E(_22E),_22Y=E(_22X.b),_22Z=E(_22X.h),_230=E(_22X.u),_231=B(_12Q(_21p,_22W.a,_22W.b,_21v,_22X.a,_22Y.a,_22Y.b,_22X.c,_22X.d,_22X.e,_22X.f,_22X.g,_22Z.a,_22Z.b,_22X.i,_22X.j,_22X.k,_22X.l,_22X.m,_22X.n,_22X.o,_22X.p,_22X.q,_22X.r,_22X.s,_22X.t,_230.a,_230.b,_230.c,_230.d,_230.e,_230.f,_230.g,_230.h,_230.i,_22X.v,_)),_=wMV(_21u,_231);return _kJ;}}}else{var _=wMV(_21u,_22E);return _kJ;}},_232=B(A(_20L,[_64,_1X6,_22e,_]));return _kJ;}}else{return new F(function(){return die(_1X2);});}}else{return new F(function(){return die(_1X2);});}},_233=function(_){return new F(function(){return _21e(_);});};
var hasteMain = function() {B(A(_233, [0]));};window.onload = hasteMain;