"use strict";
var __haste_prog_id = 'cc387ce5fb4c59aae9f1e045ca7ee53ec1fa51ea660be1a817a05658747d3f47';
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

var _0=function(_1,_2){while(1){var _3=B((function(_4,_5){var _6=E(_5);if(!_6._){_1=new T2(1,new T2(0,_6.b,_6.c),new T(function(){return B(_0(_4,_6.e));}));_2=_6.d;return __continue;}else{return E(_4);}})(_1,_2));if(_3!=__continue){return _3;}}},_7="metaKey",_8="shiftKey",_9="altKey",_a="ctrlKey",_b="keyCode",_c=function(_d,_){var _e=__get(_d,E(_b)),_f=__get(_d,E(_a)),_g=__get(_d,E(_9)),_h=__get(_d,E(_8)),_i=__get(_d,E(_7));return new T(function(){var _j=Number(_e),_k=jsTrunc(_j);return new T5(0,_k,E(_f),E(_g),E(_h),E(_i));});},_l=function(_m,_n,_){return new F(function(){return _c(E(_n),_);});},_o="keydown",_p="keyup",_q="keypress",_r=function(_s){switch(E(_s)){case 0:return E(_q);case 1:return E(_p);default:return E(_o);}},_t=new T2(0,_r,_l),_u="deltaZ",_v="deltaY",_w="deltaX",_x=function(_y,_z){var _A=E(_y);return (_A._==0)?E(_z):new T2(1,_A.a,new T(function(){return B(_x(_A.b,_z));}));},_B=function(_C,_D){var _E=jsShowI(_C);return new F(function(){return _x(fromJSStr(_E),_D);});},_F=41,_G=40,_H=function(_I,_J,_K){if(_J>=0){return new F(function(){return _B(_J,_K);});}else{if(_I<=6){return new F(function(){return _B(_J,_K);});}else{return new T2(1,_G,new T(function(){var _L=jsShowI(_J);return B(_x(fromJSStr(_L),new T2(1,_F,_K)));}));}}},_M=new T(function(){return B(unCStr(")"));}),_N=new T(function(){return B(_H(0,2,_M));}),_O=new T(function(){return B(unAppCStr(") is outside of enumeration\'s range (0,",_N));}),_P=function(_Q){return new F(function(){return err(B(unAppCStr("toEnum{MouseButton}: tag (",new T(function(){return B(_H(0,_Q,_O));}))));});},_R=function(_S,_){return new T(function(){var _T=Number(E(_S)),_U=jsTrunc(_T);if(_U<0){return B(_P(_U));}else{if(_U>2){return B(_P(_U));}else{return _U;}}});},_V=0,_W=new T3(0,_V,_V,_V),_X="button",_Y=new T(function(){return eval("jsGetMouseCoords");}),_Z=__Z,_10=function(_11,_){var _12=E(_11);if(!_12._){return _Z;}else{var _13=B(_10(_12.b,_));return new T2(1,new T(function(){var _14=Number(E(_12.a));return jsTrunc(_14);}),_13);}},_15=function(_16,_){var _17=__arr2lst(0,_16);return new F(function(){return _10(_17,_);});},_18=function(_19,_){return new F(function(){return _15(E(_19),_);});},_1a=function(_1b,_){return new T(function(){var _1c=Number(E(_1b));return jsTrunc(_1c);});},_1d=new T2(0,_1a,_18),_1e=function(_1f,_){var _1g=E(_1f);if(!_1g._){return _Z;}else{var _1h=B(_1e(_1g.b,_));return new T2(1,_1g.a,_1h);}},_1i=new T(function(){return B(unCStr("base"));}),_1j=new T(function(){return B(unCStr("GHC.IO.Exception"));}),_1k=new T(function(){return B(unCStr("IOException"));}),_1l=new T5(0,new Long(4053623282,1685460941,true),new Long(3693590983,2507416641,true),_1i,_1j,_1k),_1m=new T5(0,new Long(4053623282,1685460941,true),new Long(3693590983,2507416641,true),_1l,_Z,_Z),_1n=function(_1o){return E(_1m);},_1p=function(_1q){return E(E(_1q).a);},_1r=function(_1s,_1t,_1u){var _1v=B(A1(_1s,_)),_1w=B(A1(_1t,_)),_1x=hs_eqWord64(_1v.a,_1w.a);if(!_1x){return __Z;}else{var _1y=hs_eqWord64(_1v.b,_1w.b);return (!_1y)?__Z:new T1(1,_1u);}},_1z=function(_1A){var _1B=E(_1A);return new F(function(){return _1r(B(_1p(_1B.a)),_1n,_1B.b);});},_1C=new T(function(){return B(unCStr(": "));}),_1D=new T(function(){return B(unCStr(")"));}),_1E=new T(function(){return B(unCStr(" ("));}),_1F=new T(function(){return B(unCStr("interrupted"));}),_1G=new T(function(){return B(unCStr("system error"));}),_1H=new T(function(){return B(unCStr("unsatisified constraints"));}),_1I=new T(function(){return B(unCStr("user error"));}),_1J=new T(function(){return B(unCStr("permission denied"));}),_1K=new T(function(){return B(unCStr("illegal operation"));}),_1L=new T(function(){return B(unCStr("end of file"));}),_1M=new T(function(){return B(unCStr("resource exhausted"));}),_1N=new T(function(){return B(unCStr("resource busy"));}),_1O=new T(function(){return B(unCStr("does not exist"));}),_1P=new T(function(){return B(unCStr("already exists"));}),_1Q=new T(function(){return B(unCStr("resource vanished"));}),_1R=new T(function(){return B(unCStr("timeout"));}),_1S=new T(function(){return B(unCStr("unsupported operation"));}),_1T=new T(function(){return B(unCStr("hardware fault"));}),_1U=new T(function(){return B(unCStr("inappropriate type"));}),_1V=new T(function(){return B(unCStr("invalid argument"));}),_1W=new T(function(){return B(unCStr("failed"));}),_1X=new T(function(){return B(unCStr("protocol error"));}),_1Y=function(_1Z,_20){switch(E(_1Z)){case 0:return new F(function(){return _x(_1P,_20);});break;case 1:return new F(function(){return _x(_1O,_20);});break;case 2:return new F(function(){return _x(_1N,_20);});break;case 3:return new F(function(){return _x(_1M,_20);});break;case 4:return new F(function(){return _x(_1L,_20);});break;case 5:return new F(function(){return _x(_1K,_20);});break;case 6:return new F(function(){return _x(_1J,_20);});break;case 7:return new F(function(){return _x(_1I,_20);});break;case 8:return new F(function(){return _x(_1H,_20);});break;case 9:return new F(function(){return _x(_1G,_20);});break;case 10:return new F(function(){return _x(_1X,_20);});break;case 11:return new F(function(){return _x(_1W,_20);});break;case 12:return new F(function(){return _x(_1V,_20);});break;case 13:return new F(function(){return _x(_1U,_20);});break;case 14:return new F(function(){return _x(_1T,_20);});break;case 15:return new F(function(){return _x(_1S,_20);});break;case 16:return new F(function(){return _x(_1R,_20);});break;case 17:return new F(function(){return _x(_1Q,_20);});break;default:return new F(function(){return _x(_1F,_20);});}},_21=new T(function(){return B(unCStr("}"));}),_22=new T(function(){return B(unCStr("{handle: "));}),_23=function(_24,_25,_26,_27,_28,_29){var _2a=new T(function(){var _2b=new T(function(){var _2c=new T(function(){var _2d=E(_27);if(!_2d._){return E(_29);}else{var _2e=new T(function(){return B(_x(_2d,new T(function(){return B(_x(_1D,_29));},1)));},1);return B(_x(_1E,_2e));}},1);return B(_1Y(_25,_2c));}),_2f=E(_26);if(!_2f._){return E(_2b);}else{return B(_x(_2f,new T(function(){return B(_x(_1C,_2b));},1)));}}),_2g=E(_28);if(!_2g._){var _2h=E(_24);if(!_2h._){return E(_2a);}else{var _2i=E(_2h.a);if(!_2i._){var _2j=new T(function(){var _2k=new T(function(){return B(_x(_21,new T(function(){return B(_x(_1C,_2a));},1)));},1);return B(_x(_2i.a,_2k));},1);return new F(function(){return _x(_22,_2j);});}else{var _2l=new T(function(){var _2m=new T(function(){return B(_x(_21,new T(function(){return B(_x(_1C,_2a));},1)));},1);return B(_x(_2i.a,_2m));},1);return new F(function(){return _x(_22,_2l);});}}}else{return new F(function(){return _x(_2g.a,new T(function(){return B(_x(_1C,_2a));},1));});}},_2n=function(_2o){var _2p=E(_2o);return new F(function(){return _23(_2p.a,_2p.b,_2p.c,_2p.d,_2p.f,_Z);});},_2q=function(_2r,_2s,_2t){var _2u=E(_2s);return new F(function(){return _23(_2u.a,_2u.b,_2u.c,_2u.d,_2u.f,_2t);});},_2v=function(_2w,_2x){var _2y=E(_2w);return new F(function(){return _23(_2y.a,_2y.b,_2y.c,_2y.d,_2y.f,_2x);});},_2z=44,_2A=93,_2B=91,_2C=function(_2D,_2E,_2F){var _2G=E(_2E);if(!_2G._){return new F(function(){return unAppCStr("[]",_2F);});}else{var _2H=new T(function(){var _2I=new T(function(){var _2J=function(_2K){var _2L=E(_2K);if(!_2L._){return E(new T2(1,_2A,_2F));}else{var _2M=new T(function(){return B(A2(_2D,_2L.a,new T(function(){return B(_2J(_2L.b));})));});return new T2(1,_2z,_2M);}};return B(_2J(_2G.b));});return B(A2(_2D,_2G.a,_2I));});return new T2(1,_2B,_2H);}},_2N=function(_2O,_2P){return new F(function(){return _2C(_2v,_2O,_2P);});},_2Q=new T3(0,_2q,_2n,_2N),_2R=new T(function(){return new T5(0,_1n,_2Q,_2S,_1z,_2n);}),_2S=function(_2T){return new T2(0,_2R,_2T);},_2U=__Z,_2V=7,_2W=new T(function(){return B(unCStr("Pattern match failure in do expression at src/Haste/Prim/Any.hs:268:5-9"));}),_2X=new T6(0,_2U,_2V,_Z,_2W,_2U,_2U),_2Y=new T(function(){return B(_2S(_2X));}),_2Z=function(_){return new F(function(){return die(_2Y);});},_30=function(_31){return E(E(_31).a);},_32=function(_33,_34,_35,_){var _36=__arr2lst(0,_35),_37=B(_1e(_36,_)),_38=E(_37);if(!_38._){return new F(function(){return _2Z(_);});}else{var _39=E(_38.b);if(!_39._){return new F(function(){return _2Z(_);});}else{if(!E(_39.b)._){var _3a=B(A3(_30,_33,_38.a,_)),_3b=B(A3(_30,_34,_39.a,_));return new T2(0,_3a,_3b);}else{return new F(function(){return _2Z(_);});}}}},_3c=function(_){return new F(function(){return __jsNull();});},_3d=function(_3e){var _3f=B(A1(_3e,_));return E(_3f);},_3g=new T(function(){return B(_3d(_3c));}),_3h=new T(function(){return E(_3g);}),_3i=function(_3j,_3k,_){if(E(_3j)==7){var _3l=__app1(E(_Y),_3k),_3m=B(_32(_1d,_1d,_3l,_)),_3n=__get(_3k,E(_w)),_3o=__get(_3k,E(_v)),_3p=__get(_3k,E(_u));return new T(function(){return new T3(0,E(_3m),E(_2U),E(new T3(0,_3n,_3o,_3p)));});}else{var _3q=__app1(E(_Y),_3k),_3r=B(_32(_1d,_1d,_3q,_)),_3s=__get(_3k,E(_X)),_3t=__eq(_3s,E(_3h));if(!E(_3t)){var _3u=__isUndef(_3s);if(!E(_3u)){var _3v=B(_R(_3s,_));return new T(function(){return new T3(0,E(_3r),E(new T1(1,_3v)),E(_W));});}else{return new T(function(){return new T3(0,E(_3r),E(_2U),E(_W));});}}else{return new T(function(){return new T3(0,E(_3r),E(_2U),E(_W));});}}},_3w=function(_3x,_3y,_){return new F(function(){return _3i(_3x,E(_3y),_);});},_3z="mouseout",_3A="mouseover",_3B="mousemove",_3C="mouseup",_3D="mousedown",_3E="dblclick",_3F="click",_3G="wheel",_3H=function(_3I){switch(E(_3I)){case 0:return E(_3F);case 1:return E(_3E);case 2:return E(_3D);case 3:return E(_3C);case 4:return E(_3B);case 5:return E(_3A);case 6:return E(_3z);default:return E(_3G);}},_3J=new T2(0,_3H,_3w),_3K=function(_3L){return E(_3L);},_3M=function(_3N,_3O){return E(_3N)==E(_3O);},_3P=function(_3Q,_3R){return E(_3Q)!=E(_3R);},_3S=new T2(0,_3M,_3P),_3T="screenY",_3U="screenX",_3V="clientY",_3W="clientX",_3X="pageY",_3Y="pageX",_3Z="target",_40="identifier",_41=function(_42,_){var _43=__get(_42,E(_40)),_44=__get(_42,E(_3Z)),_45=__get(_42,E(_3Y)),_46=__get(_42,E(_3X)),_47=__get(_42,E(_3W)),_48=__get(_42,E(_3V)),_49=__get(_42,E(_3U)),_4a=__get(_42,E(_3T));return new T(function(){var _4b=Number(_43),_4c=jsTrunc(_4b);return new T5(0,_4c,_44,E(new T2(0,new T(function(){var _4d=Number(_45);return jsTrunc(_4d);}),new T(function(){var _4e=Number(_46);return jsTrunc(_4e);}))),E(new T2(0,new T(function(){var _4f=Number(_47);return jsTrunc(_4f);}),new T(function(){var _4g=Number(_48);return jsTrunc(_4g);}))),E(new T2(0,new T(function(){var _4h=Number(_49);return jsTrunc(_4h);}),new T(function(){var _4i=Number(_4a);return jsTrunc(_4i);}))));});},_4j=function(_4k,_){var _4l=E(_4k);if(!_4l._){return _Z;}else{var _4m=B(_41(E(_4l.a),_)),_4n=B(_4j(_4l.b,_));return new T2(1,_4m,_4n);}},_4o="touches",_4p=function(_4q){return E(E(_4q).b);},_4r=function(_4s,_4t,_){var _4u=__arr2lst(0,_4t),_4v=new T(function(){return B(_4p(_4s));}),_4w=function(_4x,_){var _4y=E(_4x);if(!_4y._){return _Z;}else{var _4z=B(A2(_4v,_4y.a,_)),_4A=B(_4w(_4y.b,_));return new T2(1,_4z,_4A);}};return new F(function(){return _4w(_4u,_);});},_4B=function(_4C,_){return new F(function(){return _4r(_1d,E(_4C),_);});},_4D=new T2(0,_18,_4B),_4E=new T(function(){return eval("(function(e) {  var len = e.changedTouches.length;  var chts = new Array(len);  for(var i = 0; i < len; ++i) {chts[i] = e.changedTouches[i].identifier;}  var len = e.targetTouches.length;  var tts = new Array(len);  for(var i = 0; i < len; ++i) {tts[i] = e.targetTouches[i].identifier;}  return [chts, tts];})");}),_4F=function(_4G){return E(E(_4G).a);},_4H=function(_4I,_4J,_4K){while(1){var _4L=E(_4K);if(!_4L._){return false;}else{if(!B(A3(_4F,_4I,_4J,_4L.a))){_4K=_4L.b;continue;}else{return true;}}}},_4M=function(_4N,_4O){while(1){var _4P=B((function(_4Q,_4R){var _4S=E(_4R);if(!_4S._){return __Z;}else{var _4T=_4S.a,_4U=_4S.b;if(!B(A1(_4Q,_4T))){var _4V=_4Q;_4N=_4V;_4O=_4U;return __continue;}else{return new T2(1,_4T,new T(function(){return B(_4M(_4Q,_4U));}));}}})(_4N,_4O));if(_4P!=__continue){return _4P;}}},_4W=function(_4X,_){var _4Y=__get(_4X,E(_4o)),_4Z=__arr2lst(0,_4Y),_50=B(_4j(_4Z,_)),_51=__app1(E(_4E),_4X),_52=B(_32(_4D,_4D,_51,_)),_53=E(_52),_54=new T(function(){var _55=function(_56){return new F(function(){return _4H(_3S,new T(function(){return E(_56).a;}),_53.a);});};return B(_4M(_55,_50));}),_57=new T(function(){var _58=function(_59){return new F(function(){return _4H(_3S,new T(function(){return E(_59).a;}),_53.b);});};return B(_4M(_58,_50));});return new T3(0,_50,_57,_54);},_5a=function(_5b,_5c,_){return new F(function(){return _4W(E(_5c),_);});},_5d="touchcancel",_5e="touchend",_5f="touchmove",_5g="touchstart",_5h=function(_5i){switch(E(_5i)){case 0:return E(_5g);case 1:return E(_5f);case 2:return E(_5e);default:return E(_5d);}},_5j=new T2(0,_5h,_5a),_5k=function(_5l,_5m,_){var _5n=B(A1(_5l,_)),_5o=B(A1(_5m,_));return _5n;},_5p=function(_5q,_5r,_){var _5s=B(A1(_5q,_)),_5t=B(A1(_5r,_));return new T(function(){return B(A1(_5s,_5t));});},_5u=function(_5v,_5w,_){var _5x=B(A1(_5w,_));return _5v;},_5y=function(_5z,_5A,_){var _5B=B(A1(_5A,_));return new T(function(){return B(A1(_5z,_5B));});},_5C=new T2(0,_5y,_5u),_5D=function(_5E,_){return _5E;},_5F=function(_5G,_5H,_){var _5I=B(A1(_5G,_));return new F(function(){return A1(_5H,_);});},_5J=new T5(0,_5C,_5D,_5p,_5F,_5k),_5K=new T(function(){return E(_2R);}),_5L=function(_5M){return E(E(_5M).c);},_5N=function(_5O){return new T6(0,_2U,_2V,_Z,_5O,_2U,_2U);},_5P=function(_5Q,_){var _5R=new T(function(){return B(A2(_5L,_5K,new T(function(){return B(A1(_5N,_5Q));})));});return new F(function(){return die(_5R);});},_5S=function(_5T,_){return new F(function(){return _5P(_5T,_);});},_5U=function(_5V){return new F(function(){return A1(_5S,_5V);});},_5W=function(_5X,_5Y,_){var _5Z=B(A1(_5X,_));return new F(function(){return A2(_5Y,_5Z,_);});},_60=new T5(0,_5J,_5W,_5F,_5D,_5U),_61=function(_62){return E(_62);},_63=new T2(0,_60,_61),_64=new T2(0,_63,_5D),_65=function(_66,_67){while(1){var _68=E(_66);if(!_68._){return (E(_67)._==0)?1:0;}else{var _69=E(_67);if(!_69._){return 2;}else{var _6a=E(_68.a),_6b=E(_69.a);if(_6a!=_6b){return (_6a>_6b)?2:0;}else{_66=_68.b;_67=_69.b;continue;}}}}},_6c=new T0(1),_6d=new T(function(){return B(unCStr("Failure in Data.Map.balanceR"));}),_6e=function(_6f){return new F(function(){return err(_6d);});},_6g=new T(function(){return B(_6e(_));}),_6h=function(_6i,_6j,_6k,_6l){var _6m=E(_6k);if(!_6m._){var _6n=_6m.a,_6o=E(_6l);if(!_6o._){var _6p=_6o.a,_6q=_6o.b,_6r=_6o.c;if(_6p<=(imul(3,_6n)|0)){return new T5(0,(1+_6n|0)+_6p|0,E(_6i),_6j,E(_6m),E(_6o));}else{var _6s=E(_6o.d);if(!_6s._){var _6t=_6s.a,_6u=_6s.b,_6v=_6s.c,_6w=_6s.d,_6x=E(_6o.e);if(!_6x._){var _6y=_6x.a;if(_6t>=(imul(2,_6y)|0)){var _6z=function(_6A){var _6B=E(_6i),_6C=E(_6s.e);return (_6C._==0)?new T5(0,(1+_6n|0)+_6p|0,E(_6u),_6v,E(new T5(0,(1+_6n|0)+_6A|0,E(_6B),_6j,E(_6m),E(_6w))),E(new T5(0,(1+_6y|0)+_6C.a|0,E(_6q),_6r,E(_6C),E(_6x)))):new T5(0,(1+_6n|0)+_6p|0,E(_6u),_6v,E(new T5(0,(1+_6n|0)+_6A|0,E(_6B),_6j,E(_6m),E(_6w))),E(new T5(0,1+_6y|0,E(_6q),_6r,E(_6c),E(_6x))));},_6D=E(_6w);if(!_6D._){return new F(function(){return _6z(_6D.a);});}else{return new F(function(){return _6z(0);});}}else{return new T5(0,(1+_6n|0)+_6p|0,E(_6q),_6r,E(new T5(0,(1+_6n|0)+_6t|0,E(_6i),_6j,E(_6m),E(_6s))),E(_6x));}}else{return E(_6g);}}else{return E(_6g);}}}else{return new T5(0,1+_6n|0,E(_6i),_6j,E(_6m),E(_6c));}}else{var _6E=E(_6l);if(!_6E._){var _6F=_6E.a,_6G=_6E.b,_6H=_6E.c,_6I=_6E.e,_6J=E(_6E.d);if(!_6J._){var _6K=_6J.a,_6L=_6J.b,_6M=_6J.c,_6N=_6J.d,_6O=E(_6I);if(!_6O._){var _6P=_6O.a;if(_6K>=(imul(2,_6P)|0)){var _6Q=function(_6R){var _6S=E(_6i),_6T=E(_6J.e);return (_6T._==0)?new T5(0,1+_6F|0,E(_6L),_6M,E(new T5(0,1+_6R|0,E(_6S),_6j,E(_6c),E(_6N))),E(new T5(0,(1+_6P|0)+_6T.a|0,E(_6G),_6H,E(_6T),E(_6O)))):new T5(0,1+_6F|0,E(_6L),_6M,E(new T5(0,1+_6R|0,E(_6S),_6j,E(_6c),E(_6N))),E(new T5(0,1+_6P|0,E(_6G),_6H,E(_6c),E(_6O))));},_6U=E(_6N);if(!_6U._){return new F(function(){return _6Q(_6U.a);});}else{return new F(function(){return _6Q(0);});}}else{return new T5(0,1+_6F|0,E(_6G),_6H,E(new T5(0,1+_6K|0,E(_6i),_6j,E(_6c),E(_6J))),E(_6O));}}else{return new T5(0,3,E(_6L),_6M,E(new T5(0,1,E(_6i),_6j,E(_6c),E(_6c))),E(new T5(0,1,E(_6G),_6H,E(_6c),E(_6c))));}}else{var _6V=E(_6I);return (_6V._==0)?new T5(0,3,E(_6G),_6H,E(new T5(0,1,E(_6i),_6j,E(_6c),E(_6c))),E(_6V)):new T5(0,2,E(_6i),_6j,E(_6c),E(_6E));}}else{return new T5(0,1,E(_6i),_6j,E(_6c),E(_6c));}}},_6W=function(_6X,_6Y){return new T5(0,1,E(_6X),_6Y,E(_6c),E(_6c));},_6Z=function(_70,_71,_72){var _73=E(_72);if(!_73._){return new F(function(){return _6h(_73.b,_73.c,_73.d,B(_6Z(_70,_71,_73.e)));});}else{return new F(function(){return _6W(_70,_71);});}},_74=new T(function(){return B(unCStr("Failure in Data.Map.balanceL"));}),_75=function(_76){return new F(function(){return err(_74);});},_77=new T(function(){return B(_75(_));}),_78=function(_79,_7a,_7b,_7c){var _7d=E(_7c);if(!_7d._){var _7e=_7d.a,_7f=E(_7b);if(!_7f._){var _7g=_7f.a,_7h=_7f.b,_7i=_7f.c;if(_7g<=(imul(3,_7e)|0)){return new T5(0,(1+_7g|0)+_7e|0,E(_79),_7a,E(_7f),E(_7d));}else{var _7j=E(_7f.d);if(!_7j._){var _7k=_7j.a,_7l=E(_7f.e);if(!_7l._){var _7m=_7l.a,_7n=_7l.b,_7o=_7l.c,_7p=_7l.d;if(_7m>=(imul(2,_7k)|0)){var _7q=function(_7r){var _7s=E(_7l.e);return (_7s._==0)?new T5(0,(1+_7g|0)+_7e|0,E(_7n),_7o,E(new T5(0,(1+_7k|0)+_7r|0,E(_7h),_7i,E(_7j),E(_7p))),E(new T5(0,(1+_7e|0)+_7s.a|0,E(_79),_7a,E(_7s),E(_7d)))):new T5(0,(1+_7g|0)+_7e|0,E(_7n),_7o,E(new T5(0,(1+_7k|0)+_7r|0,E(_7h),_7i,E(_7j),E(_7p))),E(new T5(0,1+_7e|0,E(_79),_7a,E(_6c),E(_7d))));},_7t=E(_7p);if(!_7t._){return new F(function(){return _7q(_7t.a);});}else{return new F(function(){return _7q(0);});}}else{return new T5(0,(1+_7g|0)+_7e|0,E(_7h),_7i,E(_7j),E(new T5(0,(1+_7e|0)+_7m|0,E(_79),_7a,E(_7l),E(_7d))));}}else{return E(_77);}}else{return E(_77);}}}else{return new T5(0,1+_7e|0,E(_79),_7a,E(_6c),E(_7d));}}else{var _7u=E(_7b);if(!_7u._){var _7v=_7u.a,_7w=_7u.b,_7x=_7u.c,_7y=_7u.e,_7z=E(_7u.d);if(!_7z._){var _7A=_7z.a,_7B=E(_7y);if(!_7B._){var _7C=_7B.a,_7D=_7B.b,_7E=_7B.c,_7F=_7B.d;if(_7C>=(imul(2,_7A)|0)){var _7G=function(_7H){var _7I=E(_7B.e);return (_7I._==0)?new T5(0,1+_7v|0,E(_7D),_7E,E(new T5(0,(1+_7A|0)+_7H|0,E(_7w),_7x,E(_7z),E(_7F))),E(new T5(0,1+_7I.a|0,E(_79),_7a,E(_7I),E(_6c)))):new T5(0,1+_7v|0,E(_7D),_7E,E(new T5(0,(1+_7A|0)+_7H|0,E(_7w),_7x,E(_7z),E(_7F))),E(new T5(0,1,E(_79),_7a,E(_6c),E(_6c))));},_7J=E(_7F);if(!_7J._){return new F(function(){return _7G(_7J.a);});}else{return new F(function(){return _7G(0);});}}else{return new T5(0,1+_7v|0,E(_7w),_7x,E(_7z),E(new T5(0,1+_7C|0,E(_79),_7a,E(_7B),E(_6c))));}}else{return new T5(0,3,E(_7w),_7x,E(_7z),E(new T5(0,1,E(_79),_7a,E(_6c),E(_6c))));}}else{var _7K=E(_7y);return (_7K._==0)?new T5(0,3,E(_7K.b),_7K.c,E(new T5(0,1,E(_7w),_7x,E(_6c),E(_6c))),E(new T5(0,1,E(_79),_7a,E(_6c),E(_6c)))):new T5(0,2,E(_79),_7a,E(_7u),E(_6c));}}else{return new T5(0,1,E(_79),_7a,E(_6c),E(_6c));}}},_7L=function(_7M,_7N,_7O){var _7P=E(_7O);if(!_7P._){return new F(function(){return _78(_7P.b,_7P.c,B(_7L(_7M,_7N,_7P.d)),_7P.e);});}else{return new F(function(){return _6W(_7M,_7N);});}},_7Q=function(_7R,_7S,_7T,_7U,_7V,_7W,_7X){return new F(function(){return _78(_7U,_7V,B(_7L(_7R,_7S,_7W)),_7X);});},_7Y=function(_7Z,_80,_81,_82,_83,_84,_85,_86){var _87=E(_81);if(!_87._){var _88=_87.a,_89=_87.b,_8a=_87.c,_8b=_87.d,_8c=_87.e;if((imul(3,_88)|0)>=_82){if((imul(3,_82)|0)>=_88){return new T5(0,(_88+_82|0)+1|0,E(_7Z),_80,E(_87),E(new T5(0,_82,E(_83),_84,E(_85),E(_86))));}else{return new F(function(){return _6h(_89,_8a,_8b,B(_7Y(_7Z,_80,_8c,_82,_83,_84,_85,_86)));});}}else{return new F(function(){return _78(_83,_84,B(_8d(_7Z,_80,_88,_89,_8a,_8b,_8c,_85)),_86);});}}else{return new F(function(){return _7Q(_7Z,_80,_82,_83,_84,_85,_86);});}},_8d=function(_8e,_8f,_8g,_8h,_8i,_8j,_8k,_8l){var _8m=E(_8l);if(!_8m._){var _8n=_8m.a,_8o=_8m.b,_8p=_8m.c,_8q=_8m.d,_8r=_8m.e;if((imul(3,_8g)|0)>=_8n){if((imul(3,_8n)|0)>=_8g){return new T5(0,(_8g+_8n|0)+1|0,E(_8e),_8f,E(new T5(0,_8g,E(_8h),_8i,E(_8j),E(_8k))),E(_8m));}else{return new F(function(){return _6h(_8h,_8i,_8j,B(_7Y(_8e,_8f,_8k,_8n,_8o,_8p,_8q,_8r)));});}}else{return new F(function(){return _78(_8o,_8p,B(_8d(_8e,_8f,_8g,_8h,_8i,_8j,_8k,_8q)),_8r);});}}else{return new F(function(){return _6Z(_8e,_8f,new T5(0,_8g,E(_8h),_8i,E(_8j),E(_8k)));});}},_8s=function(_8t,_8u,_8v,_8w){var _8x=E(_8v);if(!_8x._){var _8y=_8x.a,_8z=_8x.b,_8A=_8x.c,_8B=_8x.d,_8C=_8x.e,_8D=E(_8w);if(!_8D._){var _8E=_8D.a,_8F=_8D.b,_8G=_8D.c,_8H=_8D.d,_8I=_8D.e;if((imul(3,_8y)|0)>=_8E){if((imul(3,_8E)|0)>=_8y){return new T5(0,(_8y+_8E|0)+1|0,E(_8t),_8u,E(_8x),E(_8D));}else{return new F(function(){return _6h(_8z,_8A,_8B,B(_7Y(_8t,_8u,_8C,_8E,_8F,_8G,_8H,_8I)));});}}else{return new F(function(){return _78(_8F,_8G,B(_8d(_8t,_8u,_8y,_8z,_8A,_8B,_8C,_8H)),_8I);});}}else{return new F(function(){return _6Z(_8t,_8u,_8x);});}}else{return new F(function(){return _7L(_8t,_8u,_8w);});}},_8J=function(_8K,_8L,_8M,_8N){var _8O=E(_8K);if(_8O==1){var _8P=E(_8N);return (_8P._==0)?new T3(0,new T(function(){return new T5(0,1,E(_8L),_8M,E(_6c),E(_6c));}),_Z,_Z):(B(_65(_8L,E(_8P.a).a))==0)?new T3(0,new T(function(){return new T5(0,1,E(_8L),_8M,E(_6c),E(_6c));}),_8P,_Z):new T3(0,new T(function(){return new T5(0,1,E(_8L),_8M,E(_6c),E(_6c));}),_Z,_8P);}else{var _8Q=B(_8J(_8O>>1,_8L,_8M,_8N)),_8R=_8Q.a,_8S=_8Q.c,_8T=E(_8Q.b);if(!_8T._){return new T3(0,_8R,_Z,_8S);}else{var _8U=E(_8T.a),_8V=_8U.a,_8W=_8U.b,_8X=E(_8T.b);if(!_8X._){return new T3(0,new T(function(){return B(_6Z(_8V,_8W,_8R));}),_Z,_8S);}else{var _8Y=E(_8X.a),_8Z=_8Y.a;if(!B(_65(_8V,_8Z))){var _90=B(_8J(_8O>>1,_8Z,_8Y.b,_8X.b));return new T3(0,new T(function(){return B(_8s(_8V,_8W,_8R,_90.a));}),_90.b,_90.c);}else{return new T3(0,_8R,_Z,_8T);}}}}},_91=function(_92,_93,_94){var _95=E(_92),_96=E(_94);if(!_96._){var _97=_96.b,_98=_96.c,_99=_96.d,_9a=_96.e;switch(B(_65(_95,_97))){case 0:return new F(function(){return _78(_97,_98,B(_91(_95,_93,_99)),_9a);});break;case 1:return new T5(0,_96.a,E(_95),_93,E(_99),E(_9a));default:return new F(function(){return _6h(_97,_98,_99,B(_91(_95,_93,_9a)));});}}else{return new T5(0,1,E(_95),_93,E(_6c),E(_6c));}},_9b=function(_9c,_9d){while(1){var _9e=E(_9d);if(!_9e._){return E(_9c);}else{var _9f=E(_9e.a),_9g=B(_91(_9f.a,_9f.b,_9c));_9c=_9g;_9d=_9e.b;continue;}}},_9h=function(_9i,_9j,_9k,_9l){return new F(function(){return _9b(B(_91(_9j,_9k,_9i)),_9l);});},_9m=function(_9n,_9o,_9p){var _9q=E(_9o);return new F(function(){return _9b(B(_91(_9q.a,_9q.b,_9n)),_9p);});},_9r=function(_9s,_9t,_9u){while(1){var _9v=E(_9u);if(!_9v._){return E(_9t);}else{var _9w=E(_9v.a),_9x=_9w.a,_9y=_9w.b,_9z=E(_9v.b);if(!_9z._){return new F(function(){return _6Z(_9x,_9y,_9t);});}else{var _9A=E(_9z.a),_9B=_9A.a;if(!B(_65(_9x,_9B))){var _9C=B(_8J(_9s,_9B,_9A.b,_9z.b)),_9D=_9C.a,_9E=E(_9C.c);if(!_9E._){var _9F=_9s<<1,_9G=B(_8s(_9x,_9y,_9t,_9D));_9s=_9F;_9t=_9G;_9u=_9C.b;continue;}else{return new F(function(){return _9m(B(_8s(_9x,_9y,_9t,_9D)),_9E.a,_9E.b);});}}else{return new F(function(){return _9h(_9t,_9x,_9y,_9z);});}}}}},_9H=function(_9I,_9J,_9K,_9L,_9M){var _9N=E(_9M);if(!_9N._){return new F(function(){return _6Z(_9K,_9L,_9J);});}else{var _9O=E(_9N.a),_9P=_9O.a;if(!B(_65(_9K,_9P))){var _9Q=B(_8J(_9I,_9P,_9O.b,_9N.b)),_9R=_9Q.a,_9S=E(_9Q.c);if(!_9S._){return new F(function(){return _9r(_9I<<1,B(_8s(_9K,_9L,_9J,_9R)),_9Q.b);});}else{return new F(function(){return _9m(B(_8s(_9K,_9L,_9J,_9R)),_9S.a,_9S.b);});}}else{return new F(function(){return _9h(_9J,_9K,_9L,_9N);});}}},_9T=function(_9U){var _9V=E(_9U);if(!_9V._){return new T0(1);}else{var _9W=E(_9V.a),_9X=_9W.a,_9Y=_9W.b,_9Z=E(_9V.b);if(!_9Z._){return new T5(0,1,E(_9X),_9Y,E(_6c),E(_6c));}else{var _a0=_9Z.b,_a1=E(_9Z.a),_a2=_a1.a,_a3=_a1.b;if(!B(_65(_9X,_a2))){return new F(function(){return _9H(1,new T5(0,1,E(_9X),_9Y,E(_6c),E(_6c)),_a2,_a3,_a0);});}else{return new F(function(){return _9h(new T5(0,1,E(_9X),_9Y,E(_6c),E(_6c)),_a2,_a3,_a0);});}}}},_a4=new T(function(){return eval("(function(cv){return cv.getBoundingClientRect().height})");}),_a5=new T(function(){return eval("(function(cv){return cv.getBoundingClientRect().width})");}),_a6=new T(function(){return eval("(function(cv){return cv.height})");}),_a7=new T(function(){return eval("(function(cv){return cv.width})");}),_a8=function(_a9,_){var _aa=__app1(E(_a7),_a9),_ab=__app1(E(_a6),_a9),_ac=__app1(E(_a5),_a9),_ad=__app1(E(_a4),_a9);return new T2(0,new T2(0,_aa,_ab),new T2(0,_ac,_ad));},_ae=function(_af,_ag){while(1){var _ah=E(_af);if(!_ah._){return (E(_ag)._==0)?true:false;}else{var _ai=E(_ag);if(!_ai._){return false;}else{if(E(_ah.a)!=E(_ai.a)){return false;}else{_af=_ah.b;_ag=_ai.b;continue;}}}}},_aj=function(_ak,_al){var _am=E(_al);return (_am._==0)?__Z:new T2(1,new T(function(){return B(A1(_ak,_am.a));}),new T(function(){return B(_aj(_ak,_am.b));}));},_an=function(_ao){return new T1(3,E(B(_aj(_61,_ao))));},_ap="Tried to deserialie a non-array to a list!",_aq=new T1(0,_ap),_ar=new T1(1,_Z),_as=function(_at){var _au=E(_at);if(!_au._){return E(_ar);}else{var _av=B(_as(_au.b));return (_av._==0)?new T1(0,_av.a):new T1(1,new T2(1,_au.a,_av.a));}},_aw=function(_ax){var _ay=E(_ax);if(_ay._==3){return new F(function(){return _as(_ay.a);});}else{return E(_aq);}},_az=function(_aA){return new T1(1,_aA);},_aB=new T4(0,_61,_an,_az,_aw),_aC=function(_aD){return new F(function(){return _H(0,E(_aD),_Z);});},_aE=34,_aF=new T2(1,_aE,_Z),_aG=new T(function(){return B(unCStr("!!: negative index"));}),_aH=new T(function(){return B(unCStr("Prelude."));}),_aI=new T(function(){return B(_x(_aH,_aG));}),_aJ=new T(function(){return B(err(_aI));}),_aK=new T(function(){return B(unCStr("!!: index too large"));}),_aL=new T(function(){return B(_x(_aH,_aK));}),_aM=new T(function(){return B(err(_aL));}),_aN=function(_aO,_aP){while(1){var _aQ=E(_aO);if(!_aQ._){return E(_aM);}else{var _aR=E(_aP);if(!_aR){return E(_aQ.a);}else{_aO=_aQ.b;_aP=_aR-1|0;continue;}}}},_aS=function(_aT,_aU){if(_aU>=0){return new F(function(){return _aN(_aT,_aU);});}else{return E(_aJ);}},_aV=new T(function(){return B(unCStr("ACK"));}),_aW=new T(function(){return B(unCStr("BEL"));}),_aX=new T(function(){return B(unCStr("BS"));}),_aY=new T(function(){return B(unCStr("SP"));}),_aZ=new T2(1,_aY,_Z),_b0=new T(function(){return B(unCStr("US"));}),_b1=new T2(1,_b0,_aZ),_b2=new T(function(){return B(unCStr("RS"));}),_b3=new T2(1,_b2,_b1),_b4=new T(function(){return B(unCStr("GS"));}),_b5=new T2(1,_b4,_b3),_b6=new T(function(){return B(unCStr("FS"));}),_b7=new T2(1,_b6,_b5),_b8=new T(function(){return B(unCStr("ESC"));}),_b9=new T2(1,_b8,_b7),_ba=new T(function(){return B(unCStr("SUB"));}),_bb=new T2(1,_ba,_b9),_bc=new T(function(){return B(unCStr("EM"));}),_bd=new T2(1,_bc,_bb),_be=new T(function(){return B(unCStr("CAN"));}),_bf=new T2(1,_be,_bd),_bg=new T(function(){return B(unCStr("ETB"));}),_bh=new T2(1,_bg,_bf),_bi=new T(function(){return B(unCStr("SYN"));}),_bj=new T2(1,_bi,_bh),_bk=new T(function(){return B(unCStr("NAK"));}),_bl=new T2(1,_bk,_bj),_bm=new T(function(){return B(unCStr("DC4"));}),_bn=new T2(1,_bm,_bl),_bo=new T(function(){return B(unCStr("DC3"));}),_bp=new T2(1,_bo,_bn),_bq=new T(function(){return B(unCStr("DC2"));}),_br=new T2(1,_bq,_bp),_bs=new T(function(){return B(unCStr("DC1"));}),_bt=new T2(1,_bs,_br),_bu=new T(function(){return B(unCStr("DLE"));}),_bv=new T2(1,_bu,_bt),_bw=new T(function(){return B(unCStr("SI"));}),_bx=new T2(1,_bw,_bv),_by=new T(function(){return B(unCStr("SO"));}),_bz=new T2(1,_by,_bx),_bA=new T(function(){return B(unCStr("CR"));}),_bB=new T2(1,_bA,_bz),_bC=new T(function(){return B(unCStr("FF"));}),_bD=new T2(1,_bC,_bB),_bE=new T(function(){return B(unCStr("VT"));}),_bF=new T2(1,_bE,_bD),_bG=new T(function(){return B(unCStr("LF"));}),_bH=new T2(1,_bG,_bF),_bI=new T(function(){return B(unCStr("HT"));}),_bJ=new T2(1,_bI,_bH),_bK=new T2(1,_aX,_bJ),_bL=new T2(1,_aW,_bK),_bM=new T2(1,_aV,_bL),_bN=new T(function(){return B(unCStr("ENQ"));}),_bO=new T2(1,_bN,_bM),_bP=new T(function(){return B(unCStr("EOT"));}),_bQ=new T2(1,_bP,_bO),_bR=new T(function(){return B(unCStr("ETX"));}),_bS=new T2(1,_bR,_bQ),_bT=new T(function(){return B(unCStr("STX"));}),_bU=new T2(1,_bT,_bS),_bV=new T(function(){return B(unCStr("SOH"));}),_bW=new T2(1,_bV,_bU),_bX=new T(function(){return B(unCStr("NUL"));}),_bY=new T2(1,_bX,_bW),_bZ=92,_c0=new T(function(){return B(unCStr("\\DEL"));}),_c1=new T(function(){return B(unCStr("\\a"));}),_c2=new T(function(){return B(unCStr("\\\\"));}),_c3=new T(function(){return B(unCStr("\\SO"));}),_c4=new T(function(){return B(unCStr("\\r"));}),_c5=new T(function(){return B(unCStr("\\f"));}),_c6=new T(function(){return B(unCStr("\\v"));}),_c7=new T(function(){return B(unCStr("\\n"));}),_c8=new T(function(){return B(unCStr("\\t"));}),_c9=new T(function(){return B(unCStr("\\b"));}),_ca=function(_cb,_cc){if(_cb<=127){var _cd=E(_cb);switch(_cd){case 92:return new F(function(){return _x(_c2,_cc);});break;case 127:return new F(function(){return _x(_c0,_cc);});break;default:if(_cd<32){var _ce=E(_cd);switch(_ce){case 7:return new F(function(){return _x(_c1,_cc);});break;case 8:return new F(function(){return _x(_c9,_cc);});break;case 9:return new F(function(){return _x(_c8,_cc);});break;case 10:return new F(function(){return _x(_c7,_cc);});break;case 11:return new F(function(){return _x(_c6,_cc);});break;case 12:return new F(function(){return _x(_c5,_cc);});break;case 13:return new F(function(){return _x(_c4,_cc);});break;case 14:return new F(function(){return _x(_c3,new T(function(){var _cf=E(_cc);if(!_cf._){return __Z;}else{if(E(_cf.a)==72){return B(unAppCStr("\\&",_cf));}else{return E(_cf);}}},1));});break;default:return new F(function(){return _x(new T2(1,_bZ,new T(function(){return B(_aS(_bY,_ce));})),_cc);});}}else{return new T2(1,_cd,_cc);}}}else{var _cg=new T(function(){var _ch=jsShowI(_cb);return B(_x(fromJSStr(_ch),new T(function(){var _ci=E(_cc);if(!_ci._){return __Z;}else{var _cj=E(_ci.a);if(_cj<48){return E(_ci);}else{if(_cj>57){return E(_ci);}else{return B(unAppCStr("\\&",_ci));}}}},1)));});return new T2(1,_bZ,_cg);}},_ck=new T(function(){return B(unCStr("\\\""));}),_cl=function(_cm,_cn){var _co=E(_cm);if(!_co._){return E(_cn);}else{var _cp=_co.b,_cq=E(_co.a);if(_cq==34){return new F(function(){return _x(_ck,new T(function(){return B(_cl(_cp,_cn));},1));});}else{return new F(function(){return _ca(_cq,new T(function(){return B(_cl(_cp,_cn));}));});}}},_cr=function(_cs){return new T2(1,_aE,new T(function(){return B(_cl(_cs,_aF));}));},_ct=function(_cu,_cv){if(_cu<=_cv){var _cw=function(_cx){return new T2(1,_cx,new T(function(){if(_cx!=_cv){return B(_cw(_cx+1|0));}else{return __Z;}}));};return new F(function(){return _cw(_cu);});}else{return __Z;}},_cy=function(_cz){return new F(function(){return _ct(E(_cz),2147483647);});},_cA=function(_cB,_cC,_cD){if(_cD<=_cC){var _cE=new T(function(){var _cF=_cC-_cB|0,_cG=function(_cH){return (_cH>=(_cD-_cF|0))?new T2(1,_cH,new T(function(){return B(_cG(_cH+_cF|0));})):new T2(1,_cH,_Z);};return B(_cG(_cC));});return new T2(1,_cB,_cE);}else{return (_cD<=_cB)?new T2(1,_cB,_Z):__Z;}},_cI=function(_cJ,_cK,_cL){if(_cL>=_cK){var _cM=new T(function(){var _cN=_cK-_cJ|0,_cO=function(_cP){return (_cP<=(_cL-_cN|0))?new T2(1,_cP,new T(function(){return B(_cO(_cP+_cN|0));})):new T2(1,_cP,_Z);};return B(_cO(_cK));});return new T2(1,_cJ,_cM);}else{return (_cL>=_cJ)?new T2(1,_cJ,_Z):__Z;}},_cQ=function(_cR,_cS){if(_cS<_cR){return new F(function(){return _cA(_cR,_cS, -2147483648);});}else{return new F(function(){return _cI(_cR,_cS,2147483647);});}},_cT=function(_cU,_cV){return new F(function(){return _cQ(E(_cU),E(_cV));});},_cW=function(_cX,_cY,_cZ){if(_cY<_cX){return new F(function(){return _cA(_cX,_cY,_cZ);});}else{return new F(function(){return _cI(_cX,_cY,_cZ);});}},_d0=function(_d1,_d2,_d3){return new F(function(){return _cW(E(_d1),E(_d2),E(_d3));});},_d4=function(_d5,_d6){return new F(function(){return _ct(E(_d5),E(_d6));});},_d7=function(_d8){return E(_d8);},_d9=new T(function(){return B(unCStr("Prelude.Enum.pred{Int}: tried to take `pred\' of minBound"));}),_da=new T(function(){return B(err(_d9));}),_db=function(_dc){var _dd=E(_dc);return (_dd==( -2147483648))?E(_da):_dd-1|0;},_de=new T(function(){return B(unCStr("Prelude.Enum.succ{Int}: tried to take `succ\' of maxBound"));}),_df=new T(function(){return B(err(_de));}),_dg=function(_dh){var _di=E(_dh);return (_di==2147483647)?E(_df):_di+1|0;},_dj={_:0,a:_dg,b:_db,c:_d7,d:_d7,e:_cy,f:_cT,g:_d4,h:_d0},_dk=function(_dl,_dm){if(_dl<=0){if(_dl>=0){return new F(function(){return quot(_dl,_dm);});}else{if(_dm<=0){return new F(function(){return quot(_dl,_dm);});}else{return quot(_dl+1|0,_dm)-1|0;}}}else{if(_dm>=0){if(_dl>=0){return new F(function(){return quot(_dl,_dm);});}else{if(_dm<=0){return new F(function(){return quot(_dl,_dm);});}else{return quot(_dl+1|0,_dm)-1|0;}}}else{return quot(_dl-1|0,_dm)-1|0;}}},_dn=new T(function(){return B(unCStr("base"));}),_do=new T(function(){return B(unCStr("GHC.Exception"));}),_dp=new T(function(){return B(unCStr("ArithException"));}),_dq=new T5(0,new Long(4194982440,719304104,true),new Long(3110813675,1843557400,true),_dn,_do,_dp),_dr=new T5(0,new Long(4194982440,719304104,true),new Long(3110813675,1843557400,true),_dq,_Z,_Z),_ds=function(_dt){return E(_dr);},_du=function(_dv){var _dw=E(_dv);return new F(function(){return _1r(B(_1p(_dw.a)),_ds,_dw.b);});},_dx=new T(function(){return B(unCStr("Ratio has zero denominator"));}),_dy=new T(function(){return B(unCStr("denormal"));}),_dz=new T(function(){return B(unCStr("divide by zero"));}),_dA=new T(function(){return B(unCStr("loss of precision"));}),_dB=new T(function(){return B(unCStr("arithmetic underflow"));}),_dC=new T(function(){return B(unCStr("arithmetic overflow"));}),_dD=function(_dE,_dF){switch(E(_dE)){case 0:return new F(function(){return _x(_dC,_dF);});break;case 1:return new F(function(){return _x(_dB,_dF);});break;case 2:return new F(function(){return _x(_dA,_dF);});break;case 3:return new F(function(){return _x(_dz,_dF);});break;case 4:return new F(function(){return _x(_dy,_dF);});break;default:return new F(function(){return _x(_dx,_dF);});}},_dG=function(_dH){return new F(function(){return _dD(_dH,_Z);});},_dI=function(_dJ,_dK,_dL){return new F(function(){return _dD(_dK,_dL);});},_dM=function(_dN,_dO){return new F(function(){return _2C(_dD,_dN,_dO);});},_dP=new T3(0,_dI,_dG,_dM),_dQ=new T(function(){return new T5(0,_ds,_dP,_dR,_du,_dG);}),_dR=function(_dS){return new T2(0,_dQ,_dS);},_dT=3,_dU=new T(function(){return B(_dR(_dT));}),_dV=new T(function(){return die(_dU);}),_dW=0,_dX=new T(function(){return B(_dR(_dW));}),_dY=new T(function(){return die(_dX);}),_dZ=function(_e0,_e1){var _e2=E(_e1);switch(_e2){case  -1:var _e3=E(_e0);if(_e3==( -2147483648)){return E(_dY);}else{return new F(function(){return _dk(_e3, -1);});}break;case 0:return E(_dV);default:return new F(function(){return _dk(_e0,_e2);});}},_e4=function(_e5,_e6){return new F(function(){return _dZ(E(_e5),E(_e6));});},_e7=0,_e8=new T2(0,_dY,_e7),_e9=function(_ea,_eb){var _ec=E(_ea),_ed=E(_eb);switch(_ed){case  -1:var _ee=E(_ec);if(_ee==( -2147483648)){return E(_e8);}else{if(_ee<=0){if(_ee>=0){var _ef=quotRemI(_ee, -1);return new T2(0,_ef.a,_ef.b);}else{var _eg=quotRemI(_ee, -1);return new T2(0,_eg.a,_eg.b);}}else{var _eh=quotRemI(_ee-1|0, -1);return new T2(0,_eh.a-1|0,(_eh.b+( -1)|0)+1|0);}}break;case 0:return E(_dV);default:if(_ec<=0){if(_ec>=0){var _ei=quotRemI(_ec,_ed);return new T2(0,_ei.a,_ei.b);}else{if(_ed<=0){var _ej=quotRemI(_ec,_ed);return new T2(0,_ej.a,_ej.b);}else{var _ek=quotRemI(_ec+1|0,_ed);return new T2(0,_ek.a-1|0,(_ek.b+_ed|0)-1|0);}}}else{if(_ed>=0){if(_ec>=0){var _el=quotRemI(_ec,_ed);return new T2(0,_el.a,_el.b);}else{if(_ed<=0){var _em=quotRemI(_ec,_ed);return new T2(0,_em.a,_em.b);}else{var _en=quotRemI(_ec+1|0,_ed);return new T2(0,_en.a-1|0,(_en.b+_ed|0)-1|0);}}}else{var _eo=quotRemI(_ec-1|0,_ed);return new T2(0,_eo.a-1|0,(_eo.b+_ed|0)+1|0);}}}},_ep=function(_eq,_er){var _es=_eq%_er;if(_eq<=0){if(_eq>=0){return E(_es);}else{if(_er<=0){return E(_es);}else{var _et=E(_es);return (_et==0)?0:_et+_er|0;}}}else{if(_er>=0){if(_eq>=0){return E(_es);}else{if(_er<=0){return E(_es);}else{var _eu=E(_es);return (_eu==0)?0:_eu+_er|0;}}}else{var _ev=E(_es);return (_ev==0)?0:_ev+_er|0;}}},_ew=function(_ex,_ey){var _ez=E(_ey);switch(_ez){case  -1:return E(_e7);case 0:return E(_dV);default:return new F(function(){return _ep(E(_ex),_ez);});}},_eA=function(_eB,_eC){var _eD=E(_eB),_eE=E(_eC);switch(_eE){case  -1:var _eF=E(_eD);if(_eF==( -2147483648)){return E(_dY);}else{return new F(function(){return quot(_eF, -1);});}break;case 0:return E(_dV);default:return new F(function(){return quot(_eD,_eE);});}},_eG=function(_eH,_eI){var _eJ=E(_eH),_eK=E(_eI);switch(_eK){case  -1:var _eL=E(_eJ);if(_eL==( -2147483648)){return E(_e8);}else{var _eM=quotRemI(_eL, -1);return new T2(0,_eM.a,_eM.b);}break;case 0:return E(_dV);default:var _eN=quotRemI(_eJ,_eK);return new T2(0,_eN.a,_eN.b);}},_eO=function(_eP,_eQ){var _eR=E(_eQ);switch(_eR){case  -1:return E(_e7);case 0:return E(_dV);default:return E(_eP)%_eR;}},_eS=function(_eT){return new T1(0,_eT);},_eU=function(_eV){return new F(function(){return _eS(E(_eV));});},_eW=new T1(0,1),_eX=function(_eY){return new T2(0,E(B(_eS(E(_eY)))),E(_eW));},_eZ=function(_f0,_f1){return imul(E(_f0),E(_f1))|0;},_f2=function(_f3,_f4){return E(_f3)+E(_f4)|0;},_f5=function(_f6,_f7){return E(_f6)-E(_f7)|0;},_f8=function(_f9){var _fa=E(_f9);return (_fa<0)? -_fa:E(_fa);},_fb=function(_fc){var _fd=E(_fc);if(!_fd._){return E(_fd.a);}else{return new F(function(){return I_toInt(_fd.a);});}},_fe=function(_ff){return new F(function(){return _fb(_ff);});},_fg=function(_fh){return  -E(_fh);},_fi= -1,_fj=0,_fk=1,_fl=function(_fm){var _fn=E(_fm);return (_fn>=0)?(E(_fn)==0)?E(_fj):E(_fk):E(_fi);},_fo={_:0,a:_f2,b:_f5,c:_eZ,d:_fg,e:_f8,f:_fl,g:_fe},_fp=function(_fq,_fr){var _fs=E(_fq),_ft=E(_fr);return (_fs>_ft)?E(_fs):E(_ft);},_fu=function(_fv,_fw){var _fx=E(_fv),_fy=E(_fw);return (_fx>_fy)?E(_fy):E(_fx);},_fz=function(_fA,_fB){return (_fA>=_fB)?(_fA!=_fB)?2:1:0;},_fC=function(_fD,_fE){return new F(function(){return _fz(E(_fD),E(_fE));});},_fF=function(_fG,_fH){return E(_fG)>=E(_fH);},_fI=function(_fJ,_fK){return E(_fJ)>E(_fK);},_fL=function(_fM,_fN){return E(_fM)<=E(_fN);},_fO=function(_fP,_fQ){return E(_fP)<E(_fQ);},_fR={_:0,a:_3S,b:_fC,c:_fO,d:_fL,e:_fI,f:_fF,g:_fp,h:_fu},_fS=new T3(0,_fo,_fR,_eX),_fT={_:0,a:_fS,b:_dj,c:_eA,d:_eO,e:_e4,f:_ew,g:_eG,h:_e9,i:_eU},_fU=function(_fV){var _fW=E(_fV);return new F(function(){return Math.log(_fW+(_fW+1)*Math.sqrt((_fW-1)/(_fW+1)));});},_fX=function(_fY){var _fZ=E(_fY);return new F(function(){return Math.log(_fZ+Math.sqrt(1+_fZ*_fZ));});},_g0=function(_g1){var _g2=E(_g1);return 0.5*Math.log((1+_g2)/(1-_g2));},_g3=function(_g4,_g5){return Math.log(E(_g5))/Math.log(E(_g4));},_g6=3.141592653589793,_g7=new T1(0,1),_g8=function(_g9,_ga){var _gb=E(_g9);if(!_gb._){var _gc=_gb.a,_gd=E(_ga);if(!_gd._){var _ge=_gd.a;return (_gc!=_ge)?(_gc>_ge)?2:0:1;}else{var _gf=I_compareInt(_gd.a,_gc);return (_gf<=0)?(_gf>=0)?1:2:0;}}else{var _gg=_gb.a,_gh=E(_ga);if(!_gh._){var _gi=I_compareInt(_gg,_gh.a);return (_gi>=0)?(_gi<=0)?1:2:0;}else{var _gj=I_compare(_gg,_gh.a);return (_gj>=0)?(_gj<=0)?1:2:0;}}},_gk=function(_gl,_gm){var _gn=E(_gl);return (_gn._==0)?_gn.a*Math.pow(2,_gm):I_toNumber(_gn.a)*Math.pow(2,_gm);},_go=function(_gp,_gq){var _gr=E(_gp);if(!_gr._){var _gs=_gr.a,_gt=E(_gq);return (_gt._==0)?_gs==_gt.a:(I_compareInt(_gt.a,_gs)==0)?true:false;}else{var _gu=_gr.a,_gv=E(_gq);return (_gv._==0)?(I_compareInt(_gu,_gv.a)==0)?true:false:(I_compare(_gu,_gv.a)==0)?true:false;}},_gw=function(_gx,_gy){while(1){var _gz=E(_gx);if(!_gz._){var _gA=_gz.a,_gB=E(_gy);if(!_gB._){var _gC=_gB.a,_gD=addC(_gA,_gC);if(!E(_gD.b)){return new T1(0,_gD.a);}else{_gx=new T1(1,I_fromInt(_gA));_gy=new T1(1,I_fromInt(_gC));continue;}}else{_gx=new T1(1,I_fromInt(_gA));_gy=_gB;continue;}}else{var _gE=E(_gy);if(!_gE._){_gx=_gz;_gy=new T1(1,I_fromInt(_gE.a));continue;}else{return new T1(1,I_add(_gz.a,_gE.a));}}}},_gF=function(_gG,_gH){while(1){var _gI=E(_gG);if(!_gI._){var _gJ=E(_gI.a);if(_gJ==( -2147483648)){_gG=new T1(1,I_fromInt( -2147483648));continue;}else{var _gK=E(_gH);if(!_gK._){var _gL=_gK.a;return new T2(0,new T1(0,quot(_gJ,_gL)),new T1(0,_gJ%_gL));}else{_gG=new T1(1,I_fromInt(_gJ));_gH=_gK;continue;}}}else{var _gM=E(_gH);if(!_gM._){_gG=_gI;_gH=new T1(1,I_fromInt(_gM.a));continue;}else{var _gN=I_quotRem(_gI.a,_gM.a);return new T2(0,new T1(1,_gN.a),new T1(1,_gN.b));}}}},_gO=new T1(0,0),_gP=function(_gQ,_gR){while(1){var _gS=E(_gQ);if(!_gS._){_gQ=new T1(1,I_fromInt(_gS.a));continue;}else{return new T1(1,I_shiftLeft(_gS.a,_gR));}}},_gT=function(_gU,_gV,_gW){if(!B(_go(_gW,_gO))){var _gX=B(_gF(_gV,_gW)),_gY=_gX.a;switch(B(_g8(B(_gP(_gX.b,1)),_gW))){case 0:return new F(function(){return _gk(_gY,_gU);});break;case 1:if(!(B(_fb(_gY))&1)){return new F(function(){return _gk(_gY,_gU);});}else{return new F(function(){return _gk(B(_gw(_gY,_g7)),_gU);});}break;default:return new F(function(){return _gk(B(_gw(_gY,_g7)),_gU);});}}else{return E(_dV);}},_gZ=function(_h0,_h1){var _h2=E(_h0);if(!_h2._){var _h3=_h2.a,_h4=E(_h1);return (_h4._==0)?_h3>_h4.a:I_compareInt(_h4.a,_h3)<0;}else{var _h5=_h2.a,_h6=E(_h1);return (_h6._==0)?I_compareInt(_h5,_h6.a)>0:I_compare(_h5,_h6.a)>0;}},_h7=new T1(0,1),_h8=function(_h9,_ha){var _hb=E(_h9);if(!_hb._){var _hc=_hb.a,_hd=E(_ha);return (_hd._==0)?_hc<_hd.a:I_compareInt(_hd.a,_hc)>0;}else{var _he=_hb.a,_hf=E(_ha);return (_hf._==0)?I_compareInt(_he,_hf.a)<0:I_compare(_he,_hf.a)<0;}},_hg=new T(function(){return B(unCStr("base"));}),_hh=new T(function(){return B(unCStr("Control.Exception.Base"));}),_hi=new T(function(){return B(unCStr("PatternMatchFail"));}),_hj=new T5(0,new Long(18445595,3739165398,true),new Long(52003073,3246954884,true),_hg,_hh,_hi),_hk=new T5(0,new Long(18445595,3739165398,true),new Long(52003073,3246954884,true),_hj,_Z,_Z),_hl=function(_hm){return E(_hk);},_hn=function(_ho){var _hp=E(_ho);return new F(function(){return _1r(B(_1p(_hp.a)),_hl,_hp.b);});},_hq=function(_hr){return E(E(_hr).a);},_hs=function(_ht){return new T2(0,_hu,_ht);},_hv=function(_hw,_hx){return new F(function(){return _x(E(_hw).a,_hx);});},_hy=function(_hz,_hA){return new F(function(){return _2C(_hv,_hz,_hA);});},_hB=function(_hC,_hD,_hE){return new F(function(){return _x(E(_hD).a,_hE);});},_hF=new T3(0,_hB,_hq,_hy),_hu=new T(function(){return new T5(0,_hl,_hF,_hs,_hn,_hq);}),_hG=new T(function(){return B(unCStr("Non-exhaustive patterns in"));}),_hH=function(_hI,_hJ){return new F(function(){return die(new T(function(){return B(A2(_5L,_hJ,_hI));}));});},_hK=function(_hL,_dS){return new F(function(){return _hH(_hL,_dS);});},_hM=function(_hN,_hO){var _hP=E(_hO);if(!_hP._){return new T2(0,_Z,_Z);}else{var _hQ=_hP.a;if(!B(A1(_hN,_hQ))){return new T2(0,_Z,_hP);}else{var _hR=new T(function(){var _hS=B(_hM(_hN,_hP.b));return new T2(0,_hS.a,_hS.b);});return new T2(0,new T2(1,_hQ,new T(function(){return E(E(_hR).a);})),new T(function(){return E(E(_hR).b);}));}}},_hT=32,_hU=new T(function(){return B(unCStr("\n"));}),_hV=function(_hW){return (E(_hW)==124)?false:true;},_hX=function(_hY,_hZ){var _i0=B(_hM(_hV,B(unCStr(_hY)))),_i1=_i0.a,_i2=function(_i3,_i4){var _i5=new T(function(){var _i6=new T(function(){return B(_x(_hZ,new T(function(){return B(_x(_i4,_hU));},1)));});return B(unAppCStr(": ",_i6));},1);return new F(function(){return _x(_i3,_i5);});},_i7=E(_i0.b);if(!_i7._){return new F(function(){return _i2(_i1,_Z);});}else{if(E(_i7.a)==124){return new F(function(){return _i2(_i1,new T2(1,_hT,_i7.b));});}else{return new F(function(){return _i2(_i1,_Z);});}}},_i8=function(_i9){return new F(function(){return _hK(new T1(0,new T(function(){return B(_hX(_i9,_hG));})),_hu);});},_ia=function(_ib){var _ic=function(_id,_ie){while(1){if(!B(_h8(_id,_ib))){if(!B(_gZ(_id,_ib))){if(!B(_go(_id,_ib))){return new F(function(){return _i8("GHC/Integer/Type.lhs:(553,5)-(555,32)|function l2");});}else{return E(_ie);}}else{return _ie-1|0;}}else{var _if=B(_gP(_id,1)),_ig=_ie+1|0;_id=_if;_ie=_ig;continue;}}};return new F(function(){return _ic(_h7,0);});},_ih=function(_ii){var _ij=E(_ii);if(!_ij._){var _ik=_ij.a>>>0;if(!_ik){return  -1;}else{var _il=function(_im,_in){while(1){if(_im>=_ik){if(_im<=_ik){if(_im!=_ik){return new F(function(){return _i8("GHC/Integer/Type.lhs:(609,5)-(611,40)|function l2");});}else{return E(_in);}}else{return _in-1|0;}}else{var _io=imul(_im,2)>>>0,_ip=_in+1|0;_im=_io;_in=_ip;continue;}}};return new F(function(){return _il(1,0);});}}else{return new F(function(){return _ia(_ij);});}},_iq=function(_ir){var _is=E(_ir);if(!_is._){var _it=_is.a>>>0;if(!_it){return new T2(0, -1,0);}else{var _iu=function(_iv,_iw){while(1){if(_iv>=_it){if(_iv<=_it){if(_iv!=_it){return new F(function(){return _i8("GHC/Integer/Type.lhs:(609,5)-(611,40)|function l2");});}else{return E(_iw);}}else{return _iw-1|0;}}else{var _ix=imul(_iv,2)>>>0,_iy=_iw+1|0;_iv=_ix;_iw=_iy;continue;}}};return new T2(0,B(_iu(1,0)),(_it&_it-1>>>0)>>>0&4294967295);}}else{var _iz=_is.a;return new T2(0,B(_ih(_is)),I_compareInt(I_and(_iz,I_sub(_iz,I_fromInt(1))),0));}},_iA=function(_iB,_iC){var _iD=E(_iB);if(!_iD._){var _iE=_iD.a,_iF=E(_iC);return (_iF._==0)?_iE<=_iF.a:I_compareInt(_iF.a,_iE)>=0;}else{var _iG=_iD.a,_iH=E(_iC);return (_iH._==0)?I_compareInt(_iG,_iH.a)<=0:I_compare(_iG,_iH.a)<=0;}},_iI=function(_iJ,_iK){while(1){var _iL=E(_iJ);if(!_iL._){var _iM=_iL.a,_iN=E(_iK);if(!_iN._){return new T1(0,(_iM>>>0&_iN.a>>>0)>>>0&4294967295);}else{_iJ=new T1(1,I_fromInt(_iM));_iK=_iN;continue;}}else{var _iO=E(_iK);if(!_iO._){_iJ=_iL;_iK=new T1(1,I_fromInt(_iO.a));continue;}else{return new T1(1,I_and(_iL.a,_iO.a));}}}},_iP=function(_iQ,_iR){while(1){var _iS=E(_iQ);if(!_iS._){var _iT=_iS.a,_iU=E(_iR);if(!_iU._){var _iV=_iU.a,_iW=subC(_iT,_iV);if(!E(_iW.b)){return new T1(0,_iW.a);}else{_iQ=new T1(1,I_fromInt(_iT));_iR=new T1(1,I_fromInt(_iV));continue;}}else{_iQ=new T1(1,I_fromInt(_iT));_iR=_iU;continue;}}else{var _iX=E(_iR);if(!_iX._){_iQ=_iS;_iR=new T1(1,I_fromInt(_iX.a));continue;}else{return new T1(1,I_sub(_iS.a,_iX.a));}}}},_iY=new T1(0,2),_iZ=function(_j0,_j1){var _j2=E(_j0);if(!_j2._){var _j3=(_j2.a>>>0&(2<<_j1>>>0)-1>>>0)>>>0,_j4=1<<_j1>>>0;return (_j4<=_j3)?(_j4>=_j3)?1:2:0;}else{var _j5=B(_iI(_j2,B(_iP(B(_gP(_iY,_j1)),_h7)))),_j6=B(_gP(_h7,_j1));return (!B(_gZ(_j6,_j5)))?(!B(_h8(_j6,_j5)))?1:2:0;}},_j7=function(_j8,_j9){while(1){var _ja=E(_j8);if(!_ja._){_j8=new T1(1,I_fromInt(_ja.a));continue;}else{return new T1(1,I_shiftRight(_ja.a,_j9));}}},_jb=function(_jc,_jd,_je,_jf){var _jg=B(_iq(_jf)),_jh=_jg.a;if(!E(_jg.b)){var _ji=B(_ih(_je));if(_ji<((_jh+_jc|0)-1|0)){var _jj=_jh+(_jc-_jd|0)|0;if(_jj>0){if(_jj>_ji){if(_jj<=(_ji+1|0)){if(!E(B(_iq(_je)).b)){return 0;}else{return new F(function(){return _gk(_g7,_jc-_jd|0);});}}else{return 0;}}else{var _jk=B(_j7(_je,_jj));switch(B(_iZ(_je,_jj-1|0))){case 0:return new F(function(){return _gk(_jk,_jc-_jd|0);});break;case 1:if(!(B(_fb(_jk))&1)){return new F(function(){return _gk(_jk,_jc-_jd|0);});}else{return new F(function(){return _gk(B(_gw(_jk,_g7)),_jc-_jd|0);});}break;default:return new F(function(){return _gk(B(_gw(_jk,_g7)),_jc-_jd|0);});}}}else{return new F(function(){return _gk(_je,(_jc-_jd|0)-_jj|0);});}}else{if(_ji>=_jd){var _jl=B(_j7(_je,(_ji+1|0)-_jd|0));switch(B(_iZ(_je,_ji-_jd|0))){case 0:return new F(function(){return _gk(_jl,((_ji-_jh|0)+1|0)-_jd|0);});break;case 2:return new F(function(){return _gk(B(_gw(_jl,_g7)),((_ji-_jh|0)+1|0)-_jd|0);});break;default:if(!(B(_fb(_jl))&1)){return new F(function(){return _gk(_jl,((_ji-_jh|0)+1|0)-_jd|0);});}else{return new F(function(){return _gk(B(_gw(_jl,_g7)),((_ji-_jh|0)+1|0)-_jd|0);});}}}else{return new F(function(){return _gk(_je, -_jh);});}}}else{var _jm=B(_ih(_je))-_jh|0,_jn=function(_jo){var _jp=function(_jq,_jr){if(!B(_iA(B(_gP(_jr,_jd)),_jq))){return new F(function(){return _gT(_jo-_jd|0,_jq,_jr);});}else{return new F(function(){return _gT((_jo-_jd|0)+1|0,_jq,B(_gP(_jr,1)));});}};if(_jo>=_jd){if(_jo!=_jd){return new F(function(){return _jp(_je,new T(function(){return B(_gP(_jf,_jo-_jd|0));}));});}else{return new F(function(){return _jp(_je,_jf);});}}else{return new F(function(){return _jp(new T(function(){return B(_gP(_je,_jd-_jo|0));}),_jf);});}};if(_jc>_jm){return new F(function(){return _jn(_jc);});}else{return new F(function(){return _jn(_jm);});}}},_js=new T1(0,2147483647),_jt=new T(function(){return B(_gw(_js,_h7));}),_ju=function(_jv){var _jw=E(_jv);if(!_jw._){var _jx=E(_jw.a);return (_jx==( -2147483648))?E(_jt):new T1(0, -_jx);}else{return new T1(1,I_negate(_jw.a));}},_jy=new T(function(){return 0/0;}),_jz=new T(function(){return  -1/0;}),_jA=new T(function(){return 1/0;}),_jB=0,_jC=function(_jD,_jE){if(!B(_go(_jE,_gO))){if(!B(_go(_jD,_gO))){if(!B(_h8(_jD,_gO))){return new F(function(){return _jb( -1021,53,_jD,_jE);});}else{return  -B(_jb( -1021,53,B(_ju(_jD)),_jE));}}else{return E(_jB);}}else{return (!B(_go(_jD,_gO)))?(!B(_h8(_jD,_gO)))?E(_jA):E(_jz):E(_jy);}},_jF=function(_jG){var _jH=E(_jG);return new F(function(){return _jC(_jH.a,_jH.b);});},_jI=function(_jJ){return 1/E(_jJ);},_jK=function(_jL){var _jM=E(_jL);return (_jM!=0)?(_jM<=0)? -_jM:E(_jM):E(_jB);},_jN=function(_jO){var _jP=E(_jO);if(!_jP._){return _jP.a;}else{return new F(function(){return I_toNumber(_jP.a);});}},_jQ=function(_jR){return new F(function(){return _jN(_jR);});},_jS=1,_jT= -1,_jU=function(_jV){var _jW=E(_jV);return (_jW<=0)?(_jW>=0)?E(_jW):E(_jT):E(_jS);},_jX=function(_jY,_jZ){return E(_jY)-E(_jZ);},_k0=function(_k1){return  -E(_k1);},_k2=function(_k3,_k4){return E(_k3)+E(_k4);},_k5=function(_k6,_k7){return E(_k6)*E(_k7);},_k8={_:0,a:_k2,b:_jX,c:_k5,d:_k0,e:_jK,f:_jU,g:_jQ},_k9=function(_ka,_kb){return E(_ka)/E(_kb);},_kc=new T4(0,_k8,_k9,_jI,_jF),_kd=function(_ke){return new F(function(){return Math.acos(E(_ke));});},_kf=function(_kg){return new F(function(){return Math.asin(E(_kg));});},_kh=function(_ki){return new F(function(){return Math.atan(E(_ki));});},_kj=function(_kk){return new F(function(){return Math.cos(E(_kk));});},_kl=function(_km){return new F(function(){return cosh(E(_km));});},_kn=function(_ko){return new F(function(){return Math.exp(E(_ko));});},_kp=function(_kq){return new F(function(){return Math.log(E(_kq));});},_kr=function(_ks,_kt){return new F(function(){return Math.pow(E(_ks),E(_kt));});},_ku=function(_kv){return new F(function(){return Math.sin(E(_kv));});},_kw=function(_kx){return new F(function(){return sinh(E(_kx));});},_ky=function(_kz){return new F(function(){return Math.sqrt(E(_kz));});},_kA=function(_kB){return new F(function(){return Math.tan(E(_kB));});},_kC=function(_kD){return new F(function(){return tanh(E(_kD));});},_kE={_:0,a:_kc,b:_g6,c:_kn,d:_kp,e:_ky,f:_kr,g:_g3,h:_ku,i:_kj,j:_kA,k:_kf,l:_kd,m:_kh,n:_kw,o:_kl,p:_kC,q:_fX,r:_fU,s:_g0},_kF=0,_kG=function(_){return _kF;},_kH=new T(function(){return eval("(function(ctx){ctx.restore();})");}),_kI=new T(function(){return eval("(function(ctx){ctx.save();})");}),_kJ=new T(function(){return eval("(function(ctx,rad){ctx.rotate(rad);})");}),_kK=function(_kL,_kM,_kN,_){var _kO=__app1(E(_kI),_kN),_kP=__app2(E(_kJ),_kN,E(_kL)),_kQ=B(A2(_kM,_kN,_)),_kR=__app1(E(_kH),_kN);return new F(function(){return _kG(_);});},_kS=new T(function(){return eval("(function(ctx,x,y){ctx.translate(x,y);})");}),_kT=function(_kU,_kV,_kW,_kX,_){var _kY=__app1(E(_kI),_kX),_kZ=__app3(E(_kS),_kX,E(_kU),E(_kV)),_l0=B(A2(_kW,_kX,_)),_l1=__app1(E(_kH),_kX);return new F(function(){return _kG(_);});},_l2=function(_l3,_l4){return E(_l3)!=E(_l4);},_l5=function(_l6,_l7){return E(_l6)==E(_l7);},_l8=new T2(0,_l5,_l2),_l9=function(_la){return E(E(_la).a);},_lb=function(_lc){return E(E(_lc).a);},_ld=function(_le){return E(E(_le).b);},_lf=function(_lg){return E(E(_lg).g);},_lh=new T(function(){return B(unCStr("\u30fc\u301c\u3002\u300c\uff1c\uff1e\uff08\uff09"));}),_li=0,_lj=3.3333333333333335,_lk=16.666666666666668,_ll=function(_lm){return E(E(_lm).b);},_ln=new T1(0,0),_lo=new T1(0,2),_lp=function(_lq){return E(E(_lq).i);},_lr=function(_ls,_lt,_lu,_lv,_lw,_lx,_ly,_lz){var _lA=new T(function(){var _lB=E(_lz);if(_lB<=31){return B(_4H(_l8,_lB,_lh));}else{if(_lB>=128){return B(_4H(_l8,_lB,_lh));}else{return true;}}}),_lC=new T(function(){if(E(_lv)==8){return new T2(0,new T(function(){return B(_jN(B(A2(_lp,_lt,_lx))))*28+20;}),new T(function(){return B(_jN(B(A2(_lp,_lu,_ly))))*24+8*(E(_lw)-1);}));}else{return new T2(0,new T(function(){return B(_jN(B(A2(_lp,_lt,_lx))))*28;}),new T(function(){return B(_jN(B(A2(_lp,_lu,_ly))))*24;}));}}),_lD=new T(function(){var _lE=B(_l9(_ls));if(!E(_lA)){return B(A2(_lf,B(_lb(_lE)),_ln));}else{return B(A3(_ld,_lE,new T(function(){return B(_ll(_ls));}),new T(function(){return B(A2(_lf,B(_lb(_lE)),_lo));})));}});return new T3(0,new T2(0,new T(function(){return E(E(_lC).a);}),new T(function(){return E(E(_lC).b);})),new T2(0,new T(function(){if(!E(_lA)){return E(_li);}else{return E(_lj);}}),new T(function(){if(!E(_lA)){return E(_li);}else{return E(_lk);}})),_lD);},_lF=new T(function(){return eval("(function(ctx,s,x,y){ctx.fillText(s,x,y);})");}),_lG=function(_lH,_lI,_lJ){var _lK=new T(function(){return toJSStr(E(_lJ));});return function(_lL,_){var _lM=__app4(E(_lF),E(_lL),E(_lK),E(_lH),E(_lI));return new F(function(){return _kG(_);});};},_lN=0,_lO=",",_lP="rgba(",_lQ=new T(function(){return toJSStr(_Z);}),_lR="rgb(",_lS=")",_lT=new T2(1,_lS,_Z),_lU=function(_lV){var _lW=E(_lV);if(!_lW._){var _lX=jsCat(new T2(1,_lR,new T2(1,new T(function(){return String(_lW.a);}),new T2(1,_lO,new T2(1,new T(function(){return String(_lW.b);}),new T2(1,_lO,new T2(1,new T(function(){return String(_lW.c);}),_lT)))))),E(_lQ));return E(_lX);}else{var _lY=jsCat(new T2(1,_lP,new T2(1,new T(function(){return String(_lW.a);}),new T2(1,_lO,new T2(1,new T(function(){return String(_lW.b);}),new T2(1,_lO,new T2(1,new T(function(){return String(_lW.c);}),new T2(1,_lO,new T2(1,new T(function(){return String(_lW.d);}),_lT)))))))),E(_lQ));return E(_lY);}},_lZ="strokeStyle",_m0="fillStyle",_m1=new T(function(){return eval("(function(e,p){var x = e[p];return typeof x === \'undefined\' ? \'\' : x.toString();})");}),_m2=new T(function(){return eval("(function(e,p,v){e[p] = v;})");}),_m3=function(_m4,_m5){var _m6=new T(function(){return B(_lU(_m4));});return function(_m7,_){var _m8=E(_m7),_m9=E(_m0),_ma=E(_m1),_mb=__app2(_ma,_m8,_m9),_mc=E(_lZ),_md=__app2(_ma,_m8,_mc),_me=E(_m6),_mf=E(_m2),_mg=__app3(_mf,_m8,_m9,_me),_mh=__app3(_mf,_m8,_mc,_me),_mi=B(A2(_m5,_m8,_)),_mj=String(_mb),_mk=__app3(_mf,_m8,_m9,_mj),_ml=String(_md),_mm=__app3(_mf,_m8,_mc,_ml);return new F(function(){return _kG(_);});};},_mn="font",_mo=function(_mp,_mq){var _mr=new T(function(){return toJSStr(E(_mp));});return function(_ms,_){var _mt=E(_ms),_mu=E(_mn),_mv=__app2(E(_m1),_mt,_mu),_mw=E(_m2),_mx=__app3(_mw,_mt,_mu,E(_mr)),_my=B(A2(_mq,_mt,_)),_mz=String(_mv),_mA=__app3(_mw,_mt,_mu,_mz);return new F(function(){return _kG(_);});};},_mB=new T(function(){return B(unCStr("px IPAGothic"));}),_mC=function(_mD,_mE,_mF,_mG,_mH,_mI,_mJ,_){var _mK=new T(function(){var _mL=new T(function(){var _mM=B(_lr(_kE,_fT,_fT,_mF,_mG,_mH,_mI,_mJ)),_mN=E(_mM.a),_mO=E(_mM.b);return new T5(0,_mN.a,_mN.b,_mO.a,_mO.b,_mM.c);}),_mP=new T(function(){var _mQ=E(_mL);return E(_mQ.a)+E(_mQ.c);}),_mR=new T(function(){var _mS=E(_mL);return E(_mS.b)-E(_mS.d);}),_mT=new T(function(){return E(E(_mL).e);}),_mU=new T(function(){return B(_lG(_lN,_lN,new T2(1,_mJ,_Z)));}),_mV=function(_mW,_){return new F(function(){return _kK(_mT,_mU,E(_mW),_);});};return B(_mo(new T(function(){return B(_x(B(_H(0,E(_mF),_Z)),_mB));},1),function(_mX,_){return new F(function(){return _kT(_mP,_mR,_mV,E(_mX),_);});}));});return new F(function(){return A(_m3,[_mE,_mK,_mD,_]);});},_mY=new T3(0,153,255,255),_mZ=new T2(1,_mY,_Z),_n0=new T3(0,255,153,204),_n1=new T2(1,_n0,_mZ),_n2=new T3(0,255,204,153),_n3=new T2(1,_n2,_n1),_n4=new T3(0,200,255,200),_n5=new T2(1,_n4,_n3),_n6=20,_n7=64,_n8=1,_n9=2,_na=8,_nb=function(_nc,_nd,_ne,_nf,_ng,_nh,_ni,_){while(1){var _nj=B((function(_nk,_nl,_nm,_nn,_no,_np,_nq,_){var _nr=E(_nq);if(!_nr._){return _kF;}else{var _ns=_nr.b,_nt=E(_nr.a),_nu=E(_nt);switch(_nu){case 10:var _nv=_nk,_nw=_nl,_nx=_nn,_ny=_nn;_nc=_nv;_nd=_nw;_ne=0;_nf=_nx;_ng=new T(function(){return E(_no)-1|0;});_nh=_ny;_ni=_ns;return __continue;case 123:return new F(function(){return _nz(_nk,_nl,_nm,_nn,_no,_np,_ns,_);});break;case 65306:var _nA=new T(function(){return B(_aS(_n5,_nm));}),_nB=function(_nC,_nD,_nE,_nF,_nG,_nH,_){while(1){var _nI=B((function(_nJ,_nK,_nL,_nM,_nN,_nO,_){var _nP=E(_nO);if(!_nP._){return _kF;}else{var _nQ=_nP.b,_nR=E(_nP.a);if(E(_nR)==65306){var _nS=new T(function(){var _nT=E(_nN);if((_nT+1)*24<=E(_nl)-10){return new T2(0,_nM,_nT+1|0);}else{return new T2(0,new T(function(){return E(_nM)-1|0;}),_nK);}});return new F(function(){return _nb(_nJ,_nl,_nm,_nK,new T(function(){return E(E(_nS).a);}),new T(function(){return E(E(_nS).b);}),_nQ,_);});}else{var _nU=E(_nJ),_nV=B(_mC(_nU.a,_nA,_na,_nL,_nM,_nN,_nR,_)),_nW=_nK,_nX=_nL+1,_nY=_nM,_nZ=_nN;_nC=_nU;_nD=_nW;_nE=_nX;_nF=_nY;_nG=_nZ;_nH=_nQ;return __continue;}}})(_nC,_nD,_nE,_nF,_nG,_nH,_));if(_nI!=__continue){return _nI;}}};return new F(function(){return _nB(_nk,_nn,0,new T(function(){if(E(_nn)!=E(_np)){return E(_no);}else{return E(_no)+1|0;}}),new T(function(){var _o0=E(_np);if(E(_nn)!=_o0){return _o0-1|0;}else{var _o1=(E(_nl)-10)/24,_o2=_o1&4294967295;if(_o1>=_o2){return _o2;}else{return _o2-1|0;}}}),_ns,_);});break;default:var _o3=function(_o4,_o5){var _o6=new T(function(){switch(E(_nu)){case 42:return E(_n9);break;case 12300:return E(_n8);break;default:return _nm;}}),_o7=new T(function(){var _o8=E(_np);if((_o8+1)*24<=E(_nl)-10){return new T2(0,_no,_o8+1|0);}else{return new T2(0,new T(function(){return E(_no)-1|0;}),_nn);}});if(E(_o4)==64){return new F(function(){return _o9(_nk,_nl,_o6,_nn,new T(function(){return E(E(_o7).a);}),new T(function(){return E(E(_o7).b);}),_ns,_);});}else{var _oa=E(_nk),_ob=B(_mC(_oa.a,new T(function(){return B(_aS(_n5,E(_o6)));},1),_n6,_lN,_no,_np,_o5,_));return new F(function(){return _o9(_oa,_nl,_o6,_nn,new T(function(){return E(E(_o7).a);}),new T(function(){return E(E(_o7).b);}),_ns,_);});}},_oc=E(_nu);switch(_oc){case 42:return new F(function(){return _o3(64,_n7);});break;case 12289:return new F(function(){return _o3(64,_n7);});break;case 12290:return new F(function(){return _o3(64,_n7);});break;default:return new F(function(){return _o3(_oc,_nt);});}}}})(_nc,_nd,_ne,_nf,_ng,_nh,_ni,_));if(_nj!=__continue){return _nj;}}},_o9=function(_od,_oe,_of,_og,_oh,_oi,_oj,_){var _ok=E(_oj);if(!_ok._){return _kF;}else{var _ol=_ok.b,_om=E(_ok.a),_on=E(_om);switch(_on){case 10:return new F(function(){return _nb(_od,_oe,0,_og,new T(function(){return E(_oh)-1|0;}),_og,_ol,_);});break;case 123:return new F(function(){return _nz(_od,_oe,_of,_og,_oh,_oi,_ol,_);});break;case 65306:var _oo=new T(function(){return B(_aS(_n5,E(_of)));}),_op=function(_oq,_or,_os,_ot,_ou,_ov,_){while(1){var _ow=B((function(_ox,_oy,_oz,_oA,_oB,_oC,_){var _oD=E(_oC);if(!_oD._){return _kF;}else{var _oE=_oD.b,_oF=E(_oD.a);if(E(_oF)==65306){var _oG=new T(function(){var _oH=E(_oB);if((_oH+1)*24<=E(_oe)-10){return new T2(0,_oA,_oH+1|0);}else{return new T2(0,new T(function(){return E(_oA)-1|0;}),_oy);}});return new F(function(){return _o9(_ox,_oe,_of,_oy,new T(function(){return E(E(_oG).a);}),new T(function(){return E(E(_oG).b);}),_oE,_);});}else{var _oI=E(_ox),_oJ=B(_mC(_oI.a,_oo,_na,_oz,_oA,_oB,_oF,_)),_oK=_oy,_oL=_oz+1,_oM=_oA,_oN=_oB;_oq=_oI;_or=_oK;_os=_oL;_ot=_oM;_ou=_oN;_ov=_oE;return __continue;}}})(_oq,_or,_os,_ot,_ou,_ov,_));if(_ow!=__continue){return _ow;}}};return new F(function(){return _op(_od,_og,0,new T(function(){if(E(_og)!=E(_oi)){return E(_oh);}else{return E(_oh)+1|0;}}),new T(function(){var _oO=E(_oi);if(E(_og)!=_oO){return _oO-1|0;}else{var _oP=(E(_oe)-10)/24,_oQ=_oP&4294967295;if(_oP>=_oQ){return _oQ;}else{return _oQ-1|0;}}}),_ol,_);});break;default:var _oR=function(_oS,_oT){var _oU=new T(function(){switch(E(_on)){case 42:return E(_n9);break;case 12300:return E(_n8);break;default:return E(_of);}}),_oV=new T(function(){var _oW=E(_oi);if((_oW+1)*24<=E(_oe)-10){return new T2(0,_oh,_oW+1|0);}else{return new T2(0,new T(function(){return E(_oh)-1|0;}),_og);}});if(E(_oS)==64){return new F(function(){return _o9(_od,_oe,_oU,_og,new T(function(){return E(E(_oV).a);}),new T(function(){return E(E(_oV).b);}),_ol,_);});}else{var _oX=E(_od),_oY=B(_mC(_oX.a,new T(function(){return B(_aS(_n5,E(_oU)));},1),_n6,_lN,_oh,_oi,_oT,_));return new F(function(){return _o9(_oX,_oe,_oU,_og,new T(function(){return E(E(_oV).a);}),new T(function(){return E(E(_oV).b);}),_ol,_);});}},_oZ=E(_on);switch(_oZ){case 42:return new F(function(){return _oR(64,_n7);});break;case 12289:return new F(function(){return _oR(64,_n7);});break;case 12290:return new F(function(){return _oR(64,_n7);});break;default:return new F(function(){return _oR(_oZ,_om);});}}}},_nz=function(_p0,_p1,_p2,_p3,_p4,_p5,_p6,_){while(1){var _p7=B((function(_p8,_p9,_pa,_pb,_pc,_pd,_pe,_){var _pf=E(_pe);if(!_pf._){return _kF;}else{var _pg=_pf.b;if(E(_pf.a)==125){var _ph=new T(function(){var _pi=E(_pd);if((_pi+1)*24<=E(_p9)-10){return new T2(0,_pc,_pi+1|0);}else{return new T2(0,new T(function(){return E(_pc)-1|0;}),_pb);}});return new F(function(){return _o9(_p8,_p9,_pa,_pb,new T(function(){return E(E(_ph).a);}),new T(function(){return E(E(_ph).b);}),_pg,_);});}else{var _pj=_p8,_pk=_p9,_pl=_pa,_pm=_pb,_pn=_pc,_po=_pd;_p0=_pj;_p1=_pk;_p2=_pl;_p3=_pm;_p4=_pn;_p5=_po;_p6=_pg;return __continue;}}})(_p0,_p1,_p2,_p3,_p4,_p5,_p6,_));if(_p7!=__continue){return _p7;}}},_pp=function(_pq,_pr,_ps,_pt,_pu,_pv,_pw,_px,_){while(1){var _py=B((function(_pz,_pA,_pB,_pC,_pD,_pE,_pF,_pG,_){var _pH=E(_pG);if(!_pH._){return _kF;}else{var _pI=_pH.b,_pJ=E(_pH.a),_pK=E(_pJ);switch(_pK){case 10:var _pL=_pz,_pM=_pA,_pN=_pB,_pO=_pD,_pP=_pD;_pq=_pL;_pr=_pM;_ps=_pN;_pt=0;_pu=_pO;_pv=new T(function(){return E(_pE)-1|0;});_pw=_pP;_px=_pI;return __continue;case 123:return new F(function(){return _nz(new T2(0,_pz,_pA),_pB,_pC,_pD,_pE,_pF,_pI,_);});break;case 65306:var _pQ=new T(function(){return B(_aS(_n5,_pC));}),_pR=function(_pS,_pT,_pU,_pV,_pW,_pX,_pY,_){while(1){var _pZ=B((function(_q0,_q1,_q2,_q3,_q4,_q5,_q6,_){var _q7=E(_q6);if(!_q7._){return _kF;}else{var _q8=_q7.b,_q9=E(_q7.a);if(E(_q9)==65306){var _qa=new T(function(){var _qb=E(_q5);if((_qb+1)*24<=E(_pB)-10){return new T2(0,_q4,_qb+1|0);}else{return new T2(0,new T(function(){return E(_q4)-1|0;}),_q2);}});return new F(function(){return _pp(_q0,_q1,_pB,_pC,_q2,new T(function(){return E(E(_qa).a);}),new T(function(){return E(E(_qa).b);}),_q8,_);});}else{var _qc=B(_mC(_q0,_pQ,_na,_q3,_q4,_q5,_q9,_)),_qd=_q0,_qe=_q1,_qf=_q2,_qg=_q3+1,_qh=_q4,_qi=_q5;_pS=_qd;_pT=_qe;_pU=_qf;_pV=_qg;_pW=_qh;_pX=_qi;_pY=_q8;return __continue;}}})(_pS,_pT,_pU,_pV,_pW,_pX,_pY,_));if(_pZ!=__continue){return _pZ;}}};return new F(function(){return _pR(_pz,_pA,_pD,0,new T(function(){if(E(_pD)!=E(_pF)){return E(_pE);}else{return E(_pE)+1|0;}}),new T(function(){var _qj=E(_pF);if(E(_pD)!=_qj){return _qj-1|0;}else{var _qk=(E(_pB)-10)/24,_ql=_qk&4294967295;if(_qk>=_ql){return _ql;}else{return _ql-1|0;}}}),_pI,_);});break;default:var _qm=function(_qn,_qo){var _qp=new T(function(){switch(E(_pK)){case 42:return E(_n9);break;case 12300:return E(_n8);break;default:return _pC;}}),_qq=new T(function(){var _qr=E(_pF);if((_qr+1)*24<=E(_pB)-10){return new T2(0,_pE,_qr+1|0);}else{return new T2(0,new T(function(){return E(_pE)-1|0;}),_pD);}});if(E(_qn)==64){return new F(function(){return _o9(new T2(0,_pz,_pA),_pB,_qp,_pD,new T(function(){return E(E(_qq).a);}),new T(function(){return E(E(_qq).b);}),_pI,_);});}else{var _qs=B(_mC(_pz,new T(function(){return B(_aS(_n5,E(_qp)));},1),_n6,_lN,_pE,_pF,_qo,_));return new F(function(){return _o9(new T2(0,_pz,_pA),_pB,_qp,_pD,new T(function(){return E(E(_qq).a);}),new T(function(){return E(E(_qq).b);}),_pI,_);});}},_qt=E(_pK);switch(_qt){case 42:return new F(function(){return _qm(64,_n7);});break;case 12289:return new F(function(){return _qm(64,_n7);});break;case 12290:return new F(function(){return _qm(64,_n7);});break;default:return new F(function(){return _qm(_qt,_pJ);});}}}})(_pq,_pr,_ps,_pt,_pu,_pv,_pw,_px,_));if(_py!=__continue){return _py;}}},_qu=function(_qv,_qw){while(1){var _qx=E(_qv);if(!_qx._){return E(_qw);}else{var _qy=_qw+1|0;_qv=_qx.b;_qw=_qy;continue;}}},_qz=function(_qA,_){return _kF;},_qB=function(_qC){return E(E(_qC).a);},_qD=function(_qE,_qF){var _qG=E(_qF),_qH=new T(function(){var _qI=B(_lb(_qE)),_qJ=B(_qD(_qE,B(A3(_qB,_qI,_qG,new T(function(){return B(A2(_lf,_qI,_eW));})))));return new T2(1,_qJ.a,_qJ.b);});return new T2(0,_qG,_qH);},_qK=new T(function(){var _qL=B(_qD(_kc,_lN));return new T2(1,_qL.a,_qL.b);}),_qM=new T(function(){return B(_H(0,20,_Z));}),_qN=new T(function(){return B(unCStr("px Courier"));}),_qO=new T(function(){return B(_x(_qM,_qN));}),_qP=function(_qQ,_qR,_qS,_qT,_qU){var _qV=new T(function(){return E(_qS)*16;}),_qW=new T(function(){return E(_qT)*20;}),_qX=function(_qY,_qZ){var _r0=E(_qY);if(!_r0._){return E(_qz);}else{var _r1=E(_qZ);if(!_r1._){return E(_qz);}else{var _r2=new T(function(){return B(_qX(_r0.b,_r1.b));}),_r3=new T(function(){var _r4=new T(function(){var _r5=new T(function(){return B(_lG(new T(function(){return E(_qV)+16*E(_r1.a);}),_qW,new T2(1,_r0.a,_Z)));});return B(_mo(_qO,_r5));});return B(_m3(_qR,_r4));});return function(_r6,_){var _r7=B(A2(_r3,_r6,_));return new F(function(){return A2(_r2,_r6,_);});};}}};return new F(function(){return A3(_qX,_qU,_qK,_qQ);});},_r8=45,_r9=new T(function(){return B(unCStr("-"));}),_ra=new T2(1,_r8,_r9),_rb=function(_rc){var _rd=E(_rc);return (_rd==1)?E(_ra):new T2(1,_r8,new T(function(){return B(_rb(_rd-1|0));}));},_re=new T(function(){return B(unCStr(": empty list"));}),_rf=function(_rg){return new F(function(){return err(B(_x(_aH,new T(function(){return B(_x(_rg,_re));},1))));});},_rh=new T(function(){return B(unCStr("head"));}),_ri=new T(function(){return B(_rf(_rh));}),_rj=new T(function(){return eval("(function(e){e.width = e.width;})");}),_rk=new T(function(){return B(_lG(_lN,_lN,_Z));}),_rl=32,_rm=new T(function(){return B(unCStr("|"));}),_rn=function(_ro){var _rp=E(_ro);return (_rp._==0)?E(_rm):new T2(1,new T(function(){var _rq=E(_rp.a);switch(E(_rq.b)){case 7:return E(_rl);break;case 8:return E(_rl);break;default:return E(_rq.a);}}),new T(function(){return B(_rn(_rp.b));}));},_rr=function(_rs,_rt,_ru,_rv,_rw,_){var _rx=__app1(E(_rj),_rt),_ry=B(A2(_rk,_rs,_)),_rz=B(unAppCStr("-",new T(function(){var _rA=E(_rw);if(!_rA._){return E(_ri);}else{var _rB=B(_qu(_rA.a,0));if(0>=_rB){return E(_r9);}else{return B(_rb(_rB));}}}))),_rC=B(A(_qP,[_rs,_n4,_ru,_rv,_rz,_])),_rD=function(_rE,_rF,_rG,_){while(1){var _rH=B((function(_rI,_rJ,_rK,_){var _rL=E(_rK);if(!_rL._){return new F(function(){return A(_qP,[_rs,_n4,_rI,_rJ,_rz,_]);});}else{var _rM=B(A(_qP,[_rs,_n4,_rI,_rJ,B(unAppCStr("|",new T(function(){return B(_rn(_rL.a));}))),_])),_rN=_rI;_rE=_rN;_rF=new T(function(){return E(_rJ)+1|0;});_rG=_rL.b;return __continue;}})(_rE,_rF,_rG,_));if(_rH!=__continue){return _rH;}}};return new F(function(){return _rD(_ru,new T(function(){return E(_rv)+1|0;}),_rw,_);});},_rO=new T(function(){return eval("(function(ctx,x,y){ctx.scale(x,y);})");}),_rP=function(_rQ,_rR,_rS,_rT,_){var _rU=__app1(E(_kI),_rT),_rV=__app3(E(_rO),_rT,E(_rQ),E(_rR)),_rW=B(A2(_rS,_rT,_)),_rX=__app1(E(_kH),_rT);return new F(function(){return _kG(_);});},_rY=new T(function(){return eval("(function(ctx,i,x,y){ctx.drawImage(i,x,y);})");}),_rZ=function(_s0,_s1,_s2,_s3,_){var _s4=__app4(E(_rY),_s3,_s0,_s1,_s2);return new F(function(){return _kG(_);});},_s5=2,_s6=40,_s7=new T(function(){return B(_aS(_n5,1));}),_s8=new T(function(){return B(_aS(_n5,2));}),_s9=2,_sa=function(_sb,_sc,_sd,_se,_sf,_sg,_){var _sh=__app1(E(_rj),_sc),_si=B(A2(_rk,_sb,_)),_sj=E(_sg),_sk=E(_sj.b).a,_sl=E(_sj.a),_sm=_sl.a,_sn=E(_sj.s);if(!E(E(_sj.v).h)){return _kF;}else{var _so=B(_rr(_sb,_sc,new T(function(){return B(_f5(_se,_sk));}),_s9,_sl.b,_)),_sp=B(A(_qP,[_sb,new T(function(){if(E(_sl.e)==32){return E(_s7);}else{return E(_s8);}}),new T(function(){return ((E(E(_sm).a)+1|0)+E(_se)|0)-E(_sk)|0;},1),new T(function(){return (E(E(_sm).b)+2|0)+1|0;},1),new T2(1,_sl.d,_Z),_])),_sq=function(_sr,_){return new F(function(){return _rP(_s5,_s5,function(_ss,_){return new F(function(){return _rZ(B(_aS(E(_sf).b,(imul(E(_sn.a),8)|0)+E(_sn.b)|0)),0,0,E(_ss),_);});},E(_sr),_);});};return new F(function(){return _kT(new T(function(){return E(_sd)-(E(_sk)+10|0)*16;},1),_s6,_sq,_sb,_);});}},_st=function(_su){return E(E(_su).a);},_sv=function(_sw){return E(E(_sw).a);},_sx=function(_sy,_sz){while(1){var _sA=E(_sy);if(!_sA._){return E(_sz);}else{_sy=_sA.b;_sz=_sA.a;continue;}}},_sB=function(_sC,_sD,_sE){return new F(function(){return _sx(_sD,_sC);});},_sF=new T1(0,2),_sG=function(_sH,_sI){while(1){var _sJ=E(_sH);if(!_sJ._){var _sK=_sJ.a,_sL=E(_sI);if(!_sL._){var _sM=_sL.a;if(!(imul(_sK,_sM)|0)){return new T1(0,imul(_sK,_sM)|0);}else{_sH=new T1(1,I_fromInt(_sK));_sI=new T1(1,I_fromInt(_sM));continue;}}else{_sH=new T1(1,I_fromInt(_sK));_sI=_sL;continue;}}else{var _sN=E(_sI);if(!_sN._){_sH=_sJ;_sI=new T1(1,I_fromInt(_sN.a));continue;}else{return new T1(1,I_mul(_sJ.a,_sN.a));}}}},_sO=function(_sP,_sQ,_sR){while(1){if(!(_sQ%2)){var _sS=B(_sG(_sP,_sP)),_sT=quot(_sQ,2);_sP=_sS;_sQ=_sT;continue;}else{var _sU=E(_sQ);if(_sU==1){return new F(function(){return _sG(_sP,_sR);});}else{var _sS=B(_sG(_sP,_sP)),_sV=B(_sG(_sP,_sR));_sP=_sS;_sQ=quot(_sU-1|0,2);_sR=_sV;continue;}}}},_sW=function(_sX,_sY){while(1){if(!(_sY%2)){var _sZ=B(_sG(_sX,_sX)),_t0=quot(_sY,2);_sX=_sZ;_sY=_t0;continue;}else{var _t1=E(_sY);if(_t1==1){return E(_sX);}else{return new F(function(){return _sO(B(_sG(_sX,_sX)),quot(_t1-1|0,2),_sX);});}}}},_t2=function(_t3){return E(E(_t3).c);},_t4=function(_t5){return E(E(_t5).a);},_t6=function(_t7){return E(E(_t7).b);},_t8=function(_t9){return E(E(_t9).b);},_ta=function(_tb){return E(E(_tb).c);},_tc=new T1(0,0),_td=new T1(0,2),_te=function(_tf){return E(E(_tf).d);},_tg=function(_th,_ti){var _tj=B(_st(_th)),_tk=new T(function(){return B(_sv(_tj));}),_tl=new T(function(){return B(A3(_te,_th,_ti,new T(function(){return B(A2(_lf,_tk,_td));})));});return new F(function(){return A3(_4F,B(_t4(B(_t6(_tj)))),_tl,new T(function(){return B(A2(_lf,_tk,_tc));}));});},_tm=new T(function(){return B(unCStr("Negative exponent"));}),_tn=new T(function(){return B(err(_tm));}),_to=function(_tp){return E(E(_tp).c);},_tq=function(_tr,_ts,_tt,_tu){var _tv=B(_st(_ts)),_tw=new T(function(){return B(_sv(_tv));}),_tx=B(_t6(_tv));if(!B(A3(_ta,_tx,_tu,new T(function(){return B(A2(_lf,_tw,_tc));})))){if(!B(A3(_4F,B(_t4(_tx)),_tu,new T(function(){return B(A2(_lf,_tw,_tc));})))){var _ty=new T(function(){return B(A2(_lf,_tw,_td));}),_tz=new T(function(){return B(A2(_lf,_tw,_eW));}),_tA=B(_t4(_tx)),_tB=function(_tC,_tD,_tE){while(1){var _tF=B((function(_tG,_tH,_tI){if(!B(_tg(_ts,_tH))){if(!B(A3(_4F,_tA,_tH,_tz))){var _tJ=new T(function(){return B(A3(_to,_ts,new T(function(){return B(A3(_t8,_tw,_tH,_tz));}),_ty));});_tC=new T(function(){return B(A3(_t2,_tr,_tG,_tG));});_tD=_tJ;_tE=new T(function(){return B(A3(_t2,_tr,_tG,_tI));});return __continue;}else{return new F(function(){return A3(_t2,_tr,_tG,_tI);});}}else{var _tK=_tI;_tC=new T(function(){return B(A3(_t2,_tr,_tG,_tG));});_tD=new T(function(){return B(A3(_to,_ts,_tH,_ty));});_tE=_tK;return __continue;}})(_tC,_tD,_tE));if(_tF!=__continue){return _tF;}}},_tL=function(_tM,_tN){while(1){var _tO=B((function(_tP,_tQ){if(!B(_tg(_ts,_tQ))){if(!B(A3(_4F,_tA,_tQ,_tz))){var _tR=new T(function(){return B(A3(_to,_ts,new T(function(){return B(A3(_t8,_tw,_tQ,_tz));}),_ty));});return new F(function(){return _tB(new T(function(){return B(A3(_t2,_tr,_tP,_tP));}),_tR,_tP);});}else{return E(_tP);}}else{_tM=new T(function(){return B(A3(_t2,_tr,_tP,_tP));});_tN=new T(function(){return B(A3(_to,_ts,_tQ,_ty));});return __continue;}})(_tM,_tN));if(_tO!=__continue){return _tO;}}};return new F(function(){return _tL(_tt,_tu);});}else{return new F(function(){return A2(_lf,_tr,_eW);});}}else{return E(_tn);}},_tS=new T(function(){return B(err(_tm));}),_tT=function(_tU){var _tV=I_decodeDouble(_tU);return new T2(0,new T1(1,_tV.b),_tV.a);},_tW=function(_tX,_tY){var _tZ=B(_tT(_tY)),_u0=_tZ.a,_u1=_tZ.b,_u2=new T(function(){return B(_sv(new T(function(){return B(_st(_tX));})));});if(_u1<0){var _u3= -_u1;if(_u3>=0){var _u4=E(_u3);if(!_u4){var _u5=E(_eW);}else{var _u5=B(_sW(_sF,_u4));}if(!B(_go(_u5,_gO))){var _u6=B(_gF(_u0,_u5));return new T2(0,new T(function(){return B(A2(_lf,_u2,_u6.a));}),new T(function(){return B(_gk(_u6.b,_u1));}));}else{return E(_dV);}}else{return E(_tS);}}else{var _u7=new T(function(){var _u8=new T(function(){return B(_tq(_u2,_fT,new T(function(){return B(A2(_lf,_u2,_sF));}),_u1));});return B(A3(_t2,_u2,new T(function(){return B(A2(_lf,_u2,_u0));}),_u8));});return new T2(0,_u7,_jB);}},_u9=function(_ua,_ub){while(1){var _uc=E(_ub);if(!_uc._){return __Z;}else{var _ud=_uc.b,_ue=E(_ua);if(_ue==1){return E(_ud);}else{_ua=_ue-1|0;_ub=_ud;continue;}}}},_uf=function(_ug,_uh){var _ui=E(_uh);if(!_ui._){return __Z;}else{var _uj=_ui.a,_uk=E(_ug);return (_uk==1)?new T2(1,_uj,_Z):new T2(1,_uj,new T(function(){return B(_uf(_uk-1|0,_ui.b));}));}},_ul=function(_um,_un,_uo,_up){while(1){if(B(_aS(new T2(1,_uo,_up),_un))!=_um){var _uq=_un+1|0;_un=_uq;continue;}else{if(0>=_un){return __Z;}else{return new F(function(){return _uf(_un,new T2(1,_uo,_up));});}}}},_ur=function(_us,_ut,_uu){var _uv=E(_uu);if(!_uv._){return __Z;}else{var _uw=E(_us);if(B(_aS(_uv,_ut))!=_uw){return new F(function(){return _ul(_uw,_ut+1|0,_uv.a,_uv.b);});}else{if(0>=_ut){return __Z;}else{return new F(function(){return _uf(_ut,_uv);});}}}},_ux=function(_uy,_uz,_uA){var _uB=_uz+1|0;if(_uB>0){return new F(function(){return _u9(_uB,B(_ur(_uy,_uB,_uA)));});}else{return new F(function(){return _ur(_uy,_uB,_uA);});}},_uC=function(_uD,_uE){return (!B(_ae(_uD,_uE)))?true:false;},_uF=new T2(0,_ae,_uC),_uG=0,_uH=new T(function(){return B(_i8("Event.hs:(81,1)-(82,68)|function addEvent"));}),_uI=function(_uJ,_uK,_uL,_uM,_uN,_uO,_uP,_uQ,_uR,_uS,_uT,_uU,_uV,_uW,_uX,_uY,_uZ,_v0,_v1,_v2,_v3,_v4,_v5,_v6){while(1){var _v7=E(_uJ);if(!_v7._){return {_:0,a:_uK,b:_uL,c:_uM,d:_uN,e:_uO,f:_uP,g:_uQ,h:_uR,i:_uS,j:_uT,k:_uU,l:_uV,m:_uW,n:_uX,o:_uY,p:_uZ,q:_v0,r:_v1,s:_v2,t:_v3,u:_v4,v:_v5,w:_v6};}else{var _v8=E(_v7.b);if(!_v8._){return E(_uH);}else{var _v9=new T2(1,new T2(0,_v7.a,_v8.a),_uO),_va=new T2(1,_uG,_uP);_uJ=_v8.b;_uO=_v9;_uP=_va;continue;}}}},_vb=function(_vc,_vd,_ve){var _vf=E(_ve);if(!_vf._){return __Z;}else{var _vg=_vf.a,_vh=_vf.b;return (!B(A2(_vc,_vd,_vg)))?new T2(1,_vg,new T(function(){return B(_vb(_vc,_vd,_vh));})):E(_vh);}},_vi=function(_vj,_vk){while(1){var _vl=E(_vj);if(!_vl._){return (E(_vk)._==0)?true:false;}else{var _vm=E(_vk);if(!_vm._){return false;}else{if(E(_vl.a)!=E(_vm.a)){return false;}else{_vj=_vl.b;_vk=_vm.b;continue;}}}}},_vn=function(_vo,_vp){while(1){var _vq=E(_vo);if(!_vq._){return (E(_vp)._==0)?true:false;}else{var _vr=E(_vp);if(!_vr._){return false;}else{if(!B(_ae(_vq.a,_vr.a))){return false;}else{_vo=_vq.b;_vp=_vr.b;continue;}}}}},_vs=function(_vt,_vu,_vv){return new F(function(){return A1(_vt,new T2(1,_2z,new T(function(){return B(A1(_vu,_vv));})));});},_vw=function(_vx,_vy){switch(E(_vx)){case 0:return (E(_vy)==0)?true:false;case 1:return (E(_vy)==1)?true:false;case 2:return (E(_vy)==2)?true:false;case 3:return (E(_vy)==3)?true:false;case 4:return (E(_vy)==4)?true:false;case 5:return (E(_vy)==5)?true:false;case 6:return (E(_vy)==6)?true:false;case 7:return (E(_vy)==7)?true:false;default:return (E(_vy)==8)?true:false;}},_vz=function(_vA,_vB,_vC,_vD){if(_vA!=_vC){return false;}else{return new F(function(){return _vw(_vB,_vD);});}},_vE=function(_vF,_vG){var _vH=E(_vF),_vI=E(_vG);return new F(function(){return _vz(E(_vH.a),_vH.b,E(_vI.a),_vI.b);});},_vJ=function(_vK,_vL,_vM,_vN){if(_vK!=_vM){return true;}else{switch(E(_vL)){case 0:return (E(_vN)==0)?false:true;case 1:return (E(_vN)==1)?false:true;case 2:return (E(_vN)==2)?false:true;case 3:return (E(_vN)==3)?false:true;case 4:return (E(_vN)==4)?false:true;case 5:return (E(_vN)==5)?false:true;case 6:return (E(_vN)==6)?false:true;case 7:return (E(_vN)==7)?false:true;default:return (E(_vN)==8)?false:true;}}},_vO=function(_vP,_vQ){var _vR=E(_vP),_vS=E(_vQ);return new F(function(){return _vJ(E(_vR.a),_vR.b,E(_vS.a),_vS.b);});},_vT=new T2(0,_vE,_vO),_vU=0,_vV=function(_vW,_vX){var _vY=E(_vX);if(!_vY._){return 0;}else{var _vZ=_vY.b,_w0=E(_vW),_w1=E(_vY.a),_w2=_w1.b;if(E(_w0.a)!=E(_w1.a)){return 1+B(_vV(_w0,_vZ))|0;}else{switch(E(_w0.b)){case 0:return (E(_w2)==0)?0:1+B(_vV(_w0,_vZ))|0;case 1:return (E(_w2)==1)?0:1+B(_vV(_w0,_vZ))|0;case 2:return (E(_w2)==2)?0:1+B(_vV(_w0,_vZ))|0;case 3:return (E(_w2)==3)?0:1+B(_vV(_w0,_vZ))|0;case 4:return (E(_w2)==4)?0:1+B(_vV(_w0,_vZ))|0;case 5:return (E(_w2)==5)?0:1+B(_vV(_w0,_vZ))|0;case 6:return (E(_w2)==6)?0:1+B(_vV(_w0,_vZ))|0;case 7:return (E(_w2)==7)?0:1+B(_vV(_w0,_vZ))|0;default:return (E(_w2)==8)?0:1+B(_vV(_w0,_vZ))|0;}}}},_w3=function(_w4,_w5){return new F(function(){return _vV(_w4,_w5);});},_w6=function(_w7,_w8){var _w9=E(_w8);if(!_w9._){return new T2(0,_vU,_vU);}else{var _wa=_w9.a,_wb=_w9.b;return (!B(_4H(_vT,_w7,_wa)))?new T2(0,new T(function(){return E(B(_w6(_w7,_wb)).a);}),new T(function(){return 1+E(B(_w6(_w7,_wb)).b)|0;})):new T2(0,new T(function(){return B(_w3(_w7,_wa));}),_vU);}},_wc=function(_wd,_we){while(1){var _wf=E(_we);if(!_wf._){return __Z;}else{var _wg=_wf.b,_wh=E(_wd);if(_wh==1){return E(_wg);}else{_wd=_wh-1|0;_we=_wg;continue;}}}},_wi=new T(function(){return B(unCStr("getch"));}),_wj=new T(function(){return B(unCStr("=="));}),_wk=new T(function(){return B(unCStr("&&"));}),_wl=new T(function(){return B(unCStr("||"));}),_wm=new T(function(){return B(unCStr("getpos"));}),_wn=new T(function(){return B(unCStr("ch"));}),_wo=new T(function(){return B(unCStr("tp"));}),_wp=new T2(1,_wo,_Z),_wq=new T2(1,_wn,_wp),_wr=new T2(0,_wm,_wq),_ws=new T(function(){return B(unCStr("a"));}),_wt=new T(function(){return B(unCStr("b"));}),_wu=new T2(1,_wt,_Z),_wv=new T2(1,_ws,_wu),_ww=new T2(0,_wj,_wv),_wx=new T2(0,_wk,_wv),_wy=new T2(0,_wl,_wv),_wz=new T2(1,_wy,_Z),_wA=new T2(1,_wx,_wz),_wB=new T2(1,_ww,_wA),_wC=new T2(1,_wr,_wB),_wD=new T(function(){return B(unCStr("p"));}),_wE=new T(function(){return B(unCStr("q"));}),_wF=new T2(1,_wE,_Z),_wG=new T2(1,_wD,_wF),_wH=new T2(0,_wi,_wG),_wI=new T2(1,_wH,_wC),_wJ=new T(function(){return B(unCStr("foldr1"));}),_wK=new T(function(){return B(_rf(_wJ));}),_wL=function(_wM,_wN){var _wO=E(_wN);if(!_wO._){return E(_wK);}else{var _wP=_wO.a,_wQ=E(_wO.b);if(!_wQ._){return E(_wP);}else{return new F(function(){return A2(_wM,_wP,new T(function(){return B(_wL(_wM,_wQ));}));});}}},_wR=function(_wS){return E(E(_wS).a);},_wT=function(_wU,_wV,_wW){while(1){var _wX=E(_wW);if(!_wX._){return __Z;}else{var _wY=E(_wX.a);if(!B(A3(_4F,_wU,_wV,_wY.a))){_wW=_wX.b;continue;}else{return new T1(1,_wY.b);}}}},_wZ=new T(function(){return B(unCStr("Prelude.read: no parse"));}),_x0=new T(function(){return B(err(_wZ));}),_x1=new T(function(){return B(unCStr("T"));}),_x2=new T(function(){return B(unCStr("F"));}),_x3=new T(function(){return B(unCStr("Prelude.read: ambiguous parse"));}),_x4=new T(function(){return B(err(_x3));}),_x5=new T(function(){return B(unCStr("empty"));}),_x6=new T2(1,_x5,_Z),_x7=new T(function(){return B(_i8("Text/ParserCombinators/ReadP.hs:(128,3)-(151,52)|function <|>"));}),_x8=function(_x9,_xa){while(1){var _xb=B((function(_xc,_xd){var _xe=E(_xc);switch(_xe._){case 0:var _xf=E(_xd);if(!_xf._){return __Z;}else{_x9=B(A1(_xe.a,_xf.a));_xa=_xf.b;return __continue;}break;case 1:var _xg=B(A1(_xe.a,_xd)),_xh=_xd;_x9=_xg;_xa=_xh;return __continue;case 2:return __Z;case 3:return new T2(1,new T2(0,_xe.a,_xd),new T(function(){return B(_x8(_xe.b,_xd));}));default:return E(_xe.a);}})(_x9,_xa));if(_xb!=__continue){return _xb;}}},_xi=function(_xj,_xk){var _xl=function(_xm){var _xn=E(_xk);if(_xn._==3){return new T2(3,_xn.a,new T(function(){return B(_xi(_xj,_xn.b));}));}else{var _xo=E(_xj);if(_xo._==2){return E(_xn);}else{var _xp=E(_xn);if(_xp._==2){return E(_xo);}else{var _xq=function(_xr){var _xs=E(_xp);if(_xs._==4){var _xt=function(_xu){return new T1(4,new T(function(){return B(_x(B(_x8(_xo,_xu)),_xs.a));}));};return new T1(1,_xt);}else{var _xv=E(_xo);if(_xv._==1){var _xw=_xv.a,_xx=E(_xs);if(!_xx._){return new T1(1,function(_xy){return new F(function(){return _xi(B(A1(_xw,_xy)),_xx);});});}else{var _xz=function(_xA){return new F(function(){return _xi(B(A1(_xw,_xA)),new T(function(){return B(A1(_xx.a,_xA));}));});};return new T1(1,_xz);}}else{var _xB=E(_xs);if(!_xB._){return E(_x7);}else{var _xC=function(_xD){return new F(function(){return _xi(_xv,new T(function(){return B(A1(_xB.a,_xD));}));});};return new T1(1,_xC);}}}},_xE=E(_xo);switch(_xE._){case 1:var _xF=E(_xp);if(_xF._==4){var _xG=function(_xH){return new T1(4,new T(function(){return B(_x(B(_x8(B(A1(_xE.a,_xH)),_xH)),_xF.a));}));};return new T1(1,_xG);}else{return new F(function(){return _xq(_);});}break;case 4:var _xI=_xE.a,_xJ=E(_xp);switch(_xJ._){case 0:var _xK=function(_xL){var _xM=new T(function(){return B(_x(_xI,new T(function(){return B(_x8(_xJ,_xL));},1)));});return new T1(4,_xM);};return new T1(1,_xK);case 1:var _xN=function(_xO){var _xP=new T(function(){return B(_x(_xI,new T(function(){return B(_x8(B(A1(_xJ.a,_xO)),_xO));},1)));});return new T1(4,_xP);};return new T1(1,_xN);default:return new T1(4,new T(function(){return B(_x(_xI,_xJ.a));}));}break;default:return new F(function(){return _xq(_);});}}}}},_xQ=E(_xj);switch(_xQ._){case 0:var _xR=E(_xk);if(!_xR._){var _xS=function(_xT){return new F(function(){return _xi(B(A1(_xQ.a,_xT)),new T(function(){return B(A1(_xR.a,_xT));}));});};return new T1(0,_xS);}else{return new F(function(){return _xl(_);});}break;case 3:return new T2(3,_xQ.a,new T(function(){return B(_xi(_xQ.b,_xk));}));default:return new F(function(){return _xl(_);});}},_xU=new T(function(){return B(unCStr("("));}),_xV=new T(function(){return B(unCStr(")"));}),_xW=function(_xX,_xY){var _xZ=E(_xX);switch(_xZ._){case 0:return new T1(0,function(_y0){return new F(function(){return _xW(B(A1(_xZ.a,_y0)),_xY);});});case 1:return new T1(1,function(_y1){return new F(function(){return _xW(B(A1(_xZ.a,_y1)),_xY);});});case 2:return new T0(2);case 3:return new F(function(){return _xi(B(A1(_xY,_xZ.a)),new T(function(){return B(_xW(_xZ.b,_xY));}));});break;default:var _y2=function(_y3){var _y4=E(_y3);if(!_y4._){return __Z;}else{var _y5=E(_y4.a);return new F(function(){return _x(B(_x8(B(A1(_xY,_y5.a)),_y5.b)),new T(function(){return B(_y2(_y4.b));},1));});}},_y6=B(_y2(_xZ.a));return (_y6._==0)?new T0(2):new T1(4,_y6);}},_y7=new T0(2),_y8=function(_y9){return new T2(3,_y9,_y7);},_ya=function(_yb,_yc){var _yd=E(_yb);if(!_yd){return new F(function(){return A1(_yc,_kF);});}else{var _ye=new T(function(){return B(_ya(_yd-1|0,_yc));});return new T1(0,function(_yf){return E(_ye);});}},_yg=function(_yh,_yi,_yj){var _yk=new T(function(){return B(A1(_yh,_y8));}),_yl=function(_ym,_yn,_yo,_yp){while(1){var _yq=B((function(_yr,_ys,_yt,_yu){var _yv=E(_yr);switch(_yv._){case 0:var _yw=E(_ys);if(!_yw._){return new F(function(){return A1(_yi,_yu);});}else{var _yx=_yt+1|0,_yy=_yu;_ym=B(A1(_yv.a,_yw.a));_yn=_yw.b;_yo=_yx;_yp=_yy;return __continue;}break;case 1:var _yz=B(A1(_yv.a,_ys)),_yA=_ys,_yx=_yt,_yy=_yu;_ym=_yz;_yn=_yA;_yo=_yx;_yp=_yy;return __continue;case 2:return new F(function(){return A1(_yi,_yu);});break;case 3:var _yB=new T(function(){return B(_xW(_yv,_yu));});return new F(function(){return _ya(_yt,function(_yC){return E(_yB);});});break;default:return new F(function(){return _xW(_yv,_yu);});}})(_ym,_yn,_yo,_yp));if(_yq!=__continue){return _yq;}}};return function(_yD){return new F(function(){return _yl(_yk,_yD,0,_yj);});};},_yE=function(_yF){return new F(function(){return A1(_yF,_Z);});},_yG=function(_yH,_yI){var _yJ=function(_yK){var _yL=E(_yK);if(!_yL._){return E(_yE);}else{var _yM=_yL.a;if(!B(A1(_yH,_yM))){return E(_yE);}else{var _yN=new T(function(){return B(_yJ(_yL.b));}),_yO=function(_yP){var _yQ=new T(function(){return B(A1(_yN,function(_yR){return new F(function(){return A1(_yP,new T2(1,_yM,_yR));});}));});return new T1(0,function(_yS){return E(_yQ);});};return E(_yO);}}};return function(_yT){return new F(function(){return A2(_yJ,_yT,_yI);});};},_yU=new T0(6),_yV=new T(function(){return B(unCStr("valDig: Bad base"));}),_yW=new T(function(){return B(err(_yV));}),_yX=function(_yY,_yZ){var _z0=function(_z1,_z2){var _z3=E(_z1);if(!_z3._){var _z4=new T(function(){return B(A1(_z2,_Z));});return function(_z5){return new F(function(){return A1(_z5,_z4);});};}else{var _z6=E(_z3.a),_z7=function(_z8){var _z9=new T(function(){return B(_z0(_z3.b,function(_za){return new F(function(){return A1(_z2,new T2(1,_z8,_za));});}));}),_zb=function(_zc){var _zd=new T(function(){return B(A1(_z9,_zc));});return new T1(0,function(_ze){return E(_zd);});};return E(_zb);};switch(E(_yY)){case 8:if(48>_z6){var _zf=new T(function(){return B(A1(_z2,_Z));});return function(_zg){return new F(function(){return A1(_zg,_zf);});};}else{if(_z6>55){var _zh=new T(function(){return B(A1(_z2,_Z));});return function(_zi){return new F(function(){return A1(_zi,_zh);});};}else{return new F(function(){return _z7(_z6-48|0);});}}break;case 10:if(48>_z6){var _zj=new T(function(){return B(A1(_z2,_Z));});return function(_zk){return new F(function(){return A1(_zk,_zj);});};}else{if(_z6>57){var _zl=new T(function(){return B(A1(_z2,_Z));});return function(_zm){return new F(function(){return A1(_zm,_zl);});};}else{return new F(function(){return _z7(_z6-48|0);});}}break;case 16:if(48>_z6){if(97>_z6){if(65>_z6){var _zn=new T(function(){return B(A1(_z2,_Z));});return function(_zo){return new F(function(){return A1(_zo,_zn);});};}else{if(_z6>70){var _zp=new T(function(){return B(A1(_z2,_Z));});return function(_zq){return new F(function(){return A1(_zq,_zp);});};}else{return new F(function(){return _z7((_z6-65|0)+10|0);});}}}else{if(_z6>102){if(65>_z6){var _zr=new T(function(){return B(A1(_z2,_Z));});return function(_zs){return new F(function(){return A1(_zs,_zr);});};}else{if(_z6>70){var _zt=new T(function(){return B(A1(_z2,_Z));});return function(_zu){return new F(function(){return A1(_zu,_zt);});};}else{return new F(function(){return _z7((_z6-65|0)+10|0);});}}}else{return new F(function(){return _z7((_z6-97|0)+10|0);});}}}else{if(_z6>57){if(97>_z6){if(65>_z6){var _zv=new T(function(){return B(A1(_z2,_Z));});return function(_zw){return new F(function(){return A1(_zw,_zv);});};}else{if(_z6>70){var _zx=new T(function(){return B(A1(_z2,_Z));});return function(_zy){return new F(function(){return A1(_zy,_zx);});};}else{return new F(function(){return _z7((_z6-65|0)+10|0);});}}}else{if(_z6>102){if(65>_z6){var _zz=new T(function(){return B(A1(_z2,_Z));});return function(_zA){return new F(function(){return A1(_zA,_zz);});};}else{if(_z6>70){var _zB=new T(function(){return B(A1(_z2,_Z));});return function(_zC){return new F(function(){return A1(_zC,_zB);});};}else{return new F(function(){return _z7((_z6-65|0)+10|0);});}}}else{return new F(function(){return _z7((_z6-97|0)+10|0);});}}}else{return new F(function(){return _z7(_z6-48|0);});}}break;default:return E(_yW);}}},_zD=function(_zE){var _zF=E(_zE);if(!_zF._){return new T0(2);}else{return new F(function(){return A1(_yZ,_zF);});}};return function(_zG){return new F(function(){return A3(_z0,_zG,_61,_zD);});};},_zH=16,_zI=8,_zJ=function(_zK){var _zL=function(_zM){return new F(function(){return A1(_zK,new T1(5,new T2(0,_zI,_zM)));});},_zN=function(_zO){return new F(function(){return A1(_zK,new T1(5,new T2(0,_zH,_zO)));});},_zP=function(_zQ){switch(E(_zQ)){case 79:return new T1(1,B(_yX(_zI,_zL)));case 88:return new T1(1,B(_yX(_zH,_zN)));case 111:return new T1(1,B(_yX(_zI,_zL)));case 120:return new T1(1,B(_yX(_zH,_zN)));default:return new T0(2);}};return function(_zR){return (E(_zR)==48)?E(new T1(0,_zP)):new T0(2);};},_zS=function(_zT){return new T1(0,B(_zJ(_zT)));},_zU=function(_zV){return new F(function(){return A1(_zV,_2U);});},_zW=function(_zX){return new F(function(){return A1(_zX,_2U);});},_zY=10,_zZ=new T1(0,10),_A0=function(_A1){return new F(function(){return _eS(E(_A1));});},_A2=new T(function(){return B(unCStr("this should not happen"));}),_A3=new T(function(){return B(err(_A2));}),_A4=function(_A5,_A6){var _A7=E(_A6);if(!_A7._){return __Z;}else{var _A8=E(_A7.b);return (_A8._==0)?E(_A3):new T2(1,B(_gw(B(_sG(_A7.a,_A5)),_A8.a)),new T(function(){return B(_A4(_A5,_A8.b));}));}},_A9=new T1(0,0),_Aa=function(_Ab,_Ac,_Ad){while(1){var _Ae=B((function(_Af,_Ag,_Ah){var _Ai=E(_Ah);if(!_Ai._){return E(_A9);}else{if(!E(_Ai.b)._){return E(_Ai.a);}else{var _Aj=E(_Ag);if(_Aj<=40){var _Ak=function(_Al,_Am){while(1){var _An=E(_Am);if(!_An._){return E(_Al);}else{var _Ao=B(_gw(B(_sG(_Al,_Af)),_An.a));_Al=_Ao;_Am=_An.b;continue;}}};return new F(function(){return _Ak(_A9,_Ai);});}else{var _Ap=B(_sG(_Af,_Af));if(!(_Aj%2)){var _Aq=B(_A4(_Af,_Ai));_Ab=_Ap;_Ac=quot(_Aj+1|0,2);_Ad=_Aq;return __continue;}else{var _Aq=B(_A4(_Af,new T2(1,_A9,_Ai)));_Ab=_Ap;_Ac=quot(_Aj+1|0,2);_Ad=_Aq;return __continue;}}}}})(_Ab,_Ac,_Ad));if(_Ae!=__continue){return _Ae;}}},_Ar=function(_As,_At){return new F(function(){return _Aa(_As,new T(function(){return B(_qu(_At,0));},1),B(_aj(_A0,_At)));});},_Au=function(_Av){var _Aw=new T(function(){var _Ax=new T(function(){var _Ay=function(_Az){return new F(function(){return A1(_Av,new T1(1,new T(function(){return B(_Ar(_zZ,_Az));})));});};return new T1(1,B(_yX(_zY,_Ay)));}),_AA=function(_AB){if(E(_AB)==43){var _AC=function(_AD){return new F(function(){return A1(_Av,new T1(1,new T(function(){return B(_Ar(_zZ,_AD));})));});};return new T1(1,B(_yX(_zY,_AC)));}else{return new T0(2);}},_AE=function(_AF){if(E(_AF)==45){var _AG=function(_AH){return new F(function(){return A1(_Av,new T1(1,new T(function(){return B(_ju(B(_Ar(_zZ,_AH))));})));});};return new T1(1,B(_yX(_zY,_AG)));}else{return new T0(2);}};return B(_xi(B(_xi(new T1(0,_AE),new T1(0,_AA))),_Ax));});return new F(function(){return _xi(new T1(0,function(_AI){return (E(_AI)==101)?E(_Aw):new T0(2);}),new T1(0,function(_AJ){return (E(_AJ)==69)?E(_Aw):new T0(2);}));});},_AK=function(_AL){var _AM=function(_AN){return new F(function(){return A1(_AL,new T1(1,_AN));});};return function(_AO){return (E(_AO)==46)?new T1(1,B(_yX(_zY,_AM))):new T0(2);};},_AP=function(_AQ){return new T1(0,B(_AK(_AQ)));},_AR=function(_AS){var _AT=function(_AU){var _AV=function(_AW){return new T1(1,B(_yg(_Au,_zU,function(_AX){return new F(function(){return A1(_AS,new T1(5,new T3(1,_AU,_AW,_AX)));});})));};return new T1(1,B(_yg(_AP,_zW,_AV)));};return new F(function(){return _yX(_zY,_AT);});},_AY=function(_AZ){return new T1(1,B(_AR(_AZ)));},_B0=new T(function(){return B(unCStr("!@#$%&*+./<=>?\\^|:-~"));}),_B1=function(_B2){return new F(function(){return _4H(_l8,_B2,_B0);});},_B3=false,_B4=true,_B5=function(_B6){var _B7=new T(function(){return B(A1(_B6,_zI));}),_B8=new T(function(){return B(A1(_B6,_zH));});return function(_B9){switch(E(_B9)){case 79:return E(_B7);case 88:return E(_B8);case 111:return E(_B7);case 120:return E(_B8);default:return new T0(2);}};},_Ba=function(_Bb){return new T1(0,B(_B5(_Bb)));},_Bc=function(_Bd){return new F(function(){return A1(_Bd,_zY);});},_Be=function(_Bf){return new F(function(){return err(B(unAppCStr("Prelude.chr: bad argument: ",new T(function(){return B(_H(9,_Bf,_Z));}))));});},_Bg=function(_Bh){return new T0(2);},_Bi=function(_Bj){var _Bk=E(_Bj);if(!_Bk._){return E(_Bg);}else{var _Bl=_Bk.a,_Bm=E(_Bk.b);if(!_Bm._){return E(_Bl);}else{var _Bn=new T(function(){return B(_Bi(_Bm));}),_Bo=function(_Bp){return new F(function(){return _xi(B(A1(_Bl,_Bp)),new T(function(){return B(A1(_Bn,_Bp));}));});};return E(_Bo);}}},_Bq=function(_Br,_Bs){var _Bt=function(_Bu,_Bv,_Bw){var _Bx=E(_Bu);if(!_Bx._){return new F(function(){return A1(_Bw,_Br);});}else{var _By=E(_Bv);if(!_By._){return new T0(2);}else{if(E(_Bx.a)!=E(_By.a)){return new T0(2);}else{var _Bz=new T(function(){return B(_Bt(_Bx.b,_By.b,_Bw));});return new T1(0,function(_BA){return E(_Bz);});}}}};return function(_BB){return new F(function(){return _Bt(_Br,_BB,_Bs);});};},_BC=new T(function(){return B(unCStr("SO"));}),_BD=14,_BE=function(_BF){var _BG=new T(function(){return B(A1(_BF,_BD));});return new T1(1,B(_Bq(_BC,function(_BH){return E(_BG);})));},_BI=new T(function(){return B(unCStr("SOH"));}),_BJ=1,_BK=function(_BL){var _BM=new T(function(){return B(A1(_BL,_BJ));});return new T1(1,B(_Bq(_BI,function(_BN){return E(_BM);})));},_BO=function(_BP){return new T1(1,B(_yg(_BK,_BE,_BP)));},_BQ=new T(function(){return B(unCStr("NUL"));}),_BR=0,_BS=function(_BT){var _BU=new T(function(){return B(A1(_BT,_BR));});return new T1(1,B(_Bq(_BQ,function(_BV){return E(_BU);})));},_BW=new T(function(){return B(unCStr("STX"));}),_BX=2,_BY=function(_BZ){var _C0=new T(function(){return B(A1(_BZ,_BX));});return new T1(1,B(_Bq(_BW,function(_C1){return E(_C0);})));},_C2=new T(function(){return B(unCStr("ETX"));}),_C3=3,_C4=function(_C5){var _C6=new T(function(){return B(A1(_C5,_C3));});return new T1(1,B(_Bq(_C2,function(_C7){return E(_C6);})));},_C8=new T(function(){return B(unCStr("EOT"));}),_C9=4,_Ca=function(_Cb){var _Cc=new T(function(){return B(A1(_Cb,_C9));});return new T1(1,B(_Bq(_C8,function(_Cd){return E(_Cc);})));},_Ce=new T(function(){return B(unCStr("ENQ"));}),_Cf=5,_Cg=function(_Ch){var _Ci=new T(function(){return B(A1(_Ch,_Cf));});return new T1(1,B(_Bq(_Ce,function(_Cj){return E(_Ci);})));},_Ck=new T(function(){return B(unCStr("ACK"));}),_Cl=6,_Cm=function(_Cn){var _Co=new T(function(){return B(A1(_Cn,_Cl));});return new T1(1,B(_Bq(_Ck,function(_Cp){return E(_Co);})));},_Cq=new T(function(){return B(unCStr("BEL"));}),_Cr=7,_Cs=function(_Ct){var _Cu=new T(function(){return B(A1(_Ct,_Cr));});return new T1(1,B(_Bq(_Cq,function(_Cv){return E(_Cu);})));},_Cw=new T(function(){return B(unCStr("BS"));}),_Cx=8,_Cy=function(_Cz){var _CA=new T(function(){return B(A1(_Cz,_Cx));});return new T1(1,B(_Bq(_Cw,function(_CB){return E(_CA);})));},_CC=new T(function(){return B(unCStr("HT"));}),_CD=9,_CE=function(_CF){var _CG=new T(function(){return B(A1(_CF,_CD));});return new T1(1,B(_Bq(_CC,function(_CH){return E(_CG);})));},_CI=new T(function(){return B(unCStr("LF"));}),_CJ=10,_CK=function(_CL){var _CM=new T(function(){return B(A1(_CL,_CJ));});return new T1(1,B(_Bq(_CI,function(_CN){return E(_CM);})));},_CO=new T(function(){return B(unCStr("VT"));}),_CP=11,_CQ=function(_CR){var _CS=new T(function(){return B(A1(_CR,_CP));});return new T1(1,B(_Bq(_CO,function(_CT){return E(_CS);})));},_CU=new T(function(){return B(unCStr("FF"));}),_CV=12,_CW=function(_CX){var _CY=new T(function(){return B(A1(_CX,_CV));});return new T1(1,B(_Bq(_CU,function(_CZ){return E(_CY);})));},_D0=new T(function(){return B(unCStr("CR"));}),_D1=13,_D2=function(_D3){var _D4=new T(function(){return B(A1(_D3,_D1));});return new T1(1,B(_Bq(_D0,function(_D5){return E(_D4);})));},_D6=new T(function(){return B(unCStr("SI"));}),_D7=15,_D8=function(_D9){var _Da=new T(function(){return B(A1(_D9,_D7));});return new T1(1,B(_Bq(_D6,function(_Db){return E(_Da);})));},_Dc=new T(function(){return B(unCStr("DLE"));}),_Dd=16,_De=function(_Df){var _Dg=new T(function(){return B(A1(_Df,_Dd));});return new T1(1,B(_Bq(_Dc,function(_Dh){return E(_Dg);})));},_Di=new T(function(){return B(unCStr("DC1"));}),_Dj=17,_Dk=function(_Dl){var _Dm=new T(function(){return B(A1(_Dl,_Dj));});return new T1(1,B(_Bq(_Di,function(_Dn){return E(_Dm);})));},_Do=new T(function(){return B(unCStr("DC2"));}),_Dp=18,_Dq=function(_Dr){var _Ds=new T(function(){return B(A1(_Dr,_Dp));});return new T1(1,B(_Bq(_Do,function(_Dt){return E(_Ds);})));},_Du=new T(function(){return B(unCStr("DC3"));}),_Dv=19,_Dw=function(_Dx){var _Dy=new T(function(){return B(A1(_Dx,_Dv));});return new T1(1,B(_Bq(_Du,function(_Dz){return E(_Dy);})));},_DA=new T(function(){return B(unCStr("DC4"));}),_DB=20,_DC=function(_DD){var _DE=new T(function(){return B(A1(_DD,_DB));});return new T1(1,B(_Bq(_DA,function(_DF){return E(_DE);})));},_DG=new T(function(){return B(unCStr("NAK"));}),_DH=21,_DI=function(_DJ){var _DK=new T(function(){return B(A1(_DJ,_DH));});return new T1(1,B(_Bq(_DG,function(_DL){return E(_DK);})));},_DM=new T(function(){return B(unCStr("SYN"));}),_DN=22,_DO=function(_DP){var _DQ=new T(function(){return B(A1(_DP,_DN));});return new T1(1,B(_Bq(_DM,function(_DR){return E(_DQ);})));},_DS=new T(function(){return B(unCStr("ETB"));}),_DT=23,_DU=function(_DV){var _DW=new T(function(){return B(A1(_DV,_DT));});return new T1(1,B(_Bq(_DS,function(_DX){return E(_DW);})));},_DY=new T(function(){return B(unCStr("CAN"));}),_DZ=24,_E0=function(_E1){var _E2=new T(function(){return B(A1(_E1,_DZ));});return new T1(1,B(_Bq(_DY,function(_E3){return E(_E2);})));},_E4=new T(function(){return B(unCStr("EM"));}),_E5=25,_E6=function(_E7){var _E8=new T(function(){return B(A1(_E7,_E5));});return new T1(1,B(_Bq(_E4,function(_E9){return E(_E8);})));},_Ea=new T(function(){return B(unCStr("SUB"));}),_Eb=26,_Ec=function(_Ed){var _Ee=new T(function(){return B(A1(_Ed,_Eb));});return new T1(1,B(_Bq(_Ea,function(_Ef){return E(_Ee);})));},_Eg=new T(function(){return B(unCStr("ESC"));}),_Eh=27,_Ei=function(_Ej){var _Ek=new T(function(){return B(A1(_Ej,_Eh));});return new T1(1,B(_Bq(_Eg,function(_El){return E(_Ek);})));},_Em=new T(function(){return B(unCStr("FS"));}),_En=28,_Eo=function(_Ep){var _Eq=new T(function(){return B(A1(_Ep,_En));});return new T1(1,B(_Bq(_Em,function(_Er){return E(_Eq);})));},_Es=new T(function(){return B(unCStr("GS"));}),_Et=29,_Eu=function(_Ev){var _Ew=new T(function(){return B(A1(_Ev,_Et));});return new T1(1,B(_Bq(_Es,function(_Ex){return E(_Ew);})));},_Ey=new T(function(){return B(unCStr("RS"));}),_Ez=30,_EA=function(_EB){var _EC=new T(function(){return B(A1(_EB,_Ez));});return new T1(1,B(_Bq(_Ey,function(_ED){return E(_EC);})));},_EE=new T(function(){return B(unCStr("US"));}),_EF=31,_EG=function(_EH){var _EI=new T(function(){return B(A1(_EH,_EF));});return new T1(1,B(_Bq(_EE,function(_EJ){return E(_EI);})));},_EK=new T(function(){return B(unCStr("SP"));}),_EL=32,_EM=function(_EN){var _EO=new T(function(){return B(A1(_EN,_EL));});return new T1(1,B(_Bq(_EK,function(_EP){return E(_EO);})));},_EQ=new T(function(){return B(unCStr("DEL"));}),_ER=127,_ES=function(_ET){var _EU=new T(function(){return B(A1(_ET,_ER));});return new T1(1,B(_Bq(_EQ,function(_EV){return E(_EU);})));},_EW=new T2(1,_ES,_Z),_EX=new T2(1,_EM,_EW),_EY=new T2(1,_EG,_EX),_EZ=new T2(1,_EA,_EY),_F0=new T2(1,_Eu,_EZ),_F1=new T2(1,_Eo,_F0),_F2=new T2(1,_Ei,_F1),_F3=new T2(1,_Ec,_F2),_F4=new T2(1,_E6,_F3),_F5=new T2(1,_E0,_F4),_F6=new T2(1,_DU,_F5),_F7=new T2(1,_DO,_F6),_F8=new T2(1,_DI,_F7),_F9=new T2(1,_DC,_F8),_Fa=new T2(1,_Dw,_F9),_Fb=new T2(1,_Dq,_Fa),_Fc=new T2(1,_Dk,_Fb),_Fd=new T2(1,_De,_Fc),_Fe=new T2(1,_D8,_Fd),_Ff=new T2(1,_D2,_Fe),_Fg=new T2(1,_CW,_Ff),_Fh=new T2(1,_CQ,_Fg),_Fi=new T2(1,_CK,_Fh),_Fj=new T2(1,_CE,_Fi),_Fk=new T2(1,_Cy,_Fj),_Fl=new T2(1,_Cs,_Fk),_Fm=new T2(1,_Cm,_Fl),_Fn=new T2(1,_Cg,_Fm),_Fo=new T2(1,_Ca,_Fn),_Fp=new T2(1,_C4,_Fo),_Fq=new T2(1,_BY,_Fp),_Fr=new T2(1,_BS,_Fq),_Fs=new T2(1,_BO,_Fr),_Ft=new T(function(){return B(_Bi(_Fs));}),_Fu=34,_Fv=new T1(0,1114111),_Fw=92,_Fx=39,_Fy=function(_Fz){var _FA=new T(function(){return B(A1(_Fz,_Cr));}),_FB=new T(function(){return B(A1(_Fz,_Cx));}),_FC=new T(function(){return B(A1(_Fz,_CD));}),_FD=new T(function(){return B(A1(_Fz,_CJ));}),_FE=new T(function(){return B(A1(_Fz,_CP));}),_FF=new T(function(){return B(A1(_Fz,_CV));}),_FG=new T(function(){return B(A1(_Fz,_D1));}),_FH=new T(function(){return B(A1(_Fz,_Fw));}),_FI=new T(function(){return B(A1(_Fz,_Fx));}),_FJ=new T(function(){return B(A1(_Fz,_Fu));}),_FK=new T(function(){var _FL=function(_FM){var _FN=new T(function(){return B(_eS(E(_FM)));}),_FO=function(_FP){var _FQ=B(_Ar(_FN,_FP));if(!B(_iA(_FQ,_Fv))){return new T0(2);}else{return new F(function(){return A1(_Fz,new T(function(){var _FR=B(_fb(_FQ));if(_FR>>>0>1114111){return B(_Be(_FR));}else{return _FR;}}));});}};return new T1(1,B(_yX(_FM,_FO)));},_FS=new T(function(){var _FT=new T(function(){return B(A1(_Fz,_EF));}),_FU=new T(function(){return B(A1(_Fz,_Ez));}),_FV=new T(function(){return B(A1(_Fz,_Et));}),_FW=new T(function(){return B(A1(_Fz,_En));}),_FX=new T(function(){return B(A1(_Fz,_Eh));}),_FY=new T(function(){return B(A1(_Fz,_Eb));}),_FZ=new T(function(){return B(A1(_Fz,_E5));}),_G0=new T(function(){return B(A1(_Fz,_DZ));}),_G1=new T(function(){return B(A1(_Fz,_DT));}),_G2=new T(function(){return B(A1(_Fz,_DN));}),_G3=new T(function(){return B(A1(_Fz,_DH));}),_G4=new T(function(){return B(A1(_Fz,_DB));}),_G5=new T(function(){return B(A1(_Fz,_Dv));}),_G6=new T(function(){return B(A1(_Fz,_Dp));}),_G7=new T(function(){return B(A1(_Fz,_Dj));}),_G8=new T(function(){return B(A1(_Fz,_Dd));}),_G9=new T(function(){return B(A1(_Fz,_D7));}),_Ga=new T(function(){return B(A1(_Fz,_BD));}),_Gb=new T(function(){return B(A1(_Fz,_Cl));}),_Gc=new T(function(){return B(A1(_Fz,_Cf));}),_Gd=new T(function(){return B(A1(_Fz,_C9));}),_Ge=new T(function(){return B(A1(_Fz,_C3));}),_Gf=new T(function(){return B(A1(_Fz,_BX));}),_Gg=new T(function(){return B(A1(_Fz,_BJ));}),_Gh=new T(function(){return B(A1(_Fz,_BR));}),_Gi=function(_Gj){switch(E(_Gj)){case 64:return E(_Gh);case 65:return E(_Gg);case 66:return E(_Gf);case 67:return E(_Ge);case 68:return E(_Gd);case 69:return E(_Gc);case 70:return E(_Gb);case 71:return E(_FA);case 72:return E(_FB);case 73:return E(_FC);case 74:return E(_FD);case 75:return E(_FE);case 76:return E(_FF);case 77:return E(_FG);case 78:return E(_Ga);case 79:return E(_G9);case 80:return E(_G8);case 81:return E(_G7);case 82:return E(_G6);case 83:return E(_G5);case 84:return E(_G4);case 85:return E(_G3);case 86:return E(_G2);case 87:return E(_G1);case 88:return E(_G0);case 89:return E(_FZ);case 90:return E(_FY);case 91:return E(_FX);case 92:return E(_FW);case 93:return E(_FV);case 94:return E(_FU);case 95:return E(_FT);default:return new T0(2);}};return B(_xi(new T1(0,function(_Gk){return (E(_Gk)==94)?E(new T1(0,_Gi)):new T0(2);}),new T(function(){return B(A1(_Ft,_Fz));})));});return B(_xi(new T1(1,B(_yg(_Ba,_Bc,_FL))),_FS));});return new F(function(){return _xi(new T1(0,function(_Gl){switch(E(_Gl)){case 34:return E(_FJ);case 39:return E(_FI);case 92:return E(_FH);case 97:return E(_FA);case 98:return E(_FB);case 102:return E(_FF);case 110:return E(_FD);case 114:return E(_FG);case 116:return E(_FC);case 118:return E(_FE);default:return new T0(2);}}),_FK);});},_Gm=function(_Gn){return new F(function(){return A1(_Gn,_kF);});},_Go=function(_Gp){var _Gq=E(_Gp);if(!_Gq._){return E(_Gm);}else{var _Gr=E(_Gq.a),_Gs=_Gr>>>0,_Gt=new T(function(){return B(_Go(_Gq.b));});if(_Gs>887){var _Gu=u_iswspace(_Gr);if(!E(_Gu)){return E(_Gm);}else{var _Gv=function(_Gw){var _Gx=new T(function(){return B(A1(_Gt,_Gw));});return new T1(0,function(_Gy){return E(_Gx);});};return E(_Gv);}}else{var _Gz=E(_Gs);if(_Gz==32){var _GA=function(_GB){var _GC=new T(function(){return B(A1(_Gt,_GB));});return new T1(0,function(_GD){return E(_GC);});};return E(_GA);}else{if(_Gz-9>>>0>4){if(E(_Gz)==160){var _GE=function(_GF){var _GG=new T(function(){return B(A1(_Gt,_GF));});return new T1(0,function(_GH){return E(_GG);});};return E(_GE);}else{return E(_Gm);}}else{var _GI=function(_GJ){var _GK=new T(function(){return B(A1(_Gt,_GJ));});return new T1(0,function(_GL){return E(_GK);});};return E(_GI);}}}}},_GM=function(_GN){var _GO=new T(function(){return B(_GM(_GN));}),_GP=function(_GQ){return (E(_GQ)==92)?E(_GO):new T0(2);},_GR=function(_GS){return E(new T1(0,_GP));},_GT=new T1(1,function(_GU){return new F(function(){return A2(_Go,_GU,_GR);});}),_GV=new T(function(){return B(_Fy(function(_GW){return new F(function(){return A1(_GN,new T2(0,_GW,_B4));});}));}),_GX=function(_GY){var _GZ=E(_GY);if(_GZ==38){return E(_GO);}else{var _H0=_GZ>>>0;if(_H0>887){var _H1=u_iswspace(_GZ);return (E(_H1)==0)?new T0(2):E(_GT);}else{var _H2=E(_H0);return (_H2==32)?E(_GT):(_H2-9>>>0>4)?(E(_H2)==160)?E(_GT):new T0(2):E(_GT);}}};return new F(function(){return _xi(new T1(0,function(_H3){return (E(_H3)==92)?E(new T1(0,_GX)):new T0(2);}),new T1(0,function(_H4){var _H5=E(_H4);if(E(_H5)==92){return E(_GV);}else{return new F(function(){return A1(_GN,new T2(0,_H5,_B3));});}}));});},_H6=function(_H7,_H8){var _H9=new T(function(){return B(A1(_H8,new T1(1,new T(function(){return B(A1(_H7,_Z));}))));}),_Ha=function(_Hb){var _Hc=E(_Hb),_Hd=E(_Hc.a);if(E(_Hd)==34){if(!E(_Hc.b)){return E(_H9);}else{return new F(function(){return _H6(function(_He){return new F(function(){return A1(_H7,new T2(1,_Hd,_He));});},_H8);});}}else{return new F(function(){return _H6(function(_Hf){return new F(function(){return A1(_H7,new T2(1,_Hd,_Hf));});},_H8);});}};return new F(function(){return _GM(_Ha);});},_Hg=new T(function(){return B(unCStr("_\'"));}),_Hh=function(_Hi){var _Hj=u_iswalnum(_Hi);if(!E(_Hj)){return new F(function(){return _4H(_l8,_Hi,_Hg);});}else{return true;}},_Hk=function(_Hl){return new F(function(){return _Hh(E(_Hl));});},_Hm=new T(function(){return B(unCStr(",;()[]{}`"));}),_Hn=new T(function(){return B(unCStr("=>"));}),_Ho=new T2(1,_Hn,_Z),_Hp=new T(function(){return B(unCStr("~"));}),_Hq=new T2(1,_Hp,_Ho),_Hr=new T(function(){return B(unCStr("@"));}),_Hs=new T2(1,_Hr,_Hq),_Ht=new T(function(){return B(unCStr("->"));}),_Hu=new T2(1,_Ht,_Hs),_Hv=new T(function(){return B(unCStr("<-"));}),_Hw=new T2(1,_Hv,_Hu),_Hx=new T(function(){return B(unCStr("|"));}),_Hy=new T2(1,_Hx,_Hw),_Hz=new T(function(){return B(unCStr("\\"));}),_HA=new T2(1,_Hz,_Hy),_HB=new T(function(){return B(unCStr("="));}),_HC=new T2(1,_HB,_HA),_HD=new T(function(){return B(unCStr("::"));}),_HE=new T2(1,_HD,_HC),_HF=new T(function(){return B(unCStr(".."));}),_HG=new T2(1,_HF,_HE),_HH=function(_HI){var _HJ=new T(function(){return B(A1(_HI,_yU));}),_HK=new T(function(){var _HL=new T(function(){var _HM=function(_HN){var _HO=new T(function(){return B(A1(_HI,new T1(0,_HN)));});return new T1(0,function(_HP){return (E(_HP)==39)?E(_HO):new T0(2);});};return B(_Fy(_HM));}),_HQ=function(_HR){var _HS=E(_HR);switch(E(_HS)){case 39:return new T0(2);case 92:return E(_HL);default:var _HT=new T(function(){return B(A1(_HI,new T1(0,_HS)));});return new T1(0,function(_HU){return (E(_HU)==39)?E(_HT):new T0(2);});}},_HV=new T(function(){var _HW=new T(function(){return B(_H6(_61,_HI));}),_HX=new T(function(){var _HY=new T(function(){var _HZ=new T(function(){var _I0=function(_I1){var _I2=E(_I1),_I3=u_iswalpha(_I2);return (E(_I3)==0)?(E(_I2)==95)?new T1(1,B(_yG(_Hk,function(_I4){return new F(function(){return A1(_HI,new T1(3,new T2(1,_I2,_I4)));});}))):new T0(2):new T1(1,B(_yG(_Hk,function(_I5){return new F(function(){return A1(_HI,new T1(3,new T2(1,_I2,_I5)));});})));};return B(_xi(new T1(0,_I0),new T(function(){return new T1(1,B(_yg(_zS,_AY,_HI)));})));}),_I6=function(_I7){return (!B(_4H(_l8,_I7,_B0)))?new T0(2):new T1(1,B(_yG(_B1,function(_I8){var _I9=new T2(1,_I7,_I8);if(!B(_4H(_uF,_I9,_HG))){return new F(function(){return A1(_HI,new T1(4,_I9));});}else{return new F(function(){return A1(_HI,new T1(2,_I9));});}})));};return B(_xi(new T1(0,_I6),_HZ));});return B(_xi(new T1(0,function(_Ia){if(!B(_4H(_l8,_Ia,_Hm))){return new T0(2);}else{return new F(function(){return A1(_HI,new T1(2,new T2(1,_Ia,_Z)));});}}),_HY));});return B(_xi(new T1(0,function(_Ib){return (E(_Ib)==34)?E(_HW):new T0(2);}),_HX));});return B(_xi(new T1(0,function(_Ic){return (E(_Ic)==39)?E(new T1(0,_HQ)):new T0(2);}),_HV));});return new F(function(){return _xi(new T1(1,function(_Id){return (E(_Id)._==0)?E(_HJ):new T0(2);}),_HK);});},_Ie=0,_If=function(_Ig,_Ih){var _Ii=new T(function(){var _Ij=new T(function(){var _Ik=function(_Il){var _Im=new T(function(){var _In=new T(function(){return B(A1(_Ih,_Il));});return B(_HH(function(_Io){var _Ip=E(_Io);return (_Ip._==2)?(!B(_vi(_Ip.a,_xV)))?new T0(2):E(_In):new T0(2);}));}),_Iq=function(_Ir){return E(_Im);};return new T1(1,function(_Is){return new F(function(){return A2(_Go,_Is,_Iq);});});};return B(A2(_Ig,_Ie,_Ik));});return B(_HH(function(_It){var _Iu=E(_It);return (_Iu._==2)?(!B(_vi(_Iu.a,_xU)))?new T0(2):E(_Ij):new T0(2);}));}),_Iv=function(_Iw){return E(_Ii);};return function(_Ix){return new F(function(){return A2(_Go,_Ix,_Iv);});};},_Iy=function(_Iz,_IA){var _IB=function(_IC){var _ID=new T(function(){return B(A1(_Iz,_IC));}),_IE=function(_IF){return new F(function(){return _xi(B(A1(_ID,_IF)),new T(function(){return new T1(1,B(_If(_IB,_IF)));}));});};return E(_IE);},_IG=new T(function(){return B(A1(_Iz,_IA));}),_IH=function(_II){return new F(function(){return _xi(B(A1(_IG,_II)),new T(function(){return new T1(1,B(_If(_IB,_II)));}));});};return E(_IH);},_IJ=0,_IK=function(_IL,_IM){return new F(function(){return A1(_IM,_IJ);});},_IN=new T(function(){return B(unCStr("Fr"));}),_IO=new T2(0,_IN,_IK),_IP=1,_IQ=function(_IR,_IS){return new F(function(){return A1(_IS,_IP);});},_IT=new T(function(){return B(unCStr("Bl"));}),_IU=new T2(0,_IT,_IQ),_IV=2,_IW=function(_IX,_IY){return new F(function(){return A1(_IY,_IV);});},_IZ=new T(function(){return B(unCStr("Ex"));}),_J0=new T2(0,_IZ,_IW),_J1=3,_J2=function(_J3,_J4){return new F(function(){return A1(_J4,_J1);});},_J5=new T(function(){return B(unCStr("Mv"));}),_J6=new T2(0,_J5,_J2),_J7=4,_J8=function(_J9,_Ja){return new F(function(){return A1(_Ja,_J7);});},_Jb=new T(function(){return B(unCStr("Pn"));}),_Jc=new T2(0,_Jb,_J8),_Jd=8,_Je=function(_Jf,_Jg){return new F(function(){return A1(_Jg,_Jd);});},_Jh=new T(function(){return B(unCStr("DF"));}),_Ji=new T2(0,_Jh,_Je),_Jj=new T2(1,_Ji,_Z),_Jk=7,_Jl=function(_Jm,_Jn){return new F(function(){return A1(_Jn,_Jk);});},_Jo=new T(function(){return B(unCStr("DB"));}),_Jp=new T2(0,_Jo,_Jl),_Jq=new T2(1,_Jp,_Jj),_Jr=6,_Js=function(_Jt,_Ju){return new F(function(){return A1(_Ju,_Jr);});},_Jv=new T(function(){return B(unCStr("Cm"));}),_Jw=new T2(0,_Jv,_Js),_Jx=new T2(1,_Jw,_Jq),_Jy=5,_Jz=function(_JA,_JB){return new F(function(){return A1(_JB,_Jy);});},_JC=new T(function(){return B(unCStr("Wn"));}),_JD=new T2(0,_JC,_Jz),_JE=new T2(1,_JD,_Jx),_JF=new T2(1,_Jc,_JE),_JG=new T2(1,_J6,_JF),_JH=new T2(1,_J0,_JG),_JI=new T2(1,_IU,_JH),_JJ=new T2(1,_IO,_JI),_JK=function(_JL,_JM,_JN){var _JO=E(_JL);if(!_JO._){return new T0(2);}else{var _JP=E(_JO.a),_JQ=_JP.a,_JR=new T(function(){return B(A2(_JP.b,_JM,_JN));}),_JS=new T(function(){return B(_HH(function(_JT){var _JU=E(_JT);switch(_JU._){case 3:return (!B(_vi(_JQ,_JU.a)))?new T0(2):E(_JR);case 4:return (!B(_vi(_JQ,_JU.a)))?new T0(2):E(_JR);default:return new T0(2);}}));}),_JV=function(_JW){return E(_JS);};return new F(function(){return _xi(new T1(1,function(_JX){return new F(function(){return A2(_Go,_JX,_JV);});}),new T(function(){return B(_JK(_JO.b,_JM,_JN));}));});}},_JY=function(_JZ,_K0){return new F(function(){return _JK(_JJ,_JZ,_K0);});},_K1=function(_K2){var _K3=function(_K4){return E(new T2(3,_K2,_y7));};return new T1(1,function(_K5){return new F(function(){return A2(_Go,_K5,_K3);});});},_K6=new T(function(){return B(A3(_Iy,_JY,_Ie,_K1));}),_K7=new T(function(){return B(err(_wZ));}),_K8=new T(function(){return B(err(_x3));}),_K9=function(_Ka,_Kb){var _Kc=function(_Kd,_Ke){var _Kf=function(_Kg){return new F(function(){return A1(_Ke,new T(function(){return  -E(_Kg);}));});},_Kh=new T(function(){return B(_HH(function(_Ki){return new F(function(){return A3(_Ka,_Ki,_Kd,_Kf);});}));}),_Kj=function(_Kk){return E(_Kh);},_Kl=function(_Km){return new F(function(){return A2(_Go,_Km,_Kj);});},_Kn=new T(function(){return B(_HH(function(_Ko){var _Kp=E(_Ko);if(_Kp._==4){var _Kq=E(_Kp.a);if(!_Kq._){return new F(function(){return A3(_Ka,_Kp,_Kd,_Ke);});}else{if(E(_Kq.a)==45){if(!E(_Kq.b)._){return E(new T1(1,_Kl));}else{return new F(function(){return A3(_Ka,_Kp,_Kd,_Ke);});}}else{return new F(function(){return A3(_Ka,_Kp,_Kd,_Ke);});}}}else{return new F(function(){return A3(_Ka,_Kp,_Kd,_Ke);});}}));}),_Kr=function(_Ks){return E(_Kn);};return new T1(1,function(_Kt){return new F(function(){return A2(_Go,_Kt,_Kr);});});};return new F(function(){return _Iy(_Kc,_Kb);});},_Ku=function(_Kv){var _Kw=E(_Kv);if(!_Kw._){var _Kx=_Kw.b,_Ky=new T(function(){return B(_Aa(new T(function(){return B(_eS(E(_Kw.a)));}),new T(function(){return B(_qu(_Kx,0));},1),B(_aj(_A0,_Kx))));});return new T1(1,_Ky);}else{return (E(_Kw.b)._==0)?(E(_Kw.c)._==0)?new T1(1,new T(function(){return B(_Ar(_zZ,_Kw.a));})):__Z:__Z;}},_Kz=function(_KA,_KB){return new T0(2);},_KC=function(_KD){var _KE=E(_KD);if(_KE._==5){var _KF=B(_Ku(_KE.a));if(!_KF._){return E(_Kz);}else{var _KG=new T(function(){return B(_fb(_KF.a));});return function(_KH,_KI){return new F(function(){return A1(_KI,_KG);});};}}else{return E(_Kz);}},_KJ=new T(function(){return B(A3(_K9,_KC,_Ie,_K1));}),_KK=new T2(1,_F,_Z),_KL=function(_KM){while(1){var _KN=B((function(_KO){var _KP=E(_KO);if(!_KP._){return __Z;}else{var _KQ=_KP.b,_KR=E(_KP.a);if(!E(_KR.b)._){return new T2(1,_KR.a,new T(function(){return B(_KL(_KQ));}));}else{_KM=_KQ;return __continue;}}})(_KM));if(_KN!=__continue){return _KN;}}},_KS=function(_KT,_KU){while(1){var _KV=E(_KT);if(!_KV._){return E(_KU);}else{var _KW=new T2(1,_KV.a,_KU);_KT=_KV.b;_KU=_KW;continue;}}},_KX=function(_KY,_KZ){var _L0=E(_KY);if(!_L0._){return __Z;}else{var _L1=E(_KZ);return (_L1._==0)?__Z:new T2(1,new T2(0,_L0.a,_L1.a),new T(function(){return B(_KX(_L0.b,_L1.b));}));}},_L2=function(_L3,_L4,_L5){while(1){var _L6=B((function(_L7,_L8,_L9){var _La=E(_L9);if(!_La._){return E(_L8);}else{var _Lb=_La.a,_Lc=_La.b,_Ld=B(_wT(_uF,_Lb,_wI));if(!_Ld._){var _Le=E(_x6);}else{var _Le=E(_Ld.a);}if(!B(_vn(_Le,_x6))){var _Lf=B(_KS(B(_KX(B(_KS(_L8,_Z)),new T(function(){return B(_KS(_Le,_Z));},1))),_Z)),_Lg=B(_qu(_Lf,0)),_Lh=new T(function(){var _Li=B(_aj(_wR,_Lf));if(!_Li._){return __Z;}else{var _Lj=_Li.a,_Lk=E(_Li.b);if(!_Lk._){return __Z;}else{var _Ll=_Lk.a;if(!E(_Lk.b)._){if(!B(_vi(_Lb,_wk))){if(!B(_vi(_Lb,_wj))){if(!B(_vi(_Lb,_wi))){if(!B(_vi(_Lb,_wm))){if(!B(_vi(_Lb,_wl))){return __Z;}else{if(!B(_vi(_Lj,_x1))){if(!B(_vi(_Ll,_x1))){return E(_x2);}else{return E(_x1);}}else{return E(_x1);}}}else{var _Lm=B(_w6(new T2(0,new T(function(){var _Ln=E(_Lj);if(!_Ln._){return E(_ri);}else{return E(_Ln.a);}}),new T(function(){var _Lo=B(_KL(B(_x8(_K6,_Ll))));if(!_Lo._){return E(_x0);}else{if(!E(_Lo.b)._){return E(_Lo.a);}else{return E(_x4);}}})),E(E(_L7).a).b)),_Lp=new T(function(){return B(A3(_wL,_vs,new T2(1,function(_Lq){return new F(function(){return _H(0,E(_Lm.a),_Lq);});},new T2(1,function(_Lr){return new F(function(){return _H(0,E(_Lm.b),_Lr);});},_Z)),_KK));});return new T2(1,_G,_Lp);}}else{return new T2(1,new T(function(){var _Ls=B(_KL(B(_x8(_KJ,_Lj))));if(!_Ls._){return E(_K7);}else{if(!E(_Ls.b)._){var _Lt=B(_KL(B(_x8(_KJ,_Ll))));if(!_Lt._){return E(_K7);}else{if(!E(_Lt.b)._){return E(B(_aS(B(_aS(E(E(_L7).a).b,E(_Lt.a))),E(_Ls.a))).a);}else{return E(_K8);}}}else{return E(_K8);}}}),_Z);}}else{if(!B(_vi(_Lj,_Ll))){return E(_x2);}else{return E(_x1);}}}else{if(!B(_vi(_Lj,_x1))){return E(_x2);}else{if(!B(_vi(_Ll,_x1))){return E(_x2);}else{return E(_x1);}}}}else{return __Z;}}}});if(_Lg>0){var _Lu=_L7,_Lv=B(_x(B(_KS(B(_wc(_Lg,B(_KS(_L8,_Z)))),_Z)),new T2(1,_Lh,_Z)));_L3=_Lu;_L4=_Lv;_L5=_Lc;return __continue;}else{var _Lu=_L7,_Lv=B(_x(B(_KS(B(_KS(_L8,_Z)),_Z)),new T2(1,_Lh,_Z)));_L3=_Lu;_L4=_Lv;_L5=_Lc;return __continue;}}else{var _Lu=_L7,_Lv=B(_x(_L8,new T2(1,_Lb,_Z)));_L3=_Lu;_L4=_Lv;_L5=_Lc;return __continue;}}})(_L3,_L4,_L5));if(_L6!=__continue){return _L6;}}},_Lw=new T(function(){return B(_i8("Event.hs:(102,1)-(106,73)|function addMemory"));}),_Lx=function(_Ly,_Lz){var _LA=E(_Ly),_LB=E(_Lz);if(!B(_vi(_LA.a,_LB.a))){return false;}else{return new F(function(){return _vi(_LA.b,_LB.b);});}},_LC=new T2(1,_Z,_Z),_LD=function(_LE,_LF,_LG){var _LH=E(_LG);if(!_LH._){return new T2(0,new T2(1,_LF,_Z),_Z);}else{var _LI=E(_LF),_LJ=new T(function(){var _LK=B(_LD(_LE,_LH.a,_LH.b));return new T2(0,_LK.a,_LK.b);});return (_LE!=_LI)?new T2(0,new T2(1,_LI,new T(function(){return E(E(_LJ).a);})),new T(function(){return E(E(_LJ).b);})):new T2(0,_Z,new T2(1,new T(function(){return E(E(_LJ).a);}),new T(function(){return E(E(_LJ).b);})));}},_LL=32,_LM=function(_LN){var _LO=E(_LN);if(!_LO._){return __Z;}else{var _LP=new T(function(){return B(_x(_LO.a,new T(function(){return B(_LM(_LO.b));},1)));});return new T2(1,_LL,_LP);}},_LQ=function(_LR,_LS,_LT,_LU,_LV,_LW,_LX,_LY,_LZ,_M0,_M1,_M2,_M3,_M4,_M5,_M6,_M7,_M8,_M9,_Ma,_Mb,_Mc,_Md,_Me){while(1){var _Mf=B((function(_Mg,_Mh,_Mi,_Mj,_Mk,_Ml,_Mm,_Mn,_Mo,_Mp,_Mq,_Mr,_Ms,_Mt,_Mu,_Mv,_Mw,_Mx,_My,_Mz,_MA,_MB,_MC,_MD){var _ME=E(_Mg);if(!_ME._){return {_:0,a:_Mh,b:_Mi,c:_Mj,d:_Mk,e:_Ml,f:_Mm,g:_Mn,h:_Mo,i:_Mp,j:_Mq,k:_Mr,l:_Ms,m:_Mt,n:_Mu,o:_Mv,p:_Mw,q:_Mx,r:_My,s:_Mz,t:_MA,u:_MB,v:_MC,w:_MD};}else{var _MF=_ME.a,_MG=E(_ME.b);if(!_MG._){return E(_Lw);}else{var _MH=new T(function(){var _MI=E(_MG.a);if(!_MI._){var _MJ=B(_L2({_:0,a:E(_Mh),b:E(_Mi),c:E(_Mj),d:E(_Mk),e:E(_Ml),f:E(_Mm),g:E(_Mn),h:E(_Mo),i:_Mp,j:_Mq,k:_Mr,l:_Ms,m:E(_Mt),n:_Mu,o:E(_Mv),p:E(_Mw),q:_Mx,r:E(_My),s:E(_Mz),t:_MA,u:E(_MB),v:E(_MC),w:E(_MD)},_Z,_LC));if(!_MJ._){return __Z;}else{return B(_x(_MJ.a,new T(function(){return B(_LM(_MJ.b));},1)));}}else{var _MK=_MI.a,_ML=E(_MI.b);if(!_ML._){var _MM=B(_L2({_:0,a:E(_Mh),b:E(_Mi),c:E(_Mj),d:E(_Mk),e:E(_Ml),f:E(_Mm),g:E(_Mn),h:E(_Mo),i:_Mp,j:_Mq,k:_Mr,l:_Ms,m:E(_Mt),n:_Mu,o:E(_Mv),p:E(_Mw),q:_Mx,r:E(_My),s:E(_Mz),t:_MA,u:E(_MB),v:E(_MC),w:E(_MD)},_Z,new T2(1,new T2(1,_MK,_Z),_Z)));if(!_MM._){return __Z;}else{return B(_x(_MM.a,new T(function(){return B(_LM(_MM.b));},1)));}}else{var _MN=E(_MK),_MO=new T(function(){var _MP=B(_LD(95,_ML.a,_ML.b));return new T2(0,_MP.a,_MP.b);});if(E(_MN)==95){var _MQ=B(_L2({_:0,a:E(_Mh),b:E(_Mi),c:E(_Mj),d:E(_Mk),e:E(_Ml),f:E(_Mm),g:E(_Mn),h:E(_Mo),i:_Mp,j:_Mq,k:_Mr,l:_Ms,m:E(_Mt),n:_Mu,o:E(_Mv),p:E(_Mw),q:_Mx,r:E(_My),s:E(_Mz),t:_MA,u:E(_MB),v:E(_MC),w:E(_MD)},_Z,new T2(1,_Z,new T2(1,new T(function(){return E(E(_MO).a);}),new T(function(){return E(E(_MO).b);})))));if(!_MQ._){return __Z;}else{return B(_x(_MQ.a,new T(function(){return B(_LM(_MQ.b));},1)));}}else{var _MR=B(_L2({_:0,a:E(_Mh),b:E(_Mi),c:E(_Mj),d:E(_Mk),e:E(_Ml),f:E(_Mm),g:E(_Mn),h:E(_Mo),i:_Mp,j:_Mq,k:_Mr,l:_Ms,m:E(_Mt),n:_Mu,o:E(_Mv),p:E(_Mw),q:_Mx,r:E(_My),s:E(_Mz),t:_MA,u:E(_MB),v:E(_MC),w:E(_MD)},_Z,new T2(1,new T2(1,_MN,new T(function(){return E(E(_MO).a);})),new T(function(){return E(E(_MO).b);}))));if(!_MR._){return __Z;}else{return B(_x(_MR.a,new T(function(){return B(_LM(_MR.b));},1)));}}}}}),_MS=_Mh,_MT=_Mi,_MU=_Mj,_MV=_Mk,_MW=_Ml,_MX=_Mm,_MY=_Mo,_MZ=_Mp,_N0=_Mq,_N1=_Mr,_N2=_Ms,_N3=_Mt,_N4=_Mu,_N5=_Mv,_N6=_Mw,_N7=_Mx,_N8=_My,_N9=_Mz,_Na=_MA,_Nb=_MB,_Nc=_MC,_Nd=_MD;_LR=_MG.b;_LS=_MS;_LT=_MT;_LU=_MU;_LV=_MV;_LW=_MW;_LX=_MX;_LY=new T2(1,new T2(0,_MF,_MH),new T(function(){var _Ne=B(_wT(_uF,_MF,_Mn));if(!_Ne._){var _Nf=__Z;}else{var _Nf=E(_Ne.a);}if(!B(_vi(_Nf,_Z))){return B(_vb(_Lx,new T2(0,_MF,_Nf),_Mn));}else{return E(_Mn);}}));_LZ=_MY;_M0=_MZ;_M1=_N0;_M2=_N1;_M3=_N2;_M4=_N3;_M5=_N4;_M6=_N5;_M7=_N6;_M8=_N7;_M9=_N8;_Ma=_N9;_Mb=_Na;_Mc=_Nb;_Md=_Nc;_Me=_Nd;return __continue;}}})(_LR,_LS,_LT,_LU,_LV,_LW,_LX,_LY,_LZ,_M0,_M1,_M2,_M3,_M4,_M5,_M6,_M7,_M8,_M9,_Ma,_Mb,_Mc,_Md,_Me));if(_Mf!=__continue){return _Mf;}}},_Ng=function(_Nh){var _Ni=E(_Nh);if(!_Ni._){return new T2(0,_Z,_Z);}else{var _Nj=E(_Ni.a),_Nk=new T(function(){var _Nl=B(_Ng(_Ni.b));return new T2(0,_Nl.a,_Nl.b);});return new T2(0,new T2(1,_Nj.a,new T(function(){return E(E(_Nk).a);})),new T2(1,_Nj.b,new T(function(){return E(E(_Nk).b);})));}},_Nm=function(_Nn,_No,_Np){while(1){var _Nq=B((function(_Nr,_Ns,_Nt){var _Nu=E(_Nt);if(!_Nu._){return __Z;}else{var _Nv=_Nu.b;if(_Ns!=E(_Nu.a)){var _Nw=_Nr+1|0,_Nx=_Ns;_Nn=_Nw;_No=_Nx;_Np=_Nv;return __continue;}else{return new T2(1,_Nr,new T(function(){return B(_Nm(_Nr+1|0,_Ns,_Nv));}));}}})(_Nn,_No,_Np));if(_Nq!=__continue){return _Nq;}}},_Ny=function(_Nz,_NA,_NB){var _NC=E(_NB);if(!_NC._){return __Z;}else{var _ND=_NC.b,_NE=E(_NA);if(_NE!=E(_NC.a)){return new F(function(){return _Nm(_Nz+1|0,_NE,_ND);});}else{return new T2(1,_Nz,new T(function(){return B(_Nm(_Nz+1|0,_NE,_ND));}));}}},_NF=function(_NG,_NH,_NI,_NJ){var _NK=E(_NJ);if(!_NK._){return __Z;}else{var _NL=_NK.b;return (!B(_4H(_3S,_NG,_NI)))?new T2(1,_NK.a,new T(function(){return B(_NF(_NG+1|0,_NH,_NI,_NL));})):new T2(1,_NH,new T(function(){return B(_NF(_NG+1|0,_NH,_NI,_NL));}));}},_NM=function(_NN,_NO,_NP){var _NQ=E(_NP);if(!_NQ._){return __Z;}else{var _NR=new T(function(){var _NS=B(_Ng(_NQ.a)),_NT=_NS.a,_NU=new T(function(){return B(_NF(0,_NO,new T(function(){return B(_Ny(0,_NN,_NT));}),_NS.b));},1);return B(_KX(_NT,_NU));});return new T2(1,_NR,new T(function(){return B(_NM(_NN,_NO,_NQ.b));}));}},_NV=function(_NW){var _NX=E(_NW);return (_NX._==0)?E(_ri):E(_NX.a);},_NY=new T(function(){return B(_i8("Event.hs:(75,1)-(78,93)|function changeType"));}),_NZ=new T(function(){return B(_i8("Event.hs:72:16-116|case"));}),_O0=new T(function(){return B(unCStr("Wn"));}),_O1=new T(function(){return B(unCStr("Pn"));}),_O2=new T(function(){return B(unCStr("Mv"));}),_O3=new T(function(){return B(unCStr("Fr"));}),_O4=new T(function(){return B(unCStr("Ex"));}),_O5=new T(function(){return B(unCStr("DF"));}),_O6=new T(function(){return B(unCStr("DB"));}),_O7=new T(function(){return B(unCStr("Cm"));}),_O8=new T(function(){return B(unCStr("Bl"));}),_O9=function(_Oa){return (!B(_vi(_Oa,_O8)))?(!B(_vi(_Oa,_O7)))?(!B(_vi(_Oa,_O6)))?(!B(_vi(_Oa,_O5)))?(!B(_vi(_Oa,_O4)))?(!B(_vi(_Oa,_O3)))?(!B(_vi(_Oa,_O2)))?(!B(_vi(_Oa,_O1)))?(!B(_vi(_Oa,_O0)))?E(_NZ):5:4:3:0:2:8:7:6:1;},_Ob=function(_Oc,_Od,_Oe,_Of,_Og,_Oh,_Oi,_Oj,_Ok,_Ol,_Om,_On,_Oo,_Op,_Oq,_Or,_Os,_Ot,_Ou,_Ov,_Ow,_Ox,_Oy,_Oz){while(1){var _OA=B((function(_OB,_OC,_OD,_OE,_OF,_OG,_OH,_OI,_OJ,_OK,_OL,_OM,_ON,_OO,_OP,_OQ,_OR,_OS,_OT,_OU,_OV,_OW,_OX,_OY){var _OZ=E(_OB);if(!_OZ._){return {_:0,a:_OC,b:_OD,c:_OE,d:_OF,e:_OG,f:_OH,g:_OI,h:_OJ,i:_OK,j:_OL,k:_OM,l:_ON,m:_OO,n:_OP,o:_OQ,p:_OR,q:_OS,r:_OT,s:_OU,t:_OV,u:_OW,v:_OX,w:_OY};}else{var _P0=E(_OZ.b);if(!_P0._){return E(_NY);}else{var _P1=E(_OC),_P2=_OD,_P3=_OE,_P4=_OF,_P5=_OG,_P6=_OH,_P7=_OI,_P8=_OJ,_P9=_OK,_Pa=_OL,_Pb=_OM,_Pc=_ON,_Pd=_OO,_Pe=_OP,_Pf=_OQ,_Pg=_OR,_Ph=_OS,_Pi=_OT,_Pj=_OU,_Pk=_OV,_Pl=_OW,_Pm=_OX,_Pn=_OY;_Oc=_P0.b;_Od={_:0,a:E(_P1.a),b:E(B(_NM(new T(function(){return B(_NV(_OZ.a));}),new T(function(){return B(_O9(_P0.a));}),_P1.b))),c:E(_P1.c),d:_P1.d,e:_P1.e,f:_P1.f,g:E(_P1.g),h:_P1.h,i:E(_P1.i),j:E(_P1.j),k:E(_P1.k)};_Oe=_P2;_Of=_P3;_Og=_P4;_Oh=_P5;_Oi=_P6;_Oj=_P7;_Ok=_P8;_Ol=_P9;_Om=_Pa;_On=_Pb;_Oo=_Pc;_Op=_Pd;_Oq=_Pe;_Or=_Pf;_Os=_Pg;_Ot=_Ph;_Ou=_Pi;_Ov=_Pj;_Ow=_Pk;_Ox=_Pl;_Oy=_Pm;_Oz=_Pn;return __continue;}}})(_Oc,_Od,_Oe,_Of,_Og,_Oh,_Oi,_Oj,_Ok,_Ol,_Om,_On,_Oo,_Op,_Oq,_Or,_Os,_Ot,_Ou,_Ov,_Ow,_Ox,_Oy,_Oz));if(_OA!=__continue){return _OA;}}},_Po=function(_Pp,_Pq){while(1){var _Pr=E(_Pq);if(!_Pr._){return __Z;}else{var _Ps=_Pr.b,_Pt=E(_Pp);if(_Pt==1){return E(_Ps);}else{_Pp=_Pt-1|0;_Pq=_Ps;continue;}}}},_Pu=function(_Pv,_Pw){while(1){var _Px=E(_Pw);if(!_Px._){return __Z;}else{var _Py=_Px.b,_Pz=E(_Pv);if(_Pz==1){return E(_Py);}else{_Pv=_Pz-1|0;_Pw=_Py;continue;}}}},_PA=function(_PB,_PC,_PD,_PE,_PF){var _PG=new T(function(){var _PH=E(_PB),_PI=new T(function(){return B(_aS(_PF,_PC));}),_PJ=new T2(1,new T2(0,_PD,_PE),new T(function(){var _PK=_PH+1|0;if(_PK>0){return B(_Pu(_PK,_PI));}else{return E(_PI);}}));if(0>=_PH){return E(_PJ);}else{var _PL=function(_PM,_PN){var _PO=E(_PM);if(!_PO._){return E(_PJ);}else{var _PP=_PO.a,_PQ=E(_PN);return (_PQ==1)?new T2(1,_PP,_PJ):new T2(1,_PP,new T(function(){return B(_PL(_PO.b,_PQ-1|0));}));}};return B(_PL(_PI,_PH));}}),_PR=new T2(1,_PG,new T(function(){var _PS=_PC+1|0;if(_PS>0){return B(_Po(_PS,_PF));}else{return E(_PF);}}));if(0>=_PC){return E(_PR);}else{var _PT=function(_PU,_PV){var _PW=E(_PU);if(!_PW._){return E(_PR);}else{var _PX=_PW.a,_PY=E(_PV);return (_PY==1)?new T2(1,_PX,_PR):new T2(1,_PX,new T(function(){return B(_PT(_PW.b,_PY-1|0));}));}};return new F(function(){return _PT(_PF,_PC);});}},_PZ=32,_Q0=new T(function(){return B(unCStr("Irrefutable pattern failed for pattern"));}),_Q1=function(_Q2){return new F(function(){return _hK(new T1(0,new T(function(){return B(_hX(_Q2,_Q0));})),_hu);});},_Q3=function(_Q4){return new F(function(){return _Q1("Event.hs:58:27-53|(x\' : y\' : _)");});},_Q5=new T(function(){return B(_Q3(_));}),_Q6=function(_Q7,_Q8,_Q9,_Qa,_Qb,_Qc,_Qd,_Qe,_Qf,_Qg,_Qh,_Qi,_Qj,_Qk,_Ql,_Qm,_Qn,_Qo,_Qp,_Qq,_Qr,_Qs,_Qt,_Qu){while(1){var _Qv=B((function(_Qw,_Qx,_Qy,_Qz,_QA,_QB,_QC,_QD,_QE,_QF,_QG,_QH,_QI,_QJ,_QK,_QL,_QM,_QN,_QO,_QP,_QQ,_QR,_QS,_QT){var _QU=E(_Qw);if(!_QU._){return {_:0,a:_Qx,b:_Qy,c:_Qz,d:_QA,e:_QB,f:_QC,g:_QD,h:_QE,i:_QF,j:_QG,k:_QH,l:_QI,m:_QJ,n:_QK,o:_QL,p:_QM,q:_QN,r:_QO,s:_QP,t:_QQ,u:_QR,v:_QS,w:_QT};}else{var _QV=E(_Qx),_QW=new T(function(){var _QX=E(_QU.a);if(!_QX._){return E(_Q5);}else{var _QY=E(_QX.b);if(!_QY._){return E(_Q5);}else{var _QZ=_QY.a,_R0=_QY.b,_R1=E(_QX.a);if(E(_R1)==44){return new T2(0,_Z,new T(function(){return E(B(_LD(44,_QZ,_R0)).a);}));}else{var _R2=B(_LD(44,_QZ,_R0)),_R3=E(_R2.b);if(!_R3._){return E(_Q5);}else{return new T2(0,new T2(1,_R1,_R2.a),_R3.a);}}}}}),_R4=B(_KL(B(_x8(_KJ,new T(function(){return E(E(_QW).b);})))));if(!_R4._){return E(_K7);}else{if(!E(_R4.b)._){var _R5=new T(function(){var _R6=B(_KL(B(_x8(_KJ,new T(function(){return E(E(_QW).a);})))));if(!_R6._){return E(_K7);}else{if(!E(_R6.b)._){return E(_R6.a);}else{return E(_K8);}}},1),_R7=_Qy,_R8=_Qz,_R9=_QA,_Ra=_QB,_Rb=_QC,_Rc=_QD,_Rd=_QE,_Re=_QF,_Rf=_QG,_Rg=_QH,_Rh=_QI,_Ri=_QJ,_Rj=_QK,_Rk=_QL,_Rl=_QM,_Rm=_QN,_Rn=_QO,_Ro=_QP,_Rp=_QQ,_Rq=_QR,_Rr=_QS,_Rs=_QT;_Q7=_QU.b;_Q8={_:0,a:E(_QV.a),b:E(B(_PA(_R5,E(_R4.a),_PZ,_IJ,_QV.b))),c:E(_QV.c),d:_QV.d,e:_QV.e,f:_QV.f,g:E(_QV.g),h:_QV.h,i:E(_QV.i),j:E(_QV.j),k:E(_QV.k)};_Q9=_R7;_Qa=_R8;_Qb=_R9;_Qc=_Ra;_Qd=_Rb;_Qe=_Rc;_Qf=_Rd;_Qg=_Re;_Qh=_Rf;_Qi=_Rg;_Qj=_Rh;_Qk=_Ri;_Ql=_Rj;_Qm=_Rk;_Qn=_Rl;_Qo=_Rm;_Qp=_Rn;_Qq=_Ro;_Qr=_Rp;_Qs=_Rq;_Qt=_Rr;_Qu=_Rs;return __continue;}else{return E(_K8);}}}})(_Q7,_Q8,_Q9,_Qa,_Qb,_Qc,_Qd,_Qe,_Qf,_Qg,_Qh,_Qi,_Qj,_Qk,_Ql,_Qm,_Qn,_Qo,_Qp,_Qq,_Qr,_Qs,_Qt,_Qu));if(_Qv!=__continue){return _Qv;}}},_Rt=function(_Ru,_Rv,_Rw){var _Rx=E(_Rw);return (_Rx._==0)?0:(!B(A3(_4F,_Ru,_Rv,_Rx.a)))?1+B(_Rt(_Ru,_Rv,_Rx.b))|0:0;},_Ry=function(_Rz,_RA){while(1){var _RB=E(_RA);if(!_RB._){return __Z;}else{var _RC=_RB.b,_RD=E(_Rz);if(_RD==1){return E(_RC);}else{_Rz=_RD-1|0;_RA=_RC;continue;}}}},_RE=function(_RF,_RG){var _RH=new T(function(){var _RI=_RF+1|0;if(_RI>0){return B(_Ry(_RI,_RG));}else{return E(_RG);}});if(0>=_RF){return E(_RH);}else{var _RJ=function(_RK,_RL){var _RM=E(_RK);if(!_RM._){return E(_RH);}else{var _RN=_RM.a,_RO=E(_RL);return (_RO==1)?new T2(1,_RN,_RH):new T2(1,_RN,new T(function(){return B(_RJ(_RM.b,_RO-1|0));}));}};return new F(function(){return _RJ(_RG,_RF);});}},_RP=function(_RQ,_RR){return new F(function(){return _RE(E(_RQ),_RR);});},_RS= -1,_RT=function(_RU,_RV,_RW,_RX,_RY,_RZ,_S0,_S1,_S2,_S3,_S4,_S5,_S6,_S7,_S8,_S9,_Sa,_Sb,_Sc,_Sd,_Se,_Sf,_Sg,_Sh){while(1){var _Si=B((function(_Sj,_Sk,_Sl,_Sm,_Sn,_So,_Sp,_Sq,_Sr,_Ss,_St,_Su,_Sv,_Sw,_Sx,_Sy,_Sz,_SA,_SB,_SC,_SD,_SE,_SF,_SG){var _SH=E(_Sj);if(!_SH._){return {_:0,a:_Sk,b:_Sl,c:_Sm,d:_Sn,e:_So,f:_Sp,g:_Sq,h:_Sr,i:_Ss,j:_St,k:_Su,l:_Sv,m:_Sw,n:_Sx,o:_Sy,p:_Sz,q:_SA,r:_SB,s:_SC,t:_SD,u:_SE,v:_SF,w:_SG};}else{var _SI=_SH.a,_SJ=B(_aj(_wR,_So)),_SK=B(_4H(_uF,_SI,_SJ)),_SL=new T(function(){if(!E(_SK)){return E(_RS);}else{return B(_Rt(_uF,_SI,_SJ));}});if(!E(_SK)){var _SM=E(_So);}else{var _SM=B(_RP(_SL,_So));}if(!E(_SK)){var _SN=E(_Sp);}else{var _SN=B(_RP(_SL,_Sp));}var _SO=_Sk,_SP=_Sl,_SQ=_Sm,_SR=_Sn,_SS=_Sq,_ST=_Sr,_SU=_Ss,_SV=_St,_SW=_Su,_SX=_Sv,_SY=_Sw,_SZ=_Sx,_T0=_Sy,_T1=_Sz,_T2=_SA,_T3=_SB,_T4=_SC,_T5=_SD,_T6=_SE,_T7=_SF,_T8=_SG;_RU=_SH.b;_RV=_SO;_RW=_SP;_RX=_SQ;_RY=_SR;_RZ=_SM;_S0=_SN;_S1=_SS;_S2=_ST;_S3=_SU;_S4=_SV;_S5=_SW;_S6=_SX;_S7=_SY;_S8=_SZ;_S9=_T0;_Sa=_T1;_Sb=_T2;_Sc=_T3;_Sd=_T4;_Se=_T5;_Sf=_T6;_Sg=_T7;_Sh=_T8;return __continue;}})(_RU,_RV,_RW,_RX,_RY,_RZ,_S0,_S1,_S2,_S3,_S4,_S5,_S6,_S7,_S8,_S9,_Sa,_Sb,_Sc,_Sd,_Se,_Sf,_Sg,_Sh));if(_Si!=__continue){return _Si;}}},_T9=function(_Ta){var _Tb=E(_Ta);if(!_Tb._){return new T2(0,_Z,_Z);}else{var _Tc=E(_Tb.a),_Td=new T(function(){var _Te=B(_T9(_Tb.b));return new T2(0,_Te.a,_Te.b);});return new T2(0,new T2(1,_Tc.a,new T(function(){return E(E(_Td).a);})),new T2(1,_Tc.b,new T(function(){return E(E(_Td).b);})));}},_Tf=function(_Tg,_Th){while(1){var _Ti=E(_Tg);if(!_Ti._){return E(_Th);}else{var _Tj=_Th+E(_Ti.a)|0;_Tg=_Ti.b;_Th=_Tj;continue;}}},_Tk=function(_Tl,_Tm){while(1){var _Tn=E(_Tm);if(!_Tn._){return __Z;}else{var _To=_Tn.b,_Tp=E(_Tl);if(_Tp==1){return E(_To);}else{_Tl=_Tp-1|0;_Tm=_To;continue;}}}},_Tq=function(_Tr,_Ts,_Tt,_Tu,_Tv,_Tw,_Tx,_Ty,_Tz,_TA,_TB,_TC,_TD,_TE,_TF,_TG,_TH,_TI,_TJ,_TK,_TL,_TM,_TN,_TO){while(1){var _TP=B((function(_TQ,_TR,_TS,_TT,_TU,_TV,_TW,_TX,_TY,_TZ,_U0,_U1,_U2,_U3,_U4,_U5,_U6,_U7,_U8,_U9,_Ua,_Ub,_Uc,_Ud){var _Ue=E(_TQ);if(!_Ue._){return {_:0,a:_TR,b:_TS,c:_TT,d:_TU,e:_TV,f:_TW,g:_TX,h:_TY,i:_TZ,j:_U0,k:_U1,l:_U2,m:_U3,n:_U4,o:_U5,p:_U6,q:_U7,r:_U8,s:_U9,t:_Ua,u:_Ub,v:_Uc,w:_Ud};}else{var _Uf=new T(function(){var _Ug=B(_KL(B(_x8(_KJ,_Ue.a))));if(!_Ug._){return E(_K7);}else{if(!E(_Ug.b)._){return B(_x(B(_H(0,B(_aS(_U8,E(_Ug.a))),_Z)),new T(function(){if(_TZ>0){return B(_Tk(_TZ,_TT));}else{return E(_TT);}},1)));}else{return E(_K8);}}});if(0>=_TZ){var _Uh=E(_Uf);}else{var _Ui=function(_Uj,_Uk){var _Ul=E(_Uj);if(!_Ul._){return E(_Uf);}else{var _Um=_Ul.a,_Un=E(_Uk);return (_Un==1)?new T2(1,_Um,_Uf):new T2(1,_Um,new T(function(){return B(_Ui(_Ul.b,_Un-1|0));}));}},_Uh=B(_Ui(_TT,_TZ));}var _Uo=_TR,_Up=_TS,_Uq=_TU,_Ur=_TV,_Us=_TW,_Ut=_TX,_Uu=_TY,_Uv=_TZ,_Uw=_U0,_Ux=_U1,_Uy=_U2,_Uz=_U3,_UA=_U4,_UB=_U5,_UC=_U6,_UD=_U7,_UE=_U8,_UF=_U9,_UG=_Ua,_UH=_Ub,_UI=_Uc,_UJ=_Ud;_Tr=_Ue.b;_Ts=_Uo;_Tt=_Up;_Tu=_Uh;_Tv=_Uq;_Tw=_Ur;_Tx=_Us;_Ty=_Ut;_Tz=_Uu;_TA=_Uv;_TB=_Uw;_TC=_Ux;_TD=_Uy;_TE=_Uz;_TF=_UA;_TG=_UB;_TH=_UC;_TI=_UD;_TJ=_UE;_TK=_UF;_TL=_UG;_TM=_UH;_TN=_UI;_TO=_UJ;return __continue;}})(_Tr,_Ts,_Tt,_Tu,_Tv,_Tw,_Tx,_Ty,_Tz,_TA,_TB,_TC,_TD,_TE,_TF,_TG,_TH,_TI,_TJ,_TK,_TL,_TM,_TN,_TO));if(_TP!=__continue){return _TP;}}},_UK=function(_UL){return new F(function(){return _Q1("Event.hs:119:28-52|(c : d : _)");});},_UM=new T(function(){return B(_UK(_));}),_UN=function(_UO,_UP,_UQ,_UR,_US,_UT,_UU,_UV,_UW,_UX,_UY,_UZ,_V0,_V1,_V2,_V3,_V4,_V5,_V6,_V7,_V8,_V9,_Va,_Vb,_Vc,_Vd,_Ve,_Vf,_Vg,_Vh,_Vi,_Vj){while(1){var _Vk=B((function(_Vl,_Vm,_Vn,_Vo,_Vp,_Vq,_Vr,_Vs,_Vt,_Vu,_Vv,_Vw,_Vx,_Vy,_Vz,_VA,_VB,_VC,_VD,_VE,_VF,_VG,_VH,_VI,_VJ,_VK,_VL,_VM,_VN,_VO,_VP,_VQ){var _VR=E(_Vl);if(!_VR._){return {_:0,a:E(_Vm),b:E(_Vn),c:E(_Vo),d:E(_Vp),e:E(_Vq),f:E(_Vr),g:E(_Vs),h:E(_Vt),i:_Vu,j:_Vv,k:_Vw,l:_Vx,m:E(_Vy),n:_Vz,o:E(_VA),p:E(_VB),q:_VC,r:E(_VD),s:E(_VE),t:_VF,u:E(_VG),v:E({_:0,a:E(_VH),b:E(_VI),c:E(_VJ),d:E(_B4),e:E(_VL),f:E(_VM),g:E(_B4),h:E(_VO),i:E(_VP)}),w:E(_VQ)};}else{var _VS=new T(function(){var _VT=E(_VR.a);if(!_VT._){return E(_UM);}else{var _VU=E(_VT.b);if(!_VU._){return E(_UM);}else{var _VV=_VU.a,_VW=_VU.b,_VX=E(_VT.a);if(E(_VX)==44){return new T2(0,_Z,new T(function(){return E(B(_LD(44,_VV,_VW)).a);}));}else{var _VY=B(_LD(44,_VV,_VW)),_VZ=E(_VY.b);if(!_VZ._){return E(_UM);}else{return new T2(0,new T2(1,_VX,_VY.a),_VZ.a);}}}}}),_W0=_Vm,_W1=_Vn,_W2=_Vo,_W3=_Vp,_W4=_Vq,_W5=_Vr,_W6=_Vs,_W7=_Vt,_W8=_Vu,_W9=_Vv,_Wa=_Vw,_Wb=_Vx,_Wc=B(_x(_Vy,new T2(1,new T2(0,new T(function(){return E(E(_VS).a);}),new T(function(){return E(E(_VS).b);})),_Z))),_Wd=_Vz,_We=_VA,_Wf=_VB,_Wg=_VC,_Wh=_VD,_Wi=_VE,_Wj=_VF,_Wk=_VG,_Wl=_VH,_Wm=_VI,_Wn=_VJ,_Wo=_VK,_Wp=_VL,_Wq=_VM,_Wr=_VN,_Ws=_VO,_Wt=_VP,_Wu=_VQ;_UO=_VR.b;_UP=_W0;_UQ=_W1;_UR=_W2;_US=_W3;_UT=_W4;_UU=_W5;_UV=_W6;_UW=_W7;_UX=_W8;_UY=_W9;_UZ=_Wa;_V0=_Wb;_V1=_Wc;_V2=_Wd;_V3=_We;_V4=_Wf;_V5=_Wg;_V6=_Wh;_V7=_Wi;_V8=_Wj;_V9=_Wk;_Va=_Wl;_Vb=_Wm;_Vc=_Wn;_Vd=_Wo;_Ve=_Wp;_Vf=_Wq;_Vg=_Wr;_Vh=_Ws;_Vi=_Wt;_Vj=_Wu;return __continue;}})(_UO,_UP,_UQ,_UR,_US,_UT,_UU,_UV,_UW,_UX,_UY,_UZ,_V0,_V1,_V2,_V3,_V4,_V5,_V6,_V7,_V8,_V9,_Va,_Vb,_Vc,_Vd,_Ve,_Vf,_Vg,_Vh,_Vi,_Vj));if(_Vk!=__continue){return _Vk;}}},_Wv=function(_Ww){return new F(function(){return _Q1("Event.hs:65:27-53|(x\' : y\' : _)");});},_Wx=new T(function(){return B(_Wv(_));}),_Wy=function(_Wz){return new F(function(){return _Q1("Event.hs:66:27-55|(chs : tps : _)");});},_WA=new T(function(){return B(_Wy(_));}),_WB=new T(function(){return B(_i8("Event.hs:(63,1)-(69,83)|function putCell"));}),_WC=function(_WD,_WE,_WF,_WG,_WH,_WI,_WJ,_WK,_WL,_WM,_WN,_WO,_WP,_WQ,_WR,_WS,_WT,_WU,_WV,_WW,_WX,_WY,_WZ,_X0){while(1){var _X1=B((function(_X2,_X3,_X4,_X5,_X6,_X7,_X8,_X9,_Xa,_Xb,_Xc,_Xd,_Xe,_Xf,_Xg,_Xh,_Xi,_Xj,_Xk,_Xl,_Xm,_Xn,_Xo,_Xp){var _Xq=E(_X2);if(!_Xq._){return {_:0,a:_X3,b:_X4,c:_X5,d:_X6,e:_X7,f:_X8,g:_X9,h:_Xa,i:_Xb,j:_Xc,k:_Xd,l:_Xe,m:_Xf,n:_Xg,o:_Xh,p:_Xi,q:_Xj,r:_Xk,s:_Xl,t:_Xm,u:_Xn,v:_Xo,w:_Xp};}else{var _Xr=E(_Xq.b);if(!_Xr._){return E(_WB);}else{var _Xs=E(_X3),_Xt=new T(function(){var _Xu=E(_Xq.a);if(!_Xu._){return E(_Wx);}else{var _Xv=E(_Xu.b);if(!_Xv._){return E(_Wx);}else{var _Xw=_Xv.a,_Xx=_Xv.b,_Xy=E(_Xu.a);if(E(_Xy)==44){return new T2(0,_Z,new T(function(){return E(B(_LD(44,_Xw,_Xx)).a);}));}else{var _Xz=B(_LD(44,_Xw,_Xx)),_XA=E(_Xz.b);if(!_XA._){return E(_Wx);}else{return new T2(0,new T2(1,_Xy,_Xz.a),_XA.a);}}}}}),_XB=B(_KL(B(_x8(_KJ,new T(function(){return E(E(_Xt).b);})))));if(!_XB._){return E(_K7);}else{if(!E(_XB.b)._){var _XC=new T(function(){var _XD=E(_Xr.a);if(!_XD._){return E(_WA);}else{var _XE=E(_XD.b);if(!_XE._){return E(_WA);}else{var _XF=_XE.a,_XG=_XE.b,_XH=E(_XD.a);if(E(_XH)==44){return new T2(0,_Z,new T(function(){return E(B(_LD(44,_XF,_XG)).a);}));}else{var _XI=B(_LD(44,_XF,_XG)),_XJ=E(_XI.b);if(!_XJ._){return E(_WA);}else{return new T2(0,new T2(1,_XH,_XI.a),_XJ.a);}}}}}),_XK=new T(function(){var _XL=B(_KL(B(_x8(_KJ,new T(function(){return E(E(_Xt).a);})))));if(!_XL._){return E(_K7);}else{if(!E(_XL.b)._){return E(_XL.a);}else{return E(_K8);}}},1),_XM=_X4,_XN=_X5,_XO=_X6,_XP=_X7,_XQ=_X8,_XR=_X9,_XS=_Xa,_XT=_Xb,_XU=_Xc,_XV=_Xd,_XW=_Xe,_XX=_Xf,_XY=_Xg,_XZ=_Xh,_Y0=_Xi,_Y1=_Xj,_Y2=_Xk,_Y3=_Xl,_Y4=_Xm,_Y5=_Xn,_Y6=_Xo,_Y7=_Xp;_WD=_Xr.b;_WE={_:0,a:E(_Xs.a),b:E(B(_PA(_XK,E(_XB.a),new T(function(){return B(_NV(E(_XC).a));}),new T(function(){return B(_O9(E(_XC).b));}),_Xs.b))),c:E(_Xs.c),d:_Xs.d,e:_Xs.e,f:_Xs.f,g:E(_Xs.g),h:_Xs.h,i:E(_Xs.i),j:E(_Xs.j),k:E(_Xs.k)};_WF=_XM;_WG=_XN;_WH=_XO;_WI=_XP;_WJ=_XQ;_WK=_XR;_WL=_XS;_WM=_XT;_WN=_XU;_WO=_XV;_WP=_XW;_WQ=_XX;_WR=_XY;_WS=_XZ;_WT=_Y0;_WU=_Y1;_WV=_Y2;_WW=_Y3;_WX=_Y4;_WY=_Y5;_WZ=_Y6;_X0=_Y7;return __continue;}else{return E(_K8);}}}}})(_WD,_WE,_WF,_WG,_WH,_WI,_WJ,_WK,_WL,_WM,_WN,_WO,_WP,_WQ,_WR,_WS,_WT,_WU,_WV,_WW,_WX,_WY,_WZ,_X0));if(_X1!=__continue){return _X1;}}},_Y8=function(_Y9,_Ya){while(1){var _Yb=E(_Ya);if(!_Yb._){return __Z;}else{var _Yc=_Yb.b,_Yd=E(_Y9);if(_Yd==1){return E(_Yc);}else{_Y9=_Yd-1|0;_Ya=_Yc;continue;}}}},_Ye=function(_Yf){var _Yg=E(_Yf);if(!_Yg._){return new T2(0,_Z,_Z);}else{var _Yh=E(_Yg.a),_Yi=new T(function(){var _Yj=B(_Ye(_Yg.b));return new T2(0,_Yj.a,_Yj.b);});return new T2(0,new T2(1,_Yh.a,new T(function(){return E(E(_Yi).a);})),new T2(1,_Yh.b,new T(function(){return E(E(_Yi).b);})));}},_Yk=32,_Yl=function(_Ym,_Yn,_Yo,_Yp){var _Yq=E(_Yp);if(!_Yq._){return __Z;}else{var _Yr=_Yq.b;if(!B(_4H(_3S,_Ym,_Yo))){var _Ys=new T(function(){return B(_Yl(new T(function(){return E(_Ym)+1|0;}),_Yn,_Yo,_Yr));});return new T2(1,_Yq.a,_Ys);}else{var _Yt=new T(function(){return B(_Yl(new T(function(){return E(_Ym)+1|0;}),_Yn,_Yo,_Yr));});return new T2(1,_Yn,_Yt);}}},_Yu=function(_Yv,_Yw){var _Yx=E(_Yw);if(!_Yx._){return __Z;}else{var _Yy=new T(function(){var _Yz=B(_Ye(_Yx.a)),_YA=_Yz.a,_YB=new T(function(){return B(_Ny(0,_Yv,_YA));});return B(_KX(B(_Yl(_vU,_Yk,_YB,_YA)),new T(function(){return B(_NF(0,_IJ,_YB,_Yz.b));},1)));});return new T2(1,_Yy,new T(function(){return B(_Yu(_Yv,_Yx.b));}));}},_YC=function(_YD,_YE){var _YF=E(_YE);return (_YF._==0)?__Z:new T2(1,_YD,new T(function(){return B(_YC(_YF.a,_YF.b));}));},_YG=new T(function(){return B(unCStr("init"));}),_YH=new T(function(){return B(_rf(_YG));}),_YI=function(_YJ,_YK){var _YL=function(_YM){var _YN=E(_YM);if(!_YN._){return __Z;}else{var _YO=new T(function(){return B(_x(new T2(1,_YJ,_Z),new T(function(){return B(_YL(_YN.b));},1)));},1);return new F(function(){return _x(_YN.a,_YO);});}},_YP=B(_YL(_YK));if(!_YP._){return E(_YH);}else{return new F(function(){return _YC(_YP.a,_YP.b);});}},_YQ=61,_YR=46,_YS=new T(function(){return B(_i8("Event.hs:(109,1)-(115,61)|function makeDecision"));}),_YT=new T(function(){return B(unCStr("sm"));}),_YU=new T(function(){return B(unCStr("rt"));}),_YV=new T(function(){return B(unCStr("rs"));}),_YW=new T(function(){return B(unCStr("rk"));}),_YX=new T(function(){return B(unCStr("if"));}),_YY=new T(function(){return B(unCStr("hm"));}),_YZ=new T(function(){return B(unCStr("cleq"));}),_Z0=new T(function(){return B(unCStr("da"));}),_Z1=new T(function(){return B(unCStr("ct"));}),_Z2=function(_Z3,_Z4,_Z5,_Z6,_Z7,_Z8,_Z9,_Za,_Zb,_Zc,_Zd,_Ze,_Zf,_Zg,_Zh,_Zi,_Zj,_Zk,_Zl,_Zm,_Zn,_Zo,_Zp,_Zq){var _Zr=function(_Zs,_Zt){var _Zu=function(_Zv){if(!B(_vi(_Zs,_Z1))){if(!B(_vi(_Zs,_Z0))){var _Zw=function(_Zx){if(!B(_vi(_Zs,_YZ))){var _Zy=function(_Zz){if(!B(_vi(_Zs,_wn))){if(!B(_vi(_Zs,_YY))){if(!B(_vi(_Zs,_YX))){if(!B(_vi(_Zs,_YW))){if(!B(_vi(_Zs,_YV))){if(!B(_vi(_Zs,_YU))){if(!B(_vi(_Zs,_YT))){return {_:0,a:E(_Z4),b:E(_Z5),c:E(_Z6),d:E(_Z7),e:E(_Z8),f:E(_Z9),g:E(_Za),h:E(_Zb),i:_Zc,j:_Zd,k:_Ze,l:_Zf,m:E(_Zg),n:_Zh,o:E(_Zi),p:E(_Zj),q:_Zk,r:E(_Zl),s:E(_Zm),t:_Zn,u:E(_Zo),v:E(_Zp),w:E(_Zq)};}else{var _ZA=E(_Zp);return {_:0,a:E(_Z4),b:E(_Z5),c:E(_Z6),d:E(_Z7),e:E(_Z8),f:E(_Z9),g:E(_Za),h:E(_Zb),i:_Zc,j:_Zd,k:_Ze,l:_Zf,m:E(_Zg),n:_Zh,o:E(_Zi),p:E(_Zj),q:_Zk,r:E(_Zl),s:E(_Zm),t:_Zn,u:E(_Zo),v:E({_:0,a:E(_ZA.a),b:E(_ZA.b),c:E(_ZA.c),d:E(_ZA.d),e:E(_ZA.e),f:E(_ZA.f),g:E(_ZA.g),h:E(_B4),i:E(_ZA.i)}),w:E(_Zq)};}}else{var _ZB=B(_Tq(_Zt,_Z4,_Z5,_Z6,_Z7,_Z8,_Z9,_Za,_Zb,_Zc,_Zd,_Ze,_Zf,_Zg,_Zh,_Zi,_Zj,_Zk,_Zl,_Zm,_Zn,_Zo,_Zp,_Zq));return {_:0,a:E(_ZB.a),b:E(_ZB.b),c:E(_ZB.c),d:E(_ZB.d),e:E(_ZB.e),f:E(_ZB.f),g:E(_ZB.g),h:E(_ZB.h),i:_ZB.i,j:_ZB.j,k:_ZB.k,l:_ZB.l,m:E(_ZB.m),n:_ZB.n,o:E(_ZB.o),p:E(_ZB.p),q:_ZB.q,r:E(_ZB.r),s:E(_ZB.s),t:_ZB.t,u:E(_ZB.u),v:E(_ZB.v),w:E(_ZB.w)};}}else{var _ZC=new T(function(){return B(_x(B(_H(0,600-B(_Tf(_Zl,0))|0,_Z)),new T(function(){if(_Zc>0){return B(_Y8(_Zc,_Z6));}else{return E(_Z6);}},1)));});if(0>=_Zc){var _ZD=E(_ZC);}else{var _ZE=function(_ZF,_ZG){var _ZH=E(_ZF);if(!_ZH._){return E(_ZC);}else{var _ZI=_ZH.a,_ZJ=E(_ZG);return (_ZJ==1)?new T2(1,_ZI,_ZC):new T2(1,_ZI,new T(function(){return B(_ZE(_ZH.b,_ZJ-1|0));}));}},_ZD=B(_ZE(_Z6,_Zc));}return {_:0,a:E(_Z4),b:E(_Z5),c:E(_ZD),d:E(_Z7),e:E(_Z8),f:E(_Z9),g:E(_Za),h:E(_Zb),i:_Zc,j:_Zd,k:_Ze,l:_Zf,m:E(_Zg),n:_Zh,o:E(_Zi),p:E(_Zj),q:_Zk,r:E(_Zl),s:E(_Zm),t:_Zn,u:E(_Zo),v:E(_Zp),w:E(_Zq)};}}else{return {_:0,a:E(_Z4),b:E(_Z5),c:E(_Z6),d:E(_Z7),e:E(_Z8),f:E(_Z9),g:E(_Za),h:E(_Zb),i:_Zc,j:_Zd,k:_Ze,l:_Zf,m:E(_Zg),n:_Zh,o:E(_Zt),p:E(_Zj),q:_Zk,r:E(_Zl),s:E(_Zm),t:_Zn,u:E(_Zo),v:E(_Zp),w:E(_Zq)};}}else{var _ZK=E(_Zt);if(!_ZK._){return {_:0,a:E(_Z4),b:E(_Z5),c:E(_Z6),d:E(_Z7),e:E(_Z8),f:E(_Z9),g:E(_Za),h:E(_Zb),i:_Zc,j:_Zd,k:_Ze,l:_Zf,m:E(_Zg),n:_Zh,o:E(_Zi),p:E(_Zj),q:_Zk,r:E(_Zl),s:E(_Zm),t:_Zn,u:E(_Zo),v:E(_Zp),w:E(_Zq)};}else{var _ZL=_ZK.a,_ZM=E(_ZK.b);if(!_ZM._){return E(_YS);}else{var _ZN=_ZM.a,_ZO=B(_T9(_Za)),_ZP=_ZO.a,_ZQ=_ZO.b,_ZR=function(_ZS){if(!B(_4H(_uF,_ZL,_ZP))){return {_:0,a:E(_Z4),b:E(_Z5),c:E(_Z6),d:E(_Z7),e:E(_Z8),f:E(_Z9),g:E(_Za),h:E(_Zb),i:_Zc,j:_Zd,k:_Ze,l:_Zf,m:E(_Zg),n:_Zh,o:E(_Zi),p:E(_Zj),q:_Zk,r:E(_Zl),s:E(_Zm),t:_Zn,u:E(_Zo),v:E(_Zp),w:E(_Zq)};}else{if(!B(_vi(_ZN,B(_aS(_ZQ,B(_Rt(_uF,_ZL,_ZP))))))){return {_:0,a:E(_Z4),b:E(_Z5),c:E(_Z6),d:E(_Z7),e:E(_Z8),f:E(_Z9),g:E(_Za),h:E(_Zb),i:_Zc,j:_Zd,k:_Ze,l:_Zf,m:E(_Zg),n:_Zh,o:E(_Zi),p:E(_Zj),q:_Zk,r:E(_Zl),s:E(_Zm),t:_Zn,u:E(_Zo),v:E(_Zp),w:E(_Zq)};}else{return new F(function(){return _Z2(_ZS,_Z4,_Z5,_Z6,_Z7,_Z8,_Z9,_Za,_Zb,_Zc,_Zd,_Ze,_Zf,_Zg,_Zh,_Zi,_Zj,_Zk,_Zl,_Zm,_Zn,_Zo,_Zp,_Zq);});}}},_ZT=B(_YI(_YR,_ZM.b));if(!_ZT._){return new F(function(){return _ZR(_Z);});}else{var _ZU=_ZT.a,_ZV=E(_ZT.b);if(!_ZV._){return new F(function(){return _ZR(new T2(1,_ZU,_Z));});}else{var _ZW=_ZV.a,_ZX=_ZV.b,_ZY=E(_ZU);if(E(_ZY)==47){if(!B(_4H(_uF,_ZL,_ZP))){return new F(function(){return _Z2(B(_LD(47,_ZW,_ZX)).a,_Z4,_Z5,_Z6,_Z7,_Z8,_Z9,_Za,_Zb,_Zc,_Zd,_Ze,_Zf,_Zg,_Zh,_Zi,_Zj,_Zk,_Zl,_Zm,_Zn,_Zo,_Zp,_Zq);});}else{if(!B(_vi(_ZN,B(_aS(_ZQ,B(_Rt(_uF,_ZL,_ZP))))))){return new F(function(){return _Z2(B(_LD(47,_ZW,_ZX)).a,_Z4,_Z5,_Z6,_Z7,_Z8,_Z9,_Za,_Zb,_Zc,_Zd,_Ze,_Zf,_Zg,_Zh,_Zi,_Zj,_Zk,_Zl,_Zm,_Zn,_Zo,_Zp,_Zq);});}else{return new F(function(){return _Z2(_Z,_Z4,_Z5,_Z6,_Z7,_Z8,_Z9,_Za,_Zb,_Zc,_Zd,_Ze,_Zf,_Zg,_Zh,_Zi,_Zj,_Zk,_Zl,_Zm,_Zn,_Zo,_Zp,_Zq);});}}}else{if(!B(_4H(_uF,_ZL,_ZP))){var _ZZ=E(B(_LD(47,_ZW,_ZX)).b);if(!_ZZ._){return {_:0,a:E(_Z4),b:E(_Z5),c:E(_Z6),d:E(_Z7),e:E(_Z8),f:E(_Z9),g:E(_Za),h:E(_Zb),i:_Zc,j:_Zd,k:_Ze,l:_Zf,m:E(_Zg),n:_Zh,o:E(_Zi),p:E(_Zj),q:_Zk,r:E(_Zl),s:E(_Zm),t:_Zn,u:E(_Zo),v:E(_Zp),w:E(_Zq)};}else{return new F(function(){return _Z2(_ZZ.a,_Z4,_Z5,_Z6,_Z7,_Z8,_Z9,_Za,_Zb,_Zc,_Zd,_Ze,_Zf,_Zg,_Zh,_Zi,_Zj,_Zk,_Zl,_Zm,_Zn,_Zo,_Zp,_Zq);});}}else{if(!B(_vi(_ZN,B(_aS(_ZQ,B(_Rt(_uF,_ZL,_ZP))))))){var _100=E(B(_LD(47,_ZW,_ZX)).b);if(!_100._){return {_:0,a:E(_Z4),b:E(_Z5),c:E(_Z6),d:E(_Z7),e:E(_Z8),f:E(_Z9),g:E(_Za),h:E(_Zb),i:_Zc,j:_Zd,k:_Ze,l:_Zf,m:E(_Zg),n:_Zh,o:E(_Zi),p:E(_Zj),q:_Zk,r:E(_Zl),s:E(_Zm),t:_Zn,u:E(_Zo),v:E(_Zp),w:E(_Zq)};}else{return new F(function(){return _Z2(_100.a,_Z4,_Z5,_Z6,_Z7,_Z8,_Z9,_Za,_Zb,_Zc,_Zd,_Ze,_Zf,_Zg,_Zh,_Zi,_Zj,_Zk,_Zl,_Zm,_Zn,_Zo,_Zp,_Zq);});}}else{return new F(function(){return _Z2(new T2(1,_ZY,new T(function(){return E(B(_LD(47,_ZW,_ZX)).a);})),_Z4,_Z5,_Z6,_Z7,_Z8,_Z9,_Za,_Zb,_Zc,_Zd,_Ze,_Zf,_Zg,_Zh,_Zi,_Zj,_Zk,_Zl,_Zm,_Zn,_Zo,_Zp,_Zq);});}}}}}}}}}else{var _101=E(_Zp);return {_:0,a:E(_Z4),b:E(_Z5),c:E(_Z6),d:E(_Z7),e:E(_Z8),f:E(_Z9),g:E(_Za),h:E(_Zb),i:_Zc,j:_Zd,k:_Ze,l:_Zf,m:E(_Zg),n:_Zh,o:E(_Zi),p:E(_Zj),q:_Zk,r:E(_Zl),s:E(_Zm),t:_Zn,u:E(_Zo),v:E({_:0,a:E(_101.a),b:E(_101.b),c:E(_101.c),d:E(_101.d),e:E(_101.e),f:E(_101.f),g:E(_101.g),h:E(_B3),i:E(_101.i)}),w:E(_Zq)};}}else{var _102=E(_Zp);return new F(function(){return _UN(_Zt,_Z4,_Z5,_Z6,_Z7,_Z8,_Z9,_Za,_Zb,_Zc,_Zd,_Ze,_Zf,_Z,_Zh,_Zi,_Zj,_Zk,_Zl,_Zm,_Zn,_Zo,_102.a,_102.b,_102.c,_102.d,_102.e,_102.f,_102.g,_102.h,_102.i,_Zq);});}},_103=E(_Zs);if(!_103._){return new F(function(){return _Zy(_);});}else{if(E(_103.a)==109){if(!E(_103.b)._){var _104=B(_LQ(_Zt,_Z4,_Z5,_Z6,_Z7,_Z8,_Z9,_Za,_Zb,_Zc,_Zd,_Ze,_Zf,_Zg,_Zh,_Zi,_Zj,_Zk,_Zl,_Zm,_Zn,_Zo,_Zp,_Zq));return {_:0,a:E(_104.a),b:E(_104.b),c:E(_104.c),d:E(_104.d),e:E(_104.e),f:E(_104.f),g:E(_104.g),h:E(_104.h),i:_104.i,j:_104.j,k:_104.k,l:_104.l,m:E(_104.m),n:_104.n,o:E(_104.o),p:E(_104.p),q:_104.q,r:E(_104.r),s:E(_104.s),t:_104.t,u:E(_104.u),v:E(_104.v),w:E(_104.w)};}else{return new F(function(){return _Zy(_);});}}else{return new F(function(){return _Zy(_);});}}}else{var _105=E(_Z4);return {_:0,a:E({_:0,a:E(_105.a),b:E(B(_Yu(_YQ,_105.b))),c:E(_105.c),d:_105.d,e:_105.e,f:_105.f,g:E(_105.g),h:_105.h,i:E(_105.i),j:E(_105.j),k:E(_105.k)}),b:E(_Z5),c:E(_Z6),d:E(_Z7),e:E(_Z8),f:E(_Z9),g:E(_Za),h:E(_Zb),i:_Zc,j:_Zd,k:_Ze,l:_Zf,m:E(_Zg),n:_Zh,o:E(_Zi),p:E(_Zj),q:_Zk,r:E(_Zl),s:E(_Zm),t:_Zn,u:E(_Zo),v:E(_Zp),w:E(_Zq)};}},_106=E(_Zs);if(!_106._){return new F(function(){return _Zw(_);});}else{var _107=_106.b;switch(E(_106.a)){case 99:if(!E(_107)._){var _108=B(_Q6(_Zt,_Z4,_Z5,_Z6,_Z7,_Z8,_Z9,_Za,_Zb,_Zc,_Zd,_Ze,_Zf,_Zg,_Zh,_Zi,_Zj,_Zk,_Zl,_Zm,_Zn,_Zo,_Zp,_Zq));return {_:0,a:E(_108.a),b:E(_108.b),c:E(_108.c),d:E(_108.d),e:E(_108.e),f:E(_108.f),g:E(_108.g),h:E(_108.h),i:_108.i,j:_108.j,k:_108.k,l:_108.l,m:E(_108.m),n:_108.n,o:E(_108.o),p:E(_108.p),q:_108.q,r:E(_108.r),s:E(_108.s),t:_108.t,u:E(_108.u),v:E(_108.v),w:E(_108.w)};}else{return new F(function(){return _Zw(_);});}break;case 112:if(!E(_107)._){var _109=B(_WC(_Zt,_Z4,_Z5,_Z6,_Z7,_Z8,_Z9,_Za,_Zb,_Zc,_Zd,_Ze,_Zf,_Zg,_Zh,_Zi,_Zj,_Zk,_Zl,_Zm,_Zn,_Zo,_Zp,_Zq));return {_:0,a:E(_109.a),b:E(_109.b),c:E(_109.c),d:E(_109.d),e:E(_109.e),f:E(_109.f),g:E(_109.g),h:E(_109.h),i:_109.i,j:_109.j,k:_109.k,l:_109.l,m:E(_109.m),n:_109.n,o:E(_109.o),p:E(_109.p),q:_109.q,r:E(_109.r),s:E(_109.s),t:_109.t,u:E(_109.u),v:E(_109.v),w:E(_109.w)};}else{return new F(function(){return _Zw(_);});}break;default:return new F(function(){return _Zw(_);});}}}else{return {_:0,a:E(_Z4),b:E(_Z5),c:E(_Z6),d:E(_Z7),e:E(_Z),f:E(_Z9),g:E(_Za),h:E(_Zb),i:_Zc,j:_Zd,k:_Ze,l:_Zf,m:E(_Zg),n:_Zh,o:E(_Zi),p:E(_Zj),q:_Zk,r:E(_Zl),s:E(_Zm),t:_Zn,u:E(_Zo),v:E(_Zp),w:E(_Zq)};}}else{var _10a=B(_Ob(_Zt,_Z4,_Z5,_Z6,_Z7,_Z8,_Z9,_Za,_Zb,_Zc,_Zd,_Ze,_Zf,_Zg,_Zh,_Zi,_Zj,_Zk,_Zl,_Zm,_Zn,_Zo,_Zp,_Zq));return {_:0,a:E(_10a.a),b:E(_10a.b),c:E(_10a.c),d:E(_10a.d),e:E(_10a.e),f:E(_10a.f),g:E(_10a.g),h:E(_10a.h),i:_10a.i,j:_10a.j,k:_10a.k,l:_10a.l,m:E(_10a.m),n:_10a.n,o:E(_10a.o),p:E(_10a.p),q:_10a.q,r:E(_10a.r),s:E(_10a.s),t:_10a.t,u:E(_10a.u),v:E(_10a.v),w:E(_10a.w)};}},_10b=E(_Zs);if(!_10b._){return new F(function(){return _Zu(_);});}else{var _10c=_10b.b;switch(E(_10b.a)){case 100:if(!E(_10c)._){var _10d=B(_RT(_Zt,_Z4,_Z5,_Z6,_Z7,_Z8,_Z9,_Za,_Zb,_Zc,_Zd,_Ze,_Zf,_Zg,_Zh,_Zi,_Zj,_Zk,_Zl,_Zm,_Zn,_Zo,_Zp,_Zq));return {_:0,a:E(_10d.a),b:E(_10d.b),c:E(_10d.c),d:E(_10d.d),e:E(_10d.e),f:E(_10d.f),g:E(_10d.g),h:E(_10d.h),i:_10d.i,j:_10d.j,k:_10d.k,l:_10d.l,m:E(_10d.m),n:_10d.n,o:E(_10d.o),p:E(_10d.p),q:_10d.q,r:E(_10d.r),s:E(_10d.s),t:_10d.t,u:E(_10d.u),v:E(_10d.v),w:E(_10d.w)};}else{return new F(function(){return _Zu(_);});}break;case 101:if(!E(_10c)._){var _10e=B(_uI(_Zt,_Z4,_Z5,_Z6,_Z7,_Z8,_Z9,_Za,_Zb,_Zc,_Zd,_Ze,_Zf,_Zg,_Zh,_Zi,_Zj,_Zk,_Zl,_Zm,_Zn,_Zo,_Zp,_Zq));return {_:0,a:E(_10e.a),b:E(_10e.b),c:E(_10e.c),d:E(_10e.d),e:E(_10e.e),f:E(_10e.f),g:E(_10e.g),h:E(_10e.h),i:_10e.i,j:_10e.j,k:_10e.k,l:_10e.l,m:E(_10e.m),n:_10e.n,o:E(_10e.o),p:E(_10e.p),q:_10e.q,r:E(_10e.r),s:E(_10e.s),t:_10e.t,u:E(_10e.u),v:E(_10e.v),w:E(_10e.w)};}else{return new F(function(){return _Zu(_);});}break;default:return new F(function(){return _Zu(_);});}}},_10f=E(_Z3);if(!_10f._){return new F(function(){return _Zr(_Z,_Z);});}else{var _10g=_10f.a,_10h=E(_10f.b);if(!_10h._){return new F(function(){return _Zr(new T2(1,_10g,_Z),_Z);});}else{var _10i=E(_10g),_10j=new T(function(){var _10k=B(_LD(46,_10h.a,_10h.b));return new T2(0,_10k.a,_10k.b);});if(E(_10i)==46){return new F(function(){return _Zr(_Z,new T2(1,new T(function(){return E(E(_10j).a);}),new T(function(){return E(E(_10j).b);})));});}else{return new F(function(){return _Zr(new T2(1,_10i,new T(function(){return E(E(_10j).a);})),new T(function(){return E(E(_10j).b);}));});}}}},_10l=new T(function(){return B(unCStr("last"));}),_10m=new T(function(){return B(_rf(_10l));}),_10n=32,_10o=0,_10p=65306,_10q=125,_10r=new T1(0,1),_10s=function(_10t,_10u,_10v,_10w,_10x){var _10y=new T(function(){return E(_10x).i;}),_10z=new T(function(){var _10A=E(_10u)/28,_10B=_10A&4294967295;if(_10A>=_10B){return _10B-1|0;}else{return (_10B-1|0)-1|0;}}),_10C=new T(function(){if(!E(E(_10w).h)){return E(_n9);}else{return 2+(E(E(E(_10x).b).b)+2|0)|0;}}),_10D=new T(function(){if(!E(_10y)){return new T2(0,_10z,_10C);}else{return E(E(_10x).h);}}),_10E=new T(function(){return E(E(_10x).c);}),_10F=new T(function(){var _10G=E(_10y)+1|0;if(0>=_10G){return E(_10n);}else{var _10H=B(_uf(_10G,_10E));if(!_10H._){return E(_10n);}else{return B(_sB(_10H.a,_10H.b,_10m));}}}),_10I=new T(function(){var _10J=E(_10F);switch(E(_10J)){case 125:return E(_10n);break;case 12289:return E(_10n);break;case 12290:return E(_10n);break;default:return E(_10J);}}),_10K=new T(function(){if(E(_10I)==10){return true;}else{return false;}}),_10L=new T(function(){return E(E(_10D).b);}),_10M=new T(function(){if(!E(_10K)){if(E(_10I)==12300){return E(_n8);}else{return E(_10x).j;}}else{return E(_10o);}}),_10N=new T(function(){return E(E(_10D).a);}),_10O=new T(function(){if(E(_10I)==65306){return true;}else{return false;}}),_10P=new T(function(){if(!E(_10O)){if(!E(_10K)){var _10Q=E(_10L);if((_10Q+1)*24<=E(_10v)-10){return new T2(0,_10N,_10Q+1|0);}else{return new T2(0,new T(function(){return E(_10N)-1|0;}),_10C);}}else{return new T2(0,new T(function(){return E(_10N)-1|0;}),_10C);}}else{return new T2(0,_10N,_10L);}}),_10R=new T(function(){if(E(E(_10P).a)==1){if(E(_10N)==1){return false;}else{return true;}}else{return false;}}),_10S=new T(function(){return B(_qu(_10E,0))-1|0;}),_10T=new T(function(){if(!E(_10O)){return __Z;}else{return B(_ux(_10p,E(_10y),_10E));}}),_10U=new T(function(){if(E(_10I)==123){return true;}else{return false;}}),_10V=new T(function(){if(!E(_10U)){return __Z;}else{return B(_ux(_10q,E(_10y),_10E));}}),_10W=new T(function(){if(!E(_10O)){if(!E(_10U)){return E(_n8);}else{return B(_qu(_10V,0))+2|0;}}else{return B(_qu(_10T,0))+2|0;}}),_10X=new T(function(){var _10Y=E(_10x),_10Z=_10Y.a,_110=_10Y.b,_111=_10Y.c,_112=_10Y.d,_113=_10Y.e,_114=_10Y.f,_115=_10Y.g,_116=_10Y.h,_117=_10Y.j,_118=_10Y.k,_119=_10Y.l,_11a=_10Y.m,_11b=_10Y.n,_11c=_10Y.o,_11d=_10Y.p,_11e=_10Y.q,_11f=_10Y.r,_11g=_10Y.s,_11h=_10Y.t,_11i=_10Y.u,_11j=_10Y.w,_11k=E(_10y),_11l=E(_10W);if((_11k+_11l|0)<=E(_10S)){var _11m=E(_10w),_11n=_11m.a,_11o=_11m.b,_11p=_11m.c,_11q=_11m.e,_11r=_11m.f,_11s=_11m.g,_11t=_11m.h,_11u=_11m.i;if(E(_10F)==12290){var _11v=true;}else{var _11v=false;}if(!E(_10U)){return {_:0,a:E(_10Z),b:E(_110),c:E(_111),d:E(_112),e:E(_113),f:E(_114),g:E(_115),h:E(_116),i:_11k+_11l|0,j:_117,k:_118,l:_119,m:E(_11a),n:_11b,o:E(_11c),p:E(_11d),q:_11e,r:E(_11f),s:E(_11g),t:_11h,u:E(_11i),v:E({_:0,a:E(_11n),b:E(_11o),c:E(_11p),d:E(_11v),e:E(_11q),f:E(_11r),g:E(_11s),h:E(_11t),i:E(_11u)}),w:E(_11j)};}else{return B(_Z2(_10V,_10Z,_110,_111,_112,_113,_114,_115,_116,_11k+_11l|0,_117,_118,_119,_11a,_11b,_11c,_11d,_11e,_11f,_11g,_11h,_11i,{_:0,a:E(_11n),b:E(_11o),c:E(_11p),d:E(_11v),e:E(_11q),f:E(_11r),g:E(_11s),h:E(_11t),i:E(_11u)},_11j));}}else{var _11w=E(_10w),_11x=_11w.a,_11y=_11w.b,_11z=_11w.c,_11A=_11w.e,_11B=_11w.f,_11C=_11w.g,_11D=_11w.h,_11E=_11w.i;if(E(_10F)==12290){var _11F=true;}else{var _11F=false;}if(!E(_10U)){return {_:0,a:E(_10Z),b:E(_110),c:E(_111),d:E(_112),e:E(_113),f:E(_114),g:E(_115),h:E(_116),i:0,j:_117,k:_118,l:_119,m:E(_11a),n:_11b,o:E(_11c),p:E(_11d),q:_11e,r:E(_11f),s:E(_11g),t:_11h,u:E(_11i),v:E({_:0,a:E(_11x),b:E(_11y),c:E(_11z),d:E(_11F),e:E(_11A),f:E(_11B),g:E(_11C),h:E(_11D),i:E(_11E)}),w:E(_11j)};}else{return B(_Z2(_10V,_10Z,_110,_111,_112,_113,_114,_115,_116,0,_117,_118,_119,_11a,_11b,_11c,_11d,_11e,_11f,_11g,_11h,_11i,{_:0,a:E(_11x),b:E(_11y),c:E(_11z),d:E(_11F),e:E(_11A),f:E(_11B),g:E(_11C),h:E(_11D),i:E(_11E)},_11j));}}}),_11G=new T(function(){return E(E(_10X).v);}),_11H=new T(function(){if(!E(_10y)){return E(_10o);}else{return E(_10X).k;}}),_11I=new T(function(){var _11J=B(_sv(B(_st(_10t)))),_11K=new T(function(){var _11L=B(_tW(_10t,E(_10u)/16)),_11M=_11L.a;if(E(_11L.b)>=0){return E(_11M);}else{return B(A3(_t8,_11J,_11M,new T(function(){return B(A2(_lf,_11J,_10r));})));}});return B(A3(_t8,_11J,_11K,new T(function(){return B(A2(_lf,_11J,_lo));})));});return {_:0,a:_10I,b:_10N,c:_10L,d:new T(function(){if(E(_10C)!=E(_10L)){return E(_10N);}else{return E(_10N)+1|0;}}),e:new T(function(){var _11N=E(_10L);if(E(_10C)!=_11N){return _11N-1|0;}else{var _11O=(E(_10v)-10)/24,_11P=_11O&4294967295;if(_11O>=_11P){return _11P;}else{return _11P-1|0;}}}),f:_10C,g:_10y,h:_10E,i:new T(function(){return B(_aS(_n5,E(_10M)));}),j:_10T,k:_10z,l:_11I,m:_11H,n:_na,o:_10O,p:_10U,q:_10R,r:_11G,s:_10X,t:new T(function(){var _11Q=E(_10X),_11R=_11Q.a,_11S=_11Q.b,_11T=_11Q.c,_11U=_11Q.d,_11V=_11Q.e,_11W=_11Q.f,_11X=_11Q.g,_11Y=_11Q.i,_11Z=_11Q.l,_120=_11Q.m,_121=_11Q.n,_122=_11Q.o,_123=_11Q.p,_124=_11Q.q,_125=_11Q.r,_126=_11Q.s,_127=_11Q.t,_128=_11Q.u,_129=_11Q.w;if(!E(_10R)){var _12a=E(_10P);}else{var _12a=new T2(0,_10N,_10C);}var _12b=E(_10M);if(!E(_10R)){var _12c=E(_11G);return {_:0,a:E(_11R),b:E(_11S),c:E(_11T),d:E(_11U),e:E(_11V),f:E(_11W),g:E(_11X),h:E(_12a),i:_11Y,j:_12b,k:E(_11H),l:_11Z,m:E(_120),n:_121,o:E(_122),p:E(_123),q:_124,r:E(_125),s:E(_126),t:_127,u:E(_128),v:E({_:0,a:E(_12c.a),b:E(_12c.b),c:(E(_10y)+E(_10W)|0)<=E(_10S),d:E(_12c.d),e:E(_12c.e),f:E(_12c.f),g:E(_12c.g),h:E(_12c.h),i:E(_12c.i)}),w:E(_129)};}else{var _12d=E(_11G);return {_:0,a:E(_11R),b:E(_11S),c:E(_11T),d:E(_11U),e:E(_11V),f:E(_11W),g:E(_11X),h:E(_12a),i:_11Y,j:_12b,k:E(_11H)+1|0,l:_11Z,m:E(_120),n:_121,o:E(_122),p:E(_123),q:_124,r:E(_125),s:E(_126),t:_127,u:E(_128),v:E({_:0,a:E(_12d.a),b:E(_12d.b),c:(E(_10y)+E(_10W)|0)<=E(_10S),d:E(_12d.d),e:E(_12d.e),f:E(_12d.f),g:E(_12d.g),h:E(_12d.h),i:E(_12d.i)}),w:E(_129)};}})};},_12e=function(_12f){var _12g=E(_12f);if(!_12g._){return new T2(0,_Z,_Z);}else{var _12h=E(_12g.a),_12i=new T(function(){var _12j=B(_12e(_12g.b));return new T2(0,_12j.a,_12j.b);});return new T2(0,new T2(1,_12h.a,new T(function(){return E(E(_12i).a);})),new T2(1,_12h.b,new T(function(){return E(E(_12i).b);})));}},_12k=42,_12l=32,_12m=function(_12n,_12o,_12p){var _12q=E(_12n);if(!_12q._){return __Z;}else{var _12r=_12q.a,_12s=_12q.b;if(_12o!=_12p){var _12t=E(_12r);return (_12t._==0)?E(_ri):(E(_12t.a)==42)?new T2(1,new T2(1,_12l,_12t.b),new T(function(){return B(_12m(_12s,_12o,_12p+1|0));})):new T2(1,new T2(1,_12l,_12t),new T(function(){return B(_12m(_12s,_12o,_12p+1|0));}));}else{var _12u=E(_12r);return (_12u._==0)?E(_ri):(E(_12u.a)==42)?new T2(1,new T2(1,_12l,_12u),new T(function(){return B(_12m(_12s,_12o,_12p+1|0));})):new T2(1,new T2(1,_12k,_12u),new T(function(){return B(_12m(_12s,_12o,_12p+1|0));}));}}},_12v=new T(function(){return B(unCStr("\n\n"));}),_12w=function(_12x){var _12y=E(_12x);if(!_12y._){return __Z;}else{var _12z=new T(function(){return B(_x(_12v,new T(function(){return B(_12w(_12y.b));},1)));},1);return new F(function(){return _x(_12y.a,_12z);});}},_12A=function(_12B,_12C,_12D){var _12E=new T(function(){var _12F=new T(function(){var _12G=E(_12C);if(!_12G._){return B(_12w(_Z));}else{var _12H=_12G.a,_12I=_12G.b,_12J=E(_12D);if(!_12J){var _12K=E(_12H);if(!_12K._){return E(_ri);}else{if(E(_12K.a)==42){return B(_12w(new T2(1,new T2(1,_12l,_12K),new T(function(){return B(_12m(_12I,0,1));}))));}else{return B(_12w(new T2(1,new T2(1,_12k,_12K),new T(function(){return B(_12m(_12I,0,1));}))));}}}else{var _12L=E(_12H);if(!_12L._){return E(_ri);}else{if(E(_12L.a)==42){return B(_12w(new T2(1,new T2(1,_12l,_12L.b),new T(function(){return B(_12m(_12I,_12J,1));}))));}else{return B(_12w(new T2(1,new T2(1,_12l,_12L),new T(function(){return B(_12m(_12I,_12J,1));}))));}}}}});return B(unAppCStr("\n\n",_12F));},1);return new F(function(){return _x(_12B,_12E);});},_12M=function(_12N){return E(E(_12N).c);},_12O=function(_12P,_12Q,_12R,_12S,_12T,_12U,_12V,_12W,_12X){var _12Y=new T(function(){if(!E(_12Q)){return E(_12R);}else{return false;}}),_12Z=new T(function(){if(!E(_12Q)){return false;}else{return E(E(_12W).g);}}),_130=new T(function(){if(!E(_12Z)){if(!E(_12Y)){return B(A2(_lf,_12P,_ln));}else{return B(A3(_qB,_12P,new T(function(){return B(A3(_qB,_12P,_12U,_12V));}),new T(function(){return B(A2(_lf,_12P,_10r));})));}}else{return B(A3(_qB,_12P,_12U,_12V));}}),_131=new T(function(){if(!E(_12Z)){if(!E(_12Y)){return __Z;}else{var _132=E(_12S)+1|0;if(0>=_132){return __Z;}else{return B(_uf(_132,_12T));}}}else{return B(_12A(B(_12M(_12X)),new T(function(){return E(B(_12e(E(_12X).m)).a);},1),new T(function(){return E(_12X).n;},1)));}});return new T4(0,_12Z,_12Y,_131,_130);},_133=function(_134,_135,_136){var _137=E(_135),_138=E(_136),_139=new T(function(){var _13a=B(_lb(_134)),_13b=B(_133(_134,_138,B(A3(_t8,_13a,new T(function(){return B(A3(_qB,_13a,_138,_138));}),_137))));return new T2(1,_13b.a,_13b.b);});return new T2(0,_137,_139);},_13c=1,_13d=new T(function(){var _13e=B(_133(_kc,_lN,_13c));return new T2(1,_13e.a,_13e.b);}),_13f=function(_13g,_13h,_13i,_13j,_13k,_13l,_13m,_13n,_13o,_13p,_13q,_13r,_13s,_13t,_13u,_13v,_13w,_13x,_13y,_13z,_13A,_13B,_13C,_13D,_13E,_13F,_13G,_13H,_13I,_13J,_13K,_13L,_13M,_13N,_13O,_13P,_13Q,_){var _13R={_:0,a:E(_13H),b:E(_13I),c:E(_13J),d:E(_13K),e:E(_13L),f:E(_13M),g:E(_13N),h:E(_13O),i:E(_13P)};if(!E(_13J)){return {_:0,a:E(_13k),b:E(new T2(0,_13l,_13m)),c:E(_13n),d:E(_13o),e:E(_13p),f:E(_13q),g:E(_13r),h:E(new T2(0,_13s,_13t)),i:_13u,j:_13v,k:_13w,l:_13x,m:E(_13y),n:_13z,o:E(_13A),p:E(_13B),q:_13C,r:E(_13D),s:E(_13E),t:_13F,u:E(_13G),v:E(_13R),w:E(_13Q)};}else{if(!E(_13K)){var _13S=B(_10s(_fT,_13h,_13i,_13R,{_:0,a:E(_13k),b:E(new T2(0,_13l,_13m)),c:E(_13n),d:E(_13o),e:E(_13p),f:E(_13q),g:E(_13r),h:E(new T2(0,_13s,_13t)),i:_13u,j:_13v,k:_13w,l:_13x,m:E(_13y),n:_13z,o:E(_13A),p:E(_13B),q:_13C,r:E(_13D),s:E(_13E),t:_13F,u:E(_13G),v:E(_13R),w:E(_13Q)})),_13T=_13S.d,_13U=_13S.e,_13V=_13S.f,_13W=_13S.i,_13X=_13S.n,_13Y=_13S.p,_13Z=_13S.q,_140=_13S.s,_141=_13S.t;if(!E(_13S.o)){var _142=B(_12O(_fo,_13Y,_13Z,_13S.g,_13S.h,_13S.k,_13S.m,_13S.r,_140)),_143=_142.c,_144=_142.d,_145=function(_){var _146=function(_){if(!E(_13Y)){if(!E(_13Z)){var _147=B(_mC(E(_13g).a,_13W,_n6,_lN,_13S.b,_13S.c,_13S.a,_));return _141;}else{return _141;}}else{return _141;}};if(!E(_142.b)){return new F(function(){return _146(_);});}else{var _148=E(_13g),_149=_148.a,_14a=_148.b,_14b=B(_sa(_149,_14a,_13h,_13S.l,_13j,_140,_)),_14c=B(_pp(_149,_14a,_13i,0,_13V,_144,_13V,_143,_));return new F(function(){return _146(_);});}};if(!E(_142.a)){return new F(function(){return _145(_);});}else{var _14d=B(_nb(_13g,_13i,0,_13V,_144,_13V,_143,_));return new F(function(){return _145(_);});}}else{var _14e=E(_13S.j);if(!_14e._){return _141;}else{var _14f=E(_13d);if(!_14f._){return _141;}else{var _14g=E(_13g).a,_14h=B(_mC(_14g,_13W,_13X,_14f.a,_13T,_13U,_14e.a,_)),_14i=function(_14j,_14k,_){while(1){var _14l=E(_14j);if(!_14l._){return _kF;}else{var _14m=E(_14k);if(!_14m._){return _kF;}else{var _14n=B(_mC(_14g,_13W,_13X,_14m.a,_13T,_13U,_14l.a,_));_14j=_14l.b;_14k=_14m.b;continue;}}}},_14o=B(_14i(_14e.b,_14f.b,_));return _141;}}}}else{return {_:0,a:E(_13k),b:E(new T2(0,_13l,_13m)),c:E(_13n),d:E(_13o),e:E(_13p),f:E(_13q),g:E(_13r),h:E(new T2(0,_13s,_13t)),i:_13u,j:_13v,k:_13w,l:_13x,m:E(_13y),n:_13z,o:E(_13A),p:E(_13B),q:_13C,r:E(_13D),s:E(_13E),t:_13F,u:E(_13G),v:E(_13R),w:E(_13Q)};}}},_14p=function(_14q,_14r,_14s,_14t,_14u,_14v,_14w,_14x,_14y,_14z,_14A,_14B,_14C,_14D,_14E,_14F,_14G,_14H,_14I,_14J,_14K,_14L,_14M,_14N,_14O,_14P,_14Q,_14R,_14S,_14T,_14U,_14V,_14W,_14X,_14Y,_14Z,_150,_){while(1){var _151=B(_13f(_14q,_14r,_14s,_14t,_14u,_14v,_14w,_14x,_14y,_14z,_14A,_14B,_14C,_14D,_14E,_14F,_14G,_14H,_14I,_14J,_14K,_14L,_14M,_14N,_14O,_14P,_14Q,_14R,_14S,_14T,_14U,_14V,_14W,_14X,_14Y,_14Z,_150,_)),_152=E(_151),_153=_152.a,_154=_152.c,_155=_152.d,_156=_152.e,_157=_152.f,_158=_152.g,_159=_152.i,_15a=_152.j,_15b=_152.k,_15c=_152.l,_15d=_152.m,_15e=_152.n,_15f=_152.o,_15g=_152.p,_15h=_152.q,_15i=_152.r,_15j=_152.s,_15k=_152.t,_15l=_152.u,_15m=_152.w,_15n=E(_152.v),_15o=_15n.a,_15p=_15n.b,_15q=_15n.c,_15r=_15n.e,_15s=_15n.g,_15t=_15n.h,_15u=_15n.i,_15v=E(_152.b),_15w=E(_152.h);if(!E(_15n.d)){if(!E(_14T)){return {_:0,a:E(_153),b:E(_15v),c:E(_154),d:E(_155),e:E(_156),f:E(_157),g:E(_158),h:E(_15w),i:_159,j:_15a,k:_15b,l:_15c,m:E(_15d),n:_15e,o:E(_15f),p:E(_15g),q:_15h,r:E(_15i),s:E(_15j),t:_15k,u:E(_15l),v:E({_:0,a:E(_15o),b:E(_15p),c:E(_15q),d:E(_B3),e:E(_15r),f:E(_B3),g:E(_15s),h:E(_15t),i:E(_15u)}),w:E(_15m)};}else{_14u=_153;_14v=_15v.a;_14w=_15v.b;_14x=_154;_14y=_155;_14z=_156;_14A=_157;_14B=_158;_14C=_15w.a;_14D=_15w.b;_14E=_159;_14F=_15a;_14G=_15b;_14H=_15c;_14I=_15d;_14J=_15e;_14K=_15f;_14L=_15g;_14M=_15h;_14N=_15i;_14O=_15j;_14P=_15k;_14Q=_15l;_14R=_15o;_14S=_15p;_14T=_15q;_14U=_B3;_14V=_15r;_14W=_15n.f;_14X=_15s;_14Y=_15t;_14Z=_15u;_150=_15m;continue;}}else{return {_:0,a:E(_153),b:E(_15v),c:E(_154),d:E(_155),e:E(_156),f:E(_157),g:E(_158),h:E(_15w),i:_159,j:_15a,k:_15b,l:_15c,m:E(_15d),n:_15e,o:E(_15f),p:E(_15g),q:_15h,r:E(_15i),s:E(_15j),t:_15k,u:E(_15l),v:E({_:0,a:E(_15o),b:E(_15p),c:E(_15q),d:E(_B4),e:E(_15r),f:E(_B3),g:E(_15s),h:E(_15t),i:E(_15u)}),w:E(_15m)};}}},_15x=function(_15y,_15z,_15A,_15B,_15C,_15D,_15E,_15F,_15G,_15H,_15I,_15J,_15K,_15L,_15M,_15N,_15O,_15P,_15Q,_15R,_15S,_15T,_15U,_15V,_15W,_15X,_15Y,_15Z,_160,_161,_162,_163,_164,_165,_166,_167,_){var _168=B(_13f(_15y,_15z,_15A,_15B,_15C,_15D,_15E,_15F,_15G,_15H,_15I,_15J,_15K,_15L,_15M,_15N,_15O,_15P,_15Q,_15R,_15S,_15T,_15U,_15V,_15W,_15X,_15Y,_15Z,_160,_B4,_161,_162,_163,_164,_165,_166,_167,_)),_169=E(_168),_16a=_169.a,_16b=_169.c,_16c=_169.d,_16d=_169.e,_16e=_169.f,_16f=_169.g,_16g=_169.i,_16h=_169.j,_16i=_169.k,_16j=_169.l,_16k=_169.m,_16l=_169.n,_16m=_169.o,_16n=_169.p,_16o=_169.q,_16p=_169.r,_16q=_169.s,_16r=_169.t,_16s=_169.u,_16t=_169.w,_16u=E(_169.v),_16v=_16u.a,_16w=_16u.b,_16x=_16u.c,_16y=_16u.e,_16z=_16u.g,_16A=_16u.h,_16B=_16u.i,_16C=E(_169.b),_16D=E(_169.h);if(!E(_16u.d)){return new F(function(){return _14p(_15y,_15z,_15A,_15B,_16a,_16C.a,_16C.b,_16b,_16c,_16d,_16e,_16f,_16D.a,_16D.b,_16g,_16h,_16i,_16j,_16k,_16l,_16m,_16n,_16o,_16p,_16q,_16r,_16s,_16v,_16w,_16x,_B3,_16y,_16u.f,_16z,_16A,_16B,_16t,_);});}else{return {_:0,a:E(_16a),b:E(_16C),c:E(_16b),d:E(_16c),e:E(_16d),f:E(_16e),g:E(_16f),h:E(_16D),i:_16g,j:_16h,k:_16i,l:_16j,m:E(_16k),n:_16l,o:E(_16m),p:E(_16n),q:_16o,r:E(_16p),s:E(_16q),t:_16r,u:E(_16s),v:E({_:0,a:E(_16v),b:E(_16w),c:E(_16x),d:E(_B4),e:E(_16y),f:E(_B3),g:E(_16z),h:E(_16A),i:E(_16B)}),w:E(_16t)};}},_16E=function(_16F){var _16G=E(_16F);if(!_16G._){return __Z;}else{var _16H=E(_16G.b);return (_16H._==0)?__Z:new T2(1,new T2(0,_16G.a,_16H.a),new T(function(){return B(_16E(_16H.b));}));}},_16I=function(_16J,_16K,_16L){return new T2(1,new T2(0,_16J,_16K),new T(function(){return B(_16E(_16L));}));},_16M=function(_16N,_16O){var _16P=E(_16O);return (_16P._==0)?__Z:new T2(1,new T2(0,_16N,_16P.a),new T(function(){return B(_16E(_16P.b));}));},_16Q="Invalid JSON!",_16R=new T1(0,_16Q),_16S="No such value",_16T=new T1(0,_16S),_16U=new T(function(){return eval("(function(k) {return localStorage.getItem(k);})");}),_16V=function(_16W){return E(E(_16W).c);},_16X=function(_16Y,_16Z,_){var _170=__app1(E(_16U),_16Z),_171=__eq(_170,E(_3h));if(!E(_171)){var _172=__isUndef(_170);return (E(_172)==0)?new T(function(){var _173=String(_170),_174=jsParseJSON(_173);if(!_174._){return E(_16R);}else{return B(A2(_16V,_16Y,_174.a));}}):_16T;}else{return _16T;}},_175=new T1(0,0),_176=function(_177,_178){while(1){var _179=E(_177);if(!_179._){var _17a=_179.a,_17b=E(_178);if(!_17b._){return new T1(0,(_17a>>>0|_17b.a>>>0)>>>0&4294967295);}else{_177=new T1(1,I_fromInt(_17a));_178=_17b;continue;}}else{var _17c=E(_178);if(!_17c._){_177=_179;_178=new T1(1,I_fromInt(_17c.a));continue;}else{return new T1(1,I_or(_179.a,_17c.a));}}}},_17d=function(_17e){var _17f=E(_17e);if(!_17f._){return E(_175);}else{return new F(function(){return _176(new T1(0,E(_17f.a)),B(_gP(B(_17d(_17f.b)),31)));});}},_17g=function(_17h,_17i){if(!E(_17h)){return new F(function(){return _ju(B(_17d(_17i)));});}else{return new F(function(){return _17d(_17i);});}},_17j=1420103680,_17k=465,_17l=new T2(1,_17k,_Z),_17m=new T2(1,_17j,_17l),_17n=new T(function(){return B(_17g(_B4,_17m));}),_17o=function(_17p){return E(_17n);},_17q=new T(function(){return B(unCStr("s"));}),_17r=function(_17s,_17t){while(1){var _17u=E(_17s);if(!_17u._){return E(_17t);}else{_17s=_17u.b;_17t=_17u.a;continue;}}},_17v=function(_17w,_17x,_17y){return new F(function(){return _17r(_17x,_17w);});},_17z=new T1(0,1),_17A=function(_17B,_17C){var _17D=E(_17B);return new T2(0,_17D,new T(function(){var _17E=B(_17A(B(_gw(_17D,_17C)),_17C));return new T2(1,_17E.a,_17E.b);}));},_17F=function(_17G){var _17H=B(_17A(_17G,_17z));return new T2(1,_17H.a,_17H.b);},_17I=function(_17J,_17K){var _17L=B(_17A(_17J,new T(function(){return B(_iP(_17K,_17J));})));return new T2(1,_17L.a,_17L.b);},_17M=new T1(0,0),_17N=function(_17O,_17P){var _17Q=E(_17O);if(!_17Q._){var _17R=_17Q.a,_17S=E(_17P);return (_17S._==0)?_17R>=_17S.a:I_compareInt(_17S.a,_17R)<=0;}else{var _17T=_17Q.a,_17U=E(_17P);return (_17U._==0)?I_compareInt(_17T,_17U.a)>=0:I_compare(_17T,_17U.a)>=0;}},_17V=function(_17W,_17X,_17Y){if(!B(_17N(_17X,_17M))){var _17Z=function(_180){return (!B(_h8(_180,_17Y)))?new T2(1,_180,new T(function(){return B(_17Z(B(_gw(_180,_17X))));})):__Z;};return new F(function(){return _17Z(_17W);});}else{var _181=function(_182){return (!B(_gZ(_182,_17Y)))?new T2(1,_182,new T(function(){return B(_181(B(_gw(_182,_17X))));})):__Z;};return new F(function(){return _181(_17W);});}},_183=function(_184,_185,_186){return new F(function(){return _17V(_184,B(_iP(_185,_184)),_186);});},_187=function(_188,_189){return new F(function(){return _17V(_188,_17z,_189);});},_18a=function(_18b){return new F(function(){return _fb(_18b);});},_18c=function(_18d){return new F(function(){return _iP(_18d,_17z);});},_18e=function(_18f){return new F(function(){return _gw(_18f,_17z);});},_18g=function(_18h){return new F(function(){return _eS(E(_18h));});},_18i={_:0,a:_18e,b:_18c,c:_18g,d:_18a,e:_17F,f:_17I,g:_187,h:_183},_18j=function(_18k,_18l){while(1){var _18m=E(_18k);if(!_18m._){var _18n=E(_18m.a);if(_18n==( -2147483648)){_18k=new T1(1,I_fromInt( -2147483648));continue;}else{var _18o=E(_18l);if(!_18o._){return new T1(0,B(_dk(_18n,_18o.a)));}else{_18k=new T1(1,I_fromInt(_18n));_18l=_18o;continue;}}}else{var _18p=_18m.a,_18q=E(_18l);return (_18q._==0)?new T1(1,I_div(_18p,I_fromInt(_18q.a))):new T1(1,I_div(_18p,_18q.a));}}},_18r=function(_18s,_18t){if(!B(_go(_18t,_tc))){return new F(function(){return _18j(_18s,_18t);});}else{return E(_dV);}},_18u=function(_18v,_18w){while(1){var _18x=E(_18v);if(!_18x._){var _18y=E(_18x.a);if(_18y==( -2147483648)){_18v=new T1(1,I_fromInt( -2147483648));continue;}else{var _18z=E(_18w);if(!_18z._){var _18A=_18z.a;return new T2(0,new T1(0,B(_dk(_18y,_18A))),new T1(0,B(_ep(_18y,_18A))));}else{_18v=new T1(1,I_fromInt(_18y));_18w=_18z;continue;}}}else{var _18B=E(_18w);if(!_18B._){_18v=_18x;_18w=new T1(1,I_fromInt(_18B.a));continue;}else{var _18C=I_divMod(_18x.a,_18B.a);return new T2(0,new T1(1,_18C.a),new T1(1,_18C.b));}}}},_18D=function(_18E,_18F){if(!B(_go(_18F,_tc))){var _18G=B(_18u(_18E,_18F));return new T2(0,_18G.a,_18G.b);}else{return E(_dV);}},_18H=function(_18I,_18J){while(1){var _18K=E(_18I);if(!_18K._){var _18L=E(_18K.a);if(_18L==( -2147483648)){_18I=new T1(1,I_fromInt( -2147483648));continue;}else{var _18M=E(_18J);if(!_18M._){return new T1(0,B(_ep(_18L,_18M.a)));}else{_18I=new T1(1,I_fromInt(_18L));_18J=_18M;continue;}}}else{var _18N=_18K.a,_18O=E(_18J);return (_18O._==0)?new T1(1,I_mod(_18N,I_fromInt(_18O.a))):new T1(1,I_mod(_18N,_18O.a));}}},_18P=function(_18Q,_18R){if(!B(_go(_18R,_tc))){return new F(function(){return _18H(_18Q,_18R);});}else{return E(_dV);}},_18S=function(_18T,_18U){while(1){var _18V=E(_18T);if(!_18V._){var _18W=E(_18V.a);if(_18W==( -2147483648)){_18T=new T1(1,I_fromInt( -2147483648));continue;}else{var _18X=E(_18U);if(!_18X._){return new T1(0,quot(_18W,_18X.a));}else{_18T=new T1(1,I_fromInt(_18W));_18U=_18X;continue;}}}else{var _18Y=_18V.a,_18Z=E(_18U);return (_18Z._==0)?new T1(0,I_toInt(I_quot(_18Y,I_fromInt(_18Z.a)))):new T1(1,I_quot(_18Y,_18Z.a));}}},_190=function(_191,_192){if(!B(_go(_192,_tc))){return new F(function(){return _18S(_191,_192);});}else{return E(_dV);}},_193=function(_194,_195){if(!B(_go(_195,_tc))){var _196=B(_gF(_194,_195));return new T2(0,_196.a,_196.b);}else{return E(_dV);}},_197=function(_198,_199){while(1){var _19a=E(_198);if(!_19a._){var _19b=E(_19a.a);if(_19b==( -2147483648)){_198=new T1(1,I_fromInt( -2147483648));continue;}else{var _19c=E(_199);if(!_19c._){return new T1(0,_19b%_19c.a);}else{_198=new T1(1,I_fromInt(_19b));_199=_19c;continue;}}}else{var _19d=_19a.a,_19e=E(_199);return (_19e._==0)?new T1(1,I_rem(_19d,I_fromInt(_19e.a))):new T1(1,I_rem(_19d,_19e.a));}}},_19f=function(_19g,_19h){if(!B(_go(_19h,_tc))){return new F(function(){return _197(_19g,_19h);});}else{return E(_dV);}},_19i=function(_19j){return E(_19j);},_19k=function(_19l){return E(_19l);},_19m=function(_19n){var _19o=E(_19n);if(!_19o._){var _19p=E(_19o.a);return (_19p==( -2147483648))?E(_jt):(_19p<0)?new T1(0, -_19p):E(_19o);}else{var _19q=_19o.a;return (I_compareInt(_19q,0)>=0)?E(_19o):new T1(1,I_negate(_19q));}},_19r=new T1(0, -1),_19s=function(_19t){var _19u=E(_19t);if(!_19u._){var _19v=_19u.a;return (_19v>=0)?(E(_19v)==0)?E(_175):E(_h7):E(_19r);}else{var _19w=I_compareInt(_19u.a,0);return (_19w<=0)?(E(_19w)==0)?E(_175):E(_19r):E(_h7);}},_19x={_:0,a:_gw,b:_iP,c:_sG,d:_ju,e:_19m,f:_19s,g:_19k},_19y=function(_19z,_19A){var _19B=E(_19z);if(!_19B._){var _19C=_19B.a,_19D=E(_19A);return (_19D._==0)?_19C!=_19D.a:(I_compareInt(_19D.a,_19C)==0)?false:true;}else{var _19E=_19B.a,_19F=E(_19A);return (_19F._==0)?(I_compareInt(_19E,_19F.a)==0)?false:true:(I_compare(_19E,_19F.a)==0)?false:true;}},_19G=new T2(0,_go,_19y),_19H=function(_19I,_19J){return (!B(_iA(_19I,_19J)))?E(_19I):E(_19J);},_19K=function(_19L,_19M){return (!B(_iA(_19L,_19M)))?E(_19M):E(_19L);},_19N={_:0,a:_19G,b:_g8,c:_h8,d:_iA,e:_gZ,f:_17N,g:_19H,h:_19K},_19O=function(_19P){return new T2(0,E(_19P),E(_eW));},_19Q=new T3(0,_19x,_19N,_19O),_19R={_:0,a:_19Q,b:_18i,c:_190,d:_19f,e:_18r,f:_18P,g:_193,h:_18D,i:_19i},_19S=new T1(0,0),_19T=function(_19U,_19V,_19W){var _19X=B(A1(_19U,_19V));if(!B(_go(_19X,_19S))){return new F(function(){return _18j(B(_sG(_19V,_19W)),_19X);});}else{return E(_dV);}},_19Y=function(_19Z,_1a0){while(1){if(!B(_go(_1a0,_tc))){var _1a1=_1a0,_1a2=B(_19f(_19Z,_1a0));_19Z=_1a1;_1a0=_1a2;continue;}else{return E(_19Z);}}},_1a3=5,_1a4=new T(function(){return B(_dR(_1a3));}),_1a5=new T(function(){return die(_1a4);}),_1a6=function(_1a7,_1a8){if(!B(_go(_1a8,_tc))){var _1a9=B(_19Y(B(_19m(_1a7)),B(_19m(_1a8))));return (!B(_go(_1a9,_tc)))?new T2(0,B(_18S(_1a7,_1a9)),B(_18S(_1a8,_1a9))):E(_dV);}else{return E(_1a5);}},_1aa=function(_1ab,_1ac,_1ad,_1ae){var _1af=B(_sG(_1ac,_1ad));return new F(function(){return _1a6(B(_sG(B(_sG(_1ab,_1ae)),B(_19s(_1af)))),B(_19m(_1af)));});},_1ag=function(_1ah,_1ai,_1aj){var _1ak=new T(function(){if(!B(_go(_1aj,_tc))){var _1al=B(_gF(_1ai,_1aj));return new T2(0,_1al.a,_1al.b);}else{return E(_dV);}}),_1am=new T(function(){return B(A2(_lf,B(_sv(B(_st(_1ah)))),new T(function(){return E(E(_1ak).a);})));});return new T2(0,_1am,new T(function(){return new T2(0,E(E(_1ak).b),E(_1aj));}));},_1an=function(_1ao,_1ap,_1aq){var _1ar=B(_1ag(_1ao,_1ap,_1aq)),_1as=_1ar.a,_1at=E(_1ar.b);if(!B(_h8(B(_sG(_1at.a,_eW)),B(_sG(_tc,_1at.b))))){return E(_1as);}else{var _1au=B(_sv(B(_st(_1ao))));return new F(function(){return A3(_t8,_1au,_1as,new T(function(){return B(A2(_lf,_1au,_eW));}));});}},_1av=479723520,_1aw=40233135,_1ax=new T2(1,_1aw,_Z),_1ay=new T2(1,_1av,_1ax),_1az=new T(function(){return B(_17g(_B4,_1ay));}),_1aA=new T1(0,40587),_1aB=function(_1aC){var _1aD=new T(function(){var _1aE=B(_1aa(_1aC,_eW,_17n,_eW)),_1aF=B(_1aa(_1az,_eW,_17n,_eW)),_1aG=B(_1aa(_1aE.a,_1aE.b,_1aF.a,_1aF.b));return B(_1an(_19R,_1aG.a,_1aG.b));});return new T2(0,new T(function(){return B(_gw(_1aA,_1aD));}),new T(function(){return B(_iP(_1aC,B(_19T(_17o,B(_sG(_1aD,_17n)),_1az))));}));},_1aH=function(_1aI,_){var _1aJ=__get(_1aI,0),_1aK=__get(_1aI,1),_1aL=Number(_1aJ),_1aM=jsTrunc(_1aL),_1aN=Number(_1aK),_1aO=jsTrunc(_1aN);return new T2(0,_1aM,_1aO);},_1aP=new T(function(){return eval("(function(){var ms = new Date().getTime();                   return [(ms/1000)|0, ((ms % 1000)*1000)|0];})");}),_1aQ=660865024,_1aR=465661287,_1aS=new T2(1,_1aR,_Z),_1aT=new T2(1,_1aQ,_1aS),_1aU=new T(function(){return B(_17g(_B4,_1aT));}),_1aV=function(_){var _1aW=__app0(E(_1aP)),_1aX=B(_1aH(_1aW,_));return new T(function(){var _1aY=E(_1aX);if(!B(_go(_1aU,_19S))){return B(_gw(B(_sG(B(_eS(E(_1aY.a))),_17n)),B(_18j(B(_sG(B(_sG(B(_eS(E(_1aY.b))),_17n)),_17n)),_1aU))));}else{return E(_dV);}});},_1aZ=new T(function(){return B(err(_x3));}),_1b0=new T(function(){return B(err(_wZ));}),_1b1=new T(function(){return B(A3(_K9,_KC,_Ie,_K1));}),_1b2=new T1(0,1),_1b3=new T1(0,10),_1b4=function(_1b5){while(1){var _1b6=E(_1b5);if(!_1b6._){_1b5=new T1(1,I_fromInt(_1b6.a));continue;}else{return new F(function(){return I_toString(_1b6.a);});}}},_1b7=function(_1b8,_1b9){return new F(function(){return _x(fromJSStr(B(_1b4(_1b8))),_1b9);});},_1ba=new T1(0,0),_1bb=function(_1bc,_1bd,_1be){if(_1bc<=6){return new F(function(){return _1b7(_1bd,_1be);});}else{if(!B(_h8(_1bd,_1ba))){return new F(function(){return _1b7(_1bd,_1be);});}else{return new T2(1,_G,new T(function(){return B(_x(fromJSStr(B(_1b4(_1bd))),new T2(1,_F,_1be)));}));}}},_1bf=function(_1bg){return new F(function(){return _1bb(0,_1bg,_Z);});},_1bh=new T(function(){return B(_go(_1b3,_19S));}),_1bi=function(_1bj){while(1){if(!B(_go(_1bj,_19S))){if(!E(_1bh)){if(!B(_go(B(_18H(_1bj,_1b3)),_19S))){return new F(function(){return _1bf(_1bj);});}else{var _1bk=B(_18j(_1bj,_1b3));_1bj=_1bk;continue;}}else{return E(_dV);}}else{return __Z;}}},_1bl=46,_1bm=48,_1bn=function(_1bo,_1bp,_1bq){if(!B(_h8(_1bq,_19S))){var _1br=B(A1(_1bo,_1bq));if(!B(_go(_1br,_19S))){var _1bs=B(_18u(_1bq,_1br)),_1bt=_1bs.b,_1bu=new T(function(){var _1bv=Math.log(B(_jN(_1br)))/Math.log(10),_1bw=_1bv&4294967295,_1bx=function(_1by){if(_1by>=0){var _1bz=E(_1by);if(!_1bz){var _1bA=B(_18j(B(_iP(B(_gw(B(_sG(_1bt,_eW)),_1br)),_1b2)),_1br));}else{var _1bA=B(_18j(B(_iP(B(_gw(B(_sG(_1bt,B(_sW(_1b3,_1bz)))),_1br)),_1b2)),_1br));}var _1bB=function(_1bC){var _1bD=B(_1bb(0,_1bA,_Z)),_1bE=_1by-B(_qu(_1bD,0))|0;if(0>=_1bE){if(!E(_1bp)){return E(_1bD);}else{return new F(function(){return _1bi(_1bA);});}}else{var _1bF=new T(function(){if(!E(_1bp)){return E(_1bD);}else{return B(_1bi(_1bA));}}),_1bG=function(_1bH){var _1bI=E(_1bH);return (_1bI==1)?E(new T2(1,_1bm,_1bF)):new T2(1,_1bm,new T(function(){return B(_1bG(_1bI-1|0));}));};return new F(function(){return _1bG(_1bE);});}};if(!E(_1bp)){var _1bJ=B(_1bB(_));return (_1bJ._==0)?__Z:new T2(1,_1bl,_1bJ);}else{if(!B(_go(_1bA,_19S))){var _1bK=B(_1bB(_));return (_1bK._==0)?__Z:new T2(1,_1bl,_1bK);}else{return __Z;}}}else{return E(_tS);}};if(_1bw>=_1bv){return B(_1bx(_1bw));}else{return B(_1bx(_1bw+1|0));}},1);return new F(function(){return _x(B(_1bb(0,_1bs.a,_Z)),_1bu);});}else{return E(_dV);}}else{return new F(function(){return unAppCStr("-",new T(function(){return B(_1bn(_1bo,_1bp,B(_ju(_1bq))));}));});}},_1bL=function(_1bM,_1bN,_){var _1bO=B(_1aV(_)),_1bP=new T(function(){var _1bQ=new T(function(){var _1bR=new T(function(){var _1bS=B(_x(B(_1bn(_17o,_B4,B(_1aB(_1bO)).b)),_17q));if(!_1bS._){return E(_YH);}else{var _1bT=B(_YC(_1bS.a,_1bS.b));if(!_1bT._){return B(_17v(_Z,_Z,_10m));}else{var _1bU=_1bT.a,_1bV=E(_1bT.b);if(!_1bV._){return B(_17v(new T2(1,_1bU,_Z),_Z,_10m));}else{var _1bW=E(_1bU),_1bX=new T(function(){var _1bY=B(_LD(46,_1bV.a,_1bV.b));return new T2(0,_1bY.a,_1bY.b);});if(E(_1bW)==46){return B(_17v(_Z,new T2(1,new T(function(){return E(E(_1bX).a);}),new T(function(){return E(E(_1bX).b);})),_10m));}else{return B(_17v(new T2(1,_1bW,new T(function(){return E(E(_1bX).a);})),new T(function(){return E(E(_1bX).b);}),_10m));}}}}}),_1bZ=B(_KL(B(_x8(_1b1,_1bR))));if(!_1bZ._){return E(_1b0);}else{if(!E(_1bZ.b)._){return B(_uf(3,B(_H(0,E(_1bZ.a)+(imul(E(_1bN),E(_1bM)-1|0)|0)|0,_Z))));}else{return E(_1aZ);}}}),_1c0=B(_KL(B(_x8(_1b1,_1bQ))));if(!_1c0._){return E(_1b0);}else{if(!E(_1c0.b)._){return E(_1c0.a);}else{return E(_1aZ);}}});return new T2(0,new T(function(){return B(_ew(_1bP,_1bM));}),_1bP);},_1c1=function(_1c2,_1c3){while(1){var _1c4=E(_1c3);if(!_1c4._){return __Z;}else{var _1c5=_1c4.b,_1c6=E(_1c2);if(_1c6==1){return E(_1c5);}else{_1c2=_1c6-1|0;_1c3=_1c5;continue;}}}},_1c7=new T(function(){return B(unCStr("(Array.!): undefined array element"));}),_1c8=new T(function(){return B(err(_1c7));}),_1c9=0,_1ca=function(_1cb,_1cc,_1cd){return new F(function(){return _H(E(_1cb),E(_1cc),_1cd);});},_1ce=function(_1cf,_1cg){return new F(function(){return _H(0,E(_1cf),_1cg);});},_1ch=function(_1ci,_1cj){return new F(function(){return _2C(_1ce,_1ci,_1cj);});},_1ck=new T3(0,_1ca,_aC,_1ch),_1cl=0,_1cm=new T(function(){return B(unCStr(" out of range "));}),_1cn=new T(function(){return B(unCStr("}.index: Index "));}),_1co=new T(function(){return B(unCStr("Ix{"));}),_1cp=new T2(1,_F,_Z),_1cq=new T2(1,_F,_1cp),_1cr=0,_1cs=function(_1ct){return E(E(_1ct).a);},_1cu=function(_1cv,_1cw,_1cx,_1cy,_1cz){var _1cA=new T(function(){var _1cB=new T(function(){var _1cC=new T(function(){var _1cD=new T(function(){var _1cE=new T(function(){return B(A3(_wL,_vs,new T2(1,new T(function(){return B(A3(_1cs,_1cx,_1cr,_1cy));}),new T2(1,new T(function(){return B(A3(_1cs,_1cx,_1cr,_1cz));}),_Z)),_1cq));});return B(_x(_1cm,new T2(1,_G,new T2(1,_G,_1cE))));});return B(A(_1cs,[_1cx,_1cl,_1cw,new T2(1,_F,_1cD)]));});return B(_x(_1cn,new T2(1,_G,_1cC)));},1);return B(_x(_1cv,_1cB));},1);return new F(function(){return err(B(_x(_1co,_1cA)));});},_1cF=function(_1cG,_1cH,_1cI,_1cJ,_1cK){return new F(function(){return _1cu(_1cG,_1cH,_1cK,_1cI,_1cJ);});},_1cL=function(_1cM,_1cN,_1cO,_1cP){var _1cQ=E(_1cO);return new F(function(){return _1cF(_1cM,_1cN,_1cQ.a,_1cQ.b,_1cP);});},_1cR=function(_1cS,_1cT,_1cU,_1cV){return new F(function(){return _1cL(_1cV,_1cU,_1cT,_1cS);});},_1cW=new T(function(){return B(unCStr("Int"));}),_1cX=function(_1cY,_1cZ,_1d0){return new F(function(){return _1cR(_1ck,new T2(0,_1cZ,_1d0),_1cY,_1cW);});},_1d1=new T(function(){return B(unCStr("Negative range size"));}),_1d2=new T(function(){return B(err(_1d1));}),_1d3=function(_1d4){var _1d5=B(A1(_1d4,_));return E(_1d5);},_1d6=function(_1d7,_1d8,_1d9,_){var _1da=E(_1d7);if(!_1da){return new T2(0,_Z,_1d8);}else{var _1db=new T(function(){return B(_qu(_1d9,0))-1|0;}),_1dc=B(_1bL(new T(function(){return E(_1db)+1|0;}),_1d8,_)),_1dd=E(_1dc),_1de=_1dd.a,_1df=_1dd.b,_1dg=new T(function(){var _1dh=E(_1de);if(B(_qu(_1d9,0))>=(_1dh+1|0)){var _1di=new T(function(){var _1dj=_1dh+1|0;if(_1dj>0){return B(_1c1(_1dj,_1d9));}else{return E(_1d9);}});if(0>=_1dh){return E(_1di);}else{var _1dk=function(_1dl,_1dm){var _1dn=E(_1dl);if(!_1dn._){return E(_1di);}else{var _1do=_1dn.a,_1dp=E(_1dm);return (_1dp==1)?new T2(1,_1do,_1di):new T2(1,_1do,new T(function(){return B(_1dk(_1dn.b,_1dp-1|0));}));}};return B(_1dk(_1d9,_1dh));}}else{return E(_1d9);}}),_1dq=B(_1d6(_1da-1|0,_1df,_1dg,_)),_1dr=new T(function(){var _1ds=function(_){var _1dt=E(_1db),_1du=function(_1dv){if(_1dv>=0){var _1dw=newArr(_1dv,_1c8),_1dx=_1dw,_1dy=E(_1dv);if(!_1dy){return new T4(0,E(_1c9),E(_1dt),0,_1dx);}else{var _1dz=function(_1dA,_1dB,_){while(1){var _1dC=E(_1dA);if(!_1dC._){return E(_);}else{var _=_1dx[_1dB]=_1dC.a;if(_1dB!=(_1dy-1|0)){var _1dD=_1dB+1|0;_1dA=_1dC.b;_1dB=_1dD;continue;}else{return E(_);}}}},_=B(_1dz(_1d9,0,_));return new T4(0,E(_1c9),E(_1dt),_1dy,_1dx);}}else{return E(_1d2);}};if(0>_1dt){return new F(function(){return _1du(0);});}else{return new F(function(){return _1du(_1dt+1|0);});}},_1dE=B(_1d3(_1ds)),_1dF=E(_1dE.a),_1dG=E(_1dE.b),_1dH=E(_1de);if(_1dF>_1dH){return B(_1cX(_1dH,_1dF,_1dG));}else{if(_1dH>_1dG){return B(_1cX(_1dH,_1dF,_1dG));}else{return E(_1dE.d[_1dH-_1dF|0]);}}});return new T2(0,new T2(1,_1dr,new T(function(){return B(_wR(_1dq));})),_1df);}},_1dI=function(_1dJ,_1dK,_1dL,_1dM,_1dN,_1dO,_){var _1dP=function(_1dQ,_){return new F(function(){return _rP(_s5,_s5,function(_1dR,_){return new F(function(){return _rZ(B(_aS(_1dK,E(_1dO))),0,0,E(_1dR),_);});},E(_1dQ),_);});};return new F(function(){return _kT(new T(function(){return E(_1dL)-E(_1dM)*16;},1),new T(function(){return E(_1dN)*20;},1),_1dP,_1dJ,_);});},_1dS=1,_1dT=new T(function(){return B(_aS(_n5,1));}),_1dU=function(_1dV){return E(_1dV).d;},_1dW=function(_1dX,_1dY,_1dZ,_1e0,_1e1,_1e2,_){var _1e3=new T(function(){return E(E(_1e2).s);}),_1e4=new T(function(){return E(E(_1e3).a);}),_1e5=new T(function(){if(!B(_ep(E(_1e2).t,10))){var _1e6=E(E(_1e3).b);if(!(_1e6%2)){return _1e6+1|0;}else{return _1e6-1|0;}}else{return E(E(_1e3).b);}}),_1e7=new T(function(){var _1e8=E(_1e2);return {_:0,a:E(_1e8.a),b:E(_1e8.b),c:E(_1e8.c),d:E(_1e8.d),e:E(_1e8.e),f:E(_1e8.f),g:E(_1e8.g),h:E(_1e8.h),i:_1e8.i,j:_1e8.j,k:_1e8.k,l:_1e8.l,m:E(_1e8.m),n:_1e8.n,o:E(_1e8.o),p:E(_1e8.p),q:_1e8.q,r:E(_1e8.r),s:E(new T2(0,_1e4,_1e5)),t:_1e8.t,u:E(_1e8.u),v:E(_1e8.v),w:E(_1e8.w)};}),_1e9=new T(function(){return E(E(_1e7).a);}),_1ea=new T(function(){return E(E(_1e7).b);}),_1eb=new T(function(){return E(E(_1ea).a);}),_1ec=new T(function(){var _1ed=E(_1dZ)/16,_1ee=_1ed&4294967295;if(_1ed>=_1ee){return _1ee-2|0;}else{return (_1ee-1|0)-2|0;}}),_1ef=B(_rr(_1dX,_1dY,new T(function(){return B(_f5(_1ec,_1eb));}),_s9,new T(function(){return E(E(_1e9).b);}),_)),_1eg=new T(function(){return E(E(E(_1e7).a).a);}),_1eh=B(A(_qP,[_1dX,new T(function(){if(E(E(_1e9).e)==32){return E(_s7);}else{return E(_s8);}}),new T(function(){return ((E(E(_1eg).a)+E(_1ec)|0)-E(_1eb)|0)+1|0;},1),new T(function(){return (E(E(_1eg).b)+2|0)+1|0;},1),new T2(1,new T(function(){return B(_1dU(_1e9));}),_Z),_])),_1ei=E(_1e7),_1ej=_1ei.c,_1ek=_1ei.k,_1el=E(_1ei.v),_1em=new T(function(){var _1en=E(_1dZ)/28,_1eo=_1en&4294967295;if(_1en>=_1eo){return (_1eo-1|0)+_1ek|0;}else{return ((_1eo-1|0)-1|0)+_1ek|0;}}),_1ep=new T(function(){return (2+E(E(_1ea).b)|0)+2|0;}),_1eq=new T2(0,_1dX,_1dY),_1er=function(_){var _1es=function(_){var _1et=function(_){var _1eu=B(_1dI(_1dX,new T(function(){return E(E(_1e1).b);},1),_1dZ,new T(function(){return E(_1eb)+10|0;},1),_s9,new T(function(){return (imul(E(_1e4),8)|0)+E(_1e5)|0;},1),_));return _1ei;};if(!E(_1ei.p)._){return new F(function(){return _1et(_);});}else{var _1ev=B(A(_qP,[_1dX,_1dT,_1dS,_1dS,B(_H(0,_1ei.q,_Z)),_]));return new F(function(){return _1et(_);});}};if(!E(_1el.g)){return new F(function(){return _1es(_);});}else{var _1ew=B(_nb(_1eq,_1e0,0,_1ep,_1em,_1ep,B(_12A(_1ej,new T(function(){return B(_aj(_wR,_1ei.m));},1),_1ei.n)),_));return new F(function(){return _1es(_);});}};if(!E(_1el.c)){var _1ex=B(_nb(_1eq,_1e0,0,_1ep,_1em,_1ep,_1ej,_));return new F(function(){return _1er(_);});}else{return new F(function(){return _1er(_);});}},_1ey=function(_1ez,_1eA){while(1){var _1eB=E(_1ez);if(!_1eB._){return E(_1eA);}else{_1ez=_1eB.b;_1eA=_1eB.a;continue;}}},_1eC=function(_1eD,_1eE,_1eF){return new F(function(){return _1ey(_1eE,_1eD);});},_1eG=function(_1eH,_1eI){while(1){var _1eJ=E(_1eH);if(!_1eJ._){return E(_1eI);}else{_1eH=_1eJ.b;_1eI=_1eJ.a;continue;}}},_1eK=function(_1eL,_1eM,_1eN){return new F(function(){return _1eG(_1eM,_1eL);});},_1eO=function(_1eP,_1eQ){while(1){var _1eR=E(_1eQ);if(!_1eR._){return __Z;}else{var _1eS=_1eR.b,_1eT=E(_1eP);if(_1eT==1){return E(_1eS);}else{_1eP=_1eT-1|0;_1eQ=_1eS;continue;}}}},_1eU=function(_1eV,_1eW){var _1eX=new T(function(){var _1eY=_1eV+1|0;if(_1eY>0){return B(_1eO(_1eY,_1eW));}else{return E(_1eW);}});if(0>=_1eV){return E(_1eX);}else{var _1eZ=function(_1f0,_1f1){var _1f2=E(_1f0);if(!_1f2._){return E(_1eX);}else{var _1f3=_1f2.a,_1f4=E(_1f1);return (_1f4==1)?new T2(1,_1f3,_1eX):new T2(1,_1f3,new T(function(){return B(_1eZ(_1f2.b,_1f4-1|0));}));}};return new F(function(){return _1eZ(_1eW,_1eV);});}},_1f5=new T(function(){return B(unCStr(":"));}),_1f6=function(_1f7){var _1f8=E(_1f7);if(!_1f8._){return __Z;}else{var _1f9=new T(function(){return B(_x(_1f5,new T(function(){return B(_1f6(_1f8.b));},1)));},1);return new F(function(){return _x(_1f8.a,_1f9);});}},_1fa=function(_1fb,_1fc){var _1fd=new T(function(){return B(_x(_1f5,new T(function(){return B(_1f6(_1fc));},1)));},1);return new F(function(){return _x(_1fb,_1fd);});},_1fe=function(_1ff){return new F(function(){return _Q1("Check.hs:173:7-35|(co : na : xs)");});},_1fg=new T(function(){return B(_1fe(_));}),_1fh=new T(function(){return B(err(_wZ));}),_1fi=new T(function(){return B(err(_x3));}),_1fj=new T(function(){return B(A3(_K9,_KC,_Ie,_K1));}),_1fk=0,_1fl=new T(function(){return B(unCStr("!"));}),_1fm=function(_1fn,_1fo){var _1fp=E(_1fo);if(!_1fp._){return E(_1fg);}else{var _1fq=E(_1fp.b);if(!_1fq._){return E(_1fg);}else{var _1fr=E(_1fp.a),_1fs=new T(function(){var _1ft=B(_LD(58,_1fq.a,_1fq.b));return new T2(0,_1ft.a,_1ft.b);}),_1fu=function(_1fv,_1fw,_1fx){var _1fy=function(_1fz){if((_1fn+1|0)!=_1fz){return new T3(0,_1fn+1|0,_1fw,_1fp);}else{var _1fA=E(_1fx);return (_1fA._==0)?new T3(0,_1fk,_1fw,_Z):new T3(0,_1fk,_1fw,new T(function(){var _1fB=B(_1fa(_1fA.a,_1fA.b));if(!_1fB._){return E(_YH);}else{return B(_YC(_1fB.a,_1fB.b));}}));}};if(!B(_vi(_1fv,_1fl))){var _1fC=B(_KL(B(_x8(_1fj,_1fv))));if(!_1fC._){return E(_1fh);}else{if(!E(_1fC.b)._){return new F(function(){return _1fy(E(_1fC.a));});}else{return E(_1fi);}}}else{return new F(function(){return _1fy( -1);});}};if(E(_1fr)==58){return new F(function(){return _1fu(_Z,new T(function(){return E(E(_1fs).a);}),new T(function(){return E(E(_1fs).b);}));});}else{var _1fD=E(_1fs),_1fE=E(_1fD.b);if(!_1fE._){return E(_1fg);}else{return new F(function(){return _1fu(new T2(1,_1fr,_1fD.a),_1fE.a,_1fE.b);});}}}}},_1fF=function(_1fG,_1fH){while(1){var _1fI=E(_1fH);if(!_1fI._){return __Z;}else{var _1fJ=_1fI.b,_1fK=E(_1fG);if(_1fK==1){return E(_1fJ);}else{_1fG=_1fK-1|0;_1fH=_1fJ;continue;}}}},_1fL=function(_1fM,_1fN,_1fO){var _1fP=new T2(1,_1fN,new T(function(){var _1fQ=_1fM+1|0;if(_1fQ>0){return B(_1fF(_1fQ,_1fO));}else{return E(_1fO);}}));if(0>=_1fM){return E(_1fP);}else{var _1fR=function(_1fS,_1fT){var _1fU=E(_1fS);if(!_1fU._){return E(_1fP);}else{var _1fV=_1fU.a,_1fW=E(_1fT);return (_1fW==1)?new T2(1,_1fV,_1fP):new T2(1,_1fV,new T(function(){return B(_1fR(_1fU.b,_1fW-1|0));}));}};return new F(function(){return _1fR(_1fO,_1fM);});}},_1fX=new T2(0,_Yk,_IJ),_1fY=function(_1fZ,_1g0,_1g1){while(1){var _1g2=E(_1g1);if(!_1g2._){return E(_1fX);}else{var _1g3=_1g2.b,_1g4=E(_1g2.a),_1g5=E(_1g4.a);if(_1fZ!=E(_1g5.a)){_1g1=_1g3;continue;}else{if(_1g0!=E(_1g5.b)){_1g1=_1g3;continue;}else{return E(_1g4.b);}}}}},_1g6=function(_1g7,_1g8){while(1){var _1g9=E(_1g8);if(!_1g9._){return __Z;}else{var _1ga=_1g9.b,_1gb=E(_1g7);if(_1gb==1){return E(_1ga);}else{_1g7=_1gb-1|0;_1g8=_1ga;continue;}}}},_1gc=function(_1gd,_1ge,_1gf){var _1gg=E(_1gd);if(_1gg==1){return E(_1gf);}else{return new F(function(){return _1g6(_1gg-1|0,_1gf);});}},_1gh=function(_1gi,_1gj,_1gk){return new T2(1,new T(function(){if(0>=_1gi){return __Z;}else{return B(_uf(_1gi,new T2(1,_1gj,_1gk)));}}),new T(function(){if(_1gi>0){return B(_1gl(_1gi,B(_1gc(_1gi,_1gj,_1gk))));}else{return B(_1gh(_1gi,_1gj,_1gk));}}));},_1gl=function(_1gm,_1gn){var _1go=E(_1gn);if(!_1go._){return __Z;}else{var _1gp=_1go.a,_1gq=_1go.b;return new T2(1,new T(function(){if(0>=_1gm){return __Z;}else{return B(_uf(_1gm,_1go));}}),new T(function(){if(_1gm>0){return B(_1gl(_1gm,B(_1gc(_1gm,_1gp,_1gq))));}else{return B(_1gh(_1gm,_1gp,_1gq));}}));}},_1gr=function(_1gs,_1gt,_1gu){var _1gv=_1gt-1|0;if(0<=_1gv){var _1gw=E(_1gs),_1gx=function(_1gy){var _1gz=new T(function(){if(_1gy!=_1gv){return B(_1gx(_1gy+1|0));}else{return __Z;}}),_1gA=function(_1gB){var _1gC=E(_1gB);return (_1gC._==0)?E(_1gz):new T2(1,new T(function(){var _1gD=E(_1gu);if(!_1gD._){return E(_1fX);}else{var _1gE=_1gD.b,_1gF=E(_1gD.a),_1gG=E(_1gF.a),_1gH=E(_1gC.a);if(_1gH!=E(_1gG.a)){return B(_1fY(_1gH,_1gy,_1gE));}else{if(_1gy!=E(_1gG.b)){return B(_1fY(_1gH,_1gy,_1gE));}else{return E(_1gF.b);}}}}),new T(function(){return B(_1gA(_1gC.b));}));};return new F(function(){return _1gA(B(_ct(0,_1gw-1|0)));});};return new F(function(){return _1gl(_1gw,B(_1gx(0)));});}else{return __Z;}},_1gI=function(_1gJ){return new F(function(){return _Q1("Check.hs:72:21-47|(l : r : _)");});},_1gK=new T(function(){return B(_1gI(_));}),_1gL=61,_1gM=function(_1gN,_1gO){while(1){var _1gP=E(_1gN);if(!_1gP._){return E(_1gO);}else{_1gN=_1gP.b;_1gO=_1gP.a;continue;}}},_1gQ=function(_1gR,_1gS,_1gT){return new F(function(){return _1gM(_1gS,_1gR);});},_1gU=function(_1gV,_1gW){var _1gX=E(_1gW);if(!_1gX._){return new T2(0,_Z,_Z);}else{var _1gY=_1gX.a;if(!B(A1(_1gV,_1gY))){var _1gZ=new T(function(){var _1h0=B(_1gU(_1gV,_1gX.b));return new T2(0,_1h0.a,_1h0.b);});return new T2(0,new T2(1,_1gY,new T(function(){return E(E(_1gZ).a);})),new T(function(){return E(E(_1gZ).b);}));}else{return new T2(0,_Z,_1gX);}}},_1h1=function(_1h2,_1h3){while(1){var _1h4=E(_1h3);if(!_1h4._){return __Z;}else{if(!B(A1(_1h2,_1h4.a))){return E(_1h4);}else{_1h3=_1h4.b;continue;}}}},_1h5=function(_1h6){var _1h7=_1h6>>>0;if(_1h7>887){var _1h8=u_iswspace(_1h6);return (E(_1h8)==0)?false:true;}else{var _1h9=E(_1h7);return (_1h9==32)?true:(_1h9-9>>>0>4)?(E(_1h9)==160)?true:false:true;}},_1ha=function(_1hb){return new F(function(){return _1h5(E(_1hb));});},_1hc=function(_1hd){var _1he=B(_1h1(_1ha,_1hd));if(!_1he._){return __Z;}else{var _1hf=new T(function(){var _1hg=B(_1gU(_1ha,_1he));return new T2(0,_1hg.a,_1hg.b);});return new T2(1,new T(function(){return E(E(_1hf).a);}),new T(function(){return B(_1hc(E(_1hf).b));}));}},_1hh=function(_1hi){if(!B(_4H(_l8,_1gL,_1hi))){return new T2(0,_1hi,_Z);}else{var _1hj=new T(function(){var _1hk=E(_1hi);if(!_1hk._){return E(_1gK);}else{var _1hl=E(_1hk.b);if(!_1hl._){return E(_1gK);}else{var _1hm=_1hl.a,_1hn=_1hl.b,_1ho=E(_1hk.a);if(E(_1ho)==61){return new T2(0,_Z,new T(function(){return E(B(_LD(61,_1hm,_1hn)).a);}));}else{var _1hp=B(_LD(61,_1hm,_1hn)),_1hq=E(_1hp.b);if(!_1hq._){return E(_1gK);}else{return new T2(0,new T2(1,_1ho,_1hp.a),_1hq.a);}}}}});return new T2(0,new T(function(){var _1hr=B(_1hc(E(_1hj).a));if(!_1hr._){return __Z;}else{return B(_1gQ(_1hr.a,_1hr.b,_10m));}}),new T(function(){var _1hs=B(_1hc(E(_1hj).b));if(!_1hs._){return __Z;}else{return E(_1hs.a);}}));}},_1ht=function(_1hu,_1hv){return new F(function(){return _1eU(E(_1hu),_1hv);});},_1hw=function(_1hx){var _1hy=E(_1hx);if(!_1hy._){return new T2(0,_Z,_Z);}else{var _1hz=E(_1hy.a),_1hA=new T(function(){var _1hB=B(_1hw(_1hy.b));return new T2(0,_1hB.a,_1hB.b);});return new T2(0,new T2(1,_1hz.a,new T(function(){return E(E(_1hA).a);})),new T2(1,_1hz.b,new T(function(){return E(E(_1hA).b);})));}},_1hC=new T(function(){return B(unCStr("\u570b\uff1a\u3053\u304f\uff1a\u53f2\uff1a\u3057\uff1a\u4e26\uff1a\u306a\u3089\uff1a\u3079\u66ff\uff1a\u304b\uff1a\u3078\u554f\uff1a\u3082\u3093\uff1a\u984c\uff1a\u3060\u3044\uff1a\u3067\u3059\u3002\n{sm}{ch.\u554f\u984c\u3078,s0.\u30c1\u30e5\u30fc\u30c8\u30ea\u30a2\u30eb,t0}"));}),_1hD=new T(function(){return B(unCStr("t1"));}),_1hE=new T(function(){return B(unCStr("\n\u3053\u308c\u3089\u306e\u6587\uff1a\u3082\uff1a\u5b57\uff1a\u3058\uff1a\u306e\u65b9\u5411\u3078\u884c\uff1a\u3044\uff1a\u304f\u3068 \u3042\u306a\u305f\u306f \u3053\u308c\u3089\u306e\u6587\u5b57\u3092 <\u6301\uff1a\u3082\uff1a\u3063\u305f> \u72b6\uff1a\u3058\u3083\u3046\uff1a\u614b\uff1a\u305f\u3044\uff1a\u306b\u306a\u308a\u307e\u3059\u3002\n\u3053\u306e\u3068\u304d\uff20\u306e\u8272\uff1a\u3044\u308d\uff1a\u304c\u6fc3\uff1a\u3053\uff1a\u304f\u306a\u3063\u3066\u3090\u307e\u3059\u3002\n\u305d\u308c\u3067\u306f \uff20\u3092\u3069\u3053\u304b \u5225\uff1a\u3079\u3064\uff1a\u306e\u3068\u3053\u308d\u3078\u6301\u3063\u3066\u3044\u304d \u753b\u9762\u306e\u4e2d\uff1a\u3061\u3085\u3046\uff1a\u5fc3\uff1a\u3057\u3093\uff1a\u90e8\uff1a\u3076\uff1a\u3092\u30bf\u30c3\u30d7\u3057\u3066\u304f\u3060\u3055\u3044\u3002\n{da}{e.oa.m1:t2}{e.ob.m1:t2}{e.oc.m1:t2}"));}),_1hF=new T2(0,_1hD,_1hE),_1hG=new T(function(){return B(unCStr("t2"));}),_1hH=new T(function(){return B(unCStr("\n{da}\n\u3053\u306e\u3068\u304d \u6301\u3063\u3066\u3090\u305f\u6587\u5b57\u304c\u958b\uff1a\u304b\u3044\uff1a\u653e\uff1a\u306f\u3046\uff1a\u3055\u308c \u30de\u30c3\u30d7\u4e0a\u306b \u7f6e\uff1a\u304a\uff1a\u304b\u308c\u305f\u72b6\u614b\u306b\u306a\u308a\u307e\u3059\u3002\n\u554f\u984c\u3092\u89e3\uff1a\u3068\uff1a\u304f\u3068\u304d \u3053\u308c\u3089\u306e\u6587\u5b57\u3092 \u30a4\u30b3\u30fc\u30eb <\uff1d>\u306e\u53f3\uff1a\u307f\u304e\uff1a\u306b \u5de6\uff1a\u3072\u3060\u308a\uff1a\u304b\u3089\u9806\uff1a\u3058\u3085\u3093\uff1a\u756a\uff1a\u3070\u3093\uff1a\u306b\u4e26\uff1a\u306a\u3089\uff1a\u3079\u308b\u5fc5\uff1a\u3072\u3064\uff1a\u8981\uff1a\u3048\u3046\uff1a\u304c\u3042\u308a\u307e\u3059\u3002\n\u305d\u308c\u3067\u306f\u554f\u984c\u3092\u59cb\uff1a\u306f\u3058\uff1a\u3081\u307e\u3059\u3002{e.X.m1:t3}"));}),_1hI=new T2(0,_1hG,_1hH),_1hJ=new T(function(){return B(unCStr("t3"));}),_1hK=new T(function(){return B(unCStr("\n\u3088\u308d\u3057\u3044\u3067\u3059\u304b\uff1f{ch.\u306f\u3044,t4.\u6700\uff1a\u3055\u3044\uff1a\u521d\uff1a\u3057\u3087\uff1a\u304b\u3089,t0}"));}),_1hL=new T2(0,_1hJ,_1hK),_1hM=new T(function(){return B(unCStr("t4"));}),_1hN=new T(function(){return B(unCStr("\n\u305d\u308c\u3067\u306f\u59cb\u3081\u307e\u3059 {e.X.jl0}\n{e.X.m1:s0}"));}),_1hO=new T2(0,_1hM,_1hN),_1hP=new T(function(){return B(unCStr("s0"));}),_1hQ=new T(function(){return B(unCStr("\n\u3069\u3061\u3089\u306b\u3057\u307e\u3059\u304b\uff1f{ch.\u901a\u53f2,s01.\u8fd1\u73fe\u4ee3\u53f2,s02}"));}),_1hR=new T2(0,_1hP,_1hQ),_1hS=new T(function(){return B(unCStr("s01"));}),_1hT=new T(function(){return B(unCStr("\n\u53e4\uff1a\u3075\u308b\uff1a\u3044\u9806\uff1a\u3058\u3085\u3093\uff1a\u306b\u4e26\uff1a\u306a\u3089\uff1a\u3079\u3066\u304f\u3060\u3055\u3044\n{rk.1.z.abc.s0c1}{e.b=0.m0:s0eq}"));}),_1hU=new T2(0,_1hS,_1hT),_1hV=new T(function(){return B(unCStr("s02"));}),_1hW=new T(function(){return B(unCStr("\n\u53e4\uff1a\u3075\u308b\uff1a\u3044\u9806\uff1a\u3058\u3085\u3093\uff1a\u306b\u4e26\uff1a\u306a\u3089\uff1a\u3079\u3066\u304f\u3060\u3055\u3044\n{rk.2.z.abc.s0c2}{e.b=0.m0:s0eq}"));}),_1hX=new T2(0,_1hV,_1hW),_1hY=new T(function(){return B(unCStr("s1eq"));}),_1hZ=new T(function(){return B(unCStr("\n\u53e4\u3044\u9806\u306b\u4e26\u3079\u3066\u304f\u3060\u3055\u3044\u3002"));}),_1i0=new T2(0,_1hY,_1hZ),_1i1=new T(function(){return B(unCStr("s1c1"));}),_1i2=new T(function(){return B(unCStr("\n\u305b\u3044\u304b\u3044\uff01\u3002\n\u304b\u304b\u3063\u305f\u6642\u9593\u306f{rt.1}\n\u79d2\u3067\u3057\u305f\u3002\n\u6b21\u3078\u9032\u307f\u307e\u305b\u3046\u3002\n{d.b=0}{p.3,3.n,Ex}{e.un.l}{e.c1.m1:s21}"));}),_1i3=new T2(0,_1i1,_1i2),_1i4=new T(function(){return B(unCStr("s1c2"));}),_1i5=new T(function(){return B(unCStr("\n\u305b\u3044\u304b\u3044\uff01\u3002\n\u304b\u304b\u3063\u305f\u6642\u9593\u306f{rt.1}\n\u79d2\u3067\u3057\u305f\u3002\n\u6b21\u3078\u9032\u307f\u307e\u305b\u3046\u3002\n{d.b=0}{p.3,3.n,Ex}{e.un.l}{e.c1.m1:s22}"));}),_1i6=new T2(0,_1i4,_1i5),_1i7=new T(function(){return B(unCStr("s21"));}),_1i8=new T(function(){return B(unCStr("\n\u3060\u308c\u304b \u3090\u308b\u307f\u305f\u3044\u3067\u3059\u3002{da}{e.bA.m1:s2A0}{e.bB.m0:s2B0}{e.bC.m0:s2C0}{e.bD.m0:s2D0}{e.un.m0:s2n1}"));}),_1i9=new T2(0,_1i7,_1i8),_1ia=new T(function(){return B(unCStr("s22"));}),_1ib=new T(function(){return B(unCStr("\n\u3060\u308c\u304b \u3090\u308b\u307f\u305f\u3044\u3067\u3059\u3002{da}{e.bA.m1:s2A0}{e.bB.m0:s2B0}{e.bC.m0:s2C0}{e.bD.m0:s2D0}{e.un.m0:s2n2}"));}),_1ic=new T2(0,_1ia,_1ib),_1id=new T(function(){return B(unCStr("s2A0"));}),_1ie=new T(function(){return B(unCStr("\n\u3042\u306a\u305f\u306f \u81ea\uff1a\u3058\uff1a\u5206\uff1a\u3076\u3093\uff1a\u306e\u570b\uff1a\u304f\u306b\uff1a\u306e\u6b74\uff1a\u308c\u304d\uff1a\u53f2\uff1a\u3057\uff1a\u3092\u77e5\uff1a\u3057\uff1a\u308a\u305f\u3044\u3067\u3059\u304b\uff1f\u3002\n{ch.\u306f\u3044,s2A1_0.\u3044\u3044\u3048,s2A1_1}"));}),_1if=new T2(0,_1id,_1ie),_1ig=new T(function(){return B(unCStr("s2A1_0"));}),_1ih=new T(function(){return B(unCStr("\n\u3055\u3046\u3067\u3059\u304b\u30fb\u30fb\u30fb\u3002\n\u3061\u306a\u307f\u306b <\u81ea\u5206\u306e\u570b> \u3068\u306f\u4f55\uff1a\u306a\u3093\uff1a\u3067\u305b\u3046\u304b\u3002\n<\u6b74\u53f2>\u3068\u306f\u4f55\u3067\u305b\u3046\u304b\u3002\n\u305d\u306e\u6b74\u53f2\u3092<\u77e5\u308b>\u3068\u306f\u4f55\u3067\u305b\u3046\u304b\u3002\n{e.bA.m0:s2A1_2}"));}),_1ii=new T2(0,_1ig,_1ih),_1ij=new T(function(){return B(unCStr("s2A1_1"));}),_1ik=new T(function(){return B(unCStr("\n\u77e5\u308a\u305f\u304f\u3082\u306a\u3044\u3053\u3068\u3092 \u7121\uff1a\u3080\uff1a\u7406\uff1a\u308a\uff1a\u306b\u77e5\u308b\u5fc5\uff1a\u3072\u3064\uff1a\u8981\uff1a\u3048\u3046\uff1a\u306f\u3042\u308a\u307e\u305b\u3093\u3088\u306d\u3002 {e.bA.m1:s2A1_1}"));}),_1il=new T2(0,_1ij,_1ik),_1im=new T(function(){return B(unCStr("s2A1_2"));}),_1in=new T(function(){return B(unCStr("\n<\u81ea\u5206\u306e\u570b> \u3068\u306f\u4f55\u3067\u305b\u3046\u304b\u3002\n<\u6b74\u53f2>\u3068\u306f\u4f55\u3067\u305b\u3046\u304b\u3002\n\u305d\u306e\u6b74\u53f2\u3092<\u77e5\u308b>\u3068\u306f\u4f55\u3067\u305b\u3046\u304b\u3002"));}),_1io=new T2(0,_1im,_1in),_1ip=new T(function(){return B(unCStr("s2B0"));}),_1iq=new T(function(){return B(unCStr("\n\u79c1\uff1a\u308f\u305f\u3057\uff1a\u306e\u6301\uff1a\u3082\uff1a\u3063\u3066\u3090\u308b\u60c5\uff1a\u3058\u3083\u3046\uff1a\u5831\uff1a\u307b\u3046\uff1a\u306b\u3088\u308b\u3068\u3002\n\u30d4\u30e9\u30df\u30c3\u30c9\u3092\u9020\uff1a\u3064\u304f\uff1a\u308b\u306e\u306b\u4f7f\uff1a\u3064\u304b\uff1a\u306f\u308c\u305f\u77f3\uff1a\u3044\u3057\uff1a\u306f \u7a7a\uff1a\u304f\u3046\uff1a\u4e2d\uff1a\u3061\u3085\u3046\uff1a\u306b\u6301\uff1a\u3082\uff1a\u3061\u4e0a\uff1a\u3042\uff1a\u3052\u3089\u308c\u3066 \u7d44\uff1a\u304f\uff1a\u307f\u4e0a\u3052\u3089\u308c\u3066\u3090\u307e\u3057\u305f\u3002"));}),_1ir=new T2(0,_1ip,_1iq),_1is=new T(function(){return B(unCStr("s2C0"));}),_1it=new T(function(){return B(unCStr("\n\u30a4\u30a8\u30b9\u30fb\u30ad\u30ea\u30b9\u30c8\u306f \u30a4\u30f3\u30c9\u3084\u65e5\uff1a\u306b\uff1a\u672c\uff1a\u307b\u3093\uff1a\u3092\u8a2a\uff1a\u304a\u3068\u3065\uff1a\u308c\u3066\u3090\u305f\u3055\u3046\u3067\u3059\u3002\n\u3053\u308c\u3089\u306e\u5834\uff1a\u3070\uff1a\u6240\uff1a\u3057\u3087\uff1a\u306b\u306f \u305d\u306e\u5f62\uff1a\u3051\u3044\uff1a\u8de1\uff1a\u305b\u304d\uff1a\u304c \u3044\u304f\u3064\u3082\u6b98\uff1a\u306e\u3053\uff1a\u3063\u3066\u3090\u307e\u3059\u3002\n\u307e\u305f\u5f7c\uff1a\u304b\u308c\uff1a\u306f \u30a8\u30b8\u30d7\u30c8\u306e\u30d4\u30e9\u30df\u30c3\u30c8\u3067 \u79d8\uff1a\u3072\uff1a\u6280\uff1a\u304e\uff1a\u3092\u6388\uff1a\u3055\u3065\uff1a\u304b\u3063\u305f \u3068\u3044\u3075\u8a18\uff1a\u304d\uff1a\u9332\uff1a\u308d\u304f\uff1a\u304c\u3042\u308a\u307e\u3059\u3002"));}),_1iu=new T2(0,_1is,_1it),_1iv=new T(function(){return B(unCStr("s2D0"));}),_1iw=new T(function(){return B(unCStr("\n\u6b74\uff1a\u308c\u304d\uff1a\u53f2\uff1a\u3057\uff1a\u3068\u3044\u3075\u3082\u306e\u306f \u305d\u308c\u3092\u50b3\uff1a\u3064\u305f\uff1a\u3078\u308b\u76ee\uff1a\u3082\u304f\uff1a\u7684\uff1a\u3066\u304d\uff1a\u3084 \u50b3\u3078\u308b\u4eba\uff1a\u3072\u3068\uff1a\u3005\uff1a\u3073\u3068\uff1a\u306e\u4e16\uff1a\u305b\uff1a\u754c\uff1a\u304b\u3044\uff1a\u89c0\uff1a\u304b\u3093\uff1a \u50b3\u3078\u305f\u7576\uff1a\u305f\u3046\uff1a\u6642\uff1a\u3058\uff1a\u306b\u6b98\uff1a\u306e\u3053\uff1a\u3063\u3066\u3090\u305f\u8cc7\uff1a\u3057\uff1a\u6599\uff1a\u308c\u3046\uff1a\u306e\u7a2e\uff1a\u3057\u3085\uff1a\u985e\uff1a\u308b\u3044\uff1a\u306a\u3069\u306b\u3088\u3063\u3066 \u540c\uff1a\u304a\u306a\uff1a\u3058\u6642\uff1a\u3058\uff1a\u4ee3\uff1a\u3060\u3044\uff1a\u306b\u95dc\uff1a\u304b\u3093\uff1a\u3059\u308b\u3082\u306e\u3067\u3082 \u76f8\uff1a\u3055\u3046\uff1a\u7576\uff1a\u305f\u3046\uff1a\u7570\uff1a\u3053\u3068\uff1a\u306a\u3063\u305f\u50b3\uff1a\u3064\u305f\uff1a\u3078\u65b9\uff1a\u304b\u305f\uff1a\u304c\u70ba\uff1a\u306a\uff1a\u3055\u308c\u308b\u3082\u306e\u3067\u3059\u3002\n\u3057\u304b\u3057 \u305d\u308c\u306f \u78ba\uff1a\u304b\u304f\uff1a\u5be6\uff1a\u3058\u3064\uff1a\u306a\u6b74\u53f2\u306f\u5b58\uff1a\u305d\u3093\uff1a\u5728\uff1a\u3056\u3044\uff1a\u305b\u305a \u6b74\u53f2\u3092\u5b78\uff1a\u307e\u306a\uff1a\u3076\u610f\uff1a\u3044\uff1a\u7fa9\uff1a\u304e\uff1a\u3082\u306a\u3044 \u3068\u3044\u3075\u3053\u3068\u306b\u306f\u306a\u308a\u307e\u305b\u3093\u3002\n\u3042\u306a\u305f\u304c\u7d0d\uff1a\u306a\u3063\uff1a\u5f97\uff1a\u3068\u304f\uff1a\u3057 \u4ed6\uff1a\u307b\u304b\uff1a\u306e\u4eba\uff1a\u3072\u3068\uff1a\u9054\uff1a\u305f\u3061\uff1a\u3068\u5171\uff1a\u304d\u3087\u3046\uff1a\u6709\uff1a\u3044\u3046\n\uff1a\u3067\u304d\u308b \u5171\u6709\u3057\u305f\u3044\u6b74\u53f2\u3092 \u3042\u306a\u305f\u81ea\uff1a\u3058\uff1a\u8eab\uff1a\u3057\u3093\uff1a\u304c\u898b\uff1a\u307f\uff1a\u51fa\uff1a\u3044\u3060\uff1a\u3057 \u7d21\uff1a\u3064\u3080\uff1a\u304c\u306a\u3051\u308c\u3070\u306a\u3089\u306a\u3044\u4ed5\uff1a\u3057\uff1a\u7d44\uff1a\u304f\uff1a\u307f\u306b\u306a\u3063\u3066\u3090\u308b\u304b\u3089\u3053\u305d \u6b74\u53f2\u306b\u306f\u4fa1\uff1a\u304b\uff1a\u5024\uff1a\u3061\uff1a\u304c\u3042\u308a \u3042\u306a\u305f\u306e\u751f\uff1a\u3044\uff1a\u304d\u308b\u610f\uff1a\u3044\uff1a\u5473\uff1a\u307f\uff1a\u306b\u3082 \u7e4b\uff1a\u3064\u306a\uff1a\u304c\u3063\u3066\u304f\u308b\u306e\u3067\u306f\u306a\u3044\u3067\u305b\u3046\u304b\u3002"));}),_1ix=new T2(0,_1iv,_1iw),_1iy=new T(function(){return B(unCStr("s2n1"));}),_1iz=new T(function(){return B(unCStr("\n\u6b21\u3078\u9032\uff1a\u3059\u3059\uff1a\u307f\u307e\u3059\u304b\uff1f\n{ch.\u9032\u3080,s2n1c.\u9032\u307e\u306a\u3044,s2n0}"));}),_1iA=new T2(0,_1iy,_1iz),_1iB=new T(function(){return B(unCStr("s2n2"));}),_1iC=new T(function(){return B(unCStr("\n\u6b21\u3078\u9032\uff1a\u3059\u3059\uff1a\u307f\u307e\u3059\u304b\uff1f\n{ch.\u9032\u3080,s2n2c.\u9032\u307e\u306a\u3044,s2n0}"));}),_1iD=new T2(0,_1iB,_1iC),_1iE=new T(function(){return B(unCStr("s2n0"));}),_1iF=new T(function(){return B(unCStr("\n\u884c\u304f\u306e\u3092\u3084\u3081\u307e\u3057\u305f\u3002"));}),_1iG=new T2(0,_1iE,_1iF),_1iH=new T(function(){return B(unCStr("s2n1c"));}),_1iI=new T(function(){return B(unCStr("\n\u3067\u306f\u6b21\u3078\u884c\u304d\u307e\u305b\u3046\u3002{e.X.l}{e.c2.m1:s31}"));}),_1iJ=new T2(0,_1iH,_1iI),_1iK=new T(function(){return B(unCStr("s2n2c"));}),_1iL=new T(function(){return B(unCStr("\n\u3067\u306f\u6b21\u3078\u884c\u304d\u307e\u305b\u3046\u3002{e.X.l}{e.c2.m1:s32}"));}),_1iM=new T2(0,_1iK,_1iL),_1iN=new T(function(){return B(unCStr("s31"));}),_1iO=new T(function(){return B(unCStr("\n\u53e4\u3044\u9806\u306b\u4e26\u3079\u3066\u304f\u3060\u3055\u3044\n{da}{rk.1.z.abcd.s3c1}{e.b=0.m0:s3eq}"));}),_1iP=new T2(0,_1iN,_1iO),_1iQ=new T(function(){return B(unCStr("s32"));}),_1iR=new T(function(){return B(unCStr("\n\u53e4\u3044\u9806\u306b\u4e26\u3079\u3066\u304f\u3060\u3055\u3044\n{da}{rk.2.z.abcd.s3c2}{e.b=0.m0:s3eq}"));}),_1iS=new T2(0,_1iQ,_1iR),_1iT=new T(function(){return B(unCStr("s3eq"));}),_1iU=new T2(0,_1iT,_1hZ),_1iV=new T(function(){return B(unCStr("s3c1"));}),_1iW=new T(function(){return B(unCStr("\n\u305b\u3044\u304b\u3044\u3067\u3059\uff01\u3002\n\u304b\u304b\u3063\u305f\u6642\u9593\u306f{rt.2}\n\u79d2\u3067\u3057\u305f\u3002\n\u6b21\u3078\u884c\u304d\u307e\u305b\u3046\u3002\n{d.b=0}{p.3,3.%,Ex}{e.u%.l}{e.c3.m1:s41}"));}),_1iX=new T2(0,_1iV,_1iW),_1iY=new T(function(){return B(unCStr("s3c2"));}),_1iZ=new T(function(){return B(unCStr("\n\u305b\u3044\u304b\u3044\u3067\u3059\uff01\u3002\n\u304b\u304b\u3063\u305f\u6642\u9593\u306f{rt.2}\n\u79d2\u3067\u3057\u305f\u3002\n\u6b21\u3078\u884c\u304d\u307e\u305b\u3046\u3002\n{d.b=0}{p.3,3.%,Ex}{e.u%.l}{e.c3.m1:s42}"));}),_1j0=new T2(0,_1iY,_1iZ),_1j1=new T(function(){return B(unCStr("s41"));}),_1j2=new T(function(){return B(unCStr("\n\u53e4\u3044\u9806\u306b\u4e26\u3079\u3066\u304f\u3060\u3055\u3044\n{da}{rk.1.z.abcd.s4c1}{e.b=0.m0:s4eq}"));}),_1j3=new T2(0,_1j1,_1j2),_1j4=new T(function(){return B(unCStr("s42"));}),_1j5=new T(function(){return B(unCStr("\n\u53e4\u3044\u9806\u306b\u4e26\u3079\u3066\u304f\u3060\u3055\u3044\n{da}{rk.2.z.abcd.s4c2}{e.b=0.m0:s4eq}"));}),_1j6=new T2(0,_1j4,_1j5),_1j7=new T(function(){return B(unCStr("s4eq"));}),_1j8=new T2(0,_1j7,_1hZ),_1j9=new T(function(){return B(unCStr("s4c1"));}),_1ja=new T(function(){return B(unCStr("\n\u305b\u3044\u304b\u3044\uff01\u3002\n\u304b\u304b\u3063\u305f\u6642\u9593\u306f{rt.3}\n\u79d2\u3067\u3057\u305f\u3002\n\u6b21\u306b\u9032\u307f\u307e\u305b\u3046\u3002\n{d.b=0}{p.3,3.%,Ex}{e.u%.l}{e.c4.m1:s51}"));}),_1jb=new T2(0,_1j9,_1ja),_1jc=new T(function(){return B(unCStr("s4c2"));}),_1jd=new T(function(){return B(unCStr("\n\u305b\u3044\u304b\u3044\uff01\u3002\n\u304b\u304b\u3063\u305f\u6642\u9593\u306f{rt.3}\n\u79d2\u3067\u3057\u305f\u3002\n\u6b21\u306b\u9032\u307f\u307e\u305b\u3046\u3002\n{d.b=0}{p.3,3.%,Ex}{e.u%.l}{e.c4.m1:s52}"));}),_1je=new T2(0,_1jc,_1jd),_1jf=new T(function(){return B(unCStr("s51"));}),_1jg=new T(function(){return B(unCStr("\n\u3060\u308c\u304b \u3090\u308b\u307f\u305f\u3044\u3067\u3059\u3002{da}{e.bE.m0:s5E0}{e.bF.m0:s5F0}{e.bG.m0:s5G0}{e.bH.m0:s5H0}{e.un.m0:s5n1}"));}),_1jh=new T2(0,_1jf,_1jg),_1ji=new T(function(){return B(unCStr("s52"));}),_1jj=new T(function(){return B(unCStr("\n\u3060\u308c\u304b \u3090\u308b\u307f\u305f\u3044\u3067\u3059\u3002{da}{e.bE.m0:s5E0}{e.bF.m0:s5F0}{e.bG.m0:s5G0}{e.bH.m0:s5H0}{e.un.m0:s5n2}"));}),_1jk=new T2(0,_1ji,_1jj),_1jl=new T(function(){return B(unCStr("s5E0"));}),_1jm=new T(function(){return B(unCStr("\n\u904e\uff1a\u304b\uff1a\u53bb\uff1a\u3053\uff1a\u3082\u672a\uff1a\u307f\uff1a\u4f86\uff1a\u3089\u3044\uff1a\u3082 \u305d\u3057\u3066\u5225\uff1a\u3079\u3064\uff1a\u306e\u4e26\uff1a\u3078\u3044\uff1a\u884c\uff1a\u304b\u3046\uff1a\u4e16\uff1a\u305b\uff1a\u754c\uff1a\u304b\u3044\uff1a\u3082 \u3059\u3079\u3066\u306f \u4eca\uff1a\u3044\u307e\uff1a \u3053\u3053\u306b\u3042\u308a\u307e\u3059\u3002"));}),_1jn=new T2(0,_1jl,_1jm),_1jo=new T(function(){return B(unCStr("s5F0"));}),_1jp=new T(function(){return B(unCStr("\n\u672a\uff1a\u307f\uff1a\u4f86\uff1a\u3089\u3044\uff1a\u306f\u7576\uff1a\u305f\u3046\uff1a\u7136\uff1a\u305c\u3093\uff1a\u3055\u3046\u3067\u3059\u304c \u904e\uff1a\u304b\uff1a\u53bb\uff1a\u3053\uff1a\u3092\u6c7a\uff1a\u304d\uff1a\u3081\u308b\u306e\u3082 \u4eca\uff1a\u3044\u307e\uff1a\u306e\u3042\u306a\u305f\u6b21\uff1a\u3057\uff1a\u7b2c\uff1a\u3060\u3044\uff1a\u3067\u3059\u3002"));}),_1jq=new T2(0,_1jo,_1jp),_1jr=new T(function(){return B(unCStr("s5G0"));}),_1js=new T(function(){return B(unCStr("\n\u540c\uff1a\u304a\u306a\uff1a\u3058\u6642\uff1a\u3058\uff1a\u4ee3\uff1a\u3060\u3044\uff1a\u306e \u540c\u3058\u5834\uff1a\u3070\uff1a\u6240\uff1a\u3057\u3087\uff1a\u306b\u95dc\uff1a\u304b\u3093\uff1a\u3059\u308b\u898b\uff1a\u307f\uff1a\u65b9\uff1a\u304b\u305f\uff1a\u304c \u308f\u305f\u3057\u3068 \u3042\u306a\u305f\u3067\u9055\uff1a\u3061\u304c\uff1a\u3075\u306e\u306f\n\u4eca\uff1a\u3044\u307e\uff1a \u79c1\u3068 \u3042\u306a\u305f\u304c\u540c\u3058\u5834\u6240\u306b\u3090\u3066 \u305d\u3053\u306b\u5c45\uff1a\u3090\uff1a\u308b\u5225\uff1a\u3079\u3064\uff1a\u306e\u8ab0\uff1a\u3060\u308c\uff1a\u304b\u306b\u5c0d\uff1a\u305f\u3044\uff1a\u3059\u308b\u5370\uff1a\u3044\u3093\uff1a\u8c61\uff1a\u3057\u3083\u3046\uff1a\u304c \u308f\u305f\u3057\u3068 \u3042\u306a\u305f\u3067\u7570\uff1a\u3053\u3068\uff1a\u306a\u3063\u3066\u3090\u308b\u3053\u3068\u3068 \u4f3c\uff1a\u306b\uff1a\u3066\u3090\u307e\u3059\u3002\n\u305d\u308c\u306f \u81ea\uff1a\u3057\uff1a\u7136\uff1a\u305c\u3093\uff1a\u306a\u3053\u3068\u3067 \u308f\u305f\u3057\u3068 \u3042\u306a\u305f\u306e\u898b\u65b9\u304c\u9055\u3075\u306e\u306f \u5168\uff1a\u307e\u3063\u305f\uff1a\u304f\u554f\uff1a\u3082\u3093\uff1a\u984c\uff1a\u3060\u3044\uff1a\u3042\u308a\u307e\u305b\u3093\u3002\n\u898b\u65b9\u304c\u5168\uff1a\u305c\u3093\uff1a\u7136\uff1a\u305c\u3093\uff1a\u7570\u306a\u3063\u3066\u3090\u3066\u3082 \u308f\u305f\u3057\u3068 \u3042\u306a\u305f\u306f \u5171\uff1a\u304d\u3087\u3046\uff1a\u611f\uff1a\u304b\u3093\uff1a\u3059\u308b\u559c\uff1a\u3088\u308d\u3053\uff1a\u3073\u3092\u5473\uff1a\u3042\u3058\uff1a\u306f\u3046\u3053\u3068\u304c\u3067\u304d\u307e\u3059\u3002"));}),_1jt=new T2(0,_1jr,_1js),_1ju=new T(function(){return B(unCStr("s5H0"));}),_1jv=new T(function(){return B(unCStr("\n\u6211\uff1a\u308f\uff1a\u304c\u570b\uff1a\u304f\u306b\uff1a\u306e\u6557\uff1a\u306f\u3044\uff1a\u6230\uff1a\u305b\u3093\uff1a\u5f8c\uff1a\u3054\uff1a \u7279\uff1a\u3068\u304f\uff1a\u306b\u5f37\uff1a\u3064\u3088\uff1a\u307e\u3063\u305f \u65e5\uff1a\u306b\uff1a\u672c\uff1a\u307b\u3093\uff1a\u8a9e\uff1a\u3054\uff1a\u306e\u7834\uff1a\u306f\uff1a\u58ca\uff1a\u304b\u3044\uff1a\u5de5\uff1a\u3053\u3046\uff1a\u4f5c\uff1a\u3055\u304f\uff1a\u306f \u305d\u308c\u3092\u4ed5\uff1a\u3057\uff1a\u639b\uff1a\u304b\uff1a\u3051\u305f\u4eba\uff1a\u3072\u3068\uff1a\u306e\u610f\uff1a\u3044\uff1a\u5716\uff1a\u3068\uff1a\u3068\u9006\uff1a\u304e\u3083\u304f\uff1a\u306b \u65e5\u672c\u8a9e\u3092\u5f37\uff1a\u304d\u3083\u3046\uff1a\u5316\uff1a\u304f\u308f\uff1a\u3057 \u305d\u306e\u67d4\uff1a\u3058\u3046\uff1a\u8edf\uff1a\u306a\u3093\uff1a\u3055\u3092 \u3088\u308a\u4e16\uff1a\u305b\uff1a\u754c\uff1a\u304b\u3044\uff1a\u306b\u767c\uff1a\u306f\u3063\uff1a\u4fe1\uff1a\u3057\u3093\uff1a\u3059\u308b\u571f\uff1a\u3069\uff1a\u58cc\uff1a\u3058\u3083\u3046\uff1a\u3092\u4f5c\uff1a\u3064\u304f\uff1a\u3063\u305f\u306e\u3067\u306f\u306a\u3044\u304b\u3068 \u79c1\u306f\u8003\uff1a\u304b\u3093\u304c\uff1a\u3078\u3066\u3090\u307e\u3059\u3002\n\u3067\u3059\u304b\u3089 \u304b\u306a\u9063\uff1a\u3065\u304b\uff1a\u3072\u3092\u6df7\uff1a\u3053\u3093\uff1a\u4e82\uff1a\u3089\u3093\uff1a\u3055\u305b\u305f\u308a \u6f22\uff1a\u304b\u3093\uff1a\u5b57\uff1a\u3058\uff1a\u3092\u3068\u3063\u305f\u308a\u3064\u3051\u305f\u308a\u3057\u305f\u3053\u3068\u304c \u9006\u306b\u65e5\u672c\u8a9e\u306e\u5f37\u3055 \u67d4\u8edf\u3055\u306e\u8a3c\uff1a\u3057\u3087\u3046\uff1a\u660e\uff1a\u3081\u3044\uff1a\u3092\u3082\u305f\u3089\u3057\u305f\u3068\u3082\u3044\u3078\u308b\u306e\u3067 \u65e5\u672c\u8a9e\u3092\u6df7\u4e82\u3055\u305b\u305f\u4eba\u3005\u306b \u79c1\u306f\u611f\uff1a\u304b\u3093\uff1a\u8b1d\uff1a\u3057\u3083\uff1a\u3057\u3066\u3090\u308b\u306e\u3067\u3059\u3002"));}),_1jw=new T2(0,_1ju,_1jv),_1jx=new T(function(){return B(unCStr("s5n1"));}),_1jy=new T(function(){return B(unCStr("\n\u6b21\u3078\u9032\u307f\u307e\u3059\u304b\uff1f\n{ch.\u9032\u3080,s5n1c.\u9032\u307e\u306a\u3044,s5n0}"));}),_1jz=new T2(0,_1jx,_1jy),_1jA=new T(function(){return B(unCStr("s5n2"));}),_1jB=new T(function(){return B(unCStr("\n\u6b21\u3078\u9032\u307f\u307e\u3059\u304b\uff1f\n{ch.\u9032\u3080,s5n2c.\u9032\u307e\u306a\u3044,s5n0}"));}),_1jC=new T2(0,_1jA,_1jB),_1jD=new T(function(){return B(unCStr("s5n0"));}),_1jE=new T2(0,_1jD,_1iF),_1jF=new T(function(){return B(unCStr("s5n1c"));}),_1jG=new T(function(){return B(unCStr("\n\u3067\u306f\u6b21\u3078\u884c\u304d\u307e\u305b\u3046\u3002{e.X.l}{e.c5.m1:s61}"));}),_1jH=new T2(0,_1jF,_1jG),_1jI=new T(function(){return B(unCStr("s5n2c"));}),_1jJ=new T(function(){return B(unCStr("\n\u3067\u306f\u6b21\u3078\u884c\u304d\u307e\u305b\u3046\u3002{e.X.l}{e.c5.m1:s62}"));}),_1jK=new T2(0,_1jI,_1jJ),_1jL=new T(function(){return B(unCStr("s8I2"));}),_1jM=new T(function(){return B(unCStr("\n\u3067\u306f \u3088\u3044\u4e00\uff1a\u3044\u3061\uff1a\u65e5\uff1a\u306b\u3061\uff1a\u3092\u30fb\u30fb\u30fb\u3002{e.X.l}"));}),_1jN=new T2(0,_1jL,_1jM),_1jO=new T2(1,_1jN,_Z),_1jP=new T(function(){return B(unCStr("s8I1"));}),_1jQ=new T(function(){return B(unCStr("\n\u305d\u308c\u3067\u306f \u59cb\u3081\u307e\u305b\u3046\u3002{da}{e.c8.m1:s0}{e.X.jl0}"));}),_1jR=new T2(0,_1jP,_1jQ),_1jS=new T2(1,_1jR,_1jO),_1jT=new T(function(){return B(unCStr("s8I0"));}),_1jU=new T(function(){return B(unCStr("\n\u304a\u3064\u304b\u308c\u3055\u307e\u3067\u3059\u3002\n\u3042\u306a\u305f\u306e\u9ede\uff1a\u3066\u3093\uff1a\u6578\uff1a\u3059\u3046\uff1a\u306f{rs}\n\u9ede\uff1a\u3066\u3093\uff1a\u3067\u3059\u3002\n\u307e\u3046\u3044\u3061\u3069 \u3084\u308a\u307e\u3059\u304b\uff1f{ch.\u3084\u308b,s8I1.\u3084\u3081\u308b,s8I2}"));}),_1jV=new T2(0,_1jT,_1jU),_1jW=new T2(1,_1jV,_1jS),_1jX=new T(function(){return B(unCStr("s82"));}),_1jY=new T(function(){return B(unCStr("\n\u3060\u308c\u304b\u3090\u307e\u3059\u3002{da}{e.bI.m0:s8I0}"));}),_1jZ=new T2(0,_1jX,_1jY),_1k0=new T2(1,_1jZ,_1jW),_1k1=new T(function(){return B(unCStr("s81"));}),_1k2=new T2(0,_1k1,_1jY),_1k3=new T2(1,_1k2,_1k0),_1k4=new T(function(){return B(unCStr("s7c2"));}),_1k5=new T(function(){return B(unCStr("\n\u305b\u3044\u304b\u3044\uff01\u3002\n\u304b\u304b\u3063\u305f\u6642\u9593\u306f{rt.5}\n\u79d2\u3067\u3057\u305f\u3002\n\u6b21\u306b\u9032\u307f\u307e\u305b\u3046\u3002\n{d.b=0}{p.3,3.%,Ex}{e.u%.l}{e.c7.m1:s82}"));}),_1k6=new T2(0,_1k4,_1k5),_1k7=new T2(1,_1k6,_1k3),_1k8=new T(function(){return B(unCStr("s7c1"));}),_1k9=new T(function(){return B(unCStr("\n\u305b\u3044\u304b\u3044\uff01\u3002\n\u304b\u304b\u3063\u305f\u6642\u9593\u306f{rt.5}\n\u79d2\u3067\u3057\u305f\u3002\n\u6b21\u306b\u9032\u307f\u307e\u305b\u3046\u3002\n{d.b=0}{p.3,3.%,Ex}{e.u%.l}{e.c7.m1:s81}"));}),_1ka=new T2(0,_1k8,_1k9),_1kb=new T2(1,_1ka,_1k7),_1kc=new T(function(){return B(unCStr("s7eq"));}),_1kd=new T2(0,_1kc,_1hZ),_1ke=new T2(1,_1kd,_1kb),_1kf=new T(function(){return B(unCStr("s72"));}),_1kg=new T(function(){return B(unCStr("\n\u53e4\u3044\u9806\u306b\u4e26\u3079\u3066\u304f\u3060\u3055\u3044\n{da}{rk.2.z.abcde.s7c2}{e.b=0.m0:s7eq}"));}),_1kh=new T2(0,_1kf,_1kg),_1ki=new T2(1,_1kh,_1ke),_1kj=new T(function(){return B(unCStr("s71"));}),_1kk=new T(function(){return B(unCStr("\n\u53e4\u3044\u9806\u306b\u4e26\u3079\u3066\u304f\u3060\u3055\u3044\n{da}{rk.1.z.abcde.s7c1}{e.b=0.m0:s7eq}"));}),_1kl=new T2(0,_1kj,_1kk),_1km=new T2(1,_1kl,_1ki),_1kn=new T(function(){return B(unCStr("s6c2"));}),_1ko=new T(function(){return B(unCStr("\n\u305b\u3044\u304b\u3044\u3067\u3059\uff01\u3002\n\u304b\u304b\u3063\u305f\u6642\u9593\u306f{rt.4}\n\u79d2\u3067\u3057\u305f\u3002\n\u6b21\u306b\u9032\u307f\u307e\u305b\u3046\u3002\n{d.b=0}{p.3,3.%,Ex}{e.u%.l}{e.c6.m1:s72}"));}),_1kp=new T2(0,_1kn,_1ko),_1kq=new T2(1,_1kp,_1km),_1kr=new T(function(){return B(unCStr("s6c1"));}),_1ks=new T(function(){return B(unCStr("\n\u305b\u3044\u304b\u3044\u3067\u3059\uff01\u3002\n\u304b\u304b\u3063\u305f\u6642\u9593\u306f{rt.4}\n\u79d2\u3067\u3057\u305f\u3002\n\u6b21\u306b\u9032\u307f\u307e\u305b\u3046\u3002\n{d.b=0}{p.3,3.%,Ex}{e.u%.l}{e.c6.m1:s71}"));}),_1kt=new T2(0,_1kr,_1ks),_1ku=new T2(1,_1kt,_1kq),_1kv=new T(function(){return B(unCStr("s6eq"));}),_1kw=new T2(0,_1kv,_1hZ),_1kx=new T2(1,_1kw,_1ku),_1ky=new T(function(){return B(unCStr("s62"));}),_1kz=new T(function(){return B(unCStr("\n\u53e4\u3044\u9806\u306b\u4e26\u3079\u3066\u304f\u3060\u3055\u3044\n{rk.2.z.abcde.s6c2}{e.b=0.m0:s6eq}"));}),_1kA=new T2(0,_1ky,_1kz),_1kB=new T2(1,_1kA,_1kx),_1kC=new T(function(){return B(unCStr("s61"));}),_1kD=new T(function(){return B(unCStr("\n\u53e4\u3044\u9806\u306b\u4e26\u3079\u3066\u304f\u3060\u3055\u3044\n{rk.1.z.abcde.s6c1}{e.b=0.m0:s6eq}"));}),_1kE=new T2(0,_1kC,_1kD),_1kF=new T2(1,_1kE,_1kB),_1kG=new T2(1,_1jK,_1kF),_1kH=new T2(1,_1jH,_1kG),_1kI=new T2(1,_1jE,_1kH),_1kJ=new T2(1,_1jC,_1kI),_1kK=new T2(1,_1jz,_1kJ),_1kL=new T2(1,_1jw,_1kK),_1kM=new T2(1,_1jt,_1kL),_1kN=new T2(1,_1jq,_1kM),_1kO=new T2(1,_1jn,_1kN),_1kP=new T2(1,_1jk,_1kO),_1kQ=new T2(1,_1jh,_1kP),_1kR=new T2(1,_1je,_1kQ),_1kS=new T2(1,_1jb,_1kR),_1kT=new T2(1,_1j8,_1kS),_1kU=new T2(1,_1j6,_1kT),_1kV=new T2(1,_1j3,_1kU),_1kW=new T2(1,_1j0,_1kV),_1kX=new T2(1,_1iX,_1kW),_1kY=new T2(1,_1iU,_1kX),_1kZ=new T2(1,_1iS,_1kY),_1l0=new T2(1,_1iP,_1kZ),_1l1=new T2(1,_1iM,_1l0),_1l2=new T2(1,_1iJ,_1l1),_1l3=new T2(1,_1iG,_1l2),_1l4=new T2(1,_1iD,_1l3),_1l5=new T2(1,_1iA,_1l4),_1l6=new T2(1,_1ix,_1l5),_1l7=new T2(1,_1iu,_1l6),_1l8=new T2(1,_1ir,_1l7),_1l9=new T2(1,_1io,_1l8),_1la=new T2(1,_1il,_1l9),_1lb=new T2(1,_1ii,_1la),_1lc=new T2(1,_1if,_1lb),_1ld=new T2(1,_1ic,_1lc),_1le=new T2(1,_1i9,_1ld),_1lf=new T2(1,_1i6,_1le),_1lg=new T2(1,_1i3,_1lf),_1lh=new T2(1,_1i0,_1lg),_1li=new T(function(){return B(unCStr("s12"));}),_1lj=new T(function(){return B(unCStr("\n\u53e4\u3044\u9806\u306b\u4e26\u3079\u307e\u305b\u3046\u3002\n{da}{rk.2.z.abc.s1c2}{e.b=0.m0:s1eq}"));}),_1lk=new T2(0,_1li,_1lj),_1ll=new T2(1,_1lk,_1lh),_1lm=new T(function(){return B(unCStr("s11"));}),_1ln=new T(function(){return B(unCStr("\n\u53e4\u3044\u9806\u306b\u4e26\u3079\u307e\u305b\u3046\u3002\n{da}{rk.1.z.abc.s1c1}{e.b=0.m0:s1eq}"));}),_1lo=new T2(0,_1lm,_1ln),_1lp=new T2(1,_1lo,_1ll),_1lq=new T(function(){return B(unCStr("nubatama"));}),_1lr=new T(function(){return B(unCStr("\n\u306c\u3070\u305f\u307e\u306e \u4e16\u306f\u96e3\u3057\u304f \u601d\u3078\u308c\u3069\u3002   \n\u660e\u3051\u3066\u898b\u3086\u308b\u306f \u552f\u5927\u6cb3\u306a\u308a"));}),_1ls=new T2(0,_1lq,_1lr),_1lt=new T2(1,_1ls,_1lp),_1lu=new T(function(){return B(unCStr("\n\u4f55\u304c\u8d77\uff1a\u304a\uff1a\u3053\u3063\u305f\uff1f"));}),_1lv=new T(function(){return B(unCStr("msgW"));}),_1lw=new T2(0,_1lv,_1lu),_1lx=new T2(1,_1lw,_1lt),_1ly=new T(function(){return B(unCStr("\n\u307e\u3046\u4e00\u5ea6 \u3084\u3063\u3066\u307f\u3084\u3046"));}),_1lz=new T(function(){return B(unCStr("msgR"));}),_1lA=new T2(0,_1lz,_1ly),_1lB=new T2(1,_1lA,_1lx),_1lC=new T(function(){return B(unCStr("s0c2"));}),_1lD=new T(function(){return B(unCStr("\n\u305b\u3044\u304b\u3044\u3067\u3059\uff01\u3002\n\u304b\u304b\u3063\u305f\u6642\uff1a\u3058\uff1a\u9593\uff1a\u304b\u3093\uff1a\u306f{rt.0}\n\u79d2\uff1a\u3079\u3046\uff1a\u3067\u3057\u305f\u3002\n\u8a73\uff1a\u304f\u306f\uff1a\u3057\u3044\u8aac\uff1a\u305b\u3064\uff1a\u660e\uff1a\u3081\u3044\uff1a\u306f \u554f\uff1a\u3082\u3093\uff1a\u984c\uff1a\u3060\u3044\uff1a\u3060\u3063\u305f\u6587\uff1a\u3082\uff1a\u5b57\uff1a\u3058\uff1a\u3092<\u6301\uff1a\u3082\uff1a\u3064>\u3068\u898b\uff1a\u307f\uff1a\u308b\u3053\u3068\u304c\u3067\u304d\u307e\u3059\u3002\n\u6e96\uff1a\u3058\u3085\u3093\uff1a\u5099\uff1a\u3073\uff1a\u304c\u3067\u304d\u305f\u3089 \u6b21\uff1a\u3064\u304e\uff1a\u306e\u554f\u984c\u3078\u884c\uff1a\u3044\uff1a\u304d\u307e\u305b\u3046\u3002\n\u65b0\uff1a\u3042\u3089\uff1a\u305f\u306b\u51fa\uff1a\u3057\u3085\u3064\uff1a\u73fe\uff1a\u3052\u3093\uff1a\u3057\u305f\u6587\u5b57\u3078\u79fb\uff1a\u3044\uff1a\u52d5\uff1a\u3069\u3046\uff1a\u3057\u3066\u304f\u3060\u3055\u3044\n{d.b=0}{p.3,3.n,Ex}{e.un.l}{e.c0.m1:s12}"));}),_1lE=new T2(0,_1lC,_1lD),_1lF=new T2(1,_1lE,_1lB),_1lG=new T(function(){return B(unCStr("s0c1"));}),_1lH=new T(function(){return B(unCStr("\n\u305b\u3044\u304b\u3044\u3067\u3059\uff01\u3002\n\u304b\u304b\u3063\u305f\u6642\uff1a\u3058\uff1a\u9593\uff1a\u304b\u3093\uff1a\u306f{rt.0}\n\u79d2\uff1a\u3079\u3046\uff1a\u3067\u3057\u305f\u3002\n\u8a73\uff1a\u304f\u306f\uff1a\u3057\u3044\u8aac\uff1a\u305b\u3064\uff1a\u660e\uff1a\u3081\u3044\uff1a\u306f \u554f\uff1a\u3082\u3093\uff1a\u984c\uff1a\u3060\u3044\uff1a\u3060\u3063\u305f\u6587\uff1a\u3082\uff1a\u5b57\uff1a\u3058\uff1a\u3092<\u6301\uff1a\u3082\uff1a\u3064>\u3068\u898b\uff1a\u307f\uff1a\u308b\u3053\u3068\u304c\u3067\u304d\u307e\u3059\u3002\n\u6e96\uff1a\u3058\u3085\u3093\uff1a\u5099\uff1a\u3073\uff1a\u304c\u3067\u304d\u305f\u3089 \u6b21\uff1a\u3064\u304e\uff1a\u306e\u554f\u984c\u3078\u884c\uff1a\u3044\uff1a\u304d\u307e\u305b\u3046\u3002\n\u65b0\uff1a\u3042\u3089\uff1a\u305f\u306b\u51fa\uff1a\u3057\u3085\u3064\uff1a\u73fe\uff1a\u3052\u3093\uff1a\u3057\u305f\u6587\u5b57\u3078\u79fb\uff1a\u3044\uff1a\u52d5\uff1a\u3069\u3046\uff1a\u3057\u3066\u304f\u3060\u3055\u3044\n{d.b=0}{p.3,3.n,Ex}{e.un.l}{e.c0.m1:s11}"));}),_1lI=new T2(0,_1lG,_1lH),_1lJ=new T2(1,_1lI,_1lF),_1lK=new T(function(){return B(unCStr("s0eq"));}),_1lL=new T2(0,_1lK,_1hZ),_1lM=new T2(1,_1lL,_1lJ),_1lN=new T2(1,_1hX,_1lM),_1lO=new T2(1,_1hU,_1lN),_1lP=new T2(1,_1hR,_1lO),_1lQ=new T2(1,_1hO,_1lP),_1lR=new T2(1,_1hL,_1lQ),_1lS=new T2(1,_1hI,_1lR),_1lT=new T2(1,_1hF,_1lS),_1lU=new T(function(){return B(unCStr("t0"));}),_1lV=new T(function(){return B(unCStr("\n\u3042\u306a\u305f\u306f \u30de\u30c3\u30d7\u4e0a\u306e\uff20\u3092\u52d5\uff1a\u3046\u3054\uff1a\u304b\u3057\u307e\u3059\u3002\n\u753b\uff1a\u304c\uff1a\u9762\uff1a\u3081\u3093\uff1a\u306e\u4e0a\uff1a\u3058\u3087\u3046\uff1a\u7aef\uff1a\u305f\u3093\uff1a\u30fb\u4e0b\uff1a\u304b\uff1a\u7aef\uff1a\u305f\u3093\uff1a\u30fb\u5de6\uff1a\u3072\u3060\u308a\uff1a\u7aef\uff1a\u306f\u3057\uff1a\u30fb\u53f3\uff1a\u307f\u304e\uff1a\u7aef\uff1a\u306f\u3057\uff1a\u306a\u3069\u3092\u30bf\u30c3\u30d7\u3059\u308b\u3068\uff20\u306f\u305d\u306e\u65b9\uff1a\u306f\u3046\uff1a\u5411\uff1a\u304b\u3046\uff1a\u3078\u52d5\u304d\u307e\u3059\u3002\n{e.ea.m1:t1}{e.eb.m1:t1}{e.ec.m1:t1}"));}),_1lW=new T2(0,_1lU,_1lV),_1lX=new T2(1,_1lW,_1lT),_1lY=new T(function(){return B(unCStr("initMsg"));}),_1lZ=function(_1m0,_1m1){var _1m2=new T(function(){var _1m3=B(_1hw(_1m0));return new T2(0,_1m3.a,_1m3.b);}),_1m4=function(_1m5){var _1m6=E(_1m5);if(!_1m6._){return E(_1m2);}else{var _1m7=E(_1m6.a),_1m8=new T(function(){return B(_1m4(_1m6.b));});return new T2(0,new T2(1,_1m7.a,new T(function(){return E(E(_1m8).a);})),new T2(1,_1m7.b,new T(function(){return E(E(_1m8).b);})));}},_1m9=function(_1ma,_1mb,_1mc){var _1md=new T(function(){return B(_1m4(_1mc));});return new T2(0,new T2(1,_1ma,new T(function(){return E(E(_1md).a);})),new T2(1,_1mb,new T(function(){return E(E(_1md).b);})));},_1me=B(_1m9(_1lY,_1hC,_1lX)),_1mf=_1me.a;if(!B(_4H(_uF,_1m1,_1mf))){return __Z;}else{return new F(function(){return _aS(_1me.b,B(_Rt(_uF,_1m1,_1mf)));});}},_1mg=5,_1mh=new T2(0,_1mg,_1mg),_1mi=7,_1mj=new T2(0,_1mi,_1mg),_1mk=6,_1ml=new T2(0,_1mg,_1mk),_1mm=new T2(1,_1ml,_Z),_1mn=new T2(1,_1mj,_1mm),_1mo=new T2(1,_1mj,_1mn),_1mp=new T2(1,_1ml,_1mo),_1mq=new T2(1,_1mj,_1mp),_1mr=new T2(1,_1mj,_1mq),_1ms=new T2(1,_1ml,_1mr),_1mt=new T2(1,_1mh,_1ms),_1mu=new T2(1,_1mh,_1mt),_1mv=2,_1mw=new T2(0,_1mv,_1mv),_1mx=new T2(1,_1mw,_Z),_1my=new T2(1,_1mw,_1mx),_1mz=new T2(1,_1mw,_1my),_1mA=new T2(1,_1mw,_1mz),_1mB=new T2(1,_1mw,_1mA),_1mC=new T2(1,_1mw,_1mB),_1mD=new T2(1,_1mw,_1mC),_1mE=new T2(1,_1mw,_1mD),_1mF=new T2(1,_1mw,_1mE),_1mG=new T(function(){return B(unCStr("Int"));}),_1mH=function(_1mI,_1mJ,_1mK){return new F(function(){return _1cR(_1ck,new T2(0,_1mJ,_1mK),_1mI,_1mG);});},_1mL=new T(function(){return B(unCStr("msgR"));}),_1mM=new T(function(){return B(_1lZ(_Z,_1mL));}),_1mN=new T(function(){return B(unCStr("msgW"));}),_1mO=new T(function(){return B(_1lZ(_Z,_1mN));}),_1mP=function(_1mQ){var _1mR=E(_1mQ);return 0;},_1mS=new T(function(){return B(unCStr("@@@@@@@@@"));}),_1mT=new T(function(){var _1mU=E(_1mS);if(!_1mU._){return E(_ri);}else{return E(_1mU.a);}}),_1mV=122,_1mW=new T2(0,_1mV,_IP),_1mX=0,_1mY=new T2(0,_1mX,_1mX),_1mZ=new T2(0,_1mY,_1mW),_1n0=61,_1n1=new T2(0,_1n0,_IP),_1n2=1,_1n3=new T2(0,_1n2,_1mX),_1n4=new T2(0,_1n3,_1n1),_1n5=97,_1n6=new T2(0,_1n5,_IJ),_1n7=4,_1n8=new T2(0,_1mX,_1n7),_1n9=new T2(0,_1n8,_1n6),_1na=98,_1nb=new T2(0,_1na,_IJ),_1nc=new T2(0,_1mv,_1n7),_1nd=new T2(0,_1nc,_1nb),_1ne=99,_1nf=new T2(0,_1ne,_IJ),_1ng=new T2(0,_1n7,_1n7),_1nh=new T2(0,_1ng,_1nf),_1ni=new T2(1,_1nh,_Z),_1nj=new T2(1,_1nd,_1ni),_1nk=new T2(1,_1n9,_1nj),_1nl=new T2(1,_1n4,_1nk),_1nm=new T2(1,_1mZ,_1nl),_1nn=new T(function(){return B(_1gr(_1mg,5,_1nm));}),_1no=new T(function(){return B(_Q1("Check.hs:142:22-33|(ch : po)"));}),_1np=new T(function(){return B(_i8("Check.hs:(108,1)-(163,19)|function trEvent"));}),_1nq=110,_1nr=new T2(0,_1nq,_IV),_1ns=new T2(0,_1n7,_1mg),_1nt=new T2(0,_1ns,_1nr),_1nu=new T2(1,_1nt,_Z),_1nv=new T2(0,_1mv,_1mg),_1nw=66,_1nx=new T2(0,_1nw,_IP),_1ny=new T2(0,_1nv,_1nx),_1nz=new T2(1,_1ny,_1nu),_1nA=3,_1nB=new T2(0,_1mX,_1nA),_1nC=67,_1nD=new T2(0,_1nC,_IP),_1nE=new T2(0,_1nB,_1nD),_1nF=new T2(1,_1nE,_1nz),_1nG=new T2(0,_1n7,_1n2),_1nH=65,_1nI=new T2(0,_1nH,_IP),_1nJ=new T2(0,_1nG,_1nI),_1nK=new T2(1,_1nJ,_1nF),_1nL=68,_1nM=new T2(0,_1nL,_IP),_1nN=new T2(0,_1n3,_1nM),_1nO=new T2(1,_1nN,_1nK),_1nP=100,_1nQ=new T2(0,_1nP,_IJ),_1nR=new T2(0,_1mk,_1n7),_1nS=new T2(0,_1nR,_1nQ),_1nT=new T2(1,_1nS,_Z),_1nU=new T2(1,_1nh,_1nT),_1nV=new T2(1,_1nd,_1nU),_1nW=new T2(1,_1n9,_1nV),_1nX=new T2(1,_1n4,_1nW),_1nY=new T2(1,_1mZ,_1nX),_1nZ=70,_1o0=new T2(0,_1nZ,_IP),_1o1=new T2(0,_1nv,_1o0),_1o2=new T2(1,_1o1,_1nu),_1o3=72,_1o4=new T2(0,_1o3,_IP),_1o5=new T2(0,_1nB,_1o4),_1o6=new T2(1,_1o5,_1o2),_1o7=69,_1o8=new T2(0,_1o7,_IP),_1o9=new T2(0,_1nG,_1o8),_1oa=new T2(1,_1o9,_1o6),_1ob=71,_1oc=new T2(0,_1ob,_IP),_1od=new T2(0,_1n3,_1oc),_1oe=new T2(1,_1od,_1oa),_1of=101,_1og=new T2(0,_1of,_IJ),_1oh=new T2(0,_1n7,_1mv),_1oi=new T2(0,_1oh,_1og),_1oj=new T2(1,_1oi,_1nW),_1ok=new T2(1,_1n4,_1oj),_1ol=new T2(1,_1mZ,_1ok),_1om=73,_1on=new T2(0,_1om,_IP),_1oo=new T2(0,_1mv,_1mX),_1op=new T2(0,_1oo,_1on),_1oq=new T2(1,_1op,_Z),_1or=new T2(1,_1oq,_Z),_1os=new T2(1,_1ol,_1or),_1ot=new T2(1,_1ol,_1os),_1ou=new T2(1,_1oe,_1ot),_1ov=new T2(1,_1nY,_1ou),_1ow=new T2(1,_1nY,_1ov),_1ox=new T2(1,_1nO,_1ow),_1oy=new T2(1,_1nm,_1ox),_1oz=new T2(1,_1nm,_1oy),_1oA=function(_1oB){var _1oC=E(_1oB);if(!_1oC._){return __Z;}else{var _1oD=_1oC.b,_1oE=E(_1oC.a),_1oF=_1oE.b,_1oG=E(_1oE.a),_1oH=function(_1oI){if(E(_1oG)==32){return new T2(1,_1oE,new T(function(){return B(_1oA(_1oD));}));}else{switch(E(_1oF)){case 0:return new T2(1,new T2(0,_1oG,_IJ),new T(function(){return B(_1oA(_1oD));}));case 1:return new T2(1,new T2(0,_1oG,_Jk),new T(function(){return B(_1oA(_1oD));}));case 2:return new T2(1,new T2(0,_1oG,_IV),new T(function(){return B(_1oA(_1oD));}));case 3:return new T2(1,new T2(0,_1oG,_J1),new T(function(){return B(_1oA(_1oD));}));case 4:return new T2(1,new T2(0,_1oG,_J7),new T(function(){return B(_1oA(_1oD));}));case 5:return new T2(1,new T2(0,_1oG,_Jy),new T(function(){return B(_1oA(_1oD));}));case 6:return new T2(1,new T2(0,_1oG,_Jr),new T(function(){return B(_1oA(_1oD));}));case 7:return new T2(1,new T2(0,_1oG,_Jk),new T(function(){return B(_1oA(_1oD));}));default:return new T2(1,new T2(0,_1oG,_Jd),new T(function(){return B(_1oA(_1oD));}));}}};if(E(_1oG)==32){return new F(function(){return _1oH(_);});}else{switch(E(_1oF)){case 0:return new T2(1,new T2(0,_1oG,_Jd),new T(function(){return B(_1oA(_1oD));}));case 1:return new F(function(){return _1oH(_);});break;case 2:return new F(function(){return _1oH(_);});break;case 3:return new F(function(){return _1oH(_);});break;case 4:return new F(function(){return _1oH(_);});break;case 5:return new F(function(){return _1oH(_);});break;case 6:return new F(function(){return _1oH(_);});break;case 7:return new F(function(){return _1oH(_);});break;default:return new F(function(){return _1oH(_);});}}}},_1oJ=function(_1oK){var _1oL=E(_1oK);return (_1oL._==0)?__Z:new T2(1,new T(function(){return B(_1oA(_1oL.a));}),new T(function(){return B(_1oJ(_1oL.b));}));},_1oM=function(_1oN){var _1oO=E(_1oN);if(!_1oO._){return __Z;}else{var _1oP=_1oO.b,_1oQ=E(_1oO.a),_1oR=_1oQ.b,_1oS=E(_1oQ.a),_1oT=function(_1oU){if(E(_1oS)==32){return new T2(1,_1oQ,new T(function(){return B(_1oM(_1oP));}));}else{switch(E(_1oR)){case 0:return new T2(1,new T2(0,_1oS,_IJ),new T(function(){return B(_1oM(_1oP));}));case 1:return new T2(1,new T2(0,_1oS,_IP),new T(function(){return B(_1oM(_1oP));}));case 2:return new T2(1,new T2(0,_1oS,_IV),new T(function(){return B(_1oM(_1oP));}));case 3:return new T2(1,new T2(0,_1oS,_J1),new T(function(){return B(_1oM(_1oP));}));case 4:return new T2(1,new T2(0,_1oS,_J7),new T(function(){return B(_1oM(_1oP));}));case 5:return new T2(1,new T2(0,_1oS,_Jy),new T(function(){return B(_1oM(_1oP));}));case 6:return new T2(1,new T2(0,_1oS,_Jr),new T(function(){return B(_1oM(_1oP));}));case 7:return new T2(1,new T2(0,_1oS,_IP),new T(function(){return B(_1oM(_1oP));}));default:return new T2(1,new T2(0,_1oS,_Jd),new T(function(){return B(_1oM(_1oP));}));}}};if(E(_1oS)==32){return new F(function(){return _1oT(_);});}else{if(E(_1oR)==8){return new T2(1,new T2(0,_1oS,_IJ),new T(function(){return B(_1oM(_1oP));}));}else{return new F(function(){return _1oT(_);});}}}},_1oV=function(_1oW){var _1oX=E(_1oW);return (_1oX._==0)?__Z:new T2(1,new T(function(){return B(_1oM(_1oX.a));}),new T(function(){return B(_1oV(_1oX.b));}));},_1oY=function(_1oZ,_1p0,_1p1,_1p2,_1p3,_1p4,_1p5,_1p6,_1p7,_1p8,_1p9,_1pa,_1pb,_1pc,_1pd,_1pe,_1pf,_1pg,_1ph,_1pi,_1pj,_1pk,_1pl,_1pm,_1pn,_1po,_1pp,_1pq,_1pr,_1ps,_1pt,_1pu,_1pv,_1pw,_1px,_1py,_1pz,_1pA,_1pB,_1pC,_1pD,_1pE,_1pF){var _1pG=E(_1p0);if(!_1pG._){return E(_1np);}else{var _1pH=_1pG.b,_1pI=E(_1pG.a),_1pJ=new T(function(){var _1pK=function(_){var _1pL=B(_qu(_1pg,0))-1|0,_1pM=function(_1pN){if(_1pN>=0){var _1pO=newArr(_1pN,_1c8),_1pP=_1pO,_1pQ=E(_1pN);if(!_1pQ){return new T4(0,E(_1fk),E(_1pL),0,_1pP);}else{var _1pR=function(_1pS,_1pT,_){while(1){var _1pU=E(_1pS);if(!_1pU._){return E(_);}else{var _=_1pP[_1pT]=_1pU.a;if(_1pT!=(_1pQ-1|0)){var _1pV=_1pT+1|0;_1pS=_1pU.b;_1pT=_1pV;continue;}else{return E(_);}}}},_=B(_1pR(_1pg,0,_));return new T4(0,E(_1fk),E(_1pL),_1pQ,_1pP);}}else{return E(_1d2);}};if(0>_1pL){return new F(function(){return _1pM(0);});}else{return new F(function(){return _1pM(_1pL+1|0);});}},_1pW=B(_1d3(_1pK)),_1pX=E(_1pW.a),_1pY=E(_1pW.b),_1pZ=E(_1oZ);if(_1pX>_1pZ){return B(_1mH(_1pZ,_1pX,_1pY));}else{if(_1pZ>_1pY){return B(_1mH(_1pZ,_1pX,_1pY));}else{return E(_1pW.d[_1pZ-_1pX|0]);}}});switch(E(_1pI)){case 97:var _1q0=new T(function(){var _1q1=E(_1pH);if(!_1q1._){return E(_1no);}else{return new T2(0,_1q1.a,_1q1.b);}}),_1q2=new T(function(){var _1q3=B(_1hh(E(_1q0).b));return new T2(0,_1q3.a,_1q3.b);}),_1q4=B(_KL(B(_x8(_1fj,new T(function(){return E(E(_1q2).b);})))));if(!_1q4._){return E(_1fh);}else{if(!E(_1q4.b)._){var _1q5=new T(function(){var _1q6=B(_KL(B(_x8(_1fj,new T(function(){return E(E(_1q2).a);})))));if(!_1q6._){return E(_1fh);}else{if(!E(_1q6.b)._){return E(_1q6.a);}else{return E(_1fi);}}},1);return {_:0,a:E({_:0,a:E(_1p1),b:E(B(_PA(_1q5,E(_1q4.a),new T(function(){return E(E(_1q0).a);}),_IJ,_1p2))),c:E(_1p3),d:_1p4,e:_1p5,f:_1p6,g:E(_1p7),h:_1p8,i:E(B(_x(_1p9,_1pG))),j:E(_1pa),k:E(_1pb)}),b:E(_1pc),c:E(_1pd),d:E(_1pe),e:E(_1pf),f:E(_1pg),g:E(_1ph),h:E(_1pi),i:_1pj,j:_1pk,k:_1pl,l:_1pm,m:E(_1pn),n:_1po,o:E(_1pp),p:E(_1pq),q:_1pr,r:E(_1ps),s:E(_1pt),t:_1pu,u:E(_1pv),v:E({_:0,a:E(_1pw),b:E(_1px),c:E(_1py),d:E(_1pz),e:E(_1pA),f:E(_1pB),g:E(_1pC),h:E(_1pD),i:E(_1pE)}),w:E(_1pF)};}else{return E(_1fi);}}break;case 104:return {_:0,a:E({_:0,a:E(_1p1),b:E(B(_1oJ(_1p2))),c:E(_1p3),d:_1p4,e:_1p5,f:_1p6,g:E(_1p7),h:_1p8,i:E(B(_x(_1p9,_1pG))),j:E(_1pa),k:E(_1pb)}),b:E(_1pc),c:E(_1pd),d:E(_1pe),e:E(_1pf),f:E(_1pg),g:E(_1ph),h:E(_1pi),i:_1pj,j:_1pk,k:_1pl,l:_1pm,m:E(_1pn),n:_1po,o:E(_1pp),p:E(_1pq),q:_1pr,r:E(_1ps),s:E(_1pt),t:_1pu,u:E(_1pv),v:E({_:0,a:E(_1pw),b:E(_1px),c:E(_1py),d:E(_1pz),e:E(_1pA),f:E(_1pB),g:E(_1pC),h:E(_1pD),i:E(_1pE)}),w:E(_1pF)};case 106:var _1q7=E(_1pH);if(!_1q7._){return {_:0,a:E({_:0,a:E(_1p1),b:E(_1p2),c:E(_1p3),d:_1p4,e:_1p5,f:_1p6,g:E(_1p7),h:_1p8,i:E(B(_x(_1p9,_1pG))),j:E(_1pa),k:E(_1pb)}),b:E(_1pc),c:E(_1pd),d:E(_1pe),e:E(_1pf),f:E(_1pg),g:E(_1ph),h:E(_1pi),i:_1pj,j:_1pk,k:_1pl,l: -1,m:E(_1pn),n:_1po,o:E(_1pp),p:E(_1pq),q:_1pr,r:E(_1ps),s:E(_1pt),t:_1pu,u:E(_1pv),v:E({_:0,a:E(_1pw),b:E(_1px),c:E(_1py),d:E(_1pz),e:E(_1pA),f:E(_1pB),g:E(_1pC),h:E(_1pD),i:E(_1pE)}),w:E(_1pF)};}else{if(E(_1q7.a)==108){var _1q8=E(_1oZ),_1q9=B(_KL(B(_x8(_1fj,_1q7.b))));return (_1q9._==0)?E(_1fh):(E(_1q9.b)._==0)?{_:0,a:E({_:0,a:E(_1p1),b:E(_1p2),c:E(_1p3),d:_1p4,e:_1p5,f:_1p6,g:E(_1p7),h:_1p8,i:E(B(_x(_1p9,_1pG))),j:E(_1pa),k:E(_1pb)}),b:E(_1pc),c:E(_1pd),d:E(_1pe),e:E(B(_1eU(_1q8,_1pf))),f:E(B(_1eU(_1q8,_1pg))),g:E(_1ph),h:E(_1pi),i:_1pj,j:_1pk,k:_1pl,l:E(_1q9.a),m:E(_1pn),n:_1po,o:E(_1pp),p:E(_1pq),q:_1pr,r:E(_1ps),s:E(_1pt),t:_1pu,u:E(_1pv),v:E({_:0,a:E(_B4),b:E(_1px),c:E(_1py),d:E(_1pz),e:E(_1pA),f:E(_1pB),g:E(_1pC),h:E(_1pD),i:E(_1pE)}),w:E(_1pF)}:E(_1fi);}else{var _1qa=B(_KL(B(_x8(_1fj,_1q7))));return (_1qa._==0)?E(_1fh):(E(_1qa.b)._==0)?{_:0,a:E({_:0,a:E(_1p1),b:E(_1p2),c:E(_1p3),d:_1p4,e:_1p5,f:_1p6,g:E(_1p7),h:_1p8,i:E(B(_x(_1p9,_1pG))),j:E(_1pa),k:E(_1pb)}),b:E(_1pc),c:E(_1pd),d:E(_1pe),e:E(_1pf),f:E(_1pg),g:E(_1ph),h:E(_1pi),i:_1pj,j:_1pk,k:_1pl,l:E(_1qa.a),m:E(_1pn),n:_1po,o:E(_1pp),p:E(_1pq),q:_1pr,r:E(_1ps),s:E(_1pt),t:_1pu,u:E(_1pv),v:E({_:0,a:E(_1pw),b:E(_1px),c:E(_1py),d:E(_1pz),e:E(_1pA),f:E(_1pB),g:E(_1pC),h:E(_1pD),i:E(_1pE)}),w:E(_1pF)}:E(_1fi);}}break;case 108:var _1qb=E(_1oZ);return {_:0,a:E({_:0,a:E(_1p1),b:E(_1p2),c:E(_1p3),d:_1p4,e:_1p5,f:_1p6,g:E(_1p7),h:_1p8,i:E(B(_x(_1p9,_1pG))),j:E(_1pa),k:E(_1pb)}),b:E(_1pc),c:E(_1pd),d:E(_1pe),e:E(B(_1eU(_1qb,_1pf))),f:E(B(_1eU(_1qb,_1pg))),g:E(_1ph),h:E(_1pi),i:_1pj,j:_1pk,k:_1pl,l:_1pm,m:E(_1pn),n:_1po,o:E(_1pp),p:E(_1pq),q:_1pr,r:E(_1ps),s:E(_1pt),t:_1pu,u:E(_1pv),v:E({_:0,a:E(_B4),b:E(_1px),c:E(_1py),d:E(_1pz),e:E(_1pA),f:E(_1pB),g:E(_1pC),h:E(_1pD),i:E(_1pE)}),w:E(_1pF)};case 109:var _1qc=B(_1fm(E(_1pJ),_1pH)),_1qd=_1qc.c,_1qe=B(_vi(_1qd,_Z));if(!E(_1qe)){var _1qf=E(_1oZ),_1qg=new T(function(){var _1qh=function(_){var _1qi=B(_qu(_1pf,0))-1|0,_1qj=function(_1qk){if(_1qk>=0){var _1ql=newArr(_1qk,_1c8),_1qm=_1ql,_1qn=E(_1qk);if(!_1qn){return new T4(0,E(_1fk),E(_1qi),0,_1qm);}else{var _1qo=function(_1qp,_1qq,_){while(1){var _1qr=E(_1qp);if(!_1qr._){return E(_);}else{var _=_1qm[_1qq]=_1qr.a;if(_1qq!=(_1qn-1|0)){var _1qs=_1qq+1|0;_1qp=_1qr.b;_1qq=_1qs;continue;}else{return E(_);}}}},_=B(_1qo(_1pf,0,_));return new T4(0,E(_1fk),E(_1qi),_1qn,_1qm);}}else{return E(_1d2);}};if(0>_1qi){return new F(function(){return _1qj(0);});}else{return new F(function(){return _1qj(_1qi+1|0);});}},_1qt=B(_1d3(_1qh)),_1qu=E(_1qt.a),_1qv=E(_1qt.b);if(_1qu>_1qf){return B(_1mH(_1qf,_1qu,_1qv));}else{if(_1qf>_1qv){return B(_1mH(_1qf,_1qu,_1qv));}else{return E(E(_1qt.d[_1qf-_1qu|0]).a);}}}),_1qw=B(_1fL(_1qf,new T2(0,_1qg,new T2(1,_1pI,_1qd)),_1pf));}else{var _1qw=B(_1ht(_1oZ,_1pf));}if(!E(_1qe)){var _1qx=B(_1fL(E(_1oZ),_1qc.a,_1pg));}else{var _1qx=B(_1ht(_1oZ,_1pg));}return {_:0,a:E({_:0,a:E(_1p1),b:E(_1p2),c:E(_1p3),d:_1p4,e:_1p5,f:_1p6,g:E(_1p7),h:_1p8,i:E(B(_x(_1p9,_1pG))),j:E(_1pa),k:E(_1pb)}),b:E(_1pc),c:E(B(_1lZ(_1pe,_1qc.b))),d:E(_1pe),e:E(_1qw),f:E(_1qx),g:E(_1ph),h:E(_1pi),i:_1pj,j:_1pk,k:_1pl,l:_1pm,m:E(_1pn),n:_1po,o:E(_1pp),p:E(_1pq),q:_1pr,r:E(_1ps),s:E(_1pt),t:_1pu,u:E(_1pv),v:E({_:0,a:E(_1pw),b:E(_1px),c:E(_B4),d:E(_1pz),e:E(_1pA),f:E(_1pB),g:E(_1pC),h:E(_1pD),i:E(_1pE)}),w:E(_1pF)};case 114:var _1qy=B(_aS(_1mu,_1p6));return {_:0,a:E({_:0,a:E(B(_aS(_1mF,_1p6))),b:E(B(_1gr(_1qy.a,E(_1qy.b),new T(function(){return B(_aS(_1oz,_1p6));})))),c:E(_1p3),d:B(_aS(_1mS,_1p6)),e:32,f:_1p6,g:E(_1p7),h:_1p8,i:E(B(_x(_1p9,_1pG))),j:E(_1pa),k:E(_1pb)}),b:E(_1qy),c:E(_1mM),d:E(_1pe),e:E(_1pf),f:E(B(_aj(_1mP,_1pg))),g:E(_1ph),h:E(_1pi),i:_1pj,j:_1pk,k:_1pl,l:_1pm,m:E(_1pn),n:_1po,o:E(_1pp),p:E(_1pq),q:_1pr,r:E(_1ps),s:E(_1pt),t:_1pu,u:E(_1pv),v:E({_:0,a:E(_1pw),b:E(_1px),c:E(_B4),d:E(_1pz),e:E(_1pA),f:E(_1pB),g:E(_1pC),h:E(_1pD),i:E(_1pE)}),w:E(_1pF)};case 115:return {_:0,a:E({_:0,a:E(_1p1),b:E(B(_1oV(_1p2))),c:E(_1p3),d:_1p4,e:_1p5,f:_1p6,g:E(_1p7),h:_1p8,i:E(B(_x(_1p9,_1pG))),j:E(_1pa),k:E(_1pb)}),b:E(_1pc),c:E(_1pd),d:E(_1pe),e:E(_1pf),f:E(_1pg),g:E(_1ph),h:E(_1pi),i:_1pj,j:_1pk,k:_1pl,l:_1pm,m:E(_1pn),n:_1po,o:E(_1pp),p:E(_1pq),q:_1pr,r:E(_1ps),s:E(_1pt),t:_1pu,u:E(_1pv),v:E({_:0,a:E(_1pw),b:E(_1px),c:E(_1py),d:E(_1pz),e:E(_1pA),f:E(_1pB),g:E(_1pC),h:E(_1pD),i:E(_1pE)}),w:E(_1pF)};case 116:var _1qz=E(_1pJ),_1qA=B(_1fm(_1qz,_1pH)),_1qB=E(_1qA.a);if(!E(_1qB)){var _1qC=true;}else{var _1qC=false;}if(!E(_1qC)){var _1qD=B(_1fL(E(_1oZ),_1qB,_1pg));}else{var _1qD=B(_1fL(E(_1oZ),_1qz+1|0,_1pg));}if(!E(_1qC)){var _1qE=__Z;}else{var _1qE=E(_1qA.b);}if(!B(_vi(_1qE,_Z))){var _1qF=B(_1oY(_1oZ,_1qE,_1p1,_1p2,_1p3,_1p4,_1p5,_1p6,_1p7,_1p8,_1p9,_1pa,_1pb,_1pc,_1pd,_1pe,_1pf,_1qD,_1ph,_1pi,_1pj,_1pk,_1pl,_1pm,_1pn,_1po,_1pp,_1pq,_1pr,_1ps,_1pt,_1pu,_1pv,_1pw,_1px,_1py,_1pz,_1pA,_1pB,_1pC,_1pD,_1pE,_1pF)),_1qG=E(_1qF.a);return {_:0,a:E({_:0,a:E(_1qG.a),b:E(_1qG.b),c:E(_1qG.c),d:_1qG.d,e:_1qG.e,f:_1qG.f,g:E(_1qG.g),h:_1qG.h,i:E(B(_x(_1p9,_1pG))),j:E(_1qG.j),k:E(_1qG.k)}),b:E(_1qF.b),c:E(_1qF.c),d:E(_1qF.d),e:E(_1qF.e),f:E(_1qF.f),g:E(_1qF.g),h:E(_1qF.h),i:_1qF.i,j:_1qF.j,k:_1qF.k,l:_1qF.l,m:E(_1qF.m),n:_1qF.n,o:E(_1qF.o),p:E(_1qF.p),q:_1qF.q,r:E(_1qF.r),s:E(_1qF.s),t:_1qF.t,u:E(_1qF.u),v:E(_1qF.v),w:E(_1qF.w)};}else{return {_:0,a:E({_:0,a:E(_1p1),b:E(_1p2),c:E(_1p3),d:_1p4,e:_1p5,f:_1p6,g:E(_1p7),h:_1p8,i:E(B(_x(_1p9,_1pG))),j:E(_1pa),k:E(_1pb)}),b:E(_1pc),c:E(_1pd),d:E(_1pe),e:E(_1pf),f:E(_1qD),g:E(_1ph),h:E(_1pi),i:_1pj,j:_1pk,k:_1pl,l:_1pm,m:E(_1pn),n:_1po,o:E(_1pp),p:E(_1pq),q:_1pr,r:E(_1ps),s:E(_1pt),t:_1pu,u:E(_1pv),v:E({_:0,a:E(_1pw),b:E(_1px),c:E(_1py),d:E(_1pz),e:E(_1pA),f:E(_1pB),g:E(_1pC),h:E(_1pD),i:E(_1pE)}),w:E(_1pF)};}break;case 119:return {_:0,a:E({_:0,a:E(_1mw),b:E(_1nn),c:E(_1p3),d:E(_1mT),e:32,f:0,g:E(_1p7),h:_1p8,i:E(B(_x(_1p9,_1pG))),j:E(_1pa),k:E(_1pb)}),b:E(_1mh),c:E(_1mO),d:E(_1pe),e:E(_1pf),f:E(B(_aj(_1mP,_1pg))),g:E(_1ph),h:E(_1pi),i:_1pj,j:_1pk,k:_1pl,l:_1pm,m:E(_1pn),n:_1po,o:E(_1pp),p:E(_1pq),q:_1pr,r:E(_1ps),s:E(_1pt),t:_1pu,u:E(_1pv),v:E({_:0,a:E(_1pw),b:E(_1px),c:E(_B4),d:E(_1pz),e:E(_1pA),f:E(_1pB),g:E(_1pC),h:E(_1pD),i:E(_1pE)}),w:E(_1pF)};default:return {_:0,a:E({_:0,a:E(_1p1),b:E(_1p2),c:E(_1p3),d:_1p4,e:_1p5,f:_1p6,g:E(_1p7),h:_1p8,i:E(B(_x(_1p9,_1pG))),j:E(_1pa),k:E(_1pb)}),b:E(_1pc),c:E(_1pd),d:E(_1pe),e:E(_1pf),f:E(_1pg),g:E(_1ph),h:E(_1pi),i:_1pj,j:_1pk,k:_1pl,l:_1pm,m:E(_1pn),n:_1po,o:E(_1pp),p:E(_1pq),q:_1pr,r:E(_1ps),s:E(_1pt),t:_1pu,u:E(_1pv),v:E({_:0,a:E(_1pw),b:E(_1px),c:E(_1py),d:E(_1pz),e:E(_1pA),f:E(_1pB),g:E(_1pC),h:E(_1pD),i:E(_1pE)}),w:E(_1pF)};}}},_1qH=function(_1qI,_1qJ){while(1){var _1qK=E(_1qJ);if(!_1qK._){return __Z;}else{var _1qL=_1qK.b,_1qM=E(_1qI);if(_1qM==1){return E(_1qL);}else{_1qI=_1qM-1|0;_1qJ=_1qL;continue;}}}},_1qN=new T(function(){return B(unCStr("X"));}),_1qO=new T(function(){return B(_i8("Check.hs:(87,7)-(92,39)|function chAnd"));}),_1qP=38,_1qQ=function(_1qR,_1qS,_1qT,_1qU,_1qV,_1qW,_1qX,_1qY,_1qZ,_1r0,_1r1,_1r2,_1r3,_1r4,_1r5,_1r6,_1r7,_1r8,_1r9,_1ra,_1rb,_1rc,_1rd,_1re,_1rf,_1rg){var _1rh=E(_1qT);if(!_1rh._){return {_:0,a:_1qU,b:_1qV,c:_1qW,d:_1qX,e:_1qY,f:_1qZ,g:_1r0,h:_1r1,i:_1r2,j:_1r3,k:_1r4,l:_1r5,m:_1r6,n:_1r7,o:_1r8,p:_1r9,q:_1ra,r:_1rb,s:_1rc,t:_1rd,u:_1re,v:_1rf,w:_1rg};}else{var _1ri=_1rh.b,_1rj=E(_1rh.a),_1rk=_1rj.a,_1rl=_1rj.b,_1rm=function(_1rn,_1ro,_1rp){var _1rq=function(_1rr,_1rs){if(!B(_vi(_1rr,_Z))){var _1rt=E(_1qU),_1ru=E(_1rf),_1rv=B(_1oY(_1rs,_1rr,_1rt.a,_1rt.b,_1rt.c,_1rt.d,_1rt.e,_1rt.f,_1rt.g,_1rt.h,_1rt.i,_1rt.j,_1rt.k,_1qV,_1qW,_1qX,_1qY,_1qZ,_1r0,_1r1,_1r2,_1r3,_1r4,_1r5,_1r6,_1r7,_1r8,_1r9,_1ra,_1rb,_1rc,_1rd,_1re,_1ru.a,_1ru.b,_1ru.c,_1ru.d,_1ru.e,_1ru.f,_1ru.g,_1ru.h,_1ru.i,_1rg)),_1rw=_1rv.a,_1rx=_1rv.b,_1ry=_1rv.c,_1rz=_1rv.d,_1rA=_1rv.e,_1rB=_1rv.f,_1rC=_1rv.g,_1rD=_1rv.h,_1rE=_1rv.i,_1rF=_1rv.j,_1rG=_1rv.k,_1rH=_1rv.l,_1rI=_1rv.m,_1rJ=_1rv.n,_1rK=_1rv.o,_1rL=_1rv.p,_1rM=_1rv.q,_1rN=_1rv.r,_1rO=_1rv.s,_1rP=_1rv.t,_1rQ=_1rv.u,_1rR=_1rv.v,_1rS=_1rv.w;if(B(_qu(_1rB,0))!=B(_qu(_1qZ,0))){return {_:0,a:_1rw,b:_1rx,c:_1ry,d:_1rz,e:_1rA,f:_1rB,g:_1rC,h:_1rD,i:_1rE,j:_1rF,k:_1rG,l:_1rH,m:_1rI,n:_1rJ,o:_1rK,p:_1rL,q:_1rM,r:_1rN,s:_1rO,t:_1rP,u:_1rQ,v:_1rR,w:_1rS};}else{return new F(function(){return _1qQ(new T(function(){return E(_1qR)+1|0;}),_1qS,_1ri,_1rw,_1rx,_1ry,_1rz,_1rA,_1rB,_1rC,_1rD,_1rE,_1rF,_1rG,_1rH,_1rI,_1rJ,_1rK,_1rL,_1rM,_1rN,_1rO,_1rP,_1rQ,_1rR,_1rS);});}}else{return new F(function(){return _1qQ(new T(function(){return E(_1qR)+1|0;}),_1qS,_1ri,_1qU,_1qV,_1qW,_1qX,_1qY,_1qZ,_1r0,_1r1,_1r2,_1r3,_1r4,_1r5,_1r6,_1r7,_1r8,_1r9,_1ra,_1rb,_1rc,_1rd,_1re,_1rf,_1rg);});}},_1rT=B(_qu(_1qS,0))-B(_qu(new T2(1,_1rn,_1ro),0))|0;if(_1rT>0){var _1rU=B(_1qH(_1rT,_1qS));}else{var _1rU=E(_1qS);}if(E(B(_1eC(_1rn,_1ro,_10m)))==63){var _1rV=B(_YC(_1rn,_1ro));}else{var _1rV=new T2(1,_1rn,_1ro);}var _1rW=function(_1rX){if(!B(_4H(_l8,_1qP,_1rk))){return new T2(0,_1rl,_1qR);}else{var _1rY=function(_1rZ){while(1){var _1s0=B((function(_1s1){var _1s2=E(_1s1);if(!_1s2._){return true;}else{var _1s3=_1s2.b,_1s4=E(_1s2.a);if(!_1s4._){return E(_1qO);}else{switch(E(_1s4.a)){case 99:var _1s5=E(_1qU);if(!E(_1s5.k)){return false;}else{var _1s6=function(_1s7){while(1){var _1s8=E(_1s7);if(!_1s8._){return true;}else{var _1s9=_1s8.b,_1sa=E(_1s8.a);if(!_1sa._){return E(_1qO);}else{if(E(_1sa.a)==115){var _1sb=B(_KL(B(_x8(_1fj,_1sa.b))));if(!_1sb._){return E(_1fh);}else{if(!E(_1sb.b)._){if(_1s5.f!=E(_1sb.a)){return false;}else{_1s7=_1s9;continue;}}else{return E(_1fi);}}}else{_1s7=_1s9;continue;}}}}};return new F(function(){return _1s6(_1s3);});}break;case 115:var _1sc=E(_1qU),_1sd=_1sc.f,_1se=B(_KL(B(_x8(_1fj,_1s4.b))));if(!_1se._){return E(_1fh);}else{if(!E(_1se.b)._){if(_1sd!=E(_1se.a)){return false;}else{var _1sf=function(_1sg){while(1){var _1sh=E(_1sg);if(!_1sh._){return true;}else{var _1si=_1sh.b,_1sj=E(_1sh.a);if(!_1sj._){return E(_1qO);}else{switch(E(_1sj.a)){case 99:if(!E(_1sc.k)){return false;}else{_1sg=_1si;continue;}break;case 115:var _1sk=B(_KL(B(_x8(_1fj,_1sj.b))));if(!_1sk._){return E(_1fh);}else{if(!E(_1sk.b)._){if(_1sd!=E(_1sk.a)){return false;}else{_1sg=_1si;continue;}}else{return E(_1fi);}}break;default:_1sg=_1si;continue;}}}}};return new F(function(){return _1sf(_1s3);});}}else{return E(_1fi);}}break;default:_1rZ=_1s3;return __continue;}}}})(_1rZ));if(_1s0!=__continue){return _1s0;}}};return (!B(_1rY(_1rp)))?(!B(_vi(_1rV,_1qN)))?new T2(0,_Z,_1qR):new T2(0,_1rl,_1qR):new T2(0,_1rl,_1qR);}};if(E(B(_1eK(_1rn,_1ro,_10m)))==63){if(!B(_ae(_1rU,_Z))){var _1sl=E(_1rU);if(!_1sl._){return E(_YH);}else{if(!B(_vi(_1rV,B(_YC(_1sl.a,_1sl.b))))){if(!B(_vi(_1rV,_1qN))){return new F(function(){return _1rq(_Z,_1qR);});}else{return new F(function(){return _1rq(_1rl,_1qR);});}}else{var _1sm=B(_1rW(_));return new F(function(){return _1rq(_1sm.a,_1sm.b);});}}}else{if(!B(_vi(_1rV,_1rU))){if(!B(_vi(_1rV,_1qN))){return new F(function(){return _1rq(_Z,_1qR);});}else{return new F(function(){return _1rq(_1rl,_1qR);});}}else{var _1sn=B(_1rW(_));return new F(function(){return _1rq(_1sn.a,_1sn.b);});}}}else{if(!B(_vi(_1rV,_1rU))){if(!B(_vi(_1rV,_1qN))){return new F(function(){return _1rq(_Z,_1qR);});}else{return new F(function(){return _1rq(_1rl,_1qR);});}}else{var _1so=B(_1rW(_));return new F(function(){return _1rq(_1so.a,_1so.b);});}}},_1sp=E(_1rk);if(!_1sp._){return E(_10m);}else{var _1sq=_1sp.a,_1sr=E(_1sp.b);if(!_1sr._){return new F(function(){return _1rm(_1sq,_Z,_Z);});}else{var _1ss=E(_1sq),_1st=new T(function(){var _1su=B(_LD(38,_1sr.a,_1sr.b));return new T2(0,_1su.a,_1su.b);});if(E(_1ss)==38){return E(_10m);}else{return new F(function(){return _1rm(_1ss,new T(function(){return E(E(_1st).a);}),new T(function(){return E(E(_1st).b);}));});}}}}},_1sv="]",_1sw="}",_1sx=":",_1sy=",",_1sz=new T(function(){return eval("JSON.stringify");}),_1sA="false",_1sB="null",_1sC="[",_1sD="{",_1sE="\"",_1sF="true",_1sG=function(_1sH,_1sI){var _1sJ=E(_1sI);switch(_1sJ._){case 0:return new T2(0,new T(function(){return jsShow(_1sJ.a);}),_1sH);case 1:return new T2(0,new T(function(){var _1sK=__app1(E(_1sz),_1sJ.a);return String(_1sK);}),_1sH);case 2:return (!E(_1sJ.a))?new T2(0,_1sA,_1sH):new T2(0,_1sF,_1sH);case 3:var _1sL=E(_1sJ.a);if(!_1sL._){return new T2(0,_1sC,new T2(1,_1sv,_1sH));}else{var _1sM=new T(function(){var _1sN=new T(function(){var _1sO=function(_1sP){var _1sQ=E(_1sP);if(!_1sQ._){return E(new T2(1,_1sv,_1sH));}else{var _1sR=new T(function(){var _1sS=B(_1sG(new T(function(){return B(_1sO(_1sQ.b));}),_1sQ.a));return new T2(1,_1sS.a,_1sS.b);});return new T2(1,_1sy,_1sR);}};return B(_1sO(_1sL.b));}),_1sT=B(_1sG(_1sN,_1sL.a));return new T2(1,_1sT.a,_1sT.b);});return new T2(0,_1sC,_1sM);}break;case 4:var _1sU=E(_1sJ.a);if(!_1sU._){return new T2(0,_1sD,new T2(1,_1sw,_1sH));}else{var _1sV=E(_1sU.a),_1sW=new T(function(){var _1sX=new T(function(){var _1sY=function(_1sZ){var _1t0=E(_1sZ);if(!_1t0._){return E(new T2(1,_1sw,_1sH));}else{var _1t1=E(_1t0.a),_1t2=new T(function(){var _1t3=B(_1sG(new T(function(){return B(_1sY(_1t0.b));}),_1t1.b));return new T2(1,_1t3.a,_1t3.b);});return new T2(1,_1sy,new T2(1,_1sE,new T2(1,_1t1.a,new T2(1,_1sE,new T2(1,_1sx,_1t2)))));}};return B(_1sY(_1sU.b));}),_1t4=B(_1sG(_1sX,_1sV.b));return new T2(1,_1t4.a,_1t4.b);});return new T2(0,_1sD,new T2(1,new T(function(){var _1t5=__app1(E(_1sz),E(_1sV.a));return String(_1t5);}),new T2(1,_1sx,_1sW)));}break;default:return new T2(0,_1sB,_1sH);}},_1t6=new T(function(){return toJSStr(_Z);}),_1t7=function(_1t8){var _1t9=B(_1sG(_Z,_1t8)),_1ta=jsCat(new T2(1,_1t9.a,_1t9.b),E(_1t6));return E(_1ta);},_1tb=function(_1tc){var _1td=E(_1tc);if(!_1td._){return new T2(0,_Z,_Z);}else{var _1te=E(_1td.a),_1tf=new T(function(){var _1tg=B(_1tb(_1td.b));return new T2(0,_1tg.a,_1tg.b);});return new T2(0,new T2(1,_1te.a,new T(function(){return E(E(_1tf).a);})),new T2(1,_1te.b,new T(function(){return E(E(_1tf).b);})));}},_1th=new T(function(){return B(unCStr("Rk"));}),_1ti=function(_1tj,_1tk,_1tl,_1tm,_1tn,_1to,_1tp,_1tq,_1tr,_1ts,_1tt,_1tu,_1tv,_1tw,_1tx,_1ty,_1tz,_1tA,_1tB,_1tC,_1tD,_1tE,_1tF,_1tG){while(1){var _1tH=B((function(_1tI,_1tJ,_1tK,_1tL,_1tM,_1tN,_1tO,_1tP,_1tQ,_1tR,_1tS,_1tT,_1tU,_1tV,_1tW,_1tX,_1tY,_1tZ,_1u0,_1u1,_1u2,_1u3,_1u4,_1u5){var _1u6=E(_1tI);if(!_1u6._){return {_:0,a:_1tJ,b:_1tK,c:_1tL,d:_1tM,e:_1tN,f:_1tO,g:_1tP,h:_1tQ,i:_1tR,j:_1tS,k:_1tT,l:_1tU,m:_1tV,n:_1tW,o:_1tX,p:_1tY,q:_1tZ,r:_1u0,s:_1u1,t:_1u2,u:_1u3,v:_1u4,w:_1u5};}else{var _1u7=_1u6.a,_1u8=B(_Z2(B(unAppCStr("e.e",new T2(1,_1u7,new T(function(){return B(unAppCStr(".m0:",new T2(1,_1u7,_1th)));})))),_1tJ,_1tK,_1tL,_1tM,_1tN,_1tO,_1tP,_1tQ,_1tR,_1tS,_1tT,_1tU,_1tV,_1tW,_1tX,_1tY,_1tZ,_1u0,_1u1,_1u2,_1u3,_1u4,_1u5));_1tj=_1u6.b;_1tk=_1u8.a;_1tl=_1u8.b;_1tm=_1u8.c;_1tn=_1u8.d;_1to=_1u8.e;_1tp=_1u8.f;_1tq=_1u8.g;_1tr=_1u8.h;_1ts=_1u8.i;_1tt=_1u8.j;_1tu=_1u8.k;_1tv=_1u8.l;_1tw=_1u8.m;_1tx=_1u8.n;_1ty=_1u8.o;_1tz=_1u8.p;_1tA=_1u8.q;_1tB=_1u8.r;_1tC=_1u8.s;_1tD=_1u8.t;_1tE=_1u8.u;_1tF=_1u8.v;_1tG=_1u8.w;return __continue;}})(_1tj,_1tk,_1tl,_1tm,_1tn,_1to,_1tp,_1tq,_1tr,_1ts,_1tt,_1tu,_1tv,_1tw,_1tx,_1ty,_1tz,_1tA,_1tB,_1tC,_1tD,_1tE,_1tF,_1tG));if(_1tH!=__continue){return _1tH;}}},_1u9=function(_1ua){var _1ub=E(_1ua);switch(_1ub){case 68:return 100;case 72:return 104;case 74:return 106;case 75:return 107;case 76:return 108;case 78:return 110;case 82:return 114;case 83:return 115;default:if(_1ub>>>0>1114111){return new F(function(){return _Be(_1ub);});}else{return _1ub;}}},_1uc=function(_1ud,_1ue,_1uf){while(1){var _1ug=E(_1ue);if(!_1ug._){return (E(_1uf)._==0)?true:false;}else{var _1uh=E(_1uf);if(!_1uh._){return false;}else{if(!B(A3(_4F,_1ud,_1ug.a,_1uh.a))){return false;}else{_1ue=_1ug.b;_1uf=_1uh.b;continue;}}}}},_1ui=function(_1uj,_1uk){return (!B(_1uc(_vT,_1uj,_1uk)))?true:false;},_1ul=function(_1um,_1un){return new F(function(){return _1uc(_vT,_1um,_1un);});},_1uo=new T2(0,_1ul,_1ui),_1up=function(_1uq){var _1ur=E(_1uq);if(!_1ur._){return new T2(0,_Z,_Z);}else{var _1us=E(_1ur.a),_1ut=new T(function(){var _1uu=B(_1up(_1ur.b));return new T2(0,_1uu.a,_1uu.b);});return new T2(0,new T2(1,_1us.a,new T(function(){return E(E(_1ut).a);})),new T2(1,_1us.b,new T(function(){return E(E(_1ut).b);})));}},_1uv=function(_1uw,_1ux){while(1){var _1uy=E(_1ux);if(!_1uy._){return __Z;}else{var _1uz=_1uy.b,_1uA=E(_1uw);if(_1uA==1){return E(_1uz);}else{_1uw=_1uA-1|0;_1ux=_1uz;continue;}}}},_1uB=function(_1uC,_1uD){while(1){var _1uE=E(_1uD);if(!_1uE._){return __Z;}else{var _1uF=_1uE.b,_1uG=E(_1uC);if(_1uG==1){return E(_1uF);}else{_1uC=_1uG-1|0;_1uD=_1uF;continue;}}}},_1uH=function(_1uI){return new F(function(){return _KS(_1uI,_Z);});},_1uJ=function(_1uK,_1uL,_1uM,_1uN){var _1uO=new T(function(){return B(_Rt(_l8,_1uL,_1uM));}),_1uP=new T(function(){var _1uQ=E(_1uO),_1uR=new T(function(){var _1uS=_1uQ+1|0;if(_1uS>0){return B(_1uB(_1uS,_1uM));}else{return E(_1uM);}});if(0>=_1uQ){return E(_1uR);}else{var _1uT=function(_1uU,_1uV){var _1uW=E(_1uU);if(!_1uW._){return E(_1uR);}else{var _1uX=_1uW.a,_1uY=E(_1uV);return (_1uY==1)?new T2(1,_1uX,_1uR):new T2(1,_1uX,new T(function(){return B(_1uT(_1uW.b,_1uY-1|0));}));}};return B(_1uT(_1uM,_1uQ));}}),_1uZ=new T(function(){var _1v0=E(_1uO),_1v1=new T(function(){if(E(_1uL)==94){return B(A2(_1uK,new T(function(){return B(_aS(_1uN,_1v0+1|0));}),new T(function(){return B(_aS(_1uN,_1v0));})));}else{return B(A2(_1uK,new T(function(){return B(_aS(_1uN,_1v0));}),new T(function(){return B(_aS(_1uN,_1v0+1|0));})));}}),_1v2=new T2(1,_1v1,new T(function(){var _1v3=_1v0+2|0;if(_1v3>0){return B(_1uv(_1v3,_1uN));}else{return E(_1uN);}}));if(0>=_1v0){return E(_1v2);}else{var _1v4=function(_1v5,_1v6){var _1v7=E(_1v5);if(!_1v7._){return E(_1v2);}else{var _1v8=_1v7.a,_1v9=E(_1v6);return (_1v9==1)?new T2(1,_1v8,_1v2):new T2(1,_1v8,new T(function(){return B(_1v4(_1v7.b,_1v9-1|0));}));}};return B(_1v4(_1uN,_1v0));}});return (E(_1uL)==94)?new T2(0,new T(function(){return B(_1uH(_1uP));}),new T(function(){return B(_1uH(_1uZ));})):new T2(0,_1uP,_1uZ);},_1va=new T(function(){return B(_go(_td,_tc));}),_1vb=function(_1vc,_1vd,_1ve){while(1){if(!E(_1va)){if(!B(_go(B(_197(_1vd,_td)),_tc))){if(!B(_go(_1vd,_eW))){var _1vf=B(_sG(_1vc,_1vc)),_1vg=B(_18S(B(_iP(_1vd,_eW)),_td)),_1vh=B(_sG(_1vc,_1ve));_1vc=_1vf;_1vd=_1vg;_1ve=_1vh;continue;}else{return new F(function(){return _sG(_1vc,_1ve);});}}else{var _1vf=B(_sG(_1vc,_1vc)),_1vg=B(_18S(_1vd,_td));_1vc=_1vf;_1vd=_1vg;continue;}}else{return E(_dV);}}},_1vi=function(_1vj,_1vk){while(1){if(!E(_1va)){if(!B(_go(B(_197(_1vk,_td)),_tc))){if(!B(_go(_1vk,_eW))){return new F(function(){return _1vb(B(_sG(_1vj,_1vj)),B(_18S(B(_iP(_1vk,_eW)),_td)),_1vj);});}else{return E(_1vj);}}else{var _1vl=B(_sG(_1vj,_1vj)),_1vm=B(_18S(_1vk,_td));_1vj=_1vl;_1vk=_1vm;continue;}}else{return E(_dV);}}},_1vn=function(_1vo,_1vp){if(!B(_h8(_1vp,_tc))){if(!B(_go(_1vp,_tc))){return new F(function(){return _1vi(_1vo,_1vp);});}else{return E(_eW);}}else{return E(_tS);}},_1vq=94,_1vr=45,_1vs=43,_1vt=42,_1vu=function(_1vv,_1vw){while(1){var _1vx=B((function(_1vy,_1vz){var _1vA=E(_1vz);if(!_1vA._){return __Z;}else{if((B(_qu(_1vy,0))+1|0)==B(_qu(_1vA,0))){if(!B(_4H(_l8,_1vq,_1vy))){if(!B(_4H(_l8,_1vt,_1vy))){if(!B(_4H(_l8,_1vs,_1vy))){if(!B(_4H(_l8,_1vr,_1vy))){return E(_1vA);}else{var _1vB=B(_1uJ(_iP,45,_1vy,_1vA));_1vv=_1vB.a;_1vw=_1vB.b;return __continue;}}else{var _1vC=B(_1uJ(_gw,43,_1vy,_1vA));_1vv=_1vC.a;_1vw=_1vC.b;return __continue;}}else{var _1vD=B(_1uJ(_sG,42,_1vy,_1vA));_1vv=_1vD.a;_1vw=_1vD.b;return __continue;}}else{var _1vE=B(_1uJ(_1vn,94,new T(function(){return B(_1uH(_1vy));}),new T(function(){return B(_KS(_1vA,_Z));})));_1vv=_1vE.a;_1vw=_1vE.b;return __continue;}}else{return __Z;}}})(_1vv,_1vw));if(_1vx!=__continue){return _1vx;}}},_1vF=function(_1vG){var _1vH=E(_1vG);if(!_1vH._){return new T2(0,_Z,_Z);}else{var _1vI=E(_1vH.a),_1vJ=new T(function(){var _1vK=B(_1vF(_1vH.b));return new T2(0,_1vK.a,_1vK.b);});return new T2(0,new T2(1,_1vI.a,new T(function(){return E(E(_1vJ).a);})),new T2(1,_1vI.b,new T(function(){return E(E(_1vJ).b);})));}},_1vL=new T(function(){return B(unCStr("0123456789+-"));}),_1vM=function(_1vN){while(1){var _1vO=E(_1vN);if(!_1vO._){return true;}else{if(!B(_4H(_l8,_1vO.a,_1vL))){return false;}else{_1vN=_1vO.b;continue;}}}},_1vP=new T(function(){return B(err(_wZ));}),_1vQ=new T(function(){return B(err(_x3));}),_1vR=function(_1vS,_1vT){var _1vU=function(_1vV,_1vW){var _1vX=function(_1vY){return new F(function(){return A1(_1vW,new T(function(){return B(_ju(_1vY));}));});},_1vZ=new T(function(){return B(_HH(function(_1w0){return new F(function(){return A3(_1vS,_1w0,_1vV,_1vX);});}));}),_1w1=function(_1w2){return E(_1vZ);},_1w3=function(_1w4){return new F(function(){return A2(_Go,_1w4,_1w1);});},_1w5=new T(function(){return B(_HH(function(_1w6){var _1w7=E(_1w6);if(_1w7._==4){var _1w8=E(_1w7.a);if(!_1w8._){return new F(function(){return A3(_1vS,_1w7,_1vV,_1vW);});}else{if(E(_1w8.a)==45){if(!E(_1w8.b)._){return E(new T1(1,_1w3));}else{return new F(function(){return A3(_1vS,_1w7,_1vV,_1vW);});}}else{return new F(function(){return A3(_1vS,_1w7,_1vV,_1vW);});}}}else{return new F(function(){return A3(_1vS,_1w7,_1vV,_1vW);});}}));}),_1w9=function(_1wa){return E(_1w5);};return new T1(1,function(_1wb){return new F(function(){return A2(_Go,_1wb,_1w9);});});};return new F(function(){return _Iy(_1vU,_1vT);});},_1wc=function(_1wd){var _1we=E(_1wd);if(_1we._==5){var _1wf=B(_Ku(_1we.a));return (_1wf._==0)?E(_Kz):function(_1wg,_1wh){return new F(function(){return A1(_1wh,_1wf.a);});};}else{return E(_Kz);}},_1wi=new T(function(){return B(A3(_1vR,_1wc,_Ie,_K1));}),_1wj=function(_1wk,_1wl){var _1wm=E(_1wl);if(!_1wm._){return __Z;}else{var _1wn=_1wm.a,_1wo=_1wm.b,_1wp=function(_1wq){var _1wr=B(_1vF(_1wk)),_1ws=_1wr.a;return (!B(_4H(_uF,_1wn,_1ws)))?__Z:new T2(1,new T(function(){return B(_aS(_1wr.b,B(_Rt(_uF,_1wn,_1ws))));}),new T(function(){return B(_1wj(_1wk,_1wo));}));};if(!B(_ae(_1wn,_Z))){if(!B(_1vM(_1wn))){return new F(function(){return _1wp(_);});}else{return new T2(1,new T(function(){var _1wt=B(_KL(B(_x8(_1wi,_1wn))));if(!_1wt._){return E(_1vP);}else{if(!E(_1wt.b)._){return E(_1wt.a);}else{return E(_1vQ);}}}),new T(function(){return B(_1wj(_1wk,_1wo));}));}}else{return new F(function(){return _1wp(_);});}}},_1wu=new T(function(){return B(unCStr("+-*^"));}),_1wv=new T(function(){return B(unCStr("0123456789"));}),_1ww=new T(function(){return B(_Q1("Siki.hs:12:9-28|(hn : ns, cs)"));}),_1wx=new T2(1,_Z,_Z),_1wy=function(_1wz){var _1wA=E(_1wz);if(!_1wA._){return new T2(0,_1wx,_Z);}else{var _1wB=_1wA.a,_1wC=new T(function(){var _1wD=B(_1wy(_1wA.b)),_1wE=E(_1wD.a);if(!_1wE._){return E(_1ww);}else{return new T3(0,_1wE.a,_1wE.b,_1wD.b);}});return (!B(_4H(_l8,_1wB,_1wv)))?(!B(_4H(_l8,_1wB,_1wu)))?new T2(0,new T2(1,new T2(1,_1wB,new T(function(){return E(E(_1wC).a);})),new T(function(){return E(E(_1wC).b);})),new T(function(){return E(E(_1wC).c);})):new T2(0,new T2(1,_Z,new T2(1,new T(function(){return E(E(_1wC).a);}),new T(function(){return E(E(_1wC).b);}))),new T2(1,_1wB,new T(function(){return E(E(_1wC).c);}))):new T2(0,new T2(1,new T2(1,_1wB,new T(function(){return E(E(_1wC).a);})),new T(function(){return E(E(_1wC).b);})),new T(function(){return E(E(_1wC).c);}));}},_1wF=function(_1wG,_1wH){var _1wI=new T(function(){var _1wJ=B(_1wy(_1wH)),_1wK=E(_1wJ.a);if(!_1wK._){return E(_1ww);}else{return new T3(0,_1wK.a,_1wK.b,_1wJ.b);}});return (!B(_4H(_l8,_1wG,_1wv)))?(!B(_4H(_l8,_1wG,_1wu)))?new T2(0,new T2(1,new T2(1,_1wG,new T(function(){return E(E(_1wI).a);})),new T(function(){return E(E(_1wI).b);})),new T(function(){return E(E(_1wI).c);})):new T2(0,new T2(1,_Z,new T2(1,new T(function(){return E(E(_1wI).a);}),new T(function(){return E(E(_1wI).b);}))),new T2(1,_1wG,new T(function(){return E(E(_1wI).c);}))):new T2(0,new T2(1,new T2(1,_1wG,new T(function(){return E(E(_1wI).a);})),new T(function(){return E(E(_1wI).b);})),new T(function(){return E(E(_1wI).c);}));},_1wL=function(_1wM,_1wN){while(1){var _1wO=E(_1wM);if(!_1wO._){return E(_1wN);}else{_1wM=_1wO.b;_1wN=_1wO.a;continue;}}},_1wP=function(_1wQ,_1wR,_1wS){return new F(function(){return _1wL(_1wR,_1wQ);});},_1wT=function(_1wU,_1wV){var _1wW=E(_1wV);if(!_1wW._){return __Z;}else{var _1wX=B(_1wF(_1wW.a,_1wW.b)),_1wY=B(_1vu(_1wX.b,B(_1wj(_1wU,_1wX.a))));if(!_1wY._){return E(_1wW);}else{return new F(function(){return _1bb(0,B(_1wP(_1wY.a,_1wY.b,_10m)),_Z);});}}},_1wZ=function(_1x0,_1x1){var _1x2=function(_1x3,_1x4){while(1){var _1x5=B((function(_1x6,_1x7){var _1x8=E(_1x7);if(!_1x8._){return (!B(_vi(_1x6,_Z)))?new T2(0,_B4,_1x6):new T2(0,_B3,_Z);}else{var _1x9=_1x8.b,_1xa=B(_1up(_1x8.a)).a;if(!B(_4H(_l8,_1gL,_1xa))){var _1xb=_1x6;_1x3=_1xb;_1x4=_1x9;return __continue;}else{var _1xc=B(_1hh(_1xa)),_1xd=_1xc.a,_1xe=_1xc.b;if(!B(_ae(_1xe,_Z))){if(!B(_vi(B(_1wT(_1x0,_1xd)),B(_1wT(_1x0,_1xe))))){return new T2(0,_B3,_Z);}else{var _1xf=new T(function(){if(!B(_vi(_1x6,_Z))){return B(_x(_1x6,new T(function(){return B(unAppCStr(" ",_1xd));},1)));}else{return E(_1xd);}});_1x3=_1xf;_1x4=_1x9;return __continue;}}else{return new T2(0,_B3,_Z);}}}})(_1x3,_1x4));if(_1x5!=__continue){return _1x5;}}};return new F(function(){return _1x2(_Z,_1x1);});},_1xg=function(_1xh,_1xi){var _1xj=new T(function(){var _1xk=B(_KL(B(_x8(_1b1,new T(function(){return B(_uf(3,B(_H(0,imul(E(_1xi),E(_1xh)-1|0)|0,_Z))));})))));if(!_1xk._){return E(_1b0);}else{if(!E(_1xk.b)._){return E(_1xk.a);}else{return E(_1aZ);}}});return new T2(0,new T(function(){return B(_ew(_1xj,_1xh));}),_1xj);},_1xl=function(_1xm,_1xn){while(1){var _1xo=E(_1xn);if(!_1xo._){return __Z;}else{var _1xp=_1xo.b,_1xq=E(_1xm);if(_1xq==1){return E(_1xp);}else{_1xm=_1xq-1|0;_1xn=_1xp;continue;}}}},_1xr=function(_1xs,_1xt){while(1){var _1xu=E(_1xt);if(!_1xu._){return __Z;}else{var _1xv=_1xu.b,_1xw=E(_1xs);if(_1xw==1){return E(_1xv);}else{_1xs=_1xw-1|0;_1xt=_1xv;continue;}}}},_1xx=64,_1xy=new T2(1,_1xx,_Z),_1xz=function(_1xA,_1xB,_1xC,_1xD){return (!B(_vi(_1xA,_1xC)))?true:(!B(_go(_1xB,_1xD)))?true:false;},_1xE=function(_1xF,_1xG){var _1xH=E(_1xF),_1xI=E(_1xG);return new F(function(){return _1xz(_1xH.a,_1xH.b,_1xI.a,_1xI.b);});},_1xJ=function(_1xK,_1xL,_1xM,_1xN){if(!B(_vi(_1xK,_1xM))){return false;}else{return new F(function(){return _go(_1xL,_1xN);});}},_1xO=function(_1xP,_1xQ){var _1xR=E(_1xP),_1xS=E(_1xQ);return new F(function(){return _1xJ(_1xR.a,_1xR.b,_1xS.a,_1xS.b);});},_1xT=new T2(0,_1xO,_1xE),_1xU=function(_1xV){var _1xW=E(_1xV);if(!_1xW._){return new T2(0,_Z,_Z);}else{var _1xX=E(_1xW.a),_1xY=new T(function(){var _1xZ=B(_1xU(_1xW.b));return new T2(0,_1xZ.a,_1xZ.b);});return new T2(0,new T2(1,_1xX.a,new T(function(){return E(E(_1xY).a);})),new T2(1,_1xX.b,new T(function(){return E(E(_1xY).b);})));}},_1y0=function(_1y1){var _1y2=E(_1y1);if(!_1y2._){return new T2(0,_Z,_Z);}else{var _1y3=E(_1y2.a),_1y4=new T(function(){var _1y5=B(_1y0(_1y2.b));return new T2(0,_1y5.a,_1y5.b);});return new T2(0,new T2(1,_1y3.a,new T(function(){return E(E(_1y4).a);})),new T2(1,_1y3.b,new T(function(){return E(E(_1y4).b);})));}},_1y6=function(_1y7){var _1y8=E(_1y7);if(!_1y8._){return new T2(0,_Z,_Z);}else{var _1y9=E(_1y8.a),_1ya=new T(function(){var _1yb=B(_1y6(_1y8.b));return new T2(0,_1yb.a,_1yb.b);});return new T2(0,new T2(1,_1y9.a,new T(function(){return E(E(_1ya).a);})),new T2(1,_1y9.b,new T(function(){return E(E(_1ya).b);})));}},_1yc=function(_1yd,_1ye){return (_1yd<=_1ye)?new T2(1,_1yd,new T(function(){return B(_1yc(_1yd+1|0,_1ye));})):__Z;},_1yf=new T(function(){return B(_1yc(65,90));}),_1yg=function(_1yh){return (_1yh<=122)?new T2(1,_1yh,new T(function(){return B(_1yg(_1yh+1|0));})):E(_1yf);},_1yi=new T(function(){return B(_1yg(97));}),_1yj=function(_1yk){while(1){var _1yl=E(_1yk);if(!_1yl._){return true;}else{if(!B(_4H(_l8,_1yl.a,_1yi))){return false;}else{_1yk=_1yl.b;continue;}}}},_1ym=new T2(0,_Z,_Z),_1yn=new T(function(){return B(err(_wZ));}),_1yo=new T(function(){return B(err(_x3));}),_1yp=new T(function(){return B(A3(_1vR,_1wc,_Ie,_K1));}),_1yq=function(_1yr,_1ys,_1yt){while(1){var _1yu=B((function(_1yv,_1yw,_1yx){var _1yy=E(_1yx);if(!_1yy._){return __Z;}else{var _1yz=_1yy.b,_1yA=B(_1y0(_1yw)),_1yB=_1yA.a,_1yC=B(_1xU(_1yB)),_1yD=_1yC.a,_1yE=new T(function(){return E(B(_1y6(_1yy.a)).a);}),_1yF=new T(function(){return B(_4H(_l8,_1gL,_1yE));}),_1yG=new T(function(){if(!E(_1yF)){return E(_1ym);}else{var _1yH=B(_1hh(_1yE));return new T2(0,_1yH.a,_1yH.b);}}),_1yI=new T(function(){return E(E(_1yG).a);}),_1yJ=new T(function(){return B(_Rt(_uF,_1yI,_1yD));}),_1yK=new T(function(){var _1yL=function(_){var _1yM=B(_qu(_1yw,0))-1|0,_1yN=function(_1yO){if(_1yO>=0){var _1yP=newArr(_1yO,_1c8),_1yQ=_1yP,_1yR=E(_1yO);if(!_1yR){return new T4(0,E(_1fk),E(_1yM),0,_1yQ);}else{var _1yS=function(_1yT,_1yU,_){while(1){var _1yV=E(_1yT);if(!_1yV._){return E(_);}else{var _=_1yQ[_1yU]=_1yV.a;if(_1yU!=(_1yR-1|0)){var _1yW=_1yU+1|0;_1yT=_1yV.b;_1yU=_1yW;continue;}else{return E(_);}}}},_=B(_1yS(_1yA.b,0,_));return new T4(0,E(_1fk),E(_1yM),_1yR,_1yQ);}}else{return E(_1d2);}};if(0>_1yM){return new F(function(){return _1yN(0);});}else{return new F(function(){return _1yN(_1yM+1|0);});}};return B(_1d3(_1yL));});if(!B(_4H(_uF,_1yI,_1yD))){var _1yX=false;}else{var _1yY=E(_1yK),_1yZ=E(_1yY.a),_1z0=E(_1yY.b),_1z1=E(_1yJ);if(_1yZ>_1z1){var _1z2=B(_1mH(_1z1,_1yZ,_1z0));}else{if(_1z1>_1z0){var _1z3=B(_1mH(_1z1,_1yZ,_1z0));}else{var _1z3=E(_1yY.d[_1z1-_1yZ|0])==E(_1yv);}var _1z2=_1z3;}var _1yX=_1z2;}var _1z4=new T(function(){return E(E(_1yG).b);}),_1z5=new T(function(){return B(_Rt(_uF,_1z4,_1yD));}),_1z6=new T(function(){if(!B(_4H(_uF,_1z4,_1yD))){return false;}else{var _1z7=E(_1yK),_1z8=E(_1z7.a),_1z9=E(_1z7.b),_1za=E(_1z5);if(_1z8>_1za){return B(_1mH(_1za,_1z8,_1z9));}else{if(_1za>_1z9){return B(_1mH(_1za,_1z8,_1z9));}else{return E(_1z7.d[_1za-_1z8|0])==E(_1yv);}}}}),_1zb=new T(function(){var _1zc=function(_){var _1zd=B(_qu(_1yB,0))-1|0,_1ze=function(_1zf){if(_1zf>=0){var _1zg=newArr(_1zf,_1c8),_1zh=_1zg,_1zi=E(_1zf);if(!_1zi){return new T4(0,E(_1fk),E(_1zd),0,_1zh);}else{var _1zj=function(_1zk,_1zl,_){while(1){var _1zm=E(_1zk);if(!_1zm._){return E(_);}else{var _=_1zh[_1zl]=_1zm.a;if(_1zl!=(_1zi-1|0)){var _1zn=_1zl+1|0;_1zk=_1zm.b;_1zl=_1zn;continue;}else{return E(_);}}}},_=B(_1zj(_1yC.b,0,_));return new T4(0,E(_1fk),E(_1zd),_1zi,_1zh);}}else{return E(_1d2);}};if(0>_1zd){return new F(function(){return _1ze(0);});}else{return new F(function(){return _1ze(_1zd+1|0);});}};return B(_1d3(_1zc));}),_1zo=function(_1zp){var _1zq=function(_1zr){return (!E(_1yX))?__Z:(!E(_1z6))?__Z:new T2(1,new T2(0,_1yI,new T(function(){var _1zs=E(_1zb),_1zt=E(_1zs.a),_1zu=E(_1zs.b),_1zv=E(_1yJ);if(_1zt>_1zv){return B(_1mH(_1zv,_1zt,_1zu));}else{if(_1zv>_1zu){return B(_1mH(_1zv,_1zt,_1zu));}else{return E(_1zs.d[_1zv-_1zt|0]);}}})),new T2(1,new T2(0,_1z4,new T(function(){var _1zw=E(_1zb),_1zx=E(_1zw.a),_1zy=E(_1zw.b),_1zz=E(_1z5);if(_1zx>_1zz){return B(_1mH(_1zz,_1zx,_1zy));}else{if(_1zz>_1zy){return B(_1mH(_1zz,_1zx,_1zy));}else{return E(_1zw.d[_1zz-_1zx|0]);}}})),_Z));};if(!E(_1yX)){if(!E(_1z6)){return new F(function(){return _1zq(_);});}else{return new T2(1,new T2(0,_1z4,new T(function(){var _1zA=E(_1zb),_1zB=E(_1zA.a),_1zC=E(_1zA.b),_1zD=E(_1z5);if(_1zB>_1zD){return B(_1mH(_1zD,_1zB,_1zC));}else{if(_1zD>_1zC){return B(_1mH(_1zD,_1zB,_1zC));}else{return E(_1zA.d[_1zD-_1zB|0]);}}})),_Z);}}else{return new F(function(){return _1zq(_);});}};if(!E(_1yX)){var _1zE=B(_1zo(_));}else{if(!E(_1z6)){var _1zF=new T2(1,new T2(0,_1yI,new T(function(){var _1zG=E(_1zb),_1zH=E(_1zG.a),_1zI=E(_1zG.b),_1zJ=E(_1yJ);if(_1zH>_1zJ){return B(_1mH(_1zJ,_1zH,_1zI));}else{if(_1zJ>_1zI){return B(_1mH(_1zJ,_1zH,_1zI));}else{return E(_1zG.d[_1zJ-_1zH|0]);}}})),_Z);}else{var _1zF=B(_1zo(_));}var _1zE=_1zF;}if(!B(_1uc(_1xT,_1zE,_Z))){return new F(function(){return _x(_1zE,new T(function(){return B(_1yq(_1yv,_1yw,_1yz));},1));});}else{if(!E(_1yF)){var _1zK=_1yv,_1zL=_1yw;_1yr=_1zK;_1ys=_1zL;_1yt=_1yz;return __continue;}else{if(!B(_1yj(_1yI))){if(!B(_1yj(_1z4))){var _1zK=_1yv,_1zL=_1yw;_1yr=_1zK;_1ys=_1zL;_1yt=_1yz;return __continue;}else{if(!E(_1yX)){if(!E(_1z6)){if(!B(_ae(_1yI,_Z))){if(!B(_1vM(_1yI))){var _1zK=_1yv,_1zL=_1yw;_1yr=_1zK;_1ys=_1zL;_1yt=_1yz;return __continue;}else{return new T2(1,new T2(0,_1z4,new T(function(){var _1zM=B(_KL(B(_x8(_1yp,_1yI))));if(!_1zM._){return E(_1yn);}else{if(!E(_1zM.b)._){return E(_1zM.a);}else{return E(_1yo);}}})),new T(function(){return B(_1yq(_1yv,_1yw,_1yz));}));}}else{var _1zK=_1yv,_1zL=_1yw;_1yr=_1zK;_1ys=_1zL;_1yt=_1yz;return __continue;}}else{var _1zK=_1yv,_1zL=_1yw;_1yr=_1zK;_1ys=_1zL;_1yt=_1yz;return __continue;}}else{var _1zK=_1yv,_1zL=_1yw;_1yr=_1zK;_1ys=_1zL;_1yt=_1yz;return __continue;}}}else{if(!E(_1yX)){if(!E(_1z6)){if(!B(_ae(_1z4,_Z))){if(!B(_1vM(_1z4))){if(!B(_1yj(_1z4))){var _1zK=_1yv,_1zL=_1yw;_1yr=_1zK;_1ys=_1zL;_1yt=_1yz;return __continue;}else{if(!B(_ae(_1yI,_Z))){if(!B(_1vM(_1yI))){var _1zK=_1yv,_1zL=_1yw;_1yr=_1zK;_1ys=_1zL;_1yt=_1yz;return __continue;}else{return new T2(1,new T2(0,_1z4,new T(function(){var _1zN=B(_KL(B(_x8(_1yp,_1yI))));if(!_1zN._){return E(_1yn);}else{if(!E(_1zN.b)._){return E(_1zN.a);}else{return E(_1yo);}}})),new T(function(){return B(_1yq(_1yv,_1yw,_1yz));}));}}else{var _1zK=_1yv,_1zL=_1yw;_1yr=_1zK;_1ys=_1zL;_1yt=_1yz;return __continue;}}}else{return new T2(1,new T2(0,_1yI,new T(function(){var _1zO=B(_KL(B(_x8(_1yp,_1z4))));if(!_1zO._){return E(_1yn);}else{if(!E(_1zO.b)._){return E(_1zO.a);}else{return E(_1yo);}}})),new T(function(){return B(_1yq(_1yv,_1yw,_1yz));}));}}else{if(!B(_1yj(_1z4))){var _1zK=_1yv,_1zL=_1yw;_1yr=_1zK;_1ys=_1zL;_1yt=_1yz;return __continue;}else{if(!B(_ae(_1yI,_Z))){if(!B(_1vM(_1yI))){var _1zK=_1yv,_1zL=_1yw;_1yr=_1zK;_1ys=_1zL;_1yt=_1yz;return __continue;}else{return new T2(1,new T2(0,_1z4,new T(function(){var _1zP=B(_KL(B(_x8(_1yp,_1yI))));if(!_1zP._){return E(_1yn);}else{if(!E(_1zP.b)._){return E(_1zP.a);}else{return E(_1yo);}}})),new T(function(){return B(_1yq(_1yv,_1yw,_1yz));}));}}else{var _1zK=_1yv,_1zL=_1yw;_1yr=_1zK;_1ys=_1zL;_1yt=_1yz;return __continue;}}}}else{var _1zQ=B(_1yj(_1z4)),_1zK=_1yv,_1zL=_1yw;_1yr=_1zK;_1ys=_1zL;_1yt=_1yz;return __continue;}}else{var _1zR=B(_1yj(_1z4)),_1zK=_1yv,_1zL=_1yw;_1yr=_1zK;_1ys=_1zL;_1yt=_1yz;return __continue;}}}}}})(_1yr,_1ys,_1yt));if(_1yu!=__continue){return _1yu;}}},_1zS=102,_1zT=101,_1zU=new T(function(){return B(unCStr("=="));}),_1zV=new T(function(){return B(_i8("Action.hs:(103,17)-(107,70)|case"));}),_1zW=new T(function(){return B(_i8("Action.hs:(118,9)-(133,75)|function wnMove\'"));}),_1zX=5,_1zY=117,_1zZ=98,_1A0=110,_1A1=118,_1A2=function(_1A3,_1A4,_1A5,_1A6,_1A7,_1A8,_1A9,_1Aa,_1Ab,_1Ac,_1Ad,_1Ae,_1Af,_1Ag){var _1Ah=B(_aS(B(_aS(_1A7,_1A4)),_1A3)),_1Ai=_1Ah.a,_1Aj=_1Ah.b;if(E(_1Aa)==32){if(!B(_4H(_l8,_1Ai,_1xy))){var _1Ak=false;}else{switch(E(_1Aj)){case 0:var _1Al=true;break;case 1:var _1Al=false;break;case 2:var _1Al=false;break;case 3:var _1Al=false;break;case 4:var _1Al=false;break;case 5:var _1Al=false;break;case 6:var _1Al=false;break;case 7:var _1Al=false;break;default:var _1Al=false;}var _1Ak=_1Al;}var _1Am=_1Ak;}else{var _1Am=false;}if(E(_1Aa)==32){if(E(_1Ai)==32){var _1An=false;}else{switch(E(_1Aj)){case 0:if(!E(_1Am)){var _1Ao=true;}else{var _1Ao=false;}var _1Ap=_1Ao;break;case 1:var _1Ap=false;break;case 2:var _1Ap=false;break;case 3:var _1Ap=false;break;case 4:var _1Ap=false;break;case 5:var _1Ap=false;break;case 6:var _1Ap=false;break;case 7:var _1Ap=false;break;default:if(!E(_1Am)){var _1Aq=true;}else{var _1Aq=false;}var _1Ap=_1Aq;}var _1An=_1Ap;}var _1Ar=_1An;}else{var _1Ar=false;}var _1As=new T(function(){return B(_PA(_1A3,_1A4,new T(function(){if(!E(_1Ar)){if(!E(_1Am)){return E(_1Ai);}else{return _1A9;}}else{return E(_12l);}}),_1Aj,_1A7));});switch(E(_1Aj)){case 3:var _1At=true;break;case 4:if(E(_1Aa)==32){var _1Au=true;}else{var _1Au=false;}var _1At=_1Au;break;default:var _1At=false;}if(!E(_1At)){var _1Av=E(_1As);}else{var _1Aw=E(_1A5),_1Ax=new T(function(){return B(_aS(_1As,_1A4));}),_1Ay=function(_1Az,_1AA){var _1AB=E(_1Az);if(_1AB==( -1)){return E(_1As);}else{var _1AC=new T(function(){return B(_PA(_1A3,_1A4,_12l,_IJ,_1As));}),_1AD=E(_1AA);if(_1AD==( -1)){var _1AE=__Z;}else{var _1AE=B(_aS(_1AC,_1AD));}if(E(B(_aS(_1AE,_1AB)).a)==32){var _1AF=new T(function(){var _1AG=new T(function(){return B(_aS(_1Ax,_1A3));}),_1AH=new T2(1,new T2(0,new T(function(){return E(E(_1AG).a);}),new T(function(){return E(E(_1AG).b);})),new T(function(){var _1AI=_1AB+1|0;if(_1AI>0){return B(_1xr(_1AI,_1AE));}else{return E(_1AE);}}));if(0>=_1AB){return E(_1AH);}else{var _1AJ=function(_1AK,_1AL){var _1AM=E(_1AK);if(!_1AM._){return E(_1AH);}else{var _1AN=_1AM.a,_1AO=E(_1AL);return (_1AO==1)?new T2(1,_1AN,_1AH):new T2(1,_1AN,new T(function(){return B(_1AJ(_1AM.b,_1AO-1|0));}));}};return B(_1AJ(_1AE,_1AB));}}),_1AP=new T2(1,_1AF,new T(function(){var _1AQ=_1AA+1|0;if(_1AQ>0){return B(_1xl(_1AQ,_1AC));}else{return E(_1AC);}}));if(0>=_1AA){return E(_1AP);}else{var _1AR=function(_1AS,_1AT){var _1AU=E(_1AS);if(!_1AU._){return E(_1AP);}else{var _1AV=_1AU.a,_1AW=E(_1AT);return (_1AW==1)?new T2(1,_1AV,_1AP):new T2(1,_1AV,new T(function(){return B(_1AR(_1AU.b,_1AW-1|0));}));}};return new F(function(){return _1AR(_1AC,_1AA);});}}else{return E(_1As);}}};if(_1A3<=_1Aw){if(_1Aw<=_1A3){var _1AX=E(_1A6);if(_1A4<=_1AX){if(_1AX<=_1A4){var _1AY=E(_1zV);}else{var _1AZ=E(_1A4);if(!_1AZ){var _1B0=B(_1Ay( -1, -1));}else{var _1B0=B(_1Ay(_1A3,_1AZ-1|0));}var _1AY=_1B0;}var _1B1=_1AY;}else{if(_1A4!=(B(_qu(_1As,0))-1|0)){var _1B2=B(_1Ay(_1A3,_1A4+1|0));}else{var _1B2=B(_1Ay( -1, -1));}var _1B1=_1B2;}var _1B3=_1B1;}else{var _1B4=E(_1A3);if(!_1B4){var _1B5=B(_1Ay( -1, -1));}else{var _1B5=B(_1Ay(_1B4-1|0,_1A4));}var _1B3=_1B5;}var _1B6=_1B3;}else{if(_1A3!=(B(_qu(_1Ax,0))-1|0)){var _1B7=B(_1Ay(_1A3+1|0,_1A4));}else{var _1B7=B(_1Ay( -1, -1));}var _1B6=_1B7;}var _1Av=_1B6;}if(!E(_1Af)){var _1B8=E(_1Av);}else{var _1B9=new T(function(){var _1Ba=E(_1Av);if(!_1Ba._){return E(_ri);}else{return B(_qu(_1Ba.a,0));}}),_1Bb=new T(function(){return B(_qu(_1Av,0));}),_1Bc=function(_1Bd,_1Be,_1Bf,_1Bg,_1Bh,_1Bi,_1Bj){while(1){var _1Bk=B((function(_1Bl,_1Bm,_1Bn,_1Bo,_1Bp,_1Bq,_1Br){var _1Bs=E(_1Br);if(!_1Bs._){return E(_1Bo);}else{var _1Bt=_1Bs.b,_1Bu=E(_1Bs.a);if(!_1Bu._){return E(_1zW);}else{var _1Bv=_1Bu.b,_1Bw=E(_1Bu.a);if(E(_1Bw.b)==5){var _1Bx=new T(function(){var _1By=B(_1xg(_1zX,_1Bl));return new T2(0,_1By.a,_1By.b);}),_1Bz=new T(function(){var _1BA=function(_1BB,_1BC){var _1BD=function(_1BE){return new F(function(){return _PA(_1Bm,_1Bn,_12l,_IJ,new T(function(){return B(_PA(_1BB,_1BC,_1Bw.a,_Jy,_1Bo));}));});};if(_1BB!=_1Bm){return new F(function(){return _1BD(_);});}else{if(_1BC!=_1Bn){return new F(function(){return _1BD(_);});}else{return E(_1Bo);}}};switch(E(E(_1Bx).a)){case 1:var _1BF=_1Bm-1|0;if(_1BF<0){return B(_1BA(_1Bm,_1Bn));}else{if(_1BF>=E(_1B9)){return B(_1BA(_1Bm,_1Bn));}else{if(_1Bn<0){return B(_1BA(_1Bm,_1Bn));}else{if(_1Bn>=E(_1Bb)){return B(_1BA(_1Bm,_1Bn));}else{if(_1BF!=_1Bp){if(E(B(_aS(B(_aS(_1Bo,_1Bn)),_1BF)).a)==32){return B(_1BA(_1BF,_1Bn));}else{return B(_1BA(_1Bm,_1Bn));}}else{if(_1Bn!=_1Bq){if(E(B(_aS(B(_aS(_1Bo,_1Bn)),_1BF)).a)==32){return B(_1BA(_1BF,_1Bn));}else{return B(_1BA(_1Bm,_1Bn));}}else{return B(_1BA(_1Bm,_1Bn));}}}}}}break;case 2:if(_1Bm<0){return B(_1BA(_1Bm,_1Bn));}else{if(_1Bm>=E(_1B9)){return B(_1BA(_1Bm,_1Bn));}else{var _1BG=_1Bn-1|0;if(_1BG<0){return B(_1BA(_1Bm,_1Bn));}else{if(_1BG>=E(_1Bb)){return B(_1BA(_1Bm,_1Bn));}else{if(_1Bm!=_1Bp){if(E(B(_aS(B(_aS(_1Bo,_1BG)),_1Bm)).a)==32){return B(_1BA(_1Bm,_1BG));}else{return B(_1BA(_1Bm,_1Bn));}}else{if(_1BG!=_1Bq){if(E(B(_aS(B(_aS(_1Bo,_1BG)),_1Bm)).a)==32){return B(_1BA(_1Bm,_1BG));}else{return B(_1BA(_1Bm,_1Bn));}}else{return B(_1BA(_1Bm,_1Bn));}}}}}}break;case 3:var _1BH=_1Bm+1|0;if(_1BH<0){return B(_1BA(_1Bm,_1Bn));}else{if(_1BH>=E(_1B9)){return B(_1BA(_1Bm,_1Bn));}else{if(_1Bn<0){return B(_1BA(_1Bm,_1Bn));}else{if(_1Bn>=E(_1Bb)){return B(_1BA(_1Bm,_1Bn));}else{if(_1BH!=_1Bp){if(E(B(_aS(B(_aS(_1Bo,_1Bn)),_1BH)).a)==32){return B(_1BA(_1BH,_1Bn));}else{return B(_1BA(_1Bm,_1Bn));}}else{if(_1Bn!=_1Bq){if(E(B(_aS(B(_aS(_1Bo,_1Bn)),_1BH)).a)==32){return B(_1BA(_1BH,_1Bn));}else{return B(_1BA(_1Bm,_1Bn));}}else{return B(_1BA(_1Bm,_1Bn));}}}}}}break;case 4:if(_1Bm<0){return B(_1BA(_1Bm,_1Bn));}else{if(_1Bm>=E(_1B9)){return B(_1BA(_1Bm,_1Bn));}else{var _1BI=_1Bn+1|0;if(_1BI<0){return B(_1BA(_1Bm,_1Bn));}else{if(_1BI>=E(_1Bb)){return B(_1BA(_1Bm,_1Bn));}else{if(_1Bm!=_1Bp){if(E(B(_aS(B(_aS(_1Bo,_1BI)),_1Bm)).a)==32){return B(_1BA(_1Bm,_1BI));}else{return B(_1BA(_1Bm,_1Bn));}}else{if(_1BI!=_1Bq){if(E(B(_aS(B(_aS(_1Bo,_1BI)),_1Bm)).a)==32){return B(_1BA(_1Bm,_1BI));}else{return B(_1BA(_1Bm,_1Bn));}}else{return B(_1BA(_1Bm,_1Bn));}}}}}}break;default:if(_1Bm<0){return B(_1BA(_1Bm,_1Bn));}else{if(_1Bm>=E(_1B9)){return B(_1BA(_1Bm,_1Bn));}else{if(_1Bn<0){return B(_1BA(_1Bm,_1Bn));}else{if(_1Bn>=E(_1Bb)){return B(_1BA(_1Bm,_1Bn));}else{if(_1Bm!=_1Bp){var _1BJ=E(B(_aS(B(_aS(_1Bo,_1Bn)),_1Bm)).a);return B(_1BA(_1Bm,_1Bn));}else{if(_1Bn!=_1Bq){var _1BK=E(B(_aS(B(_aS(_1Bo,_1Bn)),_1Bm)).a);return B(_1BA(_1Bm,_1Bn));}else{return B(_1BA(_1Bm,_1Bn));}}}}}}}}),_1BL=E(_1Bv);if(!_1BL._){var _1BM=_1Bn+1|0,_1BN=_1Bp,_1BO=_1Bq;_1Bd=new T(function(){return E(E(_1Bx).b);},1);_1Be=0;_1Bf=_1BM;_1Bg=_1Bz;_1Bh=_1BN;_1Bi=_1BO;_1Bj=_1Bt;return __continue;}else{return new F(function(){return _1BP(new T(function(){return E(E(_1Bx).b);},1),_1Bm+1|0,_1Bn,_1Bz,_1Bp,_1Bq,_1BL.a,_1BL.b,_1Bt);});}}else{var _1BQ=E(_1Bv);if(!_1BQ._){var _1BR=_1Bl,_1BM=_1Bn+1|0,_1BS=_1Bo,_1BN=_1Bp,_1BO=_1Bq;_1Bd=_1BR;_1Be=0;_1Bf=_1BM;_1Bg=_1BS;_1Bh=_1BN;_1Bi=_1BO;_1Bj=_1Bt;return __continue;}else{return new F(function(){return _1BP(_1Bl,_1Bm+1|0,_1Bn,_1Bo,_1Bp,_1Bq,_1BQ.a,_1BQ.b,_1Bt);});}}}}})(_1Bd,_1Be,_1Bf,_1Bg,_1Bh,_1Bi,_1Bj));if(_1Bk!=__continue){return _1Bk;}}},_1BP=function(_1BT,_1BU,_1BV,_1BW,_1BX,_1BY,_1BZ,_1C0,_1C1){while(1){var _1C2=B((function(_1C3,_1C4,_1C5,_1C6,_1C7,_1C8,_1C9,_1Ca,_1Cb){var _1Cc=E(_1C9);if(E(_1Cc.b)==5){var _1Cd=new T(function(){var _1Ce=B(_1xg(_1zX,_1C3));return new T2(0,_1Ce.a,_1Ce.b);}),_1Cf=new T(function(){var _1Cg=function(_1Ch,_1Ci){var _1Cj=function(_1Ck){return new F(function(){return _PA(_1C4,_1C5,_12l,_IJ,new T(function(){return B(_PA(_1Ch,_1Ci,_1Cc.a,_Jy,_1C6));}));});};if(_1Ch!=_1C4){return new F(function(){return _1Cj(_);});}else{if(_1Ci!=_1C5){return new F(function(){return _1Cj(_);});}else{return E(_1C6);}}};switch(E(E(_1Cd).a)){case 1:var _1Cl=_1C4-1|0;if(_1Cl<0){return B(_1Cg(_1C4,_1C5));}else{if(_1Cl>=E(_1B9)){return B(_1Cg(_1C4,_1C5));}else{if(_1C5<0){return B(_1Cg(_1C4,_1C5));}else{if(_1C5>=E(_1Bb)){return B(_1Cg(_1C4,_1C5));}else{if(_1Cl!=_1C7){if(E(B(_aS(B(_aS(_1C6,_1C5)),_1Cl)).a)==32){return B(_1Cg(_1Cl,_1C5));}else{return B(_1Cg(_1C4,_1C5));}}else{if(_1C5!=_1C8){if(E(B(_aS(B(_aS(_1C6,_1C5)),_1Cl)).a)==32){return B(_1Cg(_1Cl,_1C5));}else{return B(_1Cg(_1C4,_1C5));}}else{return B(_1Cg(_1C4,_1C5));}}}}}}break;case 2:if(_1C4<0){return B(_1Cg(_1C4,_1C5));}else{if(_1C4>=E(_1B9)){return B(_1Cg(_1C4,_1C5));}else{var _1Cm=_1C5-1|0;if(_1Cm<0){return B(_1Cg(_1C4,_1C5));}else{if(_1Cm>=E(_1Bb)){return B(_1Cg(_1C4,_1C5));}else{if(_1C4!=_1C7){if(E(B(_aS(B(_aS(_1C6,_1Cm)),_1C4)).a)==32){return B(_1Cg(_1C4,_1Cm));}else{return B(_1Cg(_1C4,_1C5));}}else{if(_1Cm!=_1C8){if(E(B(_aS(B(_aS(_1C6,_1Cm)),_1C4)).a)==32){return B(_1Cg(_1C4,_1Cm));}else{return B(_1Cg(_1C4,_1C5));}}else{return B(_1Cg(_1C4,_1C5));}}}}}}break;case 3:var _1Cn=_1C4+1|0;if(_1Cn<0){return B(_1Cg(_1C4,_1C5));}else{if(_1Cn>=E(_1B9)){return B(_1Cg(_1C4,_1C5));}else{if(_1C5<0){return B(_1Cg(_1C4,_1C5));}else{if(_1C5>=E(_1Bb)){return B(_1Cg(_1C4,_1C5));}else{if(_1Cn!=_1C7){if(E(B(_aS(B(_aS(_1C6,_1C5)),_1Cn)).a)==32){return B(_1Cg(_1Cn,_1C5));}else{return B(_1Cg(_1C4,_1C5));}}else{if(_1C5!=_1C8){if(E(B(_aS(B(_aS(_1C6,_1C5)),_1Cn)).a)==32){return B(_1Cg(_1Cn,_1C5));}else{return B(_1Cg(_1C4,_1C5));}}else{return B(_1Cg(_1C4,_1C5));}}}}}}break;case 4:if(_1C4<0){return B(_1Cg(_1C4,_1C5));}else{if(_1C4>=E(_1B9)){return B(_1Cg(_1C4,_1C5));}else{var _1Co=_1C5+1|0;if(_1Co<0){return B(_1Cg(_1C4,_1C5));}else{if(_1Co>=E(_1Bb)){return B(_1Cg(_1C4,_1C5));}else{if(_1C4!=_1C7){if(E(B(_aS(B(_aS(_1C6,_1Co)),_1C4)).a)==32){return B(_1Cg(_1C4,_1Co));}else{return B(_1Cg(_1C4,_1C5));}}else{if(_1Co!=_1C8){if(E(B(_aS(B(_aS(_1C6,_1Co)),_1C4)).a)==32){return B(_1Cg(_1C4,_1Co));}else{return B(_1Cg(_1C4,_1C5));}}else{return B(_1Cg(_1C4,_1C5));}}}}}}break;default:if(_1C4<0){return B(_1Cg(_1C4,_1C5));}else{if(_1C4>=E(_1B9)){return B(_1Cg(_1C4,_1C5));}else{if(_1C5<0){return B(_1Cg(_1C4,_1C5));}else{if(_1C5>=E(_1Bb)){return B(_1Cg(_1C4,_1C5));}else{if(_1C4!=_1C7){var _1Cp=E(B(_aS(B(_aS(_1C6,_1C5)),_1C4)).a);return B(_1Cg(_1C4,_1C5));}else{if(_1C5!=_1C8){var _1Cq=E(B(_aS(B(_aS(_1C6,_1C5)),_1C4)).a);return B(_1Cg(_1C4,_1C5));}else{return B(_1Cg(_1C4,_1C5));}}}}}}}}),_1Cr=E(_1Ca);if(!_1Cr._){return new F(function(){return _1Bc(new T(function(){return E(E(_1Cd).b);},1),0,_1C5+1|0,_1Cf,_1C7,_1C8,_1Cb);});}else{var _1Cs=_1C4+1|0,_1Ct=_1C5,_1Cu=_1C7,_1Cv=_1C8,_1Cw=_1Cb;_1BT=new T(function(){return E(E(_1Cd).b);},1);_1BU=_1Cs;_1BV=_1Ct;_1BW=_1Cf;_1BX=_1Cu;_1BY=_1Cv;_1BZ=_1Cr.a;_1C0=_1Cr.b;_1C1=_1Cw;return __continue;}}else{var _1Cx=E(_1Ca);if(!_1Cx._){return new F(function(){return _1Bc(_1C3,0,_1C5+1|0,_1C6,_1C7,_1C8,_1Cb);});}else{var _1Cy=_1C3,_1Cs=_1C4+1|0,_1Ct=_1C5,_1Cz=_1C6,_1Cu=_1C7,_1Cv=_1C8,_1Cw=_1Cb;_1BT=_1Cy;_1BU=_1Cs;_1BV=_1Ct;_1BW=_1Cz;_1BX=_1Cu;_1BY=_1Cv;_1BZ=_1Cx.a;_1C0=_1Cx.b;_1C1=_1Cw;return __continue;}}})(_1BT,_1BU,_1BV,_1BW,_1BX,_1BY,_1BZ,_1C0,_1C1));if(_1C2!=__continue){return _1C2;}}},_1B8=B(_1Bc(_1Ad,0,0,_1Av,_1A3,_1A4,_1Av));}var _1CA=function(_1CB){var _1CC=function(_1CD){var _1CE=new T(function(){switch(E(_1Aj)){case 1:return true;break;case 5:return true;break;case 7:return true;break;default:return false;}}),_1CF=new T(function(){if(!E(_1At)){if(!E(_1CE)){return new T2(0,_1A3,_1A4);}else{return new T2(0,_1A5,_1A6);}}else{if(!B(_1uc(_1uo,_1B8,_1As))){if(!E(_1CE)){return new T2(0,_1A3,_1A4);}else{return new T2(0,_1A5,_1A6);}}else{return new T2(0,_1A5,_1A6);}}}),_1CG=new T(function(){return E(E(_1CF).b);}),_1CH=new T(function(){return E(E(_1CF).a);});if(!E(_1At)){var _1CI=E(_1Ag);}else{var _1CI=E(B(_1wZ(new T(function(){return B(_1yq(_1Ab,_1Ac,_1B8));}),_1B8)).a);}var _1CJ=new T(function(){if(!E(_1Ar)){if(!E(_1Am)){var _1CK=function(_1CL){var _1CM=function(_1CN){var _1CO=E(_1Aj);if(_1CO==4){return new T2(1,_1A0,new T2(1,_1Ai,_Z));}else{if(!E(_1CE)){return (E(_1CO)==2)?new T2(1,_1zY,new T2(1,_1Ai,_Z)):__Z;}else{var _1CP=E(_1Ai);return (E(_1CP)==61)?new T2(1,_1zZ,new T2(1,_1CP,new T(function(){return B(_H(0,_1A4,_Z));}))):new T2(1,_1zZ,new T2(1,_1CP,_Z));}}};if(!E(_1At)){return new F(function(){return _1CM(_);});}else{if(E(_1A5)!=E(_1CH)){return new T2(1,_1A1,new T2(1,_1Ai,_Z));}else{if(E(_1A6)!=E(_1CG)){return new T2(1,_1A1,new T2(1,_1Ai,_Z));}else{return new F(function(){return _1CM(_);});}}}};if(!E(_1At)){return B(_1CK(_));}else{if(!E(_1CI)){return B(_1CK(_));}else{return E(_1zU);}}}else{return new T2(1,_1zS,new T2(1,_1Ai,_Z));}}else{return new T2(1,_1zT,new T2(1,_1Ai,_Z));}},1);return {_:0,a:E(new T2(0,_1CH,_1CG)),b:E(_1B8),c:E(_1A8),d:_1CB,e:_1CD,f:_1Ab,g:E(_1Ac),h:_1Ad,i:E(B(_x(_1Ae,_1CJ))),j:E(_1Af),k:E(_1CI)};};if(!E(_1Ar)){return new F(function(){return _1CC(_1Aa);});}else{return new F(function(){return _1CC(E(_1Ai));});}};if(!E(_1Am)){return new F(function(){return _1CA(_1A9);});}else{return new F(function(){return _1CA(E(_1Ai));});}},_1CQ=new T2(1,_61,_Z),_1CR=5,_1CS=new T2(1,_1CR,_Z),_1CT=function(_1CU,_1CV){while(1){var _1CW=E(_1CU);if(!_1CW._){return E(_1CV);}else{_1CU=_1CW.b;_1CV=_1CW.a;continue;}}},_1CX=57,_1CY=48,_1CZ=new T2(1,_1xx,_Z),_1D0=new T(function(){return B(err(_x3));}),_1D1=new T(function(){return B(err(_wZ));}),_1D2=new T(function(){return B(A3(_K9,_KC,_Ie,_K1));}),_1D3=function(_1D4,_1D5){if((_1D5-48|0)>>>0>9){var _1D6=_1D5+_1D4|0,_1D7=function(_1D8){if(!B(_4H(_l8,_1D8,_1CZ))){return E(_1D8);}else{return new F(function(){return _1D3(_1D4,_1D8);});}};if(_1D6<=122){if(_1D6>=97){if(_1D6>>>0>1114111){return new F(function(){return _Be(_1D6);});}else{return new F(function(){return _1D7(_1D6);});}}else{if(_1D6<=90){if(_1D6>>>0>1114111){return new F(function(){return _Be(_1D6);});}else{return new F(function(){return _1D7(_1D6);});}}else{var _1D9=65+(_1D6-90|0)|0;if(_1D9>>>0>1114111){return new F(function(){return _Be(_1D9);});}else{return new F(function(){return _1D7(_1D9);});}}}}else{var _1Da=97+(_1D6-122|0)|0;if(_1Da>>>0>1114111){return new F(function(){return _Be(_1Da);});}else{return new F(function(){return _1D7(_1Da);});}}}else{var _1Db=B(_KL(B(_x8(_1D2,new T2(1,_1D5,_Z)))));if(!_1Db._){return E(_1D1);}else{if(!E(_1Db.b)._){var _1Dc=E(_1Db.a)+_1D4|0;switch(_1Dc){case  -1:return E(_1CY);case 10:return E(_1CX);default:return new F(function(){return _1CT(B(_H(0,_1Dc,_Z)),_10m);});}}else{return E(_1D0);}}}},_1Dd=function(_1De,_1Df){if((_1De-48|0)>>>0>9){return _1Df;}else{var _1Dg=B(_KL(B(_x8(_1D2,new T2(1,_1De,_Z)))));if(!_1Dg._){return E(_1D1);}else{if(!E(_1Dg.b)._){return new F(function(){return _1D3(E(_1Dg.a),_1Df);});}else{return E(_1D0);}}}},_1Dh=function(_1Di,_1Dj){return new F(function(){return _1Dd(E(_1Di),E(_1Dj));});},_1Dk=new T2(1,_1Dh,_Z),_1Dl=112,_1Dm=111,_1Dn=function(_1Do,_1Dp,_1Dq,_1Dr,_1Ds,_1Dt,_1Du,_1Dv,_1Dw,_1Dx,_1Dy,_1Dz){var _1DA=new T(function(){return B(_aS(B(_aS(_1Dq,_1Dp)),E(_1Do)));}),_1DB=new T(function(){return E(E(_1DA).b);}),_1DC=new T(function(){if(E(_1DB)==4){return true;}else{return false;}}),_1DD=new T(function(){return E(E(_1DA).a);});if(E(_1Dt)==32){var _1DE=false;}else{if(E(_1DD)==32){var _1DF=true;}else{var _1DF=false;}var _1DE=_1DF;}var _1DG=new T(function(){var _1DH=new T(function(){return B(A3(_aS,_1CQ,B(_Rt(_l8,_1Ds,_1xy)),_1Dt));});if(!E(_1DE)){if(!E(_1DC)){return E(_1DD);}else{if(!B(_4H(_3S,_1Du,_1CS))){return E(_1DD);}else{return B(A(_aS,[_1Dk,B(_Rt(_3S,_1Du,_1CS)),_1DH,_1DD]));}}}else{return E(_1DH);}}),_1DI=B(_PA(_1Do,_1Dp,_1DG,_1DB,_1Dq)),_1DJ=function(_1DK){var _1DL=B(_1wZ(new T(function(){return B(_1yq(_1Du,_1Dv,_1DI));}),_1DI)).a;return {_:0,a:E(new T2(0,_1Do,_1Dp)),b:E(_1DI),c:E(_1Dr),d:_1Ds,e:_1DK,f:_1Du,g:E(_1Dv),h:_1Dw,i:E(B(_x(_1Dx,new T(function(){if(!E(_1DL)){if(!E(_1DE)){if(!E(_1DC)){return __Z;}else{return new T2(1,_1Dl,new T2(1,_1DG,_Z));}}else{return new T2(1,_1Dm,new T2(1,_1DG,_Z));}}else{return E(_1zU);}},1)))),j:E(_1Dy),k:E(_1DL)};};if(!E(_1DE)){return new F(function(){return _1DJ(_1Dt);});}else{return new F(function(){return _1DJ(32);});}},_1DM=function(_1DN,_1DO){while(1){var _1DP=E(_1DO);if(!_1DP._){return __Z;}else{var _1DQ=_1DP.b,_1DR=E(_1DN);if(_1DR==1){return E(_1DQ);}else{_1DN=_1DR-1|0;_1DO=_1DQ;continue;}}}},_1DS=new T(function(){return B(unCStr("\u5e74 "));}),_1DT=function(_1DU,_1DV,_1DW,_1DX,_1DY){var _1DZ=new T(function(){var _1E0=new T(function(){var _1E1=new T(function(){var _1E2=new T(function(){var _1E3=new T(function(){return B(_x(_1DW,new T(function(){return B(unAppCStr(" >>",_1DX));},1)));});return B(unAppCStr(" >>",_1E3));},1);return B(_x(_1DV,_1E2));},1);return B(_x(_1DS,_1E1));},1);return B(_x(B(_H(0,_1DU,_Z)),_1E0));});return new T2(0,new T2(1,_1DY,_1th),_1DZ);},_1E4=function(_1E5){var _1E6=E(_1E5),_1E7=E(_1E6.a),_1E8=B(_1DT(_1E7.a,_1E7.b,_1E7.c,_1E7.d,_1E6.b));return new T2(0,_1E8.a,_1E8.b);},_1E9=function(_1Ea){var _1Eb=E(_1Ea);return new T2(0,new T2(1,_1Eb.b,_1th),E(_1Eb.a).b);},_1Ec=new T(function(){return B(_i8("Grid.hs:(31,1)-(38,56)|function checkGrid"));}),_1Ed=function(_1Ee,_1Ef){while(1){var _1Eg=E(_1Ef);if(!_1Eg._){return false;}else{var _1Eh=_1Eg.b,_1Ei=E(_1Ee),_1Ej=_1Ei.a,_1Ek=_1Ei.b,_1El=E(_1Eg.a);if(!_1El._){return E(_1Ec);}else{var _1Em=E(_1El.a),_1En=_1Em.a,_1Eo=_1Em.b,_1Ep=E(_1El.b);if(!_1Ep._){var _1Eq=E(_1Ej),_1Er=E(_1Eq);if(_1Er==32){switch(E(_1Ek)){case 0:if(!E(_1Eo)){return true;}else{_1Ee=new T2(0,_1Eq,_IJ);_1Ef=_1Eh;continue;}break;case 1:if(E(_1Eo)==1){return true;}else{_1Ee=new T2(0,_1Eq,_IP);_1Ef=_1Eh;continue;}break;case 2:if(E(_1Eo)==2){return true;}else{_1Ee=new T2(0,_1Eq,_IV);_1Ef=_1Eh;continue;}break;case 3:if(E(_1Eo)==3){return true;}else{_1Ee=new T2(0,_1Eq,_J1);_1Ef=_1Eh;continue;}break;case 4:if(E(_1Eo)==4){return true;}else{_1Ee=new T2(0,_1Eq,_J7);_1Ef=_1Eh;continue;}break;case 5:if(E(_1Eo)==5){return true;}else{_1Ee=new T2(0,_1Eq,_Jy);_1Ef=_1Eh;continue;}break;case 6:if(E(_1Eo)==6){return true;}else{_1Ee=new T2(0,_1Eq,_Jr);_1Ef=_1Eh;continue;}break;case 7:if(E(_1Eo)==7){return true;}else{_1Ee=new T2(0,_1Eq,_Jk);_1Ef=_1Eh;continue;}break;default:if(E(_1Eo)==8){return true;}else{_1Ee=new T2(0,_1Eq,_Jd);_1Ef=_1Eh;continue;}}}else{if(_1Er!=E(_1En)){_1Ee=_1Ei;_1Ef=_1Eh;continue;}else{switch(E(_1Ek)){case 0:if(!E(_1Eo)){return true;}else{_1Ee=new T2(0,_1Eq,_IJ);_1Ef=_1Eh;continue;}break;case 1:if(E(_1Eo)==1){return true;}else{_1Ee=new T2(0,_1Eq,_IP);_1Ef=_1Eh;continue;}break;case 2:if(E(_1Eo)==2){return true;}else{_1Ee=new T2(0,_1Eq,_IV);_1Ef=_1Eh;continue;}break;case 3:if(E(_1Eo)==3){return true;}else{_1Ee=new T2(0,_1Eq,_J1);_1Ef=_1Eh;continue;}break;case 4:if(E(_1Eo)==4){return true;}else{_1Ee=new T2(0,_1Eq,_J7);_1Ef=_1Eh;continue;}break;case 5:if(E(_1Eo)==5){return true;}else{_1Ee=new T2(0,_1Eq,_Jy);_1Ef=_1Eh;continue;}break;case 6:if(E(_1Eo)==6){return true;}else{_1Ee=new T2(0,_1Eq,_Jr);_1Ef=_1Eh;continue;}break;case 7:if(E(_1Eo)==7){return true;}else{_1Ee=new T2(0,_1Eq,_Jk);_1Ef=_1Eh;continue;}break;default:if(E(_1Eo)==8){return true;}else{_1Ee=new T2(0,_1Eq,_Jd);_1Ef=_1Eh;continue;}}}}}else{var _1Es=E(_1Ej),_1Et=E(_1Es);if(_1Et==32){switch(E(_1Ek)){case 0:if(!E(_1Eo)){return true;}else{_1Ee=new T2(0,_1Es,_IJ);_1Ef=new T2(1,_1Ep,_1Eh);continue;}break;case 1:if(E(_1Eo)==1){return true;}else{_1Ee=new T2(0,_1Es,_IP);_1Ef=new T2(1,_1Ep,_1Eh);continue;}break;case 2:if(E(_1Eo)==2){return true;}else{_1Ee=new T2(0,_1Es,_IV);_1Ef=new T2(1,_1Ep,_1Eh);continue;}break;case 3:if(E(_1Eo)==3){return true;}else{_1Ee=new T2(0,_1Es,_J1);_1Ef=new T2(1,_1Ep,_1Eh);continue;}break;case 4:if(E(_1Eo)==4){return true;}else{_1Ee=new T2(0,_1Es,_J7);_1Ef=new T2(1,_1Ep,_1Eh);continue;}break;case 5:if(E(_1Eo)==5){return true;}else{_1Ee=new T2(0,_1Es,_Jy);_1Ef=new T2(1,_1Ep,_1Eh);continue;}break;case 6:if(E(_1Eo)==6){return true;}else{_1Ee=new T2(0,_1Es,_Jr);_1Ef=new T2(1,_1Ep,_1Eh);continue;}break;case 7:if(E(_1Eo)==7){return true;}else{_1Ee=new T2(0,_1Es,_Jk);_1Ef=new T2(1,_1Ep,_1Eh);continue;}break;default:if(E(_1Eo)==8){return true;}else{_1Ee=new T2(0,_1Es,_Jd);_1Ef=new T2(1,_1Ep,_1Eh);continue;}}}else{if(_1Et!=E(_1En)){_1Ee=_1Ei;_1Ef=new T2(1,_1Ep,_1Eh);continue;}else{switch(E(_1Ek)){case 0:if(!E(_1Eo)){return true;}else{_1Ee=new T2(0,_1Es,_IJ);_1Ef=new T2(1,_1Ep,_1Eh);continue;}break;case 1:if(E(_1Eo)==1){return true;}else{_1Ee=new T2(0,_1Es,_IP);_1Ef=new T2(1,_1Ep,_1Eh);continue;}break;case 2:if(E(_1Eo)==2){return true;}else{_1Ee=new T2(0,_1Es,_IV);_1Ef=new T2(1,_1Ep,_1Eh);continue;}break;case 3:if(E(_1Eo)==3){return true;}else{_1Ee=new T2(0,_1Es,_J1);_1Ef=new T2(1,_1Ep,_1Eh);continue;}break;case 4:if(E(_1Eo)==4){return true;}else{_1Ee=new T2(0,_1Es,_J7);_1Ef=new T2(1,_1Ep,_1Eh);continue;}break;case 5:if(E(_1Eo)==5){return true;}else{_1Ee=new T2(0,_1Es,_Jy);_1Ef=new T2(1,_1Ep,_1Eh);continue;}break;case 6:if(E(_1Eo)==6){return true;}else{_1Ee=new T2(0,_1Es,_Jr);_1Ef=new T2(1,_1Ep,_1Eh);continue;}break;case 7:if(E(_1Eo)==7){return true;}else{_1Ee=new T2(0,_1Es,_Jk);_1Ef=new T2(1,_1Ep,_1Eh);continue;}break;default:if(E(_1Eo)==8){return true;}else{_1Ee=new T2(0,_1Es,_Jd);_1Ef=new T2(1,_1Ep,_1Eh);continue;}}}}}}}}},_1Eu=new T(function(){return B(unCStr("\n"));}),_1Ev=function(_1Ew,_1Ex,_){var _1Ey=jsWriteHandle(E(_1Ew),toJSStr(E(_1Ex)));return _kF;},_1Ez=function(_1EA,_1EB,_){var _1EC=E(_1EA),_1ED=jsWriteHandle(_1EC,toJSStr(E(_1EB)));return new F(function(){return _1Ev(_1EC,_1Eu,_);});},_1EE=function(_1EF){var _1EG=E(_1EF);if(!_1EG._){return __Z;}else{return new F(function(){return _x(_1EG.a,new T(function(){return B(_1EE(_1EG.b));},1));});}},_1EH=new T(function(){return B(unCStr("removed"));}),_1EI=new T(function(){return B(unCStr("loadError"));}),_1EJ=new T(function(){return B(unCStr("saved"));}),_1EK=new T(function(){return B(err(_wZ));}),_1EL=new T(function(){return B(err(_x3));}),_1EM=12,_1EN=3,_1EO=new T(function(){return B(unCStr("Coding : yokoP"));}),_1EP=8,_1EQ=32,_1ER=new T2(0,_1EQ,_Jy),_1ES=99,_1ET=64,_1EU=new T(function(){return B(_qu(_1oz,0));}),_1EV=new T(function(){return B(unCStr("loadError"));}),_1EW=new T(function(){return B(A3(_K9,_KC,_Ie,_K1));}),_1EX=new T(function(){return B(unCStr(","));}),_1EY=new T(function(){return B(unCStr("~"));}),_1EZ=new T(function(){return B(unCStr("savedata"));}),_1F0=new T(function(){return B(unCStr("---"));}),_1F1=new T(function(){return B(unCStr("=="));}),_1F2=4,_1F3=6,_1F4=5,_1F5=new T1(0,333),_1F6=new T(function(){return B(_ct(1,2147483647));}),_1F7=function(_1F8){var _1F9=B(_KL(B(_x8(_1EW,_1F8))));return (_1F9._==0)?E(_1EK):(E(_1F9.b)._==0)?E(_1F9.a):E(_1EL);},_1Fa=new T(function(){return B(unCStr("\""));}),_1Fb=new T2(1,_Z,_Z),_1Fc=new T(function(){return B(_aj(_1F7,_1Fb));}),_1Fd=new T(function(){var _1Fe=E(_1mS);if(!_1Fe._){return E(_ri);}else{return E(_1Fe.a);}}),_1Ff=new T(function(){return B(_1gr(_1mg,5,_1nm));}),_1Fg=new T(function(){return B(unCStr("Thank you!"));}),_1Fh=17,_1Fi=2,_1Fj=new T(function(){return B(unCStr("First Up : 2024 12 24"));}),_1Fk=function(_1Fl,_1Fm){var _1Fn=E(_1Fm);return (_1Fn._==0)?__Z:new T2(1,_1Fl,new T2(1,_1Fn.a,new T(function(){return B(_1Fk(_1Fl,_1Fn.b));})));},_1Fo=new T(function(){return B(unCStr("noContent"));}),_1Fp=new T(function(){return B(unCStr("noHint"));}),_1Fq=new T(function(){return B(err(_x3));}),_1Fr=new T(function(){return B(err(_wZ));}),_1Fs=new T(function(){return B(A3(_K9,_KC,_Ie,_K1));}),_1Ft=function(_1Fu,_1Fv){var _1Fw=E(_1Fv);if(!_1Fw._){var _1Fx=B(_KL(B(_x8(_1Fs,_1Fu))));return (_1Fx._==0)?E(_1Fr):(E(_1Fx.b)._==0)?new T4(0,E(_1Fx.a),_Z,_Z,_Z):E(_1Fq);}else{var _1Fy=_1Fw.a,_1Fz=E(_1Fw.b);if(!_1Fz._){var _1FA=B(_KL(B(_x8(_1Fs,_1Fu))));return (_1FA._==0)?E(_1Fr):(E(_1FA.b)._==0)?new T4(0,E(_1FA.a),E(_1Fy),E(_1Fp),E(_1Fo)):E(_1Fq);}else{var _1FB=_1Fz.a,_1FC=E(_1Fz.b);if(!_1FC._){var _1FD=B(_KL(B(_x8(_1Fs,_1Fu))));return (_1FD._==0)?E(_1Fr):(E(_1FD.b)._==0)?new T4(0,E(_1FD.a),E(_1Fy),E(_1FB),E(_1Fo)):E(_1Fq);}else{if(!E(_1FC.b)._){var _1FE=B(_KL(B(_x8(_1Fs,_1Fu))));return (_1FE._==0)?E(_1Fr):(E(_1FE.b)._==0)?new T4(0,E(_1FE.a),E(_1Fy),E(_1FB),E(_1FC.a)):E(_1Fq);}else{return new T4(0,0,_Z,_Z,_Z);}}}}},_1FF=function(_1FG){var _1FH=E(_1FG);if(!_1FH._){return new F(function(){return _1Ft(_Z,_Z);});}else{var _1FI=_1FH.a,_1FJ=E(_1FH.b);if(!_1FJ._){return new F(function(){return _1Ft(new T2(1,_1FI,_Z),_Z);});}else{var _1FK=E(_1FI),_1FL=new T(function(){var _1FM=B(_LD(44,_1FJ.a,_1FJ.b));return new T2(0,_1FM.a,_1FM.b);});if(E(_1FK)==44){return new F(function(){return _1Ft(_Z,new T2(1,new T(function(){return E(E(_1FL).a);}),new T(function(){return E(E(_1FL).b);})));});}else{var _1FN=E(_1FL);return new F(function(){return _1Ft(new T2(1,_1FK,_1FN.a),_1FN.b);});}}}},_1FO=function(_1FP){var _1FQ=B(_1FF(_1FP));return new T4(0,_1FQ.a,E(_1FQ.b),E(_1FQ.c),E(_1FQ.d));},_1FR=function(_1FS){return (E(_1FS)==10)?true:false;},_1FT=function(_1FU){var _1FV=E(_1FU);if(!_1FV._){return __Z;}else{var _1FW=new T(function(){var _1FX=B(_1gU(_1FR,_1FV));return new T2(0,_1FX.a,new T(function(){var _1FY=E(_1FX.b);if(!_1FY._){return __Z;}else{return B(_1FT(_1FY.b));}}));});return new T2(1,new T(function(){return E(E(_1FW).a);}),new T(function(){return E(E(_1FW).b);}));}},_1FZ=new T(function(){return B(unCStr("57,\u5974\uff1a\u306a\uff1a\u570b\uff1a\u3053\u304f\uff1a\u738b\uff1a\u304a\u3046\uff1a\u304c\u5f8c\uff1a\u3053\u3046\uff1a\u6f22\uff1a\u304b\u3093\uff1a\u304b\u3089\u91d1\uff1a\u304d\u3093\uff1a\u5370\uff1a\u3044\u3093\uff1a,<\u5f8c\uff1a\u3054\uff1a\u6f22\uff1a\u304b\u3093\uff1a\u66f8\uff1a\u3057\u3087\uff1a>\u306b\u8a18\uff1a\u304d\uff1a\u8f09\uff1a\u3055\u3044\uff1a\u304c\u3042\u308a \u6c5f\uff1a\u3048\uff1a\u6238\uff1a\u3069\uff1a\u671f\uff1a\u304d\uff1a\u306b\u305d\u308c\u3089\u3057\u304d\u91d1\u5370\u304c\u767a\u898b\u3055\u308c\u308b,\u798f\uff1a\u3075\u304f\uff1a\u5ca1\uff1a\u304a\u304b\uff1a\u770c\uff1a\u3051\u3093\uff1a\u5fd7\uff1a\u3057\uff1a\u8cc0\uff1a\u304b\u306e\uff1a\u5cf6\uff1a\u3057\u307e\uff1a\u306b\u3066<\u6f22\uff1a\u304b\u3093\u306e\uff1a\u59d4\uff1a\u308f\u306e\uff1a\u5974\uff1a\u306a\u306e\uff1a\u570b\uff1a\u3053\u304f\uff1a\u738b\uff1a\u304a\u3046\uff1a>\u3068\u523b\uff1a\u304d\u3056\uff1a\u307e\u308c\u305f\u91d1\u5370\u304c\u6c5f\u6238\u6642\u4ee3\u306b\u767c\uff1a\u306f\u3063\uff1a\u898b\uff1a\u3051\u3093\uff1a\u3055\u308c\u308b >>\u5927\uff1a\u3084\uff1a\u548c\uff1a\u307e\u3068\uff1a\u671d\uff1a\u3061\u3087\u3046\uff1a\u5ef7\uff1a\u3066\u3044\uff1a\u3068\u306e\u95dc\uff1a\u304b\u3093\uff1a\u4fc2\uff1a\u3051\u3044\uff1a\u4e0d\uff1a\u3075\uff1a\u660e\uff1a\u3081\u3044\uff1a\u306f\n239,<\u5351\uff1a\u3072\uff1a\u5f25\uff1a\u307f\uff1a\u547c\uff1a\u3053\uff1a>\u304c\u9b4f\uff1a\u304e\uff1a\u306b\u9063\uff1a\u3051\u3093\uff1a\u4f7f\uff1a\u3057\uff1a,\u652f\uff1a\u3057\uff1a\u90a3\uff1a\u306a\uff1a\u306e\u6b74\uff1a\u308c\u304d\uff1a\u53f2\uff1a\u3057\uff1a\u66f8\uff1a\u3057\u3087\uff1a<\u9b4f\uff1a\u304e\uff1a\u5fd7\uff1a\u3057\uff1a>\u306b\u8a18\uff1a\u304d\uff1a\u8f09\uff1a\u3055\u3044\uff1a\u3055\u308c\u3066\u3090\u308b\u5deb\uff1a\u307f\uff1a\u5973\uff1a\u3053\uff1a,<\u9b4f\uff1a\u304e\uff1a\u5fd7\uff1a\u3057\uff1a>\u502d\uff1a\u308f\uff1a\u4eba\uff1a\u3058\u3093\uff1a\u4f1d\uff1a\u3067\u3093\uff1a\u306b\u8a18\uff1a\u3057\u308b\uff1a\u3055\u308c\u3066\u3090\u308b<\u90aa\u99ac\u58f9\u570b(\u3084\u307e\u3044\u3061\u3053\u304f)>\u3082<\u5351\u5f25\u547c>\u3082\u65e5\u672c\u306b\u6b98\uff1a\u306e\u3053\uff1a\u308b\u8cc7\uff1a\u3057\uff1a\u6599\uff1a\u308c\u3044\uff1a\u3067\u306f\u4e00\uff1a\u3044\u3063\uff1a\u5207\uff1a\u3055\u3044\uff1a\u78ba\uff1a\u304b\u304f\uff1a\u8a8d\uff1a\u306b\u3093\uff1a\u3067\u304d\u306a\u3044\n316,\u4ec1\uff1a\u306b\u3093\uff1a\u5fb3\uff1a\u3068\u304f\uff1a\u5929\u7687 \u7a0e\uff1a\u305c\u3044\uff1a\u3092\u514d\uff1a\u3081\u3093\uff1a\u9664\uff1a\u3058\u3087\uff1a,<\u53e4\uff1a\u3053\uff1a\u4e8b\uff1a\u3058\uff1a\u8a18\uff1a\u304d\uff1a><\u65e5\uff1a\u306b\uff1a\u672c\uff1a\u307b\u3093\uff1a\u66f8\uff1a\u3057\u3087\uff1a\u7d00\uff1a\u304d\uff1a>\u306b\u8a18\uff1a\u304d\uff1a\u8f09\uff1a\u3055\u3044\uff1a\u304c\u3042\u308b,16\u4ee3\u4ec1\uff1a\u306b\u3093\uff1a\u5fb3\uff1a\u3068\u304f\uff1a\u5929\u7687\u304c<\u6c11\uff1a\u305f\u307f\uff1a\u306e\u304b\u307e\u3069\u3088\u308a\u7159\uff1a\u3051\u3080\u308a\uff1a\u304c\u305f\u3061\u306e\u307c\u3089\u306a\u3044\u306e\u306f \u8ca7\uff1a\u307e\u3065\uff1a\u3057\u304f\u3066\u708a\uff1a\u305f\uff1a\u304f\u3082\u306e\u304c\u306a\u3044\u304b\u3089\u3067\u306f\u306a\u3044\u304b>\u3068\u3057\u3066 \u5bae\uff1a\u304d\u3085\u3046\uff1a\u4e2d\uff1a\u3061\u3085\u3046\uff1a\u306e\u4fee\uff1a\u3057\u3085\u3046\uff1a\u7e55\uff1a\u305c\u3093\uff1a\u3092\u5f8c\uff1a\u3042\u3068\uff1a\u307e\u306f\u3057\u306b\u3057 \u6c11\u306e\u751f\u6d3b\u3092\u8c4a\uff1a\u3086\u305f\uff1a\u304b\u306b\u3059\u308b\u8a71\u304c<\u65e5\u672c\u66f8\u7d00>\u306b\u3042\u308b\n478,<\u502d\uff1a\u308f\uff1a>\u306e\u6b66\uff1a\u3076\uff1a\u738b\uff1a\u304a\u3046\uff1a \u5357\uff1a\u306a\u3093\uff1a\u671d\uff1a\u3061\u3087\u3046\uff1a\u306e\u5b8b\uff1a\u305d\u3046\uff1a\u3078\u9063\uff1a\u3051\u3093\uff1a\u4f7f\uff1a\u3057\uff1a,\u96c4\uff1a\u3086\u3046\uff1a\u7565\uff1a\u308a\u3083\u304f\uff1a\u5929\u7687\u3092\u6307\u3059\u3068\u3044\u3075\u306e\u304c\u5b9a\uff1a\u3066\u3044\uff1a\u8aac\uff1a\u305b\u3064\uff1a,<\u5b8b\uff1a\u305d\u3046\uff1a\u66f8\uff1a\u3057\u3087\uff1a>\u502d\uff1a\u308f\uff1a\u570b\uff1a\u3053\u304f\uff1a\u50b3\uff1a\u3067\u3093\uff1a\u306b\u8a18\uff1a\u304d\uff1a\u8f09\uff1a\u3055\u3044\uff1a\u304c\u3042\u308b >> \u96c4\u7565\u5929\u7687\u306f\u7b2c21\u4ee3\u5929\u7687\n538,\u4ecf\uff1a\u3076\u3063\uff1a\u6559\uff1a\u304d\u3087\u3046\uff1a\u516c\uff1a\u3053\u3046\uff1a\u4f1d\uff1a\u3067\u3093\uff1a,\u6b3d\uff1a\u304d\u3093\uff1a\u660e\uff1a\u3081\u3044\uff1a\u5929\u7687\u5fa1\uff1a\u307f\uff1a\u4ee3\uff1a\u3088\uff1a\u306b\u767e\uff1a\u304f\uff1a\u6e08\uff1a\u3060\u3089\uff1a\u306e\u8056\uff1a\u305b\u3044\uff1a\u660e\uff1a\u3081\u3044\uff1a\u738b\uff1a\u304a\u3046\uff1a\u304b\u3089\u50b3\uff1a\u3067\u3093\uff1a\u4f86\uff1a\u3089\u3044\uff1a\u3057\u305f\u3068\u306e\u6587\uff1a\u3076\u3093\uff1a\u732e\uff1a\u3051\u3093\uff1a\u3042\u308a,\u6b63\u78ba\u306a\u5e74\u4ee3\u306b\u3064\u3044\u3066\u306f\u8af8\uff1a\u3057\u3087\uff1a\u8aac\uff1a\u305b\u3064\uff1a\u3042\u308b\n604,\u5341\uff1a\u3058\u3085\u3046\uff1a\u4e03\uff1a\u3057\u3061\uff1a\u6761\uff1a\u3058\u3087\u3046\uff1a\u61b2\uff1a\u3051\u3093\uff1a\u6cd5\uff1a\u307d\u3046\uff1a\u5236\uff1a\u305b\u3044\uff1a\u5b9a\uff1a\u3066\u3044\uff1a,\u8056\uff1a\u3057\u3087\u3046\uff1a\u5fb3\uff1a\u3068\u304f\uff1a\u592a\uff1a\u305f\u3044\uff1a\u5b50\uff1a\u3057\uff1a\u304c\u5236\uff1a\u305b\u3044\uff1a\u5b9a\uff1a\u3066\u3044\uff1a\u3057\u305f\u3068\u3055\u308c\u308b,<\u548c\uff1a\u308f\uff1a\u3092\u4ee5\uff1a\u3082\u3063\uff1a\u3066\u8cb4\uff1a\u305f\u3075\u3068\uff1a\u3057\u3068\u70ba\uff1a\u306a\uff1a\u3057 \u5fe4(\u3055\u304b)\u3075\u308b\u3053\u3068\u7121\uff1a\u306a\uff1a\u304d\u3092\u5b97\uff1a\u3080\u306d\uff1a\u3068\u305b\u3088>\n607,\u6cd5\uff1a\u307b\u3046\uff1a\u9686\uff1a\u308a\u3085\u3046\uff1a\u5bfa\uff1a\u3058\uff1a\u304c\u5275\uff1a\u305d\u3046\uff1a\u5efa\uff1a\u3051\u3093\uff1a\u3055\u308c\u308b,\u8056\uff1a\u3057\u3087\u3046\uff1a\u5fb3\uff1a\u3068\u304f\uff1a\u592a\uff1a\u305f\u3044\uff1a\u5b50\uff1a\u3057\uff1a\u3086\u304b\u308a\u306e\u5bfa\uff1a\u3058\uff1a\u9662\uff1a\u3044\u3093\uff1a,\u897f\uff1a\u3055\u3044\uff1a\u9662\uff1a\u3044\u3093\uff1a\u4f3d\uff1a\u304c\uff1a\u85cd\uff1a\u3089\u3093\uff1a\u306f\u73fe\uff1a\u3052\u3093\uff1a\u5b58\uff1a\u305e\u3093\uff1a\u3059\u308b\u4e16\u754c\u6700\uff1a\u3055\u3044\uff1a\u53e4\uff1a\u3053\uff1a\u306e\u6728\uff1a\u3082\u304f\uff1a\u9020\uff1a\u305e\u3046\uff1a\u5efa\uff1a\u3051\u3093\uff1a\u7bc9\uff1a\u3061\u304f\uff1a\u7269\uff1a\u3076\u3064\uff1a\u3068\u3055\u308c\u3066\u3090\u308b\n645,\u4e59\uff1a\u3044\u3063\uff1a\u5df3\uff1a\u3057\uff1a\u306e\u8b8a\uff1a\u3078\u3093\uff1a,\u3053\u306e\u5f8c\u3059\u3050\u5927\uff1a\u305f\u3044\uff1a\u5316\uff1a\u304b\uff1a\u306e\u6539\uff1a\u304b\u3044\uff1a\u65b0\uff1a\u3057\u3093\uff1a\u306a\u308b,\u4e2d\uff1a\u306a\u304b\u306e\uff1a\u5927\uff1a\u304a\u304a\uff1a\u5144\uff1a\u3048\u306e\uff1a\u7687\uff1a\u304a\u3046\uff1a\u5b50\uff1a\u3058\uff1a(\u5f8c\u306e38\u4ee3\u5929\uff1a\u3066\u3093\uff1a\u667a\uff1a\u3062\uff1a\u5929\u7687)\u304c\u8607\uff1a\u305d\uff1a\u6211\uff1a\u304c\uff1a\u6c0f\uff1a\u3057\uff1a\u3092\u4ea1\uff1a\u307b\u308d\uff1a\u307c\u3059\n663,\u767d\uff1a\u306f\u304f\uff1a\u6751\uff1a\u3059\u304d\u306e\uff1a\u6c5f\uff1a\u3048\uff1a\u306e\u6230\uff1a\u305f\u305f\u304b\u3072\uff1a,\u5510\uff1a\u3068\u3046\uff1a\u3068\u65b0\uff1a\u3057\u3089\uff1a\u7f85\uff1a\u304e\uff1a\u306b\u6ec5\uff1a\u307b\u308d\uff1a\u307c\u3055\u308c\u305f\u767e\uff1a\u304f\u3060\uff1a\u6e08\uff1a\u3089\uff1a\u3092\u518d\uff1a\u3055\u3044\uff1a\u8208\uff1a\u3053\u3046\uff1a\u3059\u308b\u76ee\uff1a\u3082\u304f\uff1a\u7684\uff1a\u3066\u304d\uff1a,\u5510\uff1a\u3068\u3046\uff1a\u30fb\u65b0\uff1a\u3057\u3089\uff1a\u7f85\uff1a\u304e\uff1a\u9023\uff1a\u308c\u3093\uff1a\u5408\uff1a\u3054\u3046\uff1a\u8ecd\uff1a\u3050\u3093\uff1a\u306b\u6557\uff1a\u3084\u3076\uff1a\u308c\u308b\n672,\u58ec\uff1a\u3058\u3093\uff1a\u7533\uff1a\u3057\u3093\uff1a\u306e\u4e82\uff1a\u3089\u3093\uff1a,\u5929\uff1a\u3066\u3093\uff1a\u667a\uff1a\u3062\uff1a\u5929\u7687\u304a\u304b\u304f\u308c\u5f8c\u306e\u5f8c\uff1a\u3053\u3046\uff1a\u7d99\uff1a\u3051\u3044\uff1a\u8005\uff1a\u3057\u3083\uff1a\u4e89\uff1a\u3042\u3089\u305d\uff1a\u3072,\u5f8c\uff1a\u3053\u3046\uff1a\u7d99\uff1a\u3051\u3044\uff1a\u8005\uff1a\u3057\u3083\uff1a\u3067\u3042\u3063\u305f\u5927\uff1a\u304a\u304a\uff1a\u53cb\uff1a\u3068\u3082\u306e\uff1a\u7687\uff1a\u304a\u3046\uff1a\u5b50\uff1a\u3058\uff1a\u306b\u53d4\uff1a\u304a\uff1a\u7236\uff1a\u3058\uff1a\u306e\u5927\uff1a\u304a\u304a\uff1a\u6d77\uff1a\u3042\uff1a\u4eba\uff1a\u307e\u306e\uff1a\u7687\uff1a\u304a\u3046\uff1a\u5b50\uff1a\u3058\uff1a\u304c\u53cd\uff1a\u306f\u3093\uff1a\u65d7\uff1a\u304d\uff1a\u3092\u7ffb\uff1a\u3072\u308b\u304c\u3078\uff1a\u3057 \u5927\uff1a\u304a\u304a\uff1a\u53cb\uff1a\u3068\u3082\u306e\uff1a\u7687\uff1a\u304a\u3046\uff1a\u5b50\uff1a\u3058\uff1a\u3092\u5012\uff1a\u305f\u304a\uff1a\u3057\u3066\u5929\uff1a\u3066\u3093\uff1a\u6b66\uff1a\u3080\uff1a\u5929\u7687\u3068\u306a\u308b\n710,\u5e73\uff1a\u3078\u3044\uff1a\u57ce\uff1a\u3058\u3087\u3046\uff1a\u4eac\uff1a\u304d\u3087\u3046\uff1a\u9077\uff1a\u305b\u3093\uff1a\u90fd\uff1a\u3068\uff1a,\u5e73\u57ce\u3068\u3044\u3075\u6f22\u5b57\u306f<\u306a\u3089>\u3068\u3082\u8b80\uff1a\u3088\uff1a\u3080,\u548c\uff1a\u308f\uff1a\u9285\uff1a\u3069\u3046\uff1a3\u5e74 \u7b2c43\u4ee3\u5143\uff1a\u3052\u3093\uff1a\u660e\uff1a\u3081\u3044\uff1a\u5929\u7687\u306b\u3088\u308b \u5148\uff1a\u305b\u3093\uff1a\u4ee3\uff1a\u3060\u3044\uff1a\u306e\u6587\uff1a\u3082\u3093\uff1a\u6b66\uff1a\u3080\uff1a\u5929\u7687\u304c\u75ab\uff1a\u3048\u304d\uff1a\u75c5\uff1a\u3073\u3087\u3046\uff1a\u3067\u5d29\uff1a\u307b\u3046\uff1a\u5fa1\uff1a\u304e\u3087\uff1a\u3055\u308c\u305f\u3053\u3068\u304c \u9077\u90fd\u306e\u539f\uff1a\u3052\u3093\uff1a\u56e0\uff1a\u3044\u3093\uff1a\u306e\u3072\u3068\u3064\u3067\u3082\u3042\u3063\u305f\u3068\u3055\u308c\u308b\n794,\u5e73\uff1a\u3078\u3044\uff1a\u5b89\uff1a\u3042\u3093\uff1a\u4eac\uff1a\u304d\u3087\u3046\uff1a\u9077\uff1a\u305b\u3093\uff1a\u90fd\uff1a\u3068\uff1a,\u5ef6\uff1a\u3048\u3093\uff1a\u66a6\uff1a\u308a\u3083\u304f\uff1a13\u5e74 \u7b2c50\u4ee3\u6853\uff1a\u304b\u3093\uff1a\u6b66\uff1a\u3080\uff1a\u5929\u7687 \u9577\uff1a\u306a\u304c\uff1a\u5ca1\uff1a\u304a\u304b\uff1a\u4eac\uff1a\u304d\u3087\u3046\uff1a\u304b\u3089\u9077\u90fd\u3055\u308c\u308b,\u3053\u306e\u5f8c\u5e73\uff1a\u305f\u3044\u3089\uff1a\u6e05\uff1a\u306e\u304d\u3088\uff1a\u76db\uff1a\u3082\u308a\uff1a\u306b\u3088\u308b\u798f\uff1a\u3075\u304f\uff1a\u539f\uff1a\u306f\u3089\uff1a\u4eac\uff1a\u304d\u3087\u3046\uff1a\u9077\u90fd\u3084\u5357\uff1a\u306a\u3093\uff1a\u5317\uff1a\u307c\u304f\uff1a\u671d\uff1a\u3061\u3087\u3046\uff1a\u6642\u4ee3\u306e\u5409\uff1a\u3088\u3057\uff1a\u91ce\uff1a\u306e\uff1a\u306a\u3069\u306e\u4f8b\uff1a\u308c\u3044\uff1a\u5916\uff1a\u304c\u3044\uff1a\u306f\u3042\u308b\u3082\u306e\u306e \u660e\uff1a\u3081\u3044\uff1a\u6cbb\uff1a\u3058\uff1a\u7dad\uff1a\u3044\uff1a\u65b0\uff1a\u3057\u3093\uff1a\u307e\u3067\u5343\u5e74\u4ee5\u4e0a\u7e8c\uff1a\u3064\u3065\uff1a\u304f\n806,\u6700\uff1a\u3055\u3044\uff1a\u6f84\uff1a\u3061\u3087\u3046\uff1a\u304c\u5929\uff1a\u3066\u3093\uff1a\u53f0\uff1a\u3060\u3044\uff1a\u5b97\uff1a\u3057\u3085\u3046\uff1a \u7a7a\uff1a\u304f\u3046\uff1a\u6d77\uff1a\u304b\u3044\uff1a\u304c\u771f\uff1a\u3057\u3093\uff1a\u8a00\uff1a\u3054\u3093\uff1a\u5b97\uff1a\u3057\u3085\u3046\uff1a,\u5e73\uff1a\u3078\u3044\uff1a\u5b89\uff1a\u3042\u3093\uff1a\u6642\uff1a\u3058\uff1a\u4ee3\uff1a\u3060\u3044\uff1a\u521d\uff1a\u3057\u3087\uff1a\u671f\uff1a\u304d\uff1a \u3069\u3061\u3089\u3082\u5510\uff1a\u3068\u3046\uff1a\u3067\u4fee\uff1a\u3057\u3085\uff1a\u884c\uff1a\u304e\u3087\u3046\uff1a\u3057\u5e30\uff1a\u304d\uff1a\u570b\uff1a\u3053\u304f\uff1a\u5f8c\uff1a\u3054\uff1a \u4ecf\uff1a\u3076\u3064\uff1a\u6559\uff1a\u304d\u3087\u3046\uff1a\u3092\u50b3\uff1a\u3064\u305f\uff1a\u3078\u308b,\u6700\uff1a\u3055\u3044\uff1a\u6f84\uff1a\u3061\u3087\u3046\uff1a\u306f\u5929\uff1a\u3066\u3093\uff1a\u53f0\uff1a\u3060\u3044\uff1a\u5b97\uff1a\u3057\u3085\u3046\uff1a\u3092\u958b\uff1a\u3072\u3089\uff1a\u304d \u6bd4\uff1a\u3072\uff1a\u53e1\uff1a\u3048\u3044\uff1a\u5c71\uff1a\u3056\u3093\uff1a\u306b\u5ef6\uff1a\u3048\u3093\uff1a\u66a6\uff1a\u308a\u3083\u304f\uff1a\u5bfa\uff1a\u3058\uff1a\u3092 \u7a7a\uff1a\u304f\u3046\uff1a\u6d77\uff1a\u304b\u3044\uff1a\u306f\u771f\uff1a\u3057\u3093\uff1a\u8a00\uff1a\u3054\u3093\uff1a\u5b97\uff1a\u3057\u3085\u3046\uff1a\u3092\u958b\u304d \u9ad8\uff1a\u3053\u3046\uff1a\u91ce\uff1a\u3084\uff1a\u5c71\uff1a\u3055\u3093\uff1a\u306b\u91d1\uff1a\u3053\u3093\uff1a\u525b\uff1a\u3054\u3046\uff1a\u5cf0\uff1a\u3076\uff1a\u5bfa\uff1a\u3058\uff1a\u3092\u5efa\uff1a\u3053\u3093\uff1a\u7acb\uff1a\u308a\u3085\u3046\uff1a\n857,\u85e4\uff1a\u3075\u3058\uff1a\u539f\uff1a\u308f\u3089\u306e\uff1a\u826f\uff1a\u3088\u3057\uff1a\u623f\uff1a\u3075\u3055\uff1a\u304c\u592a\uff1a\u3060\uff1a\u653f\uff1a\u3058\u3087\u3046\uff1a\u5927\uff1a\u3060\u3044\uff1a\u81e3\uff1a\u3058\u3093\uff1a\u306b,56\u4ee3\u6e05\uff1a\u305b\u3044\uff1a\u548c\uff1a\u308f\uff1a\u5929\u7687\u306e\u6442\uff1a\u305b\u3063\uff1a\u653f\uff1a\u3057\u3087\u3046\uff1a,\u81e3\uff1a\u3057\u3093\uff1a\u4e0b\uff1a\u304b\uff1a\u306e\u8eab\uff1a\u307f\uff1a\u5206\uff1a\u3076\u3093\uff1a\u3067\u521d\u3081\u3066\u6442\uff1a\u305b\u3063\uff1a\u653f\uff1a\u3057\u3087\u3046\uff1a\u306b\u306a\u3063\u305f\n894,\u9063\uff1a\u3051\u3093\uff1a\u5510\uff1a\u3068\u3046\uff1a\u4f7f\uff1a\u3057\uff1a\u304c\u5ec3\uff1a\u306f\u3044\uff1a\u6b62\uff1a\u3057\uff1a\u3055\u308c\u308b,\u83c5\uff1a\u3059\u304c\uff1a\u539f\uff1a\u308f\u3089\u306e\uff1a\u9053\uff1a\u307f\u3061\uff1a\u771f\uff1a\u3056\u306d\uff1a\u306e\u5efa\uff1a\u3051\u3093\uff1a\u8b70\uff1a\u304e\uff1a\u306b\u3088\u308b,\u3053\u306e\u5f8c904\u5e74\u306b\u5510\uff1a\u3068\u3046\uff1a\u306f\u6ec5\uff1a\u307b\u308d\uff1a\u3073\u5c0f\uff1a\u3057\u3087\u3046\uff1a\u570b\uff1a\u3053\u304f\uff1a\u304c\u5206\uff1a\u3076\u3093\uff1a\u7acb\uff1a\u308a\u3064\uff1a\u3057\u305f\u5f8c \u5b8b\uff1a\u305d\u3046\uff1a(\u5317\uff1a\u307b\u304f\uff1a\u5b8b\uff1a\u305d\u3046\uff1a)\u304c\u652f\uff1a\u3057\uff1a\u90a3\uff1a\u306a\uff1a\u5927\uff1a\u305f\u3044\uff1a\u9678\uff1a\u308a\u304f\uff1a\u3092\u7d71\uff1a\u3068\u3046\uff1a\u4e00\uff1a\u3044\u3064\uff1a\u3059\u308b\n935,\u627f\uff1a\u3057\u3087\u3046\uff1a\u5e73\uff1a\u3078\u3044\uff1a\u5929\uff1a\u3066\u3093\uff1a\u6176\uff1a\u304e\u3087\u3046\uff1a\u306e\u4e82\uff1a\u3089\u3093\uff1a,\u5e73\uff1a\u305f\u3044\u3089\uff1a\u5c06\uff1a\u306e\u307e\u3055\uff1a\u9580\uff1a\u304b\u3069\uff1a\u3084\u85e4\uff1a\u3075\u3058\uff1a\u539f\uff1a\u308f\u3089\u306e\uff1a\u7d14\uff1a\u3059\u307f\uff1a\u53cb\uff1a\u3068\u3082\uff1a\u3068\u3044\u3064\u305f\u6b66\uff1a\u3076\uff1a\u58eb\uff1a\u3057\uff1a\u306e\u53cd\uff1a\u306f\u3093\uff1a\u4e82\uff1a\u3089\u3093\uff1a,\u6442\uff1a\u305b\u3063\uff1a\u95a2\uff1a\u304b\u3093\uff1a\u653f\uff1a\u305b\u3044\uff1a\u6cbb\uff1a\u3058\uff1a\u3078\u306e\u4e0d\uff1a\u3075\uff1a\u6e80\uff1a\u307e\u3093\uff1a\u304c\u6839\uff1a\u3053\u3093\uff1a\u5e95\uff1a\u3066\u3044\uff1a\u306b\u3042\u3063\u305f\u3068\u3055\u308c\u308b\n1016,\u85e4\uff1a\u3075\u3058\uff1a\u539f\uff1a\u308f\u3089\u306e\uff1a\u9053\uff1a\u307f\u3061\uff1a\u9577\uff1a\u306a\u304c\uff1a\u304c\u6442\uff1a\u305b\u3063\uff1a\u653f\uff1a\u3057\u3087\u3046\uff1a\u306b,\u85e4\uff1a\u3075\u3058\uff1a\u539f\uff1a\u308f\u3089\uff1a\u6c0f\uff1a\u3057\uff1a\u5168\uff1a\u305c\u3093\uff1a\u76db\uff1a\u305b\u3044\uff1a\u6642\u4ee3\u3068\u3044\u306f\u308c\u308b,\u9053\uff1a\u307f\u3061\uff1a\u9577\uff1a\u306a\u304c\uff1a\u306f\u9577\uff1a\u3061\u3087\u3046\uff1a\u5973\uff1a\u3058\u3087\uff1a\u3092\u4e00\uff1a\u3044\u3061\uff1a\u6761\uff1a\u3058\u3087\u3046\uff1a\u5929\u7687(66\u4ee3)\u306e\u540e\uff1a\u304d\u3055\u304d\uff1a\u306b \u6b21\uff1a\u3058\uff1a\u5973\uff1a\u3058\u3087\uff1a\u3092\u4e09\uff1a\u3055\u3093\uff1a\u6761\uff1a\u3058\u3087\u3046\uff1a\u5929\u7687(67\u4ee3)\u306e\u540e\u306b \u4e09\uff1a\u3055\u3093\uff1a\u5973\uff1a\u3058\u3087\uff1a\u3092\u5f8c\uff1a\u3054\uff1a\u4e00\uff1a\u3044\u3061\uff1a\u6761\uff1a\u3058\u3087\u3046\uff1a\u5929\u7687(68\u4ee3)\u306e\u540e\u306b\u3059\u308b\n1086,\u9662\uff1a\u3044\u3093\uff1a\u653f\uff1a\u305b\u3044\uff1a\u958b\uff1a\u304b\u3044\uff1a\u59cb\uff1a\u3057\uff1a,\u6442\uff1a\u305b\u3063\uff1a\u653f\uff1a\u3057\u3087\u3046\uff1a\u3084\u95a2\uff1a\u304b\u3093\uff1a\u767d\uff1a\u3071\u304f\uff1a\u306e\u529b\uff1a\u3061\u304b\u3089\uff1a\u3092\u6291\uff1a\u304a\u3055\uff1a\u3078\u308b,72\u4ee3\u767d\uff1a\u3057\u3089\uff1a\u6cb3\uff1a\u304b\u306f\uff1a\u5929\u7687\u304c\u8b72\uff1a\u3058\u3087\u3046\uff1a\u4f4d\uff1a\u3044\uff1a\u5f8c \u4e0a\uff1a\u3058\u3087\u3046\uff1a\u7687\uff1a\u3053\u3046\uff1a\u3068\u306a\u308a \u653f\uff1a\u305b\u3044\uff1a\u6cbb\uff1a\u3062\uff1a\u306e\u5b9f\uff1a\u3058\u3063\uff1a\u6a29\uff1a\u3051\u3093\uff1a\u3092\u63e1\uff1a\u306b\u304e\uff1a\u308b\n1167,\u5e73\uff1a\u305f\u3044\u3089\uff1a\u6e05\uff1a\u306e\u304d\u3088\uff1a\u76db\uff1a\u3082\u308a\uff1a\u304c\u592a\uff1a\u3060\uff1a\u653f\uff1a\u3058\u3087\u3046\uff1a\u5927\uff1a\u3060\u3044\uff1a\u81e3\uff1a\u3058\u3093\uff1a\u306b,\u5a18\uff1a\u3080\u3059\u3081\uff1a\u3092\u5929\u7687\u306e\u540e\uff1a\u304d\u3055\u304d\uff1a\u306b\u3057 81\u4ee3\u5b89\uff1a\u3042\u3093\uff1a\u5fb3\uff1a\u3068\u304f\uff1a\u5929\u7687\u304c\u8a95\uff1a\u305f\u3093\uff1a\u751f\uff1a\u3058\u3087\u3046\uff1a,\u6b66\uff1a\u3076\uff1a\u58eb\uff1a\u3057\uff1a\u3068\u3057\u3066\u521d\uff1a\u306f\u3058\uff1a\u3081\u3066\u592a\uff1a\u3060\uff1a\u653f\uff1a\u3058\u3087\u3046\uff1a\u5927\uff1a\u3060\u3044\uff1a\u81e3\uff1a\u3058\u3093\uff1a\u306b\u4efb\uff1a\u306b\u3093\uff1a\u547d\uff1a\u3081\u3044\uff1a\u3055\u308c\u308b\n1185,\u5e73\uff1a\u3078\u3044\uff1a\u5bb6\uff1a\u3051\uff1a\u6ec5\uff1a\u3081\u3064\uff1a\u4ea1\uff1a\u307c\u3046\uff1a,\u58c7\uff1a\u3060\u3093\uff1a\u30ce\uff1a\u306e\uff1a\u6d66\uff1a\u3046\u3089\uff1a\u306e\u6230\uff1a\u305f\u305f\u304b\uff1a\u3072,\u6e90\uff1a\u307f\u306a\u3082\uff1a\u983c\uff1a\u3068\u306e\u3088\uff1a\u671d\uff1a\u308a\u3068\u3082\uff1a\u306e\u547d\uff1a\u3081\u3044\uff1a\u3092\u53d7\uff1a\u3046\uff1a\u3051\u305f \u5f1f\uff1a\u304a\u3068\u3046\u3068\uff1a\u306e\u7fa9\uff1a\u3088\u3057\uff1a\u7d4c\uff1a\u3064\u306d\uff1a\u3089\u306e\u6d3b\uff1a\u304b\u3064\uff1a\u8e8d\uff1a\u3084\u304f\uff1a\u304c\u3042\u3063\u305f \u3053\u306e\u3068\u304d\u5b89\uff1a\u3042\u3093\uff1a\u5fb3\uff1a\u3068\u304f\uff1a\u5929\u7687\u306f\u6578\uff1a\u304b\u305e\uff1a\u3078\u5e74\u4e03\u6b73\uff1a\u3055\u3044\uff1a\u3067\u5165\uff1a\u306b\u3085\u3046\uff1a\u6c34\uff1a\u3059\u3044\uff1a\u3057\u5d29\uff1a\u307b\u3046\uff1a\u5fa1\uff1a\u304e\u3087\uff1a\u3055\u308c\u308b\n1192,\u6e90\uff1a\u307f\u306a\u3082\uff1a\u983c\uff1a\u3068\u306e\u3088\uff1a\u671d\uff1a\u308a\u3068\u3082\uff1a\u304c\u5f81\uff1a\u305b\u3044\uff1a\u5937\uff1a\u3044\uff1a\u5927\uff1a\u305f\u3044\uff1a\u5c06\uff1a\u3057\u3087\u3046\uff1a\u8ecd\uff1a\u3050\u3093\uff1a\u306b,\u6b66\uff1a\u3076\uff1a\u5bb6\uff1a\u3051\uff1a\u653f\uff1a\u305b\u3044\uff1a\u6a29\uff1a\u3051\u3093\uff1a\u304c\u672c\uff1a\u307b\u3093\uff1a\u683c\uff1a\u304b\u304f\uff1a\u7684\uff1a\u3066\u304d\uff1a\u306b\u59cb\uff1a\u306f\u3058\uff1a\u307e\u308b\u938c\uff1a\u304b\u307e\uff1a\u5009\uff1a\u304f\u3089\uff1a\u5e55\uff1a\u3070\u304f\uff1a\u5e9c\uff1a\u3075\uff1a\u6210\uff1a\u305b\u3044\uff1a\u7acb\uff1a\u308a\u3064\uff1a\n1221,\u627f\uff1a\u3058\u3087\u3046\uff1a\u4e45\uff1a\u304d\u3085\u3046\uff1a\u306e\u8b8a\uff1a\u3078\u3093\uff1a,\u5168\uff1a\u305c\u3093\uff1a\u570b\uff1a\u3053\u304f\uff1a\u306e\u6b66\uff1a\u3076\uff1a\u58eb\uff1a\u3057\uff1a\u306b \u57f7\uff1a\u3057\u3063\uff1a\u6a29\uff1a\u3051\u3093\uff1a\u5317\uff1a\u307b\u3046\uff1a\u6761\uff1a\u3058\u3087\u3046\uff1a\u7fa9\uff1a\u3088\u3057\uff1a\u6642\uff1a\u3068\u304d\uff1a\u306e\u8a0e\uff1a\u3068\u3046\uff1a\u4f10\uff1a\u3070\u3064\uff1a\u3092\u547d\uff1a\u3081\u3044\uff1a\u305a\u308b\u5f8c\uff1a\u3054\uff1a\u9ce5\uff1a\u3068\uff1a\u7fbd\uff1a\u3070\uff1a\u4e0a\uff1a\u3058\u3087\u3046\uff1a\u7687\uff1a\u3053\u3046\uff1a\u306e\u9662\uff1a\u3044\u3093\uff1a\u5ba3\uff1a\u305b\u3093\uff1a\u304c\u767c\uff1a\u306f\u3063\uff1a\u305b\u3089\u308c\u308b,\u4eac\uff1a\u304d\u3087\u3046\uff1a\u90fd\uff1a\u3068\uff1a\u306f\u5e55\uff1a\u3070\u304f\uff1a\u5e9c\uff1a\u3075\uff1a\u8ecd\uff1a\u3050\u3093\uff1a\u306b\u5360\uff1a\u305b\u3093\uff1a\u9818\uff1a\u308a\u3087\u3046\uff1a\u3055\u308c\u5931\uff1a\u3057\u3063\uff1a\u6557\uff1a\u3071\u3044\uff1a \n1274,\u6587\uff1a\u3076\u3093\uff1a\u6c38\uff1a\u3048\u3044\uff1a\u306e\u5f79\uff1a\u3048\u304d\uff1a,1281\u5e74\u306e\u5f18\uff1a\u3053\u3046\uff1a\u5b89\uff1a\u3042\u3093\uff1a\u306e\u5f79\uff1a\u3048\u304d\uff1a\u3068\u5408\uff1a\u3042\uff1a\u306f\u305b\u3066 \u5143\uff1a\u3052\u3093\uff1a\u5bc7\uff1a\u3053\u3046\uff1a\u3068\u547c\uff1a\u3088\uff1a\u3076,\u7d04\u4e09\u4e07\u306e\u5143\uff1a\u3052\u3093\uff1a\u8ecd\uff1a\u3050\u3093\uff1a\u304c\u7d04\uff1a\u3084\u304f\uff1a900\u96bb\uff1a\u305b\u304d\uff1a\u306e\u8ecd\uff1a\u3050\u3093\uff1a\u8239\uff1a\u305b\u3093\uff1a\u3067\u5317\uff1a\u304d\u305f\uff1a\u4e5d\uff1a\u304d\u3085\u3046\uff1a\u5dde\uff1a\u3057\u3085\u3046\uff1a\u3078\u9032\uff1a\u3057\u3093\uff1a\u653b\uff1a\u3053\u3046\uff1a\u3059\u308b\u3082\u65e5\uff1a\u306b\uff1a\u672c\uff1a\u307b\u3093\uff1a\u8ecd\uff1a\u3050\u3093\uff1a\u306b\u6483\uff1a\u3052\u304d\uff1a\u9000\uff1a\u305f\u3044\uff1a\u3055\u308c\u308b\n1334,\u5efa\uff1a\u3051\u3093\uff1a\u6b66\uff1a\u3080\uff1a\u306e\u65b0\uff1a\u3057\u3093\uff1a\u653f\uff1a\u305b\u3044\uff1a,\u5f8c\uff1a\u3054\uff1a\u918d\uff1a\u3060\u3044\uff1a\u9190\uff1a\u3054\uff1a\u5929\u7687\u304c\u938c\uff1a\u304b\u307e\uff1a\u5009\uff1a\u304f\u3089\uff1a\u5e55\uff1a\u3070\u304f\uff1a\u5e9c\uff1a\u3075\uff1a\u3092\u5012\uff1a\u305f\u304a\uff1a\u3057\u5929\u7687\u4e2d\u5fc3\u306e\u653f\uff1a\u305b\u3044\uff1a\u6cbb\uff1a\u3062\uff1a\u3092\u5fd7\uff1a\u3053\u3053\u308d\u3056\uff1a\u3059,\u4e8c\u5e74\u3042\u307e\u308a\u3067\u6b66\u58eb\u304c\u96e2\uff1a\u308a\uff1a\u53cd\uff1a\u306f\u3093\uff1a\u3057 \u5f8c\uff1a\u3054\uff1a\u918d\uff1a\u3060\u3044\uff1a\u9190\uff1a\u3054\uff1a\u5929\u7687\u306f\u5409\uff1a\u3088\u3057\uff1a\u91ce\uff1a\u306e\uff1a\u306b\u9003\uff1a\u306e\u304c\uff1a\u308c \u5357\uff1a\u306a\u3093\uff1a\u671d\uff1a\u3061\u3087\u3046\uff1a\u3092\u958b\uff1a\u3072\u3089\uff1a\u304d \u8db3\uff1a\u3042\u3057\uff1a\u5229\uff1a\u304b\u304c\uff1a\u5c0a\uff1a\u305f\u304b\uff1a\u6c0f\uff1a\u3046\u3058\uff1a\u306f\u5149\uff1a\u3053\u3046\uff1a\u660e\uff1a\u3081\u3044\uff1a\u5929\u7687\u3092\u64c1\uff1a\u3088\u3046\uff1a\u3057\u305f\u5317\uff1a\u307b\u304f\uff1a\u671d\uff1a\u3061\u3087\u3046\uff1a\u3092\u958b\u304f\n1338,\u5ba4\uff1a\u3080\u308d\uff1a\u753a\uff1a\u307e\u3061\uff1a\u5e55\uff1a\u3070\u304f\uff1a\u5e9c\uff1a\u3075\uff1a\u6210\uff1a\u305b\u3044\uff1a\u7acb\uff1a\u308a\u3064\uff1a,\u8db3\uff1a\u3042\u3057\uff1a\u5229\uff1a\u304b\u304c\uff1a\u5c0a\uff1a\u305f\u304b\uff1a\u6c0f\uff1a\u3046\u3058\uff1a\u304c\u5317\uff1a\u307b\u304f\uff1a\u671d\uff1a\u3061\u3087\u3046\uff1a\u306e\u5149\uff1a\u3053\u3046\uff1a\u660e\uff1a\u3081\u3044\uff1a\u5929\u7687\u3088\u308a\u5f81\uff1a\u305b\u3044\uff1a\u5937\uff1a\u3044\uff1a\u5927\uff1a\u305f\u3044\uff1a\u5c06\uff1a\u3057\u3087\u3046\uff1a\u8ecd\uff1a\u3050\u3093\uff1a\u306b\u4efb\uff1a\u306b\u3093\uff1a\u3058\u3089\u308c\u308b\u3053\u3068\u306b\u3088\u308a\u6210\uff1a\u305b\u3044\uff1a\u7acb\uff1a\u308a\u3064\uff1a,\u8db3\uff1a\u3042\u3057\uff1a\u5229\uff1a\u304b\u304c\uff1a\u7fa9\uff1a\u3088\u3057\uff1a\u6e80\uff1a\u307f\u3064\uff1a(3\u4ee3)\u304c\u4eac\uff1a\u304d\u3087\u3046\uff1a\u90fd\uff1a\u3068\uff1a\u306e\u5ba4\uff1a\u3080\u308d\uff1a\u753a\uff1a\u307e\u3061\uff1a\u306b<\u82b1\uff1a\u306f\u306a\uff1a\u306e\u5fa1\uff1a\u3054\uff1a\u6240\uff1a\u3057\u3087\uff1a>\u3092\u69cb\uff1a\u304b\u307e\uff1a\u3078\u653f\u6cbb\u3092\u884c\uff1a\u304a\u3053\u306a\uff1a\u3063\u305f\u3053\u3068\u304b\u3089<\u5ba4\u753a\u5e55\u5e9c>\u3068\u79f0\uff1a\u3057\u3087\u3046\uff1a\u3055\u308c\u308b\n1429,\u7409\uff1a\u308a\u3085\u3046\uff1a\u7403\uff1a\u304d\u3085\u3046\uff1a\u7d71\uff1a\u3068\u3046\uff1a\u4e00\uff1a\u3044\u3064\uff1a,\u4e09\u3064\u306e\u52e2\uff1a\u305b\u3044\uff1a\u529b\uff1a\u308a\u3087\u304f\uff1a\u304c\u5341\u4e94\u4e16\uff1a\u305b\u3044\uff1a\u7d00\uff1a\u304d\uff1a\u306b\u7d71\uff1a\u3068\u3046\uff1a\u4e00\uff1a\u3044\u3064\uff1a\u3055\u308c\u308b,\u660e\uff1a\u307f\u3093\uff1a\u306e\u518a\uff1a\u3055\u304f\uff1a\u5c01\uff1a\u307b\u3046\uff1a\u3092\u53d7\uff1a\u3046\uff1a\u3051 \u671d\uff1a\u3061\u3087\u3046\uff1a\u8ca2\uff1a\u3053\u3046\uff1a\u8cbf\uff1a\u307c\u3046\uff1a\u6613\uff1a\u3048\u304d\uff1a\u3092\u884c\uff1a\u304a\u3053\u306a\uff1a\u3075\n1467,\u61c9\uff1a\u304a\u3046\uff1a\u4ec1\uff1a\u306b\u3093\uff1a\u306e\u4e82\uff1a\u3089\u3093\uff1a,\u6230\uff1a\u305b\u3093\uff1a\u570b\uff1a\u3054\u304f\uff1a\u6642\uff1a\u3058\uff1a\u4ee3\uff1a\u3060\u3044\uff1a\u306e\u5e55\uff1a\u307e\u304f\uff1a\u958b\uff1a\u3042\uff1a\u3051,\u5c06\uff1a\u3057\u3087\u3046\uff1a\u8ecd\uff1a\u3050\u3093\uff1a\u5bb6\uff1a\u3051\uff1a\u3068\u7ba1\uff1a\u304b\u3093\uff1a\u9818\uff1a\u308c\u3044\uff1a\u5bb6\uff1a\u3051\uff1a\u306e\u8de1\uff1a\u3042\u3068\uff1a\u7d99\uff1a\u3064\u304e\uff1a\u304e\u722d\uff1a\u3042\u3089\u305d\uff1a\u3072\u304c11\u5e74\u7e8c\uff1a\u3064\u3065\uff1a\u304d\u4eac\uff1a\u304d\u3087\u3046\uff1a\u90fd\uff1a\u3068\uff1a\u306e\u753a\uff1a\u307e\u3061\uff1a\u306f\u7126\uff1a\u3057\u3087\u3046\uff1a\u571f\uff1a\u3069\uff1a\u3068\u5316\uff1a\u304b\uff1a\u3059\n1495,\u5317\uff1a\u307b\u3046\uff1a\u6761\uff1a\u3067\u3046\uff1a\u65e9\uff1a\u3055\u3046\uff1a\u96f2\uff1a\u3046\u3093\uff1a\u304c\u5c0f\uff1a\u304a\uff1a\u7530\uff1a\u3060\uff1a\u539f\uff1a\u306f\u3089\uff1a\u5165\uff1a\u306b\u3075\uff1a\u57ce\uff1a\u3058\u3083\u3046\uff1a,\u5317\uff1a\u307b\u3046\uff1a\u6761\uff1a\u3067\u3046\uff1a\u65e9\uff1a\u3055\u3046\uff1a\u96f2\uff1a\u3046\u3093\uff1a\u306f\u6230\uff1a\u305b\u3093\uff1a\u570b\uff1a\u3054\u304f\uff1a\u5927\uff1a\u3060\u3044\uff1a\u540d\uff1a\u307f\u3084\u3046\uff1a\u306e\u5148\uff1a\u3055\u304d\uff1a\u99c6\uff1a\u304c\uff1a\u3051\u3068\u8a00\u306f\u308c\u308b,\u65e9\u96f2\u304c\u95a2\uff1a\u304f\u308f\u3093\uff1a\u6771\uff1a\u3068\u3046\uff1a\u4e00\uff1a\u3044\u3061\uff1a\u5186\uff1a\u3048\u3093\uff1a\u3092\u652f\uff1a\u3057\uff1a\u914d\uff1a\u306f\u3044\uff1a\u3059\u308b\u5927\u540d\u306b\u306a\u3063\u305f\u904e\uff1a\u304b\uff1a\u7a0b\uff1a\u3066\u3044\uff1a\u306f \u5bb6\uff1a\u304b\uff1a\u81e3\uff1a\u3057\u3093\uff1a\u304c\u4e3b\uff1a\u3057\u3085\uff1a\u541b\uff1a\u304f\u3093\uff1a\u304b\u3089\u6a29\uff1a\u3051\u3093\uff1a\u529b\uff1a\u308a\u3087\u304f\uff1a\u3092\u596a\uff1a\u3046\u3070\uff1a\u3063\u3066\u306e\u3057\u4e0a\uff1a\u3042\u304c\uff1a\u308b\u3068\u3044\u3075<\u4e0b\uff1a\u3052\uff1a\u524b\uff1a\u3053\u304f\uff1a\u4e0a\uff1a\u3058\u3083\u3046\uff1a>\u3067\u3042\u308a \u65e9\u96f2\u306f\u6230\u570b\u5927\u540d\u306e\u5686\uff1a\u304b\u3046\uff1a\u77e2\uff1a\u3057\uff1a\u3068\u3044\u3078\u308b\n1542,\u658e\uff1a\u3055\u3044\uff1a\u85e4\uff1a\u3068\u3046\uff1a\u9053\uff1a\u3069\u3046\uff1a\u4e09\uff1a\u3056\u3093\uff1a\u304c\u7f8e\uff1a\u307f\uff1a\u6fc3\uff1a\u306e\uff1a\u3092\u596a\uff1a\u3046\u3070\uff1a\u3046,\u6230\uff1a\u305b\u3093\uff1a\u570b\uff1a\u3054\u304f\uff1a\u6b66\uff1a\u3076\uff1a\u5c06\uff1a\u3057\u3083\u3046\uff1a\u306e\u4e00\uff1a\u3044\u3061\uff1a,\u4ed6\uff1a\u307b\u304b\uff1a\u306b\u3082\u95a2\uff1a\u304f\u308f\u3093\uff1a\u6771\uff1a\u3068\u3046\uff1a\u4e00\uff1a\u3044\u3061\uff1a\u5186\uff1a\u3048\u3093\uff1a\u3092\u652f\uff1a\u3057\uff1a\u914d\uff1a\u306f\u3044\uff1a\u3057\u305f\u5317\uff1a\u307b\u3046\uff1a\u6761\uff1a\u3067\u3046\uff1a\u6c0f\uff1a\u3046\u3058\uff1a\u5eb7\uff1a\u3084\u3059\uff1a \u7532\uff1a\u304b\uff1a\u6590\uff1a\u3072\uff1a\u306e\u6b66\uff1a\u305f\u3051\uff1a\u7530\uff1a\u3060\uff1a\u4fe1\uff1a\u3057\u3093\uff1a\u7384\uff1a\u3052\u3093\uff1a \u8d8a\uff1a\u3048\u3061\uff1a\u5f8c\uff1a\u3054\uff1a\u306e\u4e0a\uff1a\u3046\u3048\uff1a\u6749\uff1a\u3059\u304e\uff1a\u8b19\uff1a\u3051\u3093\uff1a\u4fe1\uff1a\u3057\u3093\uff1a \u51fa\uff1a\u3067\uff1a\u7fbd\uff1a\u306f\uff1a\u3068\u9678\uff1a\u3080\uff1a\u5965\uff1a\u3064\uff1a\u306e\u4f0a\uff1a\u3060\uff1a\u9054\uff1a\u3066\uff1a\u6b63\uff1a\u307e\u3055\uff1a\u5b97\uff1a\u3080\u306d\uff1a \u5b89\uff1a\u3042\uff1a\u82b8\uff1a\u304d\uff1a\u306e\u6bdb\uff1a\u3082\u3046\uff1a\u5229\uff1a\u308a\uff1a\u5143\uff1a\u3082\u3068\uff1a\u5c31\uff1a\u306a\u308a\uff1a \u571f\uff1a\u3068\uff1a\u4f50\uff1a\u3055\uff1a\u306e\u9577\uff1a\u3061\u3083\u3046\uff1a\u5b97\uff1a\u305d\uff1a\u6211\uff1a\u304b\uff1a\u90e8\uff1a\u3079\uff1a\u5143\uff1a\u3082\u3068\uff1a\u89aa\uff1a\u3061\u304b\uff1a \u85a9\uff1a\u3055\u3064\uff1a\u6469\uff1a\u307e\uff1a\u306e\u5cf6\uff1a\u3057\u307e\uff1a\u6d25\uff1a\u3065\uff1a\u8cb4\uff1a\u3088\u3057\uff1a\u4e45\uff1a\u3072\u3055\uff1a\u306a\u3069\u304c\u3090\u305f\n1553,\u5ddd\uff1a\u304b\u306f\uff1a\u4e2d\uff1a\u306a\u304b\uff1a\u5cf6\uff1a\u3058\u307e\uff1a\u306e\u6230\uff1a\u305f\u305f\u304b\u3072\uff1a,\u7532\uff1a\u304b\uff1a\u6590\uff1a\u3072\uff1a\u306e\u6b66\uff1a\u305f\u3051\uff1a\u7530\uff1a\u3060\uff1a\u4fe1\uff1a\u3057\u3093\uff1a\u7384\uff1a\u3052\u3093\uff1a\u3068\u8d8a\uff1a\u3048\u3061\uff1a\u5f8c\uff1a\u3054\uff1a\u306e\u4e0a\uff1a\u3046\u3078\uff1a\u6749\uff1a\u3059\u304e\uff1a\u8b19\uff1a\u3051\u3093\uff1a\u4fe1\uff1a\u3057\u3093\uff1a,\u6230\uff1a\u305b\u3093\uff1a\u570b\uff1a\u3054\u304f\uff1a\u6642\uff1a\u3058\uff1a\u4ee3\uff1a\u3060\u3044\uff1a\u306e\u975e\uff1a\u3072\uff1a\u5e38\uff1a\u3058\u3083\u3046\uff1a\u306b\u6709\uff1a\u3044\u3046\uff1a\u540d\uff1a\u3081\u3044\uff1a\u306a\u6230\uff1a\u305f\u305f\u304b\uff1a\u3072\u3067\u52dd\uff1a\u3057\u3087\u3046\uff1a\u6557\uff1a\u306f\u3044\uff1a\u306f\u8af8\uff1a\u3057\u3087\uff1a\u8aac\uff1a\u305b\u3064\uff1a\u3042\u308b\u3082\u5b9a\uff1a\u3055\u3060\uff1a\u307e\u3063\u3066\u3090\u306a\u3044\n1560,\u6876\uff1a\u304a\u3051\uff1a\u72ed\uff1a\u306f\u3056\uff1a\u9593\uff1a\u307e\uff1a\u306e\u6230\uff1a\u305f\u305f\u304b\u3072\uff1a,\u5c3e\uff1a\u3092\uff1a\u5f35\uff1a\u306f\u308a\uff1a\u306e\u7e54\uff1a\u304a\uff1a\u7530\uff1a\u3060\uff1a\u4fe1\uff1a\u306e\u3076\uff1a\u9577\uff1a\u306a\u304c\uff1a\u304c\u99ff\uff1a\u3059\u308b\uff1a\u6cb3\uff1a\u304c\uff1a\u306e\u4eca\uff1a\u3044\u307e\uff1a\u5ddd\uff1a\u304c\u306f\uff1a\u7fa9\uff1a\u3088\u3057\uff1a\u5143\uff1a\u3082\u3068\uff1a\u3092\u7834\uff1a\u3084\u3076\uff1a\u308b,\u4fe1\uff1a\u306e\u3076\uff1a\u9577\uff1a\u306a\u304c\uff1a\u306f\u5c3e\uff1a\u3092\uff1a\u5f35\uff1a\u306f\u308a\uff1a\u3068\u7f8e\uff1a\u307f\uff1a\u6fc3\uff1a\u306e\uff1a\u3092\u652f\uff1a\u3057\uff1a\u914d\uff1a\u306f\u3044\uff1a\u4e0b\uff1a\u304b\uff1a\u306b\u304a\u304d <\u5929\uff1a\u3066\u3093\uff1a\u4e0b\uff1a\u304b\uff1a\u5e03\uff1a\u3075\uff1a\u6b66\uff1a\u3076\uff1a>\u3092\u304b\u304b\u3052 \u5f8c\uff1a\u306e\u3061\uff1a\u306b\u8db3\uff1a\u3042\u3057\uff1a\u5229\uff1a\u304b\u304c\uff1a\u7fa9\uff1a\u3088\u3057\uff1a\u662d\uff1a\u3042\u304d\uff1a\u3092\u4eac\uff1a\u304d\u3083\u3046\uff1a\u90fd\uff1a\u3068\uff1a\u304b\u3089\u8ffd\uff1a\u3064\u3044\uff1a\u653e\uff1a\u306f\u3046\uff1a\u3057\u3066\u5ba4\uff1a\u3080\u308d\uff1a\u753a\uff1a\u307e\u3061\uff1a\u5e55\uff1a\u3070\u304f\uff1a\u5e9c\uff1a\u3075\uff1a\u3092\u6ec5\uff1a\u3081\u3064\uff1a\u4ea1\uff1a\u3070\u3046\uff1a\u3055\u305b\u308b\n1590,\u8c4a\uff1a\u3068\u3088\uff1a\u81e3\uff1a\u3068\u307f\uff1a\u79c0\uff1a\u3072\u3067\uff1a\u5409\uff1a\u3088\u3057\uff1a\u306e\u5929\uff1a\u3066\u3093\uff1a\u4e0b\uff1a\u304b\uff1a\u7d71\uff1a\u3068\u3046\uff1a\u4e00\uff1a\u3044\u3064\uff1a,106\u4ee3\u6b63\uff1a\u304a\u307b\uff1a\u89aa\uff1a\u304e\uff1a\u753a\uff1a\u307e\u3061\uff1a\u5929\u7687\u304b\u3089\u95a2\uff1a\u304b\u3093\uff1a\u767d\uff1a\u3071\u304f\uff1a\u306e\u4f4d\uff1a\u304f\u3089\u3090\uff1a\u3092\u6388\uff1a\u3055\u3065\uff1a\u3051\u3089\u308c \u5929\uff1a\u3066\u3093\uff1a\u4e0b\uff1a\u304b\uff1a\u7d71\uff1a\u3068\u3046\uff1a\u4e00\uff1a\u3044\u3064\uff1a\u3078\u306e\u5f8c\uff1a\u3042\u3068\uff1a\u62bc\uff1a\u304a\uff1a\u3057\u3092\u3082\u3089\u3075,\u60e3\uff1a\u3055\u3046\uff1a\u7121\uff1a\u3076\uff1a\u4e8b\uff1a\u3058\uff1a\u4ee4\uff1a\u308c\u3044\uff1a\u3092\u51fa\uff1a\u3060\uff1a\u3057\u3066\u5927\uff1a\u3060\u3044\uff1a\u540d\uff1a\u307f\u3084\u3046\uff1a\u9593\uff1a\u304b\u3093\uff1a\u306e\u79c1\uff1a\u3057\uff1a\u95d8\uff1a\u305f\u3046\uff1a\u3092\u7981\uff1a\u304d\u3093\uff1a\u3058 \u5929\uff1a\u3066\u3093\uff1a\u7687\uff1a\u308f\u3046\uff1a\u3088\u308a\u8c4a\uff1a\u3068\u3088\uff1a\u81e3\uff1a\u3068\u307f\uff1a\u306e\u59d3\uff1a\u305b\u3044\uff1a\u3092\u8cdc\uff1a\u305f\u307e\u306f\uff1a\u308a \u592a\uff1a\u3060\uff1a\u653f\uff1a\u3058\u3083\u3046\uff1a\u5927\uff1a\u3060\u3044\uff1a\u81e3\uff1a\u3058\u3093\uff1a\u306b\u4efb\uff1a\u306b\u3093\uff1a\u547d\uff1a\u3081\u3044\uff1a\u3055\u308c \u5cf6\uff1a\u3057\u307e\uff1a\u6d25\uff1a\u3065\uff1a\u7fa9\uff1a\u3088\u3057\uff1a\u4e45\uff1a\u3072\u3055\uff1a \u5317\uff1a\u307b\u3046\uff1a\u6761\uff1a\u3067\u3046\uff1a\u6c0f\uff1a\u3046\u3058\uff1a\u653f\uff1a\u307e\u3055\uff1a \u4f0a\uff1a\u3060\uff1a\u9054\uff1a\u3066\uff1a\u653f\uff1a\u307e\u3055\uff1a\u5b97\uff1a\u3080\u306d\uff1a\u3089\u8af8\uff1a\u3057\u3087\uff1a\u5927\uff1a\u3060\u3044\uff1a\u540d\uff1a\u307f\u3083\u3046\uff1a\u3092\u5e73\uff1a\u3078\u3044\uff1a\u5b9a\uff1a\u3066\u3044\uff1a\u3057\u3066 \u5929\u4e0b\u7d71\u4e00\n1592,\u6587\uff1a\u3076\u3093\uff1a\u7984\uff1a\u308d\u304f\uff1a\u306e\u5f79\uff1a\u3048\u304d\uff1a,\u79c0\uff1a\u3072\u3067\uff1a\u5409\uff1a\u3088\u3057\uff1a\u306e\u671d\uff1a\u3066\u3046\uff1a\u9bae\uff1a\u305b\u3093\uff1a\u51fa\uff1a\u3057\u3085\u3063\uff1a\u5175\uff1a\u307a\u3044\uff1a,\u4e8c\uff1a\u306b\uff1a\u5ea6\uff1a\u3069\uff1a\u76ee\uff1a\u3081\uff1a\u306e\u6176\uff1a\u3051\u3044\uff1a\u9577\uff1a\u3061\u3083\u3046\uff1a\u306e\u5f79\uff1a\u3048\u304d\uff1a\u3067\u79c0\uff1a\u3072\u3067\uff1a\u5409\uff1a\u3088\u3057\uff1a\u304c\u6ca1\uff1a\u307c\u3063\uff1a\u3057 \u65e5\uff1a\u306b\uff1a\u672c\uff1a\u307b\u3093\uff1a\u8ecd\uff1a\u3050\u3093\uff1a\u306f\u671d\uff1a\u3066\u3046\uff1a\u9bae\uff1a\u305b\u3093\uff1a\u304b\u3089\u64a4\uff1a\u3066\u3063\uff1a\u9000\uff1a\u305f\u3044\uff1a\n1600,\u95a2\uff1a\u305b\u304d\uff1a\u30f6\uff1a\u304c\uff1a\u539f\uff1a\u306f\u3089\uff1a\u306e\u6230\uff1a\u305f\u305f\u304b\u3072\uff1a,\u3053\u306e\u6230\uff1a\u305f\u305f\u304b\uff1a\u3072\u306b\u52dd\uff1a\u3057\u3087\u3046\uff1a\u5229\uff1a\u308a\uff1a\u3057\u305f\u5fb3\uff1a\u3068\u304f\uff1a\u5ddd\uff1a\u304c\u306f\uff1a\u5bb6\uff1a\u3044\u3078\uff1a\u5eb7\uff1a\u3084\u3059\uff1a\u304c \u5f8c\uff1a\u3054\uff1a\u967d\uff1a\u3084\u3046\uff1a\u6210\uff1a\u305c\u3044\uff1a\u5929\u7687\u306b\u3088\u308a\u5f81\uff1a\u305b\u3044\uff1a\u5937\uff1a\u3044\uff1a\u5927\uff1a\u305f\u3044\uff1a\u5c06\uff1a\u3057\u3083\u3046\uff1a\u8ecd\uff1a\u3050\u3093\uff1a\u306b\u4efb\uff1a\u306b\u3093\uff1a\u547d\uff1a\u3081\u3044\uff1a\u3055\u308c \u6c5f\uff1a\u3048\uff1a\u6238\uff1a\u3069\uff1a\u5e55\uff1a\u3070\u304f\uff1a\u5e9c\uff1a\u3075\u304c\uff1a\u6210\uff1a\u305b\u3044\uff1a\u7acb\uff1a\u308a\u3064\uff1a,\u8c4a\uff1a\u3068\u3088\uff1a\u81e3\uff1a\u3068\u307f\uff1a\u653f\uff1a\u305b\u3044\uff1a\u6a29\uff1a\u3051\u3093\uff1a\u306b\u304a\u3051\u308b\u4e94\uff1a\u3054\uff1a\u5927\uff1a\u305f\u3044\uff1a\u8001\uff1a\u3089\u3046\uff1a\u306e\u7b46\uff1a\u3072\u3063\uff1a\u982d\uff1a\u3068\u3046\uff1a\u3067\u3042\u3063\u305f\u5fb3\uff1a\u3068\u304f\uff1a\u5ddd\uff1a\u304c\u306f\uff1a\u5bb6\uff1a\u3044\u3078\uff1a\u5eb7\uff1a\u3084\u3059\uff1a\u304c \u8c4a\uff1a\u3068\u3088\uff1a\u81e3\uff1a\u3068\u307f\uff1a\u6c0f\uff1a\u3057\uff1a\u306e\u652f\uff1a\u3057\uff1a\u914d\uff1a\u306f\u3044\uff1a\u614b\uff1a\u305f\u3044\uff1a\u52e2\uff1a\u305b\u3044\uff1a\u3092\u7dad\uff1a\u3090\uff1a\u6301\uff1a\u3062\uff1a\u3057\u3084\u3046\u3068\u3059\u308b\u77f3\uff1a\u3044\u3057\uff1a\u7530\uff1a\u3060\uff1a\u4e09\uff1a\u307f\u3064\uff1a\u6210\uff1a\u306a\u308a\uff1a\u3068\u95a2\uff1a\u305b\u304d\uff1a\u30f6\uff1a\u304c\uff1a\u539f\uff1a\u306f\u3089\uff1a\u3067\u5c0d\uff1a\u305f\u3044\uff1a\u6c7a\uff1a\u3051\u3064\uff1a\u30fc\u5929\uff1a\u3066\u3093\uff1a\u4e0b\uff1a\u304b\uff1a\u5206\uff1a\u308f\uff1a\u3051\u76ee\uff1a\u3081\uff1a\u306e\u6230\uff1a\u305f\u305f\u304b\uff1a\u3072\u3068\u3044\u306f\u308c \u6771\uff1a\u3068\u3046\uff1a\u8ecd\uff1a\u3050\u3093\uff1a\u3067\u3042\u308b\u5fb3\u5ddd\u5bb6\u5eb7\u304c\u52dd\uff1a\u3057\u3087\u3046\uff1a\u5229\uff1a\u308a\uff1a\u3057\u305f\n1637,\u5cf6\uff1a\u3057\u307e\uff1a\u539f\uff1a\u3070\u3089\uff1a\u306e\u4e82\uff1a\u3089\u3093\uff1a,\u3044\u306f\u3086\u308b<\u9396\uff1a\u3055\uff1a\u570b\uff1a\u3053\u304f\uff1a>\u653f\uff1a\u305b\u3044\uff1a\u7b56\uff1a\u3055\u304f\uff1a\u306e\u5f15\uff1a\u3072\uff1a\u304d\u91d1\uff1a\u304c\u306d\uff1a\u3068\u3082\u306a\u3064\u305f,\u30ad\u30ea\u30b9\u30c8\u6559\uff1a\u3051\u3046\uff1a\u5f92\uff1a\u3068\uff1a\u3089\u304c\u5bfa\uff1a\u3058\uff1a\u793e\uff1a\u3057\u3083\uff1a\u306b\u653e\uff1a\u306f\u3046\uff1a\u706b\uff1a\u304f\u308f\uff1a\u3057\u50e7\uff1a\u305d\u3046\uff1a\u4fb6\uff1a\u308a\u3087\uff1a\u3092\u6bba\uff1a\u3055\u3064\uff1a\u5bb3\uff1a\u304c\u3044\uff1a\u3059\u308b\u306a\u3069\u3057\u305f\u305f\u3081 \u5e55\uff1a\u3070\u304f\uff1a\u5e9c\uff1a\u3075\uff1a\u306f\u5927\uff1a\u305f\u3044\uff1a\u8ecd\uff1a\u3050\u3093\uff1a\u3092\u9001\uff1a\u304a\u304f\uff1a\u308a\u93ae\uff1a\u3061\u3093\uff1a\u58d3\uff1a\u3042\u3064\uff1a\u3059\u308b\n1685,\u751f\uff1a\u3057\u3083\u3046\uff1a\u985e\uff1a\u308b\uff1a\u6190\uff1a\u3042\u306f\u308c\uff1a\u307f\u306e\u4ee4\uff1a\u308c\u3044\uff1a,\u4e94\uff1a\u3054\uff1a\u4ee3\uff1a\u3060\u3044\uff1a\u5c06\uff1a\u3057\u3083\u3046\uff1a\u8ecd\uff1a\u3050\u3093\uff1a \u5fb3\uff1a\u3068\u304f\uff1a\u5ddd\uff1a\u304c\u306f\uff1a\u7db1\uff1a\u3064\u306a\uff1a\u5409\uff1a\u3088\u3057\uff1a,\u75c5\uff1a\u3073\u3083\u3046\uff1a\u4eba\uff1a\u306b\u3093\uff1a\u907a\uff1a\u3090\uff1a\u68c4\uff1a\u304d\uff1a\u3084\u6368\uff1a\u3059\uff1a\u3066\u5b50\uff1a\u3054\uff1a\u3092\u7981\uff1a\u304d\u3093\uff1a\u6b62\uff1a\u3057\uff1a \u4eba\uff1a\u306b\u3093\uff1a\u9593\uff1a\u3052\u3093\uff1a\u4ee5\uff1a\u3044\uff1a\u5916\uff1a\u3050\u308f\u3044\uff1a\u306e\u3042\u3089\u3086\u308b\u751f\uff1a\u305b\u3044\uff1a\u7269\uff1a\u3076\u3064\uff1a\u3078\u306e\u8650\uff1a\u304e\u3083\u304f\uff1a\u5f85\uff1a\u305f\u3044\uff1a\u3084\u6bba\uff1a\u305b\u3063\uff1a\u751f\uff1a\u3057\u3083\u3046\uff1a\u3092\u3082\u7f70\uff1a\u3070\u3064\uff1a\u3059\u308b\u3053\u3068\u3067 \u9053\uff1a\u3060\u3046\uff1a\u5fb3\uff1a\u3068\u304f\uff1a\u5fc3\uff1a\u3057\u3093\uff1a\u3092\u559a\uff1a\u304b\u3093\uff1a\u8d77\uff1a\u304d\uff1a\u3057\u3084\u3046\u3068\u3057\u305f\u3068\u3055\u308c\u308b\n1716,\u4eab\uff1a\u304d\u3084\u3046\uff1a\u4fdd\uff1a\u307b\u3046\uff1a\u306e\u6539\uff1a\u304b\u3044\uff1a\u9769\uff1a\u304b\u304f\uff1a,\u516b\uff1a\u306f\u3061\uff1a\u4ee3\uff1a\u3060\u3044\uff1a\u5c06\uff1a\u3057\u3083\u3046\uff1a\u8ecd\uff1a\u3050\u3093\uff1a \u5fb3\uff1a\u3068\u304f\uff1a\u5ddd\uff1a\u304c\u306f\uff1a\u5409\uff1a\u3088\u3057\uff1a\u5b97\uff1a\u3080\u306d\uff1a,\u8cea\uff1a\u3057\u3063\uff1a\u7d20\uff1a\u305d\uff1a\u5039\uff1a\u3051\u3093\uff1a\u7d04\uff1a\u3084\u304f\uff1a \u7c73\uff1a\u3053\u3081\uff1a\u306e\u5897\uff1a\u305e\u3046\uff1a\u53ce\uff1a\u3057\u3046\uff1a \u516c\uff1a\u304f\uff1a\u4e8b\uff1a\u3058\uff1a\u65b9\uff1a\u304b\u305f\uff1a\u5fa1\uff1a\u304a\uff1a\u5b9a\uff1a\u3055\u3060\u3081\uff1a\u66f8\uff1a\u304c\u304d\uff1a \u5be6\uff1a\u3058\u3064\uff1a\u5b78\uff1a\u304c\u304f\uff1a\u306e\u5968\uff1a\u3057\u3084\u3046\uff1a\u52b1\uff1a\u308c\u3044\uff1a \u76ee\uff1a\u3081\uff1a\u5b89\uff1a\u3084\u3059\uff1a\u7bb1\uff1a\u3070\u3053\uff1a\u306a\u3069\n1767,\u7530\uff1a\u305f\uff1a\u6cbc\uff1a\u306c\u307e\uff1a\u610f\uff1a\u304a\u304d\uff1a\u6b21\uff1a\u3064\u3050\uff1a\u306e\u653f\uff1a\u305b\u3044\uff1a\u6cbb\uff1a\u3058\uff1a,\u5341\uff1a\u3058\u3085\u3046\uff1a\u4ee3\uff1a\u3060\u3044\uff1a\u5c06\uff1a\u3057\u3083\u3046\uff1a\u8ecd\uff1a\u3050\u3093\uff1a \u5fb3\uff1a\u3068\u304f\uff1a\u5ddd\uff1a\u304c\u306f\uff1a\u5bb6\uff1a\u3044\u3078\uff1a\u6cbb\uff1a\u306f\u308b\uff1a\u306e\u6642\uff1a\u3058\uff1a\u4ee3\uff1a\u3060\u3044\uff1a,\u682a\uff1a\u304b\u3076\uff1a\u4ef2\uff1a\u306a\u304b\uff1a\u9593\uff1a\u307e\uff1a\u3092\u516c\uff1a\u3053\u3046\uff1a\u8a8d\uff1a\u306b\u3093\uff1a \u7a0e\uff1a\u305c\u3044\uff1a\u5236\uff1a\u305b\u3044\uff1a\u6539\uff1a\u304b\u3044\uff1a\u9769\uff1a\u304b\u304f\uff1a \u7d4c\uff1a\u3051\u3044\uff1a\u6e08\uff1a\u3056\u3044\uff1a\u3092\u6d3b\uff1a\u304b\u3063\uff1a\u6027\uff1a\u305b\u3044\uff1a\u5316\uff1a\u304b\uff1a\u3055\u305b\u308b\n1787,\u5bdb\uff1a\u304b\u3093\uff1a\u653f\uff1a\u305b\u3044\uff1a\u306e\u6539\uff1a\u304b\u3044\uff1a\u9769\uff1a\u304b\u304f\uff1a,\u5341\uff1a\u3058\u3085\u3046\uff1a\u4e00\uff1a\u3044\u3061\uff1a\u4ee3\uff1a\u3060\u3044\uff1a\u5c06\uff1a\u3057\u3083\u3046\uff1a\u8ecd\uff1a\u3050\u3093\uff1a \u5fb3\uff1a\u3068\u304f\uff1a\u5ddd\uff1a\u304c\u306f\uff1a\u5bb6\uff1a\u3044\u3078\uff1a\u6589\uff1a\u306a\u308a\uff1a\u304c \u767d\uff1a\u3057\u3089\uff1a\u6cb3\uff1a\u304b\u306f\uff1a\u85e9\uff1a\u306f\u3093\uff1a\u4e3b\uff1a\u3057\u3085\uff1a \u677e\uff1a\u307e\u3064\uff1a\u5e73\uff1a\u3060\u3044\u3089\uff1a\u5b9a\uff1a\u3055\u3060\uff1a\u4fe1\uff1a\u306e\u3076\uff1a\u3092\u767b\uff1a\u3068\u3046\uff1a\u7528\uff1a\u3088\u3046\uff1a,\u56f2\u7c73(\u304b\u3053\u3044\u307e\u3044) \u501f\uff1a\u3057\u3083\u3063\uff1a\u91d1\uff1a\u304d\u3093\uff1a\u306e\u5e33\uff1a\u3061\u3083\u3046\uff1a\u6d88\uff1a\u3051\uff1a\u3057 \u8fb2\uff1a\u306e\u3046\uff1a\u6c11\uff1a\u307f\u3093\uff1a\u306e\u5e30\uff1a\u304d\uff1a\u90f7\uff1a\u304d\u3083\u3046\uff1a\u3092\u4fc3\uff1a\u3046\u306a\u304c\uff1a\u3059 \u6e6f\uff1a\u3086\uff1a\u5cf6\uff1a\u3057\u307e\uff1a\u306b\u660c\uff1a\u3057\u3083\u3046\uff1a\u5e73\uff1a\u3078\u3044\uff1a\u5742\uff1a\u3056\u304b\uff1a\u5b78\uff1a\u304c\u304f\uff1a\u554f\uff1a\u3082\u3093\uff1a\u6240\uff1a\u3058\u3087\uff1a\u3092\u3064\u304f\u308a\u5b78\uff1a\u304c\u304f\uff1a\u554f\uff1a\u3082\u3093\uff1a\u30fb\u6b66\uff1a\u3076\uff1a\u8853\uff1a\u3058\u3085\u3064\uff1a\u3092\u5968\uff1a\u3057\u3083\u3046\uff1a\u52b1\uff1a\u308c\u3044\uff1a \u53b3\uff1a\u304d\u3073\uff1a\u3057\u3044\u7dca\uff1a\u304d\u3093\uff1a\u7e2e\uff1a\u3057\u3085\u304f\uff1a\u8ca1\uff1a\u3056\u3044\uff1a\u653f\uff1a\u305b\u3044\uff1a\u3067\u7d4c\uff1a\u3051\u3044\uff1a\u6e08\uff1a\u3056\u3044\uff1a\u306f\u505c\uff1a\u3066\u3044\uff1a\u6ede\uff1a\u305f\u3044\uff1a\n1837,\u5927\uff1a\u304a\u307b\uff1a\u5869\uff1a\u3057\u307b\uff1a\u5e73\uff1a\u3078\u3044\uff1a\u516b\uff1a\u306f\u3061\uff1a\u90ce\uff1a\u3089\u3046\uff1a\u306e\u4e82\uff1a\u3089\u3093\uff1a,\u5929\uff1a\u3066\u3093\uff1a\u4fdd\uff1a\u307d\u3046\uff1a\u306e\u98e2\uff1a\u304d\uff1a\u9949\uff1a\u304d\u3093\uff1a\u304c\u6839\uff1a\u3053\u3093\uff1a\u672c\uff1a\u307d\u3093\uff1a\u539f\uff1a\u3052\u3093\uff1a\u56e0\uff1a\u3044\u3093\uff1a\u306e\u3072\u3068\u3064,\u5e55\uff1a\u3070\u304f\uff1a\u5e9c\uff1a\u3075\uff1a\u306e\u5143\uff1a\u3082\u3068\uff1a\u5f79\uff1a\u3084\u304f\uff1a\u4eba\uff1a\u306b\u3093\uff1a\u306e\u53cd\uff1a\u306f\u3093\uff1a\u4e82\uff1a\u3089\u3093\uff1a\u306f\u5e55\u5e9c\u306b\u885d\uff1a\u3057\u3087\u3046\uff1a\u6483\uff1a\u3052\u304d\uff1a\u3092\u8207\uff1a\u3042\u305f\uff1a\u3078\u308b\n1854,\u65e5\uff1a\u306b\u3061\uff1a\u7c73\uff1a\u3079\u3044\uff1a\u548c\uff1a\u308f\uff1a\u89aa\uff1a\u3057\u3093\uff1a\u6761\uff1a\u3067\u3046\uff1a\u7d04\uff1a\u3084\u304f\uff1a,\u30de\u30b7\u30e5\u30fc\u30fb\u30da\u30ea\u30fc\u304c\u6d66\uff1a\u3046\u3089\uff1a\u8cc0\uff1a\u304c\uff1a\u306b\u8ecd\uff1a\u3050\u3093\uff1a\u8266\uff1a\u304b\u3093\uff1a\u56db\uff1a\u3088\u3093\uff1a\u96bb\uff1a\u305b\u304d\uff1a\u3067\u4f86\uff1a\u3089\u3044\uff1a\u822a\uff1a\u304b\u3046\uff1a,\u4e0b\uff1a\u3057\u3082\uff1a\u7530\uff1a\u3060\uff1a(\u9759\uff1a\u3057\u3065\uff1a\u5ca1\uff1a\u304a\u304b\uff1a\u770c\uff1a\u3051\u3093\uff1a)\u30fb\u7bb1\uff1a\u306f\u3053\uff1a\u9928\uff1a\u3060\u3066\uff1a(\u5317\uff1a\u307b\u3063\uff1a\u6d77\uff1a\u304b\u3044\uff1a\u9053\uff1a\u3060\u3046\uff1a)\u306e\u4e8c\uff1a\u306b\uff1a\u6e2f\uff1a\u304b\u3046\uff1a\u3092\u958b\uff1a\u3072\u3089\uff1a\u304f\n1860,\u685c\uff1a\u3055\u304f\u3089\uff1a\u7530\uff1a\u3060\uff1a\u9580\uff1a\u3082\u3093\uff1a\u5916\uff1a\u3050\u308f\u3044\uff1a\u306e\u8b8a\uff1a\u3078\u3093\uff1a,121\u4ee3\uff1a\u3060\u3044\uff1a\u5b5d\uff1a\u304b\u3046\uff1a\u660e\uff1a\u3081\u3044\uff1a\u5929\u7687\u306e\u52c5\uff1a\u3061\u3087\u304f\uff1a\u8a31\uff1a\u304d\u3087\uff1a\u3092\u5f97\u305a \u65e5\uff1a\u306b\u3061\uff1a\u7c73\uff1a\u3079\u3044\uff1a\u4fee\uff1a\u3057\u3046\uff1a\u4ea4\uff1a\u304b\u3046\uff1a\u901a\uff1a\u3064\u3046\uff1a\u5546\uff1a\u3057\u3083\u3046\uff1a\u6761\uff1a\u3067\u3046\uff1a\u7d04\uff1a\u3084\u304f\uff1a\u3092\u7d50\uff1a\u3080\u3059\uff1a\u3093\u3060 \u3068\u3044\u3075\u6279\uff1a\u3072\uff1a\u5224\uff1a\u306f\u3093\uff1a\u306b \u4e95\uff1a\u3090\uff1a\u4f0a\uff1a\u3044\uff1a\u76f4\uff1a\u306a\u307b\uff1a\u5f3c\uff1a\u3059\u3051\uff1a\u304c \u5b89\uff1a\u3042\u3093\uff1a\u653f\uff1a\u305b\u3044\uff1a\u306e\u5927\uff1a\u305f\u3044\uff1a\u7344\uff1a\u3054\u304f\uff1a\u3067\u591a\uff1a\u304a\u307b\uff1a\u304f\u306e\u5fd7\uff1a\u3057\uff1a\u58eb\uff1a\u3057\uff1a\u3092\u51e6\uff1a\u3057\u3087\uff1a\u5211\uff1a\u3051\u3044\uff1a\u3057\u305f\u3053\u3068\u304c\u539f\uff1a\u3052\u3093\uff1a\u56e0\uff1a\u3044\u3093\uff1a\u3068\u3055\u308c\u308b,\u4e95\uff1a\u3090\uff1a\u4f0a\uff1a\u3044\uff1a\u76f4\uff1a\u306a\u307b\uff1a\u5f3c\uff1a\u3059\u3051\uff1a\u304c\u6c34\uff1a\u307f\uff1a\u6238\uff1a\u3068\uff1a\u85e9\uff1a\u306f\u3093\uff1a\u306e\u6d6a\uff1a\u3089\u3046\uff1a\u58eb\uff1a\u3057\uff1a\u3089\u306b\u6697\uff1a\u3042\u3093\uff1a\u6bba\uff1a\u3055\u3064\uff1a\u3055\u308c\u308b\n1868,\u660e\uff1a\u3081\u3044\uff1a\u6cbb\uff1a\u3062\uff1a\u7dad\uff1a\u3090\uff1a\u65b0\uff1a\u3057\u3093\uff1a,\u524d\uff1a\u305c\u3093\uff1a\u5e74\uff1a\u306d\u3093\uff1a\u306e\u5927\uff1a\u305f\u3044\uff1a\u653f\uff1a\u305b\u3044\uff1a\u5949\uff1a\u307b\u3046\uff1a\u9084\uff1a\u304f\u308f\u3093\uff1a\u3092\u53d7\uff1a\u3046\uff1a\u3051 \u671d\uff1a\u3066\u3046\uff1a\u5ef7\uff1a\u3066\u3044\uff1a\u304c<\u738b\uff1a\u308f\u3046\uff1a\u653f\uff1a\u305b\u3044\uff1a\u5fa9\uff1a\u3075\u3063\uff1a\u53e4\uff1a\u3053\uff1a\u306e\u5927\uff1a\u3060\u3044\uff1a\u53f7\uff1a\u304c\u3046\uff1a\u4ee4\uff1a\u308c\u3044\uff1a>\u3092\u51fa\uff1a\u3060\uff1a\u3059,\u660e\uff1a\u3081\u3044\uff1a\u6cbb\uff1a\u3062\uff1a\u5929\u7687\u304c \u4e94\uff1a\u3054\uff1a\u7b87\uff1a\u304b\uff1a\u6761\uff1a\u3067\u3046\uff1a\u306e\u5fa1\uff1a\u3054\uff1a\u8a93\uff1a\u305b\u3044\uff1a\u6587\uff1a\u3082\u3093\uff1a\u3092\u767c\uff1a\u306f\u3063\uff1a\u5e03\uff1a\u3077\uff1a\u3055\u308c\u308b\n1875,\u6c5f\uff1a\u304b\u3046\uff1a\u83ef\uff1a\u304f\u308f\uff1a\u5cf6\uff1a\u305f\u3046\uff1a\u4e8b\uff1a\u3058\uff1a\u4ef6\uff1a\u3051\u3093\uff1a,\u3053\u306e\u4e8b\uff1a\u3058\uff1a\u4ef6\uff1a\u3051\u3093\uff1a\u306e\u7d50\uff1a\u3051\u3064\uff1a\u679c\uff1a\u304b\uff1a \u65e5\uff1a\u306b\u3063\uff1a\u9bae\uff1a\u305b\u3093\uff1a\u4fee\uff1a\u3057\u3046\uff1a\u4ea4\uff1a\u304b\u3046\uff1a\u6761\uff1a\u3067\u3046\uff1a\u898f\uff1a\u304d\uff1a(\u4e0d\uff1a\u3075\uff1a\u5e73\uff1a\u3073\u3084\u3046\uff1a\u7b49\uff1a\u3069\u3046\uff1a\u6761\uff1a\u3067\u3046\uff1a\u7d04\uff1a\u3084\u304f\uff1a\u3068\u3055\u308c\u308b)\u3092\u7de0\uff1a\u3066\u3044\uff1a\u7d50\uff1a\u3051\u3064\uff1a,\u8ecd\uff1a\u3050\u3093\uff1a\u8266\uff1a\u304b\u3093\uff1a\u96f2\uff1a\u3046\u3093\uff1a\u63da\uff1a\u3084\u3046\uff1a\u53f7\uff1a\u3054\u3046\uff1a\u304c\u98f2\uff1a\u3044\u3093\uff1a\u6599\uff1a\u308c\u3046\uff1a\u6c34\uff1a\u3059\u3044\uff1a\u78ba\uff1a\u304b\u304f\uff1a\u4fdd\uff1a\u307b\uff1a\u306e\u305f\u3081\u6c5f\uff1a\u304b\u3046\uff1a\u83ef\uff1a\u304f\u308f\uff1a\u5cf6\uff1a\u305f\u3046\uff1a\u306b\u63a5\uff1a\u305b\u3063\uff1a\u8fd1\uff1a\u304d\u3093\uff1a\u3057\u305f\u969b\uff1a\u3055\u3044\uff1a \u7a81\uff1a\u3068\u3064\uff1a\u5982\uff1a\u3058\u3087\uff1a\u540c\uff1a\u3069\u3046\uff1a\u5cf6\uff1a\u3068\u3046\uff1a\u306e\u7832\uff1a\u306f\u3046\uff1a\u53f0\uff1a\u3060\u3044\uff1a\u3088\u308a\u5f37\uff1a\u304d\u3083\u3046\uff1a\u70c8\uff1a\u308c\u3064\uff1a\u306a\u7832\uff1a\u306f\u3046\uff1a\u6483\uff1a\u3052\u304d\uff1a\u3092\u53d7\uff1a\u3046\uff1a\u3051\u308b >>\u96f2\uff1a\u3046\u3093\uff1a\u63da\uff1a\u3084\u3046\uff1a\u306f\u53cd\uff1a\u306f\u3093\uff1a\u6483\uff1a\u3052\u304d\uff1a\u3057\u9678\uff1a\u308a\u304f\uff1a\u6230\uff1a\u305b\u3093\uff1a\u968a\uff1a\u305f\u3044\uff1a\u3092\u4e0a\uff1a\u3058\u3083\u3046\uff1a\u9678\uff1a\u308a\u304f\uff1a\u3055\u305b\u7832\uff1a\u306f\u3046\uff1a\u53f0\uff1a\u3060\u3044\uff1a\u3092\u5360\uff1a\u305b\u3093\uff1a\u62e0\uff1a\u304d\u3087\uff1a \u6b66\uff1a\u3076\uff1a\u5668\uff1a\u304d\uff1a\u3092\u6355\uff1a\u307b\uff1a\u7372\uff1a\u304b\u304f\uff1a\u3057\u3066\u9577\uff1a\u306a\u304c\uff1a\u5d0e\uff1a\u3055\u304d\uff1a\u3078\u5e30\uff1a\u304d\uff1a\u7740\uff1a\u3061\u3083\u304f\uff1a\n1877,\u897f\uff1a\u305b\u3044\uff1a\u5357\uff1a\u306a\u3093\uff1a\u6230\uff1a\u305b\u3093\uff1a\u722d\uff1a\u3055\u3046\uff1a,\u620a\uff1a\u307c\uff1a\u8fb0\uff1a\u3057\u3093\uff1a\u6230\uff1a\u305b\u3093\uff1a\u722d\uff1a\u3055\u3046\uff1a\u3092\u6230\uff1a\u305f\u305f\u304b\uff1a\u3063\u305f\u58eb\uff1a\u3057\uff1a\u65cf\uff1a\u305e\u304f\uff1a\u305f\u3061\u304c \u660e\uff1a\u3081\u3044\uff1a\u6cbb\uff1a\u3062\uff1a\u7dad\uff1a\u3090\uff1a\u65b0\uff1a\u3057\u3093\uff1a\u306b\u4e0d\uff1a\u3075\uff1a\u6e80\uff1a\u307e\u3093\uff1a\u3092\u62b1\uff1a\u3044\u3060\uff1a\u304d \u897f\uff1a\u3055\u3044\uff1a\u90f7\uff1a\u304c\u3046\uff1a\u9686\uff1a\u305f\u304b\uff1a\u76db\uff1a\u3082\u308a\uff1a\u3092\u62c5\uff1a\u304b\u3064\uff1a\u3044\u3067\u8702\uff1a\u307b\u3046\uff1a\u8d77\uff1a\u304d\uff1a,\u897f\uff1a\u3055\u3044\uff1a\u90f7\uff1a\u304c\u3046\uff1a\u9686\uff1a\u305f\u304b\uff1a\u76db\uff1a\u3082\u308a\uff1a\u3092\u7dcf\uff1a\u305d\u3046\uff1a\u5927\uff1a\u3060\u3044\uff1a\u5c06\uff1a\u3057\u3083\u3046\uff1a\u3068\u3059\u308b\u53cd\uff1a\u306f\u3093\uff1a\u4e82\uff1a\u3089\u3093\uff1a\u8ecd\uff1a\u3050\u3093\uff1a\u306f\u653f\uff1a\u305b\u3044\uff1a\u5e9c\uff1a\u3075\uff1a\u8ecd\uff1a\u3050\u3093\uff1a\u306b\u93ae\uff1a\u3061\u3093\uff1a\u58d3\uff1a\u3042\u3064\uff1a\u3055\u308c \u897f\u90f7\u306f\u81ea\uff1a\u3058\uff1a\u6c7a\uff1a\u3051\u3064\uff1a \u4ee5\uff1a\u3044\uff1a\u5f8c\uff1a\u3054\uff1a\u58eb\uff1a\u3057\uff1a\u65cf\uff1a\u305e\u304f\uff1a\u306e\u53cd\u4e82\u306f\u9014\uff1a\u3068\uff1a\u7d76\uff1a\u3060\uff1a\u3078 \u620a\uff1a\u307c\uff1a\u8fb0\uff1a\u3057\u3093\uff1a\u6230\uff1a\u305b\u3093\uff1a\u722d\uff1a\u3055\u3046\uff1a\u304b\u3089\u5341\u5e74\u7e8c\uff1a\u3064\u3065\uff1a\u3044\u3066\u3090\u305f\u52d5\uff1a\u3069\u3046\uff1a\u4e82\uff1a\u3089\u3093\uff1a\u306f\u53ce\uff1a\u3057\u3046\uff1a\u675f\uff1a\u305d\u304f\uff1a\u3057\u305f\n1894,\u65e5\uff1a\u306b\u3063\uff1a\u6e05\uff1a\u3057\u3093\uff1a\u6230\uff1a\u305b\u3093\uff1a\u722d\uff1a\u3055\u3046\uff1a,\u671d\uff1a\u3066\u3046\uff1a\u9bae\uff1a\u305b\u3093\uff1a\u3067\u8fb2\uff1a\u306e\u3046\uff1a\u6c11\uff1a\u307f\u3093\uff1a\u4e00\uff1a\u3044\u3063\uff1a\u63c6\uff1a\u304d\uff1a\u304c\u653f\uff1a\u305b\u3044\uff1a\u6cbb\uff1a\u3058\uff1a\u66b4\uff1a\u307c\u3046\uff1a\u52d5\uff1a\u3069\u3046\uff1a\u5316\uff1a\u304b\uff1a(\u6771\uff1a\u3068\u3046\uff1a\u5b78\uff1a\u304c\u304f\uff1a\u9ee8\uff1a\u305f\u3046\uff1a\u306e\u4e82\uff1a\u3089\u3093\uff1a) \u304c\u8d77\uff1a\u304d\uff1a\u7206\uff1a\u3070\u304f\uff1a\u5264\uff1a\u3056\u3044\uff1a\u3068\u306a\u308b,\u8c4a\uff1a\u3068\uff1a\u5cf6\uff1a\u3057\u307e\uff1a\u6c96\uff1a\u304a\u304d\uff1a\u6d77\uff1a\u304b\u3044\uff1a\u6230\uff1a\u305b\u3093\uff1a\u306f \u6211\uff1a\u308f\uff1a\u304c\u9023\uff1a\u308c\u3093\uff1a\u5408\uff1a\u304c\u3075\uff1a\u8266\uff1a\u304b\u3093\uff1a\u968a\uff1a\u305f\u3044\uff1a\u7b2c\uff1a\u3060\u3044\uff1a\u4e00\uff1a\u3044\u3061\uff1a\u904a\uff1a\u3044\u3046\uff1a\u6483\uff1a\u3052\u304d\uff1a\u968a\uff1a\u305f\u3044\uff1a\u5409\uff1a\u3088\u3057\uff1a\u91ce\uff1a\u306e\uff1a\u304c\u793c\uff1a\u308c\u3044\uff1a\u7832\uff1a\u306f\u3046\uff1a\u4ea4\uff1a\u304b\u3046\uff1a\u63db\uff1a\u304f\u308f\u3093\uff1a\u306e\u7528\uff1a\u3088\u3046\uff1a\u610f\uff1a\u3044\uff1a\u3092\u3057\u3066\u8fd1\uff1a\u304d\u3093\uff1a\u63a5\uff1a\u305b\u3064\uff1a\u3057\u305f\u306e\u306b\u5c0d\uff1a\u305f\u3044\uff1a\u3057 \u6e05\uff1a\u3057\u3093\uff1a\u570b\uff1a\u3053\u304f\uff1a\u8ecd\uff1a\u3050\u3093\uff1a\u8266\uff1a\u304b\u3093\uff1a\u6e08\uff1a\u305b\u3044\uff1a\u9060\uff1a\u3048\u3093\uff1a\u306e\u6230\uff1a\u305b\u3093\uff1a\u95d8\uff1a\u305f\u3046\uff1a\u6e96\uff1a\u3058\u3085\u3093\uff1a\u5099\uff1a\u3073\uff1a\u304a\u3088\u3073\u767c\uff1a\u306f\u3063\uff1a\u7832\uff1a\u3071\u3046\uff1a\u3088\u308a\u306f\u3058\u307e\u308b\n1895,\u4e0b\uff1a\u3057\u3082\u306e\uff1a\u95a2\uff1a\u305b\u304d\uff1a\u6761\uff1a\u3067\u3046\uff1a\u7d04\uff1a\u3084\u304f\uff1a,\u65e5\uff1a\u306b\u3063\uff1a\u6e05\uff1a\u3057\u3093\uff1a\u6230\uff1a\u305b\u3093\uff1a\u722d\uff1a\u3055\u3046\uff1a\u306b\u6211\uff1a\u308f\u304c\uff1a\u570b\uff1a\u304f\u306b\uff1a\u304c\u52dd\uff1a\u3057\u3087\u3046\uff1a\u5229\uff1a\u308a\uff1a\u3057\u3066\u7d50\uff1a\u3080\u3059\uff1a\u3070\u308c\u305f\u6761\uff1a\u3067\u3046\uff1a\u7d04\uff1a\u3084\u304f\uff1a >> \u4e09\uff1a\u3055\u3093\uff1a\u570b\uff1a\u3054\u304f\uff1a\u5e72\uff1a\u304b\u3093\uff1a\u6e09\uff1a\u305b\u3075\uff1a\u3092\u53d7\uff1a\u3046\uff1a\u3051\u308b,\u4e00 \u6e05\uff1a\u3057\u3093\uff1a\u570b\uff1a\u3053\u304f\uff1a\u306f\u671d\uff1a\u3066\u3046\uff1a\u9bae\uff1a\u305b\u3093\uff1a\u570b\uff1a\u3053\u304f\uff1a\u304c\u5b8c\uff1a\u304b\u3093\uff1a\u5168\uff1a\u305c\u3093\uff1a\u7121\uff1a\u3080\uff1a\u6b20\uff1a\u3051\u3064\uff1a\u306e\u72ec\uff1a\u3069\u304f\uff1a\u7acb\uff1a\u308a\u3064\uff1a\u81ea\uff1a\u3058\uff1a\u4e3b\uff1a\u3057\u3085\uff1a\u306e\u570b\uff1a\u304f\u306b\uff1a\u3067\u3042\u308b\u3053\u3068\u3092\u627f\uff1a\u3057\u3087\u3046\uff1a\u8a8d\uff1a\u306b\u3093\uff1a\u3059\u308b \u4e8c \u6e05\uff1a\u3057\u3093\uff1a\u570b\uff1a\u3053\u304f\uff1a\u306f\u907c\uff1a\u308a\u3087\u3046\uff1a\u6771\uff1a\u3068\u3046\uff1a\u534a\uff1a\u306f\u3093\uff1a\u5cf6\uff1a\u305f\u3046\uff1a \u53f0\uff1a\u305f\u3044\uff1a\u6e7e\uff1a\u308f\u3093\uff1a\u5168\uff1a\u305c\u3093\uff1a\u5cf6\uff1a\u305f\u3046\uff1a\u53ca\uff1a\u304a\u3088\uff1a\u3073\u6f8e\uff1a\u307b\u3046\uff1a\u6e56\uff1a\u3053\uff1a\u5217\uff1a\u308c\u3063\uff1a\u5cf6\uff1a\u305f\u3046\uff1a\u3092\u6c38\uff1a\u3048\u3044\uff1a\u9060\uff1a\u3048\u3093\uff1a\u306b\u65e5\uff1a\u306b\uff1a\u672c\uff1a\u307b\u3093\uff1a\u306b\u5272\uff1a\u304b\u3064\uff1a\u8b72\uff1a\u3058\u3083\u3046\uff1a\u3059\u308b \u4e09 \u6e05\uff1a\u3057\u3093\uff1a\u570b\uff1a\u3053\u304f\uff1a\u306f\u8ecd\uff1a\u3050\u3093\uff1a\u8cbb\uff1a\u3074\uff1a\u8ce0\uff1a\u3070\u3044\uff1a\u511f\uff1a\u3057\u3083\u3046\uff1a\u91d1\uff1a\u304d\u3093\uff1a\u4e8c\uff1a\u306b\uff1a\u5104\uff1a\u304a\u304f\uff1a\u4e21\uff1a\u30c6\u30fc\u30eb\uff1a\u3092\u652f\uff1a\u3057\uff1a\u6255\uff1a\u306f\u3089\uff1a\u3075 \u56db \u65e5\uff1a\u306b\u3063\uff1a\u6e05\uff1a\u3057\u3093\uff1a\u9593\uff1a\u304b\u3093\uff1a\u306e\u4e00\uff1a\u3044\u3063\uff1a\u5207\uff1a\u3055\u3044\uff1a\u306e\u6761\uff1a\u3067\u3046\uff1a\u7d04\uff1a\u3084\u304f\uff1a\u306f\u4ea4\uff1a\u304b\u3046\uff1a\u6230\uff1a\u305b\u3093\uff1a\u306e\u305f\u3081\u6d88\uff1a\u3057\u3087\u3046\uff1a\u6ec5\uff1a\u3081\u3064\uff1a\u3057\u305f\u306e\u3067\u65b0\uff1a\u3042\u3089\uff1a\u305f\u306b\u901a\uff1a\u3064\u3046\uff1a\u5546\uff1a\u3057\u3083\u3046\uff1a\u822a\uff1a\u304b\u3046\uff1a\u6d77\uff1a\u304b\u3044\uff1a\u6761\uff1a\u3067\u3046\uff1a\u7d04\uff1a\u3084\u304f\uff1a\u3092\u7d50\uff1a\u3080\u3059\uff1a\u3076 \u4e94 \u672c\uff1a\u307b\u3093\uff1a\u6761\uff1a\u3067\u3046\uff1a\u7d04\uff1a\u3084\u304f\uff1a\u6279\uff1a\u3072\uff1a\u51c6\uff1a\u3058\u3085\u3093\uff1a\u5f8c\uff1a\u3054\uff1a \u76f4\uff1a\u305f\u3060\uff1a\u3061\u306b\u4fd8\uff1a\u3075\uff1a\u865c\uff1a\u308a\u3087\uff1a\u3092\u8fd4\uff1a\u3078\u3093\uff1a\u9084\uff1a\u304b\u3093\uff1a\u3059\u308b \u6e05\uff1a\u3057\u3093\uff1a\u570b\uff1a\u3053\u304f\uff1a\u306f\u9001\uff1a\u305d\u3046\uff1a\u9084\uff1a\u304f\u308f\u3093\uff1a\u3055\u308c\u305f\u4fd8\u865c\u3092\u8650\uff1a\u304e\u3083\u304f\uff1a\u5f85\uff1a\u305f\u3044\uff1a\u3042\u308b\u3044\u306f\u51e6\uff1a\u3057\u3087\uff1a\u5211\uff1a\u3051\u3044\uff1a\u305b\u306c\u3053\u3068\n1899,\u7fa9\uff1a\u304e\uff1a\u548c\uff1a\u308f\uff1a\u5718\uff1a\u3060\u3093\uff1a\u4e8b\uff1a\u3058\uff1a\u8b8a\uff1a\u3078\u3093\uff1a,\u65e5\uff1a\u306b\u3061\uff1a\u9732\uff1a\u308d\uff1a\u6230\uff1a\u305b\u3093\uff1a\u722d\uff1a\u3055\u3046\uff1a\u306e\u539f\uff1a\u3052\u3093\uff1a\u56e0\uff1a\u3044\u3093\uff1a\u306e\u3072\u3068\u3064\u3068\u8a00\uff1a\u3044\uff1a\u3078\u308b,\u5b97\uff1a\u3057\u3085\u3046\uff1a\u6559\uff1a\u3051\u3046\uff1a\u7684\uff1a\u3066\u304d\uff1a\u79d8\uff1a\u3072\uff1a\u5bc6\uff1a\u307f\u3064\uff1a\u7d50\uff1a\u3051\u3063\uff1a\u793e\uff1a\u3057\u3083\uff1a\u3067\u3042\u308b\u7fa9\uff1a\u304e\uff1a\u548c\uff1a\u308f\uff1a\u5718\uff1a\u3060\u3093\uff1a\u304c<\u6276\uff1a\u3075\uff1a\u6e05\uff1a\u3057\u3093\uff1a\u6ec5\uff1a\u3081\u3064\uff1a\u6d0b\uff1a\u3084\u3046\uff1a>\u3092\u304b\u304b\u3052 \u5c71\uff1a\u3055\u3093\uff1a\u6771\uff1a\u3068\u3046\uff1a\u7701\uff1a\u3057\u3083\u3046\uff1a\u3067 \u30ad\u30ea\u30b9\u30c8\u6559\uff1a\u3051\u3046\uff1a\u5f92\uff1a\u3068\uff1a\u306e\u6bba\uff1a\u3055\u3064\uff1a\u5bb3\uff1a\u304c\u3044\uff1a \u9244\uff1a\u3066\u3064\uff1a\u9053\uff1a\u3060\u3046\uff1a\u7834\uff1a\u306f\uff1a\u58ca\uff1a\u304b\u3044\uff1a\u306a\u3069\u3092\u884c\uff1a\u304a\u3053\uff1a\u306a\u3044 \u6e05\uff1a\u3057\u3093\uff1a\u8ecd\uff1a\u3050\u3093\uff1a\u3068\u7d50\uff1a\u3051\u3063\uff1a\u8a17\uff1a\u305f\u304f\uff1a\u3057\u3066 \u5317\uff1a\u307a\uff1a\u4eac\uff1a\u304d\u3093\uff1a\u306e\u516c\uff1a\u3053\u3046\uff1a\u4f7f\uff1a\u3057\uff1a\u9928\uff1a\u304f\u308f\u3093\uff1a\u5340\uff1a\u304f\uff1a\u57df\uff1a\u3044\u304d\uff1a\u3092\u5305\uff1a\u306f\u3046\uff1a\u56f2\uff1a\u3090\uff1a \u6e05\uff1a\u3057\u3093\uff1a\u5e1d\uff1a\u3066\u3044\uff1a\u306f\u5217\uff1a\u308c\u3063\uff1a\u570b\uff1a\u3053\u304f\uff1a\u306b\u5c0d\uff1a\u305f\u3044\uff1a\u3057 \u5ba3\uff1a\u305b\u3093\uff1a\u6230\uff1a\u305b\u3093\uff1a\u306e\u4e0a\uff1a\u3058\u3083\u3046\uff1a\u8aed\uff1a\u3086\uff1a\u3092\u767c\uff1a\u306f\u3064\uff1a\u3059\u308b\u3082 \u65e5\uff1a\u306b\uff1a\u672c\uff1a\u307b\u3093\uff1a\u570b\uff1a\u3053\u304f\uff1a\u3092\u4e3b\uff1a\u3057\u3085\uff1a\u529b\uff1a\u308a\u3087\u304f\uff1a\u3068\u3059\u308b\u516b\uff1a\u306f\u3061\uff1a\u30f6\uff1a\u304b\uff1a\u570b\uff1a\u3053\u304f\uff1a\u9023\uff1a\u308c\u3093\uff1a\u5408\uff1a\u304c\u3046\uff1a\u8ecd\uff1a\u3050\u3093\uff1a\u306f\u5317\uff1a\u307a\uff1a\u4eac\uff1a\u304d\u3093\uff1a\u516c\uff1a\u3053\u3046\uff1a\u4f7f\uff1a\u3057\uff1a\u9928\uff1a\u304f\u308f\u3093\uff1a\u5340\uff1a\u304f\uff1a\u57df\uff1a\u3044\u304d\uff1a\u3092\u7fa9\uff1a\u304e\uff1a\u548c\uff1a\u308f\uff1a\u5718\uff1a\u3060\u3093\uff1a\u30fb\u6e05\uff1a\u3057\u3093\uff1a\u5175\uff1a\u307a\u3044\uff1a\u306e\u5305\uff1a\u306f\u3046\uff1a\u56f2\uff1a\u3090\uff1a\u304b\u3089\u6551\uff1a\u304d\u3046\uff1a\u51fa\uff1a\u3057\u3085\u3064\uff1a\n1902,\u65e5\uff1a\u306b\u3061\uff1a\u82f1\uff1a\u3048\u3044\uff1a\u540c\uff1a\u3069\u3046\uff1a\u76df\uff1a\u3081\u3044\uff1a,\u65e5\uff1a\u306b\u3061\uff1a\u9732\uff1a\u308d\uff1a\u6230\uff1a\u305b\u3093\uff1a\u722d\uff1a\u3055\u3046\uff1a\u306e\u52dd\uff1a\u3057\u3083\u3046\uff1a\u5229\uff1a\u308a\uff1a\u306b\u852d\uff1a\u304b\u3052\uff1a\u306e\u529b\uff1a\u3061\u304b\u3089\uff1a\u3068\u306a\u308b,\u4e00 \u65e5\uff1a\u306b\u3061\uff1a\u82f1\uff1a\u3048\u3044\uff1a\u4e21\uff1a\u308a\u3083\u3046\uff1a\u570b\uff1a\u3053\u304f\uff1a\u306f\u6e05\uff1a\u3057\u3093\uff1a\u97d3\uff1a\u304b\u3093\uff1a\u4e21\uff1a\u308a\u3083\u3046\uff1a\u570b\uff1a\u3053\u304f\uff1a\u306e\u72ec\uff1a\u3069\u304f\uff1a\u7acb\uff1a\u308a\u3064\uff1a\u3092\u627f\uff1a\u3057\u3087\u3046\uff1a\u8a8d\uff1a\u306b\u3093\uff1a\u3059\u308b \u3057\u304b\u3057\u82f1\uff1a\u3048\u3044\uff1a\u570b\uff1a\u3053\u304f\uff1a\u306f\u6e05\uff1a\u3057\u3093\uff1a\u570b\uff1a\u3053\u304f\uff1a\u3067 \u65e5\uff1a\u306b\uff1a\u672c\uff1a\u307b\u3093\uff1a\u306f\u6e05\uff1a\u3057\u3093\uff1a\u97d3\uff1a\u304b\u3093\uff1a\u4e21\uff1a\u308a\u3083\u3046\uff1a\u570b\uff1a\u3053\u304f\uff1a\u3067\u653f\uff1a\u305b\u3044\uff1a\u6cbb\uff1a\u3058\uff1a\u30fb\u7d4c\uff1a\u3051\u3044\uff1a\u6e08\uff1a\u3056\u3044\uff1a\u4e0a\uff1a\u3058\u3083\u3046\uff1a\u683c\uff1a\u304b\u304f\uff1a\u6bb5\uff1a\u3060\u3093\uff1a\u306e\u5229\uff1a\u308a\uff1a\u76ca\uff1a\u3048\u304d\uff1a\u3092\u6709\uff1a\u3044\u3046\uff1a\u3059\u308b\u306e\u3067 \u305d\u308c\u3089\u306e\u5229\uff1a\u308a\uff1a\u76ca\uff1a\u3048\u304d\uff1a\u304c\u7b2c\uff1a\u3060\u3044\uff1a\u4e09\uff1a\u3055\u3093\uff1a\u570b\uff1a\u3054\u304f\uff1a\u306e\u4fb5\uff1a\u3057\u3093\uff1a\u7565\uff1a\u308a\u3083\u304f\uff1a\u3084\u5185\uff1a\u306a\u3044\uff1a\u4e82\uff1a\u3089\u3093\uff1a\u3067\u4fb5\uff1a\u3057\u3093\uff1a\u8feb\uff1a\u3071\u304f\uff1a\u3055\u308c\u305f\u6642\uff1a\u3068\u304d\uff1a\u306f\u5fc5\uff1a\u3072\u3064\uff1a\u8981\uff1a\u3048\u3046\uff1a\u306a\u63aa\uff1a\u305d\uff1a\u7f6e\uff1a\u3061\uff1a\u3092\u3068\u308b \u4e8c \u65e5\uff1a\u306b\u3061\uff1a\u82f1\uff1a\u3048\u3044\uff1a\u306e\u4e00\uff1a\u3044\u3063\uff1a\u65b9\uff1a\u3071\u3046\uff1a\u304c\u3053\u306e\u5229\uff1a\u308a\uff1a\u76ca\uff1a\u3048\u304d\uff1a\u3092\u8b77\uff1a\u307e\u3082\uff1a\u308b\u305f\u3081\u7b2c\uff1a\u3060\u3044\uff1a\u4e09\uff1a\u3055\u3093\uff1a\u570b\uff1a\u3054\u304f\uff1a\u3068\u6230\uff1a\u305f\u305f\u304b\uff1a\u3075\u6642\uff1a\u3068\u304d\uff1a\u306f\u4ed6\uff1a\u305f\uff1a\u306e\u4e00\uff1a\u3044\u3063\uff1a\u65b9\uff1a\u3071\u3046\uff1a\u306f\u53b3\uff1a\u3052\u3093\uff1a\u6b63\uff1a\u305b\u3044\uff1a\u4e2d\uff1a\u3061\u3085\u3046\uff1a\u7acb\uff1a\u308a\u3064\uff1a\u3092\u5b88\uff1a\u307e\u3082\uff1a\u308a \u4ed6\uff1a\u305f\uff1a\u570b\uff1a\u3053\u304f\uff1a\u304c\u6575\uff1a\u3066\u304d\uff1a\u5074\uff1a\u304c\u306f\uff1a\u306b\u53c2\uff1a\u3055\u3093\uff1a\u6230\uff1a\u305b\u3093\uff1a\u3059\u308b\u306e\u3092\u9632\uff1a\u3075\u305b\uff1a\u3050 \u4e09 \u4ed6\uff1a\u305f\uff1a\u570b\uff1a\u3053\u304f\uff1a\u304c\u540c\uff1a\u3069\u3046\uff1a\u76df\uff1a\u3081\u3044\uff1a\u570b\uff1a\u3053\u304f\uff1a\u3068\u306e\u4ea4\uff1a\u304b\u3046\uff1a\u6230\uff1a\u305b\u3093\uff1a\u306b\u52a0\uff1a\u304f\u306f\uff1a\u306f\u308b\u6642\uff1a\u3068\u304d\uff1a\u306f \u4ed6\uff1a\u305f\uff1a\u306e\u540c\uff1a\u3069\u3046\uff1a\u76df\uff1a\u3081\u3044\uff1a\u570b\uff1a\u3053\u304f\uff1a\u306f \u63f4\uff1a\u3048\u3093\uff1a\u52a9\uff1a\u3058\u3087\uff1a\u3092\u8207\uff1a\u3042\u305f\uff1a\u3078\u308b\n1904,\u65e5\uff1a\u306b\u3061\uff1a\u9732\uff1a\u308d\uff1a\u6230\uff1a\u305b\u3093\uff1a\u722d\uff1a\u3055\u3046\uff1a,\u6975\uff1a\u304d\u3087\u304f\uff1a\u6771\uff1a\u3068\u3046\uff1a\u306e\u30ed\u30b7\u30a2\u8ecd\uff1a\u3050\u3093\uff1a\u306b\u52d5\uff1a\u3069\u3046\uff1a\u54e1\uff1a\u3090\u3093\uff1a\u4ee4\uff1a\u308c\u3044\uff1a\u304c \u6e80\uff1a\u307e\u3093\uff1a\u6d32\uff1a\u3057\u3046\uff1a\u306b\u306f\u6212\uff1a\u304b\u3044\uff1a\u53b3\uff1a\u3052\u3093\uff1a\u4ee4\uff1a\u308c\u3044\uff1a\u304c\u4e0b\uff1a\u304f\u3060\uff1a\u3055\u308c \u5bfe\uff1a\u305f\u3044\uff1a\u9732\uff1a\u308d\uff1a\u4ea4\uff1a\u304b\u3046\uff1a\u6e09\uff1a\u305b\u3075\uff1a\u306f\u6c7a\uff1a\u3051\u3064\uff1a\u88c2\uff1a\u308c\u3064\uff1a \u6211\uff1a\u308f\u304c\uff1a\u570b\uff1a\u304f\u306b\uff1a\u306f\u570b\uff1a\u3053\u3063\uff1a\u4ea4\uff1a\u304b\u3046\uff1a\u65ad\uff1a\u3060\u3093\uff1a\u7d76\uff1a\u305c\u3064\uff1a\u3092\u9732\uff1a\u308d\uff1a\u570b\uff1a\u3053\u304f\uff1a\u306b\u901a\uff1a\u3064\u3046\uff1a\u544a\uff1a\u3053\u304f\uff1a,\u6211\uff1a\u308f\u304c\uff1a\u570b\uff1a\u304f\u306b\uff1a\u806f\uff1a\u308c\u3093\uff1a\u5408\uff1a\u304c\u3075\uff1a\u8266\uff1a\u304b\u3093\uff1a\u968a\uff1a\u305f\u3044\uff1a\u306b\u3088\u308b \u65c5\uff1a\u308a\u3087\uff1a\u9806\uff1a\u3058\u3085\u3093\uff1a\u6e2f\uff1a\u304b\u3046\uff1a\u5916\uff1a\u3050\u308f\u3044\uff1a\u306e\u653b\uff1a\u3053\u3046\uff1a\u6483\uff1a\u3052\u304d\uff1a \u4ec1\uff1a\u3058\u3093\uff1a\u5ddd\uff1a\u305b\u3093\uff1a\u6c96\uff1a\u304a\u304d\uff1a\u306b\u3066\u6575\uff1a\u3066\u304d\uff1a\u8266\uff1a\u304b\u3093\uff1a\u306e\u6483\uff1a\u3052\u304d\uff1a\u6c88\uff1a\u3061\u3093\uff1a\u304c\u3042\u308a \u6b21\uff1a\u3064\u304e\uff1a\u306e\u65e5\uff1a\u3072\uff1a\u306b\u5ba3\u6226 >> \u907c\uff1a\u308a\u3083\u3046\uff1a\u967d\uff1a\u3084\u3046\uff1a\u30fb\u6c99\uff1a\u3057\u3083\uff1a\u6cb3\uff1a\u304b\uff1a\u306e\u6703\uff1a\u304f\u308f\u3044\uff1a\u6230\uff1a\u305b\u3093\uff1a\u306b\u52dd\uff1a\u3057\u3087\u3046\uff1a\u5229\uff1a\u308a\uff1a \u6d77\uff1a\u304b\u3044\uff1a\u4e0a\uff1a\u3058\u3083\u3046\uff1a\u6a29\uff1a\u3051\u3093\uff1a\u306e\u7372\uff1a\u304b\u304f\uff1a\u5f97\uff1a\u3068\u304f\uff1a \u65c5\uff1a\u308a\u3087\uff1a\u9806\uff1a\u3058\u3085\u3093\uff1a\u9665\uff1a\u304b\u3093\uff1a\u843d\uff1a\u3089\u304f\uff1a \u5949\uff1a\u307b\u3046\uff1a\u5929\uff1a\u3066\u3093\uff1a\u5360\uff1a\u305b\u3093\uff1a\u9818\uff1a\u308a\u3087\u3046\uff1a\u3092\u7d4c\uff1a\u3078\uff1a\u3066 \u65e5\uff1a\u306b\uff1a\u672c\uff1a\u307b\u3093\uff1a\u6d77\uff1a\u304b\u3044\uff1a\u6d77\uff1a\u304b\u3044\uff1a\u6230\uff1a\u305b\u3093\uff1a\u306b\u3066\u30d0\u30eb\u30c1\u30c3\u30af\u8266\uff1a\u304b\u3093\uff1a\u968a\uff1a\u305f\u3044\uff1a\u3092\u5168\uff1a\u305c\u3093\uff1a\u6ec5\uff1a\u3081\u3064\uff1a\u3055\u305b \u6a3a\uff1a\u304b\u3089\uff1a\u592a\uff1a\u3075\u3068\uff1a\u5168\uff1a\u305c\u3093\uff1a\u5cf6\uff1a\u305f\u3046\uff1a\u3092\u5360\uff1a\u305b\u3093\uff1a\u9818\uff1a\u308a\u3083\u3046\uff1a\n1931,\u6e80\uff1a\u307e\u3093\uff1a\u6d32\uff1a\u3057\u3046\uff1a\u4e8b\uff1a\u3058\uff1a\u8b8a\uff1a\u3078\u3093\uff1a,\u30bd\u9023\uff1a\u308c\u3093\uff1a\u306e\u5916\uff1a\u304c\u3044\uff1a\u8499\uff1a\u3082\u3046\uff1a\u9032\uff1a\u3057\u3093\uff1a\u51fa\uff1a\u3057\u3085\u3064\uff1a \u4e8b\uff1a\u3058\uff1a\u5be6\uff1a\u3058\u3064\uff1a\u4e0a\uff1a\u3058\u3083\u3046\uff1a\u4e09\u3064\u306e\u653f\uff1a\u305b\u3044\uff1a\u5e9c\uff1a\u3075\uff1a\u3092\u6301\uff1a\u3082\uff1a\u3064\u4e0d\uff1a\u3075\uff1a\u5b89\uff1a\u3042\u3093\uff1a\u5b9a\uff1a\u3066\u3044\uff1a\u306a\u652f\uff1a\u3057\uff1a\u90a3\uff1a\u306a\uff1a \u65e5\uff1a\u306b\uff1a\u672c\uff1a\u307b\u3093\uff1a\u4eba\uff1a\u3058\u3093\uff1a\u306e\u8650\uff1a\u304e\u3083\u304f\uff1a\u6bba\uff1a\u3055\u3064\uff1a \u5f35\uff1a\u3061\u3087\u3046\uff1a\u4f5c\uff1a\u3055\u304f\uff1a\u9716\uff1a\u308a\u3093\uff1a\u30fb\u5f35\uff1a\u3061\u3087\u3046\uff1a\u5b78\uff1a\u304c\u304f\uff1a\u826f\uff1a\u308a\u3087\u3046\uff1a\u306e\u79d5\uff1a\u3072\uff1a\u653f\uff1a\u305b\u3044\uff1a\u306b\u3088\u308b\u6e80\uff1a\u307e\u3093\uff1a\u6d32\uff1a\u3057\u3046\uff1a\u4eba\uff1a\u3058\u3093\uff1a\u306e\u7aae\uff1a\u304d\u3085\u3046\uff1a\u4e4f\uff1a\u307c\u3075\uff1a \u6e80\uff1a\u307e\u3093\uff1a\u6d32\uff1a\u3057\u3046\uff1a\u72ec\uff1a\u3069\u304f\uff1a\u7acb\uff1a\u308a\u3064\uff1a\u904b\uff1a\u3046\u3093\uff1a\u52d5\uff1a\u3069\u3046\uff1a\u306a\u3069 \u6e80\u6d32\u306b\u306f\u3044\u3064\u7206\uff1a\u3070\u304f\uff1a\u767c\uff1a\u306f\u3064\uff1a\u3057\u3066\u3082\u304a\u304b\u3057\u304f\u306a\u3044 \u7dca\uff1a\u304d\u3093\uff1a\u5f35\uff1a\u3061\u3083\u3046\uff1a\u72b6\uff1a\u3058\u3083\u3046\uff1a\u614b\uff1a\u305f\u3044\uff1a\u304c\u3042\u3063\u305f,\u77f3\uff1a\u3044\u3057\uff1a\u539f\uff1a\u306f\u3089\uff1a\u839e\uff1a\u304b\u3093\uff1a\u723e\uff1a\u3058\uff1a\u4e2d\uff1a\u3061\u3085\u3046\uff1a\u4f50\uff1a\u3055\uff1a\u306e\u7dbf\uff1a\u3081\u3093\uff1a\u5bc6\uff1a\u307f\u3064\uff1a\u306a\u8a08\uff1a\u3051\u3044\uff1a\u753b\uff1a\u304b\u304f\uff1a\u306b\u3088\u308a \u67f3\uff1a\u308a\u3046\uff1a\u6761\uff1a\u3067\u3046\uff1a\u6e9d\uff1a\u3053\u3046\uff1a\u306b\u304a\u3051\u308b\u6e80\uff1a\u307e\u3093\uff1a\u6d32\uff1a\u3057\u3046\uff1a\u9244\uff1a\u3066\u3064\uff1a\u9053\uff1a\u3060\u3046\uff1a\u306e\u7dda\uff1a\u305b\u3093\uff1a\u8def\uff1a\u308d\uff1a\u304c\u5c0f\uff1a\u305b\u3046\uff1a\u898f\uff1a\u304d\uff1a\u6a21\uff1a\u307c\uff1a\u306b\u7206\uff1a\u3070\u304f\uff1a\u7834\uff1a\u306f\uff1a\u3055\u308c \u305d\u308c\u3092\u5f35\uff1a\u3061\u3087\u3046\uff1a\u5b78\uff1a\u304b\u304f\uff1a\u826f\uff1a\u308a\u3087\u3046\uff1a\u306e\u4ed5\uff1a\u3057\uff1a\u696d\uff1a\u308f\u3056\uff1a\u3068\u3057\u305f\u95a2\uff1a\u304b\u3093\uff1a\u6771\uff1a\u3068\u3046\uff1a\u8ecd\uff1a\u3050\u3093\uff1a\u306f \u5317\uff1a\u307b\u304f\uff1a\u5927\uff1a\u305f\u3044\uff1a\u55b6\uff1a\u3048\u3044\uff1a\u306e\u652f\uff1a\u3057\uff1a\u90a3\uff1a\u306a\uff1a\u8ecd\uff1a\u3050\u3093\uff1a\u3092\u6557\uff1a\u306f\u3044\uff1a\u8d70\uff1a\u305d\u3046\uff1a\u305b\u3057\u3081 \u3053\u308c\u3092\u5360\uff1a\u305b\u3093\uff1a\u9818\uff1a\u308a\u3083\u3046\uff1a\u3057\u305f\n1937,\u652f\uff1a\u3057\uff1a\u90a3\uff1a\u306a\uff1a\u4e8b\uff1a\u3058\uff1a\u8b8a\uff1a\u3078\u3093\uff1a,\u76e7\uff1a\u308d\uff1a\u6e9d\uff1a\u3053\u3046\uff1a\u6a4b\uff1a\u3051\u3046\uff1a\u4e8b\uff1a\u3058\uff1a\u4ef6\uff1a\u3051\u3093\uff1a\u3092\u5951\uff1a\u3051\u3044\uff1a\u6a5f\uff1a\u304d\uff1a\u3068\u3057 \u4e0a\uff1a\u3057\u3083\u3093\uff1a\u6d77\uff1a\u306f\u3044\uff1a\u4e8b\uff1a\u3058\uff1a\u8b8a\uff1a\u306f\u3093\uff1a\u3078 \u305d\u3057\u3066\u65e5\uff1a\u306b\u3063\uff1a\u652f\uff1a\u3057\uff1a\u4e21\uff1a\u308a\u3083\u3046\uff1a\u570b\uff1a\u3053\u304f\uff1a\u304c\u5168\uff1a\u305c\u3093\uff1a\u9762\uff1a\u3081\u3093\uff1a\u6230\uff1a\u305b\u3093\uff1a\u722d\uff1a\u3055\u3046\uff1a\u306e\u6bb5\uff1a\u3060\u3093\uff1a\u968e\uff1a\u304b\u3044\uff1a\u306b\u7a81\uff1a\u3068\u3064\uff1a\u5165\uff1a\u306b\u3075\uff1a\u3057\u305f,\u8ecd\uff1a\u3050\u3093\uff1a\u4e8b\uff1a\u3058\uff1a\u6f14\uff1a\u3048\u3093\uff1a\u7fd2\uff1a\u3057\u3075\uff1a\u3092\u7d42\uff1a\u3057\u3085\u3046\uff1a\u4e86\uff1a\u308c\u3046\uff1a\u3057\u305f\u652f\uff1a\u3057\uff1a\u90a3\uff1a\u306a\uff1a\u99d0\uff1a\u3061\u3085\u3046\uff1a\u5c6f\uff1a\u3068\u3093\uff1a\u6b69\uff1a\u307b\uff1a\u5175\uff1a\u3078\u3044\uff1a\u306b\u5c0d\uff1a\u305f\u3044\uff1a\u3057\u9283\uff1a\u3058\u3085\u3046\uff1a\u6483\uff1a\u3052\u304d\uff1a\u304c\u6d74\uff1a\u3042\uff1a\u3073\u305b\u3089\u308c \u6211\uff1a\u308f\u304c\uff1a\u8ecd\uff1a\u3050\u3093\uff1a\u306f\u61c9\uff1a\u304a\u3046\uff1a\u5c04\uff1a\u3057\u3083\uff1a\u305b\u305a\u306b\u72b6\uff1a\u3058\u3083\u3046\uff1a\u6cc1\uff1a\u304d\u3083\u3046\uff1a\u306e\u628a\uff1a\u306f\uff1a\u63e1\uff1a\u3042\u304f\uff1a \u652f\uff1a\u3057\uff1a\u90a3\uff1a\u306a\uff1a\u8ecd\uff1a\u3050\u3093\uff1a\u3068\u306e\u4ea4\uff1a\u304b\u3046\uff1a\u6e09\uff1a\u305b\u3075\uff1a\u3092\u9032\uff1a\u3059\u3059\uff1a\u3081\u305f\u304c \u6211\uff1a\u308f\u304c\uff1a\u8ecd\uff1a\u3050\u3093\uff1a\u306e\u6230\uff1a\u305b\u3093\uff1a\u95d8\uff1a\u3068\u3046\uff1a\u614b\uff1a\u305f\u3044\uff1a\u52e2\uff1a\u305b\u3044\uff1a\u3092\u307f\u305f\u652f\uff1a\u3057\uff1a\u90a3\uff1a\u306a\uff1a\u5175\uff1a\u3078\u3044\uff1a\u306f\u731b\uff1a\u307e\u3046\uff1a\u5c04\uff1a\u3057\u3083\uff1a\u3057 \u4e03\u6642\uff1a\u3058\uff1a\u9593\uff1a\u304b\u3093\uff1a\u306e\u81ea\uff1a\u3058\uff1a\u91cd\uff1a\u3061\u3087\u3046\uff1a\u3082\u865a\uff1a\u3080\u306a\uff1a\u3057\u304f\u6211\u8ecd\u306f\u53cd\uff1a\u306f\u3093\uff1a\u6483\uff1a\u3052\u304d\uff1a \u7adc\uff1a\u308a\u3085\u3046\uff1a\u738b\uff1a\u308f\u3046\uff1a\u5ef3\uff1a\u3061\u3087\u3046\uff1a\u306e\u6575\uff1a\u3066\u304d\uff1a\u3092\u6483\uff1a\u3052\u304d\uff1a\u6ec5\uff1a\u3081\u3064\uff1a\u3057\u6c38\uff1a\u3048\u3044\uff1a\u5b9a\uff1a\u3066\u3044\uff1a\u6cb3\uff1a\u304c\uff1a\u306e\u53f3\uff1a\u3046\uff1a\u5cb8\uff1a\u304c\u3093\uff1a\u3078\u9032\uff1a\u3057\u3093\uff1a\u51fa\uff1a\u3057\u3085\u3064\uff1a\n1941,\u5927\uff1a\u3060\u3044\uff1a\u6771\uff1a\u3068\u3046\uff1a\u4e9e\uff1a\u3042\uff1a\u6230\uff1a\u305b\u3093\uff1a\u722d\uff1a\u3055\u3046\uff1a,\u6557\uff1a\u306f\u3044\uff1a\u6230\uff1a\u305b\u3093\uff1a\u5f8c\uff1a\u3054\uff1a\u306e\u6211\uff1a\u308f\u304c\uff1a\u570b\uff1a\u304f\u306b\uff1a\u306f \u3053\u306e\u6230\uff1a\u305b\u3093\uff1a\u722d\uff1a\u3055\u3046\uff1a\u3092<\u592a\uff1a\u305f\u3044\uff1a\u5e73\uff1a\u3078\u3044\uff1a\u6d0b\uff1a\u3084\u3046\uff1a\u6230\u722d>\u3068\u547c\uff1a\u3053\uff1a\u7a31\uff1a\u305b\u3046\uff1a\u3057\u3066\u3090\u308b,\u3053\u306e\u6230\u722d\u306b\u6557\uff1a\u3084\u3076\uff1a\u308c\u305f\u6211\u570b\u306f\u5360\uff1a\u305b\u3093\uff1a\u9818\uff1a\u308a\u3083\u3046\uff1a\u7d71\uff1a\u3068\u3046\uff1a\u6cbb\uff1a\u3061\uff1a\u3055\u308c \u52dd\uff1a\u3057\u3087\u3046\uff1a\u8005\uff1a\u3057\u3083\uff1a\u306b\u90fd\uff1a\u3064\uff1a\u5408\uff1a\u304c\u3075\uff1a\u306e\u60e1\uff1a\u308f\u308b\uff1a\u3044\u6b74\uff1a\u308c\u304d\uff1a\u53f2\uff1a\u3057\uff1a\u306e\u6559\uff1a\u3051\u3046\uff1a\u80b2\uff1a\u3044\u304f\uff1a\u3092\u4e00\uff1a\u3044\u3063\uff1a\u5207\uff1a\u3055\u3044\uff1a\u6392\uff1a\u306f\u3044\uff1a\u9664\uff1a\u3058\u3087\uff1a\u3055\u308c\u4eca\uff1a\u3044\u307e\uff1a\u306b\u81f3\uff1a\u3044\u305f\uff1a\u308b\n1945,\u30dd\u30c4\u30c0\u30e0\u5ba3\uff1a\u305b\u3093\uff1a\u8a00\uff1a\u3052\u3093\uff1a,\u6b63\uff1a\u305b\u3044\uff1a\u5f0f\uff1a\u3057\u304d\uff1a\u540d\uff1a\u3081\u3044\uff1a\u7a31\uff1a\u305b\u3046\uff1a\u306f<\u65e5\uff1a\u306b\uff1a\u672c\uff1a\u307b\u3093\uff1a\u3078\u306e\u964d\uff1a\u304b\u3046\uff1a\u4f0f\uff1a\u3075\u304f\uff1a\u8981\uff1a\u3048\u3046\uff1a\u6c42\uff1a\u304d\u3046\uff1a\u306e\u6700\uff1a\u3055\u3044\uff1a\u7d42\uff1a\u3057\u3085\u3046\uff1a\u5ba3\uff1a\u305b\u3093\uff1a\u8a00\uff1a\u3052\u3093\uff1a>,\u5168\uff1a\u305c\u3093\uff1a13\u30f6\uff1a\u304b\uff1a\u6761\uff1a\u3067\u3046\uff1a\u304b\u3089\u306a\u308a \u30a4\u30ae\u30ea\u30b9\u30fb\u30a2\u30e1\u30ea\u30ab\u5408\uff1a\u304c\u3063\uff1a\u8846\uff1a\u3057\u3085\u3046\uff1a\u570b\uff1a\u3053\u304f\uff1a\u30fb\u4e2d\uff1a\u3061\u3085\u3046\uff1a\u83ef\uff1a\u304f\u308f\uff1a\u6c11\uff1a\u307f\u3093\uff1a\u570b\uff1a\u3053\u304f\uff1a\u306e\u653f\uff1a\u305b\u3044\uff1a\u5e9c\uff1a\u3075\uff1a\u9996\uff1a\u3057\u3085\uff1a\u8133\uff1a\u306e\u3046\uff1a\u306e\u9023\uff1a\u308c\u3093\uff1a\u540d\uff1a\u3081\u3044\uff1a\u306b\u304a\u3044\u3066\u767c\uff1a\u306f\u3063\uff1a\u305b\u3089\u308c \u30bd\u30d3\u30a8\u30c8\u9023\uff1a\u308c\u3093\uff1a\u90a6\uff1a\u3071\u3046\uff1a\u306f \u5f8c\uff1a\u3042\u3068\uff1a\u304b\u3089\u52a0\uff1a\u304f\u306f\uff1a\u306f\u308a\u8ffd\uff1a\u3064\u3044\uff1a\u8a8d\uff1a\u306b\u3093\uff1a\u3057\u305f\n1951,\u30b5\u30f3\u30d5\u30e9\u30f3\u30b7\u30b9\u30b3\u5e73\uff1a\u3078\u3044\uff1a\u548c\uff1a\u308f\uff1a\u6761\uff1a\u3067\u3046\uff1a\u7d04\uff1a\u3084\u304f\uff1a,\u6b63\uff1a\u305b\u3044\uff1a\u5f0f\uff1a\u3057\u304d\uff1a\u540d\uff1a\u3081\u3044\uff1a\u306f<\u65e5\uff1a\u306b\uff1a\u672c\uff1a\u307b\u3093\uff1a\u570b\uff1a\u3053\u304f\uff1a\u3068\u306e\u5e73\uff1a\u3078\u3044\uff1a\u548c\uff1a\u308f\uff1a\u6761\uff1a\u3067\u3046\uff1a\u7d04\uff1a\u3084\u304f\uff1a>,\u5927\uff1a\u3060\u3044\uff1a\u6771\uff1a\u3068\u3046\uff1a\u4e9e\uff1a\u3042\uff1a\u6230\uff1a\u305b\u3093\uff1a\u722d\uff1a\u3055\u3046\uff1a\u306e\u6557\uff1a\u306f\u3044\uff1a\u6230\uff1a\u305b\u3093\uff1a\u570b\uff1a\u3053\u304f\uff1a\u3067\u3042\u308a \u5360\uff1a\u305b\u3093\uff1a\u9818\uff1a\u308a\u3083\u3046\uff1a\u7d71\uff1a\u3068\u3046\uff1a\u6cbb\uff1a\u3061\uff1a\u3055\u308c\u3066\u3090\u305f\u6211\uff1a\u308f\u304c\uff1a\u570b\uff1a\u304f\u306b\uff1a\u304c \u3053\u306e\u6761\uff1a\u3067\u3046\uff1a\u7d04\uff1a\u3084\u304f\uff1a\u3092\u6279\uff1a\u3072\uff1a\u51c6\uff1a\u3058\u3085\u3093\uff1a\u3057\u305f\u9023\uff1a\u308c\u3093\uff1a\u5408\uff1a\u304c\u3075\uff1a\u570b\uff1a\u3053\u304f\uff1a\u306b\u3088\u308a\u4e3b\uff1a\u3057\u3085\uff1a\u6a29\uff1a\u3051\u3093\uff1a\u3092\u627f\uff1a\u3057\u3087\u3046\uff1a\u8a8d\uff1a\u306b\u3093\uff1a\u3055\u308c \u570b\uff1a\u3053\u304f\uff1a\u969b\uff1a\u3055\u3044\uff1a\u6cd5\uff1a\u306f\u3046\uff1a\u4e0a\uff1a\u3058\u3083\u3046\uff1a \u6211\u570b\u3068\u591a\uff1a\u304a\u307b\uff1a\u304f\u306e\u9023\u5408\u570b\u3068\u306e\u9593\uff1a\u3042\u3072\u3060\uff1a\u306e<\u6230\uff1a\u305b\u3093\uff1a\u722d\uff1a\u3055\u3046\uff1a\u72b6\uff1a\u3058\u3083\u3046\uff1a\u614b\uff1a\u305f\u3044\uff1a>\u304c\u7d42\uff1a\u3057\u3085\u3046\uff1a\u7d50\uff1a\u3051\u3064\uff1a\u3057\u305f \u3053\u306e\u6761\u7d04\u3067\u6211\u570b\u306f1875\u5e74\u306b\u5168\uff1a\u305c\u3093\uff1a\u57df\uff1a\u3044\u304d\uff1a\u3092\u9818\uff1a\u308a\u3083\u3046\uff1a\u6709\uff1a\u3044\u3046\uff1a\u3057\u305f\u5343\uff1a\u3061\uff1a\u5cf6\uff1a\u3057\u307e\uff1a\u5217\uff1a\u308c\u3063\uff1a\u5cf6\uff1a\u305f\u3046\uff1a\u3092\u653e\uff1a\u306f\u3046\uff1a\u68c4\uff1a\u304d\uff1a\u3057\u3066\u3090\u308b \u306a\u307b \u3053\u306e\u6761\u7d04\u306e\u767c\uff1a\u306f\u3063\uff1a\u52b9\uff1a\u304b\u3046\uff1a\u65e5\uff1a\u3073\uff1a\u306f1952\u5e74<\u662d\u548c27\u5e74>4\u670828\u65e5\u3067\u3042\u308a \u6211\u570b\u306e\u4e3b\uff1a\u3057\u3085\uff1a\u6a29\uff1a\u3051\u3093\uff1a\u304c\u56de\uff1a\u304b\u3044\uff1a\u5fa9\uff1a\u3075\u304f\uff1a\u3057 \u5360\uff1a\u305b\u3093\uff1a\u9818\uff1a\u308a\u3083\u3046\uff1a\u72b6\uff1a\u3058\u3083\u3046\uff1a\u614b\uff1a\u305f\u3044\uff1a\u3082\u89e3\uff1a\u304b\u3044\uff1a\u9664\uff1a\u3058\u3087\uff1a\u3055\u308c\u305f"));}),_1G0=new T(function(){return B(_1FT(_1FZ));}),_1G1=new T(function(){return B(_aj(_1FO,_1G0));}),_1G2=new T(function(){return B(_cQ(1,2));}),_1G3=new T(function(){return B(unCStr("1871,\u65e5\u6e05\u4fee\u597d\u6761\u898f,\u3053\u306e\u6642\u306e\u4e21\u56fd\u306f \u5bfe\u7b49\u306a\u6761\u7d04\u3092\u7de0\u7d50\u3057\u305f,\u3053\u306e\u5f8c\u65e5\u6e05\u6226\u4e89\u306b\u3088\u3063\u3066 \u65e5\u6e05\u9593\u306e\u6761\u7d04\u306f \u3044\u306f\u3086\u308b<\u4e0d\u5e73\u7b49>\u306a\u3082\u306e\u3068\u306a\u3063\u305f(\u65e5\u672c\u306b\u306e\u307f\u6cbb\u5916\u6cd5\u6a29\u3092\u8a8d\u3081 \u6e05\u570b\u306b\u95a2\u7a0e\u81ea\u4e3b\u6a29\u304c\u306a\u3044)\n1875,\u6c5f\u83ef\u5cf6\u4e8b\u4ef6,\u3053\u306e\u4e8b\u4ef6\u306e\u7d50\u679c \u65e5\u9bae\u4fee\u4ea4\u6761\u898f(\u4e0d\u5e73\u7b49\u6761\u7d04\u3068\u3055\u308c\u308b)\u3092\u7de0\u7d50,\u8ecd\u8266\u96f2\u63da\u53f7\u304c\u98f2\u6599\u6c34\u78ba\u4fdd\u306e\u305f\u3081\u6c5f\u83ef\u5cf6\u306b\u63a5\u8fd1\u3057\u305f\u969b \u7a81\u5982\u540c\u5cf6\u306e\u7832\u53f0\u3088\u308a\u5f37\u70c8\u306a\u7832\u6483\u3092\u53d7\u3051\u308b>>>\u96f2\u63da\u306f\u53cd\u6483\u3057\u9678\u6226\u968a\u3092\u4e0a\u9678\u3055\u305b\u7832\u53f0\u3092\u5360\u62e0 \u6b66\u5668\u3092\u6355\u7372\u3057\u3066\u9577\u5d0e\u3078\u5e30\u7740\n1877,\u897f\u5357\u6226\u4e89,\u620a\u8fb0\u6230\u722d\u3092\u6230\u3063\u305f\u58eb\u65cf\u305f\u3061\u304c \u660e\u6cbb\u7dad\u65b0\u306b\u4e0d\u6e80\u3092\u62b1\u304d \u897f\u90f7\u9686\u76db\u3092\u62c5\u3044\u3067\u8702\u8d77,\u897f\u90f7\u9686\u76db\u3092\u7dcf\u5927\u5c06\u3068\u3059\u308b\u53cd\u4e71\u8ecd\u306f\u653f\u5e9c\u8ecd\u306b\u93ae\u5727\u3055\u308c \u897f\u90f7\u306f\u81ea\u6c7a \u4ee5\u5f8c\u58eb\u65cf\u306e\u53cd\u4e71\u306f\u9014\u7d76\u3078 \u620a\u8fb0\u6226\u4e89\u304b\u3089\u5341\u5e74\u7d9a\u3044\u3066\u3090\u305f\u52d5\u4e71\u306f\u53ce\u675f\u3057\u305f\n1882,\u58ec\u5348\u306e\u5909,\u4ff8\u7d66\u306e\u9045\u914d\u3092\u304d\u3063\u304b\u3051\u3068\u3057\u305f\u65e7\u5175\u306e\u66b4\u52d5\u3092\u5927\u9662\u541b\u304c\u717d\u52d5(\u5927\u9662\u541b\u306f\u65e7\u5b88\u6d3e \u9594\u5983\u4e00\u65cf\u306f\u958b\u5316\u6d3e),\u65e5\u97d3\u4fee\u4ea4\u4ee5\u964d \u9594\u5983\u4e00\u65cf\u306e\u958b\u5316\u6d3e\u304c\u529b\u3092\u306e\u3070\u3057 \u65e5\u672c\u306e\u8fd1\u4ee3\u5316\u306b\u5023\u306f\u3093\u3068 \u5927\u898f\u6a21\u306a\u8996\u5bdf\u56e3\u3092\u6d3e\u9063\u3057\u305f\u308a \u65e5\u672c\u304b\u3089\u5800\u672c\u793c\u9020\u3092\u62db\u3044\u3066\u65b0\u5f0f\u8ecd\u968a\u3092\u7de8\u6210\u3059\u308b\u306a\u3069\u8ecd\u653f\u6539\u9769\u3092\u65ad\u884c\u3057\u3066\u3090\u305f\u304c \u65e7\u5175\u3068\u5927\u9662\u541b\u306e\u53cd\u4e71\u306b\u3088\u308a \u591a\u6570\u306e\u65e5\u672c\u4eba\u304c\u8650\u6bba\u3055\u308c\u65e5\u672c\u516c\u4f7f\u9928\u304c\u8972\u6483\u3055\u308c\u305f(\u5800\u672c\u793c\u9020\u3082\u6bba\u3055\u308c\u308b) \u6e05\u570b\u306f\u7d04\u4e94\u5343\u306e\u5175\u3092\u304a\u304f\u308a\u4e71\u306e\u93ae\u5727\u306b\u5f53\u308b\u3068\u3068\u3082\u306b \u9996\u9b41\u3067\u3042\u308b\u5927\u9662\u541b\u3092\u6e05\u570b\u306b\u62c9\u81f4\u3057\u6291\u7559>>\u3053\u306e\u4e8b\u5909\u306e\u5584\u5f8c\u7d04\u5b9a\u3068\u3057\u3066 \u65e5\u672c\u30fb\u671d\u9bae\u9593\u306b\u6e08\u7269\u6d66\u6761\u7d04\u304c\u7d50\u3070\u308c \u671d\u9bae\u5074\u306f\u72af\u4eba\u306e\u53b3\u7f70 \u8ce0\u511f\u91d1 \u516c\u4f7f\u9928\u8b66\u5099\u306e\u305f\u3081\u4eac\u57ce\u306b\u65e5\u672c\u8ecd\u82e5\u5e72\u3092\u7f6e\u304f \u65e5\u672c\u306b\u8b1d\u7f6a\u4f7f\u3092\u6d3e\u9063\u3059\u308b\u3053\u3068\u3092\u7d04\u3057\u305f\n1885,\u5929\u6d25\u6761\u7d04,\u65e5\u672c\u304c\u652f\u63f4\u3057\u671d\u9bae\u306e\u72ec\u7acb\u3092\u3081\u3056\u3059\u52e2\u529b\u3068 \u6e05\u306e\u5f8c\u62bc\u3057\u3067\u305d\u308c\u3092\u963b\u3080\u52e2\u529b\u304c\u885d\u7a81\u3057 \u591a\u6570\u306e\u72a0\u7272\u304c\u51fa\u305f\u304c \u4e00\u61c9\u3053\u306e\u6761\u7d04\u3067\u7d50\u7740\u3059\u308b,\u65e5\u6e05\u4e21\u56fd\u306e\u671d\u9bae\u304b\u3089\u306e\u64a4\u5175 \u4eca\u5f8c\u65e5\u6e05\u4e21\u56fd\u304c\u3084\u3080\u306a\u304f\u51fa\u5175\u3059\u308b\u3068\u304d\u306f\u4e8b\u524d\u901a\u544a\u3059\u308b \u306a\u3069\u304c\u5b9a\u3081\u3089\u308c\u305f\n1894,\u65e5\u6e05\u6226\u4e89,\u671d\u9bae\u3067\u8fb2\u6c11\u4e00\u63c6\u304c\u653f\u6cbb\u66b4\u52d5\u5316(\u6771\u5b66\u515a\u306e\u4e71)\u304c\u8d77\u7206\u5264\u3068\u306a\u308b,\u8c4a\u5cf6\u6c96\u6d77\u6226\u306f \u6211\u304c\u9023\u5408\u8266\u968a\u7b2c\u4e00\u904a\u6483\u968a\u5409\u91ce\u304c\u793c\u7832\u4ea4\u63db\u306e\u7528\u610f\u3092\u3057\u3066\u8fd1\u63a5\u3057\u305f\u306e\u306b\u5c0d\u3057 \u6e05\u570b\u8ecd\u8266\u6e08\u9060\u306e\u6226\u95d8\u6e96\u5099\u304a\u3088\u3073\u767a\u7832\u3088\u308a\u306f\u3058\u307e\u308b\n1895,\u4e0b\u95a2\u6761\u7d04,\u65e5\u6e05\u6226\u4e89\u306b\u6211\u570b\u304c\u52dd\u5229\u3057\u3066\u7d50\u3070\u308c\u305f\u6761\u7d04>>>\u4e09\u56fd\u5e72\u6e09\u3092\u53d7\u3051\u308b,\u4e00 \u6e05\u570b\u306f\u671d\u9bae\u570b\u304c\u5b8c\u5168\u7121\u6b20\u306e\u72ec\u7acb\u81ea\u4e3b\u306e\u570b\u3067\u3042\u308b\u3053\u3068\u3092\u627f\u8a8d\u3059\u308b \u4e8c \u6e05\u570b\u306f\u907c\u6771\u534a\u5cf6 \u53f0\u6e7e\u5168\u5cf6\u53ca\u3073\u6f8e\u6e56\u5217\u5cf6\u3092\u6c38\u9060\u306b\u65e5\u672c\u306b\u5272\u8b72\u3059\u308b \u4e09 \u6e05\u570b\u306f\u8ecd\u8cbb\u8ce0\u511f\u91d1\u4e8c\u5104\u4e21\u3092\u652f\u6255\u3075 \u56db \u65e5\u6e05\u9593\u306e\u4e00\u5207\u306e\u6761\u7d04\u306f\u4ea4\u6230\u306e\u305f\u3081\u6d88\u6ec5\u3057\u305f\u306e\u3067\u65b0\u305f\u306b\u901a\u5546\u822a\u6d77\u6761\u7d04\u3092\u7d50\u3076 \u4e94 \u672c\u6761\u7d04\u6279\u51c6\u5f8c \u76f4\u3061\u306b\u4fd8\u865c\u3092\u8fd4\u9084\u3059\u308b \u6e05\u570b\u306f\u9001\u9084\u3055\u308c\u305f\u4fd8\u865c\u3092\u8650\u5f85\u3042\u308b\u3044\u306f\u51e6\u5211\u305b\u306c\u3053\u3068\n1899,\u7fa9\u548c\u56e3\u4e8b\u5909,\u65e5\u9732\u6226\u4e89\u306e\u539f\u56e0\u306e\u3072\u3068\u3064\u3068\u8a00\u3078\u308b,<\u6276\u6e05\u6ec5\u6d0b>\u3092\u9ad8\u5531\u3057\u3066\u6392\u5916\u904b\u52d5\u3092\u8d77\u3057 \u30ad\u30ea\u30b9\u30c8\u6559\u5f92\u6bba\u5bb3 \u6559\u4f1a \u9244\u9053 \u96fb\u7dda\u306a\u3069\u3092\u7834\u58ca\u3059\u308b \u5b97\u6559\u7684\u79d8\u5bc6\u7d50\u793e\u3067\u3042\u308b\u7fa9\u548c\u56e3\u306b\u6e05\u5175\u304c\u52a0\u306f\u308a \u5404\u570b\u516c\u4f7f\u9928\u304c\u5305\u56f2\u3055\u308c\u308b\u306b\u53ca\u3073 \u82f1\u56fd\u304b\u3089\u56db\u56de\u306b\u308f\u305f\u308a\u51fa\u5175\u8981\u8acb\u304c\u3055\u308c\u305f\u65e5\u672c\u3092\u4e3b\u529b\u3068\u3059\u308b\u516b\u30f6\u56fd\u9023\u5408\u8ecd\u304c \u5317\u4eac\u516c\u4f7f\u9928\u533a\u57df\u3092\u7fa9\u548c\u56e3\u30fb\u6e05\u5175\u306e\u5305\u56f2\u304b\u3089\u6551\u51fa \u7fa9\u548c\u56e3\u4e8b\u5909\u6700\u7d42\u8b70\u5b9a\u66f8\u306f1901\u5e74\u9023\u5408\u5341\u4e00\u30f6\u56fd\u3068\u6e05\u570b\u306e\u9593\u3067\u8abf\u5370\u3055\u308c \u6e05\u306f\u8ce0\u511f\u91d1\u306e\u652f\u6255\u3072\u306e\u4ed6 \u5404\u570b\u304c\u5341\u4e8c\u30f6\u6240\u306e\u5730\u70b9\u3092\u5360\u9818\u3059\u308b\u6a29\u5229\u3092\u627f\u8a8d \u3053\u306e\u99d0\u5175\u6a29\u306b\u3088\u3063\u3066\u6211\u570b\u306f\u8af8\u5916\u56fd\u3068\u3068\u3082\u306b\u652f\u90a3\u99d0\u5c6f\u8ecd\u3092\u7f6e\u304f\u3053\u3068\u306b\u306a\u3063\u305f(\u76e7\u6e9d\u6a4b\u3067\u4e2d\u56fd\u5074\u304b\u3089\u4e0d\u6cd5\u5c04\u6483\u3092\u53d7\u3051\u305f\u90e8\u968a\u3082 \u3053\u306e\u6761\u7d04\u306b\u3088\u308b\u99d0\u5175\u6a29\u306b\u57fa\u3065\u304d\u99d0\u5c6f\u3057\u3066\u3090\u305f)\n1900,\u30ed\u30b7\u30a2\u6e80\u6d32\u5360\u9818,\u7fa9\u548c\u56e3\u306e\u4e71\u306b\u4e57\u3058\u3066\u30ed\u30b7\u30a2\u306f\u30b7\u30d9\u30ea\u30a2\u65b9\u9762\u3068\u65c5\u9806\u304b\u3089\u5927\u5175\u3092\u6e80\u6d32\u306b\u9001\u308b>>><\u9ed2\u7adc\u6c5f\u4e0a\u306e\u60b2\u5287>\u304c\u3053\u306e\u6642\u8d77\u3053\u308b,\u30ed\u30b7\u30a2\u306f\u7fa9\u548c\u56e3\u4e8b\u5909\u93ae\u5b9a\u5f8c\u3082\u7d04\u306b\u9055\u80cc\u3057\u3066\u64a4\u5175\u305b\u305a \u3084\u3046\u3084\u304f\u9732\u6e05\u9593\u306b\u6e80\u6d32\u9084\u4ed8\u5354\u7d04\u304c\u8abf\u5370\u3055\u308c\u308b\u3082 \u4e0d\u5c65\u884c\n1902,\u65e5\u82f1\u540c\u76df,\u65e5\u9732\u6226\u4e89\u306e\u52dd\u5229\u306b\u852d\u306e\u529b\u3068\u306a\u308b,\u4e00 \u65e5\u82f1\u4e21\u56fd\u306f\u6e05\u97d3\u4e21\u56fd\u306e\u72ec\u7acb\u3092\u627f\u8a8d\u3059\u308b \u3057\u304b\u3057\u82f1\u56fd\u306f\u6e05\u56fd\u3067 \u65e5\u672c\u306f\u6e05\u97d3\u4e21\u56fd\u3067\u653f\u6cbb\u30fb\u7d4c\u6e08\u4e0a\u683c\u6bb5\u306e\u5229\u76ca\u3092\u6709\u3059\u308b\u306e\u3067 \u305d\u308c\u3089\u306e\u5229\u76ca\u304c\u7b2c\u4e09\u56fd\u306e\u4fb5\u7565\u3084\u5185\u4e71\u3067\u4fb5\u8feb\u3055\u308c\u305f\u6642\u306f\u5fc5\u8981\u306a\u63aa\u7f6e\u3092\u3068\u308b \u4e8c \u65e5\u82f1\u306e\u4e00\u65b9\u304c\u3053\u306e\u5229\u76ca\u3092\u8b77\u308b\u305f\u3081\u7b2c\u4e09\u56fd\u3068\u6230\u3075\u6642\u306f\u4ed6\u306e\u4e00\u65b9\u306f\u53b3\u6b63\u4e2d\u7acb\u3092\u5b88\u308a \u4ed6\u56fd\u304c\u6575\u5074\u306b\u53c2\u6226\u3059\u308b\u306e\u3092\u9632\u3050 \u4e09 \u4ed6\u56fd\u304c\u540c\u76df\u56fd\u3068\u306e\u4ea4\u6230\u306b\u52a0\u306f\u308b\u6642\u306f \u4ed6\u306e\u540c\u76df\u56fd\u306f \u63f4\u52a9\u3092\u8207\u3078\u308b\n1904,\u65e5\u9732\u6226\u4e89,\u6975\u6771\u306e\u30ed\u30b7\u30a2\u8ecd\u306b\u52d5\u54e1\u4ee4\u304c \u6e80\u6d32\u306b\u306f\u6212\u53b3\u4ee4\u304c\u4e0b\u3055\u308c \u5bfe\u9732\u4ea4\u6e09\u306f\u6c7a\u88c2 \u6211\u570b\u306f\u570b\u4ea4\u65ad\u7d76\u3092\u9732\u570b\u306b\u901a\u544a,\u6211\u570b\u806f\u5408\u8266\u968a\u306b\u3088\u308b \u65c5\u9806\u6e2f\u5916\u306e\u653b\u6483 \u4ec1\u5ddd\u6c96\u306b\u3066\u6575\u8266\u306e\u6483\u6c88\u304c\u3042\u308a \u6b21\u306e\u65e5\u306b\u5ba3\u6226>>>\u907c\u967d\u30fb\u6c99\u6cb3\u306e\u4f1a\u6226\u306b\u52dd\u5229 \u6d77\u4e0a\u6a29\u306e\u7372\u5f97 \u65c5\u9806\u9665\u843d \u5949\u5929\u5360\u9818\u3092\u7d4c\u3066 \u65e5\u672c\u6d77\u6d77\u6226\u306b\u3066\u30d0\u30eb\u30c1\u30c3\u30af\u8266\u968a\u3092\u5168\u6ec5\u3055\u305b \u6a3a\u592a\u5168\u5cf6\u3092\u5360\u9818\n1905,\u30dd\u30fc\u30c4\u30de\u30b9\u6761\u7d04,\u7c73\u56fd\u30cb\u30e5\u30fc\u30fb\u30cf\u30f3\u30d7\u30b7\u30e3\u30fc\u5dde \u6211\u570b\u5168\u6a29\u306f\u5916\u76f8\u5c0f\u6751\u5bff\u592a\u90ce \u9732\u570b\u5168\u6a29\u306f\u524d\u8535\u76f8\u30a6\u30a3\u30c3\u30c6,\u4e00 \u9732\u570b\u306f \u65e5\u672c\u304c\u97d3\u570b\u3067\u653f\u6cbb \u8ecd\u4e8b \u7d4c\u6e08\u4e0a\u306e\u5353\u7d76\u3057\u305f\u5229\u76ca\u3092\u6709\u3057 \u304b\u3064\u5fc5\u8981\u306a\u6307\u5c0e \u4fdd\u8b77 \u76e3\u7406\u3092\u884c\u3075\u6a29\u5229\u3092\u627f\u8a8d\u3059 \u4e8c \u4e21\u570b\u306f\u5341\u516b\u30f6\u6708\u4ee5\u5185\u306b\u6e80\u6d32\u3088\u308a\u64a4\u5175\u3059 \u4e09 \u9732\u570b\u306f\u907c\u6771\u534a\u5cf6\u79df\u501f\u6a29\u3092\u65e5\u672c\u306b\u8b72\u6e21\u3059 \u3053\u308c\u306b\u3064\u304d\u4e21\u56fd\u306f\u6e05\u570b\u306e\u627f\u8afe\u3092\u5f97\u308b\u3053\u3068 \u56db \u9732\u570b\u306f\u6771\u652f\u9244\u9053\u5357\u6e80\u6d32\u652f\u7dda(\u9577\u6625\u30fb\u65c5\u9806\u9593)\u3092\u4ed8\u5c5e\u306e\u70ad\u9271\u3068\u5171\u306b\u65e5\u672c\u306b\u8b72\u6e21\u3059 \u4e94 \u9732\u570b\u306f\u5317\u7def\u4e94\u5341\u5ea6\u4ee5\u5357\u306e\u6a3a\u592a\u3092\u65e5\u672c\u306b\u8b72\u6e21\u3059 (\u6211\u570b\u306f\u8ce0\u511f\u91d1\u8981\u6c42\u3092\u653e\u68c4)\n1910,\u65e5\u97d3\u4f75\u5408,\u674e\u6c0f\u671d\u9bae\u304c\u4e94\u767e\u6709\u4f59\u5e74\u306e\u6b74\u53f2\u3092\u9589\u3058\u308b,\u65e5\u9732\u6226\u4e89\u5f8c \u97d3\u570b\u306f\u65e5\u672c\u306b\u4fdd\u8b77\u5316\u3055\u308c\u308b\u9053\u3092\u9032\u3080\u304c \u4f0a\u85e4\u535a\u6587\u304c\u6697\u6bba\u3055\u308c\u308b\u3084 \u97d3\u570b\u4f75\u5408\u8ad6\u304c\u9ad8\u307e\u308b\n1911,\u8f9b\u4ea5\u9769\u547d,\u660e\u6cbb44\u5e74 \u6e05\u671d\u306e\u6ec5\u4ea1,\u848b\u4ecb\u77f3\u306f\u5357\u4eac\u306b\u570b\u6c11\u653f\u5e9c\u3092\u7acb\u3066 \u5f35\u4f5c\u9716\u306e\u5317\u4eac\u653f\u5e9c\u3092\u8a0e\u4f10\u3059\u308b\u305f\u3081\u5317\u3078\n1914,\u7b2c\u4e00\u6b21\u4e16\u754c\u5927\u6230,\u5927\u6b633\u5e74,\u30dc\u30b9\u30cb\u30a2\u306e\u9996\u90fd\u30b5\u30e9\u30a8\u30dc\u3067\u30aa\u30fc\u30b9\u30c8\u30ea\u30a2\u7687\u592a\u5b50\u592b\u59bb\u304c\u30bb\u30eb\u30d3\u30a2\u306e\u4e00\u9752\u5e74\u306b\u6697\u6bba\u3055\u308c\u308b\u3068 \u30aa\u30fc\u30b9\u30c8\u30ea\u30a2\u304c\u30bb\u30eb\u30d3\u30a2\u306b\u5ba3\u6226 \u30c9\u30a4\u30c4\u304c\u30ed\u30b7\u30a2\u306b\u5ba3\u6230 \u4ecf\u30fb\u82f1\u3082\u5c0d\u72ec\u5ba3\u6230\n1915,\u65e5\u83ef\u6761\u7d04,\u3044\u306f\u3086\u308b<\u4e8c\u5341\u4e00\u30f6\u6761\u306e\u8981\u6c42>,\u3082\u3068\u3082\u3068\u652f\u90a3\u3068\u4ea4\u306f\u3055\u308c\u3066\u3090\u305f\u7d04\u5b9a\u3092\u6b50\u6d32\u5217\u56fd\u306e\u5e72\u6e09\u306a\u3069\u3067\u7834\u58ca\u3055\u308c\u306a\u3044\u3084\u3046\u306b \u62d8\u675f\u529b\u306e\u3042\u308b\u6761\u7d04\u306b\u3059\u308b\u305f\u3081\u306e\u3082\u306e\u3067 \u3082\u3068\u3082\u3068\u306e\u4e03\u30f6\u6761\u306f\u5e0c\u671b\u6761\u9805\u3067\u3042\u308a \u7d50\u5c40\u6761\u7d04\u3068\u3057\u3066\u7d50\u3070\u308c\u305f\u306e\u306f\u5341\u516d\u30f6\u6761\u3067\u3042\u3063\u305f\u304c \u6761\u7d04\u3092\u7d50\u3093\u3060\u4e2d\u83ef\u6c11\u56fd\u306f \u65e5\u672c\u306b\u5f37\u8feb\u3055\u308c\u3066\u7d50\u3093\u3060\u306e\u3060\u3068\u5185\u5916\u306b\u5ba3\u4f1d\u3057 1922\u5e74\u306b\u306f\u6761\u7d04\u3068\u3057\u3066\u5341\u30f6\u6761\u304c\u6b98\u5b58\u3059\u308b\u3060\u3051\u3068\u306a\u308b\u4e2d \u4e2d\u83ef\u6c11\u56fd\u56fd\u4f1a\u306f \u6761\u7d04\u306e\u7121\u52b9\u3092\u5ba3\u8a00 \u6fc0\u70c8\u306a\u53cd\u65e5\u306e\u4e2d\u3067 \u305d\u308c\u3089\u306e\u6761\u7d04\u3082\u4e8b\u5b9f\u4e0a \u7a7a\u6587\u5316\u3057\u305f\n1917,\u77f3\u4e95\u30fb\u30e9\u30f3\u30b7\u30f3\u30b0\u5354\u5b9a,\u7b2c\u4e00\u6b21\u4e16\u754c\u5927\u6226\u4e2d\u65e5\u7c73\u9593\u306b\u7d50\u3070\u308c\u305f\u5354\u5b9a,\u7c73\u56fd\u304c\u57f7\u62d7\u306b\u9580\u6238\u958b\u653e\u4e3b\u7fa9\u3092\u5531\u9053\u3057 \u65e5\u672c\u306e\u6e80\u8499\u9032\u51fa\u3092\u63a3\u8098\u305b\u3093\u3068\u3059\u308b\u52d5\u304d\u304c\u3042\u3063\u305f\u305f\u3081 \u3042\u3089\u305f\u3081\u3066\u652f\u90a3\u306b\u304a\u3051\u308b\u65e5\u672c\u306e\u7279\u6b8a\u5730\u4f4d\u306b\u95a2\u3057\u3066 \u7c73\u56fd\u306e\u627f\u8a8d\u3092\u78ba\u4fdd\u305b\u3093\u3068\u3044\u3075\u8981\u8acb\u304c\u3042\u3063\u305f>>>\u5ba3\u8a00\u306e\u524d\u6bb5\u306f<\u65e5\u672c\u56fd\u53ca\u5317\u7c73\u5408\u8846\u56fd\u4e21\u56fd\u653f\u5e9c\u306f \u9818\u571f\u76f8\u63a5\u8fd1\u3059\u308b\u56fd\u5bb6\u306e\u9593\u306b\u306f\u7279\u6b8a\u306e\u95dc\u4fc2\u3092\u751f\u305a\u308b\u3053\u3068\u3092\u627f\u8a8d\u3059 \u5f93\u3066\u5408\u8846\u56fd\u653f\u5e9c\u306f\u65e5\u672c\u304c\u652f\u90a3\u306b\u65bc\u3066\u7279\u6b8a\u306e\u5229\u76ca\u3092\u6709\u3059\u308b\u3053\u3068\u3092\u627f\u8a8d\u3059 \u65e5\u672c\u306e\u6240\u9818\u306b\u63a5\u58cc\u3059\u308b\u5730\u65b9\u306b\u65bc\u3066\u7279\u306b\u7136\u308a\u3068\u3059>>>>\u5f8c\u6bb5\u306f<\u65e5\u672c\u56fd\u53ca\u5408\u8846\u56fd\u4e21\u56fd\u653f\u5e9c\u306f\u6beb\u3082\u652f\u90a3\u306e\u72ec\u7acb\u53c8\u306f\u9818\u571f\u4fdd\u5168\u3092\u4fb5\u5bb3\u3059\u308b\u306e\u76ee\u7684\u3092\u6709\u3059\u308b\u3082\u306e\u306b\u975e\u3056\u308b\u3053\u3068\u3092\u58f0\u660e\u3059 \u304b\u3064\u4e21\u56fd\u653f\u5e9c\u306f\u5e38\u306b\u652f\u90a3\u306b\u65bc\u3066\u6240\u8b02\u9580\u6238\u958b\u653e\u53c8\u306f\u5546\u5de5\u696d\u306b\u5c0d\u3059\u308b\u6a5f\u4f1a\u5747\u7b49\u306e\u4e3b\u7fa9\u3092\u652f\u6301\u3059\u308b\u3053\u3068\u3092\u58f0\u660e\u3059>"));}),_1G4=new T(function(){return B(_1FT(_1G3));}),_1G5=new T(function(){return B(_aj(_1FO,_1G4));}),_1G6=function(_1G7,_1G8){var _1G9=E(_1G7);if(!_1G9._){return __Z;}else{var _1Ga=E(_1G8);return (_1Ga._==0)?__Z:new T2(1,new T2(0,new T(function(){return E(_1G9.a).a;}),_1Ga.a),new T(function(){return B(_1G6(_1G9.b,_1Ga.b));}));}},_1Gb=new T(function(){return eval("(function(k) {localStorage.removeItem(k);})");}),_1Gc=new T(function(){return B(unCStr("tail"));}),_1Gd=new T(function(){return B(_rf(_1Gc));}),_1Ge=new T(function(){return eval("(function(k,v) {localStorage.setItem(k,v);})");}),_1Gf=function(_1Gg){return E(E(_1Gg).b);},_1Gh=function(_1Gi,_1Gj,_1Gk){var _1Gl=new T(function(){var _1Gm=E(_1Gk);if(!_1Gm._){return __Z;}else{var _1Gn=_1Gm.b,_1Go=E(_1Gm.a),_1Gp=E(_1Go.a);if(_1Gp<_1Gi){var _1Gq=function(_1Gr){while(1){var _1Gs=B((function(_1Gt){var _1Gu=E(_1Gt);if(!_1Gu._){return __Z;}else{var _1Gv=_1Gu.b,_1Gw=E(_1Gu.a);if(E(_1Gw.a)<_1Gi){_1Gr=_1Gv;return __continue;}else{return new T2(1,_1Gw,new T(function(){return B(_1Gq(_1Gv));}));}}})(_1Gr));if(_1Gs!=__continue){return _1Gs;}}};return B(_1Gx(B(_1Gq(_1Gn))));}else{var _1Gy=new T(function(){var _1Gz=function(_1GA){while(1){var _1GB=B((function(_1GC){var _1GD=E(_1GC);if(!_1GD._){return __Z;}else{var _1GE=_1GD.b,_1GF=E(_1GD.a);if(E(_1GF.a)<_1Gi){_1GA=_1GE;return __continue;}else{return new T2(1,_1GF,new T(function(){return B(_1Gz(_1GE));}));}}})(_1GA));if(_1GB!=__continue){return _1GB;}}};return B(_1Gz(_1Gn));});return B(_1Gh(_1Gp,_1Go.b,_1Gy));}}}),_1GG=E(_1Gk);if(!_1GG._){return new F(function(){return _x(_Z,new T2(1,new T2(0,_1Gi,_1Gj),_1Gl));});}else{var _1GH=_1GG.b,_1GI=E(_1GG.a),_1GJ=E(_1GI.a);if(_1GJ>=_1Gi){var _1GK=function(_1GL){while(1){var _1GM=B((function(_1GN){var _1GO=E(_1GN);if(!_1GO._){return __Z;}else{var _1GP=_1GO.b,_1GQ=E(_1GO.a);if(E(_1GQ.a)>=_1Gi){_1GL=_1GP;return __continue;}else{return new T2(1,_1GQ,new T(function(){return B(_1GK(_1GP));}));}}})(_1GL));if(_1GM!=__continue){return _1GM;}}};return new F(function(){return _x(B(_1Gx(B(_1GK(_1GH)))),new T2(1,new T2(0,_1Gi,_1Gj),_1Gl));});}else{var _1GR=new T(function(){var _1GS=function(_1GT){while(1){var _1GU=B((function(_1GV){var _1GW=E(_1GV);if(!_1GW._){return __Z;}else{var _1GX=_1GW.b,_1GY=E(_1GW.a);if(E(_1GY.a)>=_1Gi){_1GT=_1GX;return __continue;}else{return new T2(1,_1GY,new T(function(){return B(_1GS(_1GX));}));}}})(_1GT));if(_1GU!=__continue){return _1GU;}}};return B(_1GS(_1GH));});return new F(function(){return _x(B(_1Gh(_1GJ,_1GI.b,_1GR)),new T2(1,new T2(0,_1Gi,_1Gj),_1Gl));});}}},_1Gx=function(_1GZ){var _1H0=E(_1GZ);if(!_1H0._){return __Z;}else{var _1H1=_1H0.b,_1H2=E(_1H0.a),_1H3=_1H2.a,_1H4=new T(function(){var _1H5=E(_1H1);if(!_1H5._){return __Z;}else{var _1H6=_1H5.b,_1H7=E(_1H5.a),_1H8=E(_1H7.a),_1H9=E(_1H3);if(_1H8<_1H9){var _1Ha=function(_1Hb){while(1){var _1Hc=B((function(_1Hd){var _1He=E(_1Hd);if(!_1He._){return __Z;}else{var _1Hf=_1He.b,_1Hg=E(_1He.a);if(E(_1Hg.a)<_1H9){_1Hb=_1Hf;return __continue;}else{return new T2(1,_1Hg,new T(function(){return B(_1Ha(_1Hf));}));}}})(_1Hb));if(_1Hc!=__continue){return _1Hc;}}};return B(_1Gx(B(_1Ha(_1H6))));}else{var _1Hh=new T(function(){var _1Hi=function(_1Hj){while(1){var _1Hk=B((function(_1Hl){var _1Hm=E(_1Hl);if(!_1Hm._){return __Z;}else{var _1Hn=_1Hm.b,_1Ho=E(_1Hm.a);if(E(_1Ho.a)<_1H9){_1Hj=_1Hn;return __continue;}else{return new T2(1,_1Ho,new T(function(){return B(_1Hi(_1Hn));}));}}})(_1Hj));if(_1Hk!=__continue){return _1Hk;}}};return B(_1Hi(_1H6));});return B(_1Gh(_1H8,_1H7.b,_1Hh));}}}),_1Hp=E(_1H1);if(!_1Hp._){return new F(function(){return _x(_Z,new T2(1,_1H2,_1H4));});}else{var _1Hq=_1Hp.b,_1Hr=E(_1Hp.a),_1Hs=E(_1Hr.a),_1Ht=E(_1H3);if(_1Hs>=_1Ht){var _1Hu=function(_1Hv){while(1){var _1Hw=B((function(_1Hx){var _1Hy=E(_1Hx);if(!_1Hy._){return __Z;}else{var _1Hz=_1Hy.b,_1HA=E(_1Hy.a);if(E(_1HA.a)>=_1Ht){_1Hv=_1Hz;return __continue;}else{return new T2(1,_1HA,new T(function(){return B(_1Hu(_1Hz));}));}}})(_1Hv));if(_1Hw!=__continue){return _1Hw;}}};return new F(function(){return _x(B(_1Gx(B(_1Hu(_1Hq)))),new T2(1,_1H2,_1H4));});}else{var _1HB=new T(function(){var _1HC=function(_1HD){while(1){var _1HE=B((function(_1HF){var _1HG=E(_1HF);if(!_1HG._){return __Z;}else{var _1HH=_1HG.b,_1HI=E(_1HG.a);if(E(_1HI.a)>=_1Ht){_1HD=_1HH;return __continue;}else{return new T2(1,_1HI,new T(function(){return B(_1HC(_1HH));}));}}})(_1HD));if(_1HE!=__continue){return _1HE;}}};return B(_1HC(_1Hq));});return new F(function(){return _x(B(_1Gh(_1Hs,_1Hr.b,_1HB)),new T2(1,_1H2,_1H4));});}}}},_1HJ=function(_){return new F(function(){return jsMkStdout();});},_1HK=new T(function(){return B(_3d(_1HJ));}),_1HL=new T(function(){return B(_Q1("Browser.hs:84:24-56|(Right j)"));}),_1HM=function(_1HN){var _1HO=jsParseJSON(toJSStr(E(_1HN)));return (_1HO._==0)?E(_1HL):E(_1HO.a);},_1HP=0,_1HQ=function(_1HR,_1HS,_1HT,_1HU,_1HV){var _1HW=E(_1HV);if(!_1HW._){var _1HX=new T(function(){var _1HY=B(_1HQ(_1HW.a,_1HW.b,_1HW.c,_1HW.d,_1HW.e));return new T2(0,_1HY.a,_1HY.b);});return new T2(0,new T(function(){return E(E(_1HX).a);}),new T(function(){return B(_78(_1HS,_1HT,_1HU,E(_1HX).b));}));}else{return new T2(0,new T2(0,_1HS,_1HT),_1HU);}},_1HZ=function(_1I0,_1I1,_1I2,_1I3,_1I4){var _1I5=E(_1I3);if(!_1I5._){var _1I6=new T(function(){var _1I7=B(_1HZ(_1I5.a,_1I5.b,_1I5.c,_1I5.d,_1I5.e));return new T2(0,_1I7.a,_1I7.b);});return new T2(0,new T(function(){return E(E(_1I6).a);}),new T(function(){return B(_6h(_1I1,_1I2,E(_1I6).b,_1I4));}));}else{return new T2(0,new T2(0,_1I1,_1I2),_1I4);}},_1I8=function(_1I9,_1Ia){var _1Ib=E(_1I9);if(!_1Ib._){var _1Ic=_1Ib.a,_1Id=E(_1Ia);if(!_1Id._){var _1Ie=_1Id.a;if(_1Ic<=_1Ie){var _1If=B(_1HZ(_1Ie,_1Id.b,_1Id.c,_1Id.d,_1Id.e)),_1Ig=E(_1If.a);return new F(function(){return _78(_1Ig.a,_1Ig.b,_1Ib,_1If.b);});}else{var _1Ih=B(_1HQ(_1Ic,_1Ib.b,_1Ib.c,_1Ib.d,_1Ib.e)),_1Ii=E(_1Ih.a);return new F(function(){return _6h(_1Ii.a,_1Ii.b,_1Ih.b,_1Id);});}}else{return E(_1Ib);}}else{return E(_1Ia);}},_1Ij=function(_1Ik,_1Il){var _1Im=E(_1Ik),_1In=E(_1Il);if(!_1In._){var _1Io=_1In.b,_1Ip=_1In.c,_1Iq=_1In.d,_1Ir=_1In.e;switch(B(_65(_1Im,_1Io))){case 0:return new F(function(){return _6h(_1Io,_1Ip,B(_1Ij(_1Im,_1Iq)),_1Ir);});break;case 1:return new F(function(){return _1I8(_1Iq,_1Ir);});break;default:return new F(function(){return _78(_1Io,_1Ip,_1Iq,B(_1Ij(_1Im,_1Ir)));});}}else{return new T0(1);}},_1Is=function(_1It,_1Iu){while(1){var _1Iv=E(_1It);if(!_1Iv._){return E(_1Iu);}else{var _1Iw=B(_1Ij(new T2(1,_1Iv.a,_1th),_1Iu));_1It=_1Iv.b;_1Iu=_1Iw;continue;}}},_1Ix=function(_1Iy,_1Iz,_1IA,_1IB,_1IC,_1ID,_1IE,_1IF,_1IG,_1IH,_1II,_1IJ,_1IK,_1IL,_1IM,_1IN,_1IO,_1IP,_1IQ,_1IR,_1IS,_1IT,_1IU,_1IV,_1IW,_1IX,_1IY,_1IZ,_1J0,_1J1,_1J2,_1J3,_1J4,_1J5,_1J6,_1J7,_1J8,_1J9,_1Ja,_1Jb,_1Jc,_1Jd,_1Je,_1Jf,_1Jg,_1Jh,_1Ji,_1Jj,_1Jk,_){var _1Jl={_:0,a:E(_1Jb),b:E(_1Jc),c:E(_1Jd),d:E(_1Je),e:E(_1Jf),f:E(_1Jg),g:E(_1Jh),h:E(_1Ji),i:E(_1Jj)},_1Jm=new T2(0,_1J7,_1J8),_1Jn=new T2(0,_1IV,_1IW),_1Jo=new T2(0,_1IO,_1IP),_1Jp={_:0,a:E(_1ID),b:E(_1IE),c:E(_1IF),d:_1IG,e:_1IH,f:_1II,g:E(_1IJ),h:_1IK,i:E(_1IL),j:E(_1IM),k:E(_1IN)},_1Jq={_:0,a:E(_1Jp),b:E(_1Jo),c:E(_1IQ),d:E(_1IR),e:E(_1IS),f:E(_1IT),g:E(_1IU),h:E(_1Jn),i:_1IX,j:_1IY,k:_1IZ,l:_1J0,m:E(_1J1),n:_1J2,o:E(_1J3),p:E(_1J4),q:_1J5,r:E(_1J6),s:E(_1Jm),t:_1J9,u:E(_1Ja),v:E(_1Jl),w:E(_1Jk)};if(!E(_1Jg)){if(!E(_1Jc)){var _1Jr=function(_1Js){if(!E(_1Je)){if(!E(_1Ji)){return _1Jq;}else{var _1Jt=function(_,_1Ju,_1Jv,_1Jw,_1Jx,_1Jy,_1Jz,_1JA,_1JB,_1JC,_1JD,_1JE,_1JF,_1JG,_1JH,_1JI,_1JJ,_1JK,_1JL,_1JM,_1JN,_1JO,_1JP,_1JQ,_1JR,_1JS,_1JT,_1JU,_1JV,_1JW,_1JX,_1JY,_1JZ,_1K0,_1K1){var _1K2=B(_1bL(_1F4,_1JB,_)),_1K3=_1K2,_1K4=E(_1Iy),_1K5=_1K4.a,_1K6=_1K4.b,_1K7=new T(function(){return B(_1u9(E(_1IC)));}),_1K8=new T(function(){var _1K9=E(_1K7),_1Ka=E(_1Ju),_1Kb=_1Ka.b,_1Kc=E(_1Ka.a),_1Kd=function(_1Ke,_1Kf){var _1Kg=E(_1Ke),_1Kh=E(_1Kf);if(_1Kg<=_1Kc){if(_1Kc<=_1Kg){var _1Ki=E(_1Kb);if(_1Kh<=_1Ki){if(_1Ki<=_1Kh){var _1Kj=4;}else{var _1Kj=0;}var _1Kk=_1Kj;}else{var _1Kk=1;}var _1Kl=_1Kk;}else{var _1Kl=2;}var _1Km=_1Kl;}else{var _1Km=3;}var _1Kn=function(_1Ko,_1Kp,_1Kq,_1Kr,_1Ks,_1Kt,_1Ku,_1Kv,_1Kw,_1Kx){switch(E(_1Km)){case 0:if(!E(_1Jw)){var _1Ky=new T2(0,_1JW,_1JX);}else{var _1Ky=new T2(0,_1JW,_1Fi);}var _1Kz=_1Ky;break;case 1:if(E(_1Jw)==1){var _1KA=new T2(0,_1JW,_1JX);}else{var _1KA=new T2(0,_1JW,_1HP);}var _1Kz=_1KA;break;case 2:if(E(_1Jw)==2){var _1KB=new T2(0,_1JW,_1JX);}else{var _1KB=new T2(0,_1JW,_1F3);}var _1Kz=_1KB;break;case 3:if(E(_1Jw)==3){var _1KC=new T2(0,_1JW,_1JX);}else{var _1KC=new T2(0,_1JW,_1F2);}var _1Kz=_1KC;break;default:if(E(_1Jw)==4){var _1KD=new T2(0,_1JW,_1JX);}else{var _1KD=new T2(0,_1JW,_1HP);}var _1Kz=_1KD;}var _1KE=B(_1qQ(_1HP,_1Kv,_1JI,{_:0,a:E(_1Ko),b:E(_1Kp),c:E(_1Kq),d:_1Kr,e:_1Ks,f:_1Kt,g:E(_1Ku),h:E(E(_1K3).b),i:E(_1Kv),j:E(_1Kw),k:E(_1Kx)},_1JF,_1JG,_1JH,_1JI,_1JJ,_1JK,_1JL,_1JM,_1JN,_1JO,_1JP,_1JQ,_1JR,_1JS,_1JT,_1JU,_1JV,_1Kz,_1JY,_1JZ,_1K0,_1K1)),_1KF=_1KE.a,_1KG=_1KE.b,_1KH=_1KE.c,_1KI=_1KE.d,_1KJ=_1KE.e,_1KK=_1KE.f,_1KL=_1KE.g,_1KM=_1KE.h,_1KN=_1KE.i,_1KO=_1KE.j,_1KP=_1KE.k,_1KQ=_1KE.l,_1KR=_1KE.m,_1KS=_1KE.n,_1KT=_1KE.o,_1KU=_1KE.q,_1KV=_1KE.r,_1KW=_1KE.s,_1KX=_1KE.t,_1KY=_1KE.u,_1KZ=_1KE.v,_1L0=_1KE.w,_1L1=E(_1KE.p);if(!_1L1._){return {_:0,a:E(_1KF),b:E(_1KG),c:E(_1KH),d:E(_1KI),e:E(_1KJ),f:E(_1KK),g:E(_1KL),h:E(_1KM),i:_1KN,j:_1KO,k:_1KP,l:_1KQ,m:E(_1KR),n:_1KS,o:E(_1KT),p:E(_Z),q:_1KU,r:E(_1KV),s:E(_1KW),t:_1KX,u:E(_1KY),v:E(_1KZ),w:E(_1L0)};}else{var _1L2=B(_qu(_1Kv,0))-2|0,_1L3=function(_1L4){var _1L5=E(_1KF);return {_:0,a:E({_:0,a:E(_1L5.a),b:E(_1L5.b),c:E(_1L5.c),d:_1L5.d,e:_1L5.e,f:_1L5.f,g:E(_Z),h:_1L5.h,i:E(_1L5.i),j:E(_1L5.j),k:E(_1L5.k)}),b:E(_1KG),c:E(_1KH),d:E(B(_x(B(_0(_Z,B(_1Is(B(_aj(_1Gf,_1L1)),B(_9T(_1KI)))))),new T(function(){return B(_aj(_1E4,_1L1));},1)))),e:E(_1KJ),f:E(_1KK),g:E(_1KL),h:E(_1KM),i:_1KN,j:_1KO,k:_1KP,l:_1KQ,m:E(_1KR),n:_1KS,o:E(_1KT),p:E(_Z),q:_1KU,r:E(B(_x(_1KV,new T2(1,_1KU,_Z)))),s:E(_1KW),t:_1KX,u:E(_1KY),v:E(_1KZ),w:E(_1L0)};};if(_1L2>0){if(!B(_vi(B(_1DM(_1L2,_1Kv)),_1F1))){return {_:0,a:E(_1KF),b:E(_1KG),c:E(_1KH),d:E(_1KI),e:E(_1KJ),f:E(_1KK),g:E(_1KL),h:E(_1KM),i:_1KN,j:_1KO,k:_1KP,l:_1KQ,m:E(_1KR),n:_1KS,o:E(_1KT),p:E(_1L1),q:_1KU,r:E(_1KV),s:E(_1KW),t:_1KX,u:E(_1KY),v:E(_1KZ),w:E(_1L0)};}else{return new F(function(){return _1L3(_);});}}else{if(!B(_vi(_1Kv,_1F1))){return {_:0,a:E(_1KF),b:E(_1KG),c:E(_1KH),d:E(_1KI),e:E(_1KJ),f:E(_1KK),g:E(_1KL),h:E(_1KM),i:_1KN,j:_1KO,k:_1KP,l:_1KQ,m:E(_1KR),n:_1KS,o:E(_1KT),p:E(_1L1),q:_1KU,r:E(_1KV),s:E(_1KW),t:_1KX,u:E(_1KY),v:E(_1KZ),w:E(_1L0)};}else{return new F(function(){return _1L3(_);});}}}};if(E(_1K9)==32){var _1L6=B(_1A2(_1Kg,_1Kh,_1Kc,_1Kb,_1Jv,_1Km,_1Jx,_1Jy,_1Jz,_1JA,_1JB,_1JC,_1JD,_1JE)),_1L7=E(_1L6.a),_1L8=B(_1Dn(_1L7.a,E(_1L7.b),_1L6.b,_1L6.c,_1L6.d,_1L6.e,_1L6.f,_1L6.g,_1L6.h,_1L6.i,_1L6.j,_1L6.k));return new F(function(){return _1Kn(_1L8.a,_1L8.b,_1L8.c,_1L8.d,_1L8.e,_1L8.f,_1L8.g,_1L8.i,_1L8.j,_1L8.k);});}else{var _1L9=B(_1A2(_1Kg,_1Kh,_1Kc,_1Kb,_1Jv,_1Km,_1Jx,_1Jy,_1Jz,_1JA,_1JB,_1JC,_1JD,_1JE));return new F(function(){return _1Kn(_1L9.a,_1L9.b,_1L9.c,_1L9.d,_1L9.e,_1L9.f,_1L9.g,_1L9.i,_1L9.j,_1L9.k);});}};switch(E(_1K9)){case 72:var _1La=E(_1Kb);if(0<=(_1La-1|0)){return B(_1Kd(_1Kc,_1La-1|0));}else{return B(_1Kd(_1Kc,_1La));}break;case 75:if(0<=(_1Kc-1|0)){return B(_1Kd(_1Kc-1|0,_1Kb));}else{return B(_1Kd(_1Kc,_1Kb));}break;case 77:if(E(_1IO)!=(_1Kc+1|0)){return B(_1Kd(_1Kc+1|0,_1Kb));}else{return B(_1Kd(_1Kc,_1Kb));}break;case 80:var _1Lb=E(_1Kb);if(E(_1IP)!=(_1Lb+1|0)){return B(_1Kd(_1Kc,_1Lb+1|0));}else{return B(_1Kd(_1Kc,_1Lb));}break;case 104:if(0<=(_1Kc-1|0)){return B(_1Kd(_1Kc-1|0,_1Kb));}else{return B(_1Kd(_1Kc,_1Kb));}break;case 106:var _1Lc=E(_1Kb);if(E(_1IP)!=(_1Lc+1|0)){return B(_1Kd(_1Kc,_1Lc+1|0));}else{return B(_1Kd(_1Kc,_1Lc));}break;case 107:var _1Ld=E(_1Kb);if(0<=(_1Ld-1|0)){return B(_1Kd(_1Kc,_1Ld-1|0));}else{return B(_1Kd(_1Kc,_1Ld));}break;case 108:if(E(_1IO)!=(_1Kc+1|0)){return B(_1Kd(_1Kc+1|0,_1Kb));}else{return B(_1Kd(_1Kc,_1Kb));}break;default:return B(_1Kd(_1Kc,_1Kb));}}),_1Le=B(_1dW(_1K5,_1K6,_1Iz,_1IA,_1IB,_1K8,_)),_1Lf=_1Le,_1Lg=E(_1K7),_1Lh=function(_,_1Li){var _1Lj=function(_1Lk){var _1Ll=B(_1Ez(_1HK,B(_cr(_1Li)),_)),_1Lm=E(_1Lf),_1Ln=_1Lm.d,_1Lo=_1Lm.e,_1Lp=_1Lm.f,_1Lq=_1Lm.g,_1Lr=_1Lm.i,_1Ls=_1Lm.j,_1Lt=_1Lm.k,_1Lu=_1Lm.l,_1Lv=_1Lm.m,_1Lw=_1Lm.n,_1Lx=_1Lm.o,_1Ly=_1Lm.p,_1Lz=_1Lm.q,_1LA=_1Lm.r,_1LB=_1Lm.t,_1LC=_1Lm.u,_1LD=_1Lm.w,_1LE=E(_1Lm.v),_1LF=_1LE.a,_1LG=_1LE.d,_1LH=_1LE.e,_1LI=_1LE.f,_1LJ=_1LE.g,_1LK=_1LE.h,_1LL=_1LE.i,_1LM=E(_1Lm.a),_1LN=_1LM.c,_1LO=_1LM.f,_1LP=_1LM.g,_1LQ=_1LM.h,_1LR=E(_1Lm.h),_1LS=E(_1Lm.s),_1LT=function(_1LU){var _1LV=function(_1LW){if(_1LW!=E(_1EU)){var _1LX=B(_aS(_1mu,_1LW)),_1LY=_1LX.a,_1LZ=E(_1LX.b),_1M0=B(_1gr(_1LY,_1LZ,new T(function(){return B(_aS(_1oz,_1LW));})));return new F(function(){return _1Ix(_1K4,_1Iz,_1IA,_1IB,_1ET,B(_aS(_1mF,_1LW)),_1M0,_1LN,B(_aS(_1mS,_1LW)),32,_1LW,_1LP,_1LQ,B(_x(_1LM.i,new T2(1,_1ES,new T(function(){return B(_H(0,_1LO,_Z));})))),B(_1Ed(_1ER,_1M0)),_B3,_1LY,_1LZ,_Z,_1Ln,_1Lo,_1Lp,_1Lq,_1LR.a,_1LR.b,_1Lr,_1Ls,_1Lt, -1,_1Lv,_1Lw,_1Lx,_1Ly,_1Lz,_1LA,_1LS.a,_1LS.b,_1LB,_1LC,_B3,_B3,_B3,_1LG,_1LH,_1LI,_1LJ,_1LK,_1LL,_1LD,_);});}else{var _1M1=__app1(E(_rj),_1K6),_1M2=B(A2(_rk,_1K5,_)),_1M3=B(A(_qP,[_1K5,_n4,_1EN,_1EP,_1EO,_])),_1M4=B(A(_qP,[_1K5,_n4,_1EN,_1EM,_1Fj,_])),_1M5=B(A(_qP,[_1K5,_n4,_1Fi,_1Fh,_1Fg,_]));return new T(function(){return {_:0,a:E({_:0,a:E(_1mw),b:E(_1Ff),c:E(_1LN),d:E(_1Fd),e:32,f:0,g:E(_1LP),h:_1LQ,i:E(_Z),j:E(_1LM.j),k:E(_B3)}),b:E(_1mh),c:E(_1Lm.c),d:E(_1Ln),e:E(_1Lo),f:E(_1Lp),g:E(_1Lq),h:E(_1LR),i:_1Lr,j:_1Ls,k:_1Lt,l:_1Lu,m:E(_1Lv),n:_1Lw,o:E(_1Lx),p:E(_1Ly),q:_1Lz,r:E(_1LA),s:E(_1LS),t:_1LB,u:E(_1LC),v:E({_:0,a:E(_1LF),b:E(_B4),c:E(_B3),d:E(_1LG),e:E(_1LH),f:E(_1LI),g:E(_1LJ),h:E(_1LK),i:E(_1LL)}),w:E(_1LD)};});}};if(_1Lu>=0){return new F(function(){return _1LV(_1Lu);});}else{return new F(function(){return _1LV(_1LO+1|0);});}};if(!E(_1LF)){if(E(_1Lg)==110){return new F(function(){return _1LT(_);});}else{return _1Lm;}}else{return new F(function(){return _1LT(_);});}};if(E(_1Lg)==114){if(!B(_ae(_1Li,_1EV))){var _1M6=E(_1Li);if(!_1M6._){return _1Lf;}else{var _1M7=_1M6.b;return new T(function(){var _1M8=E(_1Lf),_1M9=E(_1M8.a),_1Ma=E(_1M6.a),_1Mb=E(_1Ma);if(_1Mb==34){var _1Mc=B(_YC(_1Ma,_1M7));if(!_1Mc._){var _1Md=E(_1Gd);}else{var _1Me=E(_1Mc.b);if(!_1Me._){var _1Mf=E(_1Fb);}else{var _1Mg=_1Me.a,_1Mh=E(_1Me.b);if(!_1Mh._){var _1Mi=new T2(1,new T2(1,_1Mg,_Z),_Z);}else{var _1Mj=E(_1Mg),_1Mk=new T(function(){var _1Ml=B(_LD(126,_1Mh.a,_1Mh.b));return new T2(0,_1Ml.a,_1Ml.b);});if(E(_1Mj)==126){var _1Mm=new T2(1,_Z,new T2(1,new T(function(){return E(E(_1Mk).a);}),new T(function(){return E(E(_1Mk).b);})));}else{var _1Mm=new T2(1,new T2(1,_1Mj,new T(function(){return E(E(_1Mk).a);})),new T(function(){return E(E(_1Mk).b);}));}var _1Mi=_1Mm;}var _1Mf=_1Mi;}var _1Md=_1Mf;}var _1Mn=_1Md;}else{var _1Mo=E(_1M7);if(!_1Mo._){var _1Mp=new T2(1,new T2(1,_1Ma,_Z),_Z);}else{var _1Mq=new T(function(){var _1Mr=B(_LD(126,_1Mo.a,_1Mo.b));return new T2(0,_1Mr.a,_1Mr.b);});if(E(_1Mb)==126){var _1Ms=new T2(1,_Z,new T2(1,new T(function(){return E(E(_1Mq).a);}),new T(function(){return E(E(_1Mq).b);})));}else{var _1Ms=new T2(1,new T2(1,_1Ma,new T(function(){return E(E(_1Mq).a);})),new T(function(){return E(E(_1Mq).b);}));}var _1Mp=_1Ms;}var _1Mn=_1Mp;}var _1Mt=B(_KL(B(_x8(_1EW,new T(function(){return B(_NV(_1Mn));})))));if(!_1Mt._){return E(_1EK);}else{if(!E(_1Mt.b)._){var _1Mu=E(_1Mt.a),_1Mv=B(_aS(_1mu,_1Mu)),_1Mw=B(_aS(_1Mn,1));if(!_1Mw._){var _1Mx=__Z;}else{var _1My=E(_1Mw.b);if(!_1My._){var _1Mz=__Z;}else{var _1MA=E(_1Mw.a),_1MB=new T(function(){var _1MC=B(_LD(44,_1My.a,_1My.b));return new T2(0,_1MC.a,_1MC.b);});if(E(_1MA)==44){var _1MD=B(_16I(_Z,new T(function(){return E(E(_1MB).a);}),new T(function(){return E(E(_1MB).b);})));}else{var _1MD=B(_16M(new T2(1,_1MA,new T(function(){return E(E(_1MB).a);})),new T(function(){return E(E(_1MB).b);})));}var _1Mz=_1MD;}var _1Mx=_1Mz;}var _1ME=B(_aS(_1Mn,2));if(!_1ME._){var _1MF=E(_1Fc);}else{var _1MG=_1ME.a,_1MH=E(_1ME.b);if(!_1MH._){var _1MI=B(_aj(_1F7,new T2(1,new T2(1,_1MG,_Z),_Z)));}else{var _1MJ=E(_1MG),_1MK=new T(function(){var _1ML=B(_LD(44,_1MH.a,_1MH.b));return new T2(0,_1ML.a,_1ML.b);});if(E(_1MJ)==44){var _1MM=B(_aj(_1F7,new T2(1,_Z,new T2(1,new T(function(){return E(E(_1MK).a);}),new T(function(){return E(E(_1MK).b);})))));}else{var _1MM=B(_aj(_1F7,new T2(1,new T2(1,_1MJ,new T(function(){return E(E(_1MK).a);})),new T(function(){return E(E(_1MK).b);}))));}var _1MI=_1MM;}var _1MF=_1MI;}return {_:0,a:E({_:0,a:E(B(_aS(_1mF,_1Mu))),b:E(B(_1gr(_1Mv.a,E(_1Mv.b),new T(function(){return B(_aS(_1oz,_1Mu));})))),c:E(_1M9.c),d:B(_aS(_1mS,_1Mu)),e:32,f:_1Mu,g:E(_1M9.g),h:_1M9.h,i:E(_1M9.i),j:E(_1M9.j),k:E(_1M9.k)}),b:E(_1Mv),c:E(_1M8.c),d:E(_1M8.d),e:E(_1Mx),f:E(_1MF),g:E(_1M8.g),h:E(_1M8.h),i:_1M8.i,j:_1M8.j,k:_1M8.k,l:_1M8.l,m:E(_1M8.m),n:_1M8.n,o:E(_1M8.o),p:E(_1M8.p),q:_1M8.q,r:E(_1M8.r),s:E(_1M8.s),t:_1M8.t,u:E(_1M8.u),v:E(_1M8.v),w:E(_1M8.w)};}else{return E(_1EL);}}});}}else{return new F(function(){return _1Lj(_);});}}else{return new F(function(){return _1Lj(_);});}};switch(E(_1Lg)){case 100:var _1MN=__app1(E(_1Gb),toJSStr(E(_1EZ)));return new F(function(){return _1Lh(_,_1EH);});break;case 114:var _1MO=B(_16X(_aB,toJSStr(E(_1EZ)),_));return new F(function(){return _1Lh(_,new T(function(){var _1MP=E(_1MO);if(!_1MP._){return E(_1EI);}else{return fromJSStr(B(_1t7(_1MP.a)));}}));});break;case 115:var _1MQ=new T(function(){var _1MR=new T(function(){var _1MS=new T(function(){var _1MT=B(_aj(_aC,_1IT));if(!_1MT._){return __Z;}else{return B(_1EE(new T2(1,_1MT.a,new T(function(){return B(_1Fk(_1EX,_1MT.b));}))));}}),_1MU=new T(function(){var _1MV=function(_1MW){var _1MX=E(_1MW);if(!_1MX._){return __Z;}else{var _1MY=E(_1MX.a);return new T2(1,_1MY.a,new T2(1,_1MY.b,new T(function(){return B(_1MV(_1MX.b));})));}},_1MZ=B(_1MV(_1IS));if(!_1MZ._){return __Z;}else{return B(_1EE(new T2(1,_1MZ.a,new T(function(){return B(_1Fk(_1EX,_1MZ.b));}))));}});return B(_1Fk(_1EY,new T2(1,_1MU,new T2(1,_1MS,_Z))));});return B(_x(B(_1EE(new T2(1,new T(function(){return B(_H(0,_1II,_Z));}),_1MR))),_1Fa));}),_1N0=__app2(E(_1Ge),toJSStr(E(_1EZ)),B(_1t7(B(_1HM(B(unAppCStr("\"",_1MQ)))))));return new F(function(){return _1Lh(_,_1EJ);});break;default:return new F(function(){return _1Lh(_,_1F0);});}},_1N1=E(_1J3);if(!_1N1._){return new F(function(){return _1Jt(_,_1ID,_1IE,_1IF,_1IG,_1IH,_1II,_1IJ,_1IK,_1IL,_1IM,_1IN,_1Jo,_1IQ,_1IR,_1IS,_1IT,_1IU,_1Jn,_1IX,_1IY,_1IZ,_1J0,_1J1,_1J2,_Z,_1J4,_1J5,_1J6,_1J7,_1J8,_1J9,_1Ja,_1Jl,_1Jk);});}else{var _1N2=E(_1N1.b);if(!_1N2._){return new F(function(){return _1Jt(_,_1ID,_1IE,_1IF,_1IG,_1IH,_1II,_1IJ,_1IK,_1IL,_1IM,_1IN,_1Jo,_1IQ,_1IR,_1IS,_1IT,_1IU,_1Jn,_1IX,_1IY,_1IZ,_1J0,_1J1,_1J2,_Z,_1J4,_1J5,_1J6,_1J7,_1J8,_1J9,_1Ja,_1Jl,_1Jk);});}else{var _1N3=E(_1N2.b);if(!_1N3._){return new F(function(){return _1Jt(_,_1ID,_1IE,_1IF,_1IG,_1IH,_1II,_1IJ,_1IK,_1IL,_1IM,_1IN,_1Jo,_1IQ,_1IR,_1IS,_1IT,_1IU,_1Jn,_1IX,_1IY,_1IZ,_1J0,_1J1,_1J2,_Z,_1J4,_1J5,_1J6,_1J7,_1J8,_1J9,_1Ja,_1Jl,_1Jk);});}else{var _1N4=_1N3.a,_1N5=E(_1N3.b);if(!_1N5._){return new F(function(){return _1Jt(_,_1ID,_1IE,_1IF,_1IG,_1IH,_1II,_1IJ,_1IK,_1IL,_1IM,_1IN,_1Jo,_1IQ,_1IR,_1IS,_1IT,_1IU,_1Jn,_1IX,_1IY,_1IZ,_1J0,_1J1,_1J2,_Z,_1J4,_1J5,_1J6,_1J7,_1J8,_1J9,_1Ja,_1Jl,_1Jk);});}else{if(!E(_1N5.b)._){var _1N6=B(_1d6(B(_qu(_1N4,0)),_1IK,new T(function(){var _1N7=B(_KL(B(_x8(_1EW,_1N1.a))));if(!_1N7._){return E(_1G1);}else{if(!E(_1N7.b)._){if(E(_1N7.a)==2){return E(_1G5);}else{return E(_1G1);}}else{return E(_1G1);}}}),_)),_1N8=E(_1N6),_1N9=_1N8.a,_1Na=new T(function(){var _1Nb=new T(function(){return B(_aj(function(_1Nc){var _1Nd=B(_wT(_3S,_1Nc,B(_KX(_1F6,_1N4))));return (_1Nd._==0)?E(_1EQ):E(_1Nd.a);},B(_aj(_1Gf,B(_1Gx(B(_1G6(_1N9,_1G2))))))));}),_1Ne=B(_KX(_1N9,_1N4)),_1Nf=B(_Z2(B(unAppCStr("e.==.m1:",_1N5.a)),{_:0,a:E(_1ID),b:E(_1IE),c:E(_1IF),d:_1IG,e:_1IH,f:_1II,g:E(B(_x(_1IJ,new T2(1,new T2(0,new T2(0,_1N2.a,_1F5),_1II),new T2(1,new T2(0,new T2(0,_1Nb,_1F5),_1II),_Z))))),h:E(_1N8.b),i:E(_1IL),j:E(_1IM),k:E(_1IN)},_1Jo,_1IQ,B(_x(B(_0(_Z,B(_1Is(_1N4,B(_9T(_1IR)))))),new T(function(){return B(_aj(_1E9,_1Ne));},1))),_1IS,_1IT,_1IU,_1Jn,_1IX,_1IY,_1IZ,_1J0,_1J1,_1J2,_Z,E(_1Ne),0,_1J6,_1Jm,_1J9,_1Ja,_1Jl,_1Jk)),_1Ng=B(_1ti(_1N4,_1Nf.a,_1Nf.b,_1Nf.c,_1Nf.d,_1Nf.e,_1Nf.f,_1Nf.g,_1Nf.h,_1Nf.i,_1Nf.j,_1Nf.k,_1Nf.l,_1Nf.m,_1Nf.n,_1Nf.o,_1Nf.p,_1Nf.q,_1Nf.r,_1Nf.s,_1Nf.t,_1Nf.u,_1Nf.v,_1Nf.w));return {_:0,a:E(_1Ng.a),b:E(_1Ng.b),c:E(_1Ng.c),d:E(_1Ng.d),e:E(_1Ng.e),f:E(_1Ng.f),g:E(_1Ng.g),h:E(_1Ng.h),i:_1Ng.i,j:_1Ng.j,k:_1Ng.k,l:_1Ng.l,m:E(_1Ng.m),n:_1Ng.n,o:E(_1Ng.o),p:E(_1Ng.p),q:_1Ng.q,r:E(_1Ng.r),s:E(_1Ng.s),t:_1Ng.t,u:E(_1Ng.u),v:E(_1Ng.v),w:E(_1Ng.w)};}),_1Nh=new T(function(){var _1Ni=E(E(_1Na).a);return new T6(0,_1Ni,_1Ni.a,_1Ni.g,_1Ni.h,_1Ni.i,_1Ni.k);}),_1Nj=B(_1bL(_1F4,new T(function(){return E(E(_1Nh).d);},1),_)),_1Nk=E(_1Nj).b,_1Nl=E(_1Iy),_1Nm=_1Nl.a,_1Nn=_1Nl.b,_1No=new T(function(){return B(_1u9(E(_1IC)));}),_1Np=new T(function(){var _1Nq=E(_1Na),_1Nr=_1Nq.b,_1Ns=_1Nq.c,_1Nt=_1Nq.d,_1Nu=_1Nq.e,_1Nv=_1Nq.f,_1Nw=_1Nq.g,_1Nx=_1Nq.h,_1Ny=_1Nq.i,_1Nz=_1Nq.j,_1NA=_1Nq.k,_1NB=_1Nq.l,_1NC=_1Nq.m,_1ND=_1Nq.n,_1NE=_1Nq.o,_1NF=_1Nq.p,_1NG=_1Nq.q,_1NH=_1Nq.r,_1NI=_1Nq.t,_1NJ=_1Nq.u,_1NK=_1Nq.v,_1NL=_1Nq.w,_1NM=E(_1Nq.s),_1NN=_1NM.a,_1NO=_1NM.b,_1NP=E(_1No),_1NQ=E(_1Nh),_1NR=_1NQ.a,_1NS=E(_1NQ.b),_1NT=_1NS.b,_1NU=E(_1NS.a),_1NV=function(_1NW,_1NX){var _1NY=E(_1NX),_1NZ=E(_1NR),_1O0=_1NZ.b,_1O1=_1NZ.c,_1O2=_1NZ.d,_1O3=_1NZ.e,_1O4=_1NZ.f,_1O5=_1NZ.g,_1O6=_1NZ.h,_1O7=_1NZ.i,_1O8=_1NZ.j,_1O9=_1NZ.k,_1Oa=E(_1NZ.a),_1Ob=_1Oa.a,_1Oc=_1Oa.b;if(_1NW<=_1NU){if(_1NU<=_1NW){var _1Od=E(_1NT);if(_1NY<=_1Od){if(_1Od<=_1NY){var _1Oe=4;}else{var _1Oe=0;}var _1Of=_1Oe;}else{var _1Of=1;}var _1Og=_1Of;}else{var _1Og=2;}var _1Oh=_1Og;}else{var _1Oh=3;}var _1Oi=function(_1Oj,_1Ok,_1Ol,_1Om,_1On,_1Oo,_1Op,_1Oq,_1Or,_1Os){switch(E(_1Oh)){case 0:if(!E(_1O1)){var _1Ot=new T2(0,_1NN,_1NO);}else{var _1Ot=new T2(0,_1NN,_1Fi);}var _1Ou=_1Ot;break;case 1:if(E(_1O1)==1){var _1Ov=new T2(0,_1NN,_1NO);}else{var _1Ov=new T2(0,_1NN,_1HP);}var _1Ou=_1Ov;break;case 2:if(E(_1O1)==2){var _1Ow=new T2(0,_1NN,_1NO);}else{var _1Ow=new T2(0,_1NN,_1F3);}var _1Ou=_1Ow;break;case 3:if(E(_1O1)==3){var _1Ox=new T2(0,_1NN,_1NO);}else{var _1Ox=new T2(0,_1NN,_1F2);}var _1Ou=_1Ox;break;default:if(E(_1O1)==4){var _1Oy=new T2(0,_1NN,_1NO);}else{var _1Oy=new T2(0,_1NN,_1HP);}var _1Ou=_1Oy;}var _1Oz=B(_1qQ(_1HP,_1Oq,_1Nu,{_:0,a:E(_1Oj),b:E(_1Ok),c:E(_1Ol),d:_1Om,e:_1On,f:_1Oo,g:E(_1Op),h:E(_1Nk),i:E(_1Oq),j:E(_1Or),k:E(_1Os)},_1Nr,_1Ns,_1Nt,_1Nu,_1Nv,_1Nw,_1Nx,_1Ny,_1Nz,_1NA,_1NB,_1NC,_1ND,_1NE,_1NF,_1NG,_1NH,_1Ou,_1NI,_1NJ,_1NK,_1NL)),_1OA=_1Oz.a,_1OB=_1Oz.b,_1OC=_1Oz.c,_1OD=_1Oz.d,_1OE=_1Oz.e,_1OF=_1Oz.f,_1OG=_1Oz.g,_1OH=_1Oz.h,_1OI=_1Oz.i,_1OJ=_1Oz.j,_1OK=_1Oz.k,_1OL=_1Oz.l,_1OM=_1Oz.m,_1ON=_1Oz.n,_1OO=_1Oz.o,_1OP=_1Oz.q,_1OQ=_1Oz.r,_1OR=_1Oz.s,_1OS=_1Oz.t,_1OT=_1Oz.u,_1OU=_1Oz.v,_1OV=_1Oz.w,_1OW=E(_1Oz.p);if(!_1OW._){return {_:0,a:E(_1OA),b:E(_1OB),c:E(_1OC),d:E(_1OD),e:E(_1OE),f:E(_1OF),g:E(_1OG),h:E(_1OH),i:_1OI,j:_1OJ,k:_1OK,l:_1OL,m:E(_1OM),n:_1ON,o:E(_1OO),p:E(_Z),q:_1OP,r:E(_1OQ),s:E(_1OR),t:_1OS,u:E(_1OT),v:E(_1OU),w:E(_1OV)};}else{var _1OX=B(_qu(_1Oq,0))-2|0,_1OY=function(_1OZ){var _1P0=E(_1OA);return {_:0,a:E({_:0,a:E(_1P0.a),b:E(_1P0.b),c:E(_1P0.c),d:_1P0.d,e:_1P0.e,f:_1P0.f,g:E(_Z),h:_1P0.h,i:E(_1P0.i),j:E(_1P0.j),k:E(_1P0.k)}),b:E(_1OB),c:E(_1OC),d:E(B(_x(B(_0(_Z,B(_1Is(B(_aj(_1Gf,_1OW)),B(_9T(_1OD)))))),new T(function(){return B(_aj(_1E4,_1OW));},1)))),e:E(_1OE),f:E(_1OF),g:E(_1OG),h:E(_1OH),i:_1OI,j:_1OJ,k:_1OK,l:_1OL,m:E(_1OM),n:_1ON,o:E(_1OO),p:E(_Z),q:_1OP,r:E(B(_x(_1OQ,new T2(1,_1OP,_Z)))),s:E(_1OR),t:_1OS,u:E(_1OT),v:E(_1OU),w:E(_1OV)};};if(_1OX>0){if(!B(_vi(B(_1DM(_1OX,_1Oq)),_1F1))){return {_:0,a:E(_1OA),b:E(_1OB),c:E(_1OC),d:E(_1OD),e:E(_1OE),f:E(_1OF),g:E(_1OG),h:E(_1OH),i:_1OI,j:_1OJ,k:_1OK,l:_1OL,m:E(_1OM),n:_1ON,o:E(_1OO),p:E(_1OW),q:_1OP,r:E(_1OQ),s:E(_1OR),t:_1OS,u:E(_1OT),v:E(_1OU),w:E(_1OV)};}else{return new F(function(){return _1OY(_);});}}else{if(!B(_vi(_1Oq,_1F1))){return {_:0,a:E(_1OA),b:E(_1OB),c:E(_1OC),d:E(_1OD),e:E(_1OE),f:E(_1OF),g:E(_1OG),h:E(_1OH),i:_1OI,j:_1OJ,k:_1OK,l:_1OL,m:E(_1OM),n:_1ON,o:E(_1OO),p:E(_1OW),q:_1OP,r:E(_1OQ),s:E(_1OR),t:_1OS,u:E(_1OT),v:E(_1OU),w:E(_1OV)};}else{return new F(function(){return _1OY(_);});}}}};if(E(_1NP)==32){var _1P1=B(_1A2(_1NW,_1NY,_1Ob,_1Oc,_1O0,_1Oh,_1O2,_1O3,_1O4,_1O5,_1O6,_1O7,_1O8,_1O9)),_1P2=E(_1P1.a),_1P3=B(_1Dn(_1P2.a,E(_1P2.b),_1P1.b,_1P1.c,_1P1.d,_1P1.e,_1P1.f,_1P1.g,_1P1.h,_1P1.i,_1P1.j,_1P1.k));return new F(function(){return _1Oi(_1P3.a,_1P3.b,_1P3.c,_1P3.d,_1P3.e,_1P3.f,_1P3.g,_1P3.i,_1P3.j,_1P3.k);});}else{var _1P4=B(_1A2(_1NW,_1NY,_1Ob,_1Oc,_1O0,_1Oh,_1O2,_1O3,_1O4,_1O5,_1O6,_1O7,_1O8,_1O9));return new F(function(){return _1Oi(_1P4.a,_1P4.b,_1P4.c,_1P4.d,_1P4.e,_1P4.f,_1P4.g,_1P4.i,_1P4.j,_1P4.k);});}},_1P5=function(_1P6,_1P7){var _1P8=E(_1NR),_1P9=_1P8.b,_1Pa=_1P8.c,_1Pb=_1P8.d,_1Pc=_1P8.e,_1Pd=_1P8.f,_1Pe=_1P8.g,_1Pf=_1P8.h,_1Pg=_1P8.i,_1Ph=_1P8.j,_1Pi=_1P8.k,_1Pj=E(_1P8.a),_1Pk=_1Pj.a,_1Pl=_1Pj.b;if(_1P6<=_1NU){if(_1NU<=_1P6){var _1Pm=E(_1NT);if(_1P7<=_1Pm){if(_1Pm<=_1P7){var _1Pn=4;}else{var _1Pn=0;}var _1Po=_1Pn;}else{var _1Po=1;}var _1Pp=_1Po;}else{var _1Pp=2;}var _1Pq=_1Pp;}else{var _1Pq=3;}var _1Pr=function(_1Ps,_1Pt,_1Pu,_1Pv,_1Pw,_1Px,_1Py,_1Pz,_1PA,_1PB){switch(E(_1Pq)){case 0:if(!E(_1Pa)){var _1PC=new T2(0,_1NN,_1NO);}else{var _1PC=new T2(0,_1NN,_1Fi);}var _1PD=_1PC;break;case 1:if(E(_1Pa)==1){var _1PE=new T2(0,_1NN,_1NO);}else{var _1PE=new T2(0,_1NN,_1HP);}var _1PD=_1PE;break;case 2:if(E(_1Pa)==2){var _1PF=new T2(0,_1NN,_1NO);}else{var _1PF=new T2(0,_1NN,_1F3);}var _1PD=_1PF;break;case 3:if(E(_1Pa)==3){var _1PG=new T2(0,_1NN,_1NO);}else{var _1PG=new T2(0,_1NN,_1F2);}var _1PD=_1PG;break;default:if(E(_1Pa)==4){var _1PH=new T2(0,_1NN,_1NO);}else{var _1PH=new T2(0,_1NN,_1HP);}var _1PD=_1PH;}var _1PI=B(_1qQ(_1HP,_1Pz,_1Nu,{_:0,a:E(_1Ps),b:E(_1Pt),c:E(_1Pu),d:_1Pv,e:_1Pw,f:_1Px,g:E(_1Py),h:E(_1Nk),i:E(_1Pz),j:E(_1PA),k:E(_1PB)},_1Nr,_1Ns,_1Nt,_1Nu,_1Nv,_1Nw,_1Nx,_1Ny,_1Nz,_1NA,_1NB,_1NC,_1ND,_1NE,_1NF,_1NG,_1NH,_1PD,_1NI,_1NJ,_1NK,_1NL)),_1PJ=_1PI.a,_1PK=_1PI.b,_1PL=_1PI.c,_1PM=_1PI.d,_1PN=_1PI.e,_1PO=_1PI.f,_1PP=_1PI.g,_1PQ=_1PI.h,_1PR=_1PI.i,_1PS=_1PI.j,_1PT=_1PI.k,_1PU=_1PI.l,_1PV=_1PI.m,_1PW=_1PI.n,_1PX=_1PI.o,_1PY=_1PI.q,_1PZ=_1PI.r,_1Q0=_1PI.s,_1Q1=_1PI.t,_1Q2=_1PI.u,_1Q3=_1PI.v,_1Q4=_1PI.w,_1Q5=E(_1PI.p);if(!_1Q5._){return {_:0,a:E(_1PJ),b:E(_1PK),c:E(_1PL),d:E(_1PM),e:E(_1PN),f:E(_1PO),g:E(_1PP),h:E(_1PQ),i:_1PR,j:_1PS,k:_1PT,l:_1PU,m:E(_1PV),n:_1PW,o:E(_1PX),p:E(_Z),q:_1PY,r:E(_1PZ),s:E(_1Q0),t:_1Q1,u:E(_1Q2),v:E(_1Q3),w:E(_1Q4)};}else{var _1Q6=B(_qu(_1Pz,0))-2|0,_1Q7=function(_1Q8){var _1Q9=E(_1PJ);return {_:0,a:E({_:0,a:E(_1Q9.a),b:E(_1Q9.b),c:E(_1Q9.c),d:_1Q9.d,e:_1Q9.e,f:_1Q9.f,g:E(_Z),h:_1Q9.h,i:E(_1Q9.i),j:E(_1Q9.j),k:E(_1Q9.k)}),b:E(_1PK),c:E(_1PL),d:E(B(_x(B(_0(_Z,B(_1Is(B(_aj(_1Gf,_1Q5)),B(_9T(_1PM)))))),new T(function(){return B(_aj(_1E4,_1Q5));},1)))),e:E(_1PN),f:E(_1PO),g:E(_1PP),h:E(_1PQ),i:_1PR,j:_1PS,k:_1PT,l:_1PU,m:E(_1PV),n:_1PW,o:E(_1PX),p:E(_Z),q:_1PY,r:E(B(_x(_1PZ,new T2(1,_1PY,_Z)))),s:E(_1Q0),t:_1Q1,u:E(_1Q2),v:E(_1Q3),w:E(_1Q4)};};if(_1Q6>0){if(!B(_vi(B(_1DM(_1Q6,_1Pz)),_1F1))){return {_:0,a:E(_1PJ),b:E(_1PK),c:E(_1PL),d:E(_1PM),e:E(_1PN),f:E(_1PO),g:E(_1PP),h:E(_1PQ),i:_1PR,j:_1PS,k:_1PT,l:_1PU,m:E(_1PV),n:_1PW,o:E(_1PX),p:E(_1Q5),q:_1PY,r:E(_1PZ),s:E(_1Q0),t:_1Q1,u:E(_1Q2),v:E(_1Q3),w:E(_1Q4)};}else{return new F(function(){return _1Q7(_);});}}else{if(!B(_vi(_1Pz,_1F1))){return {_:0,a:E(_1PJ),b:E(_1PK),c:E(_1PL),d:E(_1PM),e:E(_1PN),f:E(_1PO),g:E(_1PP),h:E(_1PQ),i:_1PR,j:_1PS,k:_1PT,l:_1PU,m:E(_1PV),n:_1PW,o:E(_1PX),p:E(_1Q5),q:_1PY,r:E(_1PZ),s:E(_1Q0),t:_1Q1,u:E(_1Q2),v:E(_1Q3),w:E(_1Q4)};}else{return new F(function(){return _1Q7(_);});}}}};if(E(_1NP)==32){var _1Qa=B(_1A2(_1P6,_1P7,_1Pk,_1Pl,_1P9,_1Pq,_1Pb,_1Pc,_1Pd,_1Pe,_1Pf,_1Pg,_1Ph,_1Pi)),_1Qb=E(_1Qa.a),_1Qc=B(_1Dn(_1Qb.a,E(_1Qb.b),_1Qa.b,_1Qa.c,_1Qa.d,_1Qa.e,_1Qa.f,_1Qa.g,_1Qa.h,_1Qa.i,_1Qa.j,_1Qa.k));return new F(function(){return _1Pr(_1Qc.a,_1Qc.b,_1Qc.c,_1Qc.d,_1Qc.e,_1Qc.f,_1Qc.g,_1Qc.i,_1Qc.j,_1Qc.k);});}else{var _1Qd=B(_1A2(_1P6,_1P7,_1Pk,_1Pl,_1P9,_1Pq,_1Pb,_1Pc,_1Pd,_1Pe,_1Pf,_1Pg,_1Ph,_1Pi));return new F(function(){return _1Pr(_1Qd.a,_1Qd.b,_1Qd.c,_1Qd.d,_1Qd.e,_1Qd.f,_1Qd.g,_1Qd.i,_1Qd.j,_1Qd.k);});}};switch(E(_1NP)){case 72:var _1Qe=E(_1NT);if(0<=(_1Qe-1|0)){return B(_1P5(_1NU,_1Qe-1|0));}else{return B(_1P5(_1NU,_1Qe));}break;case 75:if(0<=(_1NU-1|0)){return B(_1NV(_1NU-1|0,_1NT));}else{return B(_1NV(_1NU,_1NT));}break;case 77:if(E(_1IO)!=(_1NU+1|0)){return B(_1NV(_1NU+1|0,_1NT));}else{return B(_1NV(_1NU,_1NT));}break;case 80:var _1Qf=E(_1NT);if(E(_1IP)!=(_1Qf+1|0)){return B(_1P5(_1NU,_1Qf+1|0));}else{return B(_1P5(_1NU,_1Qf));}break;case 104:if(0<=(_1NU-1|0)){return B(_1NV(_1NU-1|0,_1NT));}else{return B(_1NV(_1NU,_1NT));}break;case 106:var _1Qg=E(_1NT);if(E(_1IP)!=(_1Qg+1|0)){return B(_1P5(_1NU,_1Qg+1|0));}else{return B(_1P5(_1NU,_1Qg));}break;case 107:var _1Qh=E(_1NT);if(0<=(_1Qh-1|0)){return B(_1P5(_1NU,_1Qh-1|0));}else{return B(_1P5(_1NU,_1Qh));}break;case 108:if(E(_1IO)!=(_1NU+1|0)){return B(_1NV(_1NU+1|0,_1NT));}else{return B(_1NV(_1NU,_1NT));}break;default:return B(_1NV(_1NU,_1NT));}}),_1Qi=B(_1dW(_1Nm,_1Nn,_1Iz,_1IA,_1IB,_1Np,_)),_1Qj=_1Qi,_1Qk=E(_1No),_1Ql=function(_,_1Qm){var _1Qn=function(_1Qo){var _1Qp=B(_1Ez(_1HK,B(_cr(_1Qm)),_)),_1Qq=E(_1Qj),_1Qr=_1Qq.d,_1Qs=_1Qq.e,_1Qt=_1Qq.f,_1Qu=_1Qq.g,_1Qv=_1Qq.i,_1Qw=_1Qq.j,_1Qx=_1Qq.k,_1Qy=_1Qq.l,_1Qz=_1Qq.m,_1QA=_1Qq.n,_1QB=_1Qq.o,_1QC=_1Qq.p,_1QD=_1Qq.q,_1QE=_1Qq.r,_1QF=_1Qq.t,_1QG=_1Qq.u,_1QH=_1Qq.w,_1QI=E(_1Qq.v),_1QJ=_1QI.a,_1QK=_1QI.d,_1QL=_1QI.e,_1QM=_1QI.f,_1QN=_1QI.g,_1QO=_1QI.h,_1QP=_1QI.i,_1QQ=E(_1Qq.a),_1QR=_1QQ.c,_1QS=_1QQ.f,_1QT=_1QQ.g,_1QU=_1QQ.h,_1QV=E(_1Qq.h),_1QW=E(_1Qq.s),_1QX=function(_1QY){var _1QZ=function(_1R0){if(_1R0!=E(_1EU)){var _1R1=B(_aS(_1mu,_1R0)),_1R2=_1R1.a,_1R3=E(_1R1.b),_1R4=B(_1gr(_1R2,_1R3,new T(function(){return B(_aS(_1oz,_1R0));})));return new F(function(){return _1Ix(_1Nl,_1Iz,_1IA,_1IB,_1ET,B(_aS(_1mF,_1R0)),_1R4,_1QR,B(_aS(_1mS,_1R0)),32,_1R0,_1QT,_1QU,B(_x(_1QQ.i,new T2(1,_1ES,new T(function(){return B(_H(0,_1QS,_Z));})))),B(_1Ed(_1ER,_1R4)),_B3,_1R2,_1R3,_Z,_1Qr,_1Qs,_1Qt,_1Qu,_1QV.a,_1QV.b,_1Qv,_1Qw,_1Qx, -1,_1Qz,_1QA,_1QB,_1QC,_1QD,_1QE,_1QW.a,_1QW.b,_1QF,_1QG,_B3,_B3,_B3,_1QK,_1QL,_1QM,_1QN,_1QO,_1QP,_1QH,_);});}else{var _1R5=__app1(E(_rj),_1Nn),_1R6=B(A2(_rk,_1Nm,_)),_1R7=B(A(_qP,[_1Nm,_n4,_1EN,_1EP,_1EO,_])),_1R8=B(A(_qP,[_1Nm,_n4,_1EN,_1EM,_1Fj,_])),_1R9=B(A(_qP,[_1Nm,_n4,_1Fi,_1Fh,_1Fg,_]));return new T(function(){return {_:0,a:E({_:0,a:E(_1mw),b:E(_1Ff),c:E(_1QR),d:E(_1Fd),e:32,f:0,g:E(_1QT),h:_1QU,i:E(_Z),j:E(_1QQ.j),k:E(_B3)}),b:E(_1mh),c:E(_1Qq.c),d:E(_1Qr),e:E(_1Qs),f:E(_1Qt),g:E(_1Qu),h:E(_1QV),i:_1Qv,j:_1Qw,k:_1Qx,l:_1Qy,m:E(_1Qz),n:_1QA,o:E(_1QB),p:E(_1QC),q:_1QD,r:E(_1QE),s:E(_1QW),t:_1QF,u:E(_1QG),v:E({_:0,a:E(_1QJ),b:E(_B4),c:E(_B3),d:E(_1QK),e:E(_1QL),f:E(_1QM),g:E(_1QN),h:E(_1QO),i:E(_1QP)}),w:E(_1QH)};});}};if(_1Qy>=0){return new F(function(){return _1QZ(_1Qy);});}else{return new F(function(){return _1QZ(_1QS+1|0);});}};if(!E(_1QJ)){if(E(_1Qk)==110){return new F(function(){return _1QX(_);});}else{return _1Qq;}}else{return new F(function(){return _1QX(_);});}};if(E(_1Qk)==114){if(!B(_ae(_1Qm,_1EV))){var _1Ra=E(_1Qm);if(!_1Ra._){return _1Qj;}else{var _1Rb=_1Ra.b;return new T(function(){var _1Rc=E(_1Qj),_1Rd=E(_1Rc.a),_1Re=E(_1Ra.a),_1Rf=E(_1Re);if(_1Rf==34){var _1Rg=B(_YC(_1Re,_1Rb));if(!_1Rg._){var _1Rh=E(_1Gd);}else{var _1Ri=E(_1Rg.b);if(!_1Ri._){var _1Rj=E(_1Fb);}else{var _1Rk=_1Ri.a,_1Rl=E(_1Ri.b);if(!_1Rl._){var _1Rm=new T2(1,new T2(1,_1Rk,_Z),_Z);}else{var _1Rn=E(_1Rk),_1Ro=new T(function(){var _1Rp=B(_LD(126,_1Rl.a,_1Rl.b));return new T2(0,_1Rp.a,_1Rp.b);});if(E(_1Rn)==126){var _1Rq=new T2(1,_Z,new T2(1,new T(function(){return E(E(_1Ro).a);}),new T(function(){return E(E(_1Ro).b);})));}else{var _1Rq=new T2(1,new T2(1,_1Rn,new T(function(){return E(E(_1Ro).a);})),new T(function(){return E(E(_1Ro).b);}));}var _1Rm=_1Rq;}var _1Rj=_1Rm;}var _1Rh=_1Rj;}var _1Rr=_1Rh;}else{var _1Rs=E(_1Rb);if(!_1Rs._){var _1Rt=new T2(1,new T2(1,_1Re,_Z),_Z);}else{var _1Ru=new T(function(){var _1Rv=B(_LD(126,_1Rs.a,_1Rs.b));return new T2(0,_1Rv.a,_1Rv.b);});if(E(_1Rf)==126){var _1Rw=new T2(1,_Z,new T2(1,new T(function(){return E(E(_1Ru).a);}),new T(function(){return E(E(_1Ru).b);})));}else{var _1Rw=new T2(1,new T2(1,_1Re,new T(function(){return E(E(_1Ru).a);})),new T(function(){return E(E(_1Ru).b);}));}var _1Rt=_1Rw;}var _1Rr=_1Rt;}var _1Rx=B(_KL(B(_x8(_1EW,new T(function(){return B(_NV(_1Rr));})))));if(!_1Rx._){return E(_1EK);}else{if(!E(_1Rx.b)._){var _1Ry=E(_1Rx.a),_1Rz=B(_aS(_1mu,_1Ry)),_1RA=B(_aS(_1Rr,1));if(!_1RA._){var _1RB=__Z;}else{var _1RC=E(_1RA.b);if(!_1RC._){var _1RD=__Z;}else{var _1RE=E(_1RA.a),_1RF=new T(function(){var _1RG=B(_LD(44,_1RC.a,_1RC.b));return new T2(0,_1RG.a,_1RG.b);});if(E(_1RE)==44){var _1RH=B(_16I(_Z,new T(function(){return E(E(_1RF).a);}),new T(function(){return E(E(_1RF).b);})));}else{var _1RH=B(_16M(new T2(1,_1RE,new T(function(){return E(E(_1RF).a);})),new T(function(){return E(E(_1RF).b);})));}var _1RD=_1RH;}var _1RB=_1RD;}var _1RI=B(_aS(_1Rr,2));if(!_1RI._){var _1RJ=E(_1Fc);}else{var _1RK=_1RI.a,_1RL=E(_1RI.b);if(!_1RL._){var _1RM=B(_aj(_1F7,new T2(1,new T2(1,_1RK,_Z),_Z)));}else{var _1RN=E(_1RK),_1RO=new T(function(){var _1RP=B(_LD(44,_1RL.a,_1RL.b));return new T2(0,_1RP.a,_1RP.b);});if(E(_1RN)==44){var _1RQ=B(_aj(_1F7,new T2(1,_Z,new T2(1,new T(function(){return E(E(_1RO).a);}),new T(function(){return E(E(_1RO).b);})))));}else{var _1RQ=B(_aj(_1F7,new T2(1,new T2(1,_1RN,new T(function(){return E(E(_1RO).a);})),new T(function(){return E(E(_1RO).b);}))));}var _1RM=_1RQ;}var _1RJ=_1RM;}return {_:0,a:E({_:0,a:E(B(_aS(_1mF,_1Ry))),b:E(B(_1gr(_1Rz.a,E(_1Rz.b),new T(function(){return B(_aS(_1oz,_1Ry));})))),c:E(_1Rd.c),d:B(_aS(_1mS,_1Ry)),e:32,f:_1Ry,g:E(_1Rd.g),h:_1Rd.h,i:E(_1Rd.i),j:E(_1Rd.j),k:E(_1Rd.k)}),b:E(_1Rz),c:E(_1Rc.c),d:E(_1Rc.d),e:E(_1RB),f:E(_1RJ),g:E(_1Rc.g),h:E(_1Rc.h),i:_1Rc.i,j:_1Rc.j,k:_1Rc.k,l:_1Rc.l,m:E(_1Rc.m),n:_1Rc.n,o:E(_1Rc.o),p:E(_1Rc.p),q:_1Rc.q,r:E(_1Rc.r),s:E(_1Rc.s),t:_1Rc.t,u:E(_1Rc.u),v:E(_1Rc.v),w:E(_1Rc.w)};}else{return E(_1EL);}}});}}else{return new F(function(){return _1Qn(_);});}}else{return new F(function(){return _1Qn(_);});}};switch(E(_1Qk)){case 100:var _1RR=__app1(E(_1Gb),toJSStr(E(_1EZ)));return new F(function(){return _1Ql(_,_1EH);});break;case 114:var _1RS=B(_16X(_aB,toJSStr(E(_1EZ)),_));return new F(function(){return _1Ql(_,new T(function(){var _1RT=E(_1RS);if(!_1RT._){return E(_1EI);}else{return fromJSStr(B(_1t7(_1RT.a)));}}));});break;case 115:var _1RU=new T(function(){var _1RV=new T(function(){var _1RW=new T(function(){var _1RX=B(_aj(_aC,_1IT));if(!_1RX._){return __Z;}else{return B(_1EE(new T2(1,_1RX.a,new T(function(){return B(_1Fk(_1EX,_1RX.b));}))));}}),_1RY=new T(function(){var _1RZ=function(_1S0){var _1S1=E(_1S0);if(!_1S1._){return __Z;}else{var _1S2=E(_1S1.a);return new T2(1,_1S2.a,new T2(1,_1S2.b,new T(function(){return B(_1RZ(_1S1.b));})));}},_1S3=B(_1RZ(_1IS));if(!_1S3._){return __Z;}else{return B(_1EE(new T2(1,_1S3.a,new T(function(){return B(_1Fk(_1EX,_1S3.b));}))));}});return B(_1Fk(_1EY,new T2(1,_1RY,new T2(1,_1RW,_Z))));});return B(_x(B(_1EE(new T2(1,new T(function(){return B(_H(0,_1II,_Z));}),_1RV))),_1Fa));}),_1S4=__app2(E(_1Ge),toJSStr(E(_1EZ)),B(_1t7(B(_1HM(B(unAppCStr("\"",_1RU)))))));return new F(function(){return _1Ql(_,_1EJ);});break;default:return new F(function(){return _1Ql(_,_1F0);});}}else{return new F(function(){return _1Jt(_,_1ID,_1IE,_1IF,_1IG,_1IH,_1II,_1IJ,_1IK,_1IL,_1IM,_1IN,_1Jo,_1IQ,_1IR,_1IS,_1IT,_1IU,_1Jn,_1IX,_1IY,_1IZ,_1J0,_1J1,_1J2,_Z,_1J4,_1J5,_1J6,_1J7,_1J8,_1J9,_1Ja,_1Jl,_1Jk);});}}}}}}}else{if(!E(_1Jh)){return {_:0,a:E(_1Jp),b:E(_1Jo),c:E(_1IQ),d:E(_1IR),e:E(_1IS),f:E(_1IT),g:E(_1IU),h:E(_1Jn),i:_1IX,j:_1IY,k:_1IZ,l:_1J0,m:E(_1J1),n:_1J2,o:E(_1J3),p:E(_1J4),q:_1J5,r:E(_1J6),s:E(_1Jm),t:_1J9,u:E(_1Ja),v:E({_:0,a:E(_1Jb),b:E(_B3),c:E(_1Jd),d:E(_B3),e:E(_1Jf),f:E(_B3),g:E(_B3),h:E(_1Ji),i:E(_1Jj)}),w:E(_1Jk)};}else{var _1S5=E(_1Iy),_1S6=new T(function(){var _1S7=new T(function(){var _1S8=B(_1tb(_1J1));return new T2(0,_1S8.a,_1S8.b);}),_1S9=new T(function(){return B(_qu(E(_1S7).a,0))-1|0;}),_1Sa=function(_1Sb){var _1Sc=E(_1Sb);switch(_1Sc){case  -2:return E(_1Jq);case  -1:return {_:0,a:E(_1Jp),b:E(_1Jo),c:E(B(_1lZ(_Z,new T(function(){return B(_aS(E(_1S7).b,_1J2));})))),d:E(_1IR),e:E(_1IS),f:E(_1IT),g:E(_1IU),h:E(_1Jn),i:_1IX,j:_1IY,k:_1IZ,l:_1J0,m:E(_1J1),n:_1J2,o:E(_1J3),p:E(_1J4),q:_1J5,r:E(_1J6),s:E(_1Jm),t:_1J9,u:E(_1Ja),v:E({_:0,a:E(_1Jb),b:E(_B3),c:E(_B4),d:E(_B3),e:E(_1Jf),f:E(_B3),g:E(_B3),h:E(_1Ji),i:E(_1Jj)}),w:E(_1Jk)};default:return {_:0,a:E(_1Jp),b:E(_1Jo),c:E(_1IQ),d:E(_1IR),e:E(_1IS),f:E(_1IT),g:E(_1IU),h:E(_1Jn),i:_1IX,j:_1IY,k:_1IZ,l:_1J0,m:E(_1J1),n:_1Sc,o:E(_1J3),p:E(_1J4),q:_1J5,r:E(_1J6),s:E(_1Jm),t:_1J9,u:E(_1Ja),v:E(_1Jl),w:E(_1Jk)};}};switch(E(B(_1u9(E(_1IC))))){case 32:return {_:0,a:E(_1Jp),b:E(_1Jo),c:E(B(_1lZ(_Z,new T(function(){return B(_aS(E(_1S7).b,_1J2));})))),d:E(_1IR),e:E(_1IS),f:E(_1IT),g:E(_1IU),h:E(_1Jn),i:_1IX,j:_1IY,k:_1IZ,l:_1J0,m:E(_1J1),n:_1J2,o:E(_1J3),p:E(_1J4),q:_1J5,r:E(_1J6),s:E(_1Jm),t:_1J9,u:E(_1Ja),v:E({_:0,a:E(_1Jb),b:E(_B3),c:E(_B4),d:E(_B3),e:E(_1Jf),f:E(_B3),g:E(_B3),h:E(_1Ji),i:E(_1Jj)}),w:E(_1Jk)};break;case 72:var _1Sd=E(_1J2);if(!_1Sd){return B(_1Sa(E(_1S9)));}else{return B(_1Sa(_1Sd-1|0));}break;case 75:if(_1J2!=E(_1S9)){return B(_1Sa(_1J2+1|0));}else{return {_:0,a:E(_1Jp),b:E(_1Jo),c:E(_1IQ),d:E(_1IR),e:E(_1IS),f:E(_1IT),g:E(_1IU),h:E(_1Jn),i:_1IX,j:_1IY,k:_1IZ,l:_1J0,m:E(_1J1),n:0,o:E(_1J3),p:E(_1J4),q:_1J5,r:E(_1J6),s:E(_1Jm),t:_1J9,u:E(_1Ja),v:E(_1Jl),w:E(_1Jk)};}break;case 77:var _1Se=E(_1J2);if(!_1Se){return B(_1Sa(E(_1S9)));}else{return B(_1Sa(_1Se-1|0));}break;case 80:if(_1J2!=E(_1S9)){return B(_1Sa(_1J2+1|0));}else{return {_:0,a:E(_1Jp),b:E(_1Jo),c:E(_1IQ),d:E(_1IR),e:E(_1IS),f:E(_1IT),g:E(_1IU),h:E(_1Jn),i:_1IX,j:_1IY,k:_1IZ,l:_1J0,m:E(_1J1),n:0,o:E(_1J3),p:E(_1J4),q:_1J5,r:E(_1J6),s:E(_1Jm),t:_1J9,u:E(_1Ja),v:E(_1Jl),w:E(_1Jk)};}break;case 104:if(_1J2!=E(_1S9)){return B(_1Sa(_1J2+1|0));}else{return {_:0,a:E(_1Jp),b:E(_1Jo),c:E(_1IQ),d:E(_1IR),e:E(_1IS),f:E(_1IT),g:E(_1IU),h:E(_1Jn),i:_1IX,j:_1IY,k:_1IZ,l:_1J0,m:E(_1J1),n:0,o:E(_1J3),p:E(_1J4),q:_1J5,r:E(_1J6),s:E(_1Jm),t:_1J9,u:E(_1Ja),v:E(_1Jl),w:E(_1Jk)};}break;case 106:if(_1J2!=E(_1S9)){return B(_1Sa(_1J2+1|0));}else{return {_:0,a:E(_1Jp),b:E(_1Jo),c:E(_1IQ),d:E(_1IR),e:E(_1IS),f:E(_1IT),g:E(_1IU),h:E(_1Jn),i:_1IX,j:_1IY,k:_1IZ,l:_1J0,m:E(_1J1),n:0,o:E(_1J3),p:E(_1J4),q:_1J5,r:E(_1J6),s:E(_1Jm),t:_1J9,u:E(_1Ja),v:E(_1Jl),w:E(_1Jk)};}break;case 107:var _1Sf=E(_1J2);if(!_1Sf){return B(_1Sa(E(_1S9)));}else{return B(_1Sa(_1Sf-1|0));}break;case 108:var _1Sg=E(_1J2);if(!_1Sg){return B(_1Sa(E(_1S9)));}else{return B(_1Sa(_1Sg-1|0));}break;default:return E(_1Jq);}});return new F(function(){return _1dW(_1S5.a,_1S5.b,_1Iz,_1IA,_1IB,_1S6,_);});}}};if(!E(_1Jd)){return new F(function(){return _1Jr(_);});}else{if(!E(_1Je)){return new F(function(){return _15x(_1Iy,_1Iz,_1IA,_1IB,_1Jp,_1IO,_1IP,_1IQ,_1IR,_1IS,_1IT,_1IU,_1IV,_1IW,_1IX,_1IY,_1IZ,_1J0,_1J1,_1J2,_1J3,_1J4,_1J5,_1J6,_1Jm,_1J9,_1Ja,_1Jb,_B3,_B3,_1Jf,_B4,_1Jh,_1Ji,_1Jj,_1Jk,_);});}else{return new F(function(){return _1Jr(_);});}}}else{return _1Jq;}}else{return _1Jq;}},_1Sh=function(_1Si,_1Sj,_1Sk){var _1Sl=E(_1Sk);if(!_1Sl._){return 0;}else{var _1Sm=_1Sl.b,_1Sn=E(_1Sl.a),_1So=_1Sn.a,_1Sp=_1Sn.b;return (_1Si<=_1So)?1+B(_1Sh(_1Si,_1Sj,_1Sm))|0:(_1Si>=_1So+_1Sn.c)?1+B(_1Sh(_1Si,_1Sj,_1Sm))|0:(_1Sj<=_1Sp)?1+B(_1Sh(_1Si,_1Sj,_1Sm))|0:(_1Sj>=_1Sp+_1Sn.d)?1+B(_1Sh(_1Si,_1Sj,_1Sm))|0:1;}},_1Sq=function(_1Sr,_1Ss,_1St){var _1Su=E(_1St);if(!_1Su._){return 0;}else{var _1Sv=_1Su.b,_1Sw=E(_1Su.a),_1Sx=_1Sw.a,_1Sy=_1Sw.b;if(_1Sr<=_1Sx){return 1+B(_1Sq(_1Sr,_1Ss,_1Sv))|0;}else{if(_1Sr>=_1Sx+_1Sw.c){return 1+B(_1Sq(_1Sr,_1Ss,_1Sv))|0;}else{var _1Sz=E(_1Ss);return (_1Sz<=_1Sy)?1+B(_1Sh(_1Sr,_1Sz,_1Sv))|0:(_1Sz>=_1Sy+_1Sw.d)?1+B(_1Sh(_1Sr,_1Sz,_1Sv))|0:1;}}}},_1SA=function(_1SB,_1SC,_1SD){var _1SE=E(_1SD);if(!_1SE._){return 0;}else{var _1SF=_1SE.b,_1SG=E(_1SE.a),_1SH=_1SG.a,_1SI=_1SG.b,_1SJ=E(_1SB);if(_1SJ<=_1SH){return 1+B(_1Sq(_1SJ,_1SC,_1SF))|0;}else{if(_1SJ>=_1SH+_1SG.c){return 1+B(_1Sq(_1SJ,_1SC,_1SF))|0;}else{var _1SK=E(_1SC);return (_1SK<=_1SI)?1+B(_1Sh(_1SJ,_1SK,_1SF))|0:(_1SK>=_1SI+_1SG.d)?1+B(_1Sh(_1SJ,_1SK,_1SF))|0:1;}}}},_1SL=function(_1SM,_1SN){return new T2(0,new T(function(){return new T4(0,0,100,100,E(_1SN)-100);}),new T2(1,new T(function(){return new T4(0,0,E(_1SN)-100,E(_1SM),100);}),new T2(1,new T(function(){return new T4(0,0,0,E(_1SM),100);}),new T2(1,new T(function(){return new T4(0,E(_1SM)-100,100,100,E(_1SN)-100);}),new T2(1,new T(function(){return new T4(0,100,100,E(_1SM)-200,E(_1SN)-200);}),_Z)))));},_1SO=32,_1SP=76,_1SQ=75,_1SR=74,_1SS=72,_1ST=64,_1SU=function(_1SV,_1SW,_1SX,_1SY,_1SZ){var _1T0=new T(function(){var _1T1=E(_1SW),_1T2=E(_1T1.a),_1T3=_1T2.a,_1T4=_1T2.b,_1T5=B(_1SL(_1T3,_1T4)),_1T6=new T(function(){var _1T7=E(_1T1.b);return new T2(0,new T(function(){return B(_k9(_1T3,_1T7.a));}),new T(function(){return B(_k9(_1T4,_1T7.b));}));});switch(B(_1SA(new T(function(){return E(_1SY)*E(E(_1T6).a);},1),new T(function(){return E(_1SZ)*E(E(_1T6).b);},1),new T2(1,_1T5.a,_1T5.b)))){case 1:return E(_1SS);break;case 2:return E(_1SR);break;case 3:return E(_1SQ);break;case 4:return E(_1SP);break;case 5:return E(_1SO);break;default:return E(_1ST);}});return function(_1T8,_){var _1T9=E(E(_1SW).a),_1Ta=E(_1T8),_1Tb=E(_1Ta.a),_1Tc=E(_1Ta.b),_1Td=E(_1Ta.h),_1Te=E(_1Ta.s),_1Tf=E(_1Ta.v);return new F(function(){return _1Ix(_1SV,_1T9.a,_1T9.b,_1SX,_1T0,_1Tb.a,_1Tb.b,_1Tb.c,_1Tb.d,_1Tb.e,_1Tb.f,_1Tb.g,_1Tb.h,_1Tb.i,_1Tb.j,_1Tb.k,_1Tc.a,_1Tc.b,_1Ta.c,_1Ta.d,_1Ta.e,_1Ta.f,_1Ta.g,_1Td.a,_1Td.b,_1Ta.i,_1Ta.j,_1Ta.k,_1Ta.l,_1Ta.m,_1Ta.n,_1Ta.o,_1Ta.p,_1Ta.q,_1Ta.r,_1Te.a,_1Te.b,_1Ta.t,_1Ta.u,_1Tf.a,_1Tf.b,_1Tf.c,_1Tf.d,_1Tf.e,_1Tf.f,_1Tf.g,_1Tf.h,_1Tf.i,_1Ta.w,_);});};},_1Tg=function(_1Th){return E(E(_1Th).a);},_1Ti=function(_1Tj){return E(E(_1Tj).a);},_1Tk=new T1(1,_B3),_1Tl="false",_1Tm=new T1(1,_B4),_1Tn="true",_1To=function(_1Tp){var _1Tq=strEq(_1Tp,E(_1Tn));if(!E(_1Tq)){var _1Tr=strEq(_1Tp,E(_1Tl));return (E(_1Tr)==0)?__Z:E(_1Tk);}else{return E(_1Tm);}},_1Ts=2,_1Tt="paused",_1Tu="ended",_1Tv=function(_1Tw){return E(E(_1Tw).b);},_1Tx=function(_1Ty,_1Tz){var _1TA=function(_){var _1TB=E(_1Tz),_1TC=E(_m1),_1TD=__app2(_1TC,_1TB,E(_1Tu)),_1TE=String(_1TD),_1TF=function(_1TG){var _1TH=__app2(_1TC,_1TB,E(_1Tt));return new T(function(){var _1TI=String(_1TH),_1TJ=B(_1To(_1TI));if(!_1TJ._){return 0;}else{if(!E(_1TJ.a)){return 0;}else{return 1;}}});},_1TK=B(_1To(_1TE));if(!_1TK._){return new F(function(){return _1TF(_);});}else{if(!E(_1TK.a)){return new F(function(){return _1TF(_);});}else{return _1Ts;}}};return new F(function(){return A2(_1Tv,_1Ty,_1TA);});},_1TL="duration",_1TM=new T(function(){return eval("(function(e,t) {e.currentTime = t;})");}),_1TN=function(_1TO,_1TP,_1TQ){var _1TR=new T(function(){var _1TS=E(_1TQ);switch(_1TS._){case 0:return function(_){var _1TT=__app2(E(_1TM),E(_1TP),0);return new F(function(){return _kG(_);});};break;case 1:return function(_){var _1TU=E(_1TP),_1TV=__app2(E(_m1),_1TU,E(_1TL)),_1TW=String(_1TV),_1TX=Number(_1TW),_1TY=isDoubleNaN(_1TX);if(!E(_1TY)){var _1TZ=__app2(E(_1TM),_1TU,_1TX);return new F(function(){return _kG(_);});}else{var _1U0=__app2(E(_1TM),_1TU,0);return new F(function(){return _kG(_);});}};break;default:return function(_){var _1U1=__app2(E(_1TM),E(_1TP),E(_1TS.a));return new F(function(){return _kG(_);});};}});return new F(function(){return A2(_1Tv,_1TO,_1TR);});},_1U2=function(_1U3){return E(E(_1U3).c);},_1U4=function(_1U5){return E(E(_1U5).b);},_1U6=__Z,_1U7=new T(function(){return eval("(function(x){x.play();})");}),_1U8=function(_1U9){return E(E(_1U9).b);},_1Ua=function(_1Ub,_1Uc){var _1Ud=new T(function(){return B(_1TN(_1Ub,_1Uc,_1U6));}),_1Ue=B(_1Ti(_1Ub)),_1Uf=new T(function(){return B(A2(_1U8,B(_1Tg(_1Ue)),_kF));}),_1Ug=new T(function(){var _1Uh=function(_){var _1Ui=__app1(E(_1U7),E(_1Uc));return new F(function(){return _kG(_);});};return B(A2(_1Tv,_1Ub,_1Uh));}),_1Uj=function(_1Uk){return new F(function(){return A3(_1U2,_1Ue,new T(function(){if(E(_1Uk)==2){return E(_1Ud);}else{return E(_1Uf);}}),_1Ug);});};return new F(function(){return A3(_1U4,_1Ue,new T(function(){return B(_1Tx(_1Ub,_1Uc));}),_1Uj);});},_1Ul=0,_1Um=2,_1Un=2,_1Uo=1,_1Up=0,_1Uq=function(_1Ur){return E(E(_1Ur).d);},_1Us=function(_1Ut,_1Uu){var _1Uv=E(_1Ut),_1Uw=new T(function(){return B(A3(_wL,_vs,new T2(1,function(_1Ux){return new F(function(){return _H(0,E(_1Uv.a),_1Ux);});},new T2(1,function(_1Uy){return new F(function(){return _H(0,E(_1Uv.b),_1Uy);});},_Z)),new T2(1,_F,_1Uu)));});return new T2(1,_G,_1Uw);},_1Uz=function(_1UA,_){return new F(function(){return _1Ez(_1HK,B(_2C(_1Us,B(_aj(_1Uq,_1UA)),_Z)),_);});},_1UB=new T(function(){return eval("document");}),_1UC=new T(function(){return eval("(function(id){return document.getElementById(id);})");}),_1UD=new T(function(){return eval("(function(e){return e.getContext(\'2d\');})");}),_1UE=new T(function(){return eval("(function(e){return !!e.getContext;})");}),_1UF=function(_1UG,_1UH){return new F(function(){return A2(_1Tv,_1UG,function(_){var _1UI=E(_1UH),_1UJ=__app1(E(_1UE),_1UI);if(!_1UJ){return _2U;}else{var _1UK=__app1(E(_1UD),_1UI);return new T1(1,new T2(0,_1UK,_1UI));}});});},_1UL=1,_1UM=new T(function(){var _1UN=E(_1mS);if(!_1UN._){return E(_ri);}else{return {_:0,a:E(_1mw),b:E(B(_1gr(_1mg,5,_1nm))),c:E(_1UL),d:E(_1UN.a),e:32,f:0,g:E(_Z),h:0,i:E(_Z),j:E(_B3),k:E(_B3)};}}),_1UO=0,_1UP=4,_1UQ=new T2(0,_1UP,_1UO),_1UR=new T2(0,_1UO,_1UO),_1US={_:0,a:E(_B3),b:E(_B3),c:E(_B4),d:E(_B3),e:E(_B3),f:E(_B3),g:E(_B3),h:E(_B3),i:E(_B3)},_1UT=new T(function(){return {_:0,a:E(_1UM),b:E(_1mh),c:E(_1hC),d:E(_Z),e:E(_Z),f:E(_Z),g:E(_Z),h:E(_1UR),i:0,j:0,k:0,l: -1,m:E(_Z),n:0,o:E(_Z),p:E(_Z),q:0,r:E(_Z),s:E(_1UQ),t:0,u:E(_Z),v:E(_1US),w:E(_Z)};}),_1UU=new T(function(){return B(unCStr("Pattern match failure in do expression at Main.hs:49:3-9"));}),_1UV=new T6(0,_2U,_2V,_Z,_1UU,_2U,_2U),_1UW=new T(function(){return B(_2S(_1UV));}),_1UX=new T(function(){return B(unCStr("Pattern match failure in do expression at Main.hs:50:3-8"));}),_1UY=new T6(0,_2U,_2V,_Z,_1UX,_2U,_2U),_1UZ=new T(function(){return B(_2S(_1UY));}),_1V0=new T1(1,50),_1V1=new T1(0,100),_1V2=new T(function(){return B(unAppCStr("[]",_Z));}),_1V3=function(_1V4){return E(E(_1V4).a);},_1V5=function(_1V6){return E(E(_1V6).b);},_1V7=function(_1V8){return E(E(_1V8).a);},_1V9=function(_){return new F(function(){return nMV(_2U);});},_1Va=new T(function(){return B(_3d(_1V9));}),_1Vb=function(_1Vc){return E(E(_1Vc).b);},_1Vd=new T(function(){return eval("(function(e,name,f){e.addEventListener(name,f,false);return [f];})");}),_1Ve=function(_1Vf){return E(E(_1Vf).d);},_1Vg=function(_1Vh,_1Vi,_1Vj,_1Vk,_1Vl,_1Vm){var _1Vn=B(_1V3(_1Vh)),_1Vo=B(_1Ti(_1Vn)),_1Vp=new T(function(){return B(_1Tv(_1Vn));}),_1Vq=new T(function(){return B(_1Ve(_1Vo));}),_1Vr=new T(function(){return B(A1(_1Vi,_1Vk));}),_1Vs=new T(function(){return B(A2(_1V7,_1Vj,_1Vl));}),_1Vt=function(_1Vu){return new F(function(){return A1(_1Vq,new T3(0,_1Vs,_1Vr,_1Vu));});},_1Vv=function(_1Vw){var _1Vx=new T(function(){var _1Vy=new T(function(){var _1Vz=__createJSFunc(2,function(_1VA,_){var _1VB=B(A2(E(_1Vw),_1VA,_));return _3h;}),_1VC=_1Vz;return function(_){return new F(function(){return __app3(E(_1Vd),E(_1Vr),E(_1Vs),_1VC);});};});return B(A1(_1Vp,_1Vy));});return new F(function(){return A3(_1U4,_1Vo,_1Vx,_1Vt);});},_1VD=new T(function(){var _1VE=new T(function(){return B(_1Tv(_1Vn));}),_1VF=function(_1VG){var _1VH=new T(function(){return B(A1(_1VE,function(_){var _=wMV(E(_1Va),new T1(1,_1VG));return new F(function(){return A(_1V5,[_1Vj,_1Vl,_1VG,_]);});}));});return new F(function(){return A3(_1U4,_1Vo,_1VH,_1Vm);});};return B(A2(_1Vb,_1Vh,_1VF));});return new F(function(){return A3(_1U4,_1Vo,_1VD,_1Vv);});},_1VI=new T(function(){return eval("(function(e){if(e){e.preventDefault();}})");}),_1VJ=function(_){var _1VK=rMV(E(_1Va)),_1VL=E(_1VK);if(!_1VL._){var _1VM=__app1(E(_1VI),E(_3h));return new F(function(){return _kG(_);});}else{var _1VN=__app1(E(_1VI),E(_1VL.a));return new F(function(){return _kG(_);});}},_1VO=function(_1VP){return new T1(1,E(_1VP));},_1VQ=function(_1VR,_1VS){return new F(function(){return A2(_1Ve,B(_1Ti(_1VR)),new T1(1,_1VS));});},_1VT=new T2(0,_61,_1VQ),_1VU="auto",_1VV="metadata",_1VW="none",_1VX=new T(function(){return new T1(0,"preload");}),_1VY=new T(function(){return eval("(function(t){return document.createElement(t);})");}),_1VZ=function(_){return new F(function(){return __app1(E(_1VY),"source");});},_1W0=new T(function(){return new T1(0,"src");}),_1W1="audio/wav",_1W2="audio/ogg",_1W3="audio/mpeg",_1W4=new T(function(){return new T1(0,"type");}),_1W5=new T(function(){return eval("(function(c,p){p.appendChild(c);})");}),_1W6=function(_1W7){return E(E(_1W7).a);},_1W8=new T(function(){return eval("(function(e,p,v){e.setAttribute(p, v);})");}),_1W9=new T(function(){return eval("(function(e,p,v){e.style[p] = v;})");}),_1Wa=function(_1Wb,_1Wc,_1Wd,_1We){var _1Wf=new T(function(){return B(A2(_1W6,_1Wb,_1Wd));}),_1Wg=function(_1Wh,_){var _1Wi=E(_1Wh);if(!_1Wi._){return _kF;}else{var _1Wj=E(_1Wf),_1Wk=E(_1W5),_1Wl=__app2(_1Wk,E(_1Wi.a),_1Wj),_1Wm=function(_1Wn,_){while(1){var _1Wo=E(_1Wn);if(!_1Wo._){return _kF;}else{var _1Wp=__app2(_1Wk,E(_1Wo.a),_1Wj);_1Wn=_1Wo.b;continue;}}};return new F(function(){return _1Wm(_1Wi.b,_);});}},_1Wq=function(_1Wr,_){while(1){var _1Ws=B((function(_1Wt,_){var _1Wu=E(_1Wt);if(!_1Wu._){return _kF;}else{var _1Wv=_1Wu.b,_1Ww=E(_1Wu.a);if(!_1Ww._){var _1Wx=_1Ww.b,_1Wy=E(_1Ww.a);switch(_1Wy._){case 0:var _1Wz=E(_1Wf),_1WA=E(_m2),_1WB=__app3(_1WA,_1Wz,_1Wy.a,_1Wx),_1WC=function(_1WD,_){while(1){var _1WE=E(_1WD);if(!_1WE._){return _kF;}else{var _1WF=_1WE.b,_1WG=E(_1WE.a);if(!_1WG._){var _1WH=_1WG.b,_1WI=E(_1WG.a);switch(_1WI._){case 0:var _1WJ=__app3(_1WA,_1Wz,_1WI.a,_1WH);_1WD=_1WF;continue;case 1:var _1WK=__app3(E(_1W9),_1Wz,_1WI.a,_1WH);_1WD=_1WF;continue;default:var _1WL=__app3(E(_1W8),_1Wz,_1WI.a,_1WH);_1WD=_1WF;continue;}}else{var _1WM=B(_1Wg(_1WG.a,_));_1WD=_1WF;continue;}}}};return new F(function(){return _1WC(_1Wv,_);});break;case 1:var _1WN=E(_1Wf),_1WO=E(_1W9),_1WP=__app3(_1WO,_1WN,_1Wy.a,_1Wx),_1WQ=function(_1WR,_){while(1){var _1WS=E(_1WR);if(!_1WS._){return _kF;}else{var _1WT=_1WS.b,_1WU=E(_1WS.a);if(!_1WU._){var _1WV=_1WU.b,_1WW=E(_1WU.a);switch(_1WW._){case 0:var _1WX=__app3(E(_m2),_1WN,_1WW.a,_1WV);_1WR=_1WT;continue;case 1:var _1WY=__app3(_1WO,_1WN,_1WW.a,_1WV);_1WR=_1WT;continue;default:var _1WZ=__app3(E(_1W8),_1WN,_1WW.a,_1WV);_1WR=_1WT;continue;}}else{var _1X0=B(_1Wg(_1WU.a,_));_1WR=_1WT;continue;}}}};return new F(function(){return _1WQ(_1Wv,_);});break;default:var _1X1=E(_1Wf),_1X2=E(_1W8),_1X3=__app3(_1X2,_1X1,_1Wy.a,_1Wx),_1X4=function(_1X5,_){while(1){var _1X6=E(_1X5);if(!_1X6._){return _kF;}else{var _1X7=_1X6.b,_1X8=E(_1X6.a);if(!_1X8._){var _1X9=_1X8.b,_1Xa=E(_1X8.a);switch(_1Xa._){case 0:var _1Xb=__app3(E(_m2),_1X1,_1Xa.a,_1X9);_1X5=_1X7;continue;case 1:var _1Xc=__app3(E(_1W9),_1X1,_1Xa.a,_1X9);_1X5=_1X7;continue;default:var _1Xd=__app3(_1X2,_1X1,_1Xa.a,_1X9);_1X5=_1X7;continue;}}else{var _1Xe=B(_1Wg(_1X8.a,_));_1X5=_1X7;continue;}}}};return new F(function(){return _1X4(_1Wv,_);});}}else{var _1Xf=B(_1Wg(_1Ww.a,_));_1Wr=_1Wv;return __continue;}}})(_1Wr,_));if(_1Ws!=__continue){return _1Ws;}}};return new F(function(){return A2(_1Tv,_1Wc,function(_){return new F(function(){return _1Wq(_1We,_);});});});},_1Xg=function(_1Xh,_1Xi,_1Xj,_1Xk){var _1Xl=B(_1Ti(_1Xi)),_1Xm=function(_1Xn){return new F(function(){return A3(_1U2,_1Xl,new T(function(){return B(_1Wa(_1Xh,_1Xi,_1Xn,_1Xk));}),new T(function(){return B(A2(_1Ve,_1Xl,_1Xn));}));});};return new F(function(){return A3(_1U4,_1Xl,_1Xj,_1Xm);});},_1Xo=function(_1Xp,_){var _1Xq=E(_1Xp);if(!_1Xq._){return _Z;}else{var _1Xr=E(_1Xq.a),_1Xs=B(A(_1Xg,[_1VT,_63,_1VZ,new T2(1,new T(function(){var _1Xt=E(_1W4);switch(E(_1Xr.a)){case 0:return new T2(0,E(_1Xt),E(_1W3));break;case 1:return new T2(0,E(_1Xt),E(_1W2));break;default:return new T2(0,E(_1Xt),E(_1W1));}}),new T2(1,new T(function(){return new T2(0,E(_1W0),_1Xr.b);}),_Z)),_])),_1Xu=B(_1Xo(_1Xq.b,_));return new T2(1,_1Xs,_1Xu);}},_1Xv=new T(function(){return new T1(0,"volume");}),_1Xw=new T(function(){return new T1(0,"muted");}),_1Xx=new T(function(){return new T1(0,"loop");}),_1Xy=new T(function(){return new T1(0,"autoplay");}),_1Xz="true",_1XA=new T(function(){return toJSStr(_Z);}),_1XB=new T(function(){return new T1(0,"controls");}),_1XC=function(_){return new F(function(){return __app1(E(_1VY),"audio");});},_1XD=function(_1XE,_1XF,_1XG){var _1XH=function(_){var _1XI=B(_1Xo(_1XG,_)),_1XJ=B(A(_1Xg,[_1VT,_63,_1XC,new T2(1,new T(function(){var _1XK=E(_1XB);if(!E(E(_1XF).a)){return new T2(0,E(_1XK),E(_1XA));}else{return new T2(0,E(_1XK),E(_1Xz));}}),new T2(1,new T(function(){var _1XL=E(_1Xy);if(!E(E(_1XF).b)){return new T2(0,E(_1XL),E(_1XA));}else{return new T2(0,E(_1XL),E(_1Xz));}}),new T2(1,new T(function(){var _1XM=E(_1Xx);if(!E(E(_1XF).c)){return new T2(0,E(_1XM),E(_1XA));}else{return new T2(0,E(_1XM),E(_1Xz));}}),new T2(1,new T(function(){var _1XN=E(_1Xw);if(!E(E(_1XF).e)){return new T2(0,E(_1XN),E(_1XA));}else{return new T2(0,E(_1XN),E(_1Xz));}}),new T2(1,new T(function(){var _1XO=String(E(_1XF).f);return new T2(0,E(_1Xv),_1XO);}),new T2(1,new T(function(){var _1XP=E(_1VX);switch(E(E(_1XF).d)){case 0:return new T2(0,E(_1XP),E(_1VW));break;case 1:return new T2(0,E(_1XP),E(_1VV));break;default:return new T2(0,E(_1XP),E(_1VU));}}),new T2(1,new T(function(){return B(_1VO(_1XI));}),_Z))))))),_]));return new T1(0,_1XJ);};return new F(function(){return A2(_1Tv,_1XE,_1XH);});},_1XQ=new T(function(){return B(unCStr("vaw"));}),_1XR=new T(function(){return B(unCStr("ggo"));}),_1XS=new T(function(){return B(unCStr("3pm"));}),_1XT=0,_1XU=1,_1XV=2,_1XW=function(_1XX){var _1XY=B(_uf(3,B(_KS(fromJSStr(_1XX),_Z))));return (!B(_vi(_1XY,_1XS)))?(!B(_vi(_1XY,_1XR)))?(!B(_vi(_1XY,_1XQ)))?__Z:new T1(1,new T2(0,E(_1XV),_1XX)):new T1(1,new T2(0,E(_1XU),_1XX)):new T1(1,new T2(0,E(_1XT),_1XX));},_1XZ="Audio/test.mp3",_1Y0=new T(function(){var _1Y1=B(_1XW(E(_1XZ)));if(!_1Y1._){return B(_Q1("Browser.hs:99:7-37|Just adSrc"));}else{return E(_1Y1.a);}}),_1Y2=new T2(1,_1Y0,_Z),_1Y3=2,_1Y4=new T6(0,E(_B3),E(_B3),E(_B4),E(_1Y3),E(_B3),1),_1Y5=new T(function(){return B(_1XD(_63,_1Y4,_1Y2));}),_1Y6="src",_1Y7=new T(function(){return B(unCStr("img"));}),_1Y8=function(_1Y9,_1Ya){return new F(function(){return A2(_1Tv,_1Y9,function(_){var _1Yb=__app1(E(_1VY),toJSStr(E(_1Y7))),_1Yc=__app3(E(_m2),_1Yb,E(_1Y6),E(_1Ya));return _1Yb;});});},_1Yd=new T(function(){return B(unCStr(".png"));}),_1Ye=function(_1Yf,_1Yg){var _1Yh=E(_1Yf);if(_1Yh==( -1)){return __Z;}else{var _1Yi=new T(function(){var _1Yj=new T(function(){return toJSStr(B(_x(_1Yg,new T(function(){return B(_x(B(_H(0,_1Yh,_Z)),_1Yd));},1))));});return B(_1Y8(_63,_1Yj));});return new F(function(){return _x(B(_1Ye(_1Yh-1|0,_1Yg)),new T2(1,_1Yi,_Z));});}},_1Yk=new T(function(){return B(unCStr("Images/Wst/wst"));}),_1Yl=new T(function(){return B(_1Ye(120,_1Yk));}),_1Ym=function(_1Yn,_){var _1Yo=E(_1Yn);if(!_1Yo._){return _Z;}else{var _1Yp=B(A1(_1Yo.a,_)),_1Yq=B(_1Ym(_1Yo.b,_));return new T2(1,_1Yp,_1Yq);}},_1Yr=new T(function(){return B(unCStr("Images/Chara/ch"));}),_1Ys=new T(function(){return B(_1Ye(56,_1Yr));}),_1Yt=function(_1Yu,_){var _1Yv=E(_1Yu);if(!_1Yv._){return _Z;}else{var _1Yw=B(A1(_1Yv.a,_)),_1Yx=B(_1Yt(_1Yv.b,_));return new T2(1,_1Yw,_1Yx);}},_1Yy=new T(function(){return B(unCStr("Images/img"));}),_1Yz=new T(function(){return B(_1Ye(5,_1Yy));}),_1YA=function(_1YB,_){var _1YC=E(_1YB);if(!_1YC._){return _Z;}else{var _1YD=B(A1(_1YC.a,_)),_1YE=B(_1YA(_1YC.b,_));return new T2(1,_1YD,_1YE);}},_1YF=new T(function(){return eval("(function(t,f){return window.setInterval(f,t);})");}),_1YG=new T(function(){return eval("(function(t,f){return window.setTimeout(f,t);})");}),_1YH=function(_1YI,_1YJ,_1YK){var _1YL=B(_1V3(_1YI)),_1YM=new T(function(){return B(_1Tv(_1YL));}),_1YN=function(_1YO){var _1YP=function(_){var _1YQ=E(_1YJ);if(!_1YQ._){var _1YR=B(A1(_1YO,_kF)),_1YS=__createJSFunc(0,function(_){var _1YT=B(A1(_1YR,_));return _3h;}),_1YU=__app2(E(_1YG),_1YQ.a,_1YS);return new T(function(){var _1YV=Number(_1YU),_1YW=jsTrunc(_1YV);return new T2(0,_1YW,E(_1YQ));});}else{var _1YX=B(A1(_1YO,_kF)),_1YY=__createJSFunc(0,function(_){var _1YZ=B(A1(_1YX,_));return _3h;}),_1Z0=__app2(E(_1YF),_1YQ.a,_1YY);return new T(function(){var _1Z1=Number(_1Z0),_1Z2=jsTrunc(_1Z1);return new T2(0,_1Z2,E(_1YQ));});}};return new F(function(){return A1(_1YM,_1YP);});},_1Z3=new T(function(){return B(A2(_1Vb,_1YI,function(_1Z4){return E(_1YK);}));});return new F(function(){return A3(_1U4,B(_1Ti(_1YL)),_1Z3,_1YN);});},_1Z5=new T2(1,_2A,_Z),_1Z6=function(_1Z7){var _1Z8=E(_1Z7);if(!_1Z8._){return E(_1Z5);}else{var _1Z9=new T(function(){return B(_2C(_1Us,_1Z8.a,new T(function(){return B(_1Z6(_1Z8.b));})));});return new T2(1,_2z,_1Z9);}},_1Za=function(_1Zb){var _1Zc=E(_1Zb),_1Zd=E(_1Zc.a),_1Ze=new T(function(){return B(_x(_1Zd.b,new T(function(){return B(unAppCStr(" >>",_1Zd.c));},1)));});return new T2(0,new T2(1,_1Zc.b,_1th),_1Ze);},_1Zf=function(_){var _1Zg=B(_1YA(_1Yz,_)),_1Zh=B(_1Yt(_1Ys,_)),_1Zi=B(_1Ym(_1Yl,_)),_1Zj=B(A1(_1Y5,_)),_1Zk=_1Zj,_1Zl=__app1(E(_1UC),"canvas"),_1Zm=__eq(_1Zl,E(_3h));if(!E(_1Zm)){var _1Zn=__isUndef(_1Zl);if(!E(_1Zn)){var _1Zo=B(A3(_1UF,_63,_1Zl,_)),_1Zp=E(_1Zo);if(!_1Zp._){return new F(function(){return die(_1UZ);});}else{var _1Zq=E(_1Zp.a),_1Zr=_1Zq.b,_1Zs=B(_a8(_1Zr,_)),_1Zt=_1Zs,_1Zu=nMV(_1UT),_1Zv=_1Zu,_1Zw=new T3(0,_1Zg,_1Zh,_1Zi),_1Zx=B(A(_1Vg,[_64,_3K,_t,_1UB,_1Um,function(_1Zy,_){var _1Zz=B(_1VJ(_)),_1ZA=rMV(_1Zv),_1ZB=E(E(_1Zt).a),_1ZC=E(_1ZA),_1ZD=E(_1ZC.a),_1ZE=E(_1ZC.b),_1ZF=E(_1ZC.h),_1ZG=E(_1ZC.s),_1ZH=E(_1ZC.v),_1ZI=B(_1Ix(_1Zq,_1ZB.a,_1ZB.b,_1Zw,E(_1Zy).a,_1ZD.a,_1ZD.b,_1ZD.c,_1ZD.d,_1ZD.e,_1ZD.f,_1ZD.g,_1ZD.h,_1ZD.i,_1ZD.j,_1ZD.k,_1ZE.a,_1ZE.b,_1ZC.c,_1ZC.d,_1ZC.e,_1ZC.f,_1ZC.g,_1ZF.a,_1ZF.b,_1ZC.i,_1ZC.j,_1ZC.k,_1ZC.l,_1ZC.m,_1ZC.n,_1ZC.o,_1ZC.p,_1ZC.q,_1ZC.r,_1ZG.a,_1ZG.b,_1ZC.t,_1ZC.u,_1ZH.a,_1ZH.b,_1ZH.c,_1ZH.d,_1ZH.e,_1ZH.f,_1ZH.g,_1ZH.h,_1ZH.i,_1ZC.w,_)),_=wMV(_1Zv,_1ZI);return _kF;},_])),_1ZJ=B(A(_1Vg,[_64,_3K,_3J,_1Zl,_1Ul,function(_1ZK,_){var _1ZL=E(E(_1ZK).a),_1ZM=_1ZL.a,_1ZN=_1ZL.b,_1ZO=rMV(_1Zv),_1ZP=E(_1ZO),_1ZQ=E(_1ZP.v);if(!E(_1ZQ.i)){var _1ZR=B(A3(_1Ua,_63,E(_1Zk).a,_)),_1ZS=B(A(_1SU,[_1Zq,_1Zt,_1Zw,_1ZM,_1ZN,{_:0,a:E(_1ZP.a),b:E(_1ZP.b),c:E(_1ZP.c),d:E(_1ZP.d),e:E(_1ZP.e),f:E(_1ZP.f),g:E(_1ZP.g),h:E(_1ZP.h),i:_1ZP.i,j:_1ZP.j,k:_1ZP.k,l:_1ZP.l,m:E(_1ZP.m),n:_1ZP.n,o:E(_1ZP.o),p:E(_1ZP.p),q:_1ZP.q,r:E(_1ZP.r),s:E(_1ZP.s),t:_1ZP.t,u:E(_1ZP.u),v:E({_:0,a:E(_1ZQ.a),b:E(_1ZQ.b),c:E(_1ZQ.c),d:E(_1ZQ.d),e:E(_1ZQ.e),f:E(_1ZQ.f),g:E(_1ZQ.g),h:E(_1ZQ.h),i:E(_B4)}),w:E(_1ZP.w)},_])),_=wMV(_1Zv,_1ZS);return _kF;}else{var _1ZT=B(A(_1SU,[_1Zq,_1Zt,_1Zw,_1ZM,_1ZN,_1ZP,_])),_=wMV(_1Zv,_1ZT);return _kF;}},_])),_1ZU=B(A(_1Vg,[_64,_3K,_5j,_1Zl,_1Up,function(_1ZV,_){var _1ZW=B(_1Uz(E(_1ZV).a,_)),_1ZX=rMV(_1Zv),_1ZY=E(_1ZX),_1ZZ=_1ZY.a,_200=_1ZY.b,_201=_1ZY.c,_202=_1ZY.d,_203=_1ZY.e,_204=_1ZY.f,_205=_1ZY.g,_206=_1ZY.h,_207=_1ZY.i,_208=_1ZY.j,_209=_1ZY.k,_20a=_1ZY.l,_20b=_1ZY.m,_20c=_1ZY.n,_20d=_1ZY.o,_20e=_1ZY.p,_20f=_1ZY.q,_20g=_1ZY.r,_20h=_1ZY.s,_20i=_1ZY.t,_20j=_1ZY.w,_20k=E(_1ZY.v);if(!E(_20k.e)){var _=wMV(_1Zv,{_:0,a:E(_1ZZ),b:E(_200),c:E(_201),d:E(_202),e:E(_203),f:E(_204),g:E(_205),h:E(_206),i:_207,j:_208,k:_209,l:_20a,m:E(_20b),n:_20c,o:E(_20d),p:E(_20e),q:_20f,r:E(_20g),s:E(_20h),t:_20i,u:E(_Z),v:E(_20k),w:E(_20j)});return _kF;}else{var _20l=B(_1VJ(_)),_=wMV(_1Zv,{_:0,a:E(_1ZZ),b:E(_200),c:E(_201),d:E(_202),e:E(_203),f:E(_204),g:E(_205),h:E(_206),i:_207,j:_208,k:_209,l:_20a,m:E(_20b),n:_20c,o:E(_20d),p:E(_20e),q:_20f,r:E(_20g),s:E(_20h),t:_20i,u:E(_Z),v:E(_20k),w:E(_20j)});return _kF;}},_])),_20m=function(_20n,_){var _20o=E(_20n).a,_20p=B(_1Uz(_20o,_)),_20q=rMV(_1Zv),_20r=new T(function(){var _20s=E(_20q);return {_:0,a:E(_20s.a),b:E(_20s.b),c:E(_20s.c),d:E(_20s.d),e:E(_20s.e),f:E(_20s.f),g:E(_20s.g),h:E(_20s.h),i:_20s.i,j:_20s.j,k:_20s.k,l:_20s.l,m:E(_20s.m),n:_20s.n,o:E(_20s.o),p:E(_20s.p),q:_20s.q,r:E(_20s.r),s:E(_20s.s),t:_20s.t,u:E(B(_x(_20s.u,new T2(1,new T(function(){return B(_aj(_1Uq,_20o));}),_Z)))),v:E(_20s.v),w:E(_20s.w)};}),_=wMV(_1Zv,_20r);return _kF;},_20t=B(A(_1Vg,[_64,_3K,_5j,_1Zl,_1Uo,_20m,_])),_20u=function(_){var _20v=rMV(_1Zv),_=wMV(_1Zv,new T(function(){var _20w=E(_20v),_20x=E(_20w.v);return {_:0,a:E(_20w.a),b:E(_20w.b),c:E(_20w.c),d:E(_20w.d),e:E(_20w.e),f:E(_20w.f),g:E(_20w.g),h:E(_20w.h),i:_20w.i,j:_20w.j,k:_20w.k,l:_20w.l,m:E(_20w.m),n:_20w.n,o:E(_20w.o),p:E(_20w.p),q:_20w.q,r:E(_20w.r),s:E(_20w.s),t:_20w.t,u:E(_20w.u),v:E({_:0,a:E(_20x.a),b:E(_20x.b),c:E(_20x.c),d:E(_20x.d),e:E(_B3),f:E(_20x.f),g:E(_20x.g),h:E(_20x.h),i:E(_20x.i)}),w:E(_20w.w)};}));return _kF;},_20y=function(_20z,_){var _20A=E(_20z),_20B=rMV(_1Zv),_20C=E(_20B),_20D=_20C.a,_20E=_20C.b,_20F=_20C.c,_20G=_20C.d,_20H=_20C.e,_20I=_20C.f,_20J=_20C.g,_20K=_20C.h,_20L=_20C.i,_20M=_20C.j,_20N=_20C.k,_20O=_20C.l,_20P=_20C.m,_20Q=_20C.n,_20R=_20C.o,_20S=_20C.p,_20T=_20C.q,_20U=_20C.r,_20V=_20C.s,_20W=_20C.t,_20X=_20C.w,_20Y=E(_20C.v),_20Z=_20Y.a,_210=_20Y.b,_211=_20Y.c,_212=_20Y.d,_213=_20Y.f,_214=_20Y.g,_215=_20Y.h,_216=_20Y.i,_217=E(_20C.u);if(!_217._){var _218=B(_1Ez(_1HK,_1V2,_)),_=wMV(_1Zv,{_:0,a:E(_20D),b:E(_20E),c:E(_20F),d:E(_20G),e:E(_20H),f:E(_20I),g:E(_20J),h:E(_20K),i:_20L,j:_20M,k:_20N,l:_20O,m:E(_20P),n:_20Q,o:E(_20R),p:E(_20S),q:_20T,r:E(_20U),s:E(_20V),t:_20W,u:E(_Z),v:E({_:0,a:E(_20Z),b:E(_210),c:E(_211),d:E(_212),e:E(_B4),f:E(_213),g:E(_214),h:E(_215),i:E(_216)}),w:E(_20X)}),_219=B(A(_1YH,[_64,_1V1,_20u,_]));return _kF;}else{var _21a=new T(function(){return B(_2C(_1Us,_217.a,new T(function(){return B(_1Z6(_217.b));})));}),_21b=B(_1Ez(_1HK,new T2(1,_2B,_21a),_)),_=wMV(_1Zv,{_:0,a:E(_20D),b:E(_20E),c:E(_20F),d:E(_20G),e:E(_20H),f:E(_20I),g:E(_20J),h:E(_20K),i:_20L,j:_20M,k:_20N,l:_20O,m:E(_20P),n:_20Q,o:E(_20R),p:E(_20S),q:_20T,r:E(_20U),s:E(_20V),t:_20W,u:E(_217),v:E({_:0,a:E(_20Z),b:E(_210),c:E(_211),d:E(_212),e:E(_B4),f:E(_213),g:E(_214),h:E(_215),i:E(_216)}),w:E(_20X)}),_21c=B(A(_1YH,[_64,_1V1,_20u,_]));return _kF;}},_21d=B(A(_1Vg,[_64,_3K,_5j,_1Zl,_1Un,_20y,_])),_21e=function(_){var _21f=rMV(_1Zv),_21g=E(_21f),_21h=_21g.a,_21i=_21g.b,_21j=_21g.c,_21k=_21g.d,_21l=_21g.e,_21m=_21g.f,_21n=_21g.g,_21o=_21g.h,_21p=_21g.i,_21q=_21g.j,_21r=_21g.k,_21s=_21g.l,_21t=_21g.m,_21u=_21g.n,_21v=_21g.o,_21w=_21g.p,_21x=_21g.q,_21y=_21g.r,_21z=_21g.s,_21A=_21g.t,_21B=_21g.u,_21C=_21g.w,_21D=E(_21g.v),_21E=new T(function(){if(_21A<=298){return _21A+1|0;}else{return E(_1HP);}}),_21F=new T(function(){var _21G=function(_21H){var _21I=E(_21H);return (_21I==30)?{_:0,a:E(_21h),b:E(_21i),c:E(_21j),d:E(B(_x(B(_0(_Z,B(_1Is(B(_aj(_1Gf,_21w)),B(_9T(_21k)))))),new T(function(){return B(_aj(_1Za,_21w));},1)))),e:E(_21l),f:E(_21m),g:E(_21n),h:E(_21o),i:_21p,j:_21q,k:_21r,l:_21s,m:E(_21t),n:_21u,o:E(_21v),p:E(_21w),q:30,r:E(_21y),s:E(_21z),t:E(_21E),u:E(_21B),v:E(_21D),w:E(_21C)}:{_:0,a:E(_21h),b:E(_21i),c:E(_21j),d:E(_21k),e:E(_21l),f:E(_21m),g:E(_21n),h:E(_21o),i:_21p,j:_21q,k:_21r,l:_21s,m:E(_21t),n:_21u,o:E(_21v),p:E(_21w),q:_21I,r:E(_21y),s:E(_21z),t:E(_21E),u:E(_21B),v:E(_21D),w:E(_21C)};};if(!E(_21w)._){return B(_21G(_21x));}else{if(!B(_ep(E(_21E),20))){return B(_21G(_21x+1|0));}else{return B(_21G(_21x));}}});if(!E(_21D.b)){if(!E(_21D.h)){var _21J=E(E(_1Zt).a),_21K=E(_21F),_21L=E(_21K.b),_21M=E(_21K.h),_21N=E(_21K.v),_21O=B(_13f(_1Zq,_21J.a,_21J.b,_1Zw,_21K.a,_21L.a,_21L.b,_21K.c,_21K.d,_21K.e,_21K.f,_21K.g,_21M.a,_21M.b,_21K.i,_21K.j,_21K.k,_21K.l,_21K.m,_21K.n,_21K.o,_21K.p,_21K.q,_21K.r,_21K.s,_21K.t,_21K.u,_21N.a,_21N.b,_21N.c,_21N.d,_21N.e,_21N.f,_21N.g,_21N.h,_21N.i,_21K.w,_)),_=wMV(_1Zv,_21O);return _kF;}else{if(!B(_ep(E(_21E),10))){if(!E(_21D.c)){var _21P=E(E(_1Zt).a),_21Q=B(_1dW(_1Zq.a,_1Zr,_21P.a,_21P.b,_1Zw,_21F,_)),_=wMV(_1Zv,_21Q);return _kF;}else{var _21R=E(E(_1Zt).a),_21S=E(_21F),_21T=E(_21S.b),_21U=E(_21S.h),_21V=E(_21S.v),_21W=B(_13f(_1Zq,_21R.a,_21R.b,_1Zw,_21S.a,_21T.a,_21T.b,_21S.c,_21S.d,_21S.e,_21S.f,_21S.g,_21U.a,_21U.b,_21S.i,_21S.j,_21S.k,_21S.l,_21S.m,_21S.n,_21S.o,_21S.p,_21S.q,_21S.r,_21S.s,_21S.t,_21S.u,_21V.a,_21V.b,_21V.c,_21V.d,_21V.e,_21V.f,_21V.g,_21V.h,_21V.i,_21S.w,_)),_=wMV(_1Zv,_21W);return _kF;}}else{var _21X=E(E(_1Zt).a),_21Y=E(_21F),_21Z=E(_21Y.b),_220=E(_21Y.h),_221=E(_21Y.v),_222=B(_13f(_1Zq,_21X.a,_21X.b,_1Zw,_21Y.a,_21Z.a,_21Z.b,_21Y.c,_21Y.d,_21Y.e,_21Y.f,_21Y.g,_220.a,_220.b,_21Y.i,_21Y.j,_21Y.k,_21Y.l,_21Y.m,_21Y.n,_21Y.o,_21Y.p,_21Y.q,_21Y.r,_21Y.s,_21Y.t,_21Y.u,_221.a,_221.b,_221.c,_221.d,_221.e,_221.f,_221.g,_221.h,_221.i,_21Y.w,_)),_=wMV(_1Zv,_222);return _kF;}}}else{var _=wMV(_1Zv,_21F);return _kF;}},_223=B(A(_1YH,[_64,_1V0,_21e,_]));return _kF;}}else{return new F(function(){return die(_1UW);});}}else{return new F(function(){return die(_1UW);});}},_224=function(_){return new F(function(){return _1Zf(_);});};
var hasteMain = function() {B(A(_224, [0]));};window.onload = hasteMain;