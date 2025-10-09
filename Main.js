"use strict";
var __haste_prog_id = 'aa9c9d7d7c955fc025f9b17b0bd660fe645a7e254ca2136f1eb3ab44463c3475';
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

var _0=__Z,_1=new T(function(){return eval("(function(id){return document.getElementById(id);})");}),_2=function(_){return new F(function(){return __jsNull();});},_3=function(_4){var _5=B(A1(_4,_));return E(_5);},_6=new T(function(){return B(_3(_2));}),_7=new T(function(){return E(_6);}),_8=function(_9){return E(_9);},_a=function(_b,_c){return E(_b)==E(_c);},_d=function(_e,_f){return E(_e)!=E(_f);},_g=new T2(0,_a,_d),_h="screenY",_i="screenX",_j="clientY",_k="clientX",_l="pageY",_m="pageX",_n="target",_o="identifier",_p=function(_q,_){var _r=__get(_q,E(_o)),_s=__get(_q,E(_n)),_t=__get(_q,E(_m)),_u=__get(_q,E(_l)),_v=__get(_q,E(_k)),_w=__get(_q,E(_j)),_x=__get(_q,E(_i)),_y=__get(_q,E(_h));return new T(function(){var _z=Number(_r),_A=jsTrunc(_z);return new T5(0,_A,_s,E(new T2(0,new T(function(){var _B=Number(_t);return jsTrunc(_B);}),new T(function(){var _C=Number(_u);return jsTrunc(_C);}))),E(new T2(0,new T(function(){var _D=Number(_v);return jsTrunc(_D);}),new T(function(){var _E=Number(_w);return jsTrunc(_E);}))),E(new T2(0,new T(function(){var _F=Number(_x);return jsTrunc(_F);}),new T(function(){var _G=Number(_y);return jsTrunc(_G);}))));});},_H=__Z,_I=function(_J,_){var _K=E(_J);if(!_K._){return _H;}else{var _L=B(_p(E(_K.a),_)),_M=B(_I(_K.b,_));return new T2(1,_L,_M);}},_N="touches",_O=function(_P,_){var _Q=E(_P);if(!_Q._){return _H;}else{var _R=B(_O(_Q.b,_));return new T2(1,new T(function(){var _S=Number(E(_Q.a));return jsTrunc(_S);}),_R);}},_T=function(_U,_){var _V=__arr2lst(0,_U);return new F(function(){return _O(_V,_);});},_W=function(_X,_){return new F(function(){return _T(E(_X),_);});},_Y=function(_Z,_){return new T(function(){var _10=Number(E(_Z));return jsTrunc(_10);});},_11=new T2(0,_Y,_W),_12=function(_13){return E(E(_13).b);},_14=function(_15,_16,_){var _17=__arr2lst(0,_16),_18=new T(function(){return B(_12(_15));}),_19=function(_1a,_){var _1b=E(_1a);if(!_1b._){return _H;}else{var _1c=B(A2(_18,_1b.a,_)),_1d=B(_19(_1b.b,_));return new T2(1,_1c,_1d);}};return new F(function(){return _19(_17,_);});},_1e=function(_1f,_){return new F(function(){return _14(_11,E(_1f),_);});},_1g=new T2(0,_W,_1e),_1h=new T(function(){return eval("(function(e) {  var len = e.changedTouches.length;  var chts = new Array(len);  for(var i = 0; i < len; ++i) {chts[i] = e.changedTouches[i].identifier;}  var len = e.targetTouches.length;  var tts = new Array(len);  for(var i = 0; i < len; ++i) {tts[i] = e.targetTouches[i].identifier;}  return [chts, tts];})");}),_1i=function(_1j,_){var _1k=E(_1j);if(!_1k._){return _H;}else{var _1l=B(_1i(_1k.b,_));return new T2(1,_1k.a,_1l);}},_1m=new T(function(){return B(unCStr("base"));}),_1n=new T(function(){return B(unCStr("GHC.IO.Exception"));}),_1o=new T(function(){return B(unCStr("IOException"));}),_1p=new T5(0,new Long(4053623282,1685460941,true),new Long(3693590983,2507416641,true),_1m,_1n,_1o),_1q=new T5(0,new Long(4053623282,1685460941,true),new Long(3693590983,2507416641,true),_1p,_H,_H),_1r=function(_1s){return E(_1q);},_1t=function(_1u){return E(E(_1u).a);},_1v=function(_1w,_1x,_1y){var _1z=B(A1(_1w,_)),_1A=B(A1(_1x,_)),_1B=hs_eqWord64(_1z.a,_1A.a);if(!_1B){return __Z;}else{var _1C=hs_eqWord64(_1z.b,_1A.b);return (!_1C)?__Z:new T1(1,_1y);}},_1D=function(_1E){var _1F=E(_1E);return new F(function(){return _1v(B(_1t(_1F.a)),_1r,_1F.b);});},_1G=new T(function(){return B(unCStr(": "));}),_1H=new T(function(){return B(unCStr(")"));}),_1I=new T(function(){return B(unCStr(" ("));}),_1J=function(_1K,_1L){var _1M=E(_1K);return (_1M._==0)?E(_1L):new T2(1,_1M.a,new T(function(){return B(_1J(_1M.b,_1L));}));},_1N=new T(function(){return B(unCStr("interrupted"));}),_1O=new T(function(){return B(unCStr("system error"));}),_1P=new T(function(){return B(unCStr("unsatisified constraints"));}),_1Q=new T(function(){return B(unCStr("user error"));}),_1R=new T(function(){return B(unCStr("permission denied"));}),_1S=new T(function(){return B(unCStr("illegal operation"));}),_1T=new T(function(){return B(unCStr("end of file"));}),_1U=new T(function(){return B(unCStr("resource exhausted"));}),_1V=new T(function(){return B(unCStr("resource busy"));}),_1W=new T(function(){return B(unCStr("does not exist"));}),_1X=new T(function(){return B(unCStr("already exists"));}),_1Y=new T(function(){return B(unCStr("resource vanished"));}),_1Z=new T(function(){return B(unCStr("timeout"));}),_20=new T(function(){return B(unCStr("unsupported operation"));}),_21=new T(function(){return B(unCStr("hardware fault"));}),_22=new T(function(){return B(unCStr("inappropriate type"));}),_23=new T(function(){return B(unCStr("invalid argument"));}),_24=new T(function(){return B(unCStr("failed"));}),_25=new T(function(){return B(unCStr("protocol error"));}),_26=function(_27,_28){switch(E(_27)){case 0:return new F(function(){return _1J(_1X,_28);});break;case 1:return new F(function(){return _1J(_1W,_28);});break;case 2:return new F(function(){return _1J(_1V,_28);});break;case 3:return new F(function(){return _1J(_1U,_28);});break;case 4:return new F(function(){return _1J(_1T,_28);});break;case 5:return new F(function(){return _1J(_1S,_28);});break;case 6:return new F(function(){return _1J(_1R,_28);});break;case 7:return new F(function(){return _1J(_1Q,_28);});break;case 8:return new F(function(){return _1J(_1P,_28);});break;case 9:return new F(function(){return _1J(_1O,_28);});break;case 10:return new F(function(){return _1J(_25,_28);});break;case 11:return new F(function(){return _1J(_24,_28);});break;case 12:return new F(function(){return _1J(_23,_28);});break;case 13:return new F(function(){return _1J(_22,_28);});break;case 14:return new F(function(){return _1J(_21,_28);});break;case 15:return new F(function(){return _1J(_20,_28);});break;case 16:return new F(function(){return _1J(_1Z,_28);});break;case 17:return new F(function(){return _1J(_1Y,_28);});break;default:return new F(function(){return _1J(_1N,_28);});}},_29=new T(function(){return B(unCStr("}"));}),_2a=new T(function(){return B(unCStr("{handle: "));}),_2b=function(_2c,_2d,_2e,_2f,_2g,_2h){var _2i=new T(function(){var _2j=new T(function(){var _2k=new T(function(){var _2l=E(_2f);if(!_2l._){return E(_2h);}else{var _2m=new T(function(){return B(_1J(_2l,new T(function(){return B(_1J(_1H,_2h));},1)));},1);return B(_1J(_1I,_2m));}},1);return B(_26(_2d,_2k));}),_2n=E(_2e);if(!_2n._){return E(_2j);}else{return B(_1J(_2n,new T(function(){return B(_1J(_1G,_2j));},1)));}}),_2o=E(_2g);if(!_2o._){var _2p=E(_2c);if(!_2p._){return E(_2i);}else{var _2q=E(_2p.a);if(!_2q._){var _2r=new T(function(){var _2s=new T(function(){return B(_1J(_29,new T(function(){return B(_1J(_1G,_2i));},1)));},1);return B(_1J(_2q.a,_2s));},1);return new F(function(){return _1J(_2a,_2r);});}else{var _2t=new T(function(){var _2u=new T(function(){return B(_1J(_29,new T(function(){return B(_1J(_1G,_2i));},1)));},1);return B(_1J(_2q.a,_2u));},1);return new F(function(){return _1J(_2a,_2t);});}}}else{return new F(function(){return _1J(_2o.a,new T(function(){return B(_1J(_1G,_2i));},1));});}},_2v=function(_2w){var _2x=E(_2w);return new F(function(){return _2b(_2x.a,_2x.b,_2x.c,_2x.d,_2x.f,_H);});},_2y=function(_2z,_2A,_2B){var _2C=E(_2A);return new F(function(){return _2b(_2C.a,_2C.b,_2C.c,_2C.d,_2C.f,_2B);});},_2D=function(_2E,_2F){var _2G=E(_2E);return new F(function(){return _2b(_2G.a,_2G.b,_2G.c,_2G.d,_2G.f,_2F);});},_2H=44,_2I=93,_2J=91,_2K=function(_2L,_2M,_2N){var _2O=E(_2M);if(!_2O._){return new F(function(){return unAppCStr("[]",_2N);});}else{var _2P=new T(function(){var _2Q=new T(function(){var _2R=function(_2S){var _2T=E(_2S);if(!_2T._){return E(new T2(1,_2I,_2N));}else{var _2U=new T(function(){return B(A2(_2L,_2T.a,new T(function(){return B(_2R(_2T.b));})));});return new T2(1,_2H,_2U);}};return B(_2R(_2O.b));});return B(A2(_2L,_2O.a,_2Q));});return new T2(1,_2J,_2P);}},_2V=function(_2W,_2X){return new F(function(){return _2K(_2D,_2W,_2X);});},_2Y=new T3(0,_2y,_2v,_2V),_2Z=new T(function(){return new T5(0,_1r,_2Y,_30,_1D,_2v);}),_30=function(_31){return new T2(0,_2Z,_31);},_32=7,_33=new T(function(){return B(unCStr("Pattern match failure in do expression at src/Haste/Prim/Any.hs:268:5-9"));}),_34=new T6(0,_0,_32,_H,_33,_0,_0),_35=new T(function(){return B(_30(_34));}),_36=function(_){return new F(function(){return die(_35);});},_37=function(_38){return E(E(_38).a);},_39=function(_3a,_3b,_3c,_){var _3d=__arr2lst(0,_3c),_3e=B(_1i(_3d,_)),_3f=E(_3e);if(!_3f._){return new F(function(){return _36(_);});}else{var _3g=E(_3f.b);if(!_3g._){return new F(function(){return _36(_);});}else{if(!E(_3g.b)._){var _3h=B(A3(_37,_3a,_3f.a,_)),_3i=B(A3(_37,_3b,_3g.a,_));return new T2(0,_3h,_3i);}else{return new F(function(){return _36(_);});}}}},_3j=function(_3k){return E(E(_3k).a);},_3l=function(_3m,_3n,_3o){while(1){var _3p=E(_3o);if(!_3p._){return false;}else{if(!B(A3(_3j,_3m,_3n,_3p.a))){_3o=_3p.b;continue;}else{return true;}}}},_3q=function(_3r,_3s){while(1){var _3t=B((function(_3u,_3v){var _3w=E(_3v);if(!_3w._){return __Z;}else{var _3x=_3w.a,_3y=_3w.b;if(!B(A1(_3u,_3x))){var _3z=_3u;_3r=_3z;_3s=_3y;return __continue;}else{return new T2(1,_3x,new T(function(){return B(_3q(_3u,_3y));}));}}})(_3r,_3s));if(_3t!=__continue){return _3t;}}},_3A=function(_3B,_){var _3C=__get(_3B,E(_N)),_3D=__arr2lst(0,_3C),_3E=B(_I(_3D,_)),_3F=__app1(E(_1h),_3B),_3G=B(_39(_1g,_1g,_3F,_)),_3H=E(_3G),_3I=new T(function(){var _3J=function(_3K){return new F(function(){return _3l(_g,new T(function(){return E(_3K).a;}),_3H.a);});};return B(_3q(_3J,_3E));}),_3L=new T(function(){var _3M=function(_3N){return new F(function(){return _3l(_g,new T(function(){return E(_3N).a;}),_3H.b);});};return B(_3q(_3M,_3E));});return new T3(0,_3E,_3L,_3I);},_3O=function(_3P,_3Q,_){return new F(function(){return _3A(E(_3Q),_);});},_3R="touchcancel",_3S="touchend",_3T="touchmove",_3U="touchstart",_3V=function(_3W){switch(E(_3W)){case 0:return E(_3U);case 1:return E(_3T);case 2:return E(_3S);default:return E(_3R);}},_3X=new T2(0,_3V,_3O),_3Y=function(_3Z,_40,_){var _41=B(A1(_3Z,_)),_42=B(A1(_40,_));return _41;},_43=function(_44,_45,_){var _46=B(A1(_44,_)),_47=B(A1(_45,_));return new T(function(){return B(A1(_46,_47));});},_48=function(_49,_4a,_){var _4b=B(A1(_4a,_));return _49;},_4c=function(_4d,_4e,_){var _4f=B(A1(_4e,_));return new T(function(){return B(A1(_4d,_4f));});},_4g=new T2(0,_4c,_48),_4h=function(_4i,_){return _4i;},_4j=function(_4k,_4l,_){var _4m=B(A1(_4k,_));return new F(function(){return A1(_4l,_);});},_4n=new T5(0,_4g,_4h,_43,_4j,_3Y),_4o=new T(function(){return E(_2Z);}),_4p=function(_4q){return E(E(_4q).c);},_4r=function(_4s){return new T6(0,_0,_32,_H,_4s,_0,_0);},_4t=function(_4u,_){var _4v=new T(function(){return B(A2(_4p,_4o,new T(function(){return B(A1(_4r,_4u));})));});return new F(function(){return die(_4v);});},_4w=function(_4x,_){return new F(function(){return _4t(_4x,_);});},_4y=function(_4z){return new F(function(){return A1(_4w,_4z);});},_4A=function(_4B,_4C,_){var _4D=B(A1(_4B,_));return new F(function(){return A2(_4C,_4D,_);});},_4E=new T5(0,_4n,_4A,_4j,_4h,_4y),_4F=function(_4G){return E(_4G);},_4H=new T2(0,_4E,_4F),_4I=new T2(0,_4H,_4h),_4J=new T(function(){return eval("(function(cv){return cv.getBoundingClientRect().height})");}),_4K=new T(function(){return eval("(function(cv){return cv.getBoundingClientRect().width})");}),_4L=new T(function(){return eval("(function(cv){return cv.height})");}),_4M=new T(function(){return eval("(function(cv){return cv.width})");}),_4N=function(_4O,_){var _4P=__app1(E(_4M),_4O),_4Q=__app1(E(_4L),_4O),_4R=__app1(E(_4K),_4O),_4S=__app1(E(_4J),_4O);return new T2(0,new T2(0,_4P,_4Q),new T2(0,_4R,_4S));},_4T=new T(function(){return eval("(function(e){e.width = e.width;})");}),_4U=0,_4V=function(_){return _4U;},_4W=new T(function(){return eval("(function(ctx){ctx.beginPath();})");}),_4X=new T(function(){return eval("(function(ctx){ctx.stroke();})");}),_4Y=function(_4Z,_50,_){var _51=__app1(E(_4W),_50),_52=B(A2(_4Z,_50,_)),_53=__app1(E(_4X),_50);return new F(function(){return _4V(_);});},_54=function(_55){return new T2(0,new T(function(){return E(E(_55).a);}),new T(function(){return E(E(_55).b);}));},_56=",",_57="rgba(",_58=new T(function(){return toJSStr(_H);}),_59="rgb(",_5a=")",_5b=new T2(1,_5a,_H),_5c=function(_5d){var _5e=E(_5d);if(!_5e._){var _5f=jsCat(new T2(1,_59,new T2(1,new T(function(){return String(_5e.a);}),new T2(1,_56,new T2(1,new T(function(){return String(_5e.b);}),new T2(1,_56,new T2(1,new T(function(){return String(_5e.c);}),_5b)))))),E(_58));return E(_5f);}else{var _5g=jsCat(new T2(1,_57,new T2(1,new T(function(){return String(_5e.a);}),new T2(1,_56,new T2(1,new T(function(){return String(_5e.b);}),new T2(1,_56,new T2(1,new T(function(){return String(_5e.c);}),new T2(1,_56,new T2(1,new T(function(){return String(_5e.d);}),_5b)))))))),E(_58));return E(_5g);}},_5h="strokeStyle",_5i="fillStyle",_5j=new T(function(){return eval("(function(e,p){var x = e[p];return typeof x === \'undefined\' ? \'\' : x.toString();})");}),_5k=new T(function(){return eval("(function(e,p,v){e[p] = v;})");}),_5l=function(_5m,_5n){var _5o=new T(function(){return B(_5c(_5m));});return function(_5p,_){var _5q=E(_5p),_5r=E(_5i),_5s=E(_5j),_5t=__app2(_5s,_5q,_5r),_5u=E(_5h),_5v=__app2(_5s,_5q,_5u),_5w=E(_5o),_5x=E(_5k),_5y=__app3(_5x,_5q,_5r,_5w),_5z=__app3(_5x,_5q,_5u,_5w),_5A=B(A2(_5n,_5q,_)),_5B=String(_5t),_5C=__app3(_5x,_5q,_5r,_5B),_5D=String(_5v),_5E=__app3(_5x,_5q,_5u,_5D);return new F(function(){return _4V(_);});};},_5F=new T(function(){return eval("(function(ctx,x,y){ctx.moveTo(x,y);})");}),_5G=new T(function(){return eval("(function(ctx,x,y){ctx.lineTo(x,y);})");}),_5H=function(_5I,_5J,_){var _5K=E(_5I);if(!_5K._){return _4U;}else{var _5L=E(_5K.a),_5M=E(_5J),_5N=__app3(E(_5F),_5M,E(_5L.a),E(_5L.b)),_5O=E(_5K.b);if(!_5O._){return _4U;}else{var _5P=E(_5O.a),_5Q=E(_5G),_5R=__app3(_5Q,_5M,E(_5P.a),E(_5P.b)),_5S=function(_5T,_){while(1){var _5U=E(_5T);if(!_5U._){return _4U;}else{var _5V=E(_5U.a),_5W=__app3(_5Q,_5M,E(_5V.a),E(_5V.b));_5T=_5U.b;continue;}}};return new F(function(){return _5S(_5O.b,_);});}}},_5X="lineWidth",_5Y=function(_5Z,_60){var _61=new T(function(){return String(E(_5Z));});return function(_62,_){var _63=E(_62),_64=E(_5X),_65=__app2(E(_5j),_63,_64),_66=E(_5k),_67=__app3(_66,_63,_64,E(_61)),_68=B(A2(_60,_63,_)),_69=String(_65),_6a=__app3(_66,_63,_64,_69);return new F(function(){return _4V(_);});};},_6b=0.5,_6c=new T(function(){return B(unCStr("!!: negative index"));}),_6d=new T(function(){return B(unCStr("Prelude."));}),_6e=new T(function(){return B(_1J(_6d,_6c));}),_6f=new T(function(){return B(err(_6e));}),_6g=new T(function(){return B(unCStr("!!: index too large"));}),_6h=new T(function(){return B(_1J(_6d,_6g));}),_6i=new T(function(){return B(err(_6h));}),_6j=function(_6k,_6l){while(1){var _6m=E(_6k);if(!_6m._){return E(_6i);}else{var _6n=E(_6l);if(!_6n){return E(_6m.a);}else{_6k=_6m.b;_6l=_6n-1|0;continue;}}}},_6o=function(_6p,_6q){if(_6q>=0){return new F(function(){return _6j(_6p,_6q);});}else{return E(_6f);}},_6r=new T3(0,153,255,255),_6s=new T2(1,_6r,_H),_6t=new T3(0,255,153,204),_6u=new T2(1,_6t,_6s),_6v=new T3(0,255,204,153),_6w=new T2(1,_6v,_6u),_6x=new T3(0,200,255,200),_6y=new T2(1,_6x,_6w),_6z=new T(function(){return B(_6o(_6y,3));}),_6A=10,_6B=function(_6C,_6D){var _6E=E(_6D);return (_6E._==0)?__Z:new T2(1,new T(function(){return B(A1(_6C,_6E.a));}),new T(function(){return B(_6B(_6C,_6E.b));}));},_6F="globalAlpha",_6G=function(_6H,_6I){var _6J=new T(function(){return String(E(_6H));});return function(_6K,_){var _6L=E(_6K),_6M=E(_6F),_6N=__app2(E(_5j),_6L,_6M),_6O=E(_5k),_6P=__app3(_6O,_6L,_6M,E(_6J)),_6Q=B(A2(_6I,_6L,_)),_6R=String(_6N),_6S=__app3(_6O,_6L,_6M,_6R);return new F(function(){return _4V(_);});};},_6T=function(_6U,_6V,_){while(1){var _6W=B((function(_6X,_6Y,_){var _6Z=E(_6X);if(!_6Z._){return _4U;}else{var _70=new T(function(){var _71=new T(function(){var _72=new T(function(){return B(_6B(_54,_6Z.a));}),_73=function(_74,_){return new F(function(){return _5H(_72,_74,_);});};return B(_5Y(_6A,function(_75,_){return new F(function(){return _4Y(_73,E(_75),_);});}));});return B(_5l(_6z,_71));}),_76=B(A(_6G,[_6b,_70,_6Y,_])),_77=_6Y;_6U=_6Z.b;_6V=_77;return __continue;}})(_6U,_6V,_));if(_6W!=__continue){return _6W;}}},_78=function(_79){while(1){var _7a=B((function(_7b){var _7c=E(_7b);if(!_7c._){return __Z;}else{var _7d=_7c.b,_7e=E(_7c.a);if(!_7e._){_79=_7d;return __continue;}else{return new T2(1,_7e.b,new T(function(){return B(_78(_7d));}));}}})(_79));if(_7a!=__continue){return _7a;}}},_7f=function(_7g){while(1){var _7h=B((function(_7i){var _7j=E(_7i);if(!_7j._){return __Z;}else{var _7k=_7j.b,_7l=E(_7j.a);if(!_7l._){_7g=_7k;return __continue;}else{return new T2(1,_7l.a,new T(function(){return B(_7f(_7k));}));}}})(_7g));if(_7h!=__continue){return _7h;}}},_7m=function(_7n){while(1){var _7o=B((function(_7p){var _7q=E(_7p);if(!_7q._){return __Z;}else{var _7r=_7q.b,_7s=E(_7q.a);if(!_7s._){_7n=_7r;return __continue;}else{var _7t=new T(function(){return B(_7m(new T2(1,_7s.b,new T(function(){return B(_78(_7r));}))));});return new T2(1,new T2(1,_7s.a,new T(function(){return B(_7f(_7r));})),_7t);}}})(_7n));if(_7o!=__continue){return _7o;}}},_7u=function(_7v,_7w,_7x,_){var _7y=__app1(E(_4T),_7w);return new F(function(){return _6T(B(_7m(_7x)),_7v,_);});},_7z=new T(function(){return eval("(function(ctx,s,x,y){ctx.fillText(s,x,y);})");}),_7A=function(_7B,_7C,_7D){var _7E=new T(function(){return toJSStr(E(_7D));});return function(_7F,_){var _7G=__app4(E(_7z),E(_7F),E(_7E),E(_7B),E(_7C));return new F(function(){return _4V(_);});};},_7H=function(_7I,_){return _4U;},_7J=new T1(0,1),_7K=function(_7L,_7M){var _7N=E(_7L);if(!_7N._){var _7O=_7N.a,_7P=E(_7M);if(!_7P._){var _7Q=_7P.a;return (_7O!=_7Q)?(_7O>_7Q)?2:0:1;}else{var _7R=I_compareInt(_7P.a,_7O);return (_7R<=0)?(_7R>=0)?1:2:0;}}else{var _7S=_7N.a,_7T=E(_7M);if(!_7T._){var _7U=I_compareInt(_7S,_7T.a);return (_7U>=0)?(_7U<=0)?1:2:0;}else{var _7V=I_compare(_7S,_7T.a);return (_7V>=0)?(_7V<=0)?1:2:0;}}},_7W=new T(function(){return B(unCStr("base"));}),_7X=new T(function(){return B(unCStr("GHC.Exception"));}),_7Y=new T(function(){return B(unCStr("ArithException"));}),_7Z=new T5(0,new Long(4194982440,719304104,true),new Long(3110813675,1843557400,true),_7W,_7X,_7Y),_80=new T5(0,new Long(4194982440,719304104,true),new Long(3110813675,1843557400,true),_7Z,_H,_H),_81=function(_82){return E(_80);},_83=function(_84){var _85=E(_84);return new F(function(){return _1v(B(_1t(_85.a)),_81,_85.b);});},_86=new T(function(){return B(unCStr("Ratio has zero denominator"));}),_87=new T(function(){return B(unCStr("denormal"));}),_88=new T(function(){return B(unCStr("divide by zero"));}),_89=new T(function(){return B(unCStr("loss of precision"));}),_8a=new T(function(){return B(unCStr("arithmetic underflow"));}),_8b=new T(function(){return B(unCStr("arithmetic overflow"));}),_8c=function(_8d,_8e){switch(E(_8d)){case 0:return new F(function(){return _1J(_8b,_8e);});break;case 1:return new F(function(){return _1J(_8a,_8e);});break;case 2:return new F(function(){return _1J(_89,_8e);});break;case 3:return new F(function(){return _1J(_88,_8e);});break;case 4:return new F(function(){return _1J(_87,_8e);});break;default:return new F(function(){return _1J(_86,_8e);});}},_8f=function(_8g){return new F(function(){return _8c(_8g,_H);});},_8h=function(_8i,_8j,_8k){return new F(function(){return _8c(_8j,_8k);});},_8l=function(_8m,_8n){return new F(function(){return _2K(_8c,_8m,_8n);});},_8o=new T3(0,_8h,_8f,_8l),_8p=new T(function(){return new T5(0,_81,_8o,_8q,_83,_8f);}),_8q=function(_8r){return new T2(0,_8p,_8r);},_8s=3,_8t=new T(function(){return B(_8q(_8s));}),_8u=new T(function(){return die(_8t);}),_8v=function(_8w,_8x){var _8y=E(_8w);return (_8y._==0)?_8y.a*Math.pow(2,_8x):I_toNumber(_8y.a)*Math.pow(2,_8x);},_8z=function(_8A,_8B){var _8C=E(_8A);if(!_8C._){var _8D=_8C.a,_8E=E(_8B);return (_8E._==0)?_8D==_8E.a:(I_compareInt(_8E.a,_8D)==0)?true:false;}else{var _8F=_8C.a,_8G=E(_8B);return (_8G._==0)?(I_compareInt(_8F,_8G.a)==0)?true:false:(I_compare(_8F,_8G.a)==0)?true:false;}},_8H=function(_8I){var _8J=E(_8I);if(!_8J._){return E(_8J.a);}else{return new F(function(){return I_toInt(_8J.a);});}},_8K=function(_8L,_8M){while(1){var _8N=E(_8L);if(!_8N._){var _8O=_8N.a,_8P=E(_8M);if(!_8P._){var _8Q=_8P.a,_8R=addC(_8O,_8Q);if(!E(_8R.b)){return new T1(0,_8R.a);}else{_8L=new T1(1,I_fromInt(_8O));_8M=new T1(1,I_fromInt(_8Q));continue;}}else{_8L=new T1(1,I_fromInt(_8O));_8M=_8P;continue;}}else{var _8S=E(_8M);if(!_8S._){_8L=_8N;_8M=new T1(1,I_fromInt(_8S.a));continue;}else{return new T1(1,I_add(_8N.a,_8S.a));}}}},_8T=function(_8U,_8V){while(1){var _8W=E(_8U);if(!_8W._){var _8X=E(_8W.a);if(_8X==( -2147483648)){_8U=new T1(1,I_fromInt( -2147483648));continue;}else{var _8Y=E(_8V);if(!_8Y._){var _8Z=_8Y.a;return new T2(0,new T1(0,quot(_8X,_8Z)),new T1(0,_8X%_8Z));}else{_8U=new T1(1,I_fromInt(_8X));_8V=_8Y;continue;}}}else{var _90=E(_8V);if(!_90._){_8U=_8W;_8V=new T1(1,I_fromInt(_90.a));continue;}else{var _91=I_quotRem(_8W.a,_90.a);return new T2(0,new T1(1,_91.a),new T1(1,_91.b));}}}},_92=new T1(0,0),_93=function(_94,_95){while(1){var _96=E(_94);if(!_96._){_94=new T1(1,I_fromInt(_96.a));continue;}else{return new T1(1,I_shiftLeft(_96.a,_95));}}},_97=function(_98,_99,_9a){if(!B(_8z(_9a,_92))){var _9b=B(_8T(_99,_9a)),_9c=_9b.a;switch(B(_7K(B(_93(_9b.b,1)),_9a))){case 0:return new F(function(){return _8v(_9c,_98);});break;case 1:if(!(B(_8H(_9c))&1)){return new F(function(){return _8v(_9c,_98);});}else{return new F(function(){return _8v(B(_8K(_9c,_7J)),_98);});}break;default:return new F(function(){return _8v(B(_8K(_9c,_7J)),_98);});}}else{return E(_8u);}},_9d=function(_9e,_9f){var _9g=E(_9e);if(!_9g._){var _9h=_9g.a,_9i=E(_9f);return (_9i._==0)?_9h>_9i.a:I_compareInt(_9i.a,_9h)<0;}else{var _9j=_9g.a,_9k=E(_9f);return (_9k._==0)?I_compareInt(_9j,_9k.a)>0:I_compare(_9j,_9k.a)>0;}},_9l=new T1(0,1),_9m=function(_9n,_9o){var _9p=E(_9n);if(!_9p._){var _9q=_9p.a,_9r=E(_9o);return (_9r._==0)?_9q<_9r.a:I_compareInt(_9r.a,_9q)>0;}else{var _9s=_9p.a,_9t=E(_9o);return (_9t._==0)?I_compareInt(_9s,_9t.a)<0:I_compare(_9s,_9t.a)<0;}},_9u=new T(function(){return B(unCStr("base"));}),_9v=new T(function(){return B(unCStr("Control.Exception.Base"));}),_9w=new T(function(){return B(unCStr("PatternMatchFail"));}),_9x=new T5(0,new Long(18445595,3739165398,true),new Long(52003073,3246954884,true),_9u,_9v,_9w),_9y=new T5(0,new Long(18445595,3739165398,true),new Long(52003073,3246954884,true),_9x,_H,_H),_9z=function(_9A){return E(_9y);},_9B=function(_9C){var _9D=E(_9C);return new F(function(){return _1v(B(_1t(_9D.a)),_9z,_9D.b);});},_9E=function(_9F){return E(E(_9F).a);},_9G=function(_9H){return new T2(0,_9I,_9H);},_9J=function(_9K,_9L){return new F(function(){return _1J(E(_9K).a,_9L);});},_9M=function(_9N,_9O){return new F(function(){return _2K(_9J,_9N,_9O);});},_9P=function(_9Q,_9R,_9S){return new F(function(){return _1J(E(_9R).a,_9S);});},_9T=new T3(0,_9P,_9E,_9M),_9I=new T(function(){return new T5(0,_9z,_9T,_9G,_9B,_9E);}),_9U=new T(function(){return B(unCStr("Non-exhaustive patterns in"));}),_9V=function(_9W,_9X){return new F(function(){return die(new T(function(){return B(A2(_4p,_9X,_9W));}));});},_9Y=function(_9Z,_8r){return new F(function(){return _9V(_9Z,_8r);});},_a0=function(_a1,_a2){var _a3=E(_a2);if(!_a3._){return new T2(0,_H,_H);}else{var _a4=_a3.a;if(!B(A1(_a1,_a4))){return new T2(0,_H,_a3);}else{var _a5=new T(function(){var _a6=B(_a0(_a1,_a3.b));return new T2(0,_a6.a,_a6.b);});return new T2(0,new T2(1,_a4,new T(function(){return E(E(_a5).a);})),new T(function(){return E(E(_a5).b);}));}}},_a7=32,_a8=new T(function(){return B(unCStr("\n"));}),_a9=function(_aa){return (E(_aa)==124)?false:true;},_ab=function(_ac,_ad){var _ae=B(_a0(_a9,B(unCStr(_ac)))),_af=_ae.a,_ag=function(_ah,_ai){var _aj=new T(function(){var _ak=new T(function(){return B(_1J(_ad,new T(function(){return B(_1J(_ai,_a8));},1)));});return B(unAppCStr(": ",_ak));},1);return new F(function(){return _1J(_ah,_aj);});},_al=E(_ae.b);if(!_al._){return new F(function(){return _ag(_af,_H);});}else{if(E(_al.a)==124){return new F(function(){return _ag(_af,new T2(1,_a7,_al.b));});}else{return new F(function(){return _ag(_af,_H);});}}},_am=function(_an){return new F(function(){return _9Y(new T1(0,new T(function(){return B(_ab(_an,_9U));})),_9I);});},_ao=function(_ap){var _aq=function(_ar,_as){while(1){if(!B(_9m(_ar,_ap))){if(!B(_9d(_ar,_ap))){if(!B(_8z(_ar,_ap))){return new F(function(){return _am("GHC/Integer/Type.lhs:(553,5)-(555,32)|function l2");});}else{return E(_as);}}else{return _as-1|0;}}else{var _at=B(_93(_ar,1)),_au=_as+1|0;_ar=_at;_as=_au;continue;}}};return new F(function(){return _aq(_9l,0);});},_av=function(_aw){var _ax=E(_aw);if(!_ax._){var _ay=_ax.a>>>0;if(!_ay){return  -1;}else{var _az=function(_aA,_aB){while(1){if(_aA>=_ay){if(_aA<=_ay){if(_aA!=_ay){return new F(function(){return _am("GHC/Integer/Type.lhs:(609,5)-(611,40)|function l2");});}else{return E(_aB);}}else{return _aB-1|0;}}else{var _aC=imul(_aA,2)>>>0,_aD=_aB+1|0;_aA=_aC;_aB=_aD;continue;}}};return new F(function(){return _az(1,0);});}}else{return new F(function(){return _ao(_ax);});}},_aE=function(_aF){var _aG=E(_aF);if(!_aG._){var _aH=_aG.a>>>0;if(!_aH){return new T2(0, -1,0);}else{var _aI=function(_aJ,_aK){while(1){if(_aJ>=_aH){if(_aJ<=_aH){if(_aJ!=_aH){return new F(function(){return _am("GHC/Integer/Type.lhs:(609,5)-(611,40)|function l2");});}else{return E(_aK);}}else{return _aK-1|0;}}else{var _aL=imul(_aJ,2)>>>0,_aM=_aK+1|0;_aJ=_aL;_aK=_aM;continue;}}};return new T2(0,B(_aI(1,0)),(_aH&_aH-1>>>0)>>>0&4294967295);}}else{var _aN=_aG.a;return new T2(0,B(_av(_aG)),I_compareInt(I_and(_aN,I_sub(_aN,I_fromInt(1))),0));}},_aO=function(_aP,_aQ){var _aR=E(_aP);if(!_aR._){var _aS=_aR.a,_aT=E(_aQ);return (_aT._==0)?_aS<=_aT.a:I_compareInt(_aT.a,_aS)>=0;}else{var _aU=_aR.a,_aV=E(_aQ);return (_aV._==0)?I_compareInt(_aU,_aV.a)<=0:I_compare(_aU,_aV.a)<=0;}},_aW=function(_aX,_aY){while(1){var _aZ=E(_aX);if(!_aZ._){var _b0=_aZ.a,_b1=E(_aY);if(!_b1._){return new T1(0,(_b0>>>0&_b1.a>>>0)>>>0&4294967295);}else{_aX=new T1(1,I_fromInt(_b0));_aY=_b1;continue;}}else{var _b2=E(_aY);if(!_b2._){_aX=_aZ;_aY=new T1(1,I_fromInt(_b2.a));continue;}else{return new T1(1,I_and(_aZ.a,_b2.a));}}}},_b3=function(_b4,_b5){while(1){var _b6=E(_b4);if(!_b6._){var _b7=_b6.a,_b8=E(_b5);if(!_b8._){var _b9=_b8.a,_ba=subC(_b7,_b9);if(!E(_ba.b)){return new T1(0,_ba.a);}else{_b4=new T1(1,I_fromInt(_b7));_b5=new T1(1,I_fromInt(_b9));continue;}}else{_b4=new T1(1,I_fromInt(_b7));_b5=_b8;continue;}}else{var _bb=E(_b5);if(!_bb._){_b4=_b6;_b5=new T1(1,I_fromInt(_bb.a));continue;}else{return new T1(1,I_sub(_b6.a,_bb.a));}}}},_bc=new T1(0,2),_bd=function(_be,_bf){var _bg=E(_be);if(!_bg._){var _bh=(_bg.a>>>0&(2<<_bf>>>0)-1>>>0)>>>0,_bi=1<<_bf>>>0;return (_bi<=_bh)?(_bi>=_bh)?1:2:0;}else{var _bj=B(_aW(_bg,B(_b3(B(_93(_bc,_bf)),_9l)))),_bk=B(_93(_9l,_bf));return (!B(_9d(_bk,_bj)))?(!B(_9m(_bk,_bj)))?1:2:0;}},_bl=function(_bm,_bn){while(1){var _bo=E(_bm);if(!_bo._){_bm=new T1(1,I_fromInt(_bo.a));continue;}else{return new T1(1,I_shiftRight(_bo.a,_bn));}}},_bp=function(_bq,_br,_bs,_bt){var _bu=B(_aE(_bt)),_bv=_bu.a;if(!E(_bu.b)){var _bw=B(_av(_bs));if(_bw<((_bv+_bq|0)-1|0)){var _bx=_bv+(_bq-_br|0)|0;if(_bx>0){if(_bx>_bw){if(_bx<=(_bw+1|0)){if(!E(B(_aE(_bs)).b)){return 0;}else{return new F(function(){return _8v(_7J,_bq-_br|0);});}}else{return 0;}}else{var _by=B(_bl(_bs,_bx));switch(B(_bd(_bs,_bx-1|0))){case 0:return new F(function(){return _8v(_by,_bq-_br|0);});break;case 1:if(!(B(_8H(_by))&1)){return new F(function(){return _8v(_by,_bq-_br|0);});}else{return new F(function(){return _8v(B(_8K(_by,_7J)),_bq-_br|0);});}break;default:return new F(function(){return _8v(B(_8K(_by,_7J)),_bq-_br|0);});}}}else{return new F(function(){return _8v(_bs,(_bq-_br|0)-_bx|0);});}}else{if(_bw>=_br){var _bz=B(_bl(_bs,(_bw+1|0)-_br|0));switch(B(_bd(_bs,_bw-_br|0))){case 0:return new F(function(){return _8v(_bz,((_bw-_bv|0)+1|0)-_br|0);});break;case 2:return new F(function(){return _8v(B(_8K(_bz,_7J)),((_bw-_bv|0)+1|0)-_br|0);});break;default:if(!(B(_8H(_bz))&1)){return new F(function(){return _8v(_bz,((_bw-_bv|0)+1|0)-_br|0);});}else{return new F(function(){return _8v(B(_8K(_bz,_7J)),((_bw-_bv|0)+1|0)-_br|0);});}}}else{return new F(function(){return _8v(_bs, -_bv);});}}}else{var _bA=B(_av(_bs))-_bv|0,_bB=function(_bC){var _bD=function(_bE,_bF){if(!B(_aO(B(_93(_bF,_br)),_bE))){return new F(function(){return _97(_bC-_br|0,_bE,_bF);});}else{return new F(function(){return _97((_bC-_br|0)+1|0,_bE,B(_93(_bF,1)));});}};if(_bC>=_br){if(_bC!=_br){return new F(function(){return _bD(_bs,new T(function(){return B(_93(_bt,_bC-_br|0));}));});}else{return new F(function(){return _bD(_bs,_bt);});}}else{return new F(function(){return _bD(new T(function(){return B(_93(_bs,_br-_bC|0));}),_bt);});}};if(_bq>_bA){return new F(function(){return _bB(_bq);});}else{return new F(function(){return _bB(_bA);});}}},_bG=new T1(0,2147483647),_bH=new T(function(){return B(_8K(_bG,_9l));}),_bI=function(_bJ){var _bK=E(_bJ);if(!_bK._){var _bL=E(_bK.a);return (_bL==( -2147483648))?E(_bH):new T1(0, -_bL);}else{return new T1(1,I_negate(_bK.a));}},_bM=new T(function(){return 0/0;}),_bN=new T(function(){return  -1/0;}),_bO=new T(function(){return 1/0;}),_bP=0,_bQ=function(_bR,_bS){if(!B(_8z(_bS,_92))){if(!B(_8z(_bR,_92))){if(!B(_9m(_bR,_92))){return new F(function(){return _bp( -1021,53,_bR,_bS);});}else{return  -B(_bp( -1021,53,B(_bI(_bR)),_bS));}}else{return E(_bP);}}else{return (!B(_8z(_bR,_92)))?(!B(_9m(_bR,_92)))?E(_bO):E(_bN):E(_bM);}},_bT=function(_bU){var _bV=E(_bU);return new F(function(){return _bQ(_bV.a,_bV.b);});},_bW=function(_bX){return 1/E(_bX);},_bY=function(_bZ){var _c0=E(_bZ);return (_c0!=0)?(_c0<=0)? -_c0:E(_c0):E(_bP);},_c1=function(_c2){var _c3=E(_c2);if(!_c3._){return _c3.a;}else{return new F(function(){return I_toNumber(_c3.a);});}},_c4=function(_c5){return new F(function(){return _c1(_c5);});},_c6=1,_c7= -1,_c8=function(_c9){var _ca=E(_c9);return (_ca<=0)?(_ca>=0)?E(_ca):E(_c7):E(_c6);},_cb=function(_cc,_cd){return E(_cc)-E(_cd);},_ce=function(_cf){return  -E(_cf);},_cg=function(_ch,_ci){return E(_ch)+E(_ci);},_cj=function(_ck,_cl){return E(_ck)*E(_cl);},_cm={_:0,a:_cg,b:_cb,c:_cj,d:_ce,e:_bY,f:_c8,g:_c4},_cn=function(_co,_cp){return E(_co)/E(_cp);},_cq=new T4(0,_cm,_cn,_bW,_bT),_cr=new T1(0,1),_cs=function(_ct){return E(E(_ct).a);},_cu=function(_cv){return E(E(_cv).a);},_cw=function(_cx){return E(E(_cx).g);},_cy=function(_cz,_cA){var _cB=E(_cA),_cC=new T(function(){var _cD=B(_cs(_cz)),_cE=B(_cy(_cz,B(A3(_cu,_cD,_cB,new T(function(){return B(A2(_cw,_cD,_cr));})))));return new T2(1,_cE.a,_cE.b);});return new T2(0,_cB,_cC);},_cF=0,_cG=new T(function(){var _cH=B(_cy(_cq,_cF));return new T2(1,_cH.a,_cH.b);}),_cI=function(_cJ,_cK){var _cL=jsShowI(_cJ);return new F(function(){return _1J(fromJSStr(_cL),_cK);});},_cM=41,_cN=40,_cO=function(_cP,_cQ,_cR){if(_cQ>=0){return new F(function(){return _cI(_cQ,_cR);});}else{if(_cP<=6){return new F(function(){return _cI(_cQ,_cR);});}else{return new T2(1,_cN,new T(function(){var _cS=jsShowI(_cQ);return B(_1J(fromJSStr(_cS),new T2(1,_cM,_cR)));}));}}},_cT=new T(function(){return B(_cO(0,20,_H));}),_cU=new T(function(){return B(unCStr("px Courier"));}),_cV=new T(function(){return B(_1J(_cT,_cU));}),_cW="font",_cX=function(_cY,_cZ){var _d0=new T(function(){return toJSStr(E(_cY));});return function(_d1,_){var _d2=E(_d1),_d3=E(_cW),_d4=__app2(E(_5j),_d2,_d3),_d5=E(_5k),_d6=__app3(_d5,_d2,_d3,E(_d0)),_d7=B(A2(_cZ,_d2,_)),_d8=String(_d4),_d9=__app3(_d5,_d2,_d3,_d8);return new F(function(){return _4V(_);});};},_da=function(_db,_dc,_dd,_de,_df){var _dg=new T(function(){return E(_dd)*16;}),_dh=new T(function(){return E(_de)*20;}),_di=function(_dj,_dk){var _dl=E(_dj);if(!_dl._){return E(_7H);}else{var _dm=E(_dk);if(!_dm._){return E(_7H);}else{var _dn=new T(function(){return B(_di(_dl.b,_dm.b));}),_do=new T(function(){var _dp=new T(function(){var _dq=new T(function(){return B(_7A(new T(function(){return E(_dg)+16*E(_dm.a);}),_dh,new T2(1,_dl.a,_H)));});return B(_cX(_cV,_dq));});return B(_5l(_dc,_dp));});return function(_dr,_){var _ds=B(A2(_do,_dr,_));return new F(function(){return A2(_dn,_dr,_);});};}}};return new F(function(){return A3(_di,_df,_cG,_db);});},_dt=function(_du,_dv){var _dw=E(_du),_dx=E(_dv);return (_dw>_dx)?E(_dw):E(_dx);},_dy=function(_dz,_dA){var _dB=E(_dz),_dC=E(_dA);return (_dB>_dC)?E(_dC):E(_dB);},_dD=function(_dE,_dF){return (_dE>=_dF)?(_dE!=_dF)?2:1:0;},_dG=function(_dH,_dI){return new F(function(){return _dD(E(_dH),E(_dI));});},_dJ=function(_dK,_dL){return E(_dK)>=E(_dL);},_dM=function(_dN,_dO){return E(_dN)>E(_dO);},_dP=function(_dQ,_dR){return E(_dQ)<=E(_dR);},_dS=function(_dT,_dU){return E(_dT)<E(_dU);},_dV={_:0,a:_g,b:_dG,c:_dS,d:_dP,e:_dM,f:_dJ,g:_dt,h:_dy},_dW=function(_dX){return new T1(0,_dX);},_dY=function(_dZ){return E(E(_dZ).g);},_e0=new T(function(){return B(unCStr(": empty list"));}),_e1=function(_e2){return new F(function(){return err(B(_1J(_6d,new T(function(){return B(_1J(_e2,_e0));},1))));});},_e3=new T(function(){return B(unCStr("maximum"));}),_e4=new T(function(){return B(_e1(_e3));}),_e5=function(_e6,_e7){var _e8=E(_e7);if(!_e8._){return E(_e4);}else{var _e9=new T(function(){return B(_dY(_e6));}),_ea=function(_eb,_ec){while(1){var _ed=E(_eb);if(!_ed._){return E(_ec);}else{var _ee=B(A2(_e9,E(_ec),_ed.a));_eb=_ed.b;_ec=_ee;continue;}}};return new F(function(){return _ea(_e8.b,_e8.a);});}},_ef=function(_eg){return E(E(_eg).h);},_eh=new T(function(){return B(unCStr("minimum"));}),_ei=new T(function(){return B(_e1(_eh));}),_ej=function(_ek,_el){var _em=E(_el);if(!_em._){return E(_ei);}else{var _en=new T(function(){return B(_ef(_ek));}),_eo=function(_ep,_eq){while(1){var _er=E(_ep);if(!_er._){return E(_eq);}else{var _es=B(A2(_en,E(_eq),_er.a));_ep=_er.b;_eq=_es;continue;}}};return new F(function(){return _eo(_em.b,_em.a);});}},_et=function(_eu){return new F(function(){return _ej(_dV,E(_eu).b);});},_ev=function(_ew){return new F(function(){return _ej(_dV,E(_ew).a);});},_ex=124,_ey=63,_ez=new T1(0,20),_eA=function(_eB,_eC){var _eD=E(_eB);if(!_eD._){return __Z;}else{var _eE=E(_eC);return (_eE._==0)?__Z:new T2(1,new T(function(){return B(_e5(_dV,E(_eD.a).b))-E(_eE.a)|0;}),new T(function(){return B(_eA(_eD.b,_eE.b));}));}},_eF=function(_eG){var _eH=E(_eG);if(!_eH._){return new T2(0,_H,_H);}else{var _eI=E(_eH.a),_eJ=new T(function(){var _eK=B(_eF(_eH.b));return new T2(0,_eK.a,_eK.b);});return new T2(0,new T2(1,_eI.a,new T(function(){return E(E(_eJ).a);})),new T2(1,_eI.b,new T(function(){return E(E(_eJ).b);})));}},_eL=function(_eM){var _eN=B(_eF(_eM));return new T2(0,_eN.a,_eN.b);},_eO=function(_eP,_eQ){var _eR=B(_6B(_eL,B(_7m(_eQ)))),_eS=new T(function(){return E(_eP)/8;}),_eT=new T(function(){return E(_eP)/2;}),_eU=function(_eV,_eW,_eX){var _eY=E(_eV);if(!_eY._){return __Z;}else{var _eZ=E(_eW);if(!_eZ._){return __Z;}else{var _f0=E(_eX);return (_f0._==0)?__Z:new T2(1,new T(function(){if(!B(_9m(B(_dW(B(_e5(_dV,E(_eY.a).a))-E(_eZ.a)|0)),_ez))){return E(_ey);}else{var _f1=E(_f0.a);if(_f1<=E(_eS)){return E(_ey);}else{if(_f1>=E(_eT)){return E(_ey);}else{return E(_ex);}}}}),new T(function(){return B(_eU(_eY.b,_eZ.b,_f0.b));}));}}},_f2=new T(function(){return B(_eA(_eR,new T(function(){return B(_6B(_et,_eR));},1)));},1);return new F(function(){return _eU(_eR,new T(function(){return B(_6B(_ev,_eR));},1),_f2);});},_f3=false,_f4=2,_f5=1,_f6=0,_f7=true,_f8=function(_f9){return E(E(_f9).d);},_fa=new T(function(){return B(unCStr("\n"));}),_fb=function(_fc,_fd,_){var _fe=jsWriteHandle(E(_fc),toJSStr(E(_fd)));return _4U;},_ff=function(_fg,_fh,_){var _fi=E(_fg),_fj=jsWriteHandle(_fi,toJSStr(E(_fh)));return new F(function(){return _fb(_fi,_fa,_);});},_fk=function(_fl,_fm,_fn){return new F(function(){return A1(_fl,new T2(1,_2H,new T(function(){return B(A1(_fm,_fn));})));});},_fo=new T(function(){return B(unCStr("foldr1"));}),_fp=new T(function(){return B(_e1(_fo));}),_fq=function(_fr,_fs){var _ft=E(_fs);if(!_ft._){return E(_fp);}else{var _fu=_ft.a,_fv=E(_ft.b);if(!_fv._){return E(_fu);}else{return new F(function(){return A2(_fr,_fu,new T(function(){return B(_fq(_fr,_fv));}));});}}},_fw=function(_fx,_fy){var _fz=E(_fx),_fA=new T(function(){return B(A3(_fq,_fk,new T2(1,function(_fB){return new F(function(){return _cO(0,E(_fz.a),_fB);});},new T2(1,function(_fC){return new F(function(){return _cO(0,E(_fz.b),_fC);});},_H)),new T2(1,_cM,_fy)));});return new T2(1,_cN,_fA);},_fD=function(_){return new F(function(){return jsMkStdout();});},_fE=new T(function(){return B(_3(_fD));}),_fF=function(_fG,_){return new F(function(){return _ff(_fE,B(_2K(_fw,B(_6B(_f8,_fG)),_H)),_);});},_fH=new T(function(){return eval("(function(e){return e.getContext(\'2d\');})");}),_fI=new T(function(){return eval("(function(e){return !!e.getContext;})");}),_fJ=function(_fK){return E(E(_fK).b);},_fL=function(_fM,_fN){return new F(function(){return A2(_fJ,_fM,function(_){var _fO=E(_fN),_fP=__app1(E(_fI),_fO);if(!_fP){return _0;}else{var _fQ=__app1(E(_fH),_fO);return new T1(1,new T2(0,_fQ,_fO));}});});},_fR=5,_fS=new T2(0,_fR,_fR),_fT=new T(function(){return B(unCStr("\u570b\uff1a\u3053\u304f\uff1a\u53f2\uff1a\u3057\uff1a\u4e26\uff1a\u306a\u3089\uff1a\u3079\u66ff\uff1a\u304b\uff1a\u3078\u554f\uff1a\u3082\u3093\uff1a\u984c\uff1a\u3060\u3044\uff1a\u3067\u3059\u3002\n{sm}{ch.\u554f\u984c\u3078,s0.\u30c1\u30e5\u30fc\u30c8\u30ea\u30a2\u30eb,t0}"));}),_fU=function(_fV,_fW){if(_fV<=_fW){var _fX=function(_fY){return new T2(1,_fY,new T(function(){if(_fY!=_fW){return B(_fX(_fY+1|0));}else{return __Z;}}));};return new F(function(){return _fX(_fV);});}else{return __Z;}},_fZ=0,_g0=32,_g1=new T2(0,_g0,_fZ),_g2=function(_g3,_g4,_g5){while(1){var _g6=E(_g5);if(!_g6._){return E(_g1);}else{var _g7=_g6.b,_g8=E(_g6.a),_g9=E(_g8.a);if(_g3!=E(_g9.a)){_g5=_g7;continue;}else{if(_g4!=E(_g9.b)){_g5=_g7;continue;}else{return E(_g8.b);}}}}},_ga=function(_gb,_gc){while(1){var _gd=E(_gc);if(!_gd._){return __Z;}else{var _ge=_gd.b,_gf=E(_gb);if(_gf==1){return E(_ge);}else{_gb=_gf-1|0;_gc=_ge;continue;}}}},_gg=function(_gh,_gi,_gj){var _gk=E(_gh);if(_gk==1){return E(_gj);}else{return new F(function(){return _ga(_gk-1|0,_gj);});}},_gl=function(_gm,_gn){var _go=E(_gn);if(!_go._){return __Z;}else{var _gp=_go.a,_gq=E(_gm);return (_gq==1)?new T2(1,_gp,_H):new T2(1,_gp,new T(function(){return B(_gl(_gq-1|0,_go.b));}));}},_gr=function(_gs,_gt,_gu){return new T2(1,new T(function(){if(0>=_gs){return __Z;}else{return B(_gl(_gs,new T2(1,_gt,_gu)));}}),new T(function(){if(_gs>0){return B(_gv(_gs,B(_gg(_gs,_gt,_gu))));}else{return B(_gr(_gs,_gt,_gu));}}));},_gv=function(_gw,_gx){var _gy=E(_gx);if(!_gy._){return __Z;}else{var _gz=_gy.a,_gA=_gy.b;return new T2(1,new T(function(){if(0>=_gw){return __Z;}else{return B(_gl(_gw,_gy));}}),new T(function(){if(_gw>0){return B(_gv(_gw,B(_gg(_gw,_gz,_gA))));}else{return B(_gr(_gw,_gz,_gA));}}));}},_gB=function(_gC,_gD,_gE){var _gF=_gD-1|0;if(0<=_gF){var _gG=E(_gC),_gH=function(_gI){var _gJ=new T(function(){if(_gI!=_gF){return B(_gH(_gI+1|0));}else{return __Z;}}),_gK=function(_gL){var _gM=E(_gL);return (_gM._==0)?E(_gJ):new T2(1,new T(function(){var _gN=E(_gE);if(!_gN._){return E(_g1);}else{var _gO=_gN.b,_gP=E(_gN.a),_gQ=E(_gP.a),_gR=E(_gM.a);if(_gR!=E(_gQ.a)){return B(_g2(_gR,_gI,_gO));}else{if(_gI!=E(_gQ.b)){return B(_g2(_gR,_gI,_gO));}else{return E(_gP.b);}}}}),new T(function(){return B(_gK(_gM.b));}));};return new F(function(){return _gK(B(_fU(0,_gG-1|0)));});};return new F(function(){return _gv(_gG,B(_gH(0)));});}else{return __Z;}},_gS=1,_gT=new T(function(){return B(unCStr("head"));}),_gU=new T(function(){return B(_e1(_gT));}),_gV=2,_gW=new T2(0,_gV,_gV),_gX=1,_gY=122,_gZ=new T2(0,_gY,_gX),_h0=0,_h1=new T2(0,_h0,_h0),_h2=new T2(0,_h1,_gZ),_h3=61,_h4=new T2(0,_h3,_gX),_h5=1,_h6=new T2(0,_h5,_h0),_h7=new T2(0,_h6,_h4),_h8=97,_h9=new T2(0,_h8,_fZ),_ha=4,_hb=new T2(0,_h0,_ha),_hc=new T2(0,_hb,_h9),_hd=98,_he=new T2(0,_hd,_fZ),_hf=new T2(0,_gV,_ha),_hg=new T2(0,_hf,_he),_hh=99,_hi=new T2(0,_hh,_fZ),_hj=new T2(0,_ha,_ha),_hk=new T2(0,_hj,_hi),_hl=new T2(1,_hk,_H),_hm=new T2(1,_hg,_hl),_hn=new T2(1,_hc,_hm),_ho=new T2(1,_h7,_hn),_hp=new T2(1,_h2,_ho),_hq=new T(function(){return B(unCStr("@@@@@@@@@"));}),_hr=new T(function(){var _hs=E(_hq);if(!_hs._){return E(_gU);}else{return {_:0,a:E(_gW),b:E(B(_gB(_fR,5,_hp))),c:E(_gS),d:E(_hs.a),e:32,f:0,g:E(_H),h:0,i:E(_H),j:E(_f3),k:E(_f3)};}}),_ht=0,_hu=4,_hv=new T2(0,_hu,_ht),_hw=new T2(0,_ht,_ht),_hx={_:0,a:E(_f3),b:E(_f3),c:E(_f7),d:E(_f3),e:E(_f3),f:E(_f3),g:E(_f3),h:E(_f3),i:E(_f3)},_hy=new T(function(){return {_:0,a:E(_hr),b:E(_fS),c:E(_fT),d:E(_H),e:E(_H),f:E(_H),g:E(_H),h:E(_hw),i:0,j:0,k:0,l: -1,m:E(_H),n:0,o:E(_H),p:E(_H),q:0,r:E(_H),s:E(_hv),t:0,u:E(_H),v:E(_hx),w:E(_H)};}),_hz=new T(function(){return B(unCStr("Pattern match failure in do expression at /home/yokop/Documents/haskell/haste/sp/Main.hs:49:3-9"));}),_hA=new T6(0,_0,_32,_H,_hz,_0,_0),_hB=new T(function(){return B(_30(_hA));}),_hC=new T(function(){return B(unCStr("Pattern match failure in do expression at /home/yokop/Documents/haskell/haste/sp/Main.hs:50:3-8"));}),_hD=new T6(0,_0,_32,_H,_hC,_0,_0),_hE=new T(function(){return B(_30(_hD));}),_hF=new T1(1,50),_hG=new T1(0,100),_hH=34,_hI=new T2(1,_hH,_H),_hJ=new T(function(){return B(unAppCStr("[]",_H));}),_hK=function(_hL){return E(E(_hL).a);},_hM=function(_hN){return E(E(_hN).a);},_hO=function(_hP){return E(E(_hP).b);},_hQ=function(_hR){return E(E(_hR).b);},_hS=function(_hT){return E(E(_hT).a);},_hU=function(_){return new F(function(){return nMV(_0);});},_hV=new T(function(){return B(_3(_hU));}),_hW=function(_hX){return E(E(_hX).b);},_hY=new T(function(){return eval("(function(e,name,f){e.addEventListener(name,f,false);return [f];})");}),_hZ=function(_i0){return E(E(_i0).d);},_i1=function(_i2,_i3,_i4,_i5,_i6,_i7){var _i8=B(_hK(_i2)),_i9=B(_hM(_i8)),_ia=new T(function(){return B(_fJ(_i8));}),_ib=new T(function(){return B(_hZ(_i9));}),_ic=new T(function(){return B(A1(_i3,_i5));}),_id=new T(function(){return B(A2(_hS,_i4,_i6));}),_ie=function(_if){return new F(function(){return A1(_ib,new T3(0,_id,_ic,_if));});},_ig=function(_ih){var _ii=new T(function(){var _ij=new T(function(){var _ik=__createJSFunc(2,function(_il,_){var _im=B(A2(E(_ih),_il,_));return _7;}),_in=_ik;return function(_){return new F(function(){return __app3(E(_hY),E(_ic),E(_id),_in);});};});return B(A1(_ia,_ij));});return new F(function(){return A3(_hO,_i9,_ii,_ie);});},_io=new T(function(){var _ip=new T(function(){return B(_fJ(_i8));}),_iq=function(_ir){var _is=new T(function(){return B(A1(_ip,function(_){var _=wMV(E(_hV),new T1(1,_ir));return new F(function(){return A(_hQ,[_i4,_i6,_ir,_]);});}));});return new F(function(){return A3(_hO,_i9,_is,_i7);});};return B(A2(_hW,_i2,_iq));});return new F(function(){return A3(_hO,_i9,_io,_ig);});},_it=new T(function(){return eval("(function(e){if(e){e.preventDefault();}})");}),_iu=function(_){var _iv=rMV(E(_hV)),_iw=E(_iv);if(!_iw._){var _ix=__app1(E(_it),E(_7));return new F(function(){return _4V(_);});}else{var _iy=__app1(E(_it),E(_iw.a));return new F(function(){return _4V(_);});}},_iz=new T(function(){return eval("(function(t,f){return window.setInterval(f,t);})");}),_iA=new T(function(){return eval("(function(t,f){return window.setTimeout(f,t);})");}),_iB=function(_iC,_iD,_iE){var _iF=B(_hK(_iC)),_iG=new T(function(){return B(_fJ(_iF));}),_iH=function(_iI){var _iJ=function(_){var _iK=E(_iD);if(!_iK._){var _iL=B(A1(_iI,_4U)),_iM=__createJSFunc(0,function(_){var _iN=B(A1(_iL,_));return _7;}),_iO=__app2(E(_iA),_iK.a,_iM);return new T(function(){var _iP=Number(_iO),_iQ=jsTrunc(_iP);return new T2(0,_iQ,E(_iK));});}else{var _iR=B(A1(_iI,_4U)),_iS=__createJSFunc(0,function(_){var _iT=B(A1(_iR,_));return _7;}),_iU=__app2(E(_iz),_iK.a,_iS);return new T(function(){var _iV=Number(_iU),_iW=jsTrunc(_iV);return new T2(0,_iW,E(_iK));});}};return new F(function(){return A1(_iG,_iJ);});},_iX=new T(function(){return B(A2(_hW,_iC,function(_iY){return E(_iE);}));});return new F(function(){return A3(_hO,B(_hM(_iF)),_iX,_iH);});},_iZ=new T(function(){return B(unCStr("ACK"));}),_j0=new T(function(){return B(unCStr("BEL"));}),_j1=new T(function(){return B(unCStr("BS"));}),_j2=new T(function(){return B(unCStr("SP"));}),_j3=new T2(1,_j2,_H),_j4=new T(function(){return B(unCStr("US"));}),_j5=new T2(1,_j4,_j3),_j6=new T(function(){return B(unCStr("RS"));}),_j7=new T2(1,_j6,_j5),_j8=new T(function(){return B(unCStr("GS"));}),_j9=new T2(1,_j8,_j7),_ja=new T(function(){return B(unCStr("FS"));}),_jb=new T2(1,_ja,_j9),_jc=new T(function(){return B(unCStr("ESC"));}),_jd=new T2(1,_jc,_jb),_je=new T(function(){return B(unCStr("SUB"));}),_jf=new T2(1,_je,_jd),_jg=new T(function(){return B(unCStr("EM"));}),_jh=new T2(1,_jg,_jf),_ji=new T(function(){return B(unCStr("CAN"));}),_jj=new T2(1,_ji,_jh),_jk=new T(function(){return B(unCStr("ETB"));}),_jl=new T2(1,_jk,_jj),_jm=new T(function(){return B(unCStr("SYN"));}),_jn=new T2(1,_jm,_jl),_jo=new T(function(){return B(unCStr("NAK"));}),_jp=new T2(1,_jo,_jn),_jq=new T(function(){return B(unCStr("DC4"));}),_jr=new T2(1,_jq,_jp),_js=new T(function(){return B(unCStr("DC3"));}),_jt=new T2(1,_js,_jr),_ju=new T(function(){return B(unCStr("DC2"));}),_jv=new T2(1,_ju,_jt),_jw=new T(function(){return B(unCStr("DC1"));}),_jx=new T2(1,_jw,_jv),_jy=new T(function(){return B(unCStr("DLE"));}),_jz=new T2(1,_jy,_jx),_jA=new T(function(){return B(unCStr("SI"));}),_jB=new T2(1,_jA,_jz),_jC=new T(function(){return B(unCStr("SO"));}),_jD=new T2(1,_jC,_jB),_jE=new T(function(){return B(unCStr("CR"));}),_jF=new T2(1,_jE,_jD),_jG=new T(function(){return B(unCStr("FF"));}),_jH=new T2(1,_jG,_jF),_jI=new T(function(){return B(unCStr("VT"));}),_jJ=new T2(1,_jI,_jH),_jK=new T(function(){return B(unCStr("LF"));}),_jL=new T2(1,_jK,_jJ),_jM=new T(function(){return B(unCStr("HT"));}),_jN=new T2(1,_jM,_jL),_jO=new T2(1,_j1,_jN),_jP=new T2(1,_j0,_jO),_jQ=new T2(1,_iZ,_jP),_jR=new T(function(){return B(unCStr("ENQ"));}),_jS=new T2(1,_jR,_jQ),_jT=new T(function(){return B(unCStr("EOT"));}),_jU=new T2(1,_jT,_jS),_jV=new T(function(){return B(unCStr("ETX"));}),_jW=new T2(1,_jV,_jU),_jX=new T(function(){return B(unCStr("STX"));}),_jY=new T2(1,_jX,_jW),_jZ=new T(function(){return B(unCStr("SOH"));}),_k0=new T2(1,_jZ,_jY),_k1=new T(function(){return B(unCStr("NUL"));}),_k2=new T2(1,_k1,_k0),_k3=92,_k4=new T(function(){return B(unCStr("\\DEL"));}),_k5=new T(function(){return B(unCStr("\\a"));}),_k6=new T(function(){return B(unCStr("\\\\"));}),_k7=new T(function(){return B(unCStr("\\SO"));}),_k8=new T(function(){return B(unCStr("\\r"));}),_k9=new T(function(){return B(unCStr("\\f"));}),_ka=new T(function(){return B(unCStr("\\v"));}),_kb=new T(function(){return B(unCStr("\\n"));}),_kc=new T(function(){return B(unCStr("\\t"));}),_kd=new T(function(){return B(unCStr("\\b"));}),_ke=function(_kf,_kg){if(_kf<=127){var _kh=E(_kf);switch(_kh){case 92:return new F(function(){return _1J(_k6,_kg);});break;case 127:return new F(function(){return _1J(_k4,_kg);});break;default:if(_kh<32){var _ki=E(_kh);switch(_ki){case 7:return new F(function(){return _1J(_k5,_kg);});break;case 8:return new F(function(){return _1J(_kd,_kg);});break;case 9:return new F(function(){return _1J(_kc,_kg);});break;case 10:return new F(function(){return _1J(_kb,_kg);});break;case 11:return new F(function(){return _1J(_ka,_kg);});break;case 12:return new F(function(){return _1J(_k9,_kg);});break;case 13:return new F(function(){return _1J(_k8,_kg);});break;case 14:return new F(function(){return _1J(_k7,new T(function(){var _kj=E(_kg);if(!_kj._){return __Z;}else{if(E(_kj.a)==72){return B(unAppCStr("\\&",_kj));}else{return E(_kj);}}},1));});break;default:return new F(function(){return _1J(new T2(1,_k3,new T(function(){return B(_6o(_k2,_ki));})),_kg);});}}else{return new T2(1,_kh,_kg);}}}else{var _kk=new T(function(){var _kl=jsShowI(_kf);return B(_1J(fromJSStr(_kl),new T(function(){var _km=E(_kg);if(!_km._){return __Z;}else{var _kn=E(_km.a);if(_kn<48){return E(_km);}else{if(_kn>57){return E(_km);}else{return B(unAppCStr("\\&",_km));}}}},1)));});return new T2(1,_k3,_kk);}},_ko=new T(function(){return B(unCStr("\\\""));}),_kp=function(_kq,_kr){var _ks=E(_kq);if(!_ks._){return E(_kr);}else{var _kt=_ks.b,_ku=E(_ks.a);if(_ku==34){return new F(function(){return _1J(_ko,new T(function(){return B(_kp(_kt,_kr));},1));});}else{return new F(function(){return _ke(_ku,new T(function(){return B(_kp(_kt,_kr));}));});}}},_kv=new T2(1,_2I,_H),_kw=function(_kx){var _ky=E(_kx);if(!_ky._){return E(_kv);}else{var _kz=new T(function(){return B(_2K(_fw,_ky.a,new T(function(){return B(_kw(_ky.b));})));});return new T2(1,_2H,_kz);}},_kA=2,_kB=new T(function(){return B(_6o(_6y,3));}),_kC=function(_kD,_kE){return new F(function(){return _eO(E(E(_kD).a).b,_kE);});},_kF=function(_,_kG){var _kH=E(_kG);if(!_kH._){return new F(function(){return die(_hB);});}else{var _kI=_kH.a,_kJ=B(A3(_fL,_4H,_kI,_)),_kK=E(_kJ);if(!_kK._){return new F(function(){return die(_hE);});}else{var _kL=E(_kK.a),_kM=_kL.a,_kN=_kL.b,_kO=B(_4N(_kN,_)),_kP=_kO,_kQ=nMV(_hy),_kR=_kQ,_kS=B(A(_i1,[_4I,_8,_3X,_kI,_f6,function(_kT,_){var _kU=B(_fF(E(_kT).a,_)),_kV=rMV(_kR),_kW=E(_kV),_kX=_kW.a,_kY=_kW.b,_kZ=_kW.c,_l0=_kW.d,_l1=_kW.e,_l2=_kW.f,_l3=_kW.g,_l4=_kW.h,_l5=_kW.i,_l6=_kW.j,_l7=_kW.k,_l8=_kW.l,_l9=_kW.m,_la=_kW.n,_lb=_kW.o,_lc=_kW.p,_ld=_kW.q,_le=_kW.r,_lf=_kW.s,_lg=_kW.t,_lh=_kW.w,_li=E(_kW.v);if(!E(_li.e)){var _=wMV(_kR,{_:0,a:E(_kX),b:E(_kY),c:E(_kZ),d:E(_l0),e:E(_l1),f:E(_l2),g:E(_l3),h:E(_l4),i:_l5,j:_l6,k:_l7,l:_l8,m:E(_l9),n:_la,o:E(_lb),p:E(_lc),q:_ld,r:E(_le),s:E(_lf),t:_lg,u:E(_H),v:E(_li),w:E(_lh)});return _4U;}else{var _lj=B(_iu(_)),_=wMV(_kR,{_:0,a:E(_kX),b:E(_kY),c:E(_kZ),d:E(_l0),e:E(_l1),f:E(_l2),g:E(_l3),h:E(_l4),i:_l5,j:_l6,k:_l7,l:_l8,m:E(_l9),n:_la,o:E(_lb),p:E(_lc),q:_ld,r:E(_le),s:E(_lf),t:_lg,u:E(_H),v:E(_li),w:E(_lh)});return _4U;}},_])),_lk=function(_ll,_){var _lm=E(_ll).a,_ln=B(_fF(_lm,_)),_lo=rMV(_kR),_lp=new T(function(){var _lq=E(_lo);return {_:0,a:E(_lq.a),b:E(_lq.b),c:E(_lq.c),d:E(_lq.d),e:E(_lq.e),f:E(_lq.f),g:E(_lq.g),h:E(_lq.h),i:_lq.i,j:_lq.j,k:_lq.k,l:_lq.l,m:E(_lq.m),n:_lq.n,o:E(_lq.o),p:E(_lq.p),q:_lq.q,r:E(_lq.r),s:E(_lq.s),t:_lq.t,u:E(B(_1J(_lq.u,new T2(1,new T(function(){return B(_6B(_f8,_lm));}),_H)))),v:E(_lq.v),w:E(_lq.w)};}),_=wMV(_kR,_lp);return _4U;},_lr=B(A(_i1,[_4I,_8,_3X,_kI,_f5,_lk,_])),_ls=function(_lt,_){var _lu=E(_lt),_lv=rMV(_kR),_lw=E(_lv),_lx=_lw.a,_ly=_lw.b,_lz=_lw.c,_lA=_lw.d,_lB=_lw.e,_lC=_lw.f,_lD=_lw.g,_lE=_lw.h,_lF=_lw.i,_lG=_lw.j,_lH=_lw.k,_lI=_lw.l,_lJ=_lw.m,_lK=_lw.n,_lL=_lw.o,_lM=_lw.p,_lN=_lw.q,_lO=_lw.r,_lP=_lw.s,_lQ=_lw.t,_lR=_lw.u,_lS=_lw.v,_lT=_lw.w,_lU=function(_){var _lV=E(_lR);if(!_lV._){var _=wMV(_kR,new T(function(){var _lW=E(_lS);return {_:0,a:E(_lx),b:E(_ly),c:E(_lz),d:E(_lA),e:E(_lB),f:E(_lC),g:E(_lD),h:E(_lE),i:_lF,j:_lG,k:_lH,l:_lI,m:E(_lJ),n:_lK,o:E(_lL),p:E(_lM),q:_lN,r:E(_lO),s:E(_lP),t:_lQ,u:E(_H),v:E({_:0,a:E(_lW.a),b:E(_lW.b),c:E(_lW.c),d:E(_lW.d),e:E(_f7),f:E(_lW.f),g:E(_lW.g),h:E(_lW.h),i:E(_lW.i)}),w:E(_lT)};})),_lX=function(_){var _lY=rMV(_kR),_=wMV(_kR,new T(function(){var _lZ=E(_lY),_m0=E(_lZ.v);return {_:0,a:E(_lZ.a),b:E(_lZ.b),c:E(_lZ.c),d:E(_lZ.d),e:E(_lZ.e),f:E(_lZ.f),g:E(_lZ.g),h:E(_lZ.h),i:_lZ.i,j:_lZ.j,k:_lZ.k,l:_lZ.l,m:E(_lZ.m),n:_lZ.n,o:E(_lZ.o),p:E(_lZ.p),q:_lZ.q,r:E(_lZ.r),s:E(_lZ.s),t:_lZ.t,u:E(_lZ.u),v:E({_:0,a:E(_m0.a),b:E(_m0.b),c:E(_m0.c),d:E(_m0.d),e:E(_f3),f:E(_m0.f),g:E(_m0.g),h:E(_m0.h),i:E(_m0.i)}),w:E(_lZ.w)};}));return _4U;},_m1=B(A(_iB,[_4I,_hG,_lX,_]));return _4U;}else{var _m2=B(_ff(_fE,new T2(1,_hH,new T(function(){return B(_kp(B(_eO(E(E(_kP).a).b,_lV)),_hI));})),_)),_m3=B(A(_da,[_kM,_kB,_kA,_kA,B(_eO(E(E(_kP).a).b,_lV)),_])),_=wMV(_kR,new T(function(){var _m4=E(_lS);return {_:0,a:E(_lx),b:E(_ly),c:E(_lz),d:E(_lA),e:E(_lB),f:E(_lC),g:E(_lD),h:E(_lE),i:_lF,j:_lG,k:_lH,l:_lI,m:E(_lJ),n:_lK,o:E(_lL),p:E(_lM),q:_lN,r:E(_lO),s:E(_lP),t:_lQ,u:E(_lV),v:E({_:0,a:E(_m4.a),b:E(_m4.b),c:E(_m4.c),d:E(_m4.d),e:E(_f7),f:E(_m4.f),g:E(_m4.g),h:E(_m4.h),i:E(_m4.i)}),w:E(_lT)};})),_m5=function(_){var _m6=rMV(_kR),_=wMV(_kR,new T(function(){var _m7=E(_m6),_m8=E(_m7.v);return {_:0,a:E(_m7.a),b:E(_m7.b),c:E(_m7.c),d:E(_m7.d),e:E(_m7.e),f:E(_m7.f),g:E(_m7.g),h:E(_m7.h),i:_m7.i,j:_m7.j,k:_m7.k,l:_m7.l,m:E(_m7.m),n:_m7.n,o:E(_m7.o),p:E(_m7.p),q:_m7.q,r:E(_m7.r),s:E(_m7.s),t:_m7.t,u:E(_m7.u),v:E({_:0,a:E(_m8.a),b:E(_m8.b),c:E(_m8.c),d:E(_m8.d),e:E(_f3),f:E(_m8.f),g:E(_m8.g),h:E(_m8.h),i:E(_m8.i)}),w:E(_m7.w)};}));return _4U;},_m9=B(A(_iB,[_4I,_hG,_m5,_]));return _4U;}},_ma=E(_lR);if(!_ma._){var _mb=B(_ff(_fE,_hJ,_));return new F(function(){return _lU(_);});}else{var _mc=new T(function(){return B(_2K(_fw,_ma.a,new T(function(){return B(_kw(_ma.b));})));}),_md=B(_ff(_fE,new T2(1,_2J,_mc),_));return new F(function(){return _lU(_);});}},_me=B(A(_i1,[_4I,_8,_3X,_kI,_f4,_ls,_])),_mf=function(_){var _mg=rMV(_kR),_mh=new T(function(){var _mi=E(_mg),_mj=_mi.a,_mk=_mi.b,_ml=_mi.c,_mm=_mi.d,_mn=_mi.e,_mo=_mi.f,_mp=_mi.g,_mq=_mi.h,_mr=_mi.i,_ms=_mi.j,_mt=_mi.k,_mu=_mi.l,_mv=_mi.m,_mw=_mi.n,_mx=_mi.o,_my=_mi.p,_mz=_mi.q,_mA=_mi.r,_mB=_mi.s,_mC=_mi.t,_mD=_mi.u,_mE=_mi.v,_mF=_mi.w;if(_mC<=298){return {_:0,a:E(_mj),b:E(_mk),c:E(_ml),d:E(_mm),e:E(_mn),f:E(_mo),g:E(_mp),h:E(_mq),i:_mr,j:_ms,k:_mt,l:_mu,m:E(_mv),n:_mw,o:E(_mx),p:E(_my),q:_mz,r:E(_mA),s:E(_mB),t:_mC+1|0,u:E(_mD),v:E(_mE),w:E(_mF)};}else{return {_:0,a:E(_mj),b:E(_mk),c:E(_ml),d:E(_mm),e:E(_mn),f:E(_mo),g:E(_mp),h:E(_mq),i:_mr,j:_ms,k:_mt,l:_mu,m:E(_mv),n:_mw,o:E(_mx),p:E(_my),q:_mz,r:E(_mA),s:E(_mB),t:0,u:E(_mD),v:E(_mE),w:E(_mF)};}}),_mG=new T(function(){return E(E(_mh).u);}),_mH=B(_7u(_kM,_kN,_mG,_)),_mI=B(A(_da,[_kM,_kB,_kA,_kA,B(_kC(_kP,_mG)),_])),_=wMV(_kR,_mh);return _4U;},_mJ=B(A(_iB,[_4I,_hF,_mf,_]));return _4U;}}},_mK=function(_mL){return new T1(1,E(_mL));},_mM=function(_mN,_mO){return new F(function(){return A2(_hZ,B(_hM(_mN)),new T1(1,_mO));});},_mP=new T2(0,_4F,_mM),_mQ="auto",_mR="metadata",_mS="none",_mT=new T(function(){return new T1(0,"preload");}),_mU=new T(function(){return eval("(function(t){return document.createElement(t);})");}),_mV=function(_){return new F(function(){return __app1(E(_mU),"source");});},_mW=new T(function(){return new T1(0,"src");}),_mX="audio/wav",_mY="audio/ogg",_mZ="audio/mpeg",_n0=new T(function(){return new T1(0,"type");}),_n1=function(_n2){return E(E(_n2).c);},_n3=new T(function(){return eval("(function(c,p){p.appendChild(c);})");}),_n4=function(_n5){return E(E(_n5).a);},_n6=new T(function(){return eval("(function(e,p,v){e.setAttribute(p, v);})");}),_n7=new T(function(){return eval("(function(e,p,v){e.style[p] = v;})");}),_n8=function(_n9,_na,_nb,_nc){var _nd=new T(function(){return B(A2(_n4,_n9,_nb));}),_ne=function(_nf,_){var _ng=E(_nf);if(!_ng._){return _4U;}else{var _nh=E(_nd),_ni=E(_n3),_nj=__app2(_ni,E(_ng.a),_nh),_nk=function(_nl,_){while(1){var _nm=E(_nl);if(!_nm._){return _4U;}else{var _nn=__app2(_ni,E(_nm.a),_nh);_nl=_nm.b;continue;}}};return new F(function(){return _nk(_ng.b,_);});}},_no=function(_np,_){while(1){var _nq=B((function(_nr,_){var _ns=E(_nr);if(!_ns._){return _4U;}else{var _nt=_ns.b,_nu=E(_ns.a);if(!_nu._){var _nv=_nu.b,_nw=E(_nu.a);switch(_nw._){case 0:var _nx=E(_nd),_ny=E(_5k),_nz=__app3(_ny,_nx,_nw.a,_nv),_nA=function(_nB,_){while(1){var _nC=E(_nB);if(!_nC._){return _4U;}else{var _nD=_nC.b,_nE=E(_nC.a);if(!_nE._){var _nF=_nE.b,_nG=E(_nE.a);switch(_nG._){case 0:var _nH=__app3(_ny,_nx,_nG.a,_nF);_nB=_nD;continue;case 1:var _nI=__app3(E(_n7),_nx,_nG.a,_nF);_nB=_nD;continue;default:var _nJ=__app3(E(_n6),_nx,_nG.a,_nF);_nB=_nD;continue;}}else{var _nK=B(_ne(_nE.a,_));_nB=_nD;continue;}}}};return new F(function(){return _nA(_nt,_);});break;case 1:var _nL=E(_nd),_nM=E(_n7),_nN=__app3(_nM,_nL,_nw.a,_nv),_nO=function(_nP,_){while(1){var _nQ=E(_nP);if(!_nQ._){return _4U;}else{var _nR=_nQ.b,_nS=E(_nQ.a);if(!_nS._){var _nT=_nS.b,_nU=E(_nS.a);switch(_nU._){case 0:var _nV=__app3(E(_5k),_nL,_nU.a,_nT);_nP=_nR;continue;case 1:var _nW=__app3(_nM,_nL,_nU.a,_nT);_nP=_nR;continue;default:var _nX=__app3(E(_n6),_nL,_nU.a,_nT);_nP=_nR;continue;}}else{var _nY=B(_ne(_nS.a,_));_nP=_nR;continue;}}}};return new F(function(){return _nO(_nt,_);});break;default:var _nZ=E(_nd),_o0=E(_n6),_o1=__app3(_o0,_nZ,_nw.a,_nv),_o2=function(_o3,_){while(1){var _o4=E(_o3);if(!_o4._){return _4U;}else{var _o5=_o4.b,_o6=E(_o4.a);if(!_o6._){var _o7=_o6.b,_o8=E(_o6.a);switch(_o8._){case 0:var _o9=__app3(E(_5k),_nZ,_o8.a,_o7);_o3=_o5;continue;case 1:var _oa=__app3(E(_n7),_nZ,_o8.a,_o7);_o3=_o5;continue;default:var _ob=__app3(_o0,_nZ,_o8.a,_o7);_o3=_o5;continue;}}else{var _oc=B(_ne(_o6.a,_));_o3=_o5;continue;}}}};return new F(function(){return _o2(_nt,_);});}}else{var _od=B(_ne(_nu.a,_));_np=_nt;return __continue;}}})(_np,_));if(_nq!=__continue){return _nq;}}};return new F(function(){return A2(_fJ,_na,function(_){return new F(function(){return _no(_nc,_);});});});},_oe=function(_of,_og,_oh,_oi){var _oj=B(_hM(_og)),_ok=function(_ol){return new F(function(){return A3(_n1,_oj,new T(function(){return B(_n8(_of,_og,_ol,_oi));}),new T(function(){return B(A2(_hZ,_oj,_ol));}));});};return new F(function(){return A3(_hO,_oj,_oh,_ok);});},_om=function(_on,_){var _oo=E(_on);if(!_oo._){return _H;}else{var _op=E(_oo.a),_oq=B(A(_oe,[_mP,_4H,_mV,new T2(1,new T(function(){var _or=E(_n0);switch(E(_op.a)){case 0:return new T2(0,E(_or),E(_mZ));break;case 1:return new T2(0,E(_or),E(_mY));break;default:return new T2(0,E(_or),E(_mX));}}),new T2(1,new T(function(){return new T2(0,E(_mW),_op.b);}),_H)),_])),_os=B(_om(_oo.b,_));return new T2(1,_oq,_os);}},_ot=new T(function(){return new T1(0,"volume");}),_ou=new T(function(){return new T1(0,"muted");}),_ov=new T(function(){return new T1(0,"loop");}),_ow=new T(function(){return new T1(0,"autoplay");}),_ox="true",_oy=new T(function(){return toJSStr(_H);}),_oz=new T(function(){return new T1(0,"controls");}),_oA=function(_){return new F(function(){return __app1(E(_mU),"audio");});},_oB=function(_oC,_oD,_oE){var _oF=function(_){var _oG=B(_om(_oE,_)),_oH=B(A(_oe,[_mP,_4H,_oA,new T2(1,new T(function(){var _oI=E(_oz);if(!E(E(_oD).a)){return new T2(0,E(_oI),E(_oy));}else{return new T2(0,E(_oI),E(_ox));}}),new T2(1,new T(function(){var _oJ=E(_ow);if(!E(E(_oD).b)){return new T2(0,E(_oJ),E(_oy));}else{return new T2(0,E(_oJ),E(_ox));}}),new T2(1,new T(function(){var _oK=E(_ov);if(!E(E(_oD).c)){return new T2(0,E(_oK),E(_oy));}else{return new T2(0,E(_oK),E(_ox));}}),new T2(1,new T(function(){var _oL=E(_ou);if(!E(E(_oD).e)){return new T2(0,E(_oL),E(_oy));}else{return new T2(0,E(_oL),E(_ox));}}),new T2(1,new T(function(){var _oM=String(E(_oD).f);return new T2(0,E(_ot),_oM);}),new T2(1,new T(function(){var _oN=E(_mT);switch(E(E(_oD).d)){case 0:return new T2(0,E(_oN),E(_mS));break;case 1:return new T2(0,E(_oN),E(_mR));break;default:return new T2(0,E(_oN),E(_mQ));}}),new T2(1,new T(function(){return B(_mK(_oG));}),_H))))))),_]));return new T1(0,_oH);};return new F(function(){return A2(_fJ,_oC,_oF);});},_oO=new T(function(){return B(unCStr("vaw"));}),_oP=new T(function(){return B(unCStr("ggo"));}),_oQ=new T(function(){return B(unCStr("3pm"));}),_oR=0,_oS=1,_oT=2,_oU=function(_oV,_oW){while(1){var _oX=E(_oV);if(!_oX._){return (E(_oW)._==0)?true:false;}else{var _oY=E(_oW);if(!_oY._){return false;}else{if(E(_oX.a)!=E(_oY.a)){return false;}else{_oV=_oX.b;_oW=_oY.b;continue;}}}}},_oZ=function(_p0,_p1){while(1){var _p2=E(_p0);if(!_p2._){return E(_p1);}else{var _p3=new T2(1,_p2.a,_p1);_p0=_p2.b;_p1=_p3;continue;}}},_p4=function(_p5){var _p6=B(_gl(3,B(_oZ(fromJSStr(_p5),_H))));return (!B(_oU(_p6,_oQ)))?(!B(_oU(_p6,_oP)))?(!B(_oU(_p6,_oO)))?__Z:new T1(1,new T2(0,E(_oT),_p5)):new T1(1,new T2(0,E(_oS),_p5)):new T1(1,new T2(0,E(_oR),_p5));},_p7="Audio/test.mp3",_p8=new T(function(){return B(unCStr("Irrefutable pattern failed for pattern"));}),_p9=function(_pa){return new F(function(){return _9Y(new T1(0,new T(function(){return B(_ab(_pa,_p8));})),_9I);});},_pb=new T(function(){var _pc=B(_p4(E(_p7)));if(!_pc._){return B(_p9("Browser.hs:99:7-37|Just adSrc"));}else{return E(_pc.a);}}),_pd=new T2(1,_pb,_H),_pe=2,_pf=new T6(0,E(_f3),E(_f3),E(_f7),E(_pe),E(_f3),1),_pg=new T(function(){return B(_oB(_4H,_pf,_pd));}),_ph="src",_pi=new T(function(){return B(unCStr("img"));}),_pj=function(_pk,_pl){return new F(function(){return A2(_fJ,_pk,function(_){var _pm=__app1(E(_mU),toJSStr(E(_pi))),_pn=__app3(E(_5k),_pm,E(_ph),E(_pl));return _pm;});});},_po=new T(function(){return B(unCStr(".png"));}),_pp=function(_pq,_pr){var _ps=E(_pq);if(_ps==( -1)){return __Z;}else{var _pt=new T(function(){var _pu=new T(function(){return toJSStr(B(_1J(_pr,new T(function(){return B(_1J(B(_cO(0,_ps,_H)),_po));},1))));});return B(_pj(_4H,_pu));});return new F(function(){return _1J(B(_pp(_ps-1|0,_pr)),new T2(1,_pt,_H));});}},_pv=new T(function(){return B(unCStr("Images/Wst/wst"));}),_pw=new T(function(){return B(_pp(120,_pv));}),_px=function(_py,_){var _pz=E(_py);if(!_pz._){return _H;}else{var _pA=B(A1(_pz.a,_)),_pB=B(_px(_pz.b,_));return new T2(1,_pA,_pB);}},_pC=new T(function(){return B(unCStr("Images/Chara/ch"));}),_pD=new T(function(){return B(_pp(56,_pC));}),_pE=function(_pF,_){var _pG=E(_pF);if(!_pG._){return _H;}else{var _pH=B(A1(_pG.a,_)),_pI=B(_pE(_pG.b,_));return new T2(1,_pH,_pI);}},_pJ=new T(function(){return B(unCStr("Images/img"));}),_pK=new T(function(){return B(_pp(5,_pJ));}),_pL=function(_pM,_){var _pN=E(_pM);if(!_pN._){return _H;}else{var _pO=B(A1(_pN.a,_)),_pP=B(_pL(_pN.b,_));return new T2(1,_pO,_pP);}},_pQ=function(_){var _pR=B(_pL(_pK,_)),_pS=B(_pE(_pD,_)),_pT=B(_px(_pw,_)),_pU=B(A1(_pg,_)),_pV=__app1(E(_1),"canvas"),_pW=__eq(_pV,E(_7));if(!E(_pW)){var _pX=__isUndef(_pV);if(!E(_pX)){return new F(function(){return _kF(_,new T1(1,_pV));});}else{return new F(function(){return _kF(_,_0);});}}else{return new F(function(){return _kF(_,_0);});}},_pY=function(_){return new F(function(){return _pQ(_);});};
var hasteMain = function() {B(A(_pY, [0]));};window.onload = hasteMain;