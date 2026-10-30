// Runtime helpers for decompiled Hermes bytecode. These implement Hermes VM
// operations that have no direct JavaScript syntax equivalent.
var $hbc = (function () {
  "use strict";
  var H = {};
  var hasOwn = Object.prototype.hasOwnProperty;
  function isObject(v) {
    return v !== null && (typeof v === "object" || typeof v === "function");
  }

  // ---- generators & async functions -------------------------------------
  // `impl(action, value)` is the lowered generator body; action is
  // 0 (next), 1 (throw) or 2 (return). It returns {value, done}.
  var GeneratorProto = {
    next: function (v) {
      return this.$impl.call(this.$impl, 0, v);
    },
    throw: function (e) {
      return this.$impl.call(this.$impl, 1, e);
    },
    return: function (v) {
      return this.$impl.call(this.$impl, 2, v);
    },
  };
  if (typeof Symbol === "function") {
    GeneratorProto[Symbol.iterator] = function () {
      return this;
    };
    if (Symbol.toStringTag) GeneratorProto[Symbol.toStringTag] = "Generator";
  }
  H.createGenerator = function (impl) {
    var g = Object.create(GeneratorProto);
    Object.defineProperty(g, "$impl", { value: impl });
    return g;
  };
  H.spawnAsync = function (genF, self, args) {
    return new Promise(function (resolve, reject) {
      var gen = genF.apply(self, args);
      function step(nextF) {
        var next;
        try {
          next = nextF();
        } catch (e) {
          reject(e);
          return;
        }
        if (next.done) {
          resolve(next.value);
          return;
        }
        Promise.resolve(next.value).then(
          function (v) {
            step(function () {
              return gen.next(v);
            });
          },
          function (e) {
            step(function () {
              return gen.throw(e);
            });
          }
        );
      }
      step(function () {
        return gen.next(undefined);
      });
    });
  };
  H.makeAsyncIterator = function (iterable) {
    if (iterable[Symbol.asyncIterator]) return iterable[Symbol.asyncIterator]();
    var it = iterable[Symbol.iterator]();
    function wrap(r) {
      if (r.done) return Promise.resolve(r);
      return Promise.resolve(r.value).then(function (v) {
        return { done: false, value: v };
      });
    }
    return {
      next: function (v) {
        return wrap(it.next(v));
      },
      return: function (v) {
        return wrap(typeof it.return === "function" ? it.return(v) : { done: true, value: v });
      },
      throw: function (e) {
        if (typeof it.throw === "function") return wrap(it.throw(e));
        return Promise.reject(e);
      },
    };
  };

  // ---- iteration ---------------------------------------------------------
  H.iterBegin = function (src) {
    var it = src[Symbol.iterator]();
    if (!isObject(it)) throw new TypeError("iterator is not an object");
    return { it: it, next: it.next, done: false };
  };
  H.iterNext = function (rec) {
    if (rec === undefined || rec.done) return undefined;
    var r = rec.next.call(rec.it);
    if (!isObject(r)) throw new TypeError("iterator result is not an object");
    if (r.done) {
      rec.done = true;
      return undefined;
    }
    return r.value;
  };
  H.iterAlive = function (rec) {
    return rec === undefined || rec.done ? undefined : rec;
  };
  H.iterClose = function (rec, ignoreInnerException) {
    if (rec === undefined || rec.done) return;
    var ret = rec.it["return"];
    if (ret === undefined || ret === null) return;
    if (ignoreInnerException) {
      try {
        ret.call(rec.it);
      } catch (e) {}
      return;
    }
    var r = ret.call(rec.it);
    if (!isObject(r)) throw new TypeError("iterator.return() did not return an object");
  };
  H.forInBegin = function (obj) {
    if (obj === undefined || obj === null) return undefined;
    var o = Object(obj);
    var keys = [];
    for (var k in o) keys.push(k);
    return { o: o, k: keys, i: 0 };
  };
  H.forInNext = function (st) {
    while (st.i < st.k.length) {
      var k = st.k[st.i++];
      if (k in st.o) return k;
    }
    return undefined;
  };

  // ---- calls, construction & classes ----------------------------------------
  H.construct = function (F, self, args) {
    return Reflect.construct(F, args);
  };
  H.createThis = function (F) {
    var p = F.prototype;
    return Object.create(isObject(p) ? p : Object.prototype);
  };
  H.selectObject = function (self, ret) {
    return isObject(ret) ? ret : self;
  };
  H.createThisForSuper = function (F, newTarget) {
    return undefined;
  };
  H.callWithNewTarget = function (fn, newTarget, self, args) {
    if (newTarget === undefined) return Reflect.apply(fn, self, args);
    return Reflect.construct(fn, args, newTarget);
  };
  H.createClass = function (ctor, superClass) {
    if (superClass !== undefined) {
      if (superClass !== null && typeof superClass !== "function")
        throw new TypeError("Class extends value is not a constructor or null");
      var parentProto = superClass === null ? null : superClass.prototype;
      if (parentProto !== null && !isObject(parentProto))
        throw new TypeError("Class extends value does not have valid prototype property");
      ctor.prototype = Object.create(parentProto, {
        constructor: { value: ctor, writable: true, configurable: true },
      });
      Object.setPrototypeOf(ctor, superClass === null ? Function.prototype : superClass);
    }
    Object.defineProperty(ctor, "prototype", { writable: false });
    return ctor;
  };
  H.throwIfUndefined = function (v) {
    if (v === undefined) throw new ReferenceError("accessing an uninitialized variable");
    return v;
  };
  H.throwIfThisInitialized = function (v) {
    if (v !== undefined) throw new ReferenceError("super() called twice in derived constructor");
  };
  H.putWithReceiver = function (o, k, v, r) {
    Reflect.set(o, k, v, r);
  };
  H.putWithReceiverStrict = function (o, k, v, r) {
    if (!Reflect.set(o, k, v, r)) throw new TypeError("Cannot assign to property");
  };
  H.getSlot = function (o, i) {
    return o[Reflect.ownKeys(o)[i]];
  };
  H.putSlot = function (o, i, v) {
    o[Reflect.ownKeys(o)[i]] = v;
  };
  H.toNumeric = function (v) {
    var p = isObject(v) ? Number(v) : v;
    return typeof p === "bigint" ? p : +p;
  };

  // ---- private class members ------------------------------------------------
  H.privateIsIn = function (sym, obj) {
    if (!isObject(obj)) throw new TypeError("right operand of 'in' is not an object");
    return hasOwn.call(obj, sym);
  };
  H.addPrivate = function (obj, sym, v) {
    if (hasOwn.call(obj, sym)) throw new TypeError("Cannot initialize private field twice");
    Object.defineProperty(obj, sym, { value: v, writable: true });
  };
  H.getPrivate = function (obj, sym) {
    if (!isObject(obj) || !hasOwn.call(obj, sym))
      throw new TypeError("Cannot read private member from an object whose class did not declare it");
    return obj[sym];
  };
  H.putPrivate = function (obj, sym, v) {
    if (!isObject(obj) || !hasOwn.call(obj, sym))
      throw new TypeError("Cannot write private member to an object whose class did not declare it");
    obj[sym] = v;
  };

  // ---- HermesBuiltin.* --------------------------------------------------------
  H.silentSetPrototypeOf = function (o, p) {
    try {
      Object.setPrototypeOf(o, p);
    } catch (e) {}
  };
  H.requireFast = function (n) {
    return globalThis.require(n);
  };
  var templateCache = {};
  H.getTemplateObject = function (id, dup) {
    if (hasOwn.call(templateCache, id)) return templateCache[id];
    var rest = Array.prototype.slice.call(arguments, 2);
    var raw, cooked;
    if (dup) {
      raw = rest;
      cooked = rest.slice();
    } else {
      var n = rest.length / 2;
      raw = rest.slice(0, n);
      cooked = rest.slice(n);
    }
    Object.defineProperty(cooked, "raw", { value: Object.freeze(raw) });
    Object.freeze(cooked);
    templateCache[id] = cooked;
    return cooked;
  };
  H.ensureObject = function (v, msg) {
    if (!isObject(v)) throw new TypeError(msg);
  };
  H.getMethod = function (o, k) {
    var f = o[k];
    if (f === undefined || f === null) return undefined;
    if (typeof f !== "function") throw new TypeError("property is not callable");
    return f;
  };
  H.throwTypeError = function (msg) {
    throw new TypeError(msg);
  };
  H.throwReferenceError = function (msg) {
    throw new ReferenceError(msg);
  };
  H.copyDataProperties = function (target, source, excluded) {
    if (source === undefined || source === null) return target;
    var from = Object(source);
    var keys = Reflect.ownKeys(from);
    for (var i = 0; i < keys.length; i++) {
      var k = keys[i];
      if (excluded !== undefined && hasOwn.call(excluded, k)) continue;
      var d = Object.getOwnPropertyDescriptor(from, k);
      if (d && d.enumerable) {
        Object.defineProperty(target, k, {
          value: from[k],
          writable: true,
          enumerable: true,
          configurable: true,
        });
      }
    }
    return target;
  };
  H.arraySpread = function (target, source, nextIndex) {
    var it = source[Symbol.iterator]();
    for (;;) {
      var r = it.next();
      if (r.done) return nextIndex;
      Object.defineProperty(target, nextIndex++, {
        value: r.value,
        writable: true,
        enumerable: true,
        configurable: true,
      });
    }
  };
  H.apply = function (fn, argArray, thisVal) {
    if (arguments.length < 3) return Reflect.construct(fn, argArray);
    return Reflect.apply(fn, thisVal, argArray);
  };
  H.applyArguments = function (fn, thisVal, newTarget, args) {
    if (args === undefined) {
      args = newTarget;
      newTarget = undefined;
    }
    if (newTarget !== undefined) return Reflect.construct(fn, args, newTarget);
    return Reflect.apply(fn, thisVal, args);
  };
  H.applyWithNewTarget = function (fn, argArray, thisVal, newTarget) {
    return Reflect.construct(fn, argArray, newTarget);
  };
  H.exportAll = function (exports, source) {
    Object.keys(source).forEach(function (k) {
      if (k === "default" || hasOwn.call(exports, k)) return;
      Object.defineProperty(exports, k, {
        enumerable: true,
        get: function () {
          return source[k];
        },
      });
    });
  };
  H.exponentiationOperator = function (a, b) {
    return Math.pow(a, b);
  };
  H.initRegexNamedGroups = function (re, groups) {};
  H.functionPrototypeApply = Function.prototype.apply;
  H.functionPrototypeCall = Function.prototype.call;
  return H;
})();
