function makeCounter() { var c = 0; return { inc: function () { return ++c; }, get: function () { return c; } }; }
var c1 = makeCounter(), c2 = makeCounter();
c1.inc(); c1.inc(); c2.inc();
print(c1.get(), c2.get());
var fns = [];
for (let i = 0; i < 3; i++) fns.push(() => i);
print(fns.map(f => f()).join());
var fns2 = [];
for (var j = 0; j < 3; j++) fns2.push(function () { return j; });
print(fns2.map(f => f()).join());
function outer(a) {
  return function mid(b) {
    return function inner(c) { return a + b + c; };
  };
}
print(outer(1)(2)(3));
function adder(x) { return y => z => x * 100 + y * 10 + z; }
print(adder(1)(2)(3));
var self = { name: "obj", arrow() { return [1].map(() => this.name); }, reg() { return this.name; } };
print(self.arrow(), self.reg());
function fib(n) { return n < 2 ? n : fib(n - 1) + fib(n - 2); }
print(fib(15));
var memo = (function () { var cache = {}; return function sq(n) { if (n in cache) return "hit" + cache[n]; return cache[n] = n * n; }; })();
print(memo(4), memo(4));
function blockScopes() {
  var out = [];
  for (let i = 0; i < 2; i++) {
    let k = i * 10;
    out.push(() => k + i);
  }
  { let z = 5; out.push(() => z); }
  return out.map(f => f()).join();
}
print(blockScopes());
function args() { return arguments.length + ":" + Array.prototype.join.call(arguments, "-"); }
print(args(1, 2, 3), args());
function defaults(a, b = 5, ...rest) { return a + b + rest.length; }
print(defaults(1), defaults(1, 2, 3, 4));
