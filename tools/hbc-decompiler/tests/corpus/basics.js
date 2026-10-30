function Foo(x) { this.x = x; }
Foo.prototype.get = function() { return this.x; };
var o = new Foo(3);
var arr = [1, 2, "three", null];
var obj = {a: 1, b: "s", c: true};
function sw(v) { switch (v) { case 1: return "one"; case 2: return "two"; case 3: return "3"; case 4: return 4; default: return "d"; } }
function ssw(v) { switch (v) { case "a": return 1; case "b": return 2; case "c": return 3; case "d": return 4; } return 0; }
function loop(n) { var s = 0; for (var i = 0; i < n; i++) { if (i % 2) continue; s += i; } return s; }
function tc() { try { throw new Error("x"); } catch (e) { return e.message; } finally { print("fin"); } }
function* gen() { yield 1; yield 2; }
async function as() { await 1; return 2; }
function counter() { let c = 0; return () => ++c; }
var re = /ab+c/gi;
var big = 123n;
for (var k in obj) print(k);
for (var v of arr) print(v);
print(o.get(), sw(2), ssw("c"), loop(10), tc(), counter()(), re, big, [...gen()]);
