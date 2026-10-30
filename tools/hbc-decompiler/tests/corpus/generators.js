function* range(a, b) { for (var i = a; i < b; i++) yield i; }
print([...range(0, 5)].join());
function* withReturn() { var x = yield 1; print("got", x); try { yield 2; } finally { print("cleanup"); } return 3; }
var g = withReturn();
print(JSON.stringify(g.next()), JSON.stringify(g.next("hello")), JSON.stringify(g.return(9)), JSON.stringify(g.next()));
function* delegating() { yield 0; yield* range(1, 3); yield 3; }
print([...delegating()].join());
function* fibs() { var a = 0, b = 1; while (true) { yield a; [a, b] = [b, a + b]; } }
var out = []; for (var v of fibs()) { if (v > 50) break; out.push(v); }
print(out.join());
var obj = { *[Symbol.iterator]() { yield "x"; yield "y"; } };
print([...obj].join());
function* thrower() { try { yield 1; } catch (e) { yield "caught " + e; } }
var t = thrower(); t.next(); print(t.throw("err").value);
async function af(x) { var a = await x; var b = await Promise.resolve(a + 1); return a + b; }
af(1).then(v => print("async", v));
async function aerr() { try { await Promise.reject(new Error("rej")); } catch (e) { return "handled " + e.message; } }
aerr().then(print);
var arrow = async () => { var r = []; for (var i = 0; i < 3; i++) r.push(await i); return r.join(); };
arrow().then(v => print("arrow", v));
async function seq() { var s = 0; for (const p of [Promise.resolve(1), 2, Promise.resolve(3)]) s += await p; return s; }
seq().then(v => print("seq", v));
