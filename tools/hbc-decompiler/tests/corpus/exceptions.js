function f1() { try { return "try"; } finally { print("finally1"); } }
function f2() { try { throw 1; } catch (e) { return "caught " + e; } finally { print("finally2"); } }
function f3() { for (var i = 0; i < 3; i++) { try { if (i === 1) continue; if (i === 2) break; } finally { print("f3 " + i); } } return i; }
function f4() { try { try { throw new TypeError("inner"); } finally { print("inner finally"); } } catch (e) { return e.name + ":" + e.message; } }
function f5(x) { try { if (x) throw "boom"; return "ok"; } catch { return "anon catch"; } }
function f6() { var log = []; try { log.push(1); null.x; log.push(2); } catch (e) { log.push(e instanceof TypeError); } return log.join(); }
function f7() { try { return 1; } finally { return 2; } }
function f8() {
  var r = "";
  for (var i = 0; i < 3; i++) {
    try { if (i == 1) throw i; r += "a" + i; } catch (e) { r += "c" + e; continue; } finally { r += "f"; }
    r += ";";
  }
  return r;
}
function f9() { try { undefinedFunction(); } catch (e) { return e instanceof ReferenceError; } }
function rethrow() { try { try { throw new Error("x"); } catch (e) { e.message += "y"; throw e; } } catch (e2) { return e2.message; } }
print(f1(), f2(), f3(), f4(), f5(true), f5(false), f6(), f7(), f8(), f9(), rethrow());
class MyErr extends Error { constructor(m) { super(m); this.name = "MyErr"; } }
try { throw new MyErr("custom"); } catch (e) { print(e.name, e.message, e instanceof MyErr, e instanceof Error); }
