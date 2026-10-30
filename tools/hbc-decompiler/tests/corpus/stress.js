function bigSwitch(n) {
  var s = 0;
  for (var i = 0; i < n; i++) {
    if (i % 15 === 0) s += 15;
    else if (i % 5 === 0) s += 5;
    else if (i % 3 === 0) s += 3;
    else s += 1;
  }
  return s;
}
function matrix(n) {
  var m = [];
  for (var i = 0; i < n; i++) { m.push([]); for (var j = 0; j < n; j++) m[i].push(i === j ? 1 : 0); }
  var tr = 0; for (var k = 0; k < n; k++) tr += m[k][k];
  return tr;
}
function sieve(n) {
  var p = []; var isP = new Array(n + 1).fill(true);
  for (var i = 2; i <= n; i++) { if (!isP[i]) continue; p.push(i); for (var j = i * i; j <= n; j += i) isP[j] = false; }
  return p.length;
}
function qsort(a) {
  if (a.length < 2) return a;
  var pivot = a[0], l = [], r = [];
  for (var i = 1; i < a.length; i++) (a[i] < pivot ? l : r).push(a[i]);
  return qsort(l).concat([pivot], qsort(r));
}
function collatz(n) { var steps = 0; while (n != 1) { n = n % 2 ? 3 * n + 1 : n / 2; steps++; } return steps; }
function gcd(a, b) { while (b) { var t = b; b = a % b; a = t; } return a; }
function strBuild(n) { var s = ""; for (var i = 0; i < n; i++) { s += String.fromCharCode(97 + (i % 26)); if (s.length > 30) break; } return s; }
function nestedTernary(x) { return x > 10 ? "big" : x > 5 ? "mid" : x > 0 ? "small" : "none"; }
function complexCond(a, b, c, d) { if ((a > 0 && b > 0) || (c > 0 && d > 0)) return 1; if (a < 0 || (b < 0 && c < 0)) return 2; return 3; }
function loopWithTry(n) { var r = 0; for (var i = 0; i < n; i++) { try { if (i % 3 === 0) throw i; r += i; } catch (e) { r -= e; } } return r; }
function earlyExit(list) {
  var found = null;
  for (var i = 0; i < list.length; i++) {
    var item = list[i];
    if (!item) continue;
    if (item.skip) continue;
    if (item.v > 3) { found = item; break; }
  }
  return found ? found.v : -1;
}
print(bigSwitch(100), matrix(5), sieve(100), qsort([5, 3, 8, 1, 9, 2]).join(), collatz(27), gcd(48, 18));
print(strBuild(40), nestedTernary(11), nestedTernary(6), nestedTernary(1), nestedTernary(-1));
print(complexCond(1, 1, 0, 0), complexCond(0, 0, 1, 1), complexCond(-1, 0, 0, 0), complexCond(0, -1, -1, 0), complexCond(0, 0, 0, 0));
print(loopWithTry(10), earlyExit([null, { skip: 1, v: 9 }, { v: 2 }, { v: 5 }]), earlyExit([]));
