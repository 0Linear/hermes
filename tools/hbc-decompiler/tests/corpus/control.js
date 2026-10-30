function classify(n) {
  if (n < 0) return "neg";
  else if (n === 0) return "zero";
  else if (n < 10) return "small";
  return "big";
}
function sumTo(n) { var s = 0; var i = 0; while (i < n) { s += i; i++; } return s; }
function dw(n) { var c = 0; do { c++; n = n >> 1; } while (n > 0); return c; }
function nested(n) {
  var out = [];
  outer: for (var i = 0; i < n; i++) {
    for (var j = 0; j < n; j++) {
      if (j > i) continue outer;
      if (i * j > 6) break outer;
      out.push(i + ":" + j);
    }
  }
  return out.join(",");
}
function sw(x) {
  var r = "";
  switch (x) {
    case 0: r += "a";
    case 1: r += "b"; break;
    case 2: r += "c"; break;
    case 3:
    case 4: r += "d"; break;
    default: r += "z";
  }
  return r;
}
function ssw(s) {
  switch (s) {
    case "alpha": return 1; case "beta": return 2; case "gamma": return 3;
    case "delta": return 4; case "epsilon": return 5; case "zeta": return 6;
    case "eta": return 7; case "theta": return 8; default: return -1;
  }
}
function dense(x) {
  switch (x) {
    case 10: return "ten"; case 11: return "eleven"; case 12: return "twelve";
    case 13: return "thirteen"; case 14: return "fourteen"; case 15: return "fifteen";
    case 16: return "sixteen"; case 17: return "seventeen"; case 18: return "eighteen";
  }
  return "none";
}
function swLoop(arr) {
  var acc = 0;
  for (var i = 0; i < arr.length; i++) {
    switch (arr[i] % 3) {
      case 0: continue;
      case 1: acc += 1; break;
      default: acc += 10;
    }
    acc *= 2;
  }
  return acc;
}
function logic(a, b, c) {
  var r = [];
  r.push(a && b, a || b, a ?? c, !a, a ? b : c, (a && b) || c);
  if (a && (b || c)) r.push("x");
  if (!(a || b) && c) r.push("y");
  return r.join("|");
}
function early(arr) {
  for (var i = 0; i < arr.length; i++) {
    if (arr[i] === 7) return i;
  }
  return -1;
}
function whileTrue() {
  var i = 0;
  while (true) { i++; if (i > 5) break; }
  return i;
}
function forBreakInSwitch(n) {
  var log = [];
  for (var i = 0; i < n; i++) {
    switch (i) { case 2: log.push("two"); break; case 4: log.push("stop"); return log.join(); default: log.push(i); }
  }
  return log.join();
}
print(classify(-3), classify(0), classify(4), classify(40));
print(sumTo(10), dw(1024), nested(5));
print(sw(0), sw(1), sw(2), sw(3), sw(4), sw(9));
print(ssw("alpha"), ssw("theta"), ssw("x"), dense(10), dense(18), dense(5), dense(14));
print(swLoop([1, 2, 3, 4, 5, 6, 7]));
print(logic(1, 0, 2), logic(0, 3, null), logic(null, 0, 5));
print(early([1, 7, 3]), early([]), whileTrue(), forBreakInSwitch(10), forBreakInSwitch(3));
