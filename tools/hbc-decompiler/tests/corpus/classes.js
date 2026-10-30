class A { constructor(x) { this.x = x; } m() { return this.x; } static s() { return 1; } get g() { return 2; } }
class B extends A { constructor(x) { super(x + 1); this.y = 2; } m() { return super.m() * 10; } }
var b = new B(1);
print(b.m(), b.y, A.s(), b.g);
function f(...rest) { return rest.length; }
var {p, ...q} = {p: 1, r: 2};
print(f(1,2,3), `t${p}x`, q.r, [1, ...[2, 3]].length, Math.max(...[1, 5]));
