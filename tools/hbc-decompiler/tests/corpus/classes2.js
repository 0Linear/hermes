class Animal {
  static count = 0;
  #secret = 7;
  name;
  constructor(name) { this.name = name; Animal.count++; }
  speak() { return this.name + " makes a sound"; }
  get secret() { return this.#secret; }
  set secret(v) { this.#secret = v; }
  #priv() { return "p" + this.#secret; }
  callPriv() { return this.#priv(); }
  static create(n) { return new this(n); }
  hasSecret(o) { return #secret in o; }
}
class Dog extends Animal {
  constructor(name) { super(name); this.kind = "dog"; }
  speak() { return super.speak() + " (woof)"; }
  toString() { return "Dog(" + this.name + ")"; }
}
var d = new Dog("rex");
print(d.speak(), Animal.count, d.secret, String(d), d instanceof Animal);
d.secret = 11;
print(d.secret, d.callPriv(), Dog.create("fido").speak(), Animal.count, d.hasSecret(d), d.hasSecret({}));
class Point { constructor(x, y) { this.x = x; this.y = y; } add(o) { return new Point(this.x + o.x, this.y + o.y); } get len() { return Math.hypot(this.x, this.y); } }
var p = new Point(3, 4).add(new Point(0, 0));
print(p.x, p.y, p.len, Object.getOwnPropertyNames(Point.prototype).join());
function OldStyle(v) { if (!(this instanceof OldStyle)) return new OldStyle(v); this.v = v; }
OldStyle.prototype.get = function () { return this.v; };
print(OldStyle(5).get(), new OldStyle(6).get());
class Base { constructor() { this.t = new.target.name; } }
class Derived extends Base {}
print(new Derived().t, new Base().t);
var Anon = class { m() { return "anon"; } };
print(new Anon().m());
class WithStatic { static #count = 0; static inc() { return ++WithStatic.#count; } }
WithStatic.inc(); print(WithStatic.inc());
