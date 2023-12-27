import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Real.Basic

structure Complex :=
(re : Real) (im : Real)

def add (z w : Complex) : Complex :=
⟨z.re + w.re, z.im + w.im⟩

def mul (z w : Complex) : Complex :=
⟨z.re * w.re - z.im * w.im, z.re * w.im + z.im * w.re⟩

def neg (z : Complex) : Complex :=
⟨-z.re, -z.im⟩

def zero : Complex := ⟨0, 0⟩
def one : Complex := ⟨1, 0⟩

def i : Complex := ⟨0, 1⟩

theorem complex_add_assoc (z w u : Complex) : add (add z w) u = add z (add w u) :=
by
  rw [add, add, add_assoc, add_assoc, add, add]

theorem complex_zero_add (z : Complex) : add zero z = z :=
by
  simp [add, zero]

theorem complex_add_zero (z : Complex) : add z zero = z :=
by
  simp [add, zero]

theorem complex_add_left_neg (z : Complex) : add (neg z) z = zero :=
by
  simp [add, neg, zero]

theorem complex_add_comm (z w : Complex) : add z w = add w z :=
by
  simp [add]
  constructor
  rw [add_comm]
  rw [add_comm]

theorem complex_mul_assoc (z w u : Complex) : mul (mul z w) u = mul z (mul w u) :=
by
  simp [mul]
  constructor
  ring
  ring

theorem complex_mul_comm (z w : Complex) : mul z w = mul w z := -- not necessary
by
  simp [mul]
  constructor
  ring
  ring

theorem complex_zero_mul (z : Complex) : mul zero z = zero :=
by
  simp [mul, zero]

theorem complex_mul_zero (z : Complex) : mul z zero = zero :=
by
  simp [mul, zero]

theorem complex_one_mul (z : Complex) : mul one z = z :=
by
  simp [mul, one]

theorem complex_mul_one (z : Complex) : mul z one = z :=
by
  simp [mul, one]

theorem complex_left_distrib (z w u : Complex) : mul z (add w u) = add (mul z w) (mul z u) :=
by
  simp [mul, add]
  constructor
  ring
  ring

theorem complex_right_distrib (a b c : Complex) : mul (add a b) c = add (mul a c) (mul b c) :=
by
  simp [mul, add]
  constructor
  ring
  ring

instance : Ring Complex :=
{ add := add,
  add_assoc := complex_add_assoc,
  zero := zero,
  zero_add := complex_zero_add,
  add_zero := complex_add_zero,
  neg := neg,
  add_left_neg := complex_add_left_neg,
  add_comm := complex_add_comm,
  mul := mul,
  mul_assoc := complex_mul_assoc,
  zero_mul := complex_zero_mul,
  mul_zero := complex_mul_zero,
  one := one,
  one_mul := complex_one_mul,
  mul_one := complex_mul_one,
  left_distrib := complex_left_distrib,
  right_distrib := complex_right_distrib,
}


example : mul i i = ⟨-1, 0⟩ :=
by
  simp [mul, i]
