import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

structure Complex :=
(re : ℝ) (im : ℝ)

def add (z w : Complex) : Complex :=
⟨z.re + w.re, z.im + w.im⟩

def mul (z w : Complex) : Complex :=
⟨z.re * w.re - z.im * w.im, z.re * w.im + z.im * w.re⟩

def neg (z : Complex) : Complex :=
⟨-z.re, -z.im⟩

def zero : Complex := ⟨0, 0⟩
def one : Complex := ⟨1, 0⟩

def i : Complex := ⟨0, 1⟩

theorem Complex.add_assoc (z w u : Complex) : add (add z w) u = add z (add w u) :=
by
  simp [add, add, add, add]
  ring_nf
  simp

theorem Complex.zero_add (z : Complex) : add zero z = z :=
by
  simp [add, zero]

theorem Complex.add_zero (z : Complex) : add z zero = z :=
by
  simp [add, zero]

theorem Complex.add_left_neg (z : Complex) : add (neg z) z = zero :=
by
  simp [add, neg, zero]

theorem Complex.add_comm (z w : Complex) : add z w = add w z :=
by
  simp [add]
  constructor
  ring
  ring

theorem Complex.mul_assoc (z w u : Complex) : mul (mul z w) u = mul z (mul w u) :=
by
  simp [mul]
  constructor
  ring_nf
  ring_nf

theorem Complex.mul_comm (z w : Complex) : mul z w = mul w z := -- not necessary
by
  simp [mul]
  constructor
  ring_nf
  ring_nf

theorem Complex.zero_mul (z : Complex) : mul zero z = zero :=
by
  simp [mul, zero]

theorem Complex.mul_zero (z : Complex) : mul z zero = zero :=
by
  simp [mul, zero]

theorem Complex.one_mul (z : Complex) : mul one z = z :=
by
  simp [mul, one]

theorem Complex.mul_one (z : Complex) : mul z one = z :=
by
  simp [mul, one]

theorem Complex.left_distrib (z w u : Complex) : mul z (add w u) = add (mul z w) (mul z u) :=
by
  simp [mul, add]
  constructor
  ring_nf
  ring_nf

theorem Complex.right_distrib (a b c : Complex) : mul (add a b) c = add (mul a c) (mul b c) :=
by
  simp [mul, add]
  constructor
  ring_nf
  ring_nf


theorem Complex.mul_com (a c : Complex) : mul a c = mul c a :=
by
  simp [mul]
  constructor
  ring_nf
  ring_nf

theorem Complex.additive_inverse (a : Complex) : add a (neg a) = zero :=
by
  simp [add, neg, zero]

open Classical

noncomputable def inv (z : Complex) : Complex := if z = zero then zero else ⟨z.re / (z.re^2 + z.im^2), -z.im / (z.re^2 + z.im^2)⟩

theorem nonneg_add_nonneg_eq_zero_both_zero (a : ℝ) (b : ℝ) (h1: 0 ≤ a) (h2: 0 ≤ b) (h3 : a + b = 0) : a = 0 ∧ b = 0 := by
  constructor
  linarith
  linarith


theorem Complex.mul_inv_cancel (a : Complex) (h : a ≠ zero) : mul a (inv a) = one := by
  simp [mul, inv, one, h]
  simp [zero] at h
  ring_nf
  norm_num
  have denom_nonzero : a.re ^ 2 + a.im ^ 2 ≠ 0 := by
    intro probably_not
    have h1 : 0 ≤ a.im ^ 2
    {
      apply sq_nonneg
    }
    have h2 : 0 ≤ a.re ^ 2
    {
      apply sq_nonneg
    }
    have squares_zero : a.re ^ 2 = 0 ∧ a.im ^ 2 = 0
    {
      apply nonneg_add_nonneg_eq_zero_both_zero (a.re ^ 2) (a.im ^ 2) h2 h1 probably_not
    }
    have re_zero : a.re ^ 2 = 0
    {
      linarith
    }
    -- Extract a.im ^ 2 = 0 from squares_zero
    have im_zero : a.im ^ 2 = 0
    {
      linarith
    }

    rw [sq_eq_zero_iff] at re_zero
    rw [sq_eq_zero_iff] at im_zero
    have re_im_zero : a = { re := 0, im := 0 }
    {
      cases a
      simp at re_zero
      simp at im_zero
      rw [re_zero, im_zero]
    }
    contradiction
  rw [← Distrib.right_distrib, inv_eq_one_div, ← div_eq_mul_one_div, div_self denom_nonzero]


instance : Ring Complex :=
{ add := add,
  add_assoc := Complex.add_assoc,
  zero := zero,
  zero_add := Complex.zero_add,
  add_zero := Complex.add_zero,
  neg := neg,
  add_left_neg := Complex.add_left_neg,
  add_comm := Complex.add_comm,
  mul := mul,
  mul_assoc := Complex.mul_assoc,
  zero_mul := Complex.zero_mul,
  mul_zero := Complex.mul_zero,
  one := one,
  one_mul := Complex.one_mul,
  mul_one := Complex.mul_one,
  left_distrib := Complex.left_distrib,
  right_distrib := Complex.right_distrib,
}

theorem Complex.exists_pair_ne : ∃ (x y : Complex), x ≠ y := by
  exists zero
  exists one
  rw [zero, one]
  intro h
  injection h with h_re _
  apply zero_ne_one at h_re
  exact h_re

theorem Complex.inv_zero : inv zero = zero := by
  simp [inv, zero]

noncomputable instance : Field Complex :=
{
  inv := inv,
  exists_pair_ne := Complex.exists_pair_ne,
  mul_inv_cancel := Complex.mul_inv_cancel,
  inv_zero := Complex.inv_zero,
  mul_comm := Complex.mul_comm,
}
