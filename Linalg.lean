import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Real.Basic
import Mathlib.Data.Vector.Basic
import Mathlib.Tactic.Linarith

structure Complex :=
(re : ℝ) (im : ℝ)

notation "ℂ" => Complex

def complex_add (z w : ℂ) : ℂ :=
⟨z.re + w.re, z.im + w.im⟩

def complex_mul (z w : ℂ) : ℂ :=
⟨z.re * w.re - z.im * w.im, z.re * w.im + z.im * w.re⟩

def complex_neg (z : ℂ) : ℂ :=
⟨-z.re, -z.im⟩

def zero : ℂ := ⟨0, 0⟩
def one : ℂ := ⟨1, 0⟩

def i : ℂ := ⟨0, 1⟩

-- show that i × i = -1
example : complex_mul i i = ⟨-1, 0⟩ := by
  simp [i, complex_mul]

theorem Complex.add_assoc (z w u : ℂ) : complex_add (complex_add z w) u = complex_add z (complex_add w u) :=
by
  simp [complex_add, complex_add, complex_add, complex_add]
  ring_nf
  simp

theorem Complex.zero_add (z : ℂ) : complex_add zero z = z :=
by
  simp [complex_add, zero]

theorem Complex.add_zero (z : ℂ) : complex_add z zero = z :=
by
  simp [complex_add, zero]

theorem Complex.add_left_neg (z : ℂ) : complex_add (complex_neg z) z = zero :=
by
  simp [complex_add, complex_neg, zero]

theorem Complex.add_comm (z w : ℂ) : complex_add z w = complex_add w z :=
by
  simp [complex_add]
  constructor
  ring
  ring

theorem Complex.mul_assoc (z w u : ℂ) : complex_mul (complex_mul z w) u = complex_mul z (complex_mul w u) :=
by
  simp [complex_mul]
  constructor
  ring_nf
  ring_nf

theorem Complex.zero_mul (z : ℂ) : complex_mul zero z = zero :=
by
  simp [complex_mul, zero]

theorem Complex.mul_zero (z : ℂ) : complex_mul z zero = zero :=
by
  simp [complex_mul, zero]

theorem Complex.one_mul (z : ℂ) : complex_mul one z = z :=
by
  simp [complex_mul, one]

theorem Complex.mul_one (z : ℂ) : complex_mul z one = z :=
by
  simp [complex_mul, one]

theorem Complex.left_distrib (z w u : ℂ) : complex_mul z (complex_add w u) = complex_add (complex_mul z w) (complex_mul z u) :=
by
  simp [complex_mul, complex_add]
  constructor
  ring_nf
  ring_nf

theorem Complex.right_distrib (a b c : ℂ) : complex_mul (complex_add a b) c = complex_add (complex_mul a c) (complex_mul b c) :=
by
  simp [complex_mul, complex_add]
  constructor
  ring_nf
  ring_nf


theorem Complex.mul_comm (a c : ℂ) : complex_mul a c = complex_mul c a :=
by
  simp [complex_mul]
  constructor
  ring_nf
  ring_nf

theorem Complex.additive_inverse (a : ℂ) : complex_add a (complex_neg a) = zero :=
by
  simp [complex_add, complex_neg, zero]

theorem Complex.additive_inverse_unique (a b : ℂ) (h : complex_add a b = zero) : b = complex_neg a :=
by
  simp [complex_add, complex_neg, zero]
  simp [complex_add, complex_neg, zero] at h
  cases h with
  | intro x y =>
    rw [add_eq_zero_iff_neg_eq] at x
    rw [add_eq_zero_iff_neg_eq] at y
    rw [x, y]

open Classical

noncomputable def inv (z : ℂ) : ℂ := if z = zero then zero else ⟨z.re / (z.re^2 + z.im^2), -z.im / (z.re^2 + z.im^2)⟩

theorem nonneg_add_nonneg_eq_zero_both_zero (a : ℝ) (b : ℝ) (h1: 0 ≤ a) (h2: 0 ≤ b) (h3 : a + b = 0) : a = 0 ∧ b = 0 := by
  constructor
  linarith
  linarith


theorem Complex.mul_inv_cancel (a : ℂ) (h : a ≠ zero) : complex_mul a (inv a) = one := by
  simp [complex_mul, inv, one, h]
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

theorem Complex.mul_inv_unique (a b : ℂ) (a_ne_zero : a ≠ zero) (b_ne_zero : b ≠ zero) (h : complex_mul a b = one) : b = inv a := by
  simp [complex_mul, one] at h
  cases h with
  | intro re_eq_one im_eq_zero =>
  simp [inv, a_ne_zero]
  sorry

instance : Ring Complex :=
{ add := complex_add,
  add_assoc := Complex.add_assoc,
  zero := zero,
  zero_add := Complex.zero_add,
  add_zero := Complex.add_zero,
  neg := complex_neg,
  add_left_neg := Complex.add_left_neg,
  add_comm := Complex.add_comm,
  mul := complex_mul,
  mul_assoc := Complex.mul_assoc,
  zero_mul := Complex.zero_mul,
  mul_zero := Complex.mul_zero,
  one := one,
  one_mul := Complex.one_mul,
  mul_one := Complex.mul_one,
  left_distrib := Complex.left_distrib,
  right_distrib := Complex.right_distrib,
}

theorem Complex.exists_pair_ne : ∃ (x y : ℂ), x ≠ y := by
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

-- Pg 6 - intro to lists

-- we want a type that represents a list of Field elements (with the length of the list in the type)

def MyVector (α : Type u) (n : ℕ) :=
  { l : List α // l.length = n }

def MyVector_add {α : Type u} {n : ℕ} [Ring α] (v w : MyVector α n) : MyVector α n :=
  ⟨List.zipWith (· + ·) v.val w.val, by
    rw [List.length_zipWith, Vector.length_val, Vector.length_val, min_self]
  ⟩

def MyVector_scale {α : Type u} {n : ℕ} [Ring α] (a : α) (v : MyVector α n) : MyVector α n :=
  ⟨List.map (· * a) v.val, by
    rw [List.length_map, Vector.length_val]
  ⟩

theorem MyVector_add_comm {α : Type u} {n : ℕ} [Ring α] (v w : MyVector α n) : MyVector_add v w = MyVector_add w v := by
  simp [MyVector_add]
  let w_val := w.val
  let v_val := v.val
  have h1 (v1 : List α) (w1 : List α) : List.zipWith (· + ·) v1 w1 = List.zipWith (· + ·) w1 v1 := by
    clear v v_val w w_val
    induction' v1 with v1_head v1_tail v1_tail_ih generalizing w1
    {
      simp [List.zipWith]
    }
    {
      rcases w1 with (_ | ⟨w1_head, w1_tail⟩)
      {
        simp [List.zipWith]
      }
      {
        simp [List.zipWith]
        constructor
        {
          apply add_comm
        }
        {
          let e := v1_tail_ih w1_tail
          exact e
        }
      }
    }
  simp [h1]


theorem MyVector_add_assoc {α : Type u} {n : ℕ} [Ring α] (u v w : MyVector α n) : MyVector_add (MyVector_add u v) w = MyVector_add u (MyVector_add v w) := by
  simp [MyVector_add]
  let u_val := u.val
  let v_val := v.val
  let w_val := w.val

  have h1 (u1 : List α) (v1 : List α) (w1 : List α) : List.zipWith (· + ·) (List.zipWith (· + ·) u1 v1) w1 = List.zipWith (· + ·) u1 (List.zipWith (· + ·) v1 w1) := by
    clear u u_val v v_val w w_val
    induction' u1 with u1_head u1_tail u1_tail_ih generalizing v1 w1
    {
      simp [List.zipWith, List.zipWith]
    }
    {
      rcases v1 with (_ | ⟨v1_head, v1_tail⟩)
      {
        simp [List.zipWith]
      }
      {
        rcases w1 with (_ | ⟨w1_head, w1_tail⟩)
        {
          simp [List.zipWith]
        }
        {
          simp [List.zipWith]
          constructor
          {
            apply add_assoc
          }
          {
            let e := u1_tail_ih v1_tail w1_tail
            exact e
          }
        }
      }
    }
  simp [h1]

example {α : Type u} [CommSemigroup α] (a : α) : (fun (x : α) => x * a) = (fun (x : α) => a * x) := by
  funext x
  rw [mul_comm]

theorem map_mul_comm [CommSemigroup a] (b : a) (l : List a) : List.map (b * ·) l = List.map (· * b) l := by
  have h : (fun x => x * b) = (fun x => b * x) := by
    funext x
    rw [mul_comm]
  rw [h]

theorem MyVector_scale_assoc {α : Type u} {n : ℕ} [Field α] (a b : α) (v : MyVector α n) : MyVector_scale a (MyVector_scale b v) = MyVector_scale (a * b) v := by
  simp [MyVector_scale]
  have h : (fun x => x * (b * a)) = (fun x => x * (a * b)) := by
    funext x
    ring
  simp only [h]

