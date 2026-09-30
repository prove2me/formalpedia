-- Prove2me | solution 1 for lean_workbook_plus_22649
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T17:40:40.443484+00:00
-- url     : https://prove2.me/submissions/940aea3b-b642-4e74-acb5-a860caf3a8a4

import Mathlib

set_option autoImplicit false

namespace BivariateSharpProductBound

def value (p q a b : ℝ) : ℝ :=
  2 * (p * a + 1) * (q * b + 1) - (a ^ 2 + 1) * (b ^ 2 + 1)

def bound (p q : ℝ) : ℝ := (p ^ 2 + 1) * (q ^ 2 + 1)

theorem deficit_identity (p q a b : ℝ) :
    bound p q - value p q a b =
      (a * b - p * q) ^ 2 + (a - p) ^ 2 + (b - q) ^ 2 := by
  unfold bound value
  ring

theorem upper_bound (p q a b : ℝ) : value p q a b ≤ bound p q := by
  have h := deficit_identity p q a b
  nlinarith only [h, sq_nonneg (a * b - p * q), sq_nonneg (a - p), sq_nonneg (b - q)]

theorem equality_iff (p q a b : ℝ) :
    value p q a b = bound p q ↔ a = p ∧ b = q := by
  constructor
  · intro h
    have he := deficit_identity p q a b
    have ha : (a - p) ^ 2 = 0 := by
      nlinarith only [h, he, sq_nonneg (a * b - p * q), sq_nonneg (a - p), sq_nonneg (b - q)]
    have hb : (b - q) ^ 2 = 0 := by
      nlinarith only [h, he, sq_nonneg (a * b - p * q), sq_nonneg (a - p), sq_nonneg (b - q)]
    exact ⟨sub_eq_zero.mp (sq_eq_zero_iff.mp ha), sub_eq_zero.mp (sq_eq_zero_iff.mp hb)⟩
  · rintro ⟨rfl, rfl⟩
    unfold value bound
    ring

theorem line_model (p q t : ℝ) :
    value p q (p + t) q = bound p q - (q ^ 2 + 1) * t ^ 2 := by
  unfold value bound
  ring

theorem range_iff (p q v : ℝ) :
    (∃ a b : ℝ, value p q a b = v) ↔ v ≤ bound p q := by
  constructor
  · rintro ⟨a, b, rfl⟩
    exact upper_bound p q a b
  · intro hv
    have hd : 0 < q ^ 2 + 1 := by positivity
    have hs := Real.sq_sqrt (div_nonneg (sub_nonneg.mpr hv) hd.le)
    refine ⟨p + Real.sqrt ((bound p q - v) / (q ^ 2 + 1)), q, ?_⟩
    rw [line_model, hs, mul_div_cancel₀ _ (ne_of_gt hd)]
    ring

theorem full_range (p q : ℝ) :
    Set.range (fun x : ℝ × ℝ => value p q x.1 x.2) = Set.Iic (bound p q) := by
  ext v
  change (∃ x : ℝ × ℝ, value p q x.1 x.2 = v) ↔ v ≤ bound p q
  simpa only [Prod.exists] using range_iff p q v

theorem sharp_constant_iff (p q c : ℝ) :
    (∀ a b : ℝ, (a ^ 2 + 1) * (b ^ 2 + 1) + c ≥
      2 * (p * a + 1) * (q * b + 1)) ↔ bound p q ≤ c := by
  constructor
  · intro h
    have h0 := h p q
    unfold bound
    nlinarith only [h0]
  · intro h a b
    have hu := upper_bound p q a b
    unfold value at hu
    linarith

theorem unique_maximum (p q : ℝ) :
    ∃! x : ℝ × ℝ, value p q x.1 x.2 = bound p q := by
  refine ⟨(p, q), (equality_iff p q p q).mpr ⟨rfl, rfl⟩, ?_⟩
  intro x hx
  exact Prod.ext ((equality_iff p q x.1 x.2).mp hx).1
    ((equality_iff p q x.1 x.2).mp hx).2

theorem source_sharp_constant (c : ℝ) :
    (∀ a b : ℝ, (a ^ 2 + 1) * (b ^ 2 + 1) + c ≥
      2 * (2 * a + 1) * (3 * b + 1)) ↔ 50 ≤ c := by
  have hb : bound 2 3 = 50 := by norm_num [bound]
  simpa only [hb] using sharp_constant_iff 2 3 c

theorem source_equality (a b : ℝ) :
    (a ^ 2 + 1) * (b ^ 2 + 1) + 50 = 2 * (2 * a + 1) * (3 * b + 1) ↔
      a = 2 ∧ b = 3 := by
  have h := equality_iff 2 3 a b
  norm_num [bound, value] at h
  constructor
  · intro he
    apply h.mp
    linarith
  · intro he
    have hx := h.mpr he
    linarith

theorem source_range :
    Set.range (fun x : ℝ × ℝ =>
      2 * (2 * x.1 + 1) * (3 * x.2 + 1) - (x.1 ^ 2 + 1) * (x.2 ^ 2 + 1)) =
      Set.Iic (50 : ℝ) := by
  have hb : bound 2 3 = 50 := by norm_num [bound]
  simpa only [value, hb] using full_range 2 3

end BivariateSharpProductBound

theorem solution (a b : ℝ) : (a ^ 2 + 1) * (b ^ 2 + 1) + 50 ≥
    2 * (2 * a + 1) * (3 * b + 1) := by
  exact (BivariateSharpProductBound.source_sharp_constant 50).mpr le_rfl a b

#print axioms BivariateSharpProductBound.deficit_identity
#print axioms BivariateSharpProductBound.upper_bound
#print axioms BivariateSharpProductBound.equality_iff
#print axioms BivariateSharpProductBound.line_model
#print axioms BivariateSharpProductBound.range_iff
#print axioms BivariateSharpProductBound.full_range
#print axioms BivariateSharpProductBound.sharp_constant_iff
#print axioms BivariateSharpProductBound.unique_maximum
#print axioms BivariateSharpProductBound.source_sharp_constant
#print axioms BivariateSharpProductBound.source_equality
#print axioms BivariateSharpProductBound.source_range
#print axioms solution
