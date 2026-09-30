-- Prove2me | solution 1 for lean_workbook_plus_57141
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T09:40:12.648122+00:00
-- url     : https://prove2.me/submissions/296b2f8d-3fcf-486b-9ba0-b0786ef7b9e7

import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace RadicalMeanFunctionalClassification

def Equation (f : ℝ → ℝ) : Prop :=
  ∀ x y, 0 < x → 0 < y →
    f x + f y = (Real.sqrt (x / y) + Real.sqrt (y / x)) * f (Real.sqrt (x * y))

def WilsonEquation (f : ℝ → ℝ) : Prop :=
  ∀ s t, 0 < s → 0 < t → f (s * t) + f (s / t) = (t + 1 / t) * f s

theorem wilson_of_source {f : ℝ → ℝ} (hf : Equation f) : WilsonEquation f := by
  intro s t hs ht
  have hs0 := ne_of_gt hs
  have ht0 := ne_of_gt ht
  have h := hf (s * t) (s / t) (mul_pos hs ht) (div_pos hs ht)
  have h1 : (s * t) / (s / t) = t ^ 2 := by field_simp
  have h2 : (s / t) / (s * t) = (1 / t) ^ 2 := by field_simp
  have h3 : (s * t) * (s / t) = s ^ 2 := by field_simp
  rw [h1, h2, h3, Real.sqrt_sq (le_of_lt ht),
    Real.sqrt_sq (le_of_lt (div_pos (by norm_num) ht)), Real.sqrt_sq (le_of_lt hs)] at h
  exact h

theorem product_addition {f : ℝ → ℝ} (hf : WilsonEquation f)
    {s t : ℝ} (hs : 0 < s) (ht : 0 < t) :
    2 * f (s * t) = (t + 1 / t) * f s + (s + 1 / s) * f t -
      (s / t + t / s) * f 1 := by
  have hs0 := ne_of_gt hs
  have ht0 := ne_of_gt ht
  have h1 := hf s t hs ht
  have h2 := hf t s ht hs
  have h3 := hf 1 (s / t) (by norm_num) (div_pos hs ht)
  rw [one_mul, show 1 / (s / t) = t / s by field_simp] at h3
  rw [mul_comm t s] at h2
  linarith

theorem explicit_coefficients {f : ℝ → ℝ} (hf : WilsonEquation f)
    {s : ℝ} (hs : 0 < s) :
    f s = ((2 * f 2 - f 1) / 3) * s + ((4 * f 1 - 2 * f 2) / 3) / s := by
  have hs0 := ne_of_gt hs
  have h1 := product_addition hf hs (show (0 : ℝ) < 2 by norm_num)
  have h2 := product_addition hf (show 0 < s * 2 by positivity)
    (show (0 : ℝ) < 2 by norm_num)
  have h3 := product_addition hf hs (show (0 : ℝ) < 4 by norm_num)
  have h4 := product_addition hf (show (0 : ℝ) < 2 by norm_num)
    (show (0 : ℝ) < 2 by norm_num)
  have e1 : 4 * s * f (s * 2) = 5 * s * f s + 2 * (s ^ 2 + 1) * f 2 -
      (s ^ 2 + 4) * f 1 := by
    field_simp at h1
    rw [mul_comm 2 s] at h1
    nlinarith only [h1]
  have e2 : 8 * s * f (s * 4) = 10 * s * f (s * 2) +
      2 * (4 * s ^ 2 + 1) * f 2 - (4 * s ^ 2 + 4) * f 1 := by
    rw [show s * 2 * 2 = s * 4 by ring] at h2
    field_simp at h2
    rw [mul_comm 2 s] at h2
    nlinarith only [h2]
  have e3 : 8 * s * f (s * 4) = 17 * s * f s + 4 * (s ^ 2 + 1) * f 4 -
      (s ^ 2 + 16) * f 1 := by
    field_simp at h3
    nlinarith only [h3]
  have e4 : 2 * f 4 = 5 * f 2 - 2 * f 1 := by
    rw [show (2 : ℝ) * 2 = 4 by ring] at h4
    linear_combination h4
  have he : 3 * s * f s = (2 * f 2 - f 1) * s ^ 2 + (4 * f 1 - 2 * f 2) := by
    linear_combination (5 / 3 : ℝ) * e1 + (2 / 3 : ℝ) * e2 -
      (2 / 3 : ℝ) * e3 - (4 / 3 : ℝ) * (s ^ 2 + 1) * e4
  field_simp
  nlinarith only [he]

theorem model_satisfies (A B : ℝ) : Equation (fun x => A * x + B / x) := by
  intro x y hx hy
  have hu : Real.sqrt x ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hx)
  have hv : Real.sqrt y ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hy)
  rw [Real.sqrt_div (le_of_lt hx), Real.sqrt_div (le_of_lt hy),
    Real.sqrt_mul (le_of_lt hx)]
  have algebra (u v : ℝ) (hu0 : u ≠ 0) (hv0 : v ≠ 0) :
      A * u ^ 2 + B / u ^ 2 + (A * v ^ 2 + B / v ^ 2) =
        (u / v + v / u) * (A * (u * v) + B / (u * v)) := by
    field_simp
    ring
  simpa only [Real.sq_sqrt (le_of_lt hx), Real.sq_sqrt (le_of_lt hy)] using
    algebra (Real.sqrt x) (Real.sqrt y) hu hv

theorem full_source_classification (f : ℝ → ℝ) :
    Equation f ↔ ∃ A B : ℝ, ∀ x, 0 < x → f x = A * x + B / x := by
  constructor
  · intro hf
    exact ⟨(2 * f 2 - f 1) / 3, (4 * f 1 - 2 * f 2) / 3,
      fun _ hx => explicit_coefficients (wilson_of_source hf) hx⟩
  · rintro ⟨A, B, h⟩ x y hx hy
    rw [h x hx, h y hy, h (Real.sqrt (x * y)) (Real.sqrt_pos.2 (mul_pos hx hy))]
    exact model_satisfies A B x y hx hy

theorem coefficients_unique {A B C D : ℝ}
    (h : ∀ x : ℝ, 0 < x → A * x + B / x = C * x + D / x) : A = C ∧ B = D := by
  have h1 := h 1 (by norm_num)
  have h2 := h 2 (by norm_num)
  norm_num at h1 h2
  constructor <;> linarith

noncomputable def extension (A B : ℝ) (g : ℝ → ℝ) (x : ℝ) : ℝ :=
  if 0 < x then A * x + B / x else g x

theorem arbitrary_nonpositive_extension (A B : ℝ) (g : ℝ → ℝ) :
    Equation (extension A B g) ∧ (∀ x, x ≤ 0 → extension A B g x = g x) := by
  constructor
  · apply (full_source_classification _).2
    refine ⟨A, B, ?_⟩
    intro x hx
    rw [extension, if_pos hx]
  · intro x hx
    rw [extension, if_neg (not_lt.mpr hx)]

end RadicalMeanFunctionalClassification

theorem solution (x y : ℝ) (f : ℝ → ℝ)
    (_hf : f x + f y = (Real.sqrt (x / y) + Real.sqrt (y / x)) *
      f (Real.sqrt (x * y))) : ∃ f : ℝ → ℝ, ∀ x y : ℝ, 0 < x ∧ 0 < y →
    f x + f y = (Real.sqrt (x / y) + Real.sqrt (y / x)) * f (Real.sqrt (x * y)) := by
  refine ⟨fun x => 1 * x + 1 / x, ?_⟩
  intro x y hxy
  exact RadicalMeanFunctionalClassification.model_satisfies 1 1 x y hxy.1 hxy.2
