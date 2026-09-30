-- Prove2me | solution 1 for lean_workbook_plus_45780
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T08:08:45.485203+00:00
-- url     : https://prove2.me/submissions/fa4237bf-793a-45b9-af3d-e990cb98b677

import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

noncomputable def reflectionSlope : ℝ := Real.cos 1 / (1 - Real.sin 1)
noncomputable def reflectionFundamental (x : ℝ) : ℝ := Real.cos x + reflectionSlope * Real.sin x

theorem reflection_denominator_positive : 0 < 1 - Real.sin 1 := by
  exact sub_pos.mpr (Real.sin_lt (by norm_num))

theorem reflection_coefficient_identities :
    Real.cos 1 + reflectionSlope * Real.sin 1 = reflectionSlope ∧
      reflectionSlope * Real.cos 1 = 1 + Real.sin 1 := by
  have hn := reflection_denominator_positive.ne'
  unfold reflectionSlope
  constructor
  · field_simp
    ring
  · field_simp
    nlinarith [Real.sin_sq_add_cos_sq 1]

theorem reflection_mirror_derivative (f : ℝ → ℝ)
    (hf : ∀ x, HasDerivAt f (f (1 - x)) x) (x : ℝ) :
    HasDerivAt (fun t => f (1 - t)) (-f x) x := by
  simpa only [id_eq, show (1 : ℝ) - (1 - x) = x by ring, mul_neg_one] using
    (hf (1 - x)).comp x ((hasDerivAt_id x).const_sub 1)

theorem reflection_differential_invariants (f : ℝ → ℝ)
    (hf : ∀ x, HasDerivAt f (f (1 - x)) x) (x : ℝ) :
    f x * Real.cos x - f (1 - x) * Real.sin x = f 0 ∧
      f x * Real.sin x + f (1 - x) * Real.cos x = f 1 := by
  have hA (t : ℝ) : HasDerivAt (fun t => f t * Real.cos t - f (1 - t) * Real.sin t) 0 t := by
    convert ((hf t).mul (Real.hasDerivAt_cos t)).sub
      ((reflection_mirror_derivative f hf t).mul (Real.hasDerivAt_sin t)) using 1
    ring
  have hB (t : ℝ) : HasDerivAt (fun t => f t * Real.sin t + f (1 - t) * Real.cos t) 0 t := by
    convert ((hf t).mul (Real.hasDerivAt_sin t)).add
      ((reflection_mirror_derivative f hf t).mul (Real.hasDerivAt_cos t)) using 1
    ring
  constructor
  · simpa only [Real.cos_zero, Real.sin_zero, mul_zero, mul_one, sub_zero] using
      is_const_of_deriv_eq_zero (fun t => (hA t).differentiableAt) (fun t => (hA t).deriv) x 0
  · simpa only [Real.cos_zero, Real.sin_zero, mul_zero, mul_one, zero_add, sub_zero] using
      is_const_of_deriv_eq_zero (fun t => (hB t).differentiableAt) (fun t => (hB t).deriv) x 0

theorem reflection_differential_trig_form (f : ℝ → ℝ)
    (hf : ∀ x, HasDerivAt f (f (1 - x)) x) (x : ℝ) :
    f x = f 0 * Real.cos x + f 1 * Real.sin x := by
  obtain ⟨hA, hB⟩ := reflection_differential_invariants f hf x
  calc
    f x = f x * (Real.sin x ^ 2 + Real.cos x ^ 2) := by rw [Real.sin_sq_add_cos_sq, mul_one]
    _ = (f x * Real.cos x - f (1 - x) * Real.sin x) * Real.cos x +
        (f x * Real.sin x + f (1 - x) * Real.cos x) * Real.sin x := by ring
    _ = f 0 * Real.cos x + f 1 * Real.sin x := by rw [hA, hB]

theorem reflection_differential_initial_value (f : ℝ → ℝ)
    (hf : ∀ x, HasDerivAt f (f (1 - x)) x) : f 1 = f 0 * reflectionSlope := by
  have h := reflection_differential_trig_form f hf 1
  unfold reflectionSlope
  rw [← mul_div_assoc]
  apply (eq_div_iff reflection_denominator_positive.ne').mpr
  linarith

theorem reflection_differential_classification (f : ℝ → ℝ)
    (hf : ∀ x, HasDerivAt f (f (1 - x)) x) (x : ℝ) :
    f x = f 0 * reflectionFundamental x := by
  rw [reflection_differential_trig_form f hf x, reflection_differential_initial_value f hf]
  unfold reflectionFundamental
  ring

theorem reflection_fundamental_mirror (x : ℝ) :
    reflectionFundamental (1 - x) = -Real.sin x + reflectionSlope * Real.cos x := by
  unfold reflectionFundamental
  rw [Real.cos_sub, Real.sin_sub]
  calc
    Real.cos 1 * Real.cos x + Real.sin 1 * Real.sin x +
        reflectionSlope * (Real.sin 1 * Real.cos x - Real.cos 1 * Real.sin x) =
      (Real.cos 1 + reflectionSlope * Real.sin 1) * Real.cos x +
        (Real.sin 1 - reflectionSlope * Real.cos 1) * Real.sin x := by ring
    _ = -Real.sin x + reflectionSlope * Real.cos x := by
      rw [reflection_coefficient_identities.1, reflection_coefficient_identities.2]
      ring

theorem reflection_fundamental_derivative (x : ℝ) :
    HasDerivAt reflectionFundamental (reflectionFundamental (1 - x)) x := by
  rw [reflection_fundamental_mirror]
  exact (Real.hasDerivAt_cos x).add ((Real.hasDerivAt_sin x).const_mul reflectionSlope)

theorem reflection_differential_iff (f : ℝ → ℝ) :
    (∀ x, HasDerivAt f (f (1 - x)) x) ↔
      ∃ c : ℝ, f = fun x => c * reflectionFundamental x := by
  constructor
  · intro hf
    exact ⟨f 0, funext (reflection_differential_classification f hf)⟩
  · rintro ⟨c, rfl⟩ x
    exact (reflection_fundamental_derivative x).const_mul c

theorem reflection_fundamental_smooth : ContDiff ℝ ⊤ reflectionFundamental := by
  unfold reflectionFundamental
  fun_prop

theorem reflection_fundamental_at_zero : reflectionFundamental 0 = 1 := by
  simp only [reflectionFundamental, Real.cos_zero, Real.sin_zero, mul_zero, add_zero]

theorem reflection_source_unique :
    ∃! f : ℝ → ℝ, f 0 = 1 ∧ ∀ x, HasDerivAt f (f (1 - x)) x := by
  refine ⟨reflectionFundamental, ⟨reflection_fundamental_at_zero, reflection_fundamental_derivative⟩, ?_⟩
  intro f hf
  funext x
  rw [reflection_differential_classification f hf.2 x, hf.1, one_mul]

theorem reflection_source_value (f : ℝ → ℝ)
    (hf : ∀ x, HasDerivAt f (f (1 - x)) x) (h0 : f 0 = 1) :
    f 1 = Real.cos 1 / (1 - Real.sin 1) := by
  rw [reflection_differential_initial_value f hf, h0, one_mul]
  rfl

theorem reflection_source_value_gt_one : 1 < reflectionSlope := by
  have hs : 0 < Real.sin 1 := Real.sin_pos_of_pos_of_lt_pi (by norm_num) (by linarith [Real.two_le_pi])
  have hh : 1 < Real.pi / 2 := by
    simpa only [Real.sin_pi_div_two] using Real.sin_lt Real.pi_div_two_pos
  have hc : 0 < Real.cos 1 := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hh⟩
  have hp := mul_pos hs hc
  have ht := Real.sin_sq_add_cos_sq 1
  have hsum : 1 < Real.sin 1 + Real.cos 1 := by nlinarith
  unfold reflectionSlope
  apply (lt_div_iff₀ reflection_denominator_positive).mpr
  linarith

theorem solution (f : ℝ → ℝ) (hf : ∀ x, f x = f (1 - x)) (h : f 0 = 1) : f 1 = 1 := by
  simpa only [sub_zero, h] using (hf 0).symm

#print axioms reflectionSlope
#print axioms reflectionFundamental
#print axioms reflection_denominator_positive
#print axioms reflection_coefficient_identities
#print axioms reflection_mirror_derivative
#print axioms reflection_differential_invariants
#print axioms reflection_differential_trig_form
#print axioms reflection_differential_initial_value
#print axioms reflection_differential_classification
#print axioms reflection_fundamental_mirror
#print axioms reflection_fundamental_derivative
#print axioms reflection_differential_iff
#print axioms reflection_fundamental_smooth
#print axioms reflection_fundamental_at_zero
#print axioms reflection_source_unique
#print axioms reflection_source_value
#print axioms reflection_source_value_gt_one
#print axioms solution
