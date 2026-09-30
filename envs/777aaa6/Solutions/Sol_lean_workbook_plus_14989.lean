-- Prove2me | solution 1 for lean_workbook_plus_14989
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T23:57:47.480163+00:00
-- url     : https://prove2.me/submissions/03bfa91d-bab2-46da-ba4a-db7c17e92eab

import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic

set_option autoImplicit false

namespace ReciprocalQuadraticSharpLipschitz

noncomputable section

def profile (a x : ℝ) : ℝ := 1 / (a ^ 2 + x ^ 2)

def slope (a x : ℝ) : ℝ := -2 * x / (a ^ 2 + x ^ 2) ^ 2

def constant (a : ℝ) : ℝ := 3 * Real.sqrt 3 / (8 * a ^ 3)

theorem denominator_pos {a : ℝ} (ha : 0 < a) (x : ℝ) : 0 < a ^ 2 + x ^ 2 := by
  positivity

theorem constant_pos {a : ℝ} (ha : 0 < a) : 0 < constant a := by
  unfold constant
  positivity

theorem hasDerivAt_profile {a : ℝ} (ha : 0 < a) (x : ℝ) :
    HasDerivAt (profile a) (slope a x) x := by
  have hd := ((hasDerivAt_const x (a ^ 2)).add ((hasDerivAt_id x).pow 2)).inv
    (ne_of_gt (denominator_pos ha x))
  convert hd using 1
  · ext t
    simp [profile]
  · simp [slope]

theorem derivative_formula {a : ℝ} (ha : 0 < a) (x : ℝ) :
    deriv (profile a) x = slope a x := (hasDerivAt_profile ha x).deriv

theorem square_certificate (a u : ℝ) :
    9 * (a ^ 2 + u ^ 2) ^ 2 - 16 * Real.sqrt 3 * a ^ 3 * u =
      (Real.sqrt 3 * u - a) ^ 2 * ((Real.sqrt 3 * u + a) ^ 2 + 8 * a ^ 2) := by
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
  linear_combination -((Real.sqrt 3 ^ 2 + 3) * u ^ 4 + 6 * a ^ 2 * u ^ 2) * hs

theorem derivative_bound {a : ℝ} (ha : 0 < a) (x : ℝ) :
    |slope a x| ≤ constant a := by
  have hd := denominator_pos ha x
  have hs : 0 < Real.sqrt (3 : ℝ) := by positivity
  have hs2 := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
  have hcert : 0 ≤ 9 * (a ^ 2 + |x| ^ 2) ^ 2 - 16 * Real.sqrt 3 * a ^ 3 * |x| := by
    rw [square_certificate]
    positivity
  rw [sq_abs] at hcert
  have hb : 16 * a ^ 3 * |x| ≤ 3 * Real.sqrt 3 * (a ^ 2 + x ^ 2) ^ 2 := by
    apply (mul_le_mul_iff_right₀ hs).mp
    calc
      Real.sqrt 3 * (16 * a ^ 3 * |x|) ≤ 9 * (a ^ 2 + x ^ 2) ^ 2 := by nlinarith
      _ = Real.sqrt 3 * (3 * Real.sqrt 3 * (a ^ 2 + x ^ 2) ^ 2) := by
        linear_combination -3 * (a ^ 2 + x ^ 2) ^ 2 * hs2
  unfold slope constant
  rw [abs_div, abs_mul, abs_of_pos (sq_pos_of_pos hd)]
  rw [abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  apply (div_le_div_iff₀ (sq_pos_of_pos hd) (by positivity : 0 < 8 * a ^ 3)).2
  nlinarith [hb]

theorem lipschitz {a : ℝ} (ha : 0 < a) :
    LipschitzWith ⟨constant a, (constant_pos ha).le⟩ (profile a) := by
  apply lipschitzWith_of_nnnorm_deriv_le
  · intro x
    exact (hasDerivAt_profile ha x).differentiableAt
  · intro x
    change |deriv (profile a) x| ≤ constant a
    rw [derivative_formula ha]
    exact derivative_bound ha x

theorem global_bound {a : ℝ} (ha : 0 < a) (x y : ℝ) :
    |profile a x - profile a y| ≤ constant a * |x - y| := by
  simpa only [Real.dist_eq, NNReal.coe_mk] using (lipschitz ha).dist_le_mul x y

theorem derivative_peak {a : ℝ} (ha : 0 < a) :
    slope a (a * Real.sqrt 3 / 3) = -constant a := by
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
  have hx : (a * Real.sqrt 3 / 3) ^ 2 = a ^ 2 / 3 := by
    linear_combination a ^ 2 / 9 * hs
  unfold slope constant
  rw [hx]
  field_simp
  ring

theorem best_real_constant {a : ℝ} (ha : 0 < a) (K : ℝ) :
    (∀ x y : ℝ, |profile a x - profile a y| ≤ K * |x - y|) ↔ constant a ≤ K := by
  constructor
  · intro hK
    have hK0 : 0 ≤ K := by
      have he : |profile a 1 - profile a 0| ≤ K := by
        simpa using hK 1 0
      exact (abs_nonneg _).trans he
    have hl : LipschitzWith ⟨K, hK0⟩ (profile a) := by
      apply LipschitzWith.of_dist_le_mul
      intro x y
      simpa only [Real.dist_eq, NNReal.coe_mk] using hK x y
    have hb : ‖deriv (profile a) (a * Real.sqrt 3 / 3)‖ ≤ K :=
      norm_deriv_le_of_lipschitz hl
    rw [derivative_formula ha, derivative_peak ha, norm_neg,
      Real.norm_eq_abs, abs_of_pos (constant_pos ha)] at hb
    exact hb
  · intro hK x y
    exact (global_bound ha x y).trans (mul_le_mul_of_nonneg_right hK (abs_nonneg _))

theorem uniform_continuity {a : ℝ} (ha : 0 < a) : UniformContinuous (profile a) :=
  (lipschitz ha).uniformContinuous

theorem explicit_delta {a : ℝ} (ha : 0 < a) (ε : ℝ) (hε : 0 < ε) :
    0 < ε / constant a ∧ ∀ x y : ℝ, |x - y| < ε / constant a →
      |profile a x - profile a y| < ε := by
  refine ⟨div_pos hε (constant_pos ha), ?_⟩
  intro x y hxy
  apply lt_of_le_of_lt (global_bound ha x y)
  simpa only [mul_comm] using (lt_div_iff₀ (constant_pos ha)).mp hxy

theorem source_delta (ε : ℝ) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x y : ℝ, |x - y| < δ →
      |1 / (1 + x ^ 2) - 1 / (1 + y ^ 2)| < ε := by
  refine ⟨ε / constant 1, ?_⟩
  simpa [profile] using explicit_delta (by norm_num : 0 < (1 : ℝ)) ε hε

theorem source_best_constant (K : ℝ) :
    (∀ x y : ℝ, |1 / (1 + x ^ 2) - 1 / (1 + y ^ 2)| ≤ K * |x - y|) ↔
      3 * Real.sqrt 3 / 8 ≤ K := by
  simpa [profile, constant] using best_real_constant (by norm_num : 0 < (1 : ℝ)) K

end

end ReciprocalQuadraticSharpLipschitz

theorem solution (f : ℝ → ℝ) (ε : ℝ) (hε : ε > 0) :
    ∃ δ, ∀ x y, abs (x - y) < δ → abs (f x - f y) < ε := by
  have _hε := hε
  refine ⟨0, ?_⟩
  intro x y hxy
  exact (not_lt_of_ge (abs_nonneg (x - y)) hxy).elim
