-- Prove2me | solution 1 for lean_workbook_plus_49379
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T09:01:25.743516+00:00
-- url     : https://prove2.me/submissions/b1034ab1-be26-4cb4-a4ae-e9621ceb84fd

import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

open Filter Topology

theorem difference_quotient_cancellation (f g : ℝ → ℝ) (c x : ℝ) :
    (f x - f c) / (g x - g c) =
      (f x - f c) / (x - c) * (x - c) / (g x - g c) := by
  by_cases hx : x = c
  · subst x
    simp only [sub_self, zero_div, zero_mul]
  · rw [div_mul_cancel₀ _ (sub_ne_zero.mpr hx)]

theorem ratio_of_difference_quotients_tendsto (f g : ℝ → ℝ) (c d e : ℝ)
    (hf : HasDerivAt f d c) (hg : HasDerivAt g e c) (he : e ≠ 0) :
    Tendsto (fun x => (f x - f c) / (g x - g c)) (𝓝[≠] c) (𝓝 (d / e)) := by
  have ht := hf.tendsto_slope.div hg.tendsto_slope he
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin] with x hx
  have hxc : x - c ≠ 0 := sub_ne_zero.mpr hx
  change slope f c x / slope g c x = (f x - f c) / (g x - g c)
  simp only [slope_def_field]
  rw [div_div_div_cancel_right₀ hxc]

theorem sqrt_affine_hasDerivAt (A c : ℝ) (hc : c < A) :
    HasDerivAt (fun x => Real.sqrt (A - x)) (-1 / (2 * Real.sqrt (A - c))) c := by
  simpa only [id_eq] using ((hasDerivAt_id c).const_sub A).sqrt (by linarith : A - c ≠ 0)

theorem sqrt_difference_rationalization (A c x : ℝ) (hc : c < A) (hx : x ≤ A) :
    Real.sqrt (A - x) - Real.sqrt (A - c) =
      (c - x) / (Real.sqrt (A - x) + Real.sqrt (A - c)) := by
  have hp : 0 < Real.sqrt (A - c) := Real.sqrt_pos.mpr (by linarith)
  have hn := Real.sqrt_nonneg (A - x)
  have hd : Real.sqrt (A - x) + Real.sqrt (A - c) ≠ 0 := by linarith
  apply (eq_div_iff hd).mpr
  nlinarith [Real.sq_sqrt (by linarith : 0 ≤ A - x), Real.sq_sqrt (by linarith : 0 ≤ A - c)]

theorem sqrt_difference_nonzero (A c x : ℝ) (hc : c < A) (hx : x ≤ A) (hxc : x ≠ c) :
    Real.sqrt (A - x) - Real.sqrt (A - c) ≠ 0 := by
  rw [sqrt_difference_rationalization A c x hc hx]
  exact div_ne_zero (sub_ne_zero.mpr hxc.symm) (by
    have hp : 0 < Real.sqrt (A - c) := Real.sqrt_pos.mpr (by linarith)
    have hn := Real.sqrt_nonneg (A - x)
    linarith)

theorem sqrt_difference_ratio_rationalization (A B c x : ℝ)
    (hcA : c < A) (hcB : c < B) (hxA : x ≤ A) (hxB : x ≤ B) (hxc : x ≠ c) :
    (Real.sqrt (A - x) - Real.sqrt (A - c)) /
        (Real.sqrt (B - x) - Real.sqrt (B - c)) =
      (Real.sqrt (B - x) + Real.sqrt (B - c)) /
        (Real.sqrt (A - x) + Real.sqrt (A - c)) := by
  rw [sqrt_difference_rationalization A c x hcA hxA,
    sqrt_difference_rationalization B c x hcB hxB]
  have ha : Real.sqrt (A - x) + Real.sqrt (A - c) ≠ 0 := by
    have hp := Real.sqrt_pos.mpr (by linarith : 0 < A - c)
    nlinarith [Real.sqrt_nonneg (A - x)]
  have hb : Real.sqrt (B - x) + Real.sqrt (B - c) ≠ 0 := by
    have hp := Real.sqrt_pos.mpr (by linarith : 0 < B - c)
    nlinarith [Real.sqrt_nonneg (B - x)]
  field_simp [ha, hb, sub_ne_zero.mpr hxc.symm]

theorem sqrt_difference_ratio_extension_continuous (A B c : ℝ) (hc : c < A) :
    Continuous (fun x => (Real.sqrt (B - x) + Real.sqrt (B - c)) /
      (Real.sqrt (A - x) + Real.sqrt (A - c))) := by
  apply ((continuous_const.sub continuous_id).sqrt.add continuous_const).div
    ((continuous_const.sub continuous_id).sqrt.add continuous_const)
  intro x
  change Real.sqrt (A - x) + Real.sqrt (A - c) ≠ 0
  have hp := Real.sqrt_pos.mpr (by linarith : 0 < A - c)
  nlinarith [Real.sqrt_nonneg (A - x)]

theorem sqrt_difference_ratio_tendsto (A B c : ℝ) (hcA : c < A) (hcB : c < B) :
    Tendsto (fun x => (Real.sqrt (A - x) - Real.sqrt (A - c)) /
      (Real.sqrt (B - x) - Real.sqrt (B - c))) (𝓝[≠] c)
      (𝓝 (Real.sqrt (B - c) / Real.sqrt (A - c))) := by
  have ha : Real.sqrt (A - c) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by linarith))
  have hb : Real.sqrt (B - c) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by linarith))
  have ht := ratio_of_difference_quotients_tendsto
    (fun x => Real.sqrt (A - x)) (fun x => Real.sqrt (B - x)) c
    (-1 / (2 * Real.sqrt (A - c))) (-1 / (2 * Real.sqrt (B - c)))
    (sqrt_affine_hasDerivAt A c hcA) (sqrt_affine_hasDerivAt B c hcB) (by
      exact div_ne_zero (by norm_num) (mul_ne_zero (by norm_num) hb))
  have he : (-1 / (2 * Real.sqrt (A - c))) / (-1 / (2 * Real.sqrt (B - c))) =
      Real.sqrt (B - c) / Real.sqrt (A - c) := by field_simp
  simpa only [he] using ht

theorem source_sqrt_difference_ratio_limit :
    Tendsto (fun x : ℝ => (Real.sqrt (6 - x) - 2) / (Real.sqrt (3 - x) - 1))
      (𝓝[≠] 2) (𝓝 (1 / 2 : ℝ)) := by
  have hs4 : Real.sqrt ((6 : ℝ) - 2) = 2 := by
    rw [show (6 : ℝ) - 2 = 2 ^ 2 by ring, Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]
  have hs1 : Real.sqrt ((3 : ℝ) - 2) = 1 := by
    rw [show (3 : ℝ) - 2 = 1 by ring, Real.sqrt_one]
  simpa only [hs4, hs1] using sqrt_difference_ratio_tendsto 6 3 2 (by norm_num) (by norm_num)

theorem source_sqrt_difference_ratio_formula (x : ℝ) (hx : x ≤ 3) (hxc : x ≠ 2) :
    (Real.sqrt (6 - x) - 2) / (Real.sqrt (3 - x) - 1) =
      (Real.sqrt (3 - x) + 1) / (Real.sqrt (6 - x) + 2) := by
  have hs4 : Real.sqrt ((6 : ℝ) - 2) = 2 := by
    rw [show (6 : ℝ) - 2 = 2 ^ 2 by ring, Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]
  have hs1 : Real.sqrt ((3 : ℝ) - 2) = 1 := by
    rw [show (3 : ℝ) - 2 = 1 by ring, Real.sqrt_one]
  simpa only [hs4, hs1] using sqrt_difference_ratio_rationalization 6 3 2 x
    (by norm_num) (by norm_num) (by linarith) hx hxc

theorem solution (f g : ℝ → ℝ) (x : ℝ)
    (hf : f = fun (x:ℝ) => (6 - x)^(1 / 2))
    (hg : g = fun (x:ℝ) => (3 - x)^(1 / 2)) :
    (f x - f 2) / (g x - g 2) =
      (f x - f 2) / (x - 2) * (x - 2) / (g x - g 2) :=
  difference_quotient_cancellation f g 2 x

#print axioms difference_quotient_cancellation
#print axioms ratio_of_difference_quotients_tendsto
#print axioms sqrt_affine_hasDerivAt
#print axioms sqrt_difference_rationalization
#print axioms sqrt_difference_nonzero
#print axioms sqrt_difference_ratio_rationalization
#print axioms sqrt_difference_ratio_extension_continuous
#print axioms sqrt_difference_ratio_tendsto
#print axioms source_sqrt_difference_ratio_limit
#print axioms source_sqrt_difference_ratio_formula
#print axioms solution
