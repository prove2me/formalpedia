-- Prove2me | solution 1 for mme_stothers_positive_stationary_profile_unique
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-21T23:23:39.484204+00:00
-- url     : https://prove2.me/submissions/8493d22b-30d4-420e-a3a6-9f47cddb12ef

import Definitions.Def_mme_stothers_fourth_data
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

open MME.StothersFourth BigOperators

set_option autoImplicit false

private theorem stationary_log_direction_eq_zero
    (b d : Fin 10 → ℝ) (hb : InN b) (hbpos : ∀ i, 0 < b i)
    (hd : InY d) :
    ∑ i, (classMultiplicity i : ℝ) * d i * Real.log (b i) = 0 := by
  have hs := congrArg Real.log hb.2.1
  rw [Real.log_mul (hbpos 2).ne' (pow_pos (hbpos 7) 2).ne',
    Real.log_mul (mul_pos (hbpos 4) (hbpos 5)).ne' (hbpos 9).ne',
    Real.log_mul (hbpos 4).ne' (hbpos 5).ne', Real.log_pow] at hs
  norm_num at hs
  have ht := congrArg Real.log hb.2.2
  rw [Real.log_mul (mul_pos (hbpos 3) (hbpos 7)).ne' (hbpos 8).ne',
    Real.log_mul (hbpos 3).ne' (hbpos 7).ne',
    Real.log_mul (mul_pos (hbpos 4) (hbpos 6)).ne' (hbpos 9).ne',
    Real.log_mul (hbpos 4).ne' (hbpos 6).ne'] at ht
  obtain ⟨s, t, hst⟩ := hd
  simp_rw [hst]
  norm_num [classMultiplicity, kernelSigma, kernelTau, Fin.sum_univ_succ]
  change 2 * s * Real.log (b 2) +
    (2 * t * Real.log (b 3) + ((-(s * 2) + -(t * 2)) * Real.log (b 4) +
    (-(s * 2 * Real.log (b 5)) + (-(2 * t * Real.log (b 6)) +
    (2 * (s * 2 + t) * Real.log (b 7) + (t * 2 * Real.log (b 8) +
    (-(s * 2) + -(t * 2)) * Real.log (b 9))))))) = 0
  nlinarith [mul_eq_zero_of_left (by linarith :
    Real.log (b 2) + 2 * Real.log (b 7) -
      (Real.log (b 4) + Real.log (b 5) + Real.log (b 9)) = 0) s,
    mul_eq_zero_of_left (by linarith :
    Real.log (b 3) + Real.log (b 7) + Real.log (b 8) -
      (Real.log (b 4) + Real.log (b 6) + Real.log (b 9)) = 0) t]

/-- A marginal slice contains at most one strictly positive stationary profile. -/
theorem solution
    (a b : Fin 10 → ℝ) (ha : InN a) (hb : InN b)
    (hapos : ∀ i, 0 < a i) (hbpos : ∀ i, 0 < b i)
    (hsame : InY (fun i ↦ a i - b i)) : a = b := by
  have hza := stationary_log_direction_eq_zero a _ ha hapos hsame
  have hzb := stationary_log_direction_eq_zero b _ hb hbpos hsame
  have hsum : ∑ i, (classMultiplicity i : ℝ) *
      ((a i - b i) * (Real.log (a i) - Real.log (b i))) = 0 := by
    simp_rw [mul_sub, ← mul_assoc]
    rw [Finset.sum_sub_distrib, hza, hzb, sub_self]
  have hw : ∀ i, 0 < (classMultiplicity i : ℝ) := by
    intro i
    fin_cases i <;> norm_num [classMultiplicity]
  have hn : ∀ i, 0 ≤ (a i - b i) * (Real.log (a i) - Real.log (b i)) := by
    intro i
    rcases le_total (b i) (a i) with h | h
    · exact mul_nonneg (sub_nonneg.mpr h)
        (sub_nonneg.mpr (Real.log_le_log (hbpos i) h))
    · exact mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr h)
        (sub_nonpos.mpr (Real.log_le_log (hapos i) h))
  have hz := (Finset.sum_eq_zero_iff_of_nonneg
    (fun i (_ : i ∈ Finset.univ) ↦ mul_nonneg (hw i).le (hn i))).mp hsum
  funext i
  have hprod : (a i - b i) * (Real.log (a i) - Real.log (b i)) = 0 :=
    (mul_eq_zero.mp (hz i (Finset.mem_univ i))).resolve_left (hw i).ne'
  rcases mul_eq_zero.mp hprod with heq | heq
  · exact sub_eq_zero.mp heq
  · exact Real.log_injOn_pos (hapos i) (hbpos i) (sub_eq_zero.mp heq)
