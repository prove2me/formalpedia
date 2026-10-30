-- Prove2me | solution 1 for FragmentedPermHAdmissible.fragPerm_third_local_integrand_bound
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-10-28T17:34:16.820692+00:00
-- url     : https://prove2.me/submissions/cf477d63-6ca6-4893-ad9f-ac660dc8e39f

import Definitions.Def_AnalyticCombinatorics_Ch4_Analytic_Bridge
import Definitions.Def_AnalyticCombinatorics_Ch4_Analytic_Poles
import Definitions.Def_AnalyticCombinatorics_Ch8_SaddlePoint_Assembly
import Definitions.Def_AnalyticCombinatorics_Ch8_SaddlePoint_FragmentedPermThirdOrder_x1
import Definitions.Def_AnalyticCombinatorics_Ch8_SaddlePoint_SecondOrderCore
import Definitions.Def_AnalyticCombinatorics_Ch8_SaddlePoint_FragmentedPermHAdmissible
import Definitions.Def_AnalyticCombinatorics_Ch8_SaddlePoint_HAdmissible
import Definitions.Def_AnalyticCombinatorics_Ch8_SaddlePoint_ThirdOrderCore
import Definitions.Def_AnalyticCombinatorics_Ch8_SaddlePoint_FragmentedPermSecondOrder
import Definitions.Def_AnalyticCombinatorics_Ch8_SaddlePoint_FragmentedPermThirdOrder
import Theorems.Thm_FragmentedPermHAdmissible_fragPermThirdLocal_poly_bound
import Theorems.Thm_FragmentedPermHAdmissible_fragPermThirdScaledRemainder_norm_le
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib
import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Analysis.Complex.Basic
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.RingTheory.PowerSeries.Exp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Analytic.Composition
import Mathlib.RingTheory.PowerSeries.Substitution
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.Analytic.RadiusLiminf
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Algebra.Algebra.Rat
import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
import Mathlib.RingTheory.PowerSeries.PiTopology
import Mathlib.Combinatorics.Enumerative.Composition
import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Order.Partition.Finpartition
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.Data.Fintype.EquivFin
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Fintype.Card
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Data.Fintype.Powerset

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
section
/-!
# Fragmented permutations: finite-radius H-admissible saddle data

Fragmented permutations are the labelled class `SET(SEQ_{\ge 1}(Z))`, with EGF
`exp (z / (1 - z))`.  This file packages the finite-radius Hayman data for the
committed `HAdmissible` bridge.  The saddle regime is `r -> 1-`.
-/

open Complex Filter Asymptotics MeasureTheory
open scoped Topology Real NNReal ENNReal Interval PowerSeries

noncomputable section

namespace FragmentedPermHAdmissible

lemma fragPerm_sqrt_b_lower_of_Ioo_half_one {r : ℝ}
    (hr : r ∈ Set.Ioo ((1 : ℝ) / 2) 1) :
    (1 / 2 : ℝ) * (1 - r) ^ (-(3 / 2 : ℝ)) ≤
      Real.sqrt (fragPermSaddleBReal r) := by
  let u : ℝ := 1 - r
  have hu_pos : 0 < u := by dsimp [u]; linarith [hr.2]
  have hu_nonneg : 0 ≤ u := hu_pos.le
  have hden_pos : 0 < u ^ 3 := by positivity
  have hnum_ge : (1 / 2 : ℝ) ≤ r * (1 + r) := by nlinarith [hr.1]
  have hb_lower : (1 / 2 : ℝ) / u ^ 3 ≤ fragPermSaddleBReal r := by
    unfold fragPermSaddleBReal
    dsimp [u] at hden_pos ⊢
    exact div_le_div_of_nonneg_right hnum_ge hden_pos.le
  have hx_sq : ((1 / 2 : ℝ) * u ^ (-(3 / 2 : ℝ))) ^ 2 ≤
      fragPermSaddleBReal r := by
    calc
      ((1 / 2 : ℝ) * u ^ (-(3 / 2 : ℝ))) ^ 2
          = (1 / 4 : ℝ) * u ^ (-(3 : ℝ)) := by
            rw [mul_pow]
            norm_num
            rw [← Real.rpow_natCast]
            rw [← Real.rpow_mul hu_nonneg]
            norm_num
      _ ≤ (1 / 2 : ℝ) * u ^ (-(3 : ℝ)) := by
            have hpow_nonneg : 0 ≤ u ^ (-(3 : ℝ)) := Real.rpow_nonneg hu_nonneg _
            nlinarith
      _ = (1 / 2 : ℝ) / u ^ 3 := by
            rw [Real.rpow_neg hu_nonneg]
            have hu3 : u ^ (3 : ℝ) = u ^ 3 := by
              norm_num [Real.rpow_natCast]
            rw [hu3]
            ring
      _ ≤ fragPermSaddleBReal r := hb_lower
  have hsqrt := Real.le_sqrt_of_sq_le hx_sq
  simpa [u] using hsqrt

lemma fragPerm_saddleLocalRatio_eq (r θ : ℝ) :
    saddleLocalRatio fragPermFun fragPermSaddleAReal fragPermSaddleBReal r θ =
      Complex.exp (fragPermLocalExponent r θ) := by
  unfold saddleLocalRatio fragPermFun fragPermLocalExponent
  rw [← Complex.exp_sub]
  rw [← Complex.exp_add]
  rw [← Complex.exp_sub]
  congr 1
  ring

end FragmentedPermHAdmissible
end
end

/-!
# Third-order saddle data for fragmented permutations

This file adds the finite-radius third-order correction layer for
`exp (z / (1 - z))`.  The proof uses the narrower finite-radius window
`(1-r)^(29/20)`, because the second-order window is too wide for an
`o((1-r)^2)` third-order remainder.
-/

open Complex Filter Asymptotics MeasureTheory
open scoped Topology Real NNReal ENNReal Interval PowerSeries

set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false

noncomputable section

namespace FragmentedPermHAdmissible

lemma fragPermSaddleB5Real_nonneg_of_Ioo_zero_one {r : ℝ}
    (hr : r ∈ Set.Ioo (0 : ℝ) 1) :
    0 ≤ fragPermSaddleB5Real r := by
  unfold fragPermSaddleB5Real
  have hu_pos : 0 < 1 - r := by linarith [hr.2]
  have hr0 : 0 ≤ r := hr.1.le
  have hden : 0 < (1 - r) ^ 6 := pow_pos hu_pos _
  have hnum : 0 ≤ r * (1 + 26 * r + 66 * r ^ 2 + 26 * r ^ 3 + r ^ 4) := by
    positivity
  exact div_nonneg hnum hden.le

lemma fragPermSaddleB6Real_nonneg_of_Ioo_zero_one {r : ℝ}
    (hr : r ∈ Set.Ioo (0 : ℝ) 1) :
    0 ≤ fragPermSaddleB6Real r := by
  unfold fragPermSaddleB6Real
  have hu_pos : 0 < 1 - r := by linarith [hr.2]
  have hr0 : 0 ≤ r := hr.1.le
  have hden : 0 < (1 - r) ^ 7 := pow_pos hu_pos _
  have hnum :
      0 ≤ r * (1 + r) * (1 + 56 * r + 246 * r ^ 2 + 56 * r ^ 3 + r ^ 4) := by
    positivity
  exact div_nonneg hnum hden.le

private lemma fragPermThirdLocalExponent_scaled_split (r x : ℝ) :
    fragPermLocalExponent r (x / Real.sqrt (fragPermSaddleBReal r)) =
      fragPermThirdScaledCubic r x + fragPermThirdScaledQuartic r x +
        fragPermThirdScaledFifth r x + fragPermThirdScaledSixth r x +
          fragPermThirdScaledRemainder r x := by
  unfold fragPermThirdScaledRemainder
  ring

private lemma fragPermSaddleBReal_lower_half {r : ℝ}
    (hr : r ∈ Set.Ioo ((1 : ℝ) / 2) 1) :
    (1 / 2 : ℝ) / (1 - r) ^ 3 ≤ fragPermSaddleBReal r := by
  unfold fragPermSaddleBReal
  have hu_pos : 0 < 1 - r := by linarith [hr.2]
  have hden_pos : 0 < (1 - r) ^ 3 := by positivity
  have hnum_ge : (1 / 2 : ℝ) ≤ r * (1 + r) := by nlinarith [hr.1]
  exact div_le_div_of_nonneg_right hnum_ge hden_pos.le

private lemma fragPermSaddleBReal_inv_le {r : ℝ}
    (hr : r ∈ Set.Ioo ((1 : ℝ) / 2) 1) :
    (fragPermSaddleBReal r)⁻¹ ≤ 2 * (1 - r) ^ 3 := by
  have hu_pos : 0 < 1 - r := by linarith [hr.2]
  have hB_lower := fragPermSaddleBReal_lower_half hr
  have hlow_pos : 0 < (1 / 2 : ℝ) / (1 - r) ^ 3 := by positivity
  have h := inv_anti₀ hlow_pos hB_lower
  calc
    (fragPermSaddleBReal r)⁻¹ ≤ ((1 / 2 : ℝ) / (1 - r) ^ 3)⁻¹ := h
    _ = 2 * (1 - r) ^ 3 := by field_simp [hu_pos.ne']

private lemma fragPermSaddleB3Real_le {r : ℝ}
    (hr : r ∈ Set.Ioo ((1 : ℝ) / 2) 1) :
    fragPermSaddleB3Real r ≤ 6 / (1 - r) ^ 4 := by
  unfold fragPermSaddleB3Real
  have hrpos : 0 < r := lt_trans (by norm_num : (0 : ℝ) < 1 / 2) hr.1
  have hrle : r ≤ 1 := hr.2.le
  have hu_pos : 0 < 1 - r := by linarith [hr.2]
  have hden_pos : 0 < (1 - r) ^ 4 := pow_pos hu_pos _
  have hpoly : 1 + 4 * r + r ^ 2 ≤ 6 := by
    nlinarith [hr.1, hrle, sq_nonneg r, sq_nonneg (1 - r)]
  have hpoly_nonneg : 0 ≤ 1 + 4 * r + r ^ 2 := by positivity
  calc
    r * (1 + 4 * r + r ^ 2) / (1 - r) ^ 4
        ≤ 1 * 6 / (1 - r) ^ 4 := by
          exact div_le_div_of_nonneg_right
            (mul_le_mul hrle hpoly hpoly_nonneg zero_le_one) hden_pos.le
    _ = 6 / (1 - r) ^ 4 := by ring

private lemma fragPermSaddleB4Real_le {r : ℝ}
    (hr : r ∈ Set.Ioo ((1 : ℝ) / 2) 1) :
    fragPermSaddleB4Real r ≤ 24 / (1 - r) ^ 5 := by
  unfold fragPermSaddleB4Real
  have hrpos : 0 < r := lt_trans (by norm_num : (0 : ℝ) < 1 / 2) hr.1
  have hrle : r ≤ 1 := hr.2.le
  have hu_pos : 0 < 1 - r := by linarith [hr.2]
  have hden_pos : 0 < (1 - r) ^ 5 := pow_pos hu_pos _
  have hpoly : 1 + 11 * r + 11 * r ^ 2 + r ^ 3 ≤ 24 := by
    nlinarith [hr.1, hrle, sq_nonneg r, sq_nonneg (1 - r), sq_nonneg (r - 1)]
  have hpoly_nonneg : 0 ≤ 1 + 11 * r + 11 * r ^ 2 + r ^ 3 := by positivity
  calc
    r * (1 + 11 * r + 11 * r ^ 2 + r ^ 3) / (1 - r) ^ 5
        ≤ 1 * 24 / (1 - r) ^ 5 := by
          exact div_le_div_of_nonneg_right
            (mul_le_mul hrle hpoly hpoly_nonneg zero_le_one) hden_pos.le
    _ = 24 / (1 - r) ^ 5 := by ring

private lemma fragPermSaddleB5Real_le {r : ℝ}
    (hr : r ∈ Set.Ioo ((1 : ℝ) / 2) 1) :
    fragPermSaddleB5Real r ≤ 120 / (1 - r) ^ 6 := by
  unfold fragPermSaddleB5Real
  have hrpos : 0 < r := lt_trans (by norm_num : (0 : ℝ) < 1 / 2) hr.1
  have hrle : r ≤ 1 := hr.2.le
  have hu_pos : 0 < 1 - r := by linarith [hr.2]
  have hden_pos : 0 < (1 - r) ^ 6 := pow_pos hu_pos _
  have hpoly :
      1 + 26 * r + 66 * r ^ 2 + 26 * r ^ 3 + r ^ 4 ≤ 120 := by
    nlinarith [hr.1, hrle, sq_nonneg r, sq_nonneg (1 - r), sq_nonneg (r - 1),
      show 0 ≤ r ^ 3 by positivity, show 0 ≤ r ^ 4 by positivity]
  have hpoly_nonneg : 0 ≤ 1 + 26 * r + 66 * r ^ 2 + 26 * r ^ 3 + r ^ 4 := by
    positivity
  calc
    r * (1 + 26 * r + 66 * r ^ 2 + 26 * r ^ 3 + r ^ 4) / (1 - r) ^ 6
        ≤ 1 * 120 / (1 - r) ^ 6 := by
          exact div_le_div_of_nonneg_right
            (mul_le_mul hrle hpoly hpoly_nonneg zero_le_one) hden_pos.le
    _ = 120 / (1 - r) ^ 6 := by ring

private lemma fragPermSaddleB6Real_le {r : ℝ}
    (hr : r ∈ Set.Ioo ((1 : ℝ) / 2) 1) :
    fragPermSaddleB6Real r ≤ 720 / (1 - r) ^ 7 := by
  unfold fragPermSaddleB6Real
  have hrpos : 0 < r := lt_trans (by norm_num : (0 : ℝ) < 1 / 2) hr.1
  have hrle : r ≤ 1 := hr.2.le
  have hu_pos : 0 < 1 - r := by linarith [hr.2]
  have hden_pos : 0 < (1 - r) ^ 7 := pow_pos hu_pos _
  have hpoly :
      1 + 56 * r + 246 * r ^ 2 + 56 * r ^ 3 + r ^ 4 ≤ 360 := by
    nlinarith [hr.1, hrle, sq_nonneg r, sq_nonneg (1 - r), sq_nonneg (r - 1),
      show 0 ≤ r ^ 3 by positivity, show 0 ≤ r ^ 4 by positivity]
  have hpoly_nonneg :
      0 ≤ 1 + 56 * r + 246 * r ^ 2 + 56 * r ^ 3 + r ^ 4 := by
    positivity
  have hnum : r * (1 + r) *
      (1 + 56 * r + 246 * r ^ 2 + 56 * r ^ 3 + r ^ 4) ≤ 720 := by
    have hr1 : r * (1 + r) ≤ 2 := by nlinarith [hr.1, hrle]
    have hfactor_nonneg : 0 ≤ r * (1 + r) := by positivity
    calc
      r * (1 + r) *
          (1 + 56 * r + 246 * r ^ 2 + 56 * r ^ 3 + r ^ 4)
          ≤ 2 * 360 := by
            exact mul_le_mul hr1 hpoly hpoly_nonneg (by norm_num : (0 : ℝ) ≤ 2)
      _ = 720 := by norm_num
  calc
    r * (1 + r) * (1 + 56 * r + 246 * r ^ 2 + 56 * r ^ 3 + r ^ 4) /
        (1 - r) ^ 7
        ≤ 720 / (1 - r) ^ 7 := div_le_div_of_nonneg_right hnum hden_pos.le

section
end

set_option backward.isDefEq.respectTransparency false in
private lemma fragPermSqrtB_inv_le {r : ℝ}
    (hr : r ∈ Set.Ioo ((1 : ℝ) / 2) 1) :
    (Real.sqrt (fragPermSaddleBReal r))⁻¹ ≤
      2 * (1 - r) ^ (3 / 2 : ℝ) := by
  have hu_pos : 0 < 1 - r := by linarith [hr.2]
  have hu_nonneg : 0 ≤ 1 - r := hu_pos.le
  have hlow := fragPerm_sqrt_b_lower_of_Ioo_half_one hr
  have hlow_pos :
      0 < (1 / 2 : ℝ) * (1 - r) ^ (-(3 / 2 : ℝ)) := by
    positivity
  have h := inv_anti₀ hlow_pos hlow
  calc
    (Real.sqrt (fragPermSaddleBReal r))⁻¹
        ≤ ((1 / 2 : ℝ) * (1 - r) ^ (-(3 / 2 : ℝ)))⁻¹ := h
    _ = 2 * (1 - r) ^ (3 / 2 : ℝ) := by
      have hp : 0 < (1 - r) ^ (-(3 / 2 : ℝ)) :=
        Real.rpow_pos_of_pos hu_pos _
      field_simp [hp.ne']
      rw [← Real.rpow_add hu_pos]
      norm_num

private lemma fragPerm_rpow_calc_half {u : ℝ} (hu : 0 < u) :
    (1 / u ^ 4) * (2 * u ^ (3 / 2 : ℝ)) ^ 3 =
      8 * u ^ (1 / 2 : ℝ) := by
  have hun : 0 ≤ u := hu.le
  have hpow :
      (u ^ (3 / 2 : ℝ)) ^ 3 = u ^ (9 / 2 : ℝ) := by
    rw [← Real.rpow_natCast]
    rw [← Real.rpow_mul hun]
    norm_num
  calc
    (1 / u ^ 4) * (2 * u ^ (3 / 2 : ℝ)) ^ 3
        = 8 * (u ^ (9 / 2 : ℝ) / u ^ 4) := by
          rw [mul_pow, hpow]
          ring
    _ = 8 * u ^ (1 / 2 : ℝ) := by
      rw [show u ^ 4 = u ^ (4 : ℝ) by exact (Real.rpow_natCast u 4).symm]
      rw [div_eq_mul_inv]
      rw [← Real.rpow_neg hun (4 : ℝ)]
      rw [← Real.rpow_add hu]
      norm_num

private lemma fragPerm_rpow_calc_one {u : ℝ} (hu : 0 < u) :
    (1 / u ^ 5) * (2 * u ^ 3) ^ 2 = 4 * u := by
  field_simp [hu.ne']
  ring

private lemma fragPerm_rpow_calc_three_halves {u : ℝ} (hu : 0 < u) :
    (1 / u ^ 6) * (2 * u ^ (3 / 2 : ℝ)) ^ 5 =
      32 * u ^ (3 / 2 : ℝ) := by
  have hun : 0 ≤ u := hu.le
  have hpow :
      (u ^ (3 / 2 : ℝ)) ^ 5 = u ^ (15 / 2 : ℝ) := by
    rw [← Real.rpow_natCast]
    rw [← Real.rpow_mul hun]
    norm_num
  calc
    (1 / u ^ 6) * (2 * u ^ (3 / 2 : ℝ)) ^ 5
        = 32 * (u ^ (15 / 2 : ℝ) / u ^ 6) := by
          rw [mul_pow, hpow]
          ring
    _ = 32 * u ^ (3 / 2 : ℝ) := by
      rw [show u ^ 6 = u ^ (6 : ℝ) by exact (Real.rpow_natCast u 6).symm]
      rw [div_eq_mul_inv]
      rw [← Real.rpow_neg hun (6 : ℝ)]
      rw [← Real.rpow_add hu]
      norm_num

private lemma fragPerm_rpow_calc_two {u : ℝ} (hu : 0 < u) :
    (1 / u ^ 7) * (2 * u ^ 3) ^ 3 = 8 * u ^ 2 := by
  field_simp [hu.ne']
  ring

private lemma fragPermThirdScaledCubic_norm_le {r x : ℝ}
    (hr : r ∈ Set.Ioo ((1 : ℝ) / 2) 1) :
    ‖fragPermThirdScaledCubic r x‖ ≤
      10 * (1 - r) ^ (1 / 2 : ℝ) * |x| ^ 3 := by
  let u : ℝ := 1 - r
  have hrpos : 0 < r := lt_trans (by norm_num : (0 : ℝ) < 1 / 2) hr.1
  have hu_pos : 0 < u := by dsimp [u]; linarith [hr.2]
  have hu_nonneg : 0 ≤ u := hu_pos.le
  have hbpos : 0 < fragPermSaddleBReal r := by
    unfold fragPermSaddleBReal
    have hrpos : 0 < r := lt_trans (by norm_num : (0 : ℝ) < 1 / 2) hr.1
    have hnum : 0 < r * (1 + r) := by positivity
    have hden : 0 < (1 - r) ^ 3 := by positivity
    exact div_pos hnum hden
  have hsqrt_pos : 0 < Real.sqrt (fragPermSaddleBReal r) := Real.sqrt_pos.mpr hbpos
  have hb3_nonneg : 0 ≤ fragPermSaddleB3Real r := by
    unfold fragPermSaddleB3Real
    positivity
  have hb3_div : fragPermSaddleB3Real r / 6 ≤ 1 / u ^ 4 := by
    have h : fragPermSaddleB3Real r ≤ 6 / u ^ 4 := by
      simpa [u] using fragPermSaddleB3Real_le hr
    rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 6)]
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using h
  have hinv := fragPermSqrtB_inv_le hr
  have hinv3 :
      (Real.sqrt (fragPermSaddleBReal r))⁻¹ ^ 3 ≤
        (2 * u ^ (3 / 2 : ℝ)) ^ 3 := by
    dsimp [u] at hinv
    exact pow_le_pow_left₀ (inv_nonneg.mpr (Real.sqrt_nonneg _)) hinv 3
  have hcoef :
      ‖(fragPermSaddleB3Real r : ℂ) /
          (6 * (Real.sqrt (fragPermSaddleBReal r) : ℂ) ^ 3)‖ ≤
        10 * u ^ (1 / 2 : ℝ) := by
    calc
      ‖(fragPermSaddleB3Real r : ℂ) /
          (6 * (Real.sqrt (fragPermSaddleBReal r) : ℂ) ^ 3)‖
          = (fragPermSaddleB3Real r / 6) *
              (Real.sqrt (fragPermSaddleBReal r))⁻¹ ^ 3 := by
            rw [norm_div, Complex.norm_real, Real.norm_eq_abs,
              abs_of_nonneg hb3_nonneg]
            simp only [norm_mul, norm_ofNat, norm_pow, Complex.norm_real, Real.norm_eq_abs]
            rw [abs_of_pos hsqrt_pos]
            field_simp [hsqrt_pos.ne']
      _ ≤ (1 / u ^ 4) * (2 * u ^ (3 / 2 : ℝ)) ^ 3 := by
            exact mul_le_mul hb3_div hinv3
              (pow_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _)) 3)
              (div_nonneg (by norm_num) (pow_nonneg hu_nonneg 4))
      _ = 8 * u ^ (1 / 2 : ℝ) := fragPerm_rpow_calc_half hu_pos
      _ ≤ 10 * u ^ (1 / 2 : ℝ) := by
        have hpow : 0 ≤ u ^ (1 / 2 : ℝ) := Real.rpow_nonneg hu_nonneg _
        nlinarith
  calc
    ‖fragPermThirdScaledCubic r x‖
        = ‖(fragPermSaddleB3Real r : ℂ) /
            (6 * (Real.sqrt (fragPermSaddleBReal r) : ℂ) ^ 3)‖ * |x| ^ 3 := by
          unfold fragPermThirdScaledCubic
          rw [norm_mul, norm_mul, norm_neg, norm_I, one_mul, norm_pow,
            Complex.norm_real, Real.norm_eq_abs]
    _ ≤ (10 * u ^ (1 / 2 : ℝ)) * |x| ^ 3 :=
      mul_le_mul_of_nonneg_right hcoef (pow_nonneg (abs_nonneg x) 3)
    _ = 10 * (1 - r) ^ (1 / 2 : ℝ) * |x| ^ 3 := by dsimp [u]

private lemma fragPermThirdScaledQuartic_norm_le {r x : ℝ}
    (hr : r ∈ Set.Ioo ((1 : ℝ) / 2) 1) :
    ‖fragPermThirdScaledQuartic r x‖ ≤ 10 * (1 - r) * |x| ^ 4 := by
  let u : ℝ := 1 - r
  have hrpos : 0 < r := lt_trans (by norm_num : (0 : ℝ) < 1 / 2) hr.1
  have hu_pos : 0 < u := by dsimp [u]; linarith [hr.2]
  have hu_nonneg : 0 ≤ u := hu_pos.le
  have hbpos : 0 < fragPermSaddleBReal r := by
    unfold fragPermSaddleBReal
    have hrpos : 0 < r := lt_trans (by norm_num : (0 : ℝ) < 1 / 2) hr.1
    have hnum : 0 < r * (1 + r) := by positivity
    have hden : 0 < (1 - r) ^ 3 := by positivity
    exact div_pos hnum hden
  have hb4_nonneg : 0 ≤ fragPermSaddleB4Real r := by
    unfold fragPermSaddleB4Real
    positivity
  have hb4_div : fragPermSaddleB4Real r / 24 ≤ 1 / u ^ 5 := by
    have h : fragPermSaddleB4Real r ≤ 24 / u ^ 5 := by
      simpa [u] using fragPermSaddleB4Real_le hr
    rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 24)]
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using h
  have hinv := fragPermSaddleBReal_inv_le hr
  have hinv2 :
      (fragPermSaddleBReal r)⁻¹ ^ 2 ≤ (2 * u ^ 3) ^ 2 := by
    dsimp [u] at hinv
    exact pow_le_pow_left₀ (inv_nonneg.mpr hbpos.le) hinv 2
  have hcoef :
      ‖(fragPermSaddleB4Real r : ℂ) /
          (24 * (fragPermSaddleBReal r : ℂ) ^ 2)‖ ≤ 10 * u := by
    calc
      ‖(fragPermSaddleB4Real r : ℂ) /
          (24 * (fragPermSaddleBReal r : ℂ) ^ 2)‖
          = (fragPermSaddleB4Real r / 24) * (fragPermSaddleBReal r)⁻¹ ^ 2 := by
            rw [norm_div, Complex.norm_real, Real.norm_eq_abs,
              abs_of_nonneg hb4_nonneg]
            simp only [norm_mul, norm_ofNat, norm_pow, Complex.norm_real, Real.norm_eq_abs]
            rw [abs_of_pos hbpos]
            field_simp [hbpos.ne']
      _ ≤ (1 / u ^ 5) * (2 * u ^ 3) ^ 2 := by
            exact mul_le_mul hb4_div hinv2
              (pow_nonneg (inv_nonneg.mpr hbpos.le) 2)
              (div_nonneg (by norm_num) (pow_nonneg hu_nonneg 5))
      _ = 4 * u := fragPerm_rpow_calc_one hu_pos
      _ ≤ 10 * u := by nlinarith [hu_pos]
  calc
    ‖fragPermThirdScaledQuartic r x‖
        = ‖(fragPermSaddleB4Real r : ℂ) /
            (24 * (fragPermSaddleBReal r : ℂ) ^ 2)‖ * |x| ^ 4 := by
          unfold fragPermThirdScaledQuartic
          rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs]
    _ ≤ (10 * u) * |x| ^ 4 :=
      mul_le_mul_of_nonneg_right hcoef (pow_nonneg (abs_nonneg x) 4)
    _ = 10 * (1 - r) * |x| ^ 4 := by dsimp [u]

private lemma fragPermThirdScaledFifth_norm_le {r x : ℝ}
    (hr : r ∈ Set.Ioo ((1 : ℝ) / 2) 1) :
    ‖fragPermThirdScaledFifth r x‖ ≤
      40 * (1 - r) ^ (3 / 2 : ℝ) * |x| ^ 5 := by
  let u : ℝ := 1 - r
  have hrpos : 0 < r := lt_trans (by norm_num : (0 : ℝ) < 1 / 2) hr.1
  have hu_pos : 0 < u := by dsimp [u]; linarith [hr.2]
  have hu_nonneg : 0 ≤ u := hu_pos.le
  have hbpos : 0 < fragPermSaddleBReal r := by
    unfold fragPermSaddleBReal
    dsimp [u] at hu_pos
    positivity
  have hsqrt_pos : 0 < Real.sqrt (fragPermSaddleBReal r) := Real.sqrt_pos.mpr hbpos
  have hb5_nonneg : 0 ≤ fragPermSaddleB5Real r :=
    fragPermSaddleB5Real_nonneg_of_Ioo_zero_one
      ⟨lt_trans (by norm_num : (0 : ℝ) < 1 / 2) hr.1, hr.2⟩
  have hb5_div : fragPermSaddleB5Real r / 120 ≤ 1 / u ^ 6 := by
    have h : fragPermSaddleB5Real r ≤ 120 / u ^ 6 := by
      simpa [u] using fragPermSaddleB5Real_le hr
    rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 120)]
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using h
  have hinv := fragPermSqrtB_inv_le hr
  have hinv5 :
      (Real.sqrt (fragPermSaddleBReal r))⁻¹ ^ 5 ≤
        (2 * u ^ (3 / 2 : ℝ)) ^ 5 := by
    dsimp [u] at hinv
    exact pow_le_pow_left₀ (inv_nonneg.mpr (Real.sqrt_nonneg _)) hinv 5
  have hcoef :
      ‖(fragPermSaddleB5Real r : ℂ) /
          (120 * (Real.sqrt (fragPermSaddleBReal r) : ℂ) ^ 5)‖ ≤
        40 * u ^ (3 / 2 : ℝ) := by
    calc
      ‖(fragPermSaddleB5Real r : ℂ) /
          (120 * (Real.sqrt (fragPermSaddleBReal r) : ℂ) ^ 5)‖
          = (fragPermSaddleB5Real r / 120) *
              (Real.sqrt (fragPermSaddleBReal r))⁻¹ ^ 5 := by
            rw [norm_div, Complex.norm_real, Real.norm_eq_abs,
              abs_of_nonneg hb5_nonneg]
            simp only [norm_mul, norm_ofNat, norm_pow, Complex.norm_real, Real.norm_eq_abs]
            rw [abs_of_pos hsqrt_pos]
            field_simp [hsqrt_pos.ne']
      _ ≤ (1 / u ^ 6) * (2 * u ^ (3 / 2 : ℝ)) ^ 5 := by
            exact mul_le_mul hb5_div hinv5
              (pow_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _)) 5)
              (div_nonneg (by norm_num) (pow_nonneg hu_nonneg 6))
      _ = 32 * u ^ (3 / 2 : ℝ) := fragPerm_rpow_calc_three_halves hu_pos
      _ ≤ 40 * u ^ (3 / 2 : ℝ) := by
        have hpow : 0 ≤ u ^ (3 / 2 : ℝ) := Real.rpow_nonneg hu_nonneg _
        nlinarith
  calc
    ‖fragPermThirdScaledFifth r x‖
        = ‖(fragPermSaddleB5Real r : ℂ) /
            (120 * (Real.sqrt (fragPermSaddleBReal r) : ℂ) ^ 5)‖ * |x| ^ 5 := by
          unfold fragPermThirdScaledFifth
          rw [norm_mul, norm_mul, norm_I, one_mul, norm_pow,
            Complex.norm_real, Real.norm_eq_abs]
    _ ≤ (40 * u ^ (3 / 2 : ℝ)) * |x| ^ 5 :=
      mul_le_mul_of_nonneg_right hcoef (pow_nonneg (abs_nonneg x) 5)
    _ = 40 * (1 - r) ^ (3 / 2 : ℝ) * |x| ^ 5 := by dsimp [u]

private lemma fragPermThirdScaledSixth_norm_le {r x : ℝ}
    (hr : r ∈ Set.Ioo ((1 : ℝ) / 2) 1) :
    ‖fragPermThirdScaledSixth r x‖ ≤ 10 * (1 - r) ^ 2 * |x| ^ 6 := by
  let u : ℝ := 1 - r
  have hrpos : 0 < r := lt_trans (by norm_num : (0 : ℝ) < 1 / 2) hr.1
  have hu_pos : 0 < u := by dsimp [u]; linarith [hr.2]
  have hu_nonneg : 0 ≤ u := hu_pos.le
  have hbpos : 0 < fragPermSaddleBReal r := by
    unfold fragPermSaddleBReal
    dsimp [u] at hu_pos
    positivity
  have hb6_nonneg : 0 ≤ fragPermSaddleB6Real r :=
    fragPermSaddleB6Real_nonneg_of_Ioo_zero_one
      ⟨lt_trans (by norm_num : (0 : ℝ) < 1 / 2) hr.1, hr.2⟩
  have hb6_div : fragPermSaddleB6Real r / 720 ≤ 1 / u ^ 7 := by
    have h : fragPermSaddleB6Real r ≤ 720 / u ^ 7 := by
      simpa [u] using fragPermSaddleB6Real_le hr
    rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 720)]
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using h
  have hinv := fragPermSaddleBReal_inv_le hr
  have hinv3 :
      (fragPermSaddleBReal r)⁻¹ ^ 3 ≤ (2 * u ^ 3) ^ 3 := by
    dsimp [u] at hinv
    exact pow_le_pow_left₀ (inv_nonneg.mpr hbpos.le) hinv 3
  have hcoef :
      ‖(fragPermSaddleB6Real r : ℂ) /
          (720 * (fragPermSaddleBReal r : ℂ) ^ 3)‖ ≤ 10 * u ^ 2 := by
    calc
      ‖(fragPermSaddleB6Real r : ℂ) /
          (720 * (fragPermSaddleBReal r : ℂ) ^ 3)‖
          = (fragPermSaddleB6Real r / 720) * (fragPermSaddleBReal r)⁻¹ ^ 3 := by
            rw [norm_div, Complex.norm_real, Real.norm_eq_abs,
              abs_of_nonneg hb6_nonneg]
            simp only [norm_mul, norm_ofNat, norm_pow, Complex.norm_real, Real.norm_eq_abs]
            rw [abs_of_pos hbpos]
            field_simp [hbpos.ne']
      _ ≤ (1 / u ^ 7) * (2 * u ^ 3) ^ 3 := by
            exact mul_le_mul hb6_div hinv3
              (pow_nonneg (inv_nonneg.mpr hbpos.le) 3)
              (div_nonneg (by norm_num) (pow_nonneg hu_nonneg 7))
      _ = 8 * u ^ 2 := fragPerm_rpow_calc_two hu_pos
      _ ≤ 10 * u ^ 2 := by nlinarith [sq_nonneg u]
  calc
    ‖fragPermThirdScaledSixth r x‖
        = ‖(fragPermSaddleB6Real r : ℂ) /
            (720 * (fragPermSaddleBReal r : ℂ) ^ 3)‖ * |x| ^ 6 := by
          unfold fragPermThirdScaledSixth
          rw [norm_mul, norm_neg, norm_pow, Complex.norm_real, Real.norm_eq_abs]
    _ ≤ (10 * u ^ 2) * |x| ^ 6 :=
      mul_le_mul_of_nonneg_right hcoef (pow_nonneg (abs_nonneg x) 6)
    _ = 10 * (1 - r) ^ 2 * |x| ^ 6 := by dsimp [u]

private lemma fragPermThird_sqrtB_sq {r : ℝ} (hb : 0 < fragPermSaddleBReal r) :
    ((Real.sqrt (fragPermSaddleBReal r) : ℂ) ^ 2) =
      (fragPermSaddleBReal r : ℂ) := by
  exact_mod_cast (Real.sq_sqrt hb.le)

private lemma fragPerm_saddleThirdPoly_eq_scaled_terms {r x : ℝ}
    (hb : 0 < fragPermSaddleBReal r) :
    saddleThirdPoly fragPermSaddleBReal fragPermSaddleB3Real fragPermSaddleB4Real
        fragPermSaddleB5Real fragPermSaddleB6Real r x =
      1 + fragPermThirdScaledCubic r x + fragPermThirdScaledQuartic r x +
        (fragPermThirdScaledCubic r x) ^ 2 / 2 +
        fragPermThirdScaledFifth r x + fragPermThirdScaledSixth r x +
        fragPermThirdScaledCubic r x * fragPermThirdScaledQuartic r x +
        fragPermThirdScaledCubic r x * fragPermThirdScaledFifth r x +
        (fragPermThirdScaledQuartic r x) ^ 2 / 2 +
        (fragPermThirdScaledCubic r x) ^ 3 / 6 +
        (fragPermThirdScaledCubic r x) ^ 2 * fragPermThirdScaledQuartic r x / 2 +
        (fragPermThirdScaledCubic r x) ^ 4 / 24 := by
  have hsqrt_sq := fragPermThird_sqrtB_sq hb
  have hsqrt_ne : (Real.sqrt (fragPermSaddleBReal r) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hb).ne'
  have hb_ne : (fragPermSaddleBReal r : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr hb.ne'
  have hsqrt_pow6 :
      (Real.sqrt (fragPermSaddleBReal r) : ℂ) ^ 6 =
        (fragPermSaddleBReal r : ℂ) ^ 3 := by
    calc
      (Real.sqrt (fragPermSaddleBReal r) : ℂ) ^ 6 =
          ((Real.sqrt (fragPermSaddleBReal r) : ℂ) ^ 2) ^ 3 := by ring
      _ = (fragPermSaddleBReal r : ℂ) ^ 3 := by rw [hsqrt_sq]
  have hsqrt_pow8 :
      (Real.sqrt (fragPermSaddleBReal r) : ℂ) ^ 8 =
        (fragPermSaddleBReal r : ℂ) ^ 4 := by
    calc
      (Real.sqrt (fragPermSaddleBReal r) : ℂ) ^ 8 =
          ((Real.sqrt (fragPermSaddleBReal r) : ℂ) ^ 2) ^ 4 := by ring
      _ = (fragPermSaddleBReal r : ℂ) ^ 4 := by rw [hsqrt_sq]
  have hsqrt_pow12 :
      (Real.sqrt (fragPermSaddleBReal r) : ℂ) ^ 12 =
        (fragPermSaddleBReal r : ℂ) ^ 6 := by
    calc
      (Real.sqrt (fragPermSaddleBReal r) : ℂ) ^ 12 =
          ((Real.sqrt (fragPermSaddleBReal r) : ℂ) ^ 2) ^ 6 := by ring
      _ = (fragPermSaddleBReal r : ℂ) ^ 6 := by rw [hsqrt_sq]
  unfold saddleThirdPoly saddleSecondPoly fragPermThirdScaledCubic
    fragPermThirdScaledQuartic fragPermThirdScaledFifth fragPermThirdScaledSixth
  rw [← hsqrt_sq]
  field_simp [hsqrt_ne]
  ring_nf
  simp [Complex.I_sq, Complex.I_pow_three, Complex.I_pow_four, Complex.ofReal_pow]
  ring

private lemma complex_exp_third_error_bound (C Q F S R W : ℂ)
    (hW : W = C + Q + F + S + R) (hWnorm : ‖W‖ ≤ 1) :
    ‖Complex.exp W -
      (1 + C + Q + C ^ 2 / 2 + F + S + C * Q + C * F + Q ^ 2 / 2 +
        C ^ 3 / 6 + C ^ 2 * Q / 2 + C ^ 4 / 24)‖ ≤
      Real.exp 1 * ‖W‖ ^ 5 + ‖R‖ +
        ‖W ^ 2 - (C ^ 2 + 2 * C * Q + 2 * C * F + Q ^ 2)‖ +
        ‖W ^ 3 - (C ^ 3 + 3 * C ^ 2 * Q)‖ +
        ‖W ^ 4 - C ^ 4‖ := by
  have hsum :
      (∑ m ∈ Finset.range 5, W ^ m / (m.factorial : ℂ)) =
        1 + W + W ^ 2 / 2 + W ^ 3 / 6 + W ^ 4 / 24 := by
    norm_num [Finset.sum_range_succ]
  have htail :
      ‖Complex.exp W - (1 + W + W ^ 2 / 2 + W ^ 3 / 6 + W ^ 4 / 24)‖ ≤
        Real.exp 1 * ‖W‖ ^ 5 := by
    calc
      ‖Complex.exp W - (1 + W + W ^ 2 / 2 + W ^ 3 / 6 + W ^ 4 / 24)‖ =
          ‖Complex.exp W - ∑ m ∈ Finset.range 5, W ^ m / (m.factorial : ℂ)‖ := by
            rw [hsum]
      _ ≤ ‖W‖ ^ 5 * Real.exp ‖W‖ :=
        Complex.norm_exp_sub_sum_le_norm_mul_exp W 5
      _ ≤ ‖W‖ ^ 5 * Real.exp 1 :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hWnorm)
          (pow_nonneg (norm_nonneg W) 5)
      _ = Real.exp 1 * ‖W‖ ^ 5 := by ring
  have hdecomp :
      Complex.exp W -
        (1 + C + Q + C ^ 2 / 2 + F + S + C * Q + C * F + Q ^ 2 / 2 +
          C ^ 3 / 6 + C ^ 2 * Q / 2 + C ^ 4 / 24) =
        (Complex.exp W - (1 + W + W ^ 2 / 2 + W ^ 3 / 6 + W ^ 4 / 24)) +
          (R + (W ^ 2 - (C ^ 2 + 2 * C * Q + 2 * C * F + Q ^ 2)) / 2 +
            (W ^ 3 - (C ^ 3 + 3 * C ^ 2 * Q)) / 6 +
            (W ^ 4 - C ^ 4) / 24) := by
    rw [hW]
    ring
  rw [hdecomp]
  have hhalf :
      ‖(W ^ 2 - (C ^ 2 + 2 * C * Q + 2 * C * F + Q ^ 2)) / 2‖ ≤
        ‖W ^ 2 - (C ^ 2 + 2 * C * Q + 2 * C * F + Q ^ 2)‖ := by
    rw [norm_div, Complex.norm_ofNat]
    norm_num
  have hsix :
      ‖(W ^ 3 - (C ^ 3 + 3 * C ^ 2 * Q)) / 6‖ ≤
        ‖W ^ 3 - (C ^ 3 + 3 * C ^ 2 * Q)‖ := by
    rw [norm_div, Complex.norm_ofNat]
    have hnon : 0 ≤ ‖W ^ 3 - (C ^ 3 + 3 * C ^ 2 * Q)‖ := norm_nonneg _
    nlinarith
  have htwentyfour :
      ‖(W ^ 4 - C ^ 4) / 24‖ ≤ ‖W ^ 4 - C ^ 4‖ := by
    rw [norm_div, Complex.norm_ofNat]
    have hnon : 0 ≤ ‖W ^ 4 - C ^ 4‖ := norm_nonneg _
    nlinarith
  calc
    ‖(Complex.exp W - (1 + W + W ^ 2 / 2 + W ^ 3 / 6 + W ^ 4 / 24)) +
        (R + (W ^ 2 - (C ^ 2 + 2 * C * Q + 2 * C * F + Q ^ 2)) / 2 +
          (W ^ 3 - (C ^ 3 + 3 * C ^ 2 * Q)) / 6 +
          (W ^ 4 - C ^ 4) / 24)‖
        ≤ ‖Complex.exp W - (1 + W + W ^ 2 / 2 + W ^ 3 / 6 + W ^ 4 / 24)‖ +
            ‖R + (W ^ 2 - (C ^ 2 + 2 * C * Q + 2 * C * F + Q ^ 2)) / 2 +
              (W ^ 3 - (C ^ 3 + 3 * C ^ 2 * Q)) / 6 +
              (W ^ 4 - C ^ 4) / 24‖ := norm_add_le _ _
    _ ≤ Real.exp 1 * ‖W‖ ^ 5 +
          ‖R + (W ^ 2 - (C ^ 2 + 2 * C * Q + 2 * C * F + Q ^ 2)) / 2 +
            (W ^ 3 - (C ^ 3 + 3 * C ^ 2 * Q)) / 6 +
            (W ^ 4 - C ^ 4) / 24‖ := add_le_add htail (le_refl _)
    _ ≤ Real.exp 1 * ‖W‖ ^ 5 +
          (‖R‖ + ‖(W ^ 2 - (C ^ 2 + 2 * C * Q + 2 * C * F + Q ^ 2)) / 2‖ +
            ‖(W ^ 3 - (C ^ 3 + 3 * C ^ 2 * Q)) / 6‖ +
            ‖(W ^ 4 - C ^ 4) / 24‖) := by
          let A : ℂ := (W ^ 2 - (C ^ 2 + 2 * C * Q + 2 * C * F + Q ^ 2)) / 2
          let B : ℂ := (W ^ 3 - (C ^ 3 + 3 * C ^ 2 * Q)) / 6
          let D : ℂ := (W ^ 4 - C ^ 4) / 24
          have htri :
              ‖R + (W ^ 2 - (C ^ 2 + 2 * C * Q + 2 * C * F + Q ^ 2)) / 2 +
                (W ^ 3 - (C ^ 3 + 3 * C ^ 2 * Q)) / 6 +
                (W ^ 4 - C ^ 4) / 24‖ ≤
                ‖R‖ + ‖(W ^ 2 - (C ^ 2 + 2 * C * Q + 2 * C * F + Q ^ 2)) / 2‖ +
                  ‖(W ^ 3 - (C ^ 3 + 3 * C ^ 2 * Q)) / 6‖ +
                  ‖(W ^ 4 - C ^ 4) / 24‖ := by
            change ‖R + A + B + D‖ ≤ ‖R‖ + ‖A‖ + ‖B‖ + ‖D‖
            calc
              ‖R + A + B + D‖ ≤ ‖R + A + B‖ + ‖D‖ := norm_add_le _ _
              _ ≤ (‖R + A‖ + ‖B‖) + ‖D‖ := by
                have hRAB : ‖R + A + B‖ ≤ ‖R + A‖ + ‖B‖ :=
                  norm_add_le (R + A) B
                nlinarith
              _ ≤ ((‖R‖ + ‖A‖) + ‖B‖) + ‖D‖ := by
                have hRA : ‖R + A‖ ≤ ‖R‖ + ‖A‖ := norm_add_le R A
                nlinarith
              _ = ‖R‖ + ‖A‖ + ‖B‖ + ‖D‖ := by ring
          exact add_le_add (le_refl (Real.exp 1 * ‖W‖ ^ 5)) htri
    _ ≤ Real.exp 1 * ‖W‖ ^ 5 + ‖R‖ +
          ‖W ^ 2 - (C ^ 2 + 2 * C * Q + 2 * C * F + Q ^ 2)‖ +
          ‖W ^ 3 - (C ^ 3 + 3 * C ^ 2 * Q)‖ +
          ‖W ^ 4 - C ^ 4‖ := by
          nlinarith [hhalf, hsix, htwentyfour]

private lemma complex_norm_add4_le (z1 z2 z3 z4 : ℂ) :
    ‖z1 + z2 + z3 + z4‖ ≤ ‖z1‖ + ‖z2‖ + ‖z3‖ + ‖z4‖ := by
  have h12 : ‖z1 + z2‖ ≤ ‖z1‖ + ‖z2‖ := norm_add_le z1 z2
  have h123 : ‖z1 + z2 + z3‖ ≤ ‖z1 + z2‖ + ‖z3‖ :=
    norm_add_le (z1 + z2) z3
  have h1234 : ‖z1 + z2 + z3 + z4‖ ≤ ‖z1 + z2 + z3‖ + ‖z4‖ :=
    norm_add_le (z1 + z2 + z3) z4
  nlinarith

private lemma complex_norm_add5_le (z1 z2 z3 z4 z5 : ℂ) :
    ‖z1 + z2 + z3 + z4 + z5‖ ≤
      ‖z1‖ + ‖z2‖ + ‖z3‖ + ‖z4‖ + ‖z5‖ := by
  have h4 := complex_norm_add4_le z1 z2 z3 z4
  have h5 : ‖z1 + z2 + z3 + z4 + z5‖ ≤ ‖z1 + z2 + z3 + z4‖ + ‖z5‖ :=
    norm_add_le (z1 + z2 + z3 + z4) z5
  nlinarith

private lemma fragPermThirdScaledRemainderConst_pos :
    0 < fragPermThirdScaledRemainderConst := by
  unfold fragPermThirdScaledRemainderConst
  positivity

end FragmentedPermHAdmissible
end

open FragmentedPermHAdmissible
open Complex Filter Asymptotics MeasureTheory
open scoped Topology Real NNReal ENNReal Interval PowerSeries
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option backward.isDefEq.respectTransparency false in
theorem solution {r x : ℝ}
    (hr : r ∈ Set.Ioo ((1 : ℝ) / 2) 1)
    (hθδ : |x / Real.sqrt (fragPermSaddleBReal r)| ≤ fragPermThirdSaddleDeltaReal r)
    (hδle : fragPermThirdSaddleDeltaReal r ≤ 1)
    (hδu : fragPermThirdSaddleDeltaReal r ≤ (1 - r) / 4)
    (hWnorm :
      ‖fragPermLocalExponent r (x / Real.sqrt (fragPermSaddleBReal r))‖ ≤ 1) :
    ‖Complex.exp (-(x ^ 2) / 2) *
        (saddleLocalRatio fragPermFun fragPermSaddleAReal fragPermSaddleBReal r
            (x / Real.sqrt (fragPermSaddleBReal r)) -
          saddleThirdPoly fragPermSaddleBReal fragPermSaddleB3Real fragPermSaddleB4Real
            fragPermSaddleB5Real fragPermSaddleB6Real r x)‖
      ≤ fragPermThirdLocalL1Const * (1 - r) ^ (5 / 2 : ℝ) *
          fragPermThirdLocalDom x := by
  let u : ℝ := 1 - r
  let A : ℝ := u ^ (1 / 2 : ℝ)
  let B : ℝ := u
  let D : ℝ := u ^ (3 / 2 : ℝ)
  let E : ℝ := u ^ 2
  let P : ℝ := u ^ (5 / 2 : ℝ)
  let C : ℂ := fragPermThirdScaledCubic r x
  let Q : ℂ := fragPermThirdScaledQuartic r x
  let F : ℂ := fragPermThirdScaledFifth r x
  let S : ℂ := fragPermThirdScaledSixth r x
  let R : ℂ := fragPermThirdScaledRemainder r x
  let W : ℂ := fragPermLocalExponent r (x / Real.sqrt (fragPermSaddleBReal r))
  let y : ℝ := |x|
  let K : ℝ := fragPermThirdScaledRemainderConst
  let T : ℝ := 10 * y ^ 3
  let S1 : ℝ := 10 * y ^ 3 + 10 * y ^ 4 + 40 * y ^ 5 + 10 * y ^ 6 + K * y ^ 7
  let S2 : ℝ := 10 * y ^ 4 + 40 * y ^ 5 + 10 * y ^ 6 + K * y ^ 7
  let S3 : ℝ := 10 * y ^ 6 + K * y ^ 7
  let S4 : ℝ := 40 * y ^ 5 + 10 * y ^ 6 + K * y ^ 7
  let G : ℝ := ∑ k ∈ Finset.range 36, y ^ k
  have hu_pos : 0 < u := by dsimp [u]; linarith [hr.2]
  have hu_nonneg : 0 ≤ u := hu_pos.le
  have hu_le_one : u ≤ 1 := by dsimp [u]; linarith [hr.1]
  have hy0 : 0 ≤ y := by dsimp [y]; exact abs_nonneg x
  have hK_nonneg : 0 ≤ K := by dsimp [K]; exact fragPermThirdScaledRemainderConst_pos.le
  have hA_nonneg : 0 ≤ A := by dsimp [A]; exact Real.rpow_nonneg hu_nonneg _
  have hB_nonneg : 0 ≤ B := by dsimp [B]; exact hu_nonneg
  have hD_nonneg : 0 ≤ D := by dsimp [D]; exact Real.rpow_nonneg hu_nonneg _
  have hE_nonneg : 0 ≤ E := by dsimp [E]; positivity
  have hP_nonneg : 0 ≤ P := by dsimp [P]; exact Real.rpow_nonneg hu_nonneg _
  have hS1_nonneg : 0 ≤ S1 := by dsimp [S1]; positivity
  have hS2_nonneg : 0 ≤ S2 := by dsimp [S2]; positivity
  have hS3_nonneg : 0 ≤ S3 := by dsimp [S3]; positivity
  have hS4_nonneg : 0 ≤ S4 := by dsimp [S4]; positivity
  have hT_nonneg : 0 ≤ T := by dsimp [T]; positivity
  have hrpow_le (a b : ℝ) (hab : a ≤ b) : u ^ b ≤ u ^ a :=
    Real.rpow_le_rpow_of_exponent_ge hu_pos hu_le_one hab
  have hB_le_A : B ≤ A := by
    dsimp [B, A]
    simpa [Real.rpow_one] using (hrpow_le (1 / 2 : ℝ) 1 (by norm_num))
  have hD_le_A : D ≤ A := by
    dsimp [D, A]
    exact hrpow_le (1 / 2 : ℝ) (3 / 2 : ℝ) (by norm_num)
  have hE_le_A : E ≤ A := by
    dsimp [E, A]
    rw [show u ^ 2 = u ^ (2 : ℝ) by exact (Real.rpow_natCast u 2).symm]
    exact hrpow_le (1 / 2 : ℝ) 2 (by norm_num)
  have hP_le_A : P ≤ A := by
    dsimp [P, A]
    exact hrpow_le (1 / 2 : ℝ) (5 / 2 : ℝ) (by norm_num)
  have hD_le_B : D ≤ B := by
    dsimp [D, B]
    simpa [Real.rpow_one] using (hrpow_le 1 (3 / 2 : ℝ) (by norm_num))
  have hE_le_B : E ≤ B := by
    dsimp [E, B]
    simpa [Real.rpow_one, Real.rpow_natCast] using (hrpow_le 1 2 (by norm_num))
  have hP_le_B : P ≤ B := by
    dsimp [P, B]
    simpa [Real.rpow_one] using (hrpow_le 1 (5 / 2 : ℝ) (by norm_num))
  have hE_le_D : E ≤ D := by
    dsimp [E, D]
    rw [show u ^ 2 = u ^ (2 : ℝ) by exact (Real.rpow_natCast u 2).symm]
    exact hrpow_le (3 / 2 : ℝ) 2 (by norm_num)
  have hP_le_D : P ≤ D := by
    dsimp [P, D]
    exact hrpow_le (3 / 2 : ℝ) (5 / 2 : ℝ) (by norm_num)
  have hA2 : A ^ 2 = B := by
    dsimp [A, B]
    calc
      (u ^ (1 / 2 : ℝ)) ^ 2 = u ^ ((1 / 2 : ℝ) * 2) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hu_nonneg]
        norm_num
      _ = u ^ (1 : ℝ) := by norm_num
      _ = u := by rw [Real.rpow_one]
  have hA3 : A ^ 3 = D := by
    dsimp [A, D]
    calc
      (u ^ (1 / 2 : ℝ)) ^ 3 = u ^ ((1 / 2 : ℝ) * 3) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hu_nonneg]
        norm_num
      _ = u ^ (3 / 2 : ℝ) := by norm_num
  have hA5 : A ^ 5 = P := by
    dsimp [A, P]
    calc
      (u ^ (1 / 2 : ℝ)) ^ 5 = u ^ ((1 / 2 : ℝ) * 5) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hu_nonneg]
        norm_num
      _ = u ^ (5 / 2 : ℝ) := by norm_num
  have hBD : B * D = P := by
    dsimp [B, D, P]
    have h : u ^ (1 : ℝ) * u ^ (3 / 2 : ℝ) = u ^ (5 / 2 : ℝ) := by
      rw [← Real.rpow_add hu_pos]
      norm_num
    simpa [Real.rpow_one] using h
  have hAE : A * E = P := by
    dsimp [A, E, P]
    rw [show u ^ 2 = u ^ (2 : ℝ) by exact (Real.rpow_natCast u 2).symm]
    rw [← Real.rpow_add hu_pos]
    norm_num
  have hA2D : A ^ 2 * D = P := by
    rw [hA2]
    exact hBD
  have hAB2 : A * B ^ 2 = P := by
    have hB2 : B ^ 2 = E := by dsimp [B, E]
    rw [hB2]
    exact hAE
  have hA3B : A ^ 3 * B = P := by
    rw [hA3]
    simpa [mul_comm] using hBD
  have hD2_le_P : D ^ 2 ≤ P := by
    dsimp [D, P]
    calc
      (u ^ (3 / 2 : ℝ)) ^ 2 = u ^ ((3 / 2 : ℝ) * 2) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hu_nonneg]
        norm_num
      _ = u ^ (3 : ℝ) := by norm_num
      _ ≤ u ^ (5 / 2 : ℝ) := hrpow_le (5 / 2 : ℝ) 3 (by norm_num)
  have hE2_le_P : E ^ 2 ≤ P := by
    dsimp [E, P]
    calc
      (u ^ 2) ^ 2 = u ^ (4 : ℝ) := by
        rw [show u ^ 2 = u ^ (2 : ℝ) by exact (Real.rpow_natCast u 2).symm]
        rw [← Real.rpow_natCast, ← Real.rpow_mul hu_nonneg]
        norm_num
      _ ≤ u ^ (5 / 2 : ℝ) := hrpow_le (5 / 2 : ℝ) 4 (by norm_num)
  have hB3_le_P : B ^ 3 ≤ P := by
    dsimp [B, P]
    rw [show u ^ 3 = u ^ (3 : ℝ) by exact (Real.rpow_natCast u 3).symm]
    exact hrpow_le (5 / 2 : ℝ) 3 (by norm_num)
  have hbpos : 0 < fragPermSaddleBReal r := by
    unfold fragPermSaddleBReal
    have hrpos : 0 < r := lt_trans (by norm_num : (0 : ℝ) < 1 / 2) hr.1
    have hnum : 0 < r * (1 + r) := by
      exact mul_pos hrpos (by linarith)
    have hden : 0 < (1 - r) ^ 3 := by
      exact pow_pos (by linarith [hr.2] : 0 < 1 - r) _
    exact div_pos hnum hden
  have hWsplit : W = C + Q + F + S + R := by
    dsimp [W, C, Q, F, S, R]
    exact fragPermThirdLocalExponent_scaled_split r x
  have hPpoly :
      saddleThirdPoly fragPermSaddleBReal fragPermSaddleB3Real fragPermSaddleB4Real
          fragPermSaddleB5Real fragPermSaddleB6Real r x =
        1 + C + Q + C ^ 2 / 2 + F + S + C * Q + C * F + Q ^ 2 / 2 +
          C ^ 3 / 6 + C ^ 2 * Q / 2 + C ^ 4 / 24 := by
    dsimp [C, Q, F, S]
    exact fragPerm_saddleThirdPoly_eq_scaled_terms hbpos
  have herr := complex_exp_third_error_bound C Q F S R W hWsplit
    (by simpa [W] using hWnorm)
  have hC : ‖C‖ ≤ A * T := by
    calc
      ‖C‖ ≤ 10 * A * y ^ 3 := by
        dsimp [C, A, y, u]
        simpa [mul_assoc] using fragPermThirdScaledCubic_norm_le (r := r) (x := x) hr
      _ = A * T := by dsimp [T]; ring
  have hQ_B : ‖Q‖ ≤ 10 * B * y ^ 4 := by
    dsimp [Q, B, y, u]
    simpa [mul_assoc] using fragPermThirdScaledQuartic_norm_le (r := r) (x := x) hr
  have hF_D : ‖F‖ ≤ 40 * D * y ^ 5 := by
    dsimp [F, D, y, u]
    simpa [mul_assoc] using fragPermThirdScaledFifth_norm_le (r := r) (x := x) hr
  have hS_E : ‖S‖ ≤ 10 * E * y ^ 6 := by
    dsimp [S, E, y, u]
    simpa [mul_assoc] using fragPermThirdScaledSixth_norm_le (r := r) (x := x) hr
  have hR_P : ‖R‖ ≤ K * P * y ^ 7 := by
    dsimp [R, K, P, y, u]
    simpa [mul_assoc] using
      fragPermThirdScaledRemainder_norm_le (r := r) (x := x) hr hθδ hδle hδu
  have hQ_A : ‖Q‖ ≤ 10 * A * y ^ 4 := by
    exact hQ_B.trans
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hB_le_A (by norm_num : (0 : ℝ) ≤ 10))
        (pow_nonneg hy0 4))
  have hF_A : ‖F‖ ≤ 40 * A * y ^ 5 := by
    exact hF_D.trans
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hD_le_A (by norm_num : (0 : ℝ) ≤ 40))
        (pow_nonneg hy0 5))
  have hS_A : ‖S‖ ≤ 10 * A * y ^ 6 := by
    exact hS_E.trans
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hE_le_A (by norm_num : (0 : ℝ) ≤ 10))
        (pow_nonneg hy0 6))
  have hR_A : ‖R‖ ≤ K * A * y ^ 7 := by
    exact hR_P.trans
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hP_le_A hK_nonneg)
        (pow_nonneg hy0 7))
  have hF_B : ‖F‖ ≤ 40 * B * y ^ 5 := by
    exact hF_D.trans
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hD_le_B (by norm_num : (0 : ℝ) ≤ 40))
        (pow_nonneg hy0 5))
  have hS_B : ‖S‖ ≤ 10 * B * y ^ 6 := by
    exact hS_E.trans
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hE_le_B (by norm_num : (0 : ℝ) ≤ 10))
        (pow_nonneg hy0 6))
  have hR_B : ‖R‖ ≤ K * B * y ^ 7 := by
    exact hR_P.trans
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hP_le_B hK_nonneg)
        (pow_nonneg hy0 7))
  have hS_D : ‖S‖ ≤ 10 * D * y ^ 6 := by
    exact hS_E.trans
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hE_le_D (by norm_num : (0 : ℝ) ≤ 10))
        (pow_nonneg hy0 6))
  have hR_D : ‖R‖ ≤ K * D * y ^ 7 := by
    exact hR_P.trans
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hP_le_D hK_nonneg)
        (pow_nonneg hy0 7))
  have hWpoly : ‖W‖ ≤ A * S1 := by
    calc
      ‖W‖ = ‖C + Q + F + S + R‖ := by rw [hWsplit]
      _ ≤ ‖C‖ + ‖Q‖ + ‖F‖ + ‖S‖ + ‖R‖ :=
        complex_norm_add5_le C Q F S R
      _ ≤ A * T + 10 * A * y ^ 4 + 40 * A * y ^ 5 +
            10 * A * y ^ 6 + K * A * y ^ 7 := by
          linarith
      _ = A * S1 := by dsimp [S1, T]; ring
  have hU : ‖C + Q + F‖ ≤ A * S1 := by
    have htri : ‖C + Q + F‖ ≤ ‖C‖ + ‖Q‖ + ‖F‖ := by
      calc
        ‖C + Q + F‖ ≤ ‖C + Q‖ + ‖F‖ := norm_add_le _ _
        _ ≤ (‖C‖ + ‖Q‖) + ‖F‖ := by
          have h := norm_add_le C Q
          linarith
        _ = ‖C‖ + ‖Q‖ + ‖F‖ := by ring
    calc
      ‖C + Q + F‖ ≤ ‖C‖ + ‖Q‖ + ‖F‖ := htri
      _ ≤ A * T + 10 * A * y ^ 4 + 40 * A * y ^ 5 := by linarith
      _ ≤ A * S1 := by
        have hextra : 0 ≤ 10 * A * y ^ 6 + K * A * y ^ 7 := by positivity
        dsimp [S1, T]
        nlinarith
  have hY : ‖Q + F + S + R‖ ≤ B * S2 := by
    calc
      ‖Q + F + S + R‖ ≤ ‖Q‖ + ‖F‖ + ‖S‖ + ‖R‖ :=
        complex_norm_add4_le Q F S R
      _ ≤ 10 * B * y ^ 4 + 40 * B * y ^ 5 + 10 * B * y ^ 6 + K * B * y ^ 7 := by
        linarith
      _ = B * S2 := by dsimp [S2]; ring
  have hV : ‖S + R‖ ≤ E * S3 := by
    calc
      ‖S + R‖ ≤ ‖S‖ + ‖R‖ := norm_add_le _ _
      _ ≤ 10 * E * y ^ 6 + K * E * y ^ 7 := by
        have hR_E : ‖R‖ ≤ K * E * y ^ 7 := by
          exact hR_P.trans
            (mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left
                (by
                  dsimp [P, E]
                  rw [show u ^ 2 = u ^ (2 : ℝ) by
                    exact (Real.rpow_natCast u 2).symm]
                  exact hrpow_le 2 (5 / 2 : ℝ) (by norm_num))
                hK_nonneg)
              (pow_nonneg hy0 7))
        linarith
      _ = E * S3 := by dsimp [S3]; ring
  have hZ : ‖F + S + R‖ ≤ D * S4 := by
    have htri : ‖F + S + R‖ ≤ ‖F‖ + ‖S‖ + ‖R‖ := by
      calc
        ‖F + S + R‖ ≤ ‖F + S‖ + ‖R‖ := norm_add_le _ _
        _ ≤ (‖F‖ + ‖S‖) + ‖R‖ := by
          have h := norm_add_le F S
          linarith
        _ = ‖F‖ + ‖S‖ + ‖R‖ := by ring
    calc
      ‖F + S + R‖ ≤ ‖F‖ + ‖S‖ + ‖R‖ := htri
      _ ≤ 40 * D * y ^ 5 + 10 * D * y ^ 6 + K * D * y ^ 7 := by linarith
      _ = D * S4 := by dsimp [S4]; ring
  have hW5 :
      Real.exp 1 * ‖W‖ ^ 5 ≤ Real.exp 1 * P * S1 ^ 5 := by
    calc
      Real.exp 1 * ‖W‖ ^ 5 ≤ Real.exp 1 * (A * S1) ^ 5 :=
        mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (norm_nonneg W) hWpoly 5) (Real.exp_pos 1).le
      _ = Real.exp 1 * P * S1 ^ 5 := by
        rw [mul_pow, hA5]
        ring
  have hquad :
      ‖W ^ 2 - (C ^ 2 + 2 * C * Q + 2 * C * F + Q ^ 2)‖ ≤
        P * (1600 * y ^ 10 + 800 * y ^ 9 + 2 * S1 * S3 + S3 ^ 2) := by
    have hquad_id :
        W ^ 2 - (C ^ 2 + 2 * C * Q + 2 * C * F + Q ^ 2) =
          F ^ 2 + 2 * Q * F + 2 * (C + Q + F) * (S + R) + (S + R) ^ 2 := by
      rw [hWsplit]
      ring
    have hF2 : ‖F ^ 2‖ ≤ 1600 * P * y ^ 10 := by
      rw [norm_pow]
      calc
        ‖F‖ ^ 2 ≤ (40 * D * y ^ 5) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg F) hF_D 2
        _ = 1600 * D ^ 2 * y ^ 10 := by ring
        _ ≤ 1600 * P * y ^ 10 := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hD2_le_P (by norm_num : (0 : ℝ) ≤ 1600))
            (pow_nonneg hy0 10)
    have hQF : ‖2 * Q * F‖ ≤ 800 * P * y ^ 9 := by
      calc
        ‖2 * Q * F‖ ≤ 2 * ‖Q‖ * ‖F‖ := by
          rw [norm_mul, norm_mul, Complex.norm_ofNat]
        _ ≤ 2 * (10 * B * y ^ 4) * (40 * D * y ^ 5) := by
          gcongr
        _ = 800 * (B * D) * y ^ 9 := by ring
        _ = 800 * P * y ^ 9 := by rw [hBD]
    have hUV : ‖2 * (C + Q + F) * (S + R)‖ ≤ 2 * P * S1 * S3 := by
      calc
        ‖2 * (C + Q + F) * (S + R)‖ ≤
            2 * ‖C + Q + F‖ * ‖S + R‖ := by
          rw [norm_mul, norm_mul, Complex.norm_ofNat]
        _ ≤ 2 * (A * S1) * (E * S3) := by
          gcongr
        _ = 2 * (A * E) * S1 * S3 := by ring
        _ = 2 * P * S1 * S3 := by rw [hAE]
    have hV2 : ‖(S + R) ^ 2‖ ≤ P * S3 ^ 2 := by
      rw [norm_pow]
      calc
        ‖S + R‖ ^ 2 ≤ (E * S3) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg (S + R)) hV 2
        _ = E ^ 2 * S3 ^ 2 := by ring
        _ ≤ P * S3 ^ 2 :=
          mul_le_mul_of_nonneg_right hE2_le_P (pow_nonneg hS3_nonneg 2)
    rw [hquad_id]
    calc
      ‖F ^ 2 + 2 * Q * F + 2 * (C + Q + F) * (S + R) + (S + R) ^ 2‖
          ≤ ‖F ^ 2‖ + ‖2 * Q * F‖ +
              ‖2 * (C + Q + F) * (S + R)‖ + ‖(S + R) ^ 2‖ :=
        complex_norm_add4_le _ _ _ _
      _ ≤ 1600 * P * y ^ 10 + 800 * P * y ^ 9 +
            2 * P * S1 * S3 + P * S3 ^ 2 := by linarith
      _ = P * (1600 * y ^ 10 + 800 * y ^ 9 + 2 * S1 * S3 + S3 ^ 2) := by
        ring
  have hcube :
      ‖W ^ 3 - (C ^ 3 + 3 * C ^ 2 * Q)‖ ≤
        P * (3 * T ^ 2 * S4 + 3 * T * S2 ^ 2 + S2 ^ 3) := by
    have hcube_id :
        W ^ 3 - (C ^ 3 + 3 * C ^ 2 * Q) =
          3 * C ^ 2 * (F + S + R) + 3 * C * (Q + F + S + R) ^ 2 +
            (Q + F + S + R) ^ 3 := by
      rw [hWsplit]
      ring
    have hC2Z : ‖3 * C ^ 2 * (F + S + R)‖ ≤ 3 * P * T ^ 2 * S4 := by
      calc
        ‖3 * C ^ 2 * (F + S + R)‖ ≤ 3 * ‖C‖ ^ 2 * ‖F + S + R‖ := by
          rw [norm_mul, norm_mul, Complex.norm_ofNat, norm_pow]
        _ ≤ 3 * (A * T) ^ 2 * (D * S4) := by
          gcongr
        _ = 3 * (A ^ 2 * D) * T ^ 2 * S4 := by ring
        _ = 3 * P * T ^ 2 * S4 := by rw [hA2D]
    have hCY2 : ‖3 * C * (Q + F + S + R) ^ 2‖ ≤ 3 * P * T * S2 ^ 2 := by
      calc
        ‖3 * C * (Q + F + S + R) ^ 2‖ ≤
            3 * ‖C‖ * ‖Q + F + S + R‖ ^ 2 := by
          rw [norm_mul, norm_mul, Complex.norm_ofNat, norm_pow]
        _ ≤ 3 * (A * T) * (B * S2) ^ 2 := by
          gcongr
        _ = 3 * (A * B ^ 2) * T * S2 ^ 2 := by ring
        _ = 3 * P * T * S2 ^ 2 := by rw [hAB2]
    have hY3 : ‖(Q + F + S + R) ^ 3‖ ≤ P * S2 ^ 3 := by
      rw [norm_pow]
      calc
        ‖Q + F + S + R‖ ^ 3 ≤ (B * S2) ^ 3 :=
          pow_le_pow_left₀ (norm_nonneg (Q + F + S + R)) hY 3
        _ = B ^ 3 * S2 ^ 3 := by ring
        _ ≤ P * S2 ^ 3 :=
          mul_le_mul_of_nonneg_right hB3_le_P (pow_nonneg hS2_nonneg 3)
    rw [hcube_id]
    calc
      ‖3 * C ^ 2 * (F + S + R) + 3 * C * (Q + F + S + R) ^ 2 +
          (Q + F + S + R) ^ 3‖
          ≤ ‖3 * C ^ 2 * (F + S + R)‖ +
              ‖3 * C * (Q + F + S + R) ^ 2‖ +
              ‖(Q + F + S + R) ^ 3‖ := by
            calc
              ‖3 * C ^ 2 * (F + S + R) + 3 * C * (Q + F + S + R) ^ 2 +
                  (Q + F + S + R) ^ 3‖
                  ≤ ‖3 * C ^ 2 * (F + S + R) +
                      3 * C * (Q + F + S + R) ^ 2‖ +
                    ‖(Q + F + S + R) ^ 3‖ := norm_add_le _ _
              _ ≤ (‖3 * C ^ 2 * (F + S + R)‖ +
                    ‖3 * C * (Q + F + S + R) ^ 2‖) +
                    ‖(Q + F + S + R) ^ 3‖ := by
                have h := norm_add_le (3 * C ^ 2 * (F + S + R))
                  (3 * C * (Q + F + S + R) ^ 2)
                linarith
              _ = ‖3 * C ^ 2 * (F + S + R)‖ +
                    ‖3 * C * (Q + F + S + R) ^ 2‖ +
                    ‖(Q + F + S + R) ^ 3‖ := by ring
      _ ≤ 3 * P * T ^ 2 * S4 + 3 * P * T * S2 ^ 2 + P * S2 ^ 3 := by
        linarith
      _ = P * (3 * T ^ 2 * S4 + 3 * T * S2 ^ 2 + S2 ^ 3) := by ring
  have hfour :
      ‖W ^ 4 - C ^ 4‖ ≤
        P * (S2 * (S1 ^ 3 + S1 ^ 2 * T + S1 * T ^ 2 + T ^ 3)) := by
    have hfactor :
        ‖W ^ 3 + W ^ 2 * C + W * C ^ 2 + C ^ 3‖ ≤
          A ^ 3 * (S1 ^ 3 + S1 ^ 2 * T + S1 * T ^ 2 + T ^ 3) := by
      calc
        ‖W ^ 3 + W ^ 2 * C + W * C ^ 2 + C ^ 3‖
            ≤ ‖W ^ 3‖ + ‖W ^ 2 * C‖ + ‖W * C ^ 2‖ + ‖C ^ 3‖ :=
          complex_norm_add4_le _ _ _ _
        _ ≤ (A * S1) ^ 3 + (A * S1) ^ 2 * (A * T) +
              (A * S1) * (A * T) ^ 2 + (A * T) ^ 3 := by
            rw [norm_pow, norm_mul, norm_pow, norm_mul, norm_pow, norm_pow]
            gcongr
        _ = A ^ 3 * (S1 ^ 3 + S1 ^ 2 * T + S1 * T ^ 2 + T ^ 3) := by ring
    have hYdiff : ‖W - C‖ ≤ B * S2 := by
      have hdiff : W - C = Q + F + S + R := by
        rw [hWsplit]
        ring
      rw [hdiff]
      exact hY
    have hfactor_nonneg :
        0 ≤ S1 ^ 3 + S1 ^ 2 * T + S1 * T ^ 2 + T ^ 3 := by positivity
    calc
      ‖W ^ 4 - C ^ 4‖ =
          ‖(W - C) * (W ^ 3 + W ^ 2 * C + W * C ^ 2 + C ^ 3)‖ := by
            congr 1
            ring
      _ ≤ (B * S2) *
          (A ^ 3 * (S1 ^ 3 + S1 ^ 2 * T + S1 * T ^ 2 + T ^ 3)) := by
        rw [norm_mul]
        exact mul_le_mul hYdiff hfactor
          (norm_nonneg _)
          (mul_nonneg hB_nonneg hS2_nonneg)
      _ = (A ^ 3 * B) * (S2 * (S1 ^ 3 + S1 ^ 2 * T + S1 * T ^ 2 + T ^ 3)) := by
        ring
      _ = P * (S2 * (S1 ^ 3 + S1 ^ 2 * T + S1 * T ^ 2 + T ^ 3)) := by
        rw [hA3B]
  have hpoly :
      Real.exp 1 * S1 ^ 5 + K * y ^ 7 +
        (1600 * y ^ 10 + 800 * y ^ 9 + 2 * S1 * S3 + S3 ^ 2) +
        (3 * T ^ 2 * S4 + 3 * T * S2 ^ 2 + S2 ^ 3) +
        S2 * (S1 ^ 3 + S1 ^ 2 * T + S1 * T ^ 2 + T ^ 3)
          ≤ fragPermThirdLocalL1Const * G := by
    simpa [K, S1, S2, S3, S4, G, T] using
      (fragPermThirdLocal_poly_bound (y := y) hy0)
  have hdiff :
      ‖Complex.exp W -
        (1 + C + Q + C ^ 2 / 2 + F + S + C * Q + C * F + Q ^ 2 / 2 +
          C ^ 3 / 6 + C ^ 2 * Q / 2 + C ^ 4 / 24)‖
        ≤ fragPermThirdLocalL1Const * P * G := by
    calc
      ‖Complex.exp W -
        (1 + C + Q + C ^ 2 / 2 + F + S + C * Q + C * F + Q ^ 2 / 2 +
          C ^ 3 / 6 + C ^ 2 * Q / 2 + C ^ 4 / 24)‖
          ≤ Real.exp 1 * ‖W‖ ^ 5 + ‖R‖ +
              ‖W ^ 2 - (C ^ 2 + 2 * C * Q + 2 * C * F + Q ^ 2)‖ +
              ‖W ^ 3 - (C ^ 3 + 3 * C ^ 2 * Q)‖ +
              ‖W ^ 4 - C ^ 4‖ := herr
      _ ≤ Real.exp 1 * P * S1 ^ 5 + K * P * y ^ 7 +
          P * (1600 * y ^ 10 + 800 * y ^ 9 + 2 * S1 * S3 + S3 ^ 2) +
          P * (3 * T ^ 2 * S4 + 3 * T * S2 ^ 2 + S2 ^ 3) +
          P * (S2 * (S1 ^ 3 + S1 ^ 2 * T + S1 * T ^ 2 + T ^ 3)) := by
        linarith
      _ = P * (Real.exp 1 * S1 ^ 5 + K * y ^ 7 +
          (1600 * y ^ 10 + 800 * y ^ 9 + 2 * S1 * S3 + S3 ^ 2) +
          (3 * T ^ 2 * S4 + 3 * T * S2 ^ 2 + S2 ^ 3) +
          S2 * (S1 ^ 3 + S1 ^ 2 * T + S1 * T ^ 2 + T ^ 3)) := by ring
      _ ≤ P * (fragPermThirdLocalL1Const * G) :=
        mul_le_mul_of_nonneg_left hpoly hP_nonneg
      _ = fragPermThirdLocalL1Const * P * G := by ring
  rw [fragPerm_saddleLocalRatio_eq]
  rw [hPpoly]
  change
    ‖Complex.exp (-(x ^ 2) / 2) *
      (Complex.exp W -
        (1 + C + Q + C ^ 2 / 2 + F + S + C * Q + C * F + Q ^ 2 / 2 +
          C ^ 3 / 6 + C ^ 2 * Q / 2 + C ^ 4 / 24))‖
      ≤ fragPermThirdLocalL1Const * P * fragPermThirdLocalDom x
  rw [norm_mul]
  have hgauss :
      ‖Complex.exp (-(x ^ 2) / 2)‖ = Real.exp (-(x ^ 2) / 2) := by
    rw [Complex.norm_exp]
    congr 1
    simp [pow_two]
  rw [hgauss]
  unfold fragPermThirdLocalDom
  dsimp [P, G, y, u]
  calc
    Real.exp (-(x ^ 2) / 2) *
        ‖Complex.exp W -
          (1 + C + Q + C ^ 2 / 2 + F + S + C * Q + C * F + Q ^ 2 / 2 +
            C ^ 3 / 6 + C ^ 2 * Q / 2 + C ^ 4 / 24)‖
        ≤ Real.exp (-(x ^ 2) / 2) *
            (fragPermThirdLocalL1Const * (1 - r) ^ (5 / 2 : ℝ) * G) :=
          mul_le_mul_of_nonneg_left hdiff (Real.exp_pos _).le
    _ = fragPermThirdLocalL1Const * (1 - r) ^ (5 / 2 : ℝ) *
          (Real.exp (-(x ^ 2) / 2) * ∑ k ∈ Finset.range 36, |x| ^ k) := by
      ring
