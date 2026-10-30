-- Prove2me | solution 1 for riordan_thirdOrder
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-10-28T12:32:10.656622+00:00
-- url     : https://prove2.me/submissions/9ab9ac24-9dcc-417b-bb9c-6e9afd51754b

import Definitions.Def_AnalyticCombinatorics_Ch4_Analytic_Bridge
import Definitions.Def_AnalyticCombinatorics_Ch4_Analytic_DeltaDomain
import Definitions.Def_AnalyticCombinatorics_Ch4_Analytic_SqrtSingularitySecondOrder
import Definitions.Def_AnalyticCombinatorics_Ch4_Analytic_SqrtSingularityThirdOrder
import Definitions.Def_AnalyticCombinatorics_Ch7_SingularityApp_Motzkin
import Definitions.Def_AnalyticCombinatorics_Ch7_SingularityApp_RiordanSecondOrder
import Definitions.Def_AnalyticCombinatorics_Ch7_SingularityApp_RiordanThirdOrder
import Definitions.Def_AnalyticCombinatorics_Ch7_SingularityApp_Riordan
import Theorems.Thm_sqrt_singularity_thirdOrder_original_of_rescaled_singularity
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.Analytic.RadiusLiminf
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Algebra.Algebra.Rat
import Mathlib.Data.Complex.Basic
import Mathlib
import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Complex.Liouville
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Combinatorics.Enumerative.Catalan
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Choose
import Mathlib.Data.Nat.Fib.Basic
import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Analysis.Complex.Basic
import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
import Mathlib.Combinatorics.Enumerative.Composition
import Mathlib.Data.Fintype.Card

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
section
open Filter ENNReal
open scoped PowerSeries Topology NNReal ENNReal

noncomputable section

namespace PowerSeries

@[simp] lemma coeff_toFMLS (f : PowerSeries ℂ) (n : ℕ) :
    (toFMLS f).coeff n = PowerSeries.coeff (R := ℂ) n f := by
  simp [toFMLS]

@[simp] lemma coeff_mapℂ (f : PowerSeries ℚ) (n : ℕ) :
    PowerSeries.coeff (R := ℂ) n (mapℂ f) =
      algebraMap ℚ ℂ (PowerSeries.coeff (R := ℚ) n f) := by
  simp [mapℂ]

@[simp] lemma nnnorm_toFMLS_apply (f : PowerSeries ℂ) (n : ℕ) :
    ‖toFMLS f n‖₊ = ‖PowerSeries.coeff (R := ℂ) n f‖₊ := by
  apply NNReal.eq
  simp [toFMLS]

end PowerSeries
end
end

section
open Complex Filter
open scoped Topology

lemma zero_mem_deltaDomainArg {R φ : ℝ} (hR : 0 < R) (hφ : φ < Real.pi) :
    (0 : ℂ) ∈ DeltaDomainArg R φ := by
  unfold DeltaDomainArg
  constructor
  · simpa using hR
  constructor
  · norm_num
  · simpa [Complex.arg_neg_one, abs_of_pos Real.pi_pos] using hφ

lemma one_sub_mem_slitPlane_of_mem_delta {R φ : ℝ} {z : ℂ}
    (hφ0 : 0 < φ) (hz : z ∈ DeltaDomainArg R φ) :
    (1 - z) ∈ Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff]
  by_contra hnot
  push Not at hnot
  have harg0 : Complex.arg (z - 1) = 0 := by
    rw [Complex.arg_eq_zero_iff]
    constructor
    · have hre := hnot.1
      simp at hre ⊢
      linarith
    · have him := hnot.2
      simp at him ⊢
      linarith
  have hlt : φ < 0 := by
    simpa [harg0] using hz.2.2
  linarith

lemma analyticOnNhd_one_sub_cpow_deltaDomain {α : ℂ} {R φ : ℝ}
    (hφ0 : 0 < φ) (_hφπ : φ < Real.pi) :
    AnalyticOnNhd ℂ (fun z : ℂ => (1 - z) ^ (-α)) (DeltaDomainArg R φ) := by
  exact (analyticOnNhd_const.sub analyticOnNhd_id).cpow analyticOnNhd_const
    (fun z hz => one_sub_mem_slitPlane_of_mem_delta hφ0 hz)
end

section
/-!
# Motzkin-number asymptotic

This file isolates the Motzkin recurrence and the constant produced by the
square-root singularity at `1 / 3`.
-/

open Complex Filter Asymptotics
open scoped BigOperators PowerSeries Topology

noncomputable section

@[simp] lemma motzkin_zero : motzkin 0 = 1 := by
  simp [motzkin]

@[simp] lemma motzkin_succ (n : ℕ) :
    motzkin (n + 1) =
      motzkin n + ∑ k : Fin n, motzkin k * motzkin (n - 1 - k) := by
  simp [motzkin]

@[simp] lemma coeff_motzkinSeriesℂ (n : ℕ) :
    PowerSeries.coeff (R := ℂ) n motzkinSeriesℂ = (motzkin n : ℂ) := by
  simp [motzkinSeriesℂ]

@[simp] lemma constantCoeff_motzkinSeriesℂ :
    PowerSeries.constantCoeff motzkinSeriesℂ = 1 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
  simp

lemma coeff_X_mul_motzkinSeriesℂ (n : ℕ) :
    PowerSeries.coeff (R := ℂ) (n + 1) (PowerSeries.X * motzkinSeriesℂ) =
      (motzkin n : ℂ) := by
  simp

lemma coeff_X_sq_mul_motzkinSeriesℂ_sq (n : ℕ) :
    PowerSeries.coeff (R := ℂ) (n + 1)
        ((PowerSeries.X : PowerSeries ℂ) ^ 2 * motzkinSeriesℂ ^ 2) =
      ∑ k : Fin n, (motzkin k : ℂ) * (motzkin (n - 1 - k) : ℂ) := by
  set_option backward.isDefEq.respectTransparency false in
    cases n with
    | zero =>
        simp [PowerSeries.coeff_X_pow_mul']
    | succ n =>
        rw [show n + 1 + 1 = n + 2 by omega]
        rw [PowerSeries.coeff_X_pow_mul (p := motzkinSeriesℂ ^ 2) (n := 2) (d := n)]
        rw [pow_two, PowerSeries.coeff_mul]
        rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ
          (fun x y => PowerSeries.coeff (R := ℂ) x motzkinSeriesℂ *
            PowerSeries.coeff (R := ℂ) y motzkinSeriesℂ) n]
        rw [Finset.sum_fin_eq_sum_range]
        apply Finset.sum_congr rfl
        intro x hx
        have hxle : x ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hx)
        simp [hxle]

/-- The Motzkin OGF satisfies `M = 1 + X M + X^2 M^2`. -/
theorem motzkinSeriesℂ_eq_one_add_X_mul_add_X_sq_mul_sq :
    motzkinSeriesℂ =
      1 + PowerSeries.X * motzkinSeriesℂ +
        (PowerSeries.X : PowerSeries ℂ) ^ 2 * motzkinSeriesℂ ^ 2 := by
  ext n
  cases n with
  | zero =>
      simp
  | succ n =>
      simp only [coeff_motzkinSeriesℂ, map_add, PowerSeries.coeff_one, Nat.succ_ne_zero,
        ↓reduceIte, zero_add]
      rw [coeff_X_mul_motzkinSeriesℂ, coeff_X_sq_mul_motzkinSeriesℂ_sq]
      norm_num [motzkin_succ]

@[simp] lemma coeff_motzkinRescaledSeriesℂ (n : ℕ) :
    PowerSeries.coeff (R := ℂ) n motzkinRescaledSeriesℂ =
      (motzkin n : ℂ) * ((3 : ℂ)⁻¹) ^ n := by
  simp [motzkinRescaledSeriesℂ, PowerSeries.coeff_rescale, mul_comm]

lemma motzkinRescaledSeriesℂ_quadratic :
    motzkinRescaledSeriesℂ =
      1 + motzkinScaleX * motzkinRescaledSeriesℂ +
        (motzkinScaleX * motzkinRescaledSeriesℂ) ^ 2 := by
  set_option backward.isDefEq.respectTransparency false in
    change PowerSeries.rescale ((3 : ℂ)⁻¹) motzkinSeriesℂ =
      1 + motzkinScaleX * motzkinRescaledSeriesℂ +
        (motzkinScaleX * motzkinRescaledSeriesℂ) ^ 2
    rw [motzkinSeriesℂ_eq_one_add_X_mul_add_X_sq_mul_sq]
    simp only [map_add, map_mul, map_one, map_pow, PowerSeries.rescale_X]
    simp [motzkinRescaledSeriesℂ, motzkinScaleX, pow_two, mul_assoc]
    ring

lemma Complex_cpow_half_sq (z : ℂ) : (z ^ (1 / 2 : ℂ)) ^ 2 = z := by
  rw [show (1 / 2 : ℂ) = (2⁻¹ : ℂ) by norm_num]
  exact Complex.cpow_nat_inv_pow z (n := 2) (by norm_num)

lemma motzkinSqrtOneSub_sq (z : ℂ) : motzkinSqrtOneSub z ^ 2 = 1 - z := by
  rw [motzkinSqrtOneSub, Complex_cpow_half_sq]

lemma motzkinRescaledDenominator_ne_zero (z : ℂ) :
    motzkinRescaledDenominator z ≠ 0 := by
  set_option backward.isDefEq.respectTransparency false in
    intro h
    have hmul :
        (1 + z / 3) ^ (1 / 2 : ℂ) * (1 - z) ^ (1 / 2 : ℂ) = z / 3 - 1 := by
      have h' := h
      unfold motzkinRescaledDenominator motzkinSqrtPlus motzkinSqrtOneSub at h'
      linear_combination h'
    have hsq := congrArg (fun w : ℂ => w ^ 2) hmul
    change (((1 + z / 3) ^ (1 / 2 : ℂ) * (1 - z) ^ (1 / 2 : ℂ)) ^ 2 =
      (z / 3 - 1) ^ 2) at hsq
    rw [mul_pow, Complex_cpow_half_sq, Complex_cpow_half_sq] at hsq
    have hz2 : z ^ 2 = 0 := by
      linear_combination (-9 / 4 : ℂ) * hsq
    have hz : z = 0 := eq_zero_of_pow_eq_zero hz2
    subst z
    norm_num [motzkinRescaledDenominator, motzkinSqrtPlus, motzkinSqrtOneSub] at h

lemma motzkinRescaledFun_quadratic (z : ℂ) :
    motzkinRescaledFun z =
      1 + (z / 3) * motzkinRescaledFun z +
        ((z / 3) * motzkinRescaledFun z) ^ 2 := by
  set_option backward.isDefEq.respectTransparency false in
    unfold motzkinRescaledFun
    field_simp [motzkinRescaledDenominator_ne_zero z]
    unfold motzkinRescaledDenominator motzkinSqrtPlus motzkinSqrtOneSub
    ring_nf
    rw [Complex_cpow_half_sq, Complex_cpow_half_sq]
    ring_nf

lemma one_add_div_three_mem_slitPlane_of_norm_lt_three {z : ℂ} (hz : ‖z‖ < 3) :
    1 + z / 3 ∈ Complex.slitPlane := by
  refine Or.inl ?_
  have hdiv : ‖z / 3‖ < 1 := by
    rw [norm_div]
    norm_num at hz ⊢
    linarith
  have hge : -(‖z / 3‖) ≤ (z / 3).re := by
    exact (abs_le.mp (Complex.abs_re_le_norm (z / 3))).1
  have hre : -1 < (z / 3).re := by linarith
  change 0 < (1 + z / 3).re
  rw [Complex.add_re, Complex.one_re]
  linarith

lemma analyticOnNhd_motzkin_sqrt_plus :
    AnalyticOnNhd ℂ motzkinSqrtPlus
      (DeltaDomainArg (3 / 2) (Real.pi / 4)) := by
  have hbase : AnalyticOnNhd ℂ (fun z : ℂ => 1 + z / 3)
      (DeltaDomainArg (3 / 2) (Real.pi / 4)) := by
    exact analyticOnNhd_const.add analyticOnNhd_id.div_const
  convert hbase.cpow analyticOnNhd_const (fun z hz => by
    apply one_add_div_three_mem_slitPlane_of_norm_lt_three
    have hzR : ‖z‖ < (3 / 2 : ℝ) := hz.1
    nlinarith) using 1

lemma analyticOnNhd_motzkin_sqrt_one_sub :
    AnalyticOnNhd ℂ motzkinSqrtOneSub
      (DeltaDomainArg (3 / 2) (Real.pi / 4)) := by
  have h := analyticOnNhd_one_sub_cpow_deltaDomain (α := (-1 / 2 : ℂ))
    (R := (3 / 2 : ℝ)) (φ := Real.pi / 4) (by positivity) (by nlinarith [Real.pi_pos])
  convert h using 1
  ext z
  norm_num [motzkinSqrtOneSub]

lemma analyticOnNhd_motzkinRescaledDenominator :
    AnalyticOnNhd ℂ motzkinRescaledDenominator
      (DeltaDomainArg (3 / 2) (Real.pi / 4)) := by
  have hlinear : AnalyticOnNhd ℂ (fun z : ℂ => 1 - z / 3)
      (DeltaDomainArg (3 / 2) (Real.pi / 4)) := by
    exact analyticOnNhd_const.sub analyticOnNhd_id.div_const
  convert hlinear.add
    (analyticOnNhd_motzkin_sqrt_plus.mul analyticOnNhd_motzkin_sqrt_one_sub) using 1

lemma analyticOnNhd_motzkinRescaledFun :
    AnalyticOnNhd ℂ motzkinRescaledFun
      (DeltaDomainArg (3 / 2) (Real.pi / 4)) := by
  simpa [motzkinRescaledFun] using
    (analyticOnNhd_const.div analyticOnNhd_motzkinRescaledDenominator
      (fun z _hz => motzkinRescaledDenominator_ne_zero z))

lemma Real_sqrt_four_thirds :
    Real.sqrt (4 / 3 : ℝ) = 2 / Real.sqrt 3 := by
  rw [Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 4) (3 : ℝ)]
  norm_num [Real.sqrt_eq_rpow]

lemma Complex_cpow_four_thirds_half :
    (((4 / 3 : ℝ) : ℂ) ^ (1 / 2 : ℂ)) = ((2 / Real.sqrt 3 : ℝ) : ℂ) := by
  convert (show (((4 / 3 : ℝ) : ℂ) ^ ((1 / 2 : ℝ) : ℂ)) =
      ((2 / Real.sqrt 3 : ℝ) : ℂ) by
    rw [← Complex.ofReal_cpow (by norm_num : (0 : ℝ) ≤ 4 / 3) (1 / 2 : ℝ)]
    congr
    rw [← Real.sqrt_eq_rpow]
    exact Real_sqrt_four_thirds) using 2
  norm_num

lemma toFMLS_powerSeriesOfFMLSℂ (p : FormalMultilinearSeries ℂ ℂ ℂ) :
    PowerSeries.toFMLS (powerSeriesOfFMLSℂ p) = p := by
  ext n
  rw [← FormalMultilinearSeries.mkPiRing_coeff_eq
      (PowerSeries.toFMLS (powerSeriesOfFMLSℂ p)) n,
    ← FormalMultilinearSeries.mkPiRing_coeff_eq p n]
  simp [powerSeriesOfFMLSℂ]

lemma PowerSeries_toFMLS_injective :
    Function.Injective (PowerSeries.toFMLS :
      PowerSeries ℂ → FormalMultilinearSeries ℂ ℂ ℂ) := by
  intro f g h
  ext n
  have hcoeff := congrArg (fun p : FormalMultilinearSeries ℂ ℂ ℂ => p.coeff n) h
  simpa using hcoeff

lemma toFMLS_add (f g : PowerSeries ℂ) :
    PowerSeries.toFMLS (f + g) = PowerSeries.toFMLS f + PowerSeries.toFMLS g := by
  ext n
  simp [PowerSeries.toFMLS, FormalMultilinearSeries.ofScalars]

lemma toFMLS_sub (f g : PowerSeries ℂ) :
    PowerSeries.toFMLS (f - g) = PowerSeries.toFMLS f - PowerSeries.toFMLS g := by
  ext n
  simp [PowerSeries.toFMLS, FormalMultilinearSeries.ofScalars]

lemma toFMLS_C (c : ℂ) :
    PowerSeries.toFMLS (PowerSeries.C c) =
      constFormalMultilinearSeries ℂ ℂ c := by
  ext n
  cases n <;>
    simp [PowerSeries.toFMLS, FormalMultilinearSeries.ofScalars,
      constFormalMultilinearSeries]

lemma hasFPowerSeriesAt_const_toFMLS_C (c : ℂ) :
    HasFPowerSeriesAt (fun _ : ℂ => c)
      (PowerSeries.toFMLS (PowerSeries.C c)) (0 : ℂ) := by
  simpa [toFMLS_C] using
    (hasFPowerSeriesAt_const (𝕜 := ℂ) (E := ℂ) (F := ℂ)
      (c := c) (e := (0 : ℂ)))

lemma hasFPowerSeriesAt_id_toFMLS_X :
    HasFPowerSeriesAt (fun z : ℂ => z)
      (PowerSeries.toFMLS (PowerSeries.X : PowerSeries ℂ)) (0 : ℂ) := by
  rw [hasFPowerSeriesAt_iff]
  filter_upwards with z
  let term : ℕ → ℂ :=
    fun n => z ^ n • (PowerSeries.toFMLS (PowerSeries.X : PowerSeries ℂ)).coeff n
  have hsingle : HasSum term (term 1) := by
    apply hasSum_single
    intro n hn
    simp [term, PowerSeries.coeff_X, hn]
  convert hsingle using 1
  simp [term, PowerSeries.toFMLS]

lemma hasFPowerSeriesAt_mul_toFMLS {f g : ℂ → ℂ} {F G : PowerSeries ℂ}
    (hf : HasFPowerSeriesAt f (PowerSeries.toFMLS F) (0 : ℂ))
    (hg : HasFPowerSeriesAt g (PowerSeries.toFMLS G) (0 : ℂ)) :
    HasFPowerSeriesAt (fun z : ℂ => f z * g z)
      (PowerSeries.toFMLS (F * G)) (0 : ℂ) := by
  rcases hf with ⟨rf, hrf⟩
  rcases hg with ⟨rg, hrg⟩
  rw [hasFPowerSeriesAt_iff]
  refine eventually_of_mem
    (Metric.eball_mem_nhds (0 : ℂ) (lt_min hrf.r_pos hrg.r_pos)) ?_
  intro z hz
  have hzf : z ∈ Metric.eball (0 : ℂ) rf := by
    exact Metric.mem_eball.mpr
      (lt_of_lt_of_le (Metric.mem_eball.mp hz) (min_le_left _ _))
  have hzg : z ∈ Metric.eball (0 : ℂ) rg := by
    exact Metric.mem_eball.mpr
      (lt_of_lt_of_le (Metric.mem_eball.mp hz) (min_le_right _ _))
  let a : ℕ → ℂ := fun n => z ^ n * PowerSeries.coeff (R := ℂ) n F
  let b : ℕ → ℂ := fun n => z ^ n * PowerSeries.coeff (R := ℂ) n G
  have hsumf : HasSum a (f z) := by
    have h := hrf.hasSum hzf
    simpa [a, PowerSeries.toFMLS, FormalMultilinearSeries.ofScalars, smul_eq_mul,
      mul_comm, mul_left_comm, mul_assoc] using h
  have hsumg : HasSum b (g z) := by
    have h := hrg.hasSum hzg
    simpa [b, PowerSeries.toFMLS, FormalMultilinearSeries.ofScalars, smul_eq_mul,
      mul_comm, mul_left_comm, mul_assoc] using h
  have hzfrad : z ∈ Metric.eball (0 : ℂ) (PowerSeries.toFMLS F).radius :=
    Metric.eball_subset_eball hrf.r_le hzf
  have hzgrad : z ∈ Metric.eball (0 : ℂ) (PowerSeries.toFMLS G).radius :=
    Metric.eball_subset_eball hrg.r_le hzg
  have hnormf : Summable fun n : ℕ => ‖a n‖ := by
    simpa [a, PowerSeries.toFMLS, FormalMultilinearSeries.ofScalars, smul_eq_mul,
      mul_comm, mul_left_comm, mul_assoc] using
      (PowerSeries.toFMLS F).summable_norm_apply hzfrad
  have hnormg : Summable fun n : ℕ => ‖b n‖ := by
    simpa [b, PowerSeries.toFMLS, FormalMultilinearSeries.ofScalars, smul_eq_mul,
      mul_comm, mul_left_comm, mul_assoc] using
      (PowerSeries.toFMLS G).summable_norm_apply hzgrad
  let cseq : ℕ → ℂ := fun n => z ^ n * PowerSeries.coeff (R := ℂ) n (F * G)
  let d : ℕ → ℂ := fun n => ∑ kl ∈ Finset.antidiagonal n, a kl.1 * b kl.2
  have hcd : ∀ n, cseq n = d n := by
    intro n
    change z ^ n * PowerSeries.coeff (R := ℂ) n (F * G) =
      ∑ kl ∈ Finset.antidiagonal n, a kl.1 * b kl.2
    rw [PowerSeries.coeff_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro kl hkl
    have hsum : kl.1 + kl.2 = n := Finset.mem_antidiagonal.mp hkl
    simp [a, b]
    rw [← hsum, pow_add]
    ring
  have hnormd : Summable fun n : ℕ => ‖d n‖ := by
    simpa [d] using summable_norm_sum_mul_antidiagonal_of_summable_norm hnormf hnormg
  have hnormc : Summable fun n : ℕ => ‖cseq n‖ := by
    exact hnormd.congr (fun n => by rw [hcd n])
  have hsumc : Summable cseq := hnormc.of_norm
  have htsum : (∑' n : ℕ, cseq n) = f z * g z := by
    have hprod := tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hnormf hnormg
    rw [hsumf.tsum_eq, hsumg.tsum_eq] at hprod
    rw [tsum_congr hcd, ← hprod]
  have hmain : HasSum cseq (f z * g z) := hsumc.hasSum_iff.mpr htsum
  simpa [cseq, PowerSeries.toFMLS, FormalMultilinearSeries.ofScalars, smul_eq_mul,
    mul_comm, mul_left_comm, mul_assoc] using hmain

lemma coeff_motzkinScaleX_mul_zero (P : PowerSeries ℂ) :
    PowerSeries.coeff (R := ℂ) 0 (motzkinScaleX * P) = 0 := by
  simp [motzkinScaleX]

lemma coeff_motzkinScaleX_mul_succ (P : PowerSeries ℂ) (n : ℕ) :
    PowerSeries.coeff (R := ℂ) (n + 1) (motzkinScaleX * P) =
      (3 : ℂ)⁻¹ * PowerSeries.coeff (R := ℂ) n P := by
  set_option backward.isDefEq.respectTransparency false in
    rw [motzkinScaleX, mul_assoc, PowerSeries.coeff_C_mul]
    simp

lemma coeff_motzkinScaleX_mul_sq_succ_congr {P Q : PowerSeries ℂ} {n : ℕ}
    (h : ∀ k < n, PowerSeries.coeff (R := ℂ) k P =
      PowerSeries.coeff (R := ℂ) k Q) :
    PowerSeries.coeff (R := ℂ) (n + 1) ((motzkinScaleX * P) ^ 2) =
      PowerSeries.coeff (R := ℂ) (n + 1) ((motzkinScaleX * Q) ^ 2) := by
  set_option backward.isDefEq.respectTransparency false in
    rw [pow_two, pow_two, PowerSeries.coeff_mul, PowerSeries.coeff_mul]
    apply Finset.sum_congr rfl
    intro kl hkl
    have hsum : kl.1 + kl.2 = n + 1 := Finset.mem_antidiagonal.mp hkl
    by_cases h1 : kl.1 = 0
    · simp [h1, coeff_motzkinScaleX_mul_zero]
    by_cases h2 : kl.2 = 0
    · simp [h2, coeff_motzkinScaleX_mul_zero]
    obtain ⟨i, hi_eq⟩ := Nat.exists_eq_succ_of_ne_zero h1
    obtain ⟨j, hj_eq⟩ := Nat.exists_eq_succ_of_ne_zero h2
    cases kl with
    | mk k l =>
        simp only at hi_eq hj_eq hsum ⊢
        subst k
        subst l
        have hi : i < n := by omega
        have hj : j < n := by omega
        simp [coeff_motzkinScaleX_mul_succ, h i hi, h j hj]

lemma motzkin_quadratic_solution_unique {P Q : PowerSeries ℂ}
    (hP : P = 1 + motzkinScaleX * P + (motzkinScaleX * P) ^ 2)
    (hQ : Q = 1 + motzkinScaleX * Q + (motzkinScaleX * Q) ^ 2) :
    P = Q := by
  ext n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      cases n with
      | zero =>
          have hp := congrArg (fun S : PowerSeries ℂ =>
            PowerSeries.coeff (R := ℂ) 0 S) hP
          have hq := congrArg (fun S : PowerSeries ℂ =>
            PowerSeries.coeff (R := ℂ) 0 S) hQ
          simp [motzkinScaleX] at hp hq
          simp [PowerSeries.coeff_zero_eq_constantCoeff_apply, hp, hq]
      | succ n =>
          have hp := congrArg (fun S : PowerSeries ℂ =>
            PowerSeries.coeff (R := ℂ) (n + 1) S) hP
          have hq := congrArg (fun S : PowerSeries ℂ =>
            PowerSeries.coeff (R := ℂ) (n + 1) S) hQ
          simp only [map_add] at hp hq
          rw [hp, hq]
          congr 1
          · rw [coeff_motzkinScaleX_mul_succ, coeff_motzkinScaleX_mul_succ,
              ih n (Nat.lt_succ_self n)]
          · exact coeff_motzkinScaleX_mul_sq_succ_congr
              (fun k hk => ih k (Nat.lt_trans hk (Nat.lt_succ_self n)))

theorem motzkinRescaledFun_hasFPowerSeriesAt_zero :
    HasFPowerSeriesAt motzkinRescaledFun
      (PowerSeries.toFMLS motzkinRescaledSeriesℂ) (0 : ℂ) := by
  have han : AnalyticAt ℂ motzkinRescaledFun (0 : ℂ) :=
    analyticOnNhd_motzkinRescaledFun 0
      (zero_mem_deltaDomainArg (R := (3 / 2 : ℝ)) (φ := Real.pi / 4)
        (by norm_num) (by nlinarith [Real.pi_pos]))
  rcases han with ⟨p, hp⟩
  let P : PowerSeries ℂ := powerSeriesOfFMLSℂ p
  have hPto : PowerSeries.toFMLS P = p := by
    simpa [P] using toFMLS_powerSeriesOfFMLSℂ p
  have hpP : HasFPowerSeriesAt motzkinRescaledFun
      (PowerSeries.toFMLS P) (0 : ℂ) := by
    simpa [hPto] using hp
  have hconstScale : HasFPowerSeriesAt (fun _ : ℂ => ((3 : ℂ)⁻¹))
      (PowerSeries.toFMLS (PowerSeries.C ((3 : ℂ)⁻¹))) (0 : ℂ) :=
    hasFPowerSeriesAt_const_toFMLS_C ((3 : ℂ)⁻¹)
  have hscale0 := hasFPowerSeriesAt_mul_toFMLS hconstScale
    hasFPowerSeriesAt_id_toFMLS_X
  have hscale : HasFPowerSeriesAt (fun z : ℂ => z / 3)
      (PowerSeries.toFMLS motzkinScaleX) (0 : ℂ) := by
    refine hscale0.congr (Eventually.of_forall ?_)
    intro z
    ring
  have hscaleF := hasFPowerSeriesAt_mul_toFMLS hscale hpP
  have hsquare := hasFPowerSeriesAt_mul_toFMLS hscaleF hscaleF
  have hconstOne : HasFPowerSeriesAt (fun _ : ℂ => (1 : ℂ))
      (PowerSeries.toFMLS (1 : PowerSeries ℂ)) (0 : ℂ) := by
    simpa using hasFPowerSeriesAt_const_toFMLS_C (1 : ℂ)
  have hrhs0 := (hconstOne.add hscaleF).add hsquare
  have hrhs : HasFPowerSeriesAt
      (fun z : ℂ =>
        1 + (z / 3) * motzkinRescaledFun z +
          ((z / 3) * motzkinRescaledFun z) ^ 2)
      (PowerSeries.toFMLS
        (1 + motzkinScaleX * P + (motzkinScaleX * P) ^ 2)) (0 : ℂ) := by
    simpa [toFMLS_add, pow_two, add_assoc] using hrhs0
  have hFMLS :
      PowerSeries.toFMLS P =
        PowerSeries.toFMLS
          (1 + motzkinScaleX * P + (motzkinScaleX * P) ^ 2) :=
    hpP.eq_formalMultilinearSeries_of_eventually hrhs
      (Eventually.of_forall fun z => motzkinRescaledFun_quadratic z)
  have hPquad :
      P = 1 + motzkinScaleX * P + (motzkinScaleX * P) ^ 2 :=
    PowerSeries_toFMLS_injective hFMLS
  have hP_eq : P = motzkinRescaledSeriesℂ :=
    motzkin_quadratic_solution_unique hPquad motzkinRescaledSeriesℂ_quadratic
  simpa [hP_eq] using hpP

end
end

section
/-!
# Riordan-number asymptotic

This file proves the square-root singularity asymptotic for the Riordan
numbers, using the first-return decomposition of Riordan paths:

`R(z) = 1 + z^2 M(z) R(z)`.

The explicit branch is

`R(z) = 2 / (1 + z + sqrt(1 - 2 z - 3 z^2))`.
-/

open Complex Filter Asymptotics
open scoped BigOperators PowerSeries Topology

noncomputable section

@[simp] lemma riordan_zero : riordan 0 = 1 := by
  simp [riordan]

@[simp] lemma riordan_one : riordan 1 = 0 := by
  simp [riordan]

@[simp] lemma riordan_succ_succ (n : ℕ) :
    riordan (n + 2) = ∑ k : Fin (n + 1), motzkin k * riordan (n - k) := by
  simp [riordan]

/-- The ordinary generating function as a formal power series over `ℂ`. -/
def riordanSeriesℂ : PowerSeries ℂ :=
  PowerSeries.mk fun n => (riordan n : ℂ)

@[simp] lemma coeff_riordanSeriesℂ (n : ℕ) :
    PowerSeries.coeff (R := ℂ) n riordanSeriesℂ = (riordan n : ℂ) := by
  simp [riordanSeriesℂ]

@[simp] lemma constantCoeff_riordanSeriesℂ :
    PowerSeries.constantCoeff riordanSeriesℂ = 1 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
  simp

lemma coeff_motzkinSeriesℂ_mul_riordanSeriesℂ (n : ℕ) :
    PowerSeries.coeff (R := ℂ) n (motzkinSeriesℂ * riordanSeriesℂ) =
      ∑ k : Fin (n + 1), (motzkin k : ℂ) * (riordan (n - k) : ℂ) := by
  rw [PowerSeries.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun x y => PowerSeries.coeff (R := ℂ) x motzkinSeriesℂ *
      PowerSeries.coeff (R := ℂ) y riordanSeriesℂ) n]
  rw [Finset.sum_fin_eq_sum_range]
  apply Finset.sum_congr rfl
  intro x hx
  have hxle : x ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hx)
  simp [hxle]

lemma coeff_X_sq_mul_motzkinSeriesℂ_mul_riordanSeriesℂ (n : ℕ) :
    PowerSeries.coeff (R := ℂ) (n + 2)
        ((PowerSeries.X : PowerSeries ℂ) ^ 2 *
          (motzkinSeriesℂ * riordanSeriesℂ)) =
      ∑ k : Fin (n + 1), (motzkin k : ℂ) * (riordan (n - k) : ℂ) := by
  rw [PowerSeries.coeff_X_pow_mul (p := motzkinSeriesℂ * riordanSeriesℂ)
    (n := 2) (d := n)]
  exact coeff_motzkinSeriesℂ_mul_riordanSeriesℂ n

/-- The Riordan OGF satisfies the first-return equation `R = 1 + X^2 M R`. -/
theorem riordanSeriesℂ_eq_one_add_X_sq_mul_motzkin_mul :
    riordanSeriesℂ =
      1 + (PowerSeries.X : PowerSeries ℂ) ^ 2 *
        (motzkinSeriesℂ * riordanSeriesℂ) := by
  ext n
  cases n with
  | zero =>
      simp
  | succ n =>
      cases n with
      | zero =>
          simp [PowerSeries.coeff_X_pow_mul']
      | succ n =>
          simp only [coeff_riordanSeriesℂ, map_add, PowerSeries.coeff_one,
            Nat.succ_ne_zero, ↓reduceIte, zero_add]
          rw [coeff_X_sq_mul_motzkinSeriesℂ_mul_riordanSeriesℂ]
          norm_num [riordan_succ_succ]

/-- The rescaled series `R(z / 3)`. -/
def riordanRescaledSeriesℂ : PowerSeries ℂ :=
  PowerSeries.rescale ((3 : ℂ)⁻¹) riordanSeriesℂ

@[simp] lemma coeff_riordanRescaledSeriesℂ (n : ℕ) :
    PowerSeries.coeff (R := ℂ) n riordanRescaledSeriesℂ =
      (riordan n : ℂ) * ((3 : ℂ)⁻¹) ^ n := by
  simp [riordanRescaledSeriesℂ, PowerSeries.coeff_rescale, mul_comm]

/-- The formal substitution variable `z / 3`. -/
def riordanScaleX : PowerSeries ℂ :=
  PowerSeries.C ((3 : ℂ)⁻¹) * PowerSeries.X

lemma riordanRescaledSeriesℂ_functional :
    riordanRescaledSeriesℂ =
      1 + riordanScaleX ^ 2 *
        (motzkinRescaledSeriesℂ * riordanRescaledSeriesℂ) := by
  change PowerSeries.rescale ((3 : ℂ)⁻¹) riordanSeriesℂ =
    1 + riordanScaleX ^ 2 *
      (motzkinRescaledSeriesℂ * riordanRescaledSeriesℂ)
  rw [riordanSeriesℂ_eq_one_add_X_sq_mul_motzkin_mul]
  simp only [map_add, map_mul, map_one, map_pow, PowerSeries.rescale_X]
  simp [riordanRescaledSeriesℂ, motzkinRescaledSeriesℂ, riordanScaleX, pow_two, mul_assoc]

def riordanSqrtPlus (z : ℂ) : ℂ :=
  motzkinSqrtPlus z

def riordanSqrtOneSub (z : ℂ) : ℂ :=
  motzkinSqrtOneSub z

def riordanSqrtPlusAtOneℂ : ℂ :=
  ((2 / Real.sqrt 3 : ℝ) : ℂ)

/-- The singular coefficient of `R(z / 3)` at `z = 1`. -/
def riordanSingularCoeff : ℂ :=
  -(((3 * Real.sqrt 3 / 4 : ℝ) : ℂ))

/-- Denominator of the explicit rescaled Riordan OGF. -/
def riordanRescaledDenominator (z : ℂ) : ℂ :=
  1 + z / 3 + riordanSqrtPlus z * riordanSqrtOneSub z

/-- The explicit analytic branch of `R(z / 3)`. -/
def riordanRescaledFun (z : ℂ) : ℂ :=
  2 / riordanRescaledDenominator z

def riordanRegularValueℂ : ℂ := 3 / 2

lemma riordanSqrtOneSub_sq (z : ℂ) : riordanSqrtOneSub z ^ 2 = 1 - z := by
  simpa [riordanSqrtOneSub] using motzkinSqrtOneSub_sq z

lemma riordanSqrtPlus_sq (z : ℂ) : riordanSqrtPlus z ^ 2 = 1 + z / 3 := by
  simp [riordanSqrtPlus, motzkinSqrtPlus]

section
end

set_option backward.isDefEq.respectTransparency false in
lemma riordanRescaledDenominator_ne_zero_of_norm_lt_three {z : ℂ}
    (hz : ‖z‖ < 3) :
    riordanRescaledDenominator z ≠ 0 := by
  intro h
  have hmul :
      riordanSqrtPlus z * riordanSqrtOneSub z = -(1 + z / 3) := by
    have h' := h
    unfold riordanRescaledDenominator at h'
    linear_combination h'
  have hsq := congrArg (fun w : ℂ => w ^ 2) hmul
  change (riordanSqrtPlus z * riordanSqrtOneSub z) ^ 2 =
    (-(1 + z / 3)) ^ 2 at hsq
  rw [mul_pow, riordanSqrtPlus_sq, riordanSqrtOneSub_sq] at hsq
  have hzprod : z * (1 + z / 3) = 0 := by
    linear_combination (-3 / 4 : ℂ) * hsq
  rcases mul_eq_zero.mp hzprod with hz0 | hfactor
  · subst z
    norm_num [riordanRescaledDenominator, riordanSqrtPlus, riordanSqrtOneSub,
      motzkinSqrtPlus, motzkinSqrtOneSub] at h
  · have hz_eq : z = -3 := by
      linear_combination 3 * hfactor
    have hnorm : ‖z‖ = 3 := by
      rw [hz_eq]
      norm_num
    nlinarith

lemma riordanRescaledDenominator_ne_zero_delta
    {z : ℂ} (hz : z ∈ DeltaDomainArg (3 / 2) (Real.pi / 4)) :
    riordanRescaledDenominator z ≠ 0 := by
  exact riordanRescaledDenominator_ne_zero_of_norm_lt_three (by nlinarith [hz.1])

section
end

set_option backward.isDefEq.respectTransparency false in
lemma riordanRescaledFun_functional_of_norm_lt_three {z : ℂ} (hz : ‖z‖ < 3) :
    riordanRescaledFun z =
      1 + (z / 3) ^ 2 * motzkinRescaledFun z * riordanRescaledFun z := by
  unfold riordanRescaledFun motzkinRescaledFun
  field_simp [riordanRescaledDenominator_ne_zero_of_norm_lt_three hz,
    motzkinRescaledDenominator_ne_zero z]
  unfold riordanRescaledDenominator motzkinRescaledDenominator riordanSqrtPlus
    riordanSqrtOneSub motzkinSqrtPlus motzkinSqrtOneSub
  ring_nf
  rw [Complex_cpow_half_sq, Complex_cpow_half_sq]
  ring_nf

lemma analyticOnNhd_riordan_sqrt_plus :
    AnalyticOnNhd ℂ riordanSqrtPlus
      (DeltaDomainArg (3 / 2) (Real.pi / 4)) := by
  simpa [riordanSqrtPlus] using analyticOnNhd_motzkin_sqrt_plus

lemma analyticOnNhd_riordan_sqrt_one_sub :
    AnalyticOnNhd ℂ riordanSqrtOneSub
      (DeltaDomainArg (3 / 2) (Real.pi / 4)) := by
  simpa [riordanSqrtOneSub] using analyticOnNhd_motzkin_sqrt_one_sub

lemma analyticOnNhd_riordanRescaledDenominator :
    AnalyticOnNhd ℂ riordanRescaledDenominator
      (DeltaDomainArg (3 / 2) (Real.pi / 4)) := by
  have hlinear : AnalyticOnNhd ℂ (fun z : ℂ => 1 + z / 3)
      (DeltaDomainArg (3 / 2) (Real.pi / 4)) := by
    exact analyticOnNhd_const.add analyticOnNhd_id.div_const
  convert hlinear.add
    (analyticOnNhd_riordan_sqrt_plus.mul analyticOnNhd_riordan_sqrt_one_sub) using 1

lemma analyticOnNhd_riordanRescaledFun :
    AnalyticOnNhd ℂ riordanRescaledFun
      (DeltaDomainArg (3 / 2) (Real.pi / 4)) := by
  simpa [riordanRescaledFun] using
    (analyticOnNhd_const.div analyticOnNhd_riordanRescaledDenominator
      (fun z hz => riordanRescaledDenominator_ne_zero_delta hz))

lemma coeff_riordanScaleX_mul_zero (P : PowerSeries ℂ) :
    PowerSeries.coeff (R := ℂ) 0 (riordanScaleX * P) = 0 := by
  simp [riordanScaleX]

section
end

set_option backward.isDefEq.respectTransparency false in
lemma coeff_riordanScaleX_mul_succ (P : PowerSeries ℂ) (n : ℕ) :
    PowerSeries.coeff (R := ℂ) (n + 1) (riordanScaleX * P) =
      (3 : ℂ)⁻¹ * PowerSeries.coeff (R := ℂ) n P := by
  rw [riordanScaleX, mul_assoc, PowerSeries.coeff_C_mul]
  simp

section
end

set_option backward.isDefEq.respectTransparency false in
lemma coeff_riordanScaleX_sq_mul_succ_succ (P : PowerSeries ℂ) (n : ℕ) :
    PowerSeries.coeff (R := ℂ) (n + 2) (riordanScaleX ^ 2 * P) =
      ((3 : ℂ)⁻¹) ^ 2 * PowerSeries.coeff (R := ℂ) n P := by
  rw [pow_two, mul_assoc, coeff_riordanScaleX_mul_succ, coeff_riordanScaleX_mul_succ]
  ring

section
end

set_option backward.isDefEq.respectTransparency false in
lemma coeff_riordanScaleX_sq_mul_of_lt_two (P : PowerSeries ℂ) {n : ℕ} (hn : n < 2) :
    PowerSeries.coeff (R := ℂ) n (riordanScaleX ^ 2 * P) = 0 := by
  cases n with
  | zero =>
      simp [riordanScaleX]
  | succ n =>
      cases n with
      | zero =>
          rw [pow_two, mul_assoc, coeff_riordanScaleX_mul_succ,
            coeff_riordanScaleX_mul_zero]
          ring
      | succ n =>
          omega

lemma riordan_linear_solution_unique {P Q : PowerSeries ℂ}
    (hP : P = 1 + riordanScaleX ^ 2 * (motzkinRescaledSeriesℂ * P))
    (hQ : Q = 1 + riordanScaleX ^ 2 * (motzkinRescaledSeriesℂ * Q)) :
    P = Q := by
  ext n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      cases n with
      | zero =>
          have hp := congrArg (fun S : PowerSeries ℂ =>
            PowerSeries.coeff (R := ℂ) 0 S) hP
          have hq := congrArg (fun S : PowerSeries ℂ =>
            PowerSeries.coeff (R := ℂ) 0 S) hQ
          simp [riordanScaleX] at hp hq
          simp [PowerSeries.coeff_zero_eq_constantCoeff_apply, hp, hq]
      | succ n =>
          cases n with
          | zero =>
              have hp := congrArg (fun S : PowerSeries ℂ =>
                PowerSeries.coeff (R := ℂ) 1 S) hP
              have hq := congrArg (fun S : PowerSeries ℂ =>
                PowerSeries.coeff (R := ℂ) 1 S) hQ
              simp only [map_add, PowerSeries.coeff_one, one_ne_zero, ↓reduceIte,
                zero_add] at hp hq
              rw [hp, hq]
              rw [coeff_riordanScaleX_sq_mul_of_lt_two _ (by norm_num : 1 < 2),
                coeff_riordanScaleX_sq_mul_of_lt_two _ (by norm_num : 1 < 2)]
          | succ n =>
              have hp := congrArg (fun S : PowerSeries ℂ =>
                PowerSeries.coeff (R := ℂ) (n + 2) S) hP
              have hq := congrArg (fun S : PowerSeries ℂ =>
                PowerSeries.coeff (R := ℂ) (n + 2) S) hQ
              simp only [map_add, PowerSeries.coeff_one, Nat.succ_ne_zero, ↓reduceIte,
                zero_add] at hp hq
              rw [hp, hq]
              rw [coeff_riordanScaleX_sq_mul_succ_succ,
                coeff_riordanScaleX_sq_mul_succ_succ]
              congr 1
              rw [PowerSeries.coeff_mul, PowerSeries.coeff_mul]
              apply Finset.sum_congr rfl
              intro kl hkl
              have hlt : kl.2 < n + 2 := by
                have hsum : kl.1 + kl.2 = n := Finset.mem_antidiagonal.mp hkl
                omega
              simp [ih kl.2 hlt]

theorem riordanRescaledFun_hasFPowerSeriesAt_zero :
    HasFPowerSeriesAt riordanRescaledFun
      (PowerSeries.toFMLS riordanRescaledSeriesℂ) (0 : ℂ) := by
  have han : AnalyticAt ℂ riordanRescaledFun (0 : ℂ) :=
    analyticOnNhd_riordanRescaledFun 0
      (zero_mem_deltaDomainArg (R := (3 / 2 : ℝ)) (φ := Real.pi / 4)
        (by norm_num) (by nlinarith [Real.pi_pos]))
  rcases han with ⟨p, hp⟩
  let P : PowerSeries ℂ := powerSeriesOfFMLSℂ p
  have hPto : PowerSeries.toFMLS P = p := by
    simpa [P] using toFMLS_powerSeriesOfFMLSℂ p
  have hpP : HasFPowerSeriesAt riordanRescaledFun
      (PowerSeries.toFMLS P) (0 : ℂ) := by
    simpa [hPto] using hp
  have hconstScale : HasFPowerSeriesAt (fun _ : ℂ => ((3 : ℂ)⁻¹))
      (PowerSeries.toFMLS (PowerSeries.C ((3 : ℂ)⁻¹))) (0 : ℂ) :=
    hasFPowerSeriesAt_const_toFMLS_C ((3 : ℂ)⁻¹)
  have hscale0 := hasFPowerSeriesAt_mul_toFMLS hconstScale
    hasFPowerSeriesAt_id_toFMLS_X
  have hscale : HasFPowerSeriesAt (fun z : ℂ => z / 3)
      (PowerSeries.toFMLS riordanScaleX) (0 : ℂ) := by
    refine hscale0.congr (Eventually.of_forall ?_)
    intro z
    ring
  have hscaleSq := hasFPowerSeriesAt_mul_toFMLS hscale hscale
  have hMF := hasFPowerSeriesAt_mul_toFMLS
    motzkinRescaledFun_hasFPowerSeriesAt_zero hpP
  have hterm := hasFPowerSeriesAt_mul_toFMLS hscaleSq hMF
  have hconstOne : HasFPowerSeriesAt (fun _ : ℂ => (1 : ℂ))
      (PowerSeries.toFMLS (1 : PowerSeries ℂ)) (0 : ℂ) := by
    simpa using hasFPowerSeriesAt_const_toFMLS_C (1 : ℂ)
  have hrhs0 := hconstOne.add hterm
  have hrhs : HasFPowerSeriesAt
      (fun z : ℂ =>
        1 + (z / 3) ^ 2 * motzkinRescaledFun z * riordanRescaledFun z)
      (PowerSeries.toFMLS
        (1 + riordanScaleX ^ 2 * (motzkinRescaledSeriesℂ * P))) (0 : ℂ) := by
    simpa [toFMLS_add, pow_two, mul_assoc] using hrhs0
  have hevent :
      (fun z : ℂ =>
        riordanRescaledFun z) =ᶠ[𝓝 (0 : ℂ)]
      (fun z : ℂ =>
        1 + (z / 3) ^ 2 * motzkinRescaledFun z * riordanRescaledFun z) := by
    refine eventually_of_mem
      (Metric.ball_mem_nhds (0 : ℂ) (by norm_num : (0 : ℝ) < 1)) ?_
    intro z hz
    have hnorm1 : ‖z‖ < 1 := by
      simpa [Metric.mem_ball, dist_eq_norm] using hz
    exact riordanRescaledFun_functional_of_norm_lt_three (by nlinarith)
  have hFMLS :
      PowerSeries.toFMLS P =
        PowerSeries.toFMLS
          (1 + riordanScaleX ^ 2 * (motzkinRescaledSeriesℂ * P)) :=
    hpP.eq_formalMultilinearSeries_of_eventually hrhs hevent
  have hPquad :
      P = 1 + riordanScaleX ^ 2 * (motzkinRescaledSeriesℂ * P) :=
    PowerSeries_toFMLS_injective hFMLS
  have hP_eq : P = riordanRescaledSeriesℂ :=
    riordan_linear_solution_unique hPquad riordanRescaledSeriesℂ_functional
  simpa [hP_eq] using hpP

end
end

section
/-!
# Second-order Riordan asymptotics

The centered rescaled Riordan function has an analytic linear term between the
two half-integer singular terms.  We subtract that linear term before applying
the general second-order transfer theorem; its coefficients vanish for `n ≥ 2`.
-/

set_option maxHeartbeats 1200000

open Complex Filter Asymptotics Set
open scoped Topology BigOperators PowerSeries

noncomputable section

def riordanAnalyticLinearCoeff : ℂ := (3 / 2 : ℂ)

def riordanSecondSingularCoeff : ℂ :=
  riordanSingularCoeff * (9 / 8 : ℂ)

def riordanSecondAsymptoticConstant : ℝ :=
  -(63 * Real.sqrt 3 / (128 * Real.sqrt Real.pi))

def riordanOneSubSeriesℂ : PowerSeries ℂ :=
  (1 : PowerSeries ℂ) - PowerSeries.X

lemma hasFPowerSeriesAt_riordanOneSub_toFMLS :
    HasFPowerSeriesAt (fun z : ℂ => 1 - z)
      (PowerSeries.toFMLS riordanOneSubSeriesℂ) (0 : ℂ) := by
  have hconst := hasFPowerSeriesAt_const_toFMLS_C (1 : ℂ)
  have hid := hasFPowerSeriesAt_id_toFMLS_X
  have hsub := hconst.sub hid
  simpa [riordanOneSubSeriesℂ, toFMLS_sub] using hsub

lemma riordanSqrtPlus_one :
    riordanSqrtPlus (1 : ℂ) = riordanSqrtPlusAtOneℂ := by
  unfold riordanSqrtPlus riordanSqrtPlusAtOneℂ motzkinSqrtPlus
  rw [show (1 : ℂ) + 1 / 3 = ((4 / 3 : ℝ) : ℂ) by norm_num]
  exact Complex_cpow_four_thirds_half

lemma hasDerivAt_riordanSqrtPlus_one :
    HasDerivAt riordanSqrtPlus (((Real.sqrt 3 / 12 : ℝ) : ℂ)) (1 : ℂ) := by
  have hid : HasDerivAt (fun z : ℂ => z) 1 (1 : ℂ) := by
    simpa using hasDerivAt_id (1 : ℂ)
  have hbase0 := (hasDerivAt_const (1 : ℂ) (1 : ℂ)).add (hid.div_const (3 : ℂ))
  have hbase : HasDerivAt (fun z : ℂ => 1 + z / 3) (1 / 3 : ℂ) (1 : ℂ) := by
    simpa only [Pi.add_apply, zero_add] using hbase0
  have hslit : (1 : ℂ) + 1 / 3 ∈ Complex.slitPlane := by
    convert Complex.ofReal_mem_slitPlane.2 (by norm_num : (0 : ℝ) < 4 / 3) using 1
    norm_num
  have hpow := hbase.cpow_const (c := (1 / 2 : ℂ)) hslit
  convert hpow using 1
  rw [show (1 : ℂ) + 1 / 3 = ((4 / 3 : ℝ) : ℂ) by norm_num]
  rw [show (1 / 2 : ℂ) - 1 = -(1 / 2 : ℂ) by norm_num]
  rw [Complex.cpow_neg, Complex_cpow_four_thirds_half]
  have hs3 : ((Real.sqrt 3 : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_ne_zero'.mpr (by norm_num : (0 : ℝ) < 3))
  norm_num [Complex.ofReal_div, Complex.ofReal_mul]
  field_simp [hs3]
  norm_num

lemma riordanSecondAsymptoticConstant_eq_relative :
    riordanSecondAsymptoticConstant =
      riordanAsymptoticConstant * riordanRelativeSecondConstant := by
  unfold riordanSecondAsymptoticConstant riordanAsymptoticConstant
    riordanRelativeSecondConstant
  ring

end
end

/-!
# Third-order Riordan asymptotics

This file plugs the Riordan square-root data at `ρ = 1 / 3` into the
third-order square-root applicator.
-/

set_option maxHeartbeats 1200000

open Complex Filter Asymptotics Set
open scoped Topology BigOperators PowerSeries

noncomputable section

def riordanRho : ℝ := 1 / 3

def riordanAnalyticQuadraticCoeff : ℂ := 3 / 2

def riordanSingularDerivAtRho : ℂ :=
  (((81 * Real.sqrt 3 / 32 : ℝ) : ℂ))

def riordanSingularSecondDerivAtRho : ℂ :=
  -(((3969 * Real.sqrt 3 / 256 : ℝ) : ℂ))

def riordanThirdSingularCoeff : ℂ :=
  -(((441 * Real.sqrt 3 / 512 : ℝ) : ℂ))

def riordanThirdAsymptoticConstant : ℝ :=
  2055 * Real.sqrt 3 / (4096 * Real.sqrt Real.pi)

def riordanOneSubThreeXSeriesℂ : PowerSeries ℂ :=
  (1 : PowerSeries ℂ) - PowerSeries.C (3 : ℂ) * PowerSeries.X

def riordanThirdOriginalSeriesℂ : PowerSeries ℂ :=
  riordanSeriesℂ -
    PowerSeries.C riordanAnalyticQuadraticCoeff * riordanOneSubThreeXSeriesℂ ^ 2

def riordanThirdAdjustedRescaledSeriesℂ : PowerSeries ℂ :=
  riordanRescaledSeriesℂ -
    PowerSeries.C riordanAnalyticQuadraticCoeff * riordanOneSubSeriesℂ ^ 2

def riordanOriginalFun (z : ℂ) : ℂ :=
  riordanRescaledFun (3 * z)

def riordanThirdOriginalFun (z : ℂ) : ℂ :=
  riordanOriginalFun z - riordanAnalyticQuadraticCoeff * (1 - 3 * z) ^ 2

def riordanThirdAdjustedRescaledFun (z : ℂ) : ℂ :=
  riordanRescaledFun z - riordanAnalyticQuadraticCoeff * (1 - z) ^ 2

section
end

set_option backward.isDefEq.respectTransparency false in
lemma riordanThirdOriginalFun_rescale (z : ℂ) :
    riordanThirdOriginalFun (((riordanRho : ℝ) : ℂ) * z) =
      riordanThirdAdjustedRescaledFun z := by
  unfold riordanThirdOriginalFun riordanOriginalFun riordanThirdAdjustedRescaledFun
    riordanRho riordanAnalyticQuadraticCoeff
  have hscale : 3 * (((1 / 3 : ℝ) : ℂ) * z) = z := by
    have h : (3 : ℂ) * (((1 / 3 : ℝ) : ℂ)) = 1 := by norm_num
    calc
      3 * (((1 / 3 : ℝ) : ℂ) * z) =
          ((3 : ℂ) * (((1 / 3 : ℝ) : ℂ))) * z := by ring
      _ = z := by rw [h]; ring
  rw [hscale]

private lemma PowerSeries_rescale_C (a c : ℂ) :
    PowerSeries.rescale a (PowerSeries.C c) = PowerSeries.C c := by
  ext n
  rw [PowerSeries.coeff_rescale]
  cases n with
  | zero =>
      simp
  | succ n =>
      simp

lemma rescale_riordanOneSubThreeXSeriesℂ :
    PowerSeries.rescale (((riordanRho : ℝ) : ℂ)) riordanOneSubThreeXSeriesℂ =
      riordanOneSubSeriesℂ := by
  ext n
  rw [PowerSeries.coeff_rescale]
  cases n with
  | zero =>
      simp [riordanOneSubThreeXSeriesℂ, riordanOneSubSeriesℂ]
  | succ n =>
      cases n with
      | zero =>
          simp [riordanOneSubThreeXSeriesℂ, riordanOneSubSeriesℂ, riordanRho,
            PowerSeries.coeff_X, PowerSeries.coeff_C]
      | succ n =>
          simp [riordanOneSubThreeXSeriesℂ, riordanOneSubSeriesℂ, PowerSeries.coeff_X]

lemma rescale_riordanThirdOriginalSeriesℂ :
    PowerSeries.rescale (((riordanRho : ℝ) : ℂ)) riordanThirdOriginalSeriesℂ =
      riordanThirdAdjustedRescaledSeriesℂ := by
  unfold riordanThirdOriginalSeriesℂ riordanThirdAdjustedRescaledSeriesℂ
  simp only [map_sub, map_mul, map_pow,
    rescale_riordanOneSubThreeXSeriesℂ]
  rw [PowerSeries_rescale_C]
  have hρ : (((riordanRho : ℝ) : ℂ)) = (3 : ℂ)⁻¹ := by
    unfold riordanRho
    norm_num
  rw [hρ]
  rfl

lemma riordanThirdAdjustedRescaledFun_hasFPowerSeriesAt_zero :
    HasFPowerSeriesAt riordanThirdAdjustedRescaledFun
      (PowerSeries.toFMLS riordanThirdAdjustedRescaledSeriesℂ) (0 : ℂ) := by
  have hsquare : HasFPowerSeriesAt (fun z : ℂ => (1 - z) * (1 - z))
      (PowerSeries.toFMLS (riordanOneSubSeriesℂ ^ 2)) (0 : ℂ) := by
    simpa [pow_two] using
      hasFPowerSeriesAt_mul_toFMLS hasFPowerSeriesAt_riordanOneSub_toFMLS
        hasFPowerSeriesAt_riordanOneSub_toFMLS
  have hquad : HasFPowerSeriesAt
      (fun z : ℂ => riordanAnalyticQuadraticCoeff * (1 - z) ^ 2)
      (PowerSeries.toFMLS
        (PowerSeries.C riordanAnalyticQuadraticCoeff * riordanOneSubSeriesℂ ^ 2))
      (0 : ℂ) := by
    have h := hsquare.const_smul (c := riordanAnalyticQuadraticCoeff)
    convert h using 1
    · ext z
      simp [pow_two, smul_eq_mul]
    · ext n
      simp [PowerSeries.toFMLS, FormalMultilinearSeries.ofScalars,
        PowerSeries.coeff_C_mul]
  have hsub := riordanRescaledFun_hasFPowerSeriesAt_zero.sub hquad
  simpa [riordanThirdAdjustedRescaledFun, riordanThirdAdjustedRescaledSeriesℂ,
    toFMLS_sub] using hsub

lemma riordanThirdOriginalFun_rescaled_hasFPowerSeriesAt_zero :
    HasFPowerSeriesAt
      (fun z : ℂ => riordanThirdOriginalFun (((riordanRho : ℝ) : ℂ) * z))
      (PowerSeries.toFMLS
        (PowerSeries.rescale (((riordanRho : ℝ) : ℂ)) riordanThirdOriginalSeriesℂ))
      (0 : ℂ) := by
  rw [rescale_riordanThirdOriginalSeriesℂ]
  simpa [riordanThirdOriginalFun_rescale] using
    riordanThirdAdjustedRescaledFun_hasFPowerSeriesAt_zero

lemma analyticOnNhd_riordanThirdAdjustedRescaledFun :
    AnalyticOnNhd ℂ riordanThirdAdjustedRescaledFun
      (DeltaDomainArg (3 / 2) (Real.pi / 4)) := by
  have hquad : AnalyticOnNhd ℂ
      (fun z : ℂ => riordanAnalyticQuadraticCoeff * (1 - z) ^ 2)
      (DeltaDomainArg (3 / 2) (Real.pi / 4)) := by
    simpa [pow_two] using
      (analyticOnNhd_const.mul
        ((analyticOnNhd_const.sub analyticOnNhd_id).mul
          (analyticOnNhd_const.sub analyticOnNhd_id)))
  simpa [riordanThirdAdjustedRescaledFun] using
    analyticOnNhd_riordanRescaledFun.sub hquad

lemma analyticOnNhd_riordanThirdOriginalFun_rescaled :
    AnalyticOnNhd ℂ
      (fun z : ℂ => riordanThirdOriginalFun (((riordanRho : ℝ) : ℂ) * z))
      (DeltaDomainArg (3 / 2) (Real.pi / 4)) := by
  simpa [riordanThirdOriginalFun_rescale] using
    analyticOnNhd_riordanThirdAdjustedRescaledFun

def riordanAnalyticPart (z : ℂ) : ℂ :=
  (3 / 2 : ℂ) / z

def riordanSingularPart (z : ℂ) : ℂ :=
  -(3 / 2 : ℂ) / (z * riordanSqrtPlus z)

def riordanOneSubInvTaylor (u : ℂ) : ℂ :=
  1 + u + u ^ 2

def riordanSqrtPlusInvTaylor (u : ℂ) : ℂ :=
  (((Real.sqrt 3 / 2 : ℝ) : ℂ)) * (1 + u / 8 + 3 * u ^ 2 / 128)

def riordanSingularPartTaylorFull (u : ℂ) : ℂ :=
  -(3 / 2 : ℂ) * riordanOneSubInvTaylor u * riordanSqrtPlusInvTaylor u

private lemma tendsto_isBigO_one_complex {α : Type*} [TopologicalSpace α]
    {l : Filter α} {f : α → ℂ} {a : ℂ} (hf : Tendsto f l (𝓝 a)) :
    f =O[l] (fun _ : α => (1 : ℝ)) := by
  refine IsBigO.of_bound (‖a‖ + 1) ?_
  have hlt : ‖a‖ < ‖a‖ + 1 := by linarith
  filter_upwards [hf.norm.eventually (Iio_mem_nhds hlt)] with x hx
  simpa using le_of_lt hx

private lemma cubic_mul_continuous_isBigO (g : ℂ → ℂ)
    (hg : ContinuousAt g 0) :
    (fun u : ℂ => u ^ 3 * g u) =O[𝓝 (0 : ℂ)]
      (fun u : ℂ => ‖u‖ ^ 3) := by
  refine IsBigO.of_bound (‖g 0‖ + 1) ?_
  have hlt : ‖g 0‖ < ‖g 0‖ + 1 := by linarith
  filter_upwards [hg.norm.eventually (Iio_mem_nhds hlt)] with u hu
  rw [norm_mul, norm_pow]
  have hnonneg : 0 ≤ ‖u‖ ^ 3 := by positivity
  calc
    ‖u‖ ^ 3 * ‖g u‖ ≤ ‖u‖ ^ 3 * (‖g 0‖ + 1) :=
      mul_le_mul_of_nonneg_left (le_of_lt hu) hnonneg
    _ = (‖g 0‖ + 1) * ‖‖u‖ ^ 3‖ := by
      rw [Real.norm_of_nonneg hnonneg]
      ring

private lemma norm_rpow_half_tendsto_zero :
    Tendsto (fun u : ℂ => ‖u‖ ^ (1 / 2 : ℝ)) (𝓝 (0 : ℂ)) (𝓝 0) := by
  have hpow : ContinuousAt (fun x : ℝ => x ^ (1 / 2 : ℝ)) 0 :=
    Real.continuousAt_rpow_const 0 (1 / 2 : ℝ)
      (Or.inr (by norm_num : (0 : ℝ) ≤ 1 / 2))
  have h := hpow.tendsto.comp
    (tendsto_norm_zero : Tendsto (fun u : ℂ => ‖u‖) (𝓝 0) (𝓝 0))
  change Tendsto (fun u : ℂ => ‖u‖ ^ (1 / 2 : ℝ)) (𝓝 0)
    (𝓝 ((0 : ℝ) ^ (1 / 2 : ℝ))) at h
  norm_num at h
  exact h

section
end

set_option backward.isDefEq.respectTransparency false in
private lemma norm_pow_three_isLittleO_norm_rpow_five_halves :
    (fun u : ℂ => ‖u‖ ^ 3) =o[𝓝 (0 : ℂ)]
      (fun u : ℂ => ‖u‖ ^ (5 / 2 : ℝ)) := by
  have hsmall : (fun u : ℂ => ‖u‖ ^ (1 / 2 : ℝ)) =o[𝓝 (0 : ℂ)]
      (fun _ : ℂ => (1 : ℝ)) :=
    (isLittleO_one_iff ℝ).2 norm_rpow_half_tendsto_zero
  have hbase : (fun u : ℂ => ‖u‖ ^ (5 / 2 : ℝ)) =O[𝓝 (0 : ℂ)]
      (fun u : ℂ => ‖u‖ ^ (5 / 2 : ℝ)) := isBigO_refl _ _
  have hprod := hbase.mul_isLittleO hsmall
  refine hprod.congr' ?_ ?_
  · filter_upwards with u
    by_cases hu : u = 0
    · simp [hu]
    · have hpos : 0 < ‖u‖ := norm_pos_iff.mpr hu
      rw [← Real.rpow_add hpos]
      norm_num
  · filter_upwards with u
    ring

private lemma norm_pow_three_mul_rpow_half_isLittleO_norm_rpow_five_halves :
    (fun u : ℂ => ‖u‖ ^ 3 * ‖u‖ ^ (1 / 2 : ℝ)) =o[𝓝 (0 : ℂ)]
      (fun u : ℂ => ‖u‖ ^ (5 / 2 : ℝ)) := by
  have hsmall : (fun u : ℂ => ‖u‖) =o[𝓝 (0 : ℂ)]
      (fun _ : ℂ => (1 : ℝ)) :=
    (isLittleO_one_iff ℝ).2 tendsto_norm_zero
  have hbase : (fun u : ℂ => ‖u‖ ^ (5 / 2 : ℝ)) =O[𝓝 (0 : ℂ)]
      (fun u : ℂ => ‖u‖ ^ (5 / 2 : ℝ)) := isBigO_refl _ _
  have hprod := hbase.mul_isLittleO hsmall
  refine hprod.congr' ?_ ?_
  · filter_upwards with u
    by_cases hu : u = 0
    · simp [hu]
    · have hpos : 0 < ‖u‖ := norm_pos_iff.mpr hu
      calc
        ‖u‖ ^ (5 / 2 : ℝ) * ‖u‖ =
            ‖u‖ ^ (5 / 2 : ℝ) * ‖u‖ ^ (1 : ℝ) := by rw [Real.rpow_one]
        _ = ‖u‖ ^ ((5 / 2 : ℝ) + 1) := by rw [← Real.rpow_add hpos]
        _ = ‖u‖ ^ (3 + (1 / 2 : ℝ)) := by norm_num
        _ = ‖u‖ ^ 3 * ‖u‖ ^ (1 / 2 : ℝ) := by
          rw [Real.rpow_add hpos]
          norm_num
  · filter_upwards with u
    ring

lemma riordanSqrtPlus_ne_zero_of_norm_lt_three {z : ℂ} (hz : ‖z‖ < 3) :
    riordanSqrtPlus z ≠ 0 := by
  intro h
  have hsq := riordanSqrtPlus_sq z
  rw [h] at hsq
  norm_num at hsq
  have hsum : 1 + z / 3 = 0 := by simpa using hsq.symm
  have hz_eq : z = -3 := by linear_combination 3 * hsum
  have hnorm : ‖z‖ = 3 := by rw [hz_eq]; norm_num
  nlinarith

lemma riordanRescaledFun_decomp {z : ℂ} (hz0 : z ≠ 0) (hznorm : ‖z‖ < 3) :
    riordanRescaledFun z =
      riordanAnalyticPart z + riordanSingularPart z * riordanSqrtOneSub z := by
  have hD : riordanRescaledDenominator z ≠ 0 :=
    riordanRescaledDenominator_ne_zero_of_norm_lt_three hznorm
  have ht : riordanSqrtPlus z ≠ 0 := riordanSqrtPlus_ne_zero_of_norm_lt_three hznorm
  unfold riordanRescaledFun riordanAnalyticPart riordanSingularPart
  field_simp [hD, hz0, ht]
  unfold riordanRescaledDenominator
  ring_nf
  rw [riordanSqrtPlus_sq, riordanSqrtOneSub_sq]
  ring

lemma riordanAnalyticPart_remainder_isBigO :
    (fun u : ℂ =>
      riordanAnalyticPart (1 - u) -
        (riordanRegularValueℂ + riordanAnalyticLinearCoeff * u +
          riordanAnalyticQuadraticCoeff * u ^ 2))
      =O[𝓝 (0 : ℂ)] (fun u : ℂ => ‖u‖ ^ 3) := by
  have hbase := cubic_mul_continuous_isBigO
    (fun u : ℂ => (3 / 2 : ℂ) / (1 - u))
    (by
      apply ContinuousAt.div
      · fun_prop
      · fun_prop
      · norm_num)
  refine hbase.congr' ?_ (EventuallyEq.refl _ _)
  filter_upwards [eventually_ne_nhds (show (0 : ℂ) ≠ 1 by norm_num)] with u hu
  unfold riordanAnalyticPart riordanRegularValueℂ riordanAnalyticLinearCoeff
    riordanAnalyticQuadraticCoeff
  field_simp [sub_ne_zero.mpr (Ne.symm hu)]
  ring

lemma riordanOneSubInv_sub_taylor_isBigO :
    (fun u : ℂ => (1 - u)⁻¹ - riordanOneSubInvTaylor u)
      =O[𝓝 (0 : ℂ)] (fun u : ℂ => ‖u‖ ^ 3) := by
  have hbase := cubic_mul_continuous_isBigO
    (fun u : ℂ => (1 - u)⁻¹)
    (by
      apply ContinuousAt.inv₀
      · fun_prop
      · norm_num)
  refine hbase.congr' ?_ (EventuallyEq.refl _ _)
  filter_upwards [eventually_ne_nhds (show (0 : ℂ) ≠ 1 by norm_num)] with u hu
  unfold riordanOneSubInvTaylor
  field_simp [sub_ne_zero.mpr (Ne.symm hu)]
  ring

lemma riordanSqrtPlusInvTaylor_sq_residual (u : ℂ) :
    1 - (riordanSqrtPlus (1 - u) * riordanSqrtPlusInvTaylor u) ^ 2 =
      u ^ 3 * ((5 / 512 : ℂ) + (15 / 16384 : ℂ) * u + (9 / 65536 : ℂ) * u ^ 2) := by
  rw [show (riordanSqrtPlus (1 - u) * riordanSqrtPlusInvTaylor u) ^ 2 =
      (riordanSqrtPlus (1 - u)) ^ 2 * (riordanSqrtPlusInvTaylor u) ^ 2 by ring]
  rw [riordanSqrtPlus_sq]
  unfold riordanSqrtPlusInvTaylor
  norm_num [Complex.ofReal_div, Complex.ofReal_mul]
  ring_nf
  rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
  norm_num
  ring_nf

lemma riordanSqrtPlusInvTaylor_sq_residual_isBigO :
    (fun u : ℂ => 1 - (riordanSqrtPlus (1 - u) * riordanSqrtPlusInvTaylor u) ^ 2)
      =O[𝓝 (0 : ℂ)] (fun u : ℂ => ‖u‖ ^ 3) := by
  have hbase := cubic_mul_continuous_isBigO
    (fun u : ℂ => (5 / 512 : ℂ) + (15 / 16384 : ℂ) * u + (9 / 65536 : ℂ) * u ^ 2)
    (by fun_prop)
  refine hbase.congr_left ?_
  intro u
  rw [riordanSqrtPlusInvTaylor_sq_residual]

lemma riordanSqrtPlusInv_sub_taylor_isBigO :
    (fun u : ℂ => (riordanSqrtPlus (1 - u))⁻¹ - riordanSqrtPlusInvTaylor u)
      =O[𝓝 (0 : ℂ)] (fun u : ℂ => ‖u‖ ^ 3) := by
  let t : ℂ → ℂ := fun u => riordanSqrtPlus (1 - u)
  let q : ℂ → ℂ := riordanSqrtPlusInvTaylor
  have ht : Tendsto t (𝓝 (0 : ℂ)) (𝓝 riordanSqrtPlusAtOneℂ) := by
    have harg : Tendsto (fun u : ℂ => 1 - u) (𝓝 (0 : ℂ)) (𝓝 (1 : ℂ)) := by
      simpa using
        (continuousAt_const.sub continuousAt_id :
          ContinuousAt (fun u : ℂ => 1 - u) 0).tendsto
    simpa [t, riordanSqrtPlus_one] using
      hasDerivAt_riordanSqrtPlus_one.continuousAt.tendsto.comp harg
  have hq : Tendsto q (𝓝 (0 : ℂ)) (𝓝 ((((Real.sqrt 3 / 2 : ℝ) : ℂ)))) := by
    have hcont : ContinuousAt q 0 := by
      unfold q riordanSqrtPlusInvTaylor
      fun_prop
    simpa [q, riordanSqrtPlusInvTaylor] using hcont.tendsto
  have htq : Tendsto (fun u : ℂ => t u * q u) (𝓝 (0 : ℂ)) (𝓝 (1 : ℂ)) := by
    have hmul := ht.mul hq
    convert hmul using 1
    unfold riordanSqrtPlusAtOneℂ
    have hs3 : ((Real.sqrt 3 : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast (Real.sqrt_ne_zero'.mpr (by norm_num : (0 : ℝ) < 3))
    norm_num [Complex.ofReal_div, Complex.ofReal_mul]
  have hsum_tendsto : Tendsto (fun u : ℂ => 1 + t u * q u)
      (𝓝 (0 : ℂ)) (𝓝 (2 : ℂ)) := by
    convert tendsto_const_nhds.add htq using 1
    norm_num
  have hden : Tendsto (fun u : ℂ => (1 + t u * q u)⁻¹)
      (𝓝 (0 : ℂ)) (𝓝 ((2 : ℂ)⁻¹)) :=
    hsum_tendsto.inv₀ (by norm_num : (2 : ℂ) ≠ 0)
  have hdenO : (fun u : ℂ => (1 + t u * q u)⁻¹)
      =O[𝓝 (0 : ℂ)] (fun _ : ℂ => (1 : ℝ)) :=
    tendsto_isBigO_one_complex hden
  have hprod := riordanSqrtPlusInvTaylor_sq_residual_isBigO.mul hdenO
  have hone_minus : (fun u : ℂ => 1 - t u * q u)
      =O[𝓝 (0 : ℂ)] (fun u : ℂ => ‖u‖ ^ 3) := by
    refine hprod.congr' ?_ ?_
    · have hsum_ne : ∀ᶠ u : ℂ in 𝓝 (0 : ℂ), 1 + t u * q u ≠ 0 :=
        hsum_tendsto.eventually_ne (by norm_num : (2 : ℂ) ≠ 0)
      filter_upwards [hsum_ne] with u hu
      dsimp [t, q] at hu ⊢
      rw [show 1 - riordanSqrtPlus (1 - u) * riordanSqrtPlusInvTaylor u =
          (1 - (riordanSqrtPlus (1 - u) * riordanSqrtPlusInvTaylor u) ^ 2) *
            (1 + riordanSqrtPlus (1 - u) * riordanSqrtPlusInvTaylor u)⁻¹ by
        field_simp [hu]
        ring]
    · filter_upwards with u
      ring
  have htinv : Tendsto (fun u : ℂ => (t u)⁻¹)
      (𝓝 (0 : ℂ)) (𝓝 (riordanSqrtPlusAtOneℂ⁻¹)) := by
    refine ht.inv₀ ?_
    unfold riordanSqrtPlusAtOneℂ
    norm_num
  have htinvO : (fun u : ℂ => (t u)⁻¹)
      =O[𝓝 (0 : ℂ)] (fun _ : ℂ => (1 : ℝ)) :=
    tendsto_isBigO_one_complex htinv
  have hfinal := hone_minus.mul htinvO
  refine hfinal.congr' ?_ ?_
  · have ht_ne : ∀ᶠ u : ℂ in 𝓝 (0 : ℂ), t u ≠ 0 := by
      exact ht.eventually_ne (by
        unfold riordanSqrtPlusAtOneℂ
        norm_num)
    filter_upwards [ht_ne] with u hu
    dsimp [t, q] at hu ⊢
    field_simp [hu]
  · filter_upwards with u
    ring

lemma riordanSingularPartTaylorFull_sub_trunc (u : ℂ) :
    riordanSingularPartTaylorFull u -
        (riordanSingularCoeff + riordanSecondSingularCoeff * u +
          riordanThirdSingularCoeff * u ^ 2) =
      u ^ 3 * (riordanSingularCoeff * ((19 / 128 : ℂ) + (3 / 128 : ℂ) * u)) := by
  unfold riordanSingularPartTaylorFull riordanOneSubInvTaylor riordanSqrtPlusInvTaylor
    riordanThirdSingularCoeff riordanSecondSingularCoeff riordanSingularCoeff
  norm_num [Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_neg]
  ring

lemma riordanSingularPartTaylorFull_sub_trunc_isBigO :
    (fun u : ℂ =>
      riordanSingularPartTaylorFull u -
        (riordanSingularCoeff + riordanSecondSingularCoeff * u +
          riordanThirdSingularCoeff * u ^ 2))
      =O[𝓝 (0 : ℂ)] (fun u : ℂ => ‖u‖ ^ 3) := by
  have hbase := cubic_mul_continuous_isBigO
    (fun u : ℂ => riordanSingularCoeff * ((19 / 128 : ℂ) + (3 / 128 : ℂ) * u))
    (by fun_prop)
  refine hbase.congr_left ?_
  intro u
  rw [riordanSingularPartTaylorFull_sub_trunc]

lemma riordanSingularPart_remainder_isBigO :
    (fun u : ℂ =>
      riordanSingularPart (1 - u) -
        (riordanSingularCoeff + riordanSecondSingularCoeff * u +
          riordanThirdSingularCoeff * u ^ 2))
      =O[𝓝 (0 : ℂ)] (fun u : ℂ => ‖u‖ ^ 3) := by
  let t : ℂ → ℂ := fun u => riordanSqrtPlus (1 - u)
  let oneInv : ℂ → ℂ := fun u => (1 - u)⁻¹
  let sqrtInv : ℂ → ℂ := fun u => (t u)⁻¹
  let oneTaylor : ℂ → ℂ := riordanOneSubInvTaylor
  let sqrtTaylor : ℂ → ℂ := riordanSqrtPlusInvTaylor
  have harg : Tendsto (fun u : ℂ => 1 - u) (𝓝 (0 : ℂ)) (𝓝 (1 : ℂ)) := by
    simpa using
      (continuousAt_const.sub continuousAt_id :
        ContinuousAt (fun u : ℂ => 1 - u) 0).tendsto
  have ht : Tendsto t (𝓝 (0 : ℂ)) (𝓝 riordanSqrtPlusAtOneℂ) := by
    simpa [t, riordanSqrtPlus_one] using
      hasDerivAt_riordanSqrtPlus_one.continuousAt.tendsto.comp harg
  have hsInvO : sqrtInv =O[𝓝 (0 : ℂ)] (fun _ : ℂ => (1 : ℝ)) := by
    have htinv : Tendsto sqrtInv (𝓝 (0 : ℂ)) (𝓝 (riordanSqrtPlusAtOneℂ⁻¹)) := by
      refine ht.inv₀ ?_
      unfold riordanSqrtPlusAtOneℂ
      norm_num
    exact tendsto_isBigO_one_complex htinv
  have hOneDiff : (fun u : ℂ => oneInv u - oneTaylor u)
      =O[𝓝 (0 : ℂ)] (fun u : ℂ => ‖u‖ ^ 3) := by
    simpa [oneInv, oneTaylor] using riordanOneSubInv_sub_taylor_isBigO
  have hTermOne := hOneDiff.mul hsInvO
  have hOneTaylorO : oneTaylor =O[𝓝 (0 : ℂ)] (fun _ : ℂ => (1 : ℝ)) := by
    have hcont : ContinuousAt oneTaylor 0 := by
      unfold oneTaylor riordanOneSubInvTaylor
      fun_prop
    exact tendsto_isBigO_one_complex hcont.tendsto
  have hSqrtDiff : (fun u : ℂ => sqrtInv u - sqrtTaylor u)
      =O[𝓝 (0 : ℂ)] (fun u : ℂ => ‖u‖ ^ 3) := by
    simpa [sqrtInv, sqrtTaylor, t] using riordanSqrtPlusInv_sub_taylor_isBigO
  have hTermTwo := hOneTaylorO.mul hSqrtDiff
  have hTermTwo' : (fun u : ℂ => oneTaylor u * (sqrtInv u - sqrtTaylor u))
      =O[𝓝 (0 : ℂ)] (fun u : ℂ => ‖u‖ ^ 3 * 1) := by
    refine hTermTwo.congr_right ?_
    intro u
    ring
  have hprodDiff : (fun u : ℂ =>
      oneInv u * sqrtInv u - oneTaylor u * sqrtTaylor u)
      =O[𝓝 (0 : ℂ)] (fun u : ℂ => ‖u‖ ^ 3) := by
    have hsum := hTermOne.add hTermTwo'
    exact (hsum.congr_left (by intro u; ring)).congr_right (by intro u; ring)
  have hscaled : (fun u : ℂ =>
      -(3 / 2 : ℂ) * (oneInv u * sqrtInv u - oneTaylor u * sqrtTaylor u))
      =O[𝓝 (0 : ℂ)] (fun u : ℂ => ‖u‖ ^ 3) :=
    hprodDiff.const_mul_left (-(3 / 2 : ℂ))
  have hsum := hscaled.add riordanSingularPartTaylorFull_sub_trunc_isBigO
  refine hsum.congr' ?_ (EventuallyEq.refl _ _)
  have ht_ne : ∀ᶠ u : ℂ in 𝓝 (0 : ℂ), t u ≠ 0 := by
    exact ht.eventually_ne (by
      unfold riordanSqrtPlusAtOneℂ
      norm_num)
  filter_upwards [eventually_ne_nhds (show (0 : ℂ) ≠ 1 by norm_num), ht_ne] with u hu1 ht0
  dsimp [oneInv, sqrtInv, oneTaylor, sqrtTaylor, t]
  unfold riordanSingularPart riordanSingularPartTaylorFull
  field_simp [sub_ne_zero.mpr (Ne.symm hu1), ht0]
  ring

lemma riordanSqrtOneSub_local_isBigO :
    (fun u : ℂ => riordanSqrtOneSub (1 - u)) =O[𝓝 (0 : ℂ)]
      (fun u : ℂ => ‖u‖ ^ (1 / 2 : ℝ)) := by
  refine IsBigO.of_bound 1 ?_
  filter_upwards with u
  unfold riordanSqrtOneSub motzkinSqrtOneSub
  rw [show (1 : ℂ) - (1 - u) = u by ring]
  rw [show (1 / 2 : ℂ) = (((1 / 2 : ℝ) : ℂ)) by norm_num]
  rw [Complex.norm_cpow_real u (1 / 2 : ℝ)]
  rw [Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg u) _)]
  simp

lemma riordanThird_local_residual_eq {u : ℂ}
    (hu1 : u ≠ 1) (hznorm : ‖(1 : ℂ) - u‖ < 3) :
    sqrtAdjustedFun riordanThirdAdjustedRescaledFun riordanRegularValueℂ
        (-riordanAnalyticLinearCoeff) (1 - u) -
        riordanSingularCoeff * u ^ (1 / 2 : ℂ) -
        riordanSecondSingularCoeff * u ^ (3 / 2 : ℂ) -
        riordanThirdSingularCoeff * u ^ (5 / 2 : ℂ) =
      (riordanAnalyticPart (1 - u) -
        (riordanRegularValueℂ + riordanAnalyticLinearCoeff * u +
          riordanAnalyticQuadraticCoeff * u ^ 2)) +
        (riordanSingularPart (1 - u) -
          (riordanSingularCoeff + riordanSecondSingularCoeff * u +
            riordanThirdSingularCoeff * u ^ 2)) *
          riordanSqrtOneSub (1 - u) := by
  have hz_ne : (1 : ℂ) - u ≠ 0 := sub_ne_zero.mpr (Ne.symm hu1)
  have hdecomp := riordanRescaledFun_decomp (z := 1 - u) hz_ne hznorm
  have hs : riordanSqrtOneSub (1 - u) = u ^ (1 / 2 : ℂ) := by
    unfold riordanSqrtOneSub motzkinSqrtOneSub
    rw [show (1 : ℂ) - (1 - u) = u by ring]
  have hpow3 : u ^ (3 / 2 : ℂ) = u * riordanSqrtOneSub (1 - u) := by
    by_cases hu0 : u = 0
    · subst u
      norm_num [riordanSqrtOneSub, motzkinSqrtOneSub]
    · rw [hs]
      rw [show (3 / 2 : ℂ) = 1 + (1 / 2 : ℂ) by norm_num]
      rw [Complex.cpow_add _ _ hu0, Complex.cpow_one]
  have hpow5 : u ^ (5 / 2 : ℂ) = u ^ 2 * riordanSqrtOneSub (1 - u) := by
    by_cases hu0 : u = 0
    · subst u
      norm_num [riordanSqrtOneSub, motzkinSqrtOneSub]
    · rw [hs]
      rw [show (5 / 2 : ℂ) = 2 + (1 / 2 : ℂ) by norm_num]
      rw [Complex.cpow_add _ _ hu0]
      norm_num [Complex.cpow_natCast]
  unfold sqrtAdjustedFun sqrtLinearAtOneFun riordanThirdAdjustedRescaledFun
  rw [hdecomp, hpow3, hpow5, hs]
  ring

lemma riordanThird_local_residual_isLittleO :
    (fun u : ℂ =>
      sqrtAdjustedFun riordanThirdAdjustedRescaledFun riordanRegularValueℂ
          (-riordanAnalyticLinearCoeff) (1 - u) -
          riordanSingularCoeff * u ^ (1 / 2 : ℂ) -
          riordanSecondSingularCoeff * u ^ (3 / 2 : ℂ) -
          riordanThirdSingularCoeff * u ^ (5 / 2 : ℂ))
      =o[𝓝 (0 : ℂ)] (fun u : ℂ => ‖u‖ ^ (5 / 2 : ℝ)) := by
  have hA := riordanAnalyticPart_remainder_isBigO.trans_isLittleO
    norm_pow_three_isLittleO_norm_rpow_five_halves
  have hBbig := riordanSingularPart_remainder_isBigO.mul
    riordanSqrtOneSub_local_isBigO
  have hB := hBbig.trans_isLittleO
    norm_pow_three_mul_rpow_half_isLittleO_norm_rpow_five_halves
  have hsum := hA.add hB
  refine hsum.congr' ?_ (EventuallyEq.refl _ _)
  have hnorm : ∀ᶠ u : ℂ in 𝓝 (0 : ℂ), ‖(1 : ℂ) - u‖ < 3 := by
    have hcont : ContinuousAt (fun u : ℂ => ‖(1 : ℂ) - u‖) 0 := by
      fun_prop
    exact hcont.tendsto.eventually (Iio_mem_nhds (by norm_num : ‖(1 : ℂ) - 0‖ < 3))
  filter_upwards [eventually_ne_nhds (show (0 : ℂ) ≠ 1 by norm_num), hnorm] with u hu1 hzu
  simpa using (riordanThird_local_residual_eq (u := u) hu1 hzu).symm

lemma tendsto_riordanThirdAdjustedRescaledFun_singularity :
    Tendsto
      (fun z : ℂ =>
        ‖sqrtAdjustedFun riordanThirdAdjustedRescaledFun riordanRegularValueℂ
            (-riordanAnalyticLinearCoeff) z -
            riordanSingularCoeff * (1 - z) ^ (1 / 2 : ℂ) -
            riordanSecondSingularCoeff * (1 - z) ^ (3 / 2 : ℂ) -
            riordanThirdSingularCoeff * (1 - z) ^ (5 / 2 : ℂ)‖ *
          ‖(1 : ℂ) - z‖ ^ (-(5 / 2 : ℝ)))
      (𝓝[DeltaDomainArg (3 / 2) (Real.pi / 4)] (1 : ℂ)) (𝓝 0) := by
  let l := 𝓝[DeltaDomainArg (3 / 2) (Real.pi / 4)] (1 : ℂ)
  have hu : Tendsto (fun z : ℂ => 1 - z) l (𝓝 (0 : ℂ)) := by
    have hcont : ContinuousAt (fun z : ℂ => 1 - z) 1 := by fun_prop
    simpa using Tendsto.mono_left hcont.tendsto nhdsWithin_le_nhds
  have hcomp := riordanThird_local_residual_isLittleO.comp_tendsto hu
  have hdiv := hcomp.norm_norm.tendsto_div_nhds_zero
  refine hdiv.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with z hz
  have hz_ne : z ≠ 1 := hz.2.1
  have hpos : 0 < ‖(1 : ℂ) - z‖ := norm_pos_iff.mpr (sub_ne_zero.mpr (Ne.symm hz_ne))
  rw [div_eq_mul_inv]
  dsimp only [Function.comp_apply]
  rw [show (1 : ℂ) - (1 - z) = z by ring]
  rw [Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg ((1 : ℂ) - z)) _)]
  rw [Real.rpow_neg hpos.le]

lemma riordanSecondSingularCoeff_eq_meta :
    riordanSecondSingularCoeff =
      -(((riordanRho : ℝ) : ℂ) * riordanSingularDerivAtRho) := by
  unfold riordanSecondSingularCoeff riordanSingularCoeff riordanRho
    riordanSingularDerivAtRho
  norm_num [Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_neg]
  ring

lemma riordanThirdSingularCoeff_eq_meta :
    riordanThirdSingularCoeff =
      ((((riordanRho : ℝ) : ℂ) ^ 2 * riordanSingularSecondDerivAtRho) / 2) := by
  unfold riordanThirdSingularCoeff riordanRho riordanSingularSecondDerivAtRho
  norm_num [Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_neg]
  ring

lemma riordanThirdAsymptoticConstant_eq_meta :
    sqrtSingularityC2 riordanRho riordanSingularCoeff
        riordanSingularDerivAtRho riordanSingularSecondDerivAtRho =
      ((riordanThirdAsymptoticConstant : ℝ) : ℂ) := by
  unfold sqrtSingularityC2 sqrtSingularityC2Rescaled riordanRho riordanSingularCoeff
    riordanSingularDerivAtRho riordanSingularSecondDerivAtRho
    riordanThirdAsymptoticConstant
  norm_num [Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_neg]
  ring

lemma riordanFirstAsymptoticConstant_eq_meta :
    sqrtSingularityC0 riordanSingularCoeff =
      ((riordanAsymptoticConstant : ℝ) : ℂ) := by
  unfold sqrtSingularityC0 riordanSingularCoeff riordanAsymptoticConstant
  norm_num [Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_neg]
  ring

lemma riordanSecondAsymptoticConstant_eq_meta :
    sqrtSingularityC1 riordanRho riordanSingularCoeff riordanSingularDerivAtRho =
      ((riordanSecondAsymptoticConstant : ℝ) : ℂ) := by
  unfold sqrtSingularityC1 sqrtSingularityC1Rescaled riordanRho riordanSingularCoeff
    riordanSingularDerivAtRho riordanSecondAsymptoticConstant
  norm_num [Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_neg]
  ring

lemma riordanSingularCoeff_ne_zero : riordanSingularCoeff ≠ 0 := by
  unfold riordanSingularCoeff
  norm_num

theorem riordanThirdOriginalSeries_complex_meta :
    (fun n : ℕ =>
      PowerSeries.coeff (R := ℂ) n riordanThirdOriginalSeriesℂ -
        (((((riordanRho : ℝ) : ℂ)⁻¹) ^ n) *
          (sqrtSingularityC0 riordanSingularCoeff *
              (((n : ℝ) ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ) +
            sqrtSingularityC1 riordanRho riordanSingularCoeff riordanSingularDerivAtRho *
              (((n : ℝ) ^ (-(5 / 2 : ℝ)) : ℝ) : ℂ) +
            sqrtSingularityC2 riordanRho riordanSingularCoeff
                riordanSingularDerivAtRho riordanSingularSecondDerivAtRho *
              (((n : ℝ) ^ (-(7 / 2 : ℝ)) : ℝ) : ℂ))))
      =o[atTop]
        (fun n : ℕ =>
          ‖(((((riordanRho : ℝ) : ℂ)⁻¹) ^ n) *
            (((n : ℝ) ^ (-(7 / 2 : ℝ)) : ℝ) : ℂ))‖) := by
  refine sqrt_singularity_thirdOrder_original_of_rescaled_singularity
    (ρ := riordanRho) (R := (3 / 2 : ℝ)) (φ := Real.pi / 4)
    (F := riordanThirdOriginalFun) (P := riordanThirdOriginalSeriesℂ)
    (A0 := riordanRegularValueℂ) (A1 := -riordanAnalyticLinearCoeff)
    (Bρ := riordanSingularCoeff)
    (Bderivρ := riordanSingularDerivAtRho)
    (Bsecondρ := riordanSingularSecondDerivAtRho)
    ?_ riordanSingularCoeff_ne_zero ?_ ?_ ?_
    riordanThirdOriginalFun_rescaled_hasFPowerSeriesAt_zero
    analyticOnNhd_riordanThirdOriginalFun_rescaled ?_
  · unfold riordanRho
    norm_num
  · norm_num
  · positivity
  · nlinarith [Real.pi_pos]
  · have h := tendsto_riordanThirdAdjustedRescaledFun_singularity
    have hrescale : ∀ w : ℂ,
        riordanThirdOriginalFun (((riordanRho : ℝ) : ℂ) * w) =
          riordanThirdAdjustedRescaledFun w :=
      riordanThirdOriginalFun_rescale
    have hrescale3 : ∀ w : ℂ,
        riordanThirdOriginalFun ((3 : ℂ)⁻¹ * w) =
          riordanThirdAdjustedRescaledFun w := by
      intro w
      have hρ : (((riordanRho : ℝ) : ℂ)) = (3 : ℂ)⁻¹ := by
        unfold riordanRho
        norm_num
      rw [← hρ]
      exact hrescale w
    refine h.congr' ?_
    filter_upwards with z
    simp [sqrtAdjustedFun, hrescale, riordanSecondSingularCoeff_eq_meta,
      riordanThirdSingularCoeff_eq_meta]

section
end

set_option backward.isDefEq.respectTransparency false in
lemma riordanOneSubThreeXSeries_sq_coeff_of_three_le {n : ℕ} (hn : 3 ≤ n) :
    PowerSeries.coeff (R := ℂ) n (riordanOneSubThreeXSeriesℂ ^ 2) = 0 := by
  rw [pow_two, PowerSeries.coeff_mul]
  apply Finset.sum_eq_zero
  intro p hp
  rcases p with ⟨i, j⟩
  have hij : i + j = n := Finset.mem_antidiagonal.mp hp
  have hlarge : 2 ≤ i ∨ 2 ≤ j := by
    by_contra h
    push Not at h
    have hi : i ≤ 1 := Nat.lt_succ_iff.mp h.1
    have hj : j ≤ 1 := Nat.lt_succ_iff.mp h.2
    omega
  rcases hlarge with hi | hj
  · have hcoeff : PowerSeries.coeff (R := ℂ) i riordanOneSubThreeXSeriesℂ = 0 := by
      unfold riordanOneSubThreeXSeriesℂ
      simp [PowerSeries.coeff_X,
        ne_of_gt (lt_of_lt_of_le (by norm_num : 0 < 2) hi),
        ne_of_gt (lt_of_lt_of_le (by norm_num : 1 < 2) hi)]
    simp [hcoeff]
  · have hcoeff : PowerSeries.coeff (R := ℂ) j riordanOneSubThreeXSeriesℂ = 0 := by
      unfold riordanOneSubThreeXSeriesℂ
      simp [PowerSeries.coeff_X,
        ne_of_gt (lt_of_lt_of_le (by norm_num : 0 < 2) hj),
        ne_of_gt (lt_of_lt_of_le (by norm_num : 1 < 2) hj)]
    simp [hcoeff]

lemma coeff_riordanThirdOriginalSeriesℂ_of_three_le {n : ℕ} (hn : 3 ≤ n) :
    PowerSeries.coeff (R := ℂ) n riordanThirdOriginalSeriesℂ = (riordan n : ℂ) := by
  unfold riordanThirdOriginalSeriesℂ
  simp [PowerSeries.coeff_C_mul, riordanOneSubThreeXSeries_sq_coeff_of_three_le hn]

private lemma complex_re_isLittleO_ofReal {f : ℕ → ℂ} {g r : ℕ → ℝ}
    (h : (fun n : ℕ => f n - ((g n : ℝ) : ℂ)) =o[atTop] r) :
    (fun n : ℕ => (f n).re - g n) =o[atTop] r := by
  rw [Asymptotics.isLittleO_iff] at h ⊢
  intro c hc
  have hc_bound := h hc
  filter_upwards [hc_bound] with n hn
  calc
    ‖(f n).re - g n‖ = ‖(f n - (g n : ℂ)).re‖ := by
      simp [Complex.sub_re]
    _ ≤ ‖f n - (g n : ℂ)‖ := Complex.abs_re_le_norm _
    _ ≤ c * ‖r n‖ := hn

section
end

set_option backward.isDefEq.respectTransparency false in
theorem riordan_complex_thirdOrder_additive :
    (fun n : ℕ =>
      (riordan n : ℂ) -
        (((((3 : ℝ) ^ n) *
          (riordanAsymptoticConstant * (n : ℝ) ^ (-(3 / 2 : ℝ)) +
            riordanSecondAsymptoticConstant * (n : ℝ) ^ (-(5 / 2 : ℝ)) +
            riordanThirdAsymptoticConstant * (n : ℝ) ^ (-(7 / 2 : ℝ))) : ℝ) : ℂ)))
      =o[atTop]
        (fun n : ℕ => (3 : ℝ) ^ n * (n : ℝ) ^ (-(7 / 2 : ℝ))) := by
  have h := riordanThirdOriginalSeries_complex_meta
  refine h.congr' ?_ ?_
  · filter_upwards [eventually_ge_atTop 3] with n hn
    rw [coeff_riordanThirdOriginalSeriesℂ_of_three_le hn]
    rw [riordanFirstAsymptoticConstant_eq_meta,
      riordanSecondAsymptoticConstant_eq_meta,
      riordanThirdAsymptoticConstant_eq_meta]
    have hρ : (((riordanRho : ℝ) : ℂ)⁻¹) ^ n = (((3 : ℝ) ^ n : ℝ) : ℂ) := by
      have hbase : (((riordanRho : ℝ) : ℂ)⁻¹) = ((3 : ℝ) : ℂ) := by
        unfold riordanRho
        norm_num
      rw [hbase, Complex.ofReal_pow]
    rw [hρ]
    norm_num [Complex.ofReal_mul, Complex.ofReal_add]
  · filter_upwards [eventually_ge_atTop 1] with n hn
    have hnpos : 0 < (n : ℝ) := by
      exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < (1 : ℕ)) hn)
    have hρ : (((riordanRho : ℝ) : ℂ)⁻¹) ^ n = (((3 : ℝ) ^ n : ℝ) : ℂ) := by
      have hbase : (((riordanRho : ℝ) : ℂ)⁻¹) = ((3 : ℝ) : ℂ) := by
        unfold riordanRho
        norm_num
      rw [hbase, Complex.ofReal_pow]
    rw [hρ, norm_mul, Complex.norm_real, Complex.norm_real]
    rw [Real.norm_of_nonneg (by positivity : 0 ≤ (3 : ℝ) ^ n)]
    rw [Real.norm_of_nonneg (Real.rpow_nonneg (le_of_lt hnpos) _)]

theorem riordan_thirdOrder_additive :
    (fun n : ℕ =>
      (riordan n : ℝ) -
        (3 : ℝ) ^ n *
          (riordanAsymptoticConstant * (n : ℝ) ^ (-(3 / 2 : ℝ)) +
            riordanSecondAsymptoticConstant * (n : ℝ) ^ (-(5 / 2 : ℝ)) +
            riordanThirdAsymptoticConstant * (n : ℝ) ^ (-(7 / 2 : ℝ))))
      =o[atTop]
        (fun n : ℕ => (3 : ℝ) ^ n * (n : ℝ) ^ (-(7 / 2 : ℝ))) := by
  have hcomplex :
      (fun n : ℕ =>
        (((riordan n : ℝ) : ℂ) -
          ((((3 : ℝ) ^ n *
            (riordanAsymptoticConstant * (n : ℝ) ^ (-(3 / 2 : ℝ)) +
              riordanSecondAsymptoticConstant * (n : ℝ) ^ (-(5 / 2 : ℝ)) +
              riordanThirdAsymptoticConstant * (n : ℝ) ^ (-(7 / 2 : ℝ))) : ℝ) : ℂ))))
        =o[atTop]
          (fun n : ℕ => (3 : ℝ) ^ n * (n : ℝ) ^ (-(7 / 2 : ℝ))) := by
    simpa [Complex.ofReal_mul, Complex.ofReal_add] using riordan_complex_thirdOrder_additive
  have hreal := complex_re_isLittleO_ofReal hcomplex
  simpa using hreal

lemma riordanThirdAsymptoticConstant_eq_relative :
    riordanThirdAsymptoticConstant =
      riordanAsymptoticConstant * riordanRelativeThirdConstant := by
  unfold riordanThirdAsymptoticConstant riordanAsymptoticConstant
    riordanRelativeThirdConstant
  ring

end

set_option maxHeartbeats 1200000
open Complex Filter Asymptotics Set
open scoped Topology BigOperators PowerSeries
theorem solution :
    (fun n : ℕ =>
      (riordan n : ℝ) -
        (3 : ℝ) ^ n * riordanAsymptoticConstant *
          (n : ℝ) ^ (-(3 / 2 : ℝ)) *
          (1 + riordanRelativeSecondConstant * (n : ℝ) ^ (-(1 : ℝ)) +
            riordanRelativeThirdConstant * (n : ℝ) ^ (-(2 : ℝ))))
      =o[atTop]
        (fun n : ℕ => (3 : ℝ) ^ n * (n : ℝ) ^ (-(7 / 2 : ℝ))) := by
  refine riordan_thirdOrder_additive.congr' ?_ (EventuallyEq.refl _ _)
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hnpos : 0 < (n : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < (1 : ℕ)) hn)
  have hpow5 : (n : ℝ) ^ (-(5 / 2 : ℝ)) =
      (n : ℝ) ^ (-(3 / 2 : ℝ)) * (n : ℝ) ^ (-(1 : ℝ)) := by
    rw [← Real.rpow_add hnpos]
    norm_num
  have hpow7 : (n : ℝ) ^ (-(7 / 2 : ℝ)) =
      (n : ℝ) ^ (-(3 / 2 : ℝ)) * (n : ℝ) ^ (-(2 : ℝ)) := by
    rw [← Real.rpow_add hnpos]
    norm_num
  rw [riordanSecondAsymptoticConstant_eq_relative,
    riordanThirdAsymptoticConstant_eq_relative, hpow5, hpow7]
  ring
