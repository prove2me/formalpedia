-- Prove2me | solution 1 for motzkin_thirdOrder
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-10-28T12:32:06.080498+00:00
-- url     : https://prove2.me/submissions/3b1f564b-ce7d-4ab9-b25b-0f12886afe98

import Definitions.Def_AnalyticCombinatorics_Ch4_Analytic_Bridge
import Definitions.Def_AnalyticCombinatorics_Ch4_Analytic_DeltaDomain
import Definitions.Def_AnalyticCombinatorics_Ch4_Analytic_SqrtSingularitySecondOrder
import Definitions.Def_AnalyticCombinatorics_Ch4_Analytic_SqrtSingularityThirdOrder
import Definitions.Def_AnalyticCombinatorics_Ch7_SingularityApp_Motzkin
import Definitions.Def_AnalyticCombinatorics_Ch7_SingularityApp_MotzkinSecondOrder
import Definitions.Def_AnalyticCombinatorics_Ch7_SingularityApp_MotzkinThirdOrder
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
# Second-order Motzkin asymptotics

The centered rescaled Motzkin function has an analytic linear term between the
two half-integer singular terms.  We subtract that linear term before applying
the general second-order transfer theorem; its coefficients vanish for `n ≥ 2`.
-/

set_option maxHeartbeats 1200000

open Complex Filter Asymptotics Set
open scoped Topology BigOperators PowerSeries

noncomputable section

def motzkinAnalyticLinearCoeff : ℂ := (15 / 2 : ℂ)

def motzkinSecondSingularCoeff : ℂ :=
  -(((45 * Real.sqrt 3 / 8 : ℝ) : ℂ))

def motzkinSecondAsymptoticConstant : ℝ :=
  -(117 * Real.sqrt 3 / (32 * Real.sqrt Real.pi))

def motzkinOneSubSeriesℂ : PowerSeries ℂ :=
  (1 : PowerSeries ℂ) - PowerSeries.X

lemma hasFPowerSeriesAt_one_sub_toFMLS :
    HasFPowerSeriesAt (fun z : ℂ => 1 - z)
      (PowerSeries.toFMLS motzkinOneSubSeriesℂ) (0 : ℂ) := by
  have hconst := hasFPowerSeriesAt_const_toFMLS_C (1 : ℂ)
  have hid := hasFPowerSeriesAt_id_toFMLS_X
  have hsub := hconst.sub hid
  simpa [motzkinOneSubSeriesℂ, toFMLS_sub] using hsub

lemma motzkinSqrtPlus_one :
    motzkinSqrtPlus (1 : ℂ) = ((2 / Real.sqrt 3 : ℝ) : ℂ) := by
  unfold motzkinSqrtPlus
  rw [show (1 : ℂ) + 1 / 3 = ((4 / 3 : ℝ) : ℂ) by norm_num]
  exact Complex_cpow_four_thirds_half

lemma hasDerivAt_motzkinSqrtPlus_one :
    HasDerivAt motzkinSqrtPlus (((Real.sqrt 3 / 12 : ℝ) : ℂ)) (1 : ℂ) := by
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

lemma motzkinSecondAsymptoticConstant_eq_relative :
    motzkinSecondAsymptoticConstant =
      motzkinAsymptoticConstant * motzkinRelativeSecondConstant := by
  unfold motzkinSecondAsymptoticConstant motzkinAsymptoticConstant
    motzkinRelativeSecondConstant
  ring

end
end

/-!
# Third-order Motzkin asymptotics

This file plugs the Motzkin square-root data at `ρ = 1 / 3` into the
third-order square-root applicator.
-/

set_option maxHeartbeats 1200000

open Complex Filter Asymptotics Set
open scoped Topology BigOperators PowerSeries

noncomputable section

def motzkinRho : ℝ := 1 / 3

def motzkinAnalyticQuadraticCoeff : ℂ := 12

def motzkinSingularDerivAtRho : ℂ :=
  (((135 * Real.sqrt 3 / 8 : ℝ) : ℂ))

def motzkinSingularSecondDerivAtRho : ℂ :=
  -(((9477 * Real.sqrt 3 / 64 : ℝ) : ℂ))

def motzkinThirdSingularCoeff : ℂ :=
  ((((motzkinRho : ℝ) : ℂ) ^ 2 * motzkinSingularSecondDerivAtRho) / 2)

def motzkinThirdAsymptoticConstant : ℝ :=
  7995 * Real.sqrt 3 / (1024 * Real.sqrt Real.pi)

def motzkinOneSubThreeXSeriesℂ : PowerSeries ℂ :=
  (1 : PowerSeries ℂ) - PowerSeries.C (3 : ℂ) * PowerSeries.X

def motzkinThirdOriginalSeriesℂ : PowerSeries ℂ :=
  motzkinSeriesℂ -
    PowerSeries.C motzkinAnalyticQuadraticCoeff * motzkinOneSubThreeXSeriesℂ ^ 2

def motzkinThirdAdjustedRescaledSeriesℂ : PowerSeries ℂ :=
  motzkinRescaledSeriesℂ -
    PowerSeries.C motzkinAnalyticQuadraticCoeff * motzkinOneSubSeriesℂ ^ 2

def motzkinOriginalFun (z : ℂ) : ℂ :=
  motzkinRescaledFun (3 * z)

def motzkinThirdOriginalFun (z : ℂ) : ℂ :=
  motzkinOriginalFun z - motzkinAnalyticQuadraticCoeff * (1 - 3 * z) ^ 2

def motzkinThirdAdjustedRescaledFun (z : ℂ) : ℂ :=
  motzkinRescaledFun z - motzkinAnalyticQuadraticCoeff * (1 - z) ^ 2

section
end

set_option backward.isDefEq.respectTransparency false in
lemma motzkinThirdOriginalFun_rescale (z : ℂ) :
    motzkinThirdOriginalFun (((motzkinRho : ℝ) : ℂ) * z) =
      motzkinThirdAdjustedRescaledFun z := by
  unfold motzkinThirdOriginalFun motzkinOriginalFun motzkinThirdAdjustedRescaledFun
    motzkinRho motzkinAnalyticQuadraticCoeff
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

lemma rescale_motzkinOneSubThreeXSeriesℂ :
    PowerSeries.rescale (((motzkinRho : ℝ) : ℂ)) motzkinOneSubThreeXSeriesℂ =
      motzkinOneSubSeriesℂ := by
  ext n
  rw [PowerSeries.coeff_rescale]
  cases n with
  | zero =>
      simp [motzkinOneSubThreeXSeriesℂ, motzkinOneSubSeriesℂ]
  | succ n =>
      cases n with
      | zero =>
          simp [motzkinOneSubThreeXSeriesℂ, motzkinOneSubSeriesℂ, motzkinRho,
            PowerSeries.coeff_X, PowerSeries.coeff_C]
      | succ n =>
          simp [motzkinOneSubThreeXSeriesℂ, motzkinOneSubSeriesℂ, PowerSeries.coeff_X]

lemma rescale_motzkinThirdOriginalSeriesℂ :
    PowerSeries.rescale (((motzkinRho : ℝ) : ℂ)) motzkinThirdOriginalSeriesℂ =
      motzkinThirdAdjustedRescaledSeriesℂ := by
  unfold motzkinThirdOriginalSeriesℂ motzkinThirdAdjustedRescaledSeriesℂ
  simp only [map_sub, map_mul, map_pow,
    rescale_motzkinOneSubThreeXSeriesℂ]
  rw [PowerSeries_rescale_C]
  have hρ : (((motzkinRho : ℝ) : ℂ)) = (3 : ℂ)⁻¹ := by
    unfold motzkinRho
    norm_num
  rw [hρ]
  rfl

lemma motzkinThirdAdjustedRescaledFun_hasFPowerSeriesAt_zero :
    HasFPowerSeriesAt motzkinThirdAdjustedRescaledFun
      (PowerSeries.toFMLS motzkinThirdAdjustedRescaledSeriesℂ) (0 : ℂ) := by
  have hsquare : HasFPowerSeriesAt (fun z : ℂ => (1 - z) * (1 - z))
      (PowerSeries.toFMLS (motzkinOneSubSeriesℂ ^ 2)) (0 : ℂ) := by
    simpa [pow_two] using
      hasFPowerSeriesAt_mul_toFMLS hasFPowerSeriesAt_one_sub_toFMLS
        hasFPowerSeriesAt_one_sub_toFMLS
  have hquad : HasFPowerSeriesAt
      (fun z : ℂ => motzkinAnalyticQuadraticCoeff * (1 - z) ^ 2)
      (PowerSeries.toFMLS
        (PowerSeries.C motzkinAnalyticQuadraticCoeff * motzkinOneSubSeriesℂ ^ 2))
      (0 : ℂ) := by
    have h := hsquare.const_smul (c := motzkinAnalyticQuadraticCoeff)
    convert h using 1
    · ext z
      simp [pow_two, smul_eq_mul]
    · ext n
      simp [PowerSeries.toFMLS, FormalMultilinearSeries.ofScalars,
        PowerSeries.coeff_C_mul]
  have hsub := motzkinRescaledFun_hasFPowerSeriesAt_zero.sub hquad
  simpa [motzkinThirdAdjustedRescaledFun, motzkinThirdAdjustedRescaledSeriesℂ,
    toFMLS_sub] using hsub

lemma motzkinThirdOriginalFun_rescaled_hasFPowerSeriesAt_zero :
    HasFPowerSeriesAt
      (fun z : ℂ => motzkinThirdOriginalFun (((motzkinRho : ℝ) : ℂ) * z))
      (PowerSeries.toFMLS
        (PowerSeries.rescale (((motzkinRho : ℝ) : ℂ)) motzkinThirdOriginalSeriesℂ))
      (0 : ℂ) := by
  rw [rescale_motzkinThirdOriginalSeriesℂ]
  simpa [motzkinThirdOriginalFun_rescale] using
    motzkinThirdAdjustedRescaledFun_hasFPowerSeriesAt_zero

lemma analyticOnNhd_motzkinThirdAdjustedRescaledFun :
    AnalyticOnNhd ℂ motzkinThirdAdjustedRescaledFun
      (DeltaDomainArg (3 / 2) (Real.pi / 4)) := by
  have hquad : AnalyticOnNhd ℂ
      (fun z : ℂ => motzkinAnalyticQuadraticCoeff * (1 - z) ^ 2)
      (DeltaDomainArg (3 / 2) (Real.pi / 4)) := by
    simpa [pow_two] using
      (analyticOnNhd_const.mul
        ((analyticOnNhd_const.sub analyticOnNhd_id).mul
          (analyticOnNhd_const.sub analyticOnNhd_id)))
  simpa [motzkinThirdAdjustedRescaledFun] using
    analyticOnNhd_motzkinRescaledFun.sub hquad

lemma analyticOnNhd_motzkinThirdOriginalFun_rescaled :
    AnalyticOnNhd ℂ
      (fun z : ℂ => motzkinThirdOriginalFun (((motzkinRho : ℝ) : ℂ) * z))
      (DeltaDomainArg (3 / 2) (Real.pi / 4)) := by
  simpa [motzkinThirdOriginalFun_rescale] using
    analyticOnNhd_motzkinThirdAdjustedRescaledFun

def motzkinAnalyticPart (z : ℂ) : ℂ :=
  (9 / 2 : ℂ) * (1 - z / 3) / z ^ 2

def motzkinSingularPart (z : ℂ) : ℂ :=
  -(9 / 2 : ℂ) * motzkinSqrtPlus z / z ^ 2

def motzkinSqrtPlusTaylor (u : ℂ) : ℂ :=
  (((2 / Real.sqrt 3 : ℝ) : ℂ)) * (1 - u / 8 - u ^ 2 / 128)

def motzkinSqrtPlusBTaylor (u : ℂ) : ℂ :=
  -(2 / 9 : ℂ) *
    (motzkinSingularCoeff + motzkinSecondSingularCoeff * u +
      motzkinThirdSingularCoeff * u ^ 2) * (1 - u) ^ 2

section
end

set_option backward.isDefEq.respectTransparency false in
lemma motzkinRescaledFun_decomp {z : ℂ} (hz : z ≠ 0) :
    motzkinRescaledFun z =
      motzkinAnalyticPart z + motzkinSingularPart z * motzkinSqrtOneSub z := by
  unfold motzkinRescaledFun
  rw [div_eq_iff (motzkinRescaledDenominator_ne_zero z)]
  unfold motzkinAnalyticPart motzkinSingularPart motzkinRescaledDenominator
  field_simp [hz]
  ring_nf
  rw [motzkinSqrtOneSub_sq]
  unfold motzkinSqrtPlus
  rw [Complex_cpow_half_sq]
  ring_nf

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

lemma motzkinSqrtPlus_sq_sub_taylor_sq (u : ℂ) :
    (motzkinSqrtPlus (1 - u)) ^ 2 - (motzkinSqrtPlusTaylor u) ^ 2 =
      -u ^ 3 * (32 + u) / 12288 := by
  unfold motzkinSqrtPlus motzkinSqrtPlusTaylor
  rw [Complex_cpow_half_sq]
  norm_num [Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_sub]
  field_simp
  ring_nf
  rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
  norm_num
  ring_nf

lemma motzkinSqrtPlus_sub_taylor_isBigO :
    (fun u : ℂ => motzkinSqrtPlus (1 - u) - motzkinSqrtPlusTaylor u)
      =O[𝓝 (0 : ℂ)] (fun u : ℂ => ‖u‖ ^ 3) := by
  let t : ℂ → ℂ := fun u => motzkinSqrtPlus (1 - u)
  let q : ℂ → ℂ := motzkinSqrtPlusTaylor
  have ht : Tendsto t (𝓝 (0 : ℂ)) (𝓝 (((2 / Real.sqrt 3 : ℝ) : ℂ))) := by
    have harg : Tendsto (fun u : ℂ => 1 - u) (𝓝 (0 : ℂ)) (𝓝 (1 : ℂ)) := by
      simpa using (continuousAt_const.sub continuousAt_id : ContinuousAt (fun u : ℂ => 1 - u) 0).tendsto
    have h := hasDerivAt_motzkinSqrtPlus_one.continuousAt.tendsto.comp harg
    simpa [t, motzkinSqrtPlus_one] using h
  have hq : Tendsto q (𝓝 (0 : ℂ)) (𝓝 (((2 / Real.sqrt 3 : ℝ) : ℂ))) := by
    have hcont : ContinuousAt q 0 := by
      unfold q motzkinSqrtPlusTaylor
      fun_prop
    simpa [q, motzkinSqrtPlusTaylor] using hcont.tendsto
  have hden : Tendsto (fun u : ℂ => (t u + q u)⁻¹) (𝓝 (0 : ℂ))
      (𝓝 (((((2 / Real.sqrt 3 : ℝ) : ℂ)) +
        (((2 / Real.sqrt 3 : ℝ) : ℂ)))⁻¹)) := by
    refine (ht.add hq).inv₀ ?_
    have hs3 : ((Real.sqrt 3 : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast (Real.sqrt_ne_zero'.mpr (by norm_num : (0 : ℝ) < 3))
    norm_num [Complex.ofReal_div]
  have hdenO : (fun u : ℂ => (t u + q u)⁻¹) =O[𝓝 (0 : ℂ)]
      (fun _ : ℂ => (1 : ℝ)) :=
    tendsto_isBigO_one_complex hden
  have hsqO : (fun u : ℂ => (t u) ^ 2 - (q u) ^ 2) =O[𝓝 (0 : ℂ)]
      (fun u : ℂ => ‖u‖ ^ 3) := by
    have hbase := cubic_mul_continuous_isBigO
      (fun u : ℂ => -(32 + u) / 12288)
      (by fun_prop)
    refine hbase.congr_left ?_
    intro u
    rw [motzkinSqrtPlus_sq_sub_taylor_sq]
    ring
  have hprod := hsqO.mul hdenO
  refine hprod.congr' ?_ ?_
  · have hsum_ne : ∀ᶠ u : ℂ in 𝓝 (0 : ℂ), t u + q u ≠ 0 := by
      have hsum := ht.add hq
      refine hsum.eventually_ne ?_
      have hs3 : ((Real.sqrt 3 : ℝ) : ℂ) ≠ 0 := by
        exact_mod_cast (Real.sqrt_ne_zero'.mpr (by norm_num : (0 : ℝ) < 3))
      norm_num [Complex.ofReal_div]
    filter_upwards [hsum_ne] with u hu
    dsimp [t, q] at hu ⊢
    set a := motzkinSqrtPlus (1 - u)
    set b := motzkinSqrtPlusTaylor u
    rw [show a ^ 2 - b ^ 2 = (a - b) * (a + b) by ring]
    rw [mul_assoc, mul_inv_cancel₀ hu, mul_one]
  · filter_upwards with u
    ring

lemma motzkinAnalyticPart_remainder_isBigO :
    (fun u : ℂ =>
      motzkinAnalyticPart (1 - u) -
        (3 + motzkinAnalyticLinearCoeff * u + motzkinAnalyticQuadraticCoeff * u ^ 2))
      =O[𝓝 (0 : ℂ)] (fun u : ℂ => ‖u‖ ^ 3) := by
  have hbase := cubic_mul_continuous_isBigO
    (fun u : ℂ => ((33 / 2 : ℂ) - 12 * u) / (1 - u) ^ 2)
    (by
      apply ContinuousAt.div
      · fun_prop
      · fun_prop
      · norm_num)
  refine hbase.congr' ?_ (EventuallyEq.refl _ _)
  filter_upwards [eventually_ne_nhds (show (0 : ℂ) ≠ 1 by norm_num)] with u hu
  unfold motzkinAnalyticPart motzkinAnalyticLinearCoeff motzkinAnalyticQuadraticCoeff
  field_simp [sub_ne_zero.mpr (Ne.symm hu)]
  ring

section
end

set_option backward.isDefEq.respectTransparency false in
lemma motzkinSqrtPlusTaylor_sub_BTaylor_isBigO :
    (fun u : ℂ => motzkinSqrtPlusTaylor u - motzkinSqrtPlusBTaylor u)
      =O[𝓝 (0 : ℂ)] (fun u : ℂ => ‖u‖ ^ 3) := by
  have hbase := cubic_mul_continuous_isBigO
    (fun u : ℂ => (((2 / Real.sqrt 3 : ℝ) : ℂ)) *
      ((231 / 64 : ℂ) - (351 / 128 : ℂ) * u))
    (by fun_prop)
  refine hbase.congr_left ?_
  intro u
  unfold motzkinSqrtPlusTaylor motzkinSqrtPlusBTaylor motzkinSingularCoeff
    motzkinSecondSingularCoeff motzkinThirdSingularCoeff motzkinRho
    motzkinSingularSecondDerivAtRho
  have hs3 : ((Real.sqrt 3 : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_ne_zero'.mpr (by norm_num : (0 : ℝ) < 3))
  field_simp [hs3]
  ring_nf
  norm_num [Complex.ofReal_div, Complex.ofReal_mul] at *
  field_simp [hs3]
  ring_nf
  rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
  norm_num
  ring_nf

section
end

set_option backward.isDefEq.respectTransparency false in
lemma motzkinSingularPart_remainder_isBigO :
    (fun u : ℂ =>
      motzkinSingularPart (1 - u) -
        (motzkinSingularCoeff + motzkinSecondSingularCoeff * u +
          motzkinThirdSingularCoeff * u ^ 2))
      =O[𝓝 (0 : ℂ)] (fun u : ℂ => ‖u‖ ^ 3) := by
  have hdiff : (fun u : ℂ => motzkinSqrtPlus (1 - u) - motzkinSqrtPlusBTaylor u)
      =O[𝓝 (0 : ℂ)] (fun u : ℂ => ‖u‖ ^ 3) := by
    have hsum := motzkinSqrtPlus_sub_taylor_isBigO.add
      motzkinSqrtPlusTaylor_sub_BTaylor_isBigO
    refine hsum.congr_left ?_
    intro u
    ring
  have hden_tendsto : Tendsto (fun u : ℂ => ((1 - u) ^ 2)⁻¹) (𝓝 (0 : ℂ)) (𝓝 (1 : ℂ)) := by
    have hcont : ContinuousAt (fun u : ℂ => (1 - u) ^ 2) 0 := by fun_prop
    have hne : ((1 - (0 : ℂ)) ^ 2) ≠ 0 := by norm_num
    convert hcont.tendsto.inv₀ hne using 1
    norm_num
  have hdenO : (fun u : ℂ => ((1 - u) ^ 2)⁻¹) =O[𝓝 (0 : ℂ)]
      (fun _ : ℂ => (1 : ℝ)) :=
    tendsto_isBigO_one_complex hden_tendsto
  have hprod := hdiff.mul hdenO
  have hscaled : (fun u : ℂ =>
      (-(9 / 2 : ℂ)) *
        ((motzkinSqrtPlus (1 - u) - motzkinSqrtPlusBTaylor u) * ((1 - u) ^ 2)⁻¹))
      =O[𝓝 (0 : ℂ)] (fun u : ℂ => ‖u‖ ^ 3) := by
    refine (hprod.const_mul_left (-(9 / 2 : ℂ))).congr_right ?_
    intro u
    ring
  refine hscaled.congr' ?_ (EventuallyEq.refl _ _)
  filter_upwards [eventually_ne_nhds (show (0 : ℂ) ≠ 1 by norm_num)] with u hu
  unfold motzkinSingularPart motzkinSqrtPlusBTaylor
  field_simp [sub_ne_zero.mpr (Ne.symm hu)]
  ring

lemma motzkinSqrtOneSub_local_isBigO :
    (fun u : ℂ => motzkinSqrtOneSub (1 - u)) =O[𝓝 (0 : ℂ)]
      (fun u : ℂ => ‖u‖ ^ (1 / 2 : ℝ)) := by
  refine IsBigO.of_bound 1 ?_
  filter_upwards with u
  unfold motzkinSqrtOneSub
  rw [show (1 : ℂ) - (1 - u) = u by ring]
  rw [show (1 / 2 : ℂ) = (((1 / 2 : ℝ) : ℂ)) by norm_num]
  rw [Complex.norm_cpow_real u (1 / 2 : ℝ)]
  rw [Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg u) _)]
  simp

lemma motzkinThird_local_residual_eq {u : ℂ} (hu1 : u ≠ 1) :
    sqrtAdjustedFun motzkinThirdAdjustedRescaledFun 3 (-motzkinAnalyticLinearCoeff) (1 - u) -
        motzkinSingularCoeff * u ^ (1 / 2 : ℂ) -
        motzkinSecondSingularCoeff * u ^ (3 / 2 : ℂ) -
        motzkinThirdSingularCoeff * u ^ (5 / 2 : ℂ) =
      (motzkinAnalyticPart (1 - u) -
        (3 + motzkinAnalyticLinearCoeff * u + motzkinAnalyticQuadraticCoeff * u ^ 2)) +
        (motzkinSingularPart (1 - u) -
          (motzkinSingularCoeff + motzkinSecondSingularCoeff * u +
            motzkinThirdSingularCoeff * u ^ 2)) *
          motzkinSqrtOneSub (1 - u) := by
  have hz_ne : (1 : ℂ) - u ≠ 0 := sub_ne_zero.mpr (Ne.symm hu1)
  have hdecomp := motzkinRescaledFun_decomp (z := 1 - u) hz_ne
  have hs : motzkinSqrtOneSub (1 - u) = u ^ (1 / 2 : ℂ) := by
    unfold motzkinSqrtOneSub
    rw [show (1 : ℂ) - (1 - u) = u by ring]
  have hpow3 : u ^ (3 / 2 : ℂ) = u * motzkinSqrtOneSub (1 - u) := by
    by_cases hu0 : u = 0
    · subst u
      norm_num [motzkinSqrtOneSub]
    · rw [hs]
      rw [show (3 / 2 : ℂ) = 1 + (1 / 2 : ℂ) by norm_num]
      rw [Complex.cpow_add _ _ hu0, Complex.cpow_one]
  have hpow5 : u ^ (5 / 2 : ℂ) = u ^ 2 * motzkinSqrtOneSub (1 - u) := by
    by_cases hu0 : u = 0
    · subst u
      norm_num [motzkinSqrtOneSub]
    · rw [hs]
      rw [show (5 / 2 : ℂ) = 2 + (1 / 2 : ℂ) by norm_num]
      rw [Complex.cpow_add _ _ hu0]
      norm_num [Complex.cpow_natCast]
  unfold sqrtAdjustedFun sqrtLinearAtOneFun motzkinThirdAdjustedRescaledFun
  rw [hdecomp, hpow3, hpow5, hs]
  ring

lemma motzkinThird_local_residual_isLittleO :
    (fun u : ℂ =>
      sqrtAdjustedFun motzkinThirdAdjustedRescaledFun 3 (-motzkinAnalyticLinearCoeff) (1 - u) -
          motzkinSingularCoeff * u ^ (1 / 2 : ℂ) -
          motzkinSecondSingularCoeff * u ^ (3 / 2 : ℂ) -
          motzkinThirdSingularCoeff * u ^ (5 / 2 : ℂ))
      =o[𝓝 (0 : ℂ)] (fun u : ℂ => ‖u‖ ^ (5 / 2 : ℝ)) := by
  have hA := motzkinAnalyticPart_remainder_isBigO.trans_isLittleO
    norm_pow_three_isLittleO_norm_rpow_five_halves
  have hBbig := motzkinSingularPart_remainder_isBigO.mul
    motzkinSqrtOneSub_local_isBigO
  have hB := hBbig.trans_isLittleO
    norm_pow_three_mul_rpow_half_isLittleO_norm_rpow_five_halves
  have hsum := hA.add hB
  refine hsum.congr' ?_ (EventuallyEq.refl _ _)
  filter_upwards [eventually_ne_nhds (show (0 : ℂ) ≠ 1 by norm_num)] with u hu1
  simpa using (motzkinThird_local_residual_eq (u := u) hu1).symm

lemma tendsto_motzkinThirdAdjustedRescaledFun_singularity :
    Tendsto
      (fun z : ℂ =>
        ‖sqrtAdjustedFun motzkinThirdAdjustedRescaledFun 3 (-motzkinAnalyticLinearCoeff) z -
            motzkinSingularCoeff * (1 - z) ^ (1 / 2 : ℂ) -
            motzkinSecondSingularCoeff * (1 - z) ^ (3 / 2 : ℂ) -
            motzkinThirdSingularCoeff * (1 - z) ^ (5 / 2 : ℂ)‖ *
          ‖(1 : ℂ) - z‖ ^ (-(5 / 2 : ℝ)))
      (𝓝[DeltaDomainArg (3 / 2) (Real.pi / 4)] (1 : ℂ)) (𝓝 0) := by
  let l := 𝓝[DeltaDomainArg (3 / 2) (Real.pi / 4)] (1 : ℂ)
  have hu : Tendsto (fun z : ℂ => 1 - z) l (𝓝 (0 : ℂ)) := by
    have hcont : ContinuousAt (fun z : ℂ => 1 - z) 1 := by fun_prop
    simpa using Tendsto.mono_left hcont.tendsto nhdsWithin_le_nhds
  have hcomp := motzkinThird_local_residual_isLittleO.comp_tendsto hu
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

lemma motzkinSecondSingularCoeff_eq_meta :
    motzkinSecondSingularCoeff =
      -(((motzkinRho : ℝ) : ℂ) * motzkinSingularDerivAtRho) := by
  unfold motzkinSecondSingularCoeff motzkinRho motzkinSingularDerivAtRho
  norm_num [Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_neg]
  ring

lemma motzkinThirdAsymptoticConstant_eq_meta :
    sqrtSingularityC2 motzkinRho motzkinSingularCoeff
        motzkinSingularDerivAtRho motzkinSingularSecondDerivAtRho =
      ((motzkinThirdAsymptoticConstant : ℝ) : ℂ) := by
  unfold sqrtSingularityC2 sqrtSingularityC2Rescaled motzkinRho motzkinSingularCoeff
    motzkinSingularDerivAtRho motzkinSingularSecondDerivAtRho
    motzkinThirdAsymptoticConstant
  norm_num [Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_neg]
  ring

lemma motzkinFirstAsymptoticConstant_eq_meta :
    sqrtSingularityC0 motzkinSingularCoeff =
      ((motzkinAsymptoticConstant : ℝ) : ℂ) := by
  unfold sqrtSingularityC0 motzkinSingularCoeff motzkinAsymptoticConstant
  norm_num [Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_neg]

lemma motzkinSecondAsymptoticConstant_eq_meta :
    sqrtSingularityC1 motzkinRho motzkinSingularCoeff motzkinSingularDerivAtRho =
      ((motzkinSecondAsymptoticConstant : ℝ) : ℂ) := by
  unfold sqrtSingularityC1 sqrtSingularityC1Rescaled motzkinRho motzkinSingularCoeff
    motzkinSingularDerivAtRho motzkinSecondAsymptoticConstant
  norm_num [Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_neg]
  ring

lemma motzkinSingularCoeff_ne_zero : motzkinSingularCoeff ≠ 0 := by
  unfold motzkinSingularCoeff
  norm_num

theorem motzkinThirdOriginalSeries_complex_meta :
    (fun n : ℕ =>
      PowerSeries.coeff (R := ℂ) n motzkinThirdOriginalSeriesℂ -
        (((((motzkinRho : ℝ) : ℂ)⁻¹) ^ n) *
          (sqrtSingularityC0 motzkinSingularCoeff *
              (((n : ℝ) ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ) +
            sqrtSingularityC1 motzkinRho motzkinSingularCoeff motzkinSingularDerivAtRho *
              (((n : ℝ) ^ (-(5 / 2 : ℝ)) : ℝ) : ℂ) +
            sqrtSingularityC2 motzkinRho motzkinSingularCoeff
                motzkinSingularDerivAtRho motzkinSingularSecondDerivAtRho *
              (((n : ℝ) ^ (-(7 / 2 : ℝ)) : ℝ) : ℂ))))
      =o[atTop]
        (fun n : ℕ =>
          ‖(((((motzkinRho : ℝ) : ℂ)⁻¹) ^ n) *
            (((n : ℝ) ^ (-(7 / 2 : ℝ)) : ℝ) : ℂ))‖) := by
  refine sqrt_singularity_thirdOrder_original_of_rescaled_singularity
    (ρ := motzkinRho) (R := (3 / 2 : ℝ)) (φ := Real.pi / 4)
    (F := motzkinThirdOriginalFun) (P := motzkinThirdOriginalSeriesℂ)
    (A0 := 3) (A1 := -motzkinAnalyticLinearCoeff)
    (Bρ := motzkinSingularCoeff)
    (Bderivρ := motzkinSingularDerivAtRho)
    (Bsecondρ := motzkinSingularSecondDerivAtRho)
    ?_ motzkinSingularCoeff_ne_zero ?_ ?_ ?_
    motzkinThirdOriginalFun_rescaled_hasFPowerSeriesAt_zero
    analyticOnNhd_motzkinThirdOriginalFun_rescaled ?_
  · unfold motzkinRho
    norm_num
  · norm_num
  · positivity
  · nlinarith [Real.pi_pos]
  · have h := tendsto_motzkinThirdAdjustedRescaledFun_singularity
    have hrescale : ∀ w : ℂ,
        motzkinThirdOriginalFun (((motzkinRho : ℝ) : ℂ) * w) =
          motzkinThirdAdjustedRescaledFun w :=
      motzkinThirdOriginalFun_rescale
    have hrescale3 : ∀ w : ℂ,
        motzkinThirdOriginalFun ((3 : ℂ)⁻¹ * w) =
          motzkinThirdAdjustedRescaledFun w := by
      intro w
      have hρ : (((motzkinRho : ℝ) : ℂ)) = (3 : ℂ)⁻¹ := by
        unfold motzkinRho
        norm_num
      rw [← hρ]
      exact hrescale w
    refine h.congr' ?_
    filter_upwards with z
    simp [sqrtAdjustedFun, hrescale, motzkinSecondSingularCoeff_eq_meta,
      motzkinThirdSingularCoeff]

section
end

set_option backward.isDefEq.respectTransparency false in
lemma motzkinOneSubThreeXSeries_sq_coeff_of_three_le {n : ℕ} (hn : 3 ≤ n) :
    PowerSeries.coeff (R := ℂ) n (motzkinOneSubThreeXSeriesℂ ^ 2) = 0 := by
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
  · have hcoeff : PowerSeries.coeff (R := ℂ) i motzkinOneSubThreeXSeriesℂ = 0 := by
      unfold motzkinOneSubThreeXSeriesℂ
      simp [PowerSeries.coeff_X,
        ne_of_gt (lt_of_lt_of_le (by norm_num : 0 < 2) hi),
        ne_of_gt (lt_of_lt_of_le (by norm_num : 1 < 2) hi)]
    simp [hcoeff]
  · have hcoeff : PowerSeries.coeff (R := ℂ) j motzkinOneSubThreeXSeriesℂ = 0 := by
      unfold motzkinOneSubThreeXSeriesℂ
      simp [PowerSeries.coeff_X,
        ne_of_gt (lt_of_lt_of_le (by norm_num : 0 < 2) hj),
        ne_of_gt (lt_of_lt_of_le (by norm_num : 1 < 2) hj)]
    simp [hcoeff]

lemma coeff_motzkinThirdOriginalSeriesℂ_of_three_le {n : ℕ} (hn : 3 ≤ n) :
    PowerSeries.coeff (R := ℂ) n motzkinThirdOriginalSeriesℂ = (motzkin n : ℂ) := by
  unfold motzkinThirdOriginalSeriesℂ
  simp [PowerSeries.coeff_C_mul, motzkinOneSubThreeXSeries_sq_coeff_of_three_le hn]

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
theorem motzkin_complex_thirdOrder_additive :
    (fun n : ℕ =>
      (motzkin n : ℂ) -
        (((((3 : ℝ) ^ n) *
          (motzkinAsymptoticConstant * (n : ℝ) ^ (-(3 / 2 : ℝ)) +
            motzkinSecondAsymptoticConstant * (n : ℝ) ^ (-(5 / 2 : ℝ)) +
            motzkinThirdAsymptoticConstant * (n : ℝ) ^ (-(7 / 2 : ℝ))) : ℝ) : ℂ)))
      =o[atTop]
        (fun n : ℕ => (3 : ℝ) ^ n * (n : ℝ) ^ (-(7 / 2 : ℝ))) := by
  have h := motzkinThirdOriginalSeries_complex_meta
  refine h.congr' ?_ ?_
  · filter_upwards [eventually_ge_atTop 3] with n hn
    rw [coeff_motzkinThirdOriginalSeriesℂ_of_three_le hn]
    rw [motzkinFirstAsymptoticConstant_eq_meta,
      motzkinSecondAsymptoticConstant_eq_meta,
      motzkinThirdAsymptoticConstant_eq_meta]
    have hρ : (((motzkinRho : ℝ) : ℂ)⁻¹) ^ n = (((3 : ℝ) ^ n : ℝ) : ℂ) := by
      have hbase : (((motzkinRho : ℝ) : ℂ)⁻¹) = ((3 : ℝ) : ℂ) := by
        unfold motzkinRho
        norm_num
      rw [hbase, Complex.ofReal_pow]
    rw [hρ]
    norm_num [Complex.ofReal_mul, Complex.ofReal_add]
  · filter_upwards [eventually_ge_atTop 1] with n hn
    have hnpos : 0 < (n : ℝ) := by
      exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < (1 : ℕ)) hn)
    have hρ : (((motzkinRho : ℝ) : ℂ)⁻¹) ^ n = (((3 : ℝ) ^ n : ℝ) : ℂ) := by
      have hbase : (((motzkinRho : ℝ) : ℂ)⁻¹) = ((3 : ℝ) : ℂ) := by
        unfold motzkinRho
        norm_num
      rw [hbase, Complex.ofReal_pow]
    rw [hρ, norm_mul, Complex.norm_real, Complex.norm_real]
    rw [Real.norm_of_nonneg (by positivity : 0 ≤ (3 : ℝ) ^ n)]
    rw [Real.norm_of_nonneg (Real.rpow_nonneg (le_of_lt hnpos) _)]

theorem motzkin_thirdOrder_additive :
    (fun n : ℕ =>
      (motzkin n : ℝ) -
        (3 : ℝ) ^ n *
          (motzkinAsymptoticConstant * (n : ℝ) ^ (-(3 / 2 : ℝ)) +
            motzkinSecondAsymptoticConstant * (n : ℝ) ^ (-(5 / 2 : ℝ)) +
            motzkinThirdAsymptoticConstant * (n : ℝ) ^ (-(7 / 2 : ℝ))))
      =o[atTop]
        (fun n : ℕ => (3 : ℝ) ^ n * (n : ℝ) ^ (-(7 / 2 : ℝ))) := by
  have hcomplex :
      (fun n : ℕ =>
        (((motzkin n : ℝ) : ℂ) -
          ((((3 : ℝ) ^ n *
            (motzkinAsymptoticConstant * (n : ℝ) ^ (-(3 / 2 : ℝ)) +
              motzkinSecondAsymptoticConstant * (n : ℝ) ^ (-(5 / 2 : ℝ)) +
              motzkinThirdAsymptoticConstant * (n : ℝ) ^ (-(7 / 2 : ℝ))) : ℝ) : ℂ))))
        =o[atTop]
          (fun n : ℕ => (3 : ℝ) ^ n * (n : ℝ) ^ (-(7 / 2 : ℝ))) := by
    simpa [Complex.ofReal_mul, Complex.ofReal_add] using motzkin_complex_thirdOrder_additive
  have hreal := complex_re_isLittleO_ofReal hcomplex
  simpa using hreal

lemma motzkinThirdAsymptoticConstant_eq_relative :
    motzkinThirdAsymptoticConstant =
      motzkinAsymptoticConstant * motzkinRelativeThirdConstant := by
  unfold motzkinThirdAsymptoticConstant motzkinAsymptoticConstant
    motzkinRelativeThirdConstant
  ring

end

set_option maxHeartbeats 1200000
open Complex Filter Asymptotics Set
open scoped Topology BigOperators PowerSeries
theorem solution :
    (fun n : ℕ =>
      (motzkin n : ℝ) -
        (3 : ℝ) ^ n * motzkinAsymptoticConstant *
          (n : ℝ) ^ (-(3 / 2 : ℝ)) *
          (1 + motzkinRelativeSecondConstant * (n : ℝ) ^ (-(1 : ℝ)) +
            motzkinRelativeThirdConstant * (n : ℝ) ^ (-(2 : ℝ))))
      =o[atTop]
        (fun n : ℕ => (3 : ℝ) ^ n * (n : ℝ) ^ (-(7 / 2 : ℝ))) := by
  refine motzkin_thirdOrder_additive.congr' ?_ (EventuallyEq.refl _ _)
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
  rw [motzkinSecondAsymptoticConstant_eq_relative,
    motzkinThirdAsymptoticConstant_eq_relative, hpow5, hpow7]
  ring
