-- Prove2me | solution 1 for schroeder_complex_thirdOrder
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-10-28T12:32:14.949568+00:00
-- url     : https://prove2.me/submissions/b0cdabca-78bf-4f9a-b88e-89aea3b62c56

import Definitions.Def_AnalyticCombinatorics_Ch4_Analytic_Bridge
import Definitions.Def_AnalyticCombinatorics_Ch4_Analytic_DeltaDomain
import Definitions.Def_AnalyticCombinatorics_Ch4_Analytic_SqrtSingularitySecondOrder
import Definitions.Def_AnalyticCombinatorics_Ch4_Analytic_SqrtSingularityThirdOrder
import Definitions.Def_AnalyticCombinatorics_Ch7_SingularityApp_Motzkin
import Definitions.Def_AnalyticCombinatorics_Ch7_SingularityApp_Schroeder
import Definitions.Def_AnalyticCombinatorics_Ch7_SingularityApp_SchroederSecondOrder
import Definitions.Def_AnalyticCombinatorics_Ch7_SingularityApp_SchroederThirdOrder
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

@[simp] lemma coeff_motzkinRescaledSeriesℂ (n : ℕ) :
    PowerSeries.coeff (R := ℂ) n motzkinRescaledSeriesℂ =
      (motzkin n : ℂ) * ((3 : ℂ)⁻¹) ^ n := by
  simp [motzkinRescaledSeriesℂ, PowerSeries.coeff_rescale, mul_comm]

lemma Complex_cpow_half_sq (z : ℂ) : (z ^ (1 / 2 : ℂ)) ^ 2 = z := by
  rw [show (1 / 2 : ℂ) = (2⁻¹ : ℂ) by norm_num]
  exact Complex.cpow_nat_inv_pow z (n := 2) (by norm_num)

lemma analyticOnNhd_motzkin_sqrt_one_sub :
    AnalyticOnNhd ℂ motzkinSqrtOneSub
      (DeltaDomainArg (3 / 2) (Real.pi / 4)) := by
  have h := analyticOnNhd_one_sub_cpow_deltaDomain (α := (-1 / 2 : ℂ))
    (R := (3 / 2 : ℝ)) (φ := Real.pi / 4) (by positivity) (by nlinarith [Real.pi_pos])
  convert h using 1
  ext z
  norm_num [motzkinSqrtOneSub]

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

end
end

section
/-!
# Large Schroeder-number asymptotic

This file proves the square-root singularity asymptotic for the large
Schroeder numbers with OGF
`S(z) = (1 - z - sqrt (1 - 6 z + z^2)) / (2 z)`.
-/

open Complex Filter Asymptotics
open scoped BigOperators PowerSeries Topology

noncomputable section

@[simp] lemma schroeder_zero : schroeder 0 = 1 := by
  simp [schroeder]

@[simp] lemma schroeder_succ (n : ℕ) :
    schroeder (n + 1) =
      schroeder n + ∑ k : Fin (n + 1), schroeder k * schroeder (n - k) := by
  simp [schroeder]

/-- Exponential growth base, the reciprocal of `schroederRho`. -/
def schroederGrowthBase : ℝ := 3 + 2 * Real.sqrt 2

lemma schroeder_rho_mul_growthBase :
    schroederRho * schroederGrowthBase = 1 := by
  rw [schroederRho, schroederGrowthBase]
  ring_nf
  rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  norm_num

lemma schroederGrowthBase_pos : 0 < schroederGrowthBase := by
  rw [schroederGrowthBase]
  positivity

lemma schroederGrowthBase_gt_one : 1 < schroederGrowthBase := by
  rw [schroederGrowthBase]
  have hsqrt_nonneg : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  nlinarith

lemma schroederRho_pos : 0 < schroederRho := by
  have hmul := schroeder_rho_mul_growthBase
  have hg := schroederGrowthBase_pos
  nlinarith

lemma schroederRho_ne_zero : schroederRho ≠ 0 :=
  ne_of_gt schroederRho_pos

lemma schroederRho_lt_one : schroederRho < 1 := by
  have hmul := schroeder_rho_mul_growthBase
  have hg := schroederGrowthBase_gt_one
  have hρpos := schroederRho_pos
  nlinarith

lemma schroederRho_nonneg : 0 ≤ schroederRho :=
  le_of_lt schroederRho_pos

lemma one_sub_schroederRho_pos : 0 < 1 - schroederRho := by
  linarith [schroederRho_lt_one]

lemma one_sub_schroederRho_ne_zero : (1 - schroederRho : ℝ) ≠ 0 :=
  ne_of_gt one_sub_schroederRho_pos

lemma one_sub_schroederRho_ne_zeroℂ :
    (((1 - schroederRho : ℝ) : ℂ)) ≠ 0 := by
  exact_mod_cast one_sub_schroederRho_ne_zero

section
end

set_option backward.isDefEq.respectTransparency false in
lemma one_sub_schroederRho_sq :
    (1 - schroederRho) ^ 2 = 4 * schroederRho := by
  rw [schroederRho]
  ring_nf
  rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  ring

lemma one_sub_schroederRho_sq_pos : 0 < 1 - schroederRho ^ 2 := by
  nlinarith [schroederRho_pos, schroederRho_lt_one]

lemma one_sub_schroederRho_sq_nonneg : 0 ≤ 1 - schroederRho ^ 2 :=
  le_of_lt one_sub_schroederRho_sq_pos

lemma schroederRho_sq_mul_three_halves_lt_one :
    schroederRho ^ 2 * (3 / 2 : ℝ) < 1 := by
  have hρpos := schroederRho_pos
  have hρlt : schroederRho < 1 / 2 := by
    rw [schroederRho]
    have hsqrt_gt : (5 / 4 : ℝ) < Real.sqrt 2 := by
      rw [Real.lt_sqrt (by norm_num : (0 : ℝ) ≤ 5 / 4)]
      norm_num
    nlinarith
  nlinarith

/-- The ordinary generating function as a formal power series over `ℂ`. -/
def schroederSeriesℂ : PowerSeries ℂ :=
  PowerSeries.mk fun n => (schroeder n : ℂ)

@[simp] lemma coeff_schroederSeriesℂ (n : ℕ) :
    PowerSeries.coeff (R := ℂ) n schroederSeriesℂ = (schroeder n : ℂ) := by
  simp [schroederSeriesℂ]

@[simp] lemma constantCoeff_schroederSeriesℂ :
    PowerSeries.constantCoeff schroederSeriesℂ = 1 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
  simp

lemma coeff_X_mul_schroederSeriesℂ (n : ℕ) :
    PowerSeries.coeff (R := ℂ) (n + 1) (PowerSeries.X * schroederSeriesℂ) =
      (schroeder n : ℂ) := by
  simp

section
end

set_option backward.isDefEq.respectTransparency false in
lemma coeff_schroederSeriesℂ_sq (n : ℕ) :
    PowerSeries.coeff (R := ℂ) n (schroederSeriesℂ ^ 2) =
      ∑ k : Fin (n + 1), (schroeder k : ℂ) * (schroeder (n - k) : ℂ) := by
  rw [pow_two, PowerSeries.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun x y => PowerSeries.coeff (R := ℂ) x schroederSeriesℂ *
      PowerSeries.coeff (R := ℂ) y schroederSeriesℂ) n]
  rw [Finset.sum_fin_eq_sum_range]
  apply Finset.sum_congr rfl
  intro x hx
  have hxle : x ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hx)
  simp [hxle]

lemma coeff_X_mul_schroederSeriesℂ_sq (n : ℕ) :
    PowerSeries.coeff (R := ℂ) (n + 1)
        (PowerSeries.X * schroederSeriesℂ ^ 2) =
      ∑ k : Fin (n + 1), (schroeder k : ℂ) * (schroeder (n - k) : ℂ) := by
  rw [← coeff_schroederSeriesℂ_sq n]
  simp

/-- The Schroeder OGF satisfies `S = 1 + X S + X S^2`. -/
theorem schroederSeriesℂ_eq_one_add_X_mul_add_X_mul_sq :
    schroederSeriesℂ =
      1 + PowerSeries.X * schroederSeriesℂ +
        PowerSeries.X * schroederSeriesℂ ^ 2 := by
  ext n
  cases n with
  | zero =>
      simp
  | succ n =>
      simp only [coeff_schroederSeriesℂ, map_add, PowerSeries.coeff_one, Nat.succ_ne_zero,
        ↓reduceIte, zero_add]
      rw [coeff_X_mul_schroederSeriesℂ, coeff_X_mul_schroederSeriesℂ_sq]
      norm_num [schroeder_succ]

/-- The rescaled series `S(rho z)`. -/
def schroederRescaledSeriesℂ : PowerSeries ℂ :=
  PowerSeries.rescale ((schroederRho : ℝ) : ℂ) schroederSeriesℂ

@[simp] lemma coeff_schroederRescaledSeriesℂ (n : ℕ) :
    PowerSeries.coeff (R := ℂ) n schroederRescaledSeriesℂ =
      (schroeder n : ℂ) * (((schroederRho : ℝ) : ℂ)) ^ n := by
  simp [schroederRescaledSeriesℂ, PowerSeries.coeff_rescale, mul_comm]

/-- The formal substitution variable `rho z`. -/
def schroederScaleX : PowerSeries ℂ :=
  PowerSeries.C (((schroederRho : ℝ) : ℂ)) * PowerSeries.X

lemma schroederRescaledSeriesℂ_quadratic :
    schroederRescaledSeriesℂ =
      1 + schroederScaleX * schroederRescaledSeriesℂ +
        schroederScaleX * schroederRescaledSeriesℂ ^ 2 := by
  change PowerSeries.rescale (((schroederRho : ℝ) : ℂ)) schroederSeriesℂ =
    1 + schroederScaleX * schroederRescaledSeriesℂ +
      schroederScaleX * schroederRescaledSeriesℂ ^ 2
  rw [schroederSeriesℂ_eq_one_add_X_mul_add_X_mul_sq]
  simp only [map_add, map_mul, map_one, map_pow, PowerSeries.rescale_X]
  simp [schroederRescaledSeriesℂ, schroederScaleX, pow_two, mul_assoc]

def schroederSqrtRegular (z : ℂ) : ℂ :=
  (1 - schroederRhoℂ ^ 2 * z) ^ (1 / 2 : ℂ)

def schroederSqrtOneSub (z : ℂ) : ℂ :=
  (1 - z) ^ (1 / 2 : ℂ)

/-- Denominator of the explicit rescaled Schroeder OGF. -/
def schroederRescaledDenominator (z : ℂ) : ℂ :=
  1 - schroederRhoℂ * z + schroederSqrtRegular z * schroederSqrtOneSub z

/-- The explicit analytic branch of `S(rho z)`. -/
def schroederRescaledFun (z : ℂ) : ℂ :=
  2 / schroederRescaledDenominator z

def schroederRegularValueℂ : ℂ :=
  2 / schroederOneSubRhoℂ

lemma schroederSqrtOneSub_sq (z : ℂ) : schroederSqrtOneSub z ^ 2 = 1 - z := by
  rw [schroederSqrtOneSub, Complex_cpow_half_sq]

lemma schroederSqrtRegular_sq (z : ℂ) :
    schroederSqrtRegular z ^ 2 = 1 - schroederRhoℂ ^ 2 * z := by
  rw [schroederSqrtRegular, Complex_cpow_half_sq]

lemma schroeder_one_sub_rho_sq_complex :
    (1 - schroederRhoℂ) ^ 2 = 4 * schroederRhoℂ := by
  unfold schroederRhoℂ
  rw [← Complex.ofReal_one, ← Complex.ofReal_sub, ← Complex.ofReal_pow,
    ← Complex.ofReal_ofNat, ← Complex.ofReal_mul]
  exact_mod_cast one_sub_schroederRho_sq

section
end

set_option backward.isDefEq.respectTransparency false in
lemma schroederRescaledDenominator_ne_zero (z : ℂ) :
    schroederRescaledDenominator z ≠ 0 := by
  intro h
  have hmul :
      schroederSqrtRegular z * schroederSqrtOneSub z =
        schroederRhoℂ * z - 1 := by
    have h' := h
    unfold schroederRescaledDenominator at h'
    linear_combination h'
  have hsq := congrArg (fun w : ℂ => w ^ 2) hmul
  change (schroederSqrtRegular z * schroederSqrtOneSub z) ^ 2 =
    (schroederRhoℂ * z - 1) ^ 2 at hsq
  rw [mul_pow, schroederSqrtRegular_sq, schroederSqrtOneSub_sq] at hsq
  have hzprod : (1 - schroederRhoℂ) ^ 2 * z = 0 := by
    calc
      (1 - schroederRhoℂ) ^ 2 * z =
          (schroederRhoℂ * z - 1) ^ 2 -
            (1 - schroederRhoℂ ^ 2 * z) * (1 - z) := by ring
      _ = 0 := by
        rw [← hsq]
        ring
  have hone : (1 - schroederRhoℂ) ^ 2 ≠ 0 := by
    apply pow_ne_zero
    intro hzero
    have hreal : (1 - schroederRho : ℝ) = 0 := by
      apply Complex.ofReal_injective
      simpa [schroederRhoℂ, Complex.ofReal_sub] using hzero
    exact one_sub_schroederRho_ne_zero hreal
  have hz : z = 0 := by
    exact eq_zero_of_ne_zero_of_mul_left_eq_zero hone hzprod
  subst z
  norm_num [schroederRescaledDenominator, schroederSqrtRegular, schroederSqrtOneSub,
    schroederRhoℂ] at h

lemma schroederRescaledFun_quadratic (z : ℂ) :
    schroederRescaledFun z =
      1 + (schroederRhoℂ * z) * schroederRescaledFun z +
        (schroederRhoℂ * z) * schroederRescaledFun z ^ 2 := by
  unfold schroederRescaledFun
  field_simp [schroederRescaledDenominator_ne_zero z]
  unfold schroederRescaledDenominator schroederSqrtRegular schroederSqrtOneSub
  ring_nf
  rw [Complex_cpow_half_sq, Complex_cpow_half_sq]
  have hsq := schroeder_one_sub_rho_sq_complex
  ring_nf at hsq ⊢
  linear_combination z * hsq

lemma one_sub_rho_sq_mul_mem_slitPlane_of_norm_lt_three_halves {z : ℂ}
    (hz : ‖z‖ < (3 / 2 : ℝ)) :
    1 - schroederRhoℂ ^ 2 * z ∈ Complex.slitPlane := by
  refine Or.inl ?_
  let w : ℂ := schroederRhoℂ ^ 2 * z
  have hnormρ : ‖schroederRhoℂ ^ 2‖ = schroederRho ^ 2 := by
    rw [norm_pow, schroederRhoℂ]
    simp [Real.norm_of_nonneg schroederRho_nonneg]
  have hw_norm : ‖w‖ < 1 := by
    have hz_nonneg : 0 ≤ ‖z‖ := norm_nonneg z
    have hρsq_nonneg : 0 ≤ schroederRho ^ 2 := sq_nonneg schroederRho
    change ‖schroederRhoℂ ^ 2 * z‖ < 1
    rw [norm_mul, hnormρ]
    nlinarith [hz, schroederRho_sq_mul_three_halves_lt_one]
  have hre_le : w.re ≤ ‖w‖ := (abs_le.mp (Complex.abs_re_le_norm w)).2
  change 0 < (1 - schroederRhoℂ ^ 2 * z).re
  rw [show schroederRhoℂ ^ 2 * z = w by rfl, Complex.sub_re, Complex.one_re]
  linarith

lemma analyticOnNhd_schroeder_sqrt_regular :
    AnalyticOnNhd ℂ schroederSqrtRegular
      (DeltaDomainArg (3 / 2) (Real.pi / 4)) := by
  have hbase : AnalyticOnNhd ℂ (fun z : ℂ => 1 - schroederRhoℂ ^ 2 * z)
      (DeltaDomainArg (3 / 2) (Real.pi / 4)) := by
    exact analyticOnNhd_const.sub (analyticOnNhd_const.mul analyticOnNhd_id)
  convert hbase.cpow analyticOnNhd_const (fun z hz => by
    exact one_sub_rho_sq_mul_mem_slitPlane_of_norm_lt_three_halves hz.1) using 1

lemma analyticOnNhd_schroeder_sqrt_one_sub :
    AnalyticOnNhd ℂ schroederSqrtOneSub
      (DeltaDomainArg (3 / 2) (Real.pi / 4)) := by
  simpa [schroederSqrtOneSub, motzkinSqrtOneSub] using
    analyticOnNhd_motzkin_sqrt_one_sub

lemma analyticOnNhd_schroederRescaledDenominator :
    AnalyticOnNhd ℂ schroederRescaledDenominator
      (DeltaDomainArg (3 / 2) (Real.pi / 4)) := by
  have hlinear : AnalyticOnNhd ℂ (fun z : ℂ => 1 - schroederRhoℂ * z)
      (DeltaDomainArg (3 / 2) (Real.pi / 4)) := by
    exact analyticOnNhd_const.sub (analyticOnNhd_const.mul analyticOnNhd_id)
  convert hlinear.add
    (analyticOnNhd_schroeder_sqrt_regular.mul analyticOnNhd_schroeder_sqrt_one_sub) using 1

lemma analyticOnNhd_schroederRescaledFun :
    AnalyticOnNhd ℂ schroederRescaledFun
      (DeltaDomainArg (3 / 2) (Real.pi / 4)) := by
  simpa [schroederRescaledFun] using
    (analyticOnNhd_const.div analyticOnNhd_schroederRescaledDenominator
      (fun z _hz => schroederRescaledDenominator_ne_zero z))

lemma Complex_cpow_one_sub_schroederRho_sq_half :
    (((1 - schroederRho ^ 2 : ℝ) : ℂ) ^ (1 / 2 : ℂ)) =
      schroederSqrtRegularAtOneℂ := by
  unfold schroederSqrtRegularAtOneℂ
  convert (show (((1 - schroederRho ^ 2 : ℝ) : ℂ) ^ ((1 / 2 : ℝ) : ℂ)) =
      ((Real.sqrt (1 - schroederRho ^ 2) : ℝ) : ℂ) by
    rw [← Complex.ofReal_cpow one_sub_schroederRho_sq_nonneg (1 / 2 : ℝ)]
    congr
    rw [← Real.sqrt_eq_rpow]) using 2
  norm_num

section
end

set_option backward.isDefEq.respectTransparency false in
lemma coeff_schroederScaleX_mul_succ (P : PowerSeries ℂ) (n : ℕ) :
    PowerSeries.coeff (R := ℂ) (n + 1) (schroederScaleX * P) =
      schroederRhoℂ * PowerSeries.coeff (R := ℂ) n P := by
  rw [schroederScaleX, schroederRhoℂ, mul_assoc, PowerSeries.coeff_C_mul]
  simp

section
end

set_option backward.isDefEq.respectTransparency false in
lemma coeff_schroederScaleX_mul_sq_succ_congr {P Q : PowerSeries ℂ} {n : ℕ}
    (h : ∀ k ≤ n, PowerSeries.coeff (R := ℂ) k P =
      PowerSeries.coeff (R := ℂ) k Q) :
    PowerSeries.coeff (R := ℂ) (n + 1) (schroederScaleX * P ^ 2) =
      PowerSeries.coeff (R := ℂ) (n + 1) (schroederScaleX * Q ^ 2) := by
  rw [coeff_schroederScaleX_mul_succ, coeff_schroederScaleX_mul_succ]
  congr 1
  rw [pow_two, pow_two, PowerSeries.coeff_mul, PowerSeries.coeff_mul]
  apply Finset.sum_congr rfl
  intro kl hkl
  have hsum : kl.1 + kl.2 = n := Finset.mem_antidiagonal.mp hkl
  have h1 : kl.1 ≤ n := by omega
  have h2 : kl.2 ≤ n := by omega
  simp [h kl.1 h1, h kl.2 h2]

lemma schroeder_quadratic_solution_unique {P Q : PowerSeries ℂ}
    (hP : P = 1 + schroederScaleX * P + schroederScaleX * P ^ 2)
    (hQ : Q = 1 + schroederScaleX * Q + schroederScaleX * Q ^ 2) :
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
          simp [schroederScaleX] at hp hq
          simp [PowerSeries.coeff_zero_eq_constantCoeff_apply, hp, hq]
      | succ n =>
          have hp := congrArg (fun S : PowerSeries ℂ =>
            PowerSeries.coeff (R := ℂ) (n + 1) S) hP
          have hq := congrArg (fun S : PowerSeries ℂ =>
            PowerSeries.coeff (R := ℂ) (n + 1) S) hQ
          simp only [map_add] at hp hq
          rw [hp, hq]
          congr 1
          · rw [coeff_schroederScaleX_mul_succ, coeff_schroederScaleX_mul_succ,
              ih n (Nat.lt_succ_self n)]
          · exact coeff_schroederScaleX_mul_sq_succ_congr
              (fun k hk => ih k (Nat.lt_succ_of_le hk))

theorem schroederRescaledFun_hasFPowerSeriesAt_zero :
    HasFPowerSeriesAt schroederRescaledFun
      (PowerSeries.toFMLS schroederRescaledSeriesℂ) (0 : ℂ) := by
  have han : AnalyticAt ℂ schroederRescaledFun (0 : ℂ) :=
    analyticOnNhd_schroederRescaledFun 0
      (zero_mem_deltaDomainArg (R := (3 / 2 : ℝ)) (φ := Real.pi / 4)
        (by norm_num) (by nlinarith [Real.pi_pos]))
  rcases han with ⟨p, hp⟩
  let P : PowerSeries ℂ := powerSeriesOfFMLSℂ p
  have hPto : PowerSeries.toFMLS P = p := by
    simpa [P] using toFMLS_powerSeriesOfFMLSℂ p
  have hpP : HasFPowerSeriesAt schroederRescaledFun
      (PowerSeries.toFMLS P) (0 : ℂ) := by
    simpa [hPto] using hp
  have hconstScale : HasFPowerSeriesAt (fun _ : ℂ => schroederRhoℂ)
      (PowerSeries.toFMLS (PowerSeries.C schroederRhoℂ)) (0 : ℂ) :=
    hasFPowerSeriesAt_const_toFMLS_C schroederRhoℂ
  have hscale0 := hasFPowerSeriesAt_mul_toFMLS hconstScale
    hasFPowerSeriesAt_id_toFMLS_X
  have hscale : HasFPowerSeriesAt (fun z : ℂ => schroederRhoℂ * z)
      (PowerSeries.toFMLS schroederScaleX) (0 : ℂ) := by
    refine hscale0.congr (Eventually.of_forall ?_)
    intro z
    ring
  have hscaleF := hasFPowerSeriesAt_mul_toFMLS hscale hpP
  have hsquare := hasFPowerSeriesAt_mul_toFMLS hpP hpP
  have hscaleSquare := hasFPowerSeriesAt_mul_toFMLS hscale hsquare
  have hconstOne : HasFPowerSeriesAt (fun _ : ℂ => (1 : ℂ))
      (PowerSeries.toFMLS (1 : PowerSeries ℂ)) (0 : ℂ) := by
    simpa using hasFPowerSeriesAt_const_toFMLS_C (1 : ℂ)
  have hrhs0 := (hconstOne.add hscaleF).add hscaleSquare
  have hrhs : HasFPowerSeriesAt
      (fun z : ℂ =>
        1 + (schroederRhoℂ * z) * schroederRescaledFun z +
          (schroederRhoℂ * z) * schroederRescaledFun z ^ 2)
      (PowerSeries.toFMLS
        (1 + schroederScaleX * P + schroederScaleX * P ^ 2)) (0 : ℂ) := by
    simpa [toFMLS_add, pow_two, add_assoc] using hrhs0
  have hFMLS :
      PowerSeries.toFMLS P =
        PowerSeries.toFMLS
          (1 + schroederScaleX * P + schroederScaleX * P ^ 2) :=
    hpP.eq_formalMultilinearSeries_of_eventually hrhs
      (Eventually.of_forall fun z => schroederRescaledFun_quadratic z)
  have hPquad :
      P = 1 + schroederScaleX * P + schroederScaleX * P ^ 2 :=
    PowerSeries_toFMLS_injective hFMLS
  have hP_eq : P = schroederRescaledSeriesℂ :=
    schroeder_quadratic_solution_unique hPquad schroederRescaledSeriesℂ_quadratic
  simpa [hP_eq] using hpP

end
end

section
/-!
# Second-order large Schroeder asymptotics

This file subtracts the analytic linear term in the centered rescaled
Schroeder OGF and applies `transfer_twoTerm_secondOrder_general` at
`α = -1/2`.
-/

set_option maxHeartbeats 1200000

open Complex Filter Asymptotics Set
open scoped Topology BigOperators PowerSeries

noncomputable section

def schroederAnalyticLinearCoeff : ℂ :=
  2 / schroederOneSubRhoℂ ^ 2

def schroederOneSubSeriesℂ : PowerSeries ℂ :=
  (1 : PowerSeries ℂ) - PowerSeries.X

lemma hasFPowerSeriesAt_schroederOneSub_toFMLS :
    HasFPowerSeriesAt (fun z : ℂ => 1 - z)
      (PowerSeries.toFMLS schroederOneSubSeriesℂ) (0 : ℂ) := by
  have hconst := hasFPowerSeriesAt_const_toFMLS_C (1 : ℂ)
  have hid := hasFPowerSeriesAt_id_toFMLS_X
  have hsub := hconst.sub hid
  simpa [schroederOneSubSeriesℂ, toFMLS_sub] using hsub

lemma schroederSqrtRegular_one :
    schroederSqrtRegular (1 : ℂ) = schroederSqrtRegularAtOneℂ := by
  unfold schroederSqrtRegular schroederRhoℂ
  simpa [Complex.ofReal_sub, Complex.ofReal_pow] using
    Complex_cpow_one_sub_schroederRho_sq_half

lemma schroederSqrtRegularAtOne_sq :
    schroederSqrtRegularAtOneℂ ^ 2 = 1 - schroederRhoℂ ^ 2 := by
  have h := schroederSqrtRegular_sq (1 : ℂ)
  rwa [schroederSqrtRegular_one, mul_one] at h

lemma schroederSqrtRegularAtOne_ne_zero :
    schroederSqrtRegularAtOneℂ ≠ 0 := by
  unfold schroederSqrtRegularAtOneℂ
  exact_mod_cast (Real.sqrt_ne_zero'.mpr one_sub_schroederRho_sq_pos)

lemma hasDerivAt_schroederSqrtRegular_one :
    HasDerivAt schroederSqrtRegular
      (-(schroederRhoℂ ^ 2) / (2 * schroederSqrtRegularAtOneℂ)) (1 : ℂ) := by
  have hid : HasDerivAt (fun z : ℂ => z) 1 (1 : ℂ) := by
    simpa using hasDerivAt_id (1 : ℂ)
  have hbase : HasDerivAt (fun z : ℂ => 1 - schroederRhoℂ ^ 2 * z)
      (-(schroederRhoℂ ^ 2)) (1 : ℂ) := by
    have h := (hasDerivAt_const (1 : ℂ) (1 : ℂ)).sub
      (HasDerivAt.const_mul (schroederRhoℂ ^ 2) hid)
    simpa only [Pi.sub_apply, zero_sub, mul_one] using h
  have hslit : (1 : ℂ) - schroederRhoℂ ^ 2 * (1 : ℂ) ∈ Complex.slitPlane := by
    convert Complex.ofReal_mem_slitPlane.2 one_sub_schroederRho_sq_pos using 1
    simp [schroederRhoℂ, Complex.ofReal_sub, Complex.ofReal_pow]
  have hpow := hbase.cpow_const (c := (1 / 2 : ℂ)) hslit
  convert hpow using 1
  · rw [show (1 / 2 : ℂ) - 1 = -(1 / 2 : ℂ) by norm_num]
    rw [Complex.cpow_neg]
    rw [show ((1 : ℂ) - schroederRhoℂ ^ 2 * (1 : ℂ)) ^ (1 / 2 : ℂ) =
        schroederSqrtRegularAtOneℂ by
        simpa [schroederSqrtRegular] using schroederSqrtRegular_one]
    field_simp [schroederSqrtRegularAtOne_ne_zero]

lemma schroederOneSubRhoℂ_eq :
    schroederOneSubRhoℂ = 1 - schroederRhoℂ := by
  simp [schroederOneSubRhoℂ, schroederRhoℂ, Complex.ofReal_sub]

end
end

/-!
# Third-order large Schroeder asymptotics

This file plugs the large-Schroeder square-root data at
`ρ = 3 - 2 * sqrt 2` into the third-order square-root applicator.
-/

set_option maxHeartbeats 1200000

open Complex Filter Asymptotics Set
open scoped Topology BigOperators PowerSeries

noncomputable section

def schroederAnalyticQuadraticCoeff : ℂ :=
  2 / schroederOneSubRhoℂ ^ 2

private lemma schroederSqrtRegularAtOne_add_self_ne_zero :
    schroederSqrtRegularAtOneℂ + schroederSqrtRegularAtOneℂ ≠ 0 := by
  intro h
  have hmul : (2 : ℂ) * schroederSqrtRegularAtOneℂ = 0 := by
    simpa [two_mul] using h
  rcases mul_eq_zero.mp hmul with htwo | ht
  · norm_num at htwo
  · exact schroederSqrtRegularAtOne_ne_zero ht

private lemma schroederOneSubRhoℂ_ne_zero : schroederOneSubRhoℂ ≠ 0 := by
  unfold schroederOneSubRhoℂ
  exact one_sub_schroederRho_ne_zeroℂ

def schroederThirdOriginalOneSubSeriesℂ : PowerSeries ℂ :=
  (1 : PowerSeries ℂ) - PowerSeries.C schroederRhoℂ⁻¹ * PowerSeries.X

def schroederThirdOriginalSeriesℂ : PowerSeries ℂ :=
  schroederSeriesℂ -
    PowerSeries.C schroederAnalyticQuadraticCoeff *
      schroederThirdOriginalOneSubSeriesℂ ^ 2

def schroederThirdAdjustedRescaledSeriesℂ : PowerSeries ℂ :=
  schroederRescaledSeriesℂ -
    PowerSeries.C schroederAnalyticQuadraticCoeff * schroederOneSubSeriesℂ ^ 2

def schroederThirdOriginalFun (z : ℂ) : ℂ :=
  schroederRescaledFun (schroederRhoℂ⁻¹ * z) -
    schroederAnalyticQuadraticCoeff * (1 - schroederRhoℂ⁻¹ * z) ^ 2

def schroederThirdAdjustedRescaledFun (z : ℂ) : ℂ :=
  schroederRescaledFun z - schroederAnalyticQuadraticCoeff * (1 - z) ^ 2

lemma schroederThirdOriginalFun_rescale (z : ℂ) :
    schroederThirdOriginalFun (schroederRhoℂ * z) =
      schroederThirdAdjustedRescaledFun z := by
  have hρ : schroederRhoℂ ≠ 0 := by
    unfold schroederRhoℂ
    exact_mod_cast schroederRho_ne_zero
  unfold schroederThirdOriginalFun schroederThirdAdjustedRescaledFun
  have hscale : schroederRhoℂ⁻¹ * (schroederRhoℂ * z) = z := by
    rw [← mul_assoc, inv_mul_cancel₀ hρ, one_mul]
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

lemma rescale_schroederThirdOriginalOneSubSeriesℂ :
    PowerSeries.rescale schroederRhoℂ schroederThirdOriginalOneSubSeriesℂ =
      schroederOneSubSeriesℂ := by
  have hρ : schroederRhoℂ ≠ 0 := by
    unfold schroederRhoℂ
    exact_mod_cast schroederRho_ne_zero
  ext n
  rw [PowerSeries.coeff_rescale]
  cases n with
  | zero =>
      simp [schroederThirdOriginalOneSubSeriesℂ, schroederOneSubSeriesℂ]
  | succ n =>
      cases n with
      | zero =>
          simp [schroederThirdOriginalOneSubSeriesℂ, schroederOneSubSeriesℂ,
            PowerSeries.coeff_X, PowerSeries.coeff_C, hρ]
      | succ n =>
          simp [schroederThirdOriginalOneSubSeriesℂ, schroederOneSubSeriesℂ,
            PowerSeries.coeff_X]

lemma rescale_schroederThirdOriginalSeriesℂ :
    PowerSeries.rescale schroederRhoℂ schroederThirdOriginalSeriesℂ =
      schroederThirdAdjustedRescaledSeriesℂ := by
  unfold schroederThirdOriginalSeriesℂ schroederThirdAdjustedRescaledSeriesℂ
  simp only [map_sub, map_mul, map_pow, rescale_schroederThirdOriginalOneSubSeriesℂ]
  rw [PowerSeries_rescale_C]
  rfl

lemma schroederThirdAdjustedRescaledFun_hasFPowerSeriesAt_zero :
    HasFPowerSeriesAt schroederThirdAdjustedRescaledFun
      (PowerSeries.toFMLS schroederThirdAdjustedRescaledSeriesℂ) (0 : ℂ) := by
  have hsquare : HasFPowerSeriesAt (fun z : ℂ => (1 - z) * (1 - z))
      (PowerSeries.toFMLS (schroederOneSubSeriesℂ ^ 2)) (0 : ℂ) := by
    simpa [pow_two] using
      hasFPowerSeriesAt_mul_toFMLS hasFPowerSeriesAt_schroederOneSub_toFMLS
        hasFPowerSeriesAt_schroederOneSub_toFMLS
  have hquad : HasFPowerSeriesAt
      (fun z : ℂ => schroederAnalyticQuadraticCoeff * (1 - z) ^ 2)
      (PowerSeries.toFMLS
        (PowerSeries.C schroederAnalyticQuadraticCoeff *
          schroederOneSubSeriesℂ ^ 2)) (0 : ℂ) := by
    have h := hsquare.const_smul (c := schroederAnalyticQuadraticCoeff)
    convert h using 1
    · ext z
      simp [pow_two, smul_eq_mul]
    · ext n
      simp [PowerSeries.toFMLS, FormalMultilinearSeries.ofScalars,
        PowerSeries.coeff_C_mul]
  have hsub := schroederRescaledFun_hasFPowerSeriesAt_zero.sub hquad
  simpa [schroederThirdAdjustedRescaledFun, schroederThirdAdjustedRescaledSeriesℂ,
    toFMLS_sub] using hsub

lemma schroederThirdOriginalFun_rescaled_hasFPowerSeriesAt_zero :
    HasFPowerSeriesAt
      (fun z : ℂ => schroederThirdOriginalFun (schroederRhoℂ * z))
      (PowerSeries.toFMLS
        (PowerSeries.rescale schroederRhoℂ schroederThirdOriginalSeriesℂ))
      (0 : ℂ) := by
  rw [rescale_schroederThirdOriginalSeriesℂ]
  simpa [schroederThirdOriginalFun_rescale] using
    schroederThirdAdjustedRescaledFun_hasFPowerSeriesAt_zero

lemma analyticOnNhd_schroederThirdAdjustedRescaledFun :
    AnalyticOnNhd ℂ schroederThirdAdjustedRescaledFun
      (DeltaDomainArg (3 / 2) (Real.pi / 4)) := by
  have hquad : AnalyticOnNhd ℂ
      (fun z : ℂ => schroederAnalyticQuadraticCoeff * (1 - z) ^ 2)
      (DeltaDomainArg (3 / 2) (Real.pi / 4)) := by
    simpa [pow_two] using
      (analyticOnNhd_const.mul
        ((analyticOnNhd_const.sub analyticOnNhd_id).mul
          (analyticOnNhd_const.sub analyticOnNhd_id)))
  simpa [schroederThirdAdjustedRescaledFun] using
    analyticOnNhd_schroederRescaledFun.sub hquad

lemma analyticOnNhd_schroederThirdOriginalFun_rescaled :
    AnalyticOnNhd ℂ
      (fun z : ℂ => schroederThirdOriginalFun (schroederRhoℂ * z))
      (DeltaDomainArg (3 / 2) (Real.pi / 4)) := by
  simpa [schroederThirdOriginalFun_rescale] using
    analyticOnNhd_schroederThirdAdjustedRescaledFun

def schroederAnalyticPart (z : ℂ) : ℂ :=
  2 * (1 - schroederRhoℂ * z) / (schroederOneSubRhoℂ ^ 2 * z)

def schroederSingularPart (z : ℂ) : ℂ :=
  -2 * schroederSqrtRegular z / (schroederOneSubRhoℂ ^ 2 * z)

lemma schroederRescaledFun_decomp {z : ℂ} (hz : z ≠ 0) :
    schroederRescaledFun z =
      schroederAnalyticPart z + schroederSingularPart z * schroederSqrtOneSub z := by
  unfold schroederRescaledFun schroederAnalyticPart schroederSingularPart
  rw [div_eq_iff (schroederRescaledDenominator_ne_zero z)]
  have hzq : schroederOneSubRhoℂ ^ 2 * z ≠ 0 := by
    exact mul_ne_zero (pow_ne_zero 2 one_sub_schroederRho_ne_zeroℂ) hz
  have hden := schroederRescaledDenominator_ne_zero z
  field_simp [hzq, hden]
  unfold schroederRescaledDenominator
  ring_nf
  rw [schroederSqrtRegular_sq, schroederSqrtOneSub_sq]
  rw [schroederOneSubRhoℂ_eq]
  have hq : (1 : ℂ) - schroederRhoℂ ≠ 0 := by
    simpa [schroederOneSubRhoℂ, schroederRhoℂ, Complex.ofReal_sub] using
      one_sub_schroederRho_ne_zeroℂ
  field_simp [pow_ne_zero 2 hq]
  ring

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

def schroederSqrtRegularTaylor (u : ℂ) : ℂ :=
  schroederSqrtRegularAtOneℂ +
    schroederSqrtRegularLinearCoeff * u +
      schroederSqrtRegularQuadraticCoeff * u ^ 2

def schroederSqrtRegularBTaylor (u : ℂ) : ℂ :=
  -(schroederOneSubRhoℂ ^ 2 / 2) *
    (schroederSingularCoeff + schroederSecondSingularCoeff * u +
      schroederThirdSingularCoeff * u ^ 2) * (1 - u)

lemma schroederSqrtRegular_sq_sub_taylor_sq (u : ℂ) :
    (schroederSqrtRegular (1 - u)) ^ 2 -
        (schroederSqrtRegularTaylor u) ^ 2 =
      u ^ 3 *
        (schroederRhoℂ ^ 6 / (8 * schroederSqrtRegularAtOneℂ ^ 4) -
          schroederRhoℂ ^ 8 / (64 * schroederSqrtRegularAtOneℂ ^ 6) * u) := by
  unfold schroederSqrtRegularTaylor schroederSqrtRegularLinearCoeff
    schroederSqrtRegularQuadraticCoeff
  rw [schroederSqrtRegular_sq]
  field_simp [schroederSqrtRegularAtOne_ne_zero]
  rw [show schroederSqrtRegularAtOneℂ ^ 6 =
      (1 - schroederRhoℂ ^ 2) ^ 3 by
        rw [show schroederSqrtRegularAtOneℂ ^ 6 =
            (schroederSqrtRegularAtOneℂ ^ 2) ^ 3 by ring,
          schroederSqrtRegularAtOne_sq]]
  rw [schroederSqrtRegularAtOne_sq]
  ring

lemma schroederSqrtRegular_sub_taylor_isBigO :
    (fun u : ℂ => schroederSqrtRegular (1 - u) - schroederSqrtRegularTaylor u)
      =O[𝓝 (0 : ℂ)] (fun u : ℂ => ‖u‖ ^ 3) := by
  let t : ℂ → ℂ := fun u => schroederSqrtRegular (1 - u)
  let q : ℂ → ℂ := schroederSqrtRegularTaylor
  have ht : Tendsto t (𝓝 (0 : ℂ)) (𝓝 schroederSqrtRegularAtOneℂ) := by
    have harg : Tendsto (fun u : ℂ => 1 - u) (𝓝 (0 : ℂ)) (𝓝 (1 : ℂ)) := by
      simpa using
        (continuousAt_const.sub continuousAt_id : ContinuousAt (fun u : ℂ => 1 - u) 0).tendsto
    have h := hasDerivAt_schroederSqrtRegular_one.continuousAt.tendsto.comp harg
    simpa [t, schroederSqrtRegular_one] using h
  have hq : Tendsto q (𝓝 (0 : ℂ)) (𝓝 schroederSqrtRegularAtOneℂ) := by
    have hcont : ContinuousAt q 0 := by
      unfold q schroederSqrtRegularTaylor
      fun_prop
    simpa [q, schroederSqrtRegularTaylor] using hcont.tendsto
  have hden : Tendsto (fun u : ℂ => (t u + q u)⁻¹) (𝓝 (0 : ℂ))
      (𝓝 ((schroederSqrtRegularAtOneℂ + schroederSqrtRegularAtOneℂ)⁻¹)) := by
    exact (ht.add hq).inv₀ schroederSqrtRegularAtOne_add_self_ne_zero
  have hdenO : (fun u : ℂ => (t u + q u)⁻¹) =O[𝓝 (0 : ℂ)]
      (fun _ : ℂ => (1 : ℝ)) :=
    tendsto_isBigO_one_complex hden
  have hsqO : (fun u : ℂ => (t u) ^ 2 - (q u) ^ 2) =O[𝓝 (0 : ℂ)]
      (fun u : ℂ => ‖u‖ ^ 3) := by
    have hbase := cubic_mul_continuous_isBigO
      (fun u : ℂ =>
        schroederRhoℂ ^ 6 / (8 * schroederSqrtRegularAtOneℂ ^ 4) -
          schroederRhoℂ ^ 8 / (64 * schroederSqrtRegularAtOneℂ ^ 6) * u)
      (by fun_prop)
    refine hbase.congr_left ?_
    intro u
    dsimp [t, q]
    rw [schroederSqrtRegular_sq_sub_taylor_sq]
  have hprod := hsqO.mul hdenO
  refine hprod.congr' ?_ ?_
  · have hsum_ne : ∀ᶠ u : ℂ in 𝓝 (0 : ℂ), t u + q u ≠ 0 := by
      have hsum := ht.add hq
      exact hsum.eventually_ne schroederSqrtRegularAtOne_add_self_ne_zero
    filter_upwards [hsum_ne] with u hu
    dsimp [t, q] at hu ⊢
    set a := schroederSqrtRegular (1 - u)
    set b := schroederSqrtRegularTaylor u
    rw [show a ^ 2 - b ^ 2 = (a - b) * (a + b) by ring]
    rw [mul_assoc, mul_inv_cancel₀ hu, mul_one]
  · filter_upwards with u
    ring

lemma schroederAnalyticPart_remainder_isBigO :
    (fun u : ℂ =>
      schroederAnalyticPart (1 - u) -
        (schroederRegularValueℂ + schroederAnalyticLinearCoeff * u +
          schroederAnalyticQuadraticCoeff * u ^ 2))
      =O[𝓝 (0 : ℂ)] (fun u : ℂ => ‖u‖ ^ 3) := by
  have hbase := cubic_mul_continuous_isBigO
    (fun u : ℂ => (2 / schroederOneSubRhoℂ ^ 2) / (1 - u))
    (by
      apply ContinuousAt.div
      · fun_prop
      · fun_prop
      · norm_num)
  refine hbase.congr' ?_ (EventuallyEq.refl _ _)
  filter_upwards [eventually_ne_nhds (show (0 : ℂ) ≠ 1 by norm_num)] with u hu
  unfold schroederAnalyticPart schroederRegularValueℂ schroederAnalyticLinearCoeff
    schroederAnalyticQuadraticCoeff
  rw [schroederOneSubRhoℂ_eq]
  have hq : (1 : ℂ) - schroederRhoℂ ≠ 0 := by
    simpa [schroederOneSubRhoℂ, schroederRhoℂ, Complex.ofReal_sub] using
      one_sub_schroederRho_ne_zeroℂ
  field_simp [sub_ne_zero.mpr (Ne.symm hu), hq, pow_ne_zero 2 hq]
  ring

section
end

set_option backward.isDefEq.respectTransparency false in
lemma schroederSqrtRegularTaylor_sub_BTaylor_isBigO :
    (fun u : ℂ => schroederSqrtRegularTaylor u - schroederSqrtRegularBTaylor u)
      =O[𝓝 (0 : ℂ)] (fun u : ℂ => ‖u‖ ^ 3) := by
  have hbase := cubic_mul_continuous_isBigO
    (fun _u : ℂ =>
      schroederSqrtRegularAtOneℂ + schroederSqrtRegularLinearCoeff +
        schroederSqrtRegularQuadraticCoeff)
    (by fun_prop)
  refine hbase.congr_left ?_
  intro u
  dsimp
  unfold schroederSqrtRegularTaylor schroederSqrtRegularBTaylor
    schroederThirdSingularCoeff schroederSecondSingularCoeff
    schroederSecondKℂ schroederSingularCoeff schroederSqrtRegularLinearCoeff
    schroederSqrtRegularQuadraticCoeff
  unfold schroederThirdKℂ
  unfold schroederSqrtRegularLinearCoeff schroederSqrtRegularQuadraticCoeff
  field_simp [schroederSqrtRegularAtOne_ne_zero,
    schroederOneSubRhoℂ_ne_zero, pow_ne_zero 2 schroederOneSubRhoℂ_ne_zero]
  field_simp [schroederOneSubRhoℂ_ne_zero]
  rw [show schroederSqrtRegularAtOneℂ ^ 2 = 1 - schroederRhoℂ ^ 2 by
    exact schroederSqrtRegularAtOne_sq]
  field_simp [one_sub_schroederRho_ne_zeroℂ]
  try ring_nf

section
end

set_option backward.isDefEq.respectTransparency false in
lemma schroederSingularPart_remainder_isBigO :
    (fun u : ℂ =>
      schroederSingularPart (1 - u) -
        (schroederSingularCoeff + schroederSecondSingularCoeff * u +
          schroederThirdSingularCoeff * u ^ 2))
      =O[𝓝 (0 : ℂ)] (fun u : ℂ => ‖u‖ ^ 3) := by
  have hdiff : (fun u : ℂ =>
      schroederSqrtRegular (1 - u) - schroederSqrtRegularBTaylor u)
      =O[𝓝 (0 : ℂ)] (fun u : ℂ => ‖u‖ ^ 3) := by
    have hsum := schroederSqrtRegular_sub_taylor_isBigO.add
      schroederSqrtRegularTaylor_sub_BTaylor_isBigO
    refine hsum.congr_left ?_
    intro u
    ring
  have hden_tendsto : Tendsto (fun u : ℂ => (1 - u)⁻¹) (𝓝 (0 : ℂ))
      (𝓝 (1 : ℂ)) := by
    have hcont : ContinuousAt (fun u : ℂ => 1 - u) 0 := by fun_prop
    have hne : (1 - (0 : ℂ)) ≠ 0 := by norm_num
    convert hcont.tendsto.inv₀ hne using 1
    norm_num
  have hdenO : (fun u : ℂ => (1 - u)⁻¹) =O[𝓝 (0 : ℂ)]
      (fun _ : ℂ => (1 : ℝ)) :=
    tendsto_isBigO_one_complex hden_tendsto
  have hprod := hdiff.mul hdenO
  have hscaled : (fun u : ℂ =>
      (-2 / schroederOneSubRhoℂ ^ 2) *
        ((schroederSqrtRegular (1 - u) - schroederSqrtRegularBTaylor u) *
          (1 - u)⁻¹))
      =O[𝓝 (0 : ℂ)] (fun u : ℂ => ‖u‖ ^ 3) := by
    refine (hprod.const_mul_left (-2 / schroederOneSubRhoℂ ^ 2)).congr_right ?_
    intro u
    ring
  refine hscaled.congr' ?_ (EventuallyEq.refl _ _)
  filter_upwards [eventually_ne_nhds (show (0 : ℂ) ≠ 1 by norm_num)] with u hu
  unfold schroederSingularPart schroederSqrtRegularBTaylor
  field_simp [sub_ne_zero.mpr (Ne.symm hu), schroederOneSubRhoℂ_ne_zero,
    pow_ne_zero 2 schroederOneSubRhoℂ_ne_zero]
  field_simp [schroederOneSubRhoℂ_ne_zero]
  try ring

lemma schroederSqrtOneSub_local_isBigO :
    (fun u : ℂ => schroederSqrtOneSub (1 - u)) =O[𝓝 (0 : ℂ)]
      (fun u : ℂ => ‖u‖ ^ (1 / 2 : ℝ)) := by
  refine IsBigO.of_bound 1 ?_
  filter_upwards with u
  unfold schroederSqrtOneSub
  rw [show (1 : ℂ) - (1 - u) = u by ring]
  rw [show (1 / 2 : ℂ) = (((1 / 2 : ℝ) : ℂ)) by norm_num]
  rw [Complex.norm_cpow_real u (1 / 2 : ℝ)]
  rw [Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg u) _)]
  simp

lemma schroederThird_local_residual_eq {u : ℂ} (hu1 : u ≠ 1) :
    sqrtAdjustedFun schroederThirdAdjustedRescaledFun schroederRegularValueℂ
        (-schroederAnalyticLinearCoeff) (1 - u) -
        schroederSingularCoeff * u ^ (1 / 2 : ℂ) -
        schroederSecondSingularCoeff * u ^ (3 / 2 : ℂ) -
        schroederThirdSingularCoeff * u ^ (5 / 2 : ℂ) =
      (schroederAnalyticPart (1 - u) -
        (schroederRegularValueℂ + schroederAnalyticLinearCoeff * u +
          schroederAnalyticQuadraticCoeff * u ^ 2)) +
        (schroederSingularPart (1 - u) -
          (schroederSingularCoeff + schroederSecondSingularCoeff * u +
            schroederThirdSingularCoeff * u ^ 2)) *
          schroederSqrtOneSub (1 - u) := by
  have hz_ne : (1 : ℂ) - u ≠ 0 := sub_ne_zero.mpr (Ne.symm hu1)
  have hdecomp := schroederRescaledFun_decomp (z := 1 - u) hz_ne
  have hs : schroederSqrtOneSub (1 - u) = u ^ (1 / 2 : ℂ) := by
    unfold schroederSqrtOneSub
    rw [show (1 : ℂ) - (1 - u) = u by ring]
  have hpow3 : u ^ (3 / 2 : ℂ) = u * schroederSqrtOneSub (1 - u) := by
    by_cases hu0 : u = 0
    · subst u
      norm_num [schroederSqrtOneSub]
    · rw [hs]
      rw [show (3 / 2 : ℂ) = 1 + (1 / 2 : ℂ) by norm_num]
      rw [Complex.cpow_add _ _ hu0, Complex.cpow_one]
  have hpow5 : u ^ (5 / 2 : ℂ) = u ^ 2 * schroederSqrtOneSub (1 - u) := by
    by_cases hu0 : u = 0
    · subst u
      norm_num [schroederSqrtOneSub]
    · rw [hs]
      rw [show (5 / 2 : ℂ) = 2 + (1 / 2 : ℂ) by norm_num]
      rw [Complex.cpow_add _ _ hu0]
      norm_num [Complex.cpow_natCast]
  unfold sqrtAdjustedFun sqrtLinearAtOneFun schroederThirdAdjustedRescaledFun
  rw [hdecomp, hpow3, hpow5, hs]
  ring

lemma schroederThird_local_residual_isLittleO :
    (fun u : ℂ =>
      sqrtAdjustedFun schroederThirdAdjustedRescaledFun schroederRegularValueℂ
          (-schroederAnalyticLinearCoeff) (1 - u) -
          schroederSingularCoeff * u ^ (1 / 2 : ℂ) -
          schroederSecondSingularCoeff * u ^ (3 / 2 : ℂ) -
          schroederThirdSingularCoeff * u ^ (5 / 2 : ℂ))
      =o[𝓝 (0 : ℂ)] (fun u : ℂ => ‖u‖ ^ (5 / 2 : ℝ)) := by
  have hA := schroederAnalyticPart_remainder_isBigO.trans_isLittleO
    norm_pow_three_isLittleO_norm_rpow_five_halves
  have hBbig := schroederSingularPart_remainder_isBigO.mul
    schroederSqrtOneSub_local_isBigO
  have hB := hBbig.trans_isLittleO
    norm_pow_three_mul_rpow_half_isLittleO_norm_rpow_five_halves
  have hsum := hA.add hB
  refine hsum.congr' ?_ (EventuallyEq.refl _ _)
  filter_upwards [eventually_ne_nhds (show (0 : ℂ) ≠ 1 by norm_num)] with u hu1
  simpa using (schroederThird_local_residual_eq (u := u) hu1).symm

lemma tendsto_schroederThirdAdjustedRescaledFun_singularity :
    Tendsto
      (fun z : ℂ =>
        ‖sqrtAdjustedFun schroederThirdAdjustedRescaledFun schroederRegularValueℂ
            (-schroederAnalyticLinearCoeff) z -
            schroederSingularCoeff * (1 - z) ^ (1 / 2 : ℂ) -
            schroederSecondSingularCoeff * (1 - z) ^ (3 / 2 : ℂ) -
            schroederThirdSingularCoeff * (1 - z) ^ (5 / 2 : ℂ)‖ *
          ‖(1 : ℂ) - z‖ ^ (-(5 / 2 : ℝ)))
      (𝓝[DeltaDomainArg (3 / 2) (Real.pi / 4)] (1 : ℂ)) (𝓝 0) := by
  let l := 𝓝[DeltaDomainArg (3 / 2) (Real.pi / 4)] (1 : ℂ)
  have hu : Tendsto (fun z : ℂ => 1 - z) l (𝓝 (0 : ℂ)) := by
    have hcont : ContinuousAt (fun z : ℂ => 1 - z) 1 := by fun_prop
    simpa using Tendsto.mono_left hcont.tendsto nhdsWithin_le_nhds
  have hcomp := schroederThird_local_residual_isLittleO.comp_tendsto hu
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

lemma schroederSecondSingularCoeff_eq_meta :
    schroederSecondSingularCoeff =
      -(schroederRhoℂ * schroederSingularDerivAtRho) := by
  unfold schroederSingularDerivAtRho
  field_simp [show schroederRhoℂ ≠ 0 by
    unfold schroederRhoℂ
    exact_mod_cast schroederRho_ne_zero]

lemma schroederThirdSingularCoeff_eq_meta :
    schroederThirdSingularCoeff =
      (schroederRhoℂ ^ 2 * schroederSingularSecondDerivAtRho) / 2 := by
  unfold schroederSingularSecondDerivAtRho
  field_simp [show schroederRhoℂ ≠ 0 by
    unfold schroederRhoℂ
    exact_mod_cast schroederRho_ne_zero]

lemma schroederSingularCoeff_ne_zero : schroederSingularCoeff ≠ 0 := by
  unfold schroederSingularCoeff
  exact div_ne_zero
    (mul_ne_zero (by norm_num) schroederSqrtRegularAtOne_ne_zero)
    (pow_ne_zero 2 one_sub_schroederRho_ne_zeroℂ)

theorem schroederThirdOriginalSeries_complex_meta :
    (fun n : ℕ =>
      PowerSeries.coeff (R := ℂ) n schroederThirdOriginalSeriesℂ -
        (((schroederRhoℂ⁻¹) ^ n) *
          (sqrtSingularityC0 schroederSingularCoeff *
              (((n : ℝ) ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ) +
            sqrtSingularityC1 schroederRho schroederSingularCoeff
                schroederSingularDerivAtRho *
              (((n : ℝ) ^ (-(5 / 2 : ℝ)) : ℝ) : ℂ) +
            sqrtSingularityC2 schroederRho schroederSingularCoeff
                schroederSingularDerivAtRho schroederSingularSecondDerivAtRho *
              (((n : ℝ) ^ (-(7 / 2 : ℝ)) : ℝ) : ℂ))))
      =o[atTop]
        (fun n : ℕ =>
          ‖((schroederRhoℂ⁻¹) ^ n *
            (((n : ℝ) ^ (-(7 / 2 : ℝ)) : ℝ) : ℂ))‖) := by
  refine sqrt_singularity_thirdOrder_original_of_rescaled_singularity
    (ρ := schroederRho) (R := (3 / 2 : ℝ)) (φ := Real.pi / 4)
    (F := schroederThirdOriginalFun) (P := schroederThirdOriginalSeriesℂ)
    (A0 := schroederRegularValueℂ) (A1 := -schroederAnalyticLinearCoeff)
    (Bρ := schroederSingularCoeff)
    (Bderivρ := schroederSingularDerivAtRho)
    (Bsecondρ := schroederSingularSecondDerivAtRho)
    schroederRho_pos schroederSingularCoeff_ne_zero ?_ ?_ ?_
    ?_ ?_ ?_
  · norm_num
  · positivity
  · nlinarith [Real.pi_pos]
  · simpa [schroederRhoℂ] using
      schroederThirdOriginalFun_rescaled_hasFPowerSeriesAt_zero
  · simpa [schroederRhoℂ] using
      analyticOnNhd_schroederThirdOriginalFun_rescaled
  · have h := tendsto_schroederThirdAdjustedRescaledFun_singularity
    refine h.congr' ?_
    filter_upwards with z
    have hfun :
        schroederThirdOriginalFun (((schroederRho : ℝ) : ℂ) * z) =
          schroederThirdAdjustedRescaledFun z := by
      change schroederThirdOriginalFun (schroederRhoℂ * z) =
        schroederThirdAdjustedRescaledFun z
      exact schroederThirdOriginalFun_rescale z
    have hadj :
        sqrtAdjustedFun
            (fun w : ℂ => schroederThirdOriginalFun (((schroederRho : ℝ) : ℂ) * w))
            schroederRegularValueℂ (-schroederAnalyticLinearCoeff) z =
          sqrtAdjustedFun schroederThirdAdjustedRescaledFun schroederRegularValueℂ
            (-schroederAnalyticLinearCoeff) z := by
      unfold sqrtAdjustedFun
      simpa using
        congrArg (fun x : ℂ =>
          x - sqrtLinearAtOneFun schroederRegularValueℂ
            (-schroederAnalyticLinearCoeff) z) hfun
    rw [hadj]
    rw [show -(((schroederRho : ℝ) : ℂ) * schroederSingularDerivAtRho) =
        schroederSecondSingularCoeff by
          change -(schroederRhoℂ * schroederSingularDerivAtRho) =
            schroederSecondSingularCoeff
          exact schroederSecondSingularCoeff_eq_meta.symm]
    rw [show ((((schroederRho : ℝ) : ℂ) ^ 2 *
          schroederSingularSecondDerivAtRho) / 2) =
        schroederThirdSingularCoeff by
          change (schroederRhoℂ ^ 2 * schroederSingularSecondDerivAtRho) / 2 =
            schroederThirdSingularCoeff
          exact schroederThirdSingularCoeff_eq_meta.symm]

section
end

set_option backward.isDefEq.respectTransparency false in
lemma schroederThirdOriginalOneSubSeries_sq_coeff_of_three_le {n : ℕ} (hn : 3 ≤ n) :
    PowerSeries.coeff (R := ℂ) n (schroederThirdOriginalOneSubSeriesℂ ^ 2) = 0 := by
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
  · have hcoeff : PowerSeries.coeff (R := ℂ) i schroederThirdOriginalOneSubSeriesℂ = 0 := by
      unfold schroederThirdOriginalOneSubSeriesℂ
      simp [PowerSeries.coeff_X,
        ne_of_gt (lt_of_lt_of_le (by norm_num : 0 < 2) hi),
        ne_of_gt (lt_of_lt_of_le (by norm_num : 1 < 2) hi)]
    simp [hcoeff]
  · have hcoeff : PowerSeries.coeff (R := ℂ) j schroederThirdOriginalOneSubSeriesℂ = 0 := by
      unfold schroederThirdOriginalOneSubSeriesℂ
      simp [PowerSeries.coeff_X,
        ne_of_gt (lt_of_lt_of_le (by norm_num : 0 < 2) hj),
        ne_of_gt (lt_of_lt_of_le (by norm_num : 1 < 2) hj)]
    simp [hcoeff]

lemma coeff_schroederThirdOriginalSeriesℂ_of_three_le {n : ℕ} (hn : 3 ≤ n) :
    PowerSeries.coeff (R := ℂ) n schroederThirdOriginalSeriesℂ = (schroeder n : ℂ) := by
  unfold schroederThirdOriginalSeriesℂ
  simp [PowerSeries.coeff_C_mul, schroederThirdOriginalOneSubSeries_sq_coeff_of_three_le hn]

lemma schroederThirdLeadingConstantℂ_ne_zero :
    schroederThirdLeadingConstantℂ ≠ 0 := by
  unfold schroederThirdLeadingConstantℂ sqrtSingularityC0
  have hden : (((2 * Real.sqrt Real.pi : ℝ) : ℂ)) ≠ 0 := by
    exact_mod_cast
      (mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0)
        (Real.sqrt_ne_zero'.mpr Real.pi_pos))
  exact div_ne_zero (neg_ne_zero.mpr schroederSingularCoeff_ne_zero) hden

theorem schroeder_complex_thirdOrder_additive_meta :
    (fun n : ℕ =>
      (schroeder n : ℂ) -
        ((schroederRhoℂ⁻¹) ^ n *
          (sqrtSingularityC0 schroederSingularCoeff *
              (((n : ℝ) ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ) +
            sqrtSingularityC1 schroederRho schroederSingularCoeff
                schroederSingularDerivAtRho *
              (((n : ℝ) ^ (-(5 / 2 : ℝ)) : ℝ) : ℂ) +
            sqrtSingularityC2 schroederRho schroederSingularCoeff
                schroederSingularDerivAtRho schroederSingularSecondDerivAtRho *
              (((n : ℝ) ^ (-(7 / 2 : ℝ)) : ℝ) : ℂ))))
      =o[atTop]
        (fun n : ℕ =>
          ‖((schroederRhoℂ⁻¹) ^ n *
            (((n : ℝ) ^ (-(7 / 2 : ℝ)) : ℝ) : ℂ))‖) := by
  have h := schroederThirdOriginalSeries_complex_meta
  refine h.congr' ?_ (EventuallyEq.refl _ _)
  filter_upwards [eventually_ge_atTop 3] with n hn
  rw [coeff_schroederThirdOriginalSeriesℂ_of_three_le hn]

end

set_option maxHeartbeats 1200000
open Complex Filter Asymptotics Set
open scoped Topology BigOperators PowerSeries
theorem solution :
    (fun n : ℕ =>
      (schroeder n : ℂ) -
        (schroederRhoℂ⁻¹) ^ n * schroederThirdLeadingConstantℂ *
          (((n : ℝ) ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ) *
          (1 + schroederRelativeSecondMetaConstantℂ *
              (((n : ℝ) ^ (-(1 : ℝ)) : ℝ) : ℂ) +
            schroederRelativeThirdMetaConstantℂ *
              (((n : ℝ) ^ (-(2 : ℝ)) : ℝ) : ℂ)))
      =o[atTop]
        (fun n : ℕ =>
          ‖((schroederRhoℂ⁻¹) ^ n *
            (((n : ℝ) ^ (-(7 / 2 : ℝ)) : ℝ) : ℂ))‖) := by
  refine schroeder_complex_thirdOrder_additive_meta.congr' ?_ (EventuallyEq.refl _ _)
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hnpos : 0 < (n : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < (1 : ℕ)) hn)
  have hpow5 :
      (((n : ℝ) ^ (-(5 / 2 : ℝ)) : ℝ) : ℂ) =
        (((n : ℝ) ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ) *
          (((n : ℝ) ^ (-(1 : ℝ)) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul]
    congr 1
    rw [← Real.rpow_add hnpos]
    norm_num
  have hpow7 :
      (((n : ℝ) ^ (-(7 / 2 : ℝ)) : ℝ) : ℂ) =
        (((n : ℝ) ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ) *
          (((n : ℝ) ^ (-(2 : ℝ)) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul]
    congr 1
    rw [← Real.rpow_add hnpos]
    norm_num
  unfold schroederRelativeSecondMetaConstantℂ schroederRelativeThirdMetaConstantℂ
  rw [hpow5, hpow7]
  field_simp [schroederThirdLeadingConstantℂ_ne_zero]
  unfold schroederThirdLeadingConstantℂ
  ring
