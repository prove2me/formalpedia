-- Prove2me | solution 1 for AnalyticCombinatorics.Ch9.LimitLaws.PermCycleCountBridge.permutationCycles_gaussian_uniformPerm
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-10-28T15:58:41.214988+00:00
-- url     : https://prove2.me/submissions/955134b9-ff58-4672-b302-8d560baf5e06

import Definitions.Def_AnalyticCombinatorics_Ch9_LimitLaws_FixedPointsPoisson
import Definitions.Def_AnalyticCombinatorics_Ch9_LimitLaws_PermutationCycles
import Definitions.Def_AnalyticCombinatorics_Ch9_LimitLaws_QuasiPowers
import Definitions.Def_AnalyticCombinatorics_Compatibility_TendstoInDistribution
import Definitions.Def_AnalyticCombinatorics_Ch9_LimitLaws_PMFToDistribution
import Definitions.Def_AnalyticCombinatorics_Ch9_LimitLaws_RCyclesPoisson
import Definitions.Def_AnalyticCombinatorics_Ch9_LimitLaws_ExpectedCycles
import Theorems.Thm_AnalyticCombinatorics_Ch9_LimitLaws_quasiPowers_tendstoInDistribution_of_continuousAt
import Mathlib
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
import Mathlib.Combinatorics.Derangements.Exponential
import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent

namespace AnalyticCombinatorics.Ch9.LimitLaws.PermCycleCountBridge end AnalyticCombinatorics.Ch9.LimitLaws.PermCycleCountBridge

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
section
/-!
# Quasi-powers and Gaussian limit laws

This file formalizes the Mathlib-supported core of Hwang's quasi-powers theorem.

Mathlib v4.29.0 has Levy's continuity theorem for characteristic functions as
`MeasureTheory.ProbabilityMeasure.tendsto_iff_tendsto_charFun`, but not a
corresponding Curtiss-style continuity theorem for moment-generating functions.
Accordingly the main limit theorem below takes a logarithmic quasi-powers expansion
on the imaginary axis, proves convergence of normalized characteristic functions,
and then applies Levy's theorem.
-/

noncomputable section

open Asymptotics Complex Filter MeasureTheory ProbabilityTheory

open scoped RealInnerProductSpace Topology

namespace AnalyticCombinatorics
namespace Ch9
namespace LimitLaws

/-- If `β_n -> infinity`, then each fixed scaled real argument tends to zero. -/
lemma quasiPower_scaledRealArgument_tendsto_zero {β : ℕ → ℝ} {u₂ t : ℝ}
    (hβ : Tendsto β atTop atTop) (hu₂ : 0 < u₂) :
    Tendsto (fun n => (Real.sqrt (β n * u₂))⁻¹ * t) atTop (𝓝 0) := by
  have hprod : Tendsto (fun n => β n * u₂) atTop atTop := hβ.atTop_mul_const hu₂
  simpa using
    (tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp hprod)).mul_const t

/-- If `β_n -> infinity`, then each fixed scaled imaginary point tends to zero. -/
lemma quasiPower_scaledArgument_tendsto_zero {β : ℕ → ℝ} {u₂ t : ℝ}
    (hβ : Tendsto β atTop atTop) (hu₂ : 0 < u₂) :
    Tendsto (fun n => qpZ β u₂ n t) atTop (𝓝 0) := by
  have hreal := quasiPower_scaledRealArgument_tendsto_zero
    (β := β) (u₂ := u₂) (t := t) hβ hu₂
  simpa [qpZ] using hreal.ofReal.const_mul Complex.I

end LimitLaws
end Ch9
end AnalyticCombinatorics
end
end

section
/-!
# Cycles of a fixed length in a random permutation

This file sets up the genuine random variable counting cycles of length exactly
`r` in a uniform random permutation of `Fin n`.

For `r = 1` this is the fixed-point count.  For `r ≥ 2` it is the multiplicity
of `r` in Mathlib's `cycleType`, equivalently the number of nontrivial cycle
factors with support of cardinality `r`.
-/

noncomputable section

open Filter MeasureTheory
open scoped Topology ENNReal NNReal

namespace AnalyticCombinatorics
namespace Ch9
namespace LimitLaws
namespace RCyclesPoissonNS

@[simp]
lemma rCycleCount_one (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    rCycleCount n 1 σ = FixedPointsPoissonNS.fixedPointCount n σ := by
  simp [rCycleCount]

lemma rCycleCount_eq_cycleType_count_of_ne_one {n r : ℕ}
    (hr : r ≠ 1) (σ : Equiv.Perm (Fin n)) :
    rCycleCount n r σ = σ.cycleType.count r := by
  simp [rCycleCount, hr]

end RCyclesPoissonNS
end LimitLaws
end Ch9
end AnalyticCombinatorics
end
end

section
/-!
# Cycles in a random permutation

This file instantiates the local quasi-powers interface for the Feller coupling
model of the number of cycles in a uniform random permutation:
`C_n = sum_{k=1}^n B_k`, with independent Bernoulli variables
`P(B_k = 1) = 1 / k`.
-/

noncomputable section

open Complex Filter MeasureTheory ProbabilityTheory

open scoped Topology

namespace AnalyticCombinatorics
namespace Ch9
namespace LimitLaws

/-- Bernoulli law with success probability `1 / (k + 1)`. -/
def cycleBernoulliLaw (k : ℕ) : Measure ℝ :=
  ENNReal.ofReal (1 - ((k : ℝ) + 1)⁻¹) • Measure.dirac (0 : ℝ) +
    ENNReal.ofReal (((k : ℝ) + 1)⁻¹) • Measure.dirac (1 : ℝ)

lemma cycleBernoulliLaw_isProbabilityMass (k : ℕ) :
    (cycleBernoulliLaw k) Set.univ = 1 := by
  rw [cycleBernoulliLaw]
  simp only [Measure.add_apply, Measure.smul_apply, Measure.dirac_apply]
  simp
  have hpos : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have hnonneg : 0 ≤ 1 - ((k : ℝ) + 1)⁻¹ := by
    rw [sub_nonneg]
    have hk_nonneg : (0 : ℝ) ≤ (k : ℝ) := by exact_mod_cast Nat.zero_le k
    exact inv_le_one_of_one_le₀ (by linarith : (1 : ℝ) ≤ (k : ℝ) + 1)
  rw [← ENNReal.ofReal_add hnonneg (inv_nonneg.mpr hpos.le)]
  rw [show 1 - ((k : ℝ) + 1)⁻¹ + ((k : ℝ) + 1)⁻¹ = (1 : ℝ) by ring]
  simp

instance cycleBernoulliLaw_isProbabilityMeasure (k : ℕ) :
    IsProbabilityMeasure (cycleBernoulliLaw k) where
  measure_univ := cycleBernoulliLaw_isProbabilityMass k

/-- Product probability space for the first `n` Feller Bernoulli variables. -/
abbrev CycleΩ (n : ℕ) := Fin n → ℝ

/-- Product law of the independent Bernoulli variables `B_k`, `1 ≤ k ≤ n`. -/
def cycleP (n : ℕ) : Measure (CycleΩ n) :=
  Measure.pi (fun i : Fin n => cycleBernoulliLaw i.1)

instance cycleP_isProbabilityMeasure (n : ℕ) : IsProbabilityMeasure (cycleP n) := by
  unfold cycleP
  infer_instance

/-- Feller coupling model for the number of cycles in a uniform random permutation. -/
def cycleCount (n : ℕ) (ω : CycleΩ n) : ℝ :=
  ∑ i, ω i

/-- One factor in the cycle-count characteristic function, in logarithmic variable `z`. -/
def cycleBase (k : ℕ) (z : ℂ) : ℂ :=
  ((1 - ((k : ℝ) + 1)⁻¹ : ℝ) : ℂ) +
    (((k : ℝ) + 1)⁻¹ : ℝ) * Complex.exp z

/-- The `H_n`-scale quadratic main term.  Its first two Taylor coefficients are both `1`. -/
def cycleMain (z : ℂ) : ℂ :=
  z + z ^ 2 / 2

/-- Exact logarithmic remainder in the quasi-powers expansion. -/
def cycleR (n : ℕ) (z : ℂ) : ℂ :=
  if n = 0 then 0 else
    ((∑ i : Fin n, Complex.log (cycleBase i.1 z)) - (cycleH n : ℂ) * cycleMain z) /
      (cycleH n : ℂ)

lemma cycleH_zero : cycleH 0 = 0 := by
  simp [cycleH]

lemma cycleH_pos {n : ℕ} (hn : n ≠ 0) : 0 < cycleH n := by
  unfold cycleH
  exact_mod_cast harmonic_pos hn

lemma cycleH_ne_zero {n : ℕ} (hn : n ≠ 0) : (cycleH n : ℂ) ≠ 0 := by
  exact_mod_cast (cycleH_pos hn).ne'

lemma cycleBernoulliLaw_charFun (k : ℕ) (s : ℝ) :
    charFun (cycleBernoulliLaw k) s = cycleBase k (Complex.I * (s : ℂ)) := by
  rw [cycleBernoulliLaw, charFun_apply_real]
  have h0 : Integrable (fun x : ℝ => Complex.exp (s * x * Complex.I))
      (Measure.dirac (0 : ℝ)) := by
    simpa using
      (integrable_dirac (a := (0 : ℝ))
        (f := fun x : ℝ => Complex.exp (s * x * Complex.I)) (by simp))
  have h1 : Integrable (fun x : ℝ => Complex.exp (s * x * Complex.I))
      (Measure.dirac (1 : ℝ)) := by
    simpa using
      (integrable_dirac (a := (1 : ℝ))
        (f := fun x : ℝ => Complex.exp (s * x * Complex.I)) (by simp))
  rw [integral_add_measure (h0.smul_measure ENNReal.ofReal_ne_top)
    (h1.smul_measure ENNReal.ofReal_ne_top), integral_smul_measure, integral_smul_measure,
    integral_dirac, integral_dirac]
  have hpos : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have hnonneg : 0 ≤ 1 - ((k : ℝ) + 1)⁻¹ := by
    rw [sub_nonneg]
    have hk_nonneg : (0 : ℝ) ≤ (k : ℝ) := by exact_mod_cast Nat.zero_le k
    exact inv_le_one_of_one_le₀ (by linarith : (1 : ℝ) ≤ (k : ℝ) + 1)
  rw [ENNReal.toReal_ofReal hnonneg, ENNReal.toReal_ofReal (inv_nonneg.mpr hpos.le)]
  have hcomm : (s : ℂ) * Complex.I = Complex.I * (s : ℂ) := by ring
  apply Complex.ext
  · dsimp [cycleBase]
    simp [hcomm]
    have hre0 :
        (((1 - ((k : ℝ) + 1)⁻¹ : ℝ) • (1 : ℂ)).re) =
          (1 - ((k : ℝ) + 1)⁻¹) * 1 := by
      rw [Complex.smul_re]
      simp [smul_eq_mul]
    have hre1 :
        ((((k : ℝ) + 1)⁻¹ : ℝ) • Complex.exp (Complex.I * (s : ℂ))).re =
          ((k : ℝ) + 1)⁻¹ * (Complex.exp (Complex.I * (s : ℂ))).re := by
      rw [Complex.smul_re]
      simp [smul_eq_mul]
    exact calc
      ((1 - ((k : ℝ) + 1)⁻¹ : ℝ) • (1 : ℂ)).re +
          ((((k : ℝ) + 1)⁻¹ : ℝ) • Complex.exp (Complex.I * (s : ℂ))).re
          = (1 - ((k : ℝ) + 1)⁻¹) * 1 +
              ((k : ℝ) + 1)⁻¹ * (Complex.exp (Complex.I * (s : ℂ))).re := by
              exact congrArg₂ (fun a b : ℝ => a + b) hre0 hre1
      _ = 1 - ((k : ℝ) + 1)⁻¹ +
              ((k : ℝ) + 1)⁻¹ * (Complex.exp (Complex.I * (s : ℂ))).re := by
              ring_nf
  · dsimp [cycleBase]
    simp [hcomm]
    have him0 :
        (((1 - ((k : ℝ) + 1)⁻¹ : ℝ) • (1 : ℂ)).im) =
          (1 - ((k : ℝ) + 1)⁻¹) * 0 := by
      rw [Complex.smul_im]
      simp [smul_eq_mul]
    have him1 :
        ((((k : ℝ) + 1)⁻¹ : ℝ) • Complex.exp (Complex.I * (s : ℂ))).im =
          ((k : ℝ) + 1)⁻¹ * (Complex.exp (Complex.I * (s : ℂ))).im := by
      rw [Complex.smul_im]
      simp [smul_eq_mul]
    exact calc
      ((1 - ((k : ℝ) + 1)⁻¹ : ℝ) • (1 : ℂ)).im +
          ((((k : ℝ) + 1)⁻¹ : ℝ) • Complex.exp (Complex.I * (s : ℂ))).im
          = (1 - ((k : ℝ) + 1)⁻¹) * 0 +
              ((k : ℝ) + 1)⁻¹ * (Complex.exp (Complex.I * (s : ℂ))).im := by
              exact congrArg₂ (fun a b : ℝ => a + b) him0 him1
      _ = ((k : ℝ) + 1)⁻¹ * (Complex.exp (Complex.I * (s : ℂ))).im := by
              ring_nf

lemma cycleCount_charFun (n : ℕ) (s : ℝ) :
    charFun ((cycleP n).map (cycleCount n)) s =
      ∏ i : Fin n, cycleBase i.1 (Complex.I * (s : ℂ)) := by
  change charFun ((Measure.pi fun i : Fin n => cycleBernoulliLaw i.1).map
      (fun p => ∑ i, p i)) s =
    ∏ i : Fin n, cycleBase i.1 (Complex.I * (s : ℂ))
  have h := congrFun (charFun_map_sum_pi_eq_prod
    (μ := fun i : Fin n => cycleBernoulliLaw i.1)) s
  rw [h]
  simp [cycleBernoulliLaw_charFun]

lemma cycleBase_ne_zero_of_abs_le_half {k : ℕ} {s : ℝ} (hs : |s| ≤ (1 / 2 : ℝ)) :
    cycleBase k (Complex.I * (s : ℂ)) ≠ 0 := by
  let p : ℝ := ((k : ℝ) + 1)⁻¹
  have hp_nonneg : 0 ≤ p := by
    dsimp [p]
    positivity
  have hp_le_one : p ≤ 1 := by
    dsimp [p]
    have hk_nonneg : (0 : ℝ) ≤ (k : ℝ) := by exact_mod_cast Nat.zero_le k
    exact inv_le_one_of_one_le₀ (by linarith : (1 : ℝ) ≤ (k : ℝ) + 1)
  have hdist : ‖(p : ℂ) * (Complex.exp (Complex.I * (s : ℂ)) - 1)‖ < 1 := by
    calc
      ‖(p : ℂ) * (Complex.exp (Complex.I * (s : ℂ)) - 1)‖
          = p * ‖Complex.exp (Complex.I * (s : ℂ)) - 1‖ := by
            rw [norm_mul, norm_real, Real.norm_eq_abs, abs_of_nonneg hp_nonneg]
      _ ≤ p * ‖s‖ := by
            gcongr
            simpa [mul_comm] using Real.norm_exp_I_mul_ofReal_sub_one_le (x := s)
      _ ≤ p * (1 / 2 : ℝ) := by
            gcongr
            simpa [Real.norm_eq_abs] using hs
      _ ≤ 1 * (1 / 2 : ℝ) := by
            gcongr
      _ < 1 := by norm_num
  have hbase :
      cycleBase k (Complex.I * (s : ℂ)) =
        1 + (p : ℂ) * (Complex.exp (Complex.I * (s : ℂ)) - 1) := by
    change (((1 - p : ℝ) : ℂ) + (p : ℂ) *
        Complex.exp (Complex.I * (s : ℂ))) =
      1 + (p : ℂ) * (Complex.exp (Complex.I * (s : ℂ)) - 1)
    rw [show ((1 - p : ℝ) : ℂ) = 1 - (p : ℂ) by norm_cast]
    ring
  rw [hbase]
  exact Complex.slitPlane_ne_zero (Complex.mem_slitPlane_of_norm_lt_one hdist)

lemma cycle_hChar : ∃ s₀ > 0, ∀ n s, |s| ≤ s₀ →
    charFun ((cycleP n).map (cycleCount n)) s =
      Complex.exp ((cycleH n : ℂ) * (((1 : ℝ) : ℂ) * (Complex.I * (s : ℂ)) +
        ((1 : ℝ) : ℂ) * (Complex.I * (s : ℂ)) ^ 2 / 2 +
        cycleR n (Complex.I * (s : ℂ))) + (0 : ℂ)) := by
  refine ⟨(1 / 2 : ℝ), by norm_num, ?_⟩
  intro n s hs
  rw [cycleCount_charFun]
  by_cases hn : n = 0
  · subst n
    simp [cycleR, cycleH_zero]
  · let z : ℂ := Complex.I * (s : ℂ)
    have hbase : ∀ i : Fin n, cycleBase i.1 z ≠ 0 := fun i =>
      cycleBase_ne_zero_of_abs_le_half (k := i.1) (s := s) hs
    change (∏ i : Fin n, cycleBase i.1 z) =
      Complex.exp ((cycleH n : ℂ) * ((1 : ℂ) * z + (1 : ℂ) * z ^ 2 / 2 + cycleR n z) + 0)
    rw [cycleR, if_neg hn]
    have hH : (cycleH n : ℂ) ≠ 0 := cycleH_ne_zero hn
    rw [show (cycleH n : ℂ) * ((1 : ℂ) * z + (1 : ℂ) * z ^ 2 / 2 +
          ((∑ i : Fin n, Complex.log (cycleBase i.1 z)) - (cycleH n : ℂ) * cycleMain z) /
            (cycleH n : ℂ)) + 0 =
        ∑ i : Fin n, Complex.log (cycleBase i.1 z) by
      field_simp [hH]
      simp [cycleMain]
      ring_nf]
    rw [Complex.exp_sum]
    exact Finset.prod_congr rfl fun i _ => (Complex.exp_log (hbase i)).symm

lemma cycleH_tendsto_atTop : Tendsto cycleH atTop atTop := by
  have hlog : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hbounded :
      Tendsto (fun n : ℕ => cycleH n - Real.log (n : ℝ))
        atTop (𝓝 Real.eulerMascheroniConstant) := by
    simpa [cycleH] using Real.tendsto_harmonic_sub_log
  have hsum := hlog.atTop_add hbounded
  refine Tendsto.congr' ?_ hsum
  filter_upwards with n
  ring

/-- The Bernoulli success weight in the Feller cycle decomposition. -/
private def cycleW (k : ℕ) : ℝ :=
  ((k : ℝ) + 1)⁻¹

private lemma cycleW_nonneg (k : ℕ) : 0 ≤ cycleW k := by
  dsimp [cycleW]
  positivity

private lemma cycleW_le_one (k : ℕ) : cycleW k ≤ 1 := by
  dsimp [cycleW]
  have hk_nonneg : (0 : ℝ) ≤ (k : ℝ) := by exact_mod_cast Nat.zero_le k
  exact inv_le_one_of_one_le₀ (by linarith : (1 : ℝ) ≤ (k : ℝ) + 1)

private lemma cycleH_nonneg (n : ℕ) : 0 ≤ cycleH n := by
  by_cases hn : n = 0
  · simp [hn, cycleH_zero]
  · exact (cycleH_pos hn).le

private lemma cycleBase_eq_one_add_cycleW (k : ℕ) (z : ℂ) :
    cycleBase k z = 1 + (cycleW k : ℂ) * (Complex.exp z - 1) := by
  dsimp [cycleBase, cycleW]
  rw [show ((1 - ((k : ℝ) + 1)⁻¹ : ℝ) : ℂ) =
      1 - ((((k : ℝ) + 1)⁻¹ : ℝ) : ℂ) by norm_cast]
  ring

private lemma cycleW_sum_eq_cycleH_real (n : ℕ) :
    (∑ i : Fin n, cycleW i.1) = cycleH n := by
  rw [cycleH, harmonic]
  rw [Rat.cast_sum]
  rw [Finset.sum_fin_eq_sum_range]
  apply Finset.sum_congr rfl
  intro x hx
  simp [cycleW, Finset.mem_range.mp hx]

private lemma cycleW_sum_eq_cycleH_complex (n : ℕ) :
    (∑ i : Fin n, (cycleW i.1 : ℂ)) = (cycleH n : ℂ) := by
  rw [← cycleW_sum_eq_cycleH_real n]
  norm_cast

private lemma cycleW_sq_summable :
    Summable (fun k : ℕ => cycleW k ^ 2) := by
  have h := (Real.summable_one_div_nat_add_rpow 1 2).2 (by norm_num : (1 : ℝ) < 2)
  refine h.congr ?_
  intro k
  have hk : 0 < (k : ℝ) + 1 := by positivity
  rw [cycleW, abs_of_pos hk]
  field_simp [pow_two]
  rw [Real.rpow_two]

private lemma cycleW_sq_sum_le_tsum (n : ℕ) :
    (∑ i : Fin n, cycleW i.1 ^ 2) ≤ ∑' k : ℕ, cycleW k ^ 2 := by
  calc
    (∑ i : Fin n, cycleW i.1 ^ 2)
        = ∑ k ∈ Finset.range n, cycleW k ^ 2 := by
          rw [Finset.sum_fin_eq_sum_range]
          apply Finset.sum_congr rfl
          intro x hx
          simp [cycleW, Finset.mem_range.mp hx]
    _ ≤ ∑' k : ℕ, cycleW k ^ 2 := by
          exact cycleW_sq_summable.sum_le_tsum (Finset.range n)
            (fun i _hi => by positivity)

private lemma cycleW_sq_tsum_nonneg : 0 ≤ ∑' k : ℕ, cycleW k ^ 2 :=
  tsum_nonneg fun k => by positivity

private lemma norm_exp_sub_quadratic_le {z : ℂ} (hz : ‖z‖ ≤ 1) :
    ‖Complex.exp z - (1 + z + z ^ 2 / 2)‖ ≤ ‖z‖ ^ 3 := by
  have h := Complex.exp_bound (x := z) (n := 3) hz (by norm_num)
  have hsum (z : ℂ) :
      (∑ m ∈ Finset.range 3, z ^ m / (m.factorial : ℂ)) =
        1 + z + z ^ 2 / 2 := by
    norm_num [Finset.sum_range_succ, Nat.factorial]
  rw [hsum] at h
  have hconst : ((Nat.succ 3 : ℝ) * ((Nat.factorial 3 : ℝ) * (3 : ℝ))⁻¹) ≤ 1 := by
    norm_num [Nat.factorial]
  refine h.trans ?_
  calc
    ‖z‖ ^ 3 * ((Nat.succ 3 : ℝ) * ((Nat.factorial 3 : ℝ) * (3 : ℝ))⁻¹)
        ≤ ‖z‖ ^ 3 * 1 := by
          gcongr
    _ = ‖z‖ ^ 3 := by ring

private lemma norm_log_one_add_sub_self_sq {x : ℂ} (hx : ‖x‖ ≤ 1 / 2) :
    ‖Complex.log (1 + x) - x‖ ≤ ‖x‖ ^ 2 := by
  have hxlt : ‖x‖ < 1 := lt_of_le_of_lt hx (by norm_num)
  have h := Complex.norm_log_one_add_sub_self_le (z := x) hxlt
  have hinv : (1 - ‖x‖)⁻¹ ≤ (2 : ℝ) := by
    rw [inv_le_comm₀]
    · linarith
    · linarith
    · norm_num
  calc
    ‖Complex.log (1 + x) - x‖ ≤ ‖x‖ ^ 2 * (1 - ‖x‖)⁻¹ / 2 := h
    _ ≤ ‖x‖ ^ 2 * 2 / 2 := by gcongr
    _ = ‖x‖ ^ 2 := by ring

private lemma cycle_scaled_remainder_norm_le {n : ℕ} {z : ℂ}
    (hn : n ≠ 0) (hw : ‖Complex.exp z - 1‖ ≤ 1 / 2) :
    ‖(cycleH n : ℂ) * cycleR n z‖ ≤
      cycleH n * ‖Complex.exp z - 1 - z - z ^ 2 / 2‖ +
        (∑ i : Fin n, cycleW i.1 ^ 2) * ‖Complex.exp z - 1‖ ^ 2 := by
  let w : ℂ := Complex.exp z - 1
  let x : Fin n → ℂ := fun i => (cycleW i.1 : ℂ) * w
  have hscaled :
      (cycleH n : ℂ) * cycleR n z =
        (∑ i : Fin n, Complex.log (1 + x i)) - (cycleH n : ℂ) * cycleMain z := by
    rw [cycleR, if_neg hn]
    field_simp [cycleH_ne_zero hn]
    apply congrArg₂ (fun a b : ℂ => a - b) ?_ rfl
    apply Finset.sum_congr rfl
    intro i _hi
    rw [cycleBase_eq_one_add_cycleW]
  have hxsum : (∑ i : Fin n, x i) = (cycleH n : ℂ) * w := by
    calc
      (∑ i : Fin n, x i) = (∑ i : Fin n, (cycleW i.1 : ℂ) * w) := rfl
      _ = (∑ i : Fin n, (cycleW i.1 : ℂ)) * w := by rw [Finset.sum_mul]
      _ = (cycleH n : ℂ) * w := by rw [cycleW_sum_eq_cycleH_complex]
  have hlogsum :
      (∑ i : Fin n, Complex.log (1 + x i)) =
        (∑ i : Fin n, x i) + ∑ i : Fin n, (Complex.log (1 + x i) - x i) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _hi
    ring
  have hdecomp :
      (cycleH n : ℂ) * cycleR n z =
        (cycleH n : ℂ) * (w - z - z ^ 2 / 2) +
          ∑ i : Fin n, (Complex.log (1 + x i) - x i) := by
    rw [hscaled, hlogsum, hxsum]
    simp [cycleMain, w]
    ring
  have hxnorm (i : Fin n) : ‖x i‖ = cycleW i.1 * ‖w‖ := by
    simp [x, Real.norm_eq_abs, abs_of_nonneg (cycleW_nonneg i.1)]
  have hxhalf (i : Fin n) : ‖x i‖ ≤ 1 / 2 := by
    rw [hxnorm]
    calc
      cycleW i.1 * ‖w‖ ≤ 1 * (1 / 2 : ℝ) := by
        gcongr
        exact cycleW_le_one i.1
      _ = 1 / 2 := by ring
  have hlog_bound :
      ‖∑ i : Fin n, (Complex.log (1 + x i) - x i)‖ ≤
        (∑ i : Fin n, cycleW i.1 ^ 2) * ‖w‖ ^ 2 := by
    calc
      ‖∑ i : Fin n, (Complex.log (1 + x i) - x i)‖
          ≤ ∑ i : Fin n, ‖Complex.log (1 + x i) - x i‖ := norm_sum_le _ _
      _ ≤ ∑ i : Fin n, ‖x i‖ ^ 2 := by
            exact Finset.sum_le_sum fun i _hi => norm_log_one_add_sub_self_sq (hxhalf i)
      _ = (∑ i : Fin n, cycleW i.1 ^ 2) * ‖w‖ ^ 2 := by
            simp_rw [hxnorm]
            calc
              (∑ x : Fin n, (cycleW ↑x * ‖w‖) ^ 2)
                  = ∑ i : Fin n, cycleW i.1 ^ 2 * ‖w‖ ^ 2 := by
                    apply Finset.sum_congr rfl
                    intro i _hi
                    ring
              _ = (∑ i : Fin n, cycleW i.1 ^ 2) * ‖w‖ ^ 2 := by
                    rw [Finset.sum_mul]
  have hmain :
      ‖(cycleH n : ℂ) * (w - z - z ^ 2 / 2)‖ =
        cycleH n * ‖Complex.exp z - 1 - z - z ^ 2 / 2‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (cycleH_nonneg n)]
  rw [hdecomp]
  calc
    ‖(cycleH n : ℂ) * (w - z - z ^ 2 / 2) +
        ∑ i : Fin n, (Complex.log (1 + x i) - x i)‖
        ≤ ‖(cycleH n : ℂ) * (w - z - z ^ 2 / 2)‖ +
            ‖∑ i : Fin n, (Complex.log (1 + x i) - x i)‖ := norm_add_le _ _
    _ ≤ cycleH n * ‖Complex.exp z - 1 - z - z ^ 2 / 2‖ +
          (∑ i : Fin n, cycleW i.1 ^ 2) * ‖Complex.exp z - 1‖ ^ 2 := by
          exact add_le_add (le_of_eq hmain) hlog_bound

private lemma norm_qpZ_cycleH (n : ℕ) (t : ℝ) :
    ‖qpZ cycleH 1 n t‖ = |t| * (Real.sqrt (cycleH n))⁻¹ := by
  have hs : 0 ≤ Real.sqrt (cycleH n) := Real.sqrt_nonneg _
  simp [qpZ, Real.norm_eq_abs, abs_of_nonneg hs, mul_comm, mul_left_comm]

private lemma cycleH_mul_norm_qpZ_cube_tendsto_zero (t : ℝ) :
    Tendsto (fun n : ℕ => cycleH n * ‖qpZ cycleH 1 n t‖ ^ 3) atTop (𝓝 0) := by
  have hsqrt_atTop : Tendsto (fun n : ℕ => Real.sqrt (cycleH n)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp cycleH_tendsto_atTop
  have hinv : Tendsto (fun n : ℕ => (Real.sqrt (cycleH n))⁻¹) atTop (𝓝 (0 : ℝ)) :=
    tendsto_inv_atTop_zero.comp hsqrt_atTop
  have hlim : Tendsto
      (fun n : ℕ => |t| ^ 3 * (Real.sqrt (cycleH n))⁻¹) atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds (x := |t| ^ 3)).mul hinv
  refine Tendsto.congr' ?_ hlim
  filter_upwards [cycleH_tendsto_atTop.eventually (eventually_gt_atTop (0 : ℝ))] with n hn
  let s := Real.sqrt (cycleH n)
  have hs_ne : s ≠ 0 := Real.sqrt_ne_zero'.mpr hn
  have hsq : s ^ 2 = cycleH n := Real.sq_sqrt hn.le
  have hs_aux : cycleH n * s⁻¹ ^ 3 = s⁻¹ := by
    rw [← hsq]
    field_simp [hs_ne]
  rw [norm_qpZ_cycleH]
  change |t| ^ 3 * s⁻¹ = cycleH n * (|t| * s⁻¹) ^ 3
  calc
    |t| ^ 3 * s⁻¹ = |t| ^ 3 * (cycleH n * s⁻¹ ^ 3) := by rw [hs_aux]
    _ = cycleH n * (|t| * s⁻¹) ^ 3 := by ring

private theorem cycleR_scaled_tendsto_zero :
    ∀ t, Tendsto
      (fun n : ℕ => (cycleH n : ℂ) * cycleR n (qpZ cycleH 1 n t)) atTop (𝓝 0) := by
  intro t
  let C : ℝ := ∑' k : ℕ, cycleW k ^ 2
  let z : ℕ → ℂ := fun n => qpZ cycleH 1 n t
  have hz0 : Tendsto z atTop (𝓝 0) :=
    quasiPower_scaledArgument_tendsto_zero (β := cycleH) (u₂ := 1) (t := t)
      cycleH_tendsto_atTop (by norm_num)
  have hnormsq : Tendsto (fun n : ℕ => ‖z n‖ ^ 2) atTop (𝓝 0) := by
    simpa using (hz0.norm.pow 2)
  have hCnormsq : Tendsto (fun n : ℕ => (4 * C) * ‖z n‖ ^ 2) atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds (x := 4 * C)).mul hnormsq
  have hbound_tendsto :
      Tendsto (fun n : ℕ => cycleH n * ‖z n‖ ^ 3 + (4 * C) * ‖z n‖ ^ 2)
        atTop (𝓝 0) := by
    simpa [z] using (cycleH_mul_norm_qpZ_cube_tendsto_zero t).add hCnormsq
  refine squeeze_zero_norm' ?_ hbound_tendsto
  have hzsmall : ∀ᶠ n in atTop, ‖z n‖ < 1 / 4 := by
    exact (tendsto_zero_iff_norm_tendsto_zero.mp hz0).eventually
      (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 4))
  filter_upwards [
      cycleH_tendsto_atTop.eventually (eventually_gt_atTop (0 : ℝ)),
      hzsmall] with n hHpos hzlt
  have hn : n ≠ 0 := by
    intro hn
    subst n
    simp [cycleH_zero] at hHpos
  have hzle1 : ‖z n‖ ≤ 1 := by
    exact hzlt.le.trans (by norm_num : (1 / 4 : ℝ) ≤ 1)
  have hw : ‖Complex.exp (z n) - 1‖ ≤ 1 / 2 := by
    calc
      ‖Complex.exp (z n) - 1‖ ≤ 2 * ‖z n‖ := Complex.norm_exp_sub_one_le hzle1
      _ ≤ 2 * (1 / 4 : ℝ) := by gcongr
      _ = 1 / 2 := by norm_num
  have hraw := cycle_scaled_remainder_norm_le (n := n) (z := z n) hn hw
  have hHnonneg : 0 ≤ cycleH n := cycleH_nonneg n
  have hSnonneg : 0 ≤ ∑ i : Fin n, cycleW i.1 ^ 2 := by positivity
  have hCnonneg : 0 ≤ C := by
    dsimp [C]
    exact cycleW_sq_tsum_nonneg
  have hSleC : (∑ i : Fin n, cycleW i.1 ^ 2) ≤ C := by
    dsimp [C]
    exact cycleW_sq_sum_le_tsum n
  have hexp_quad :
      ‖Complex.exp (z n) - 1 - z n - z n ^ 2 / 2‖ ≤ ‖z n‖ ^ 3 := by
    convert norm_exp_sub_quadratic_le (z := z n) hzle1 using 1
    ring_nf
  have hw2 : ‖Complex.exp (z n) - 1‖ ^ 2 ≤ (2 * ‖z n‖) ^ 2 := by
    gcongr
    exact Complex.norm_exp_sub_one_le hzle1
  calc
    ‖(cycleH n : ℂ) * cycleR n (qpZ cycleH 1 n t)‖
        = ‖(cycleH n : ℂ) * cycleR n (z n)‖ := rfl
    _ ≤ cycleH n * ‖Complex.exp (z n) - 1 - z n - z n ^ 2 / 2‖ +
          (∑ i : Fin n, cycleW i.1 ^ 2) * ‖Complex.exp (z n) - 1‖ ^ 2 := hraw
    _ ≤ cycleH n * ‖z n‖ ^ 3 + (4 * C) * ‖z n‖ ^ 2 := by
          calc
            cycleH n * ‖Complex.exp (z n) - 1 - z n - z n ^ 2 / 2‖ +
                (∑ i : Fin n, cycleW i.1 ^ 2) * ‖Complex.exp (z n) - 1‖ ^ 2
                ≤ cycleH n * ‖z n‖ ^ 3 +
                    C * (2 * ‖z n‖) ^ 2 := by
                    gcongr
            _ = cycleH n * ‖z n‖ ^ 3 + (4 * C) * ‖z n‖ ^ 2 := by ring

lemma cycleCount_aemeasurable (n : ℕ) :
    AEMeasurable (cycleCount n) (cycleP n) := by
  unfold cycleCount cycleP
  exact Finset.aemeasurable_fun_sum _ fun i _ => (measurable_pi_apply i).aemeasurable

/--
Conditional quasi-powers CLT for the Feller coupling cycle-count model.

The only hypothesis is the scaled logarithmic remainder estimate at the
quasi-powers normalization points.
-/
theorem permutationCycles_tendstoInDistribution_gaussian_of_cycleR_tendsto
    (hR : ∀ t, Tendsto
      (fun n : ℕ => (cycleH n : ℂ) * cycleR n (qpZ cycleH 1 n t)) atTop (𝓝 0)) :
    AnalyticCombinatorics.Compatibility.TendstoInDistribution
      (fun n ω => (cycleCount n ω - cycleH n) / Real.sqrt (cycleH n)) atTop
      (fun x : ℝ => x) cycleP (gaussianReal 0 1) := by
  simpa using
    (quasiPowers_tendstoInDistribution_of_continuousAt
      (P := cycleP) (X := cycleCount) (β := cycleH)
      (u₁ := 1) (u₂ := 1) (R := cycleR) (V := fun _ : ℂ => 0)
      cycleCount_aemeasurable
      cycleH_tendsto_atTop
      (by norm_num : (0 : ℝ) < 1)
      continuousAt_const
      rfl
      cycle_hChar
      hR)

theorem permutationCycles_tendstoInDistribution_gaussian :
    AnalyticCombinatorics.Compatibility.TendstoInDistribution
      (fun n ω => (cycleCount n ω - cycleH n) / Real.sqrt (cycleH n)) atTop
      (fun x : ℝ => x) cycleP (gaussianReal 0 1) := by
  exact permutationCycles_tendstoInDistribution_gaussian_of_cycleR_tendsto
    cycleR_scaled_tendsto_zero

end LimitLaws
end Ch9
end AnalyticCombinatorics
end
end

/-!
# Towards the Feller → uniform-permutation cycle-count bridge

The Gaussian cycle CLT proved in `PermutationCycles.lean`
(`permutationCycles_tendstoInDistribution_gaussian`) is stated for the **Feller
coupling** `cycleP n = Measure.pi (Bernoulli(1/(k+1)))`, NOT for the genuine
uniform permutation measure `uniformPermMeasure n`.  To upgrade the result to a
*faithful* statement about uniform random permutations one needs the
**equidistribution bridge**: the total cycle count of a uniform random
permutation of `Fin n` has the same law (on `ℕ`) as `∑_{k=1}^n Bern(1/k)`.

Both laws have the same probability generating function

  `E[x^{Ncyc}] = ∏_{k=1}^n (x + k - 1)/k = x^{(n)} / n!`   (rising factorial / n!),

so equality of laws follows from the **rising-factorial cycle-count identity**

  `∑_{σ : Perm (Fin n)} x^{Ncyc(σ)} = ∏_{k=0}^{n-1} (x + k)`.

This file banks the *verified foundation* for that identity: the behaviour of the
number-of-cycles statistic `numC` under the `Equiv.Perm.decomposeOption`
bijection `Perm (Option α) ≃ Option α × Perm α`, which is the inductive engine of
the rising-factorial identity.  The "none-fixed" half of the recursion is proved
here in full (clean-3).  The remaining "splice/merge" half — and the assembly
into the generating identity, the char-function computation, and the
`IdentDistrib` transport of the Gaussian CLT — is documented as the open content.

`numC σ` is the genuine number of orbits (cycles, including fixed points) of `σ`:
`numC σ = (#α - #support σ) + (#nontrivial cycles of σ)`
        = (number of fixed points) + (number of nontrivial cycles).
-/

noncomputable section

open Equiv Equiv.Perm

namespace AnalyticCombinatorics
namespace Ch9
namespace LimitLaws
namespace PermCycleCountBridge

variable {α : Type*} [DecidableEq α] [Fintype α]

/-- `α` is equivalent to the non-`none` elements of `Option α`, via `some`. -/
def someSub (α : Type*) : α ≃ {o : Option α // o ≠ none} where
  toFun a := ⟨some a, by simp⟩
  invFun o := o.1.get (Option.ne_none_iff_isSome.mp o.2)
  left_inv a := by simp
  right_inv := by rintro ⟨(_ | a), h⟩ <;> simp at h ⊢

/-- `optionCongr` (extend a permutation of `α` to `Option α` fixing `none`)
is exactly the `extendDomain` along the `some`-subtype embedding.  This lets us
reuse Mathlib's `cycleType`/`support` lemmas for `extendDomain`. -/
lemma optionCongr_eq_extendDomain (σ : Perm α) :
    σ.optionCongr = σ.extendDomain (someSub α) := by
  ext o
  cases o with
  | none => simp [Equiv.Perm.extendDomain_apply_not_subtype]
  | some a =>
      rw [Equiv.Perm.extendDomain_apply_subtype σ (someSub α) (by simp)]
      simp [someSub]

/-- Extending a permutation to `Option α` (fixing `none`) preserves the cycle
type: no new nontrivial cycle is created. -/
lemma cycleType_optionCongr (σ : Perm α) :
    Equiv.Perm.cycleType (α := Option α) σ.optionCongr = σ.cycleType := by
  rw [optionCongr_eq_extendDomain, Equiv.Perm.cycleType_extendDomain]

/-- Extending a permutation to `Option α` (fixing `none`) preserves the support
cardinality. -/
lemma support_card_optionCongr (σ : Perm α) :
    (Equiv.Perm.support (α := Option α) σ.optionCongr).card = σ.support.card := by
  rw [optionCongr_eq_extendDomain]
  exact Equiv.Perm.card_support_extend_domain _

/-- The number of orbits (cycles, including fixed points) of `σ`:
`#fixed points + #nontrivial cycles = (#α - #support) + #cycleType`. -/
def numC (σ : Perm α) : ℕ :=
  (Fintype.card α - σ.support.card) + Multiset.card σ.cycleType

private lemma support_card_le (σ : Perm α) : σ.support.card ≤ Fintype.card α := by
  exact le_trans (Finset.card_le_card (Finset.subset_univ _)) (le_of_eq Finset.card_univ)

/-- **None-fixed half of the cycle-count recursion.**
Extending `σ` to `Option α` by adjoining `none` as a new fixed point creates
exactly one new cycle (the singleton `{none}`):
`numC (σ.optionCongr) = numC σ + 1`.

This is the `x`-coefficient half of the rising-factorial recursion
`∑_{Perm (Option α)} x^{numC} = (x + #α) · ∑_{Perm α} x^{numC}`
(the `+1` cycle multiplies the generating sum by the leading `x`). -/
theorem numC_optionCongr (σ : Perm α) :
    numC (σ.optionCongr : Perm (Option α)) = numC σ + 1 := by
  unfold numC
  rw [support_card_optionCongr]
  have hc : Fintype.card (Option α) = Fintype.card α + 1 := by simp
  rw [hc, cycleType_optionCongr]
  have hle := support_card_le σ
  omega

/-- **Splice/merge, fixed-point subcase.**
If `z` and `y` are *both* fixed points of `τ` (`z ≠ y`), then `swap z y` is
disjoint from `τ`, so `swap z y * τ` replaces the two singleton cycles `{z}, {y}`
by a single transposition: `cycleType (swap z y * τ) = {2} + τ.cycleType`.

In the cycle-count recursion this is the subcase where the inserted element `none`
lands on a *fixed point* `some a` of `optionCongr σ` (i.e. `σ a = a`): the two
fixed points `none`, `some a` merge into one 2-cycle, so the orbit count is
unchanged.  This half of the splice is fully proved (clean-3). -/
theorem cycleType_swap_mul_of_both_fixed (τ : Perm α) {z y : α}
    (hz : τ z = z) (hy : τ y = y) (hzy : z ≠ y) :
    (swap z y * τ).cycleType = {2} + τ.cycleType := by
  have hdis : Disjoint (swap z y) τ := by
    rw [Equiv.Perm.disjoint_iff_eq_or_eq]
    intro w
    by_cases hw : w = z
    · subst hw; right; exact hz
    · by_cases hw2 : w = y
      · subst hw2; right; exact hy
      · left; rw [Equiv.swap_apply_of_ne_of_ne hw hw2]
  rw [hdis.cycleType_mul, Equiv.Perm.IsCycle.cycleType (Equiv.Perm.isCycle_swap hzy),
    Equiv.Perm.card_support_swap hzy]

/-- **Cycle insertion (the converse of `Equiv.Perm.IsCycle.swap_mul`).**
If `c` is a cycle, `y ∈ c.support`, and `z ∉ c.support` with `z ≠ y`, then
`swap z y * c` is again a cycle whose support is `c.support` with `z` inserted
(right before `y`).  Mathlib supplies only the *splitting* direction
(`IsCycle.swap_mul`, which pops an element OUT of a cycle); this insertion
direction — needed for the cycle-MERGE half of the rising-factorial recursion —
is built here from the low-level `isCycle_swap_mul_aux₂` machinery via an explicit
`SameCycle` orbit-threading argument. -/
theorem isCycle_swap_mul_insert {c : Perm α} (hc : c.IsCycle) {z y : α}
    (hy : y ∈ c.support) (hz : z ∉ c.support) (hzy : z ≠ y) :
    (swap z y * c).IsCycle ∧ (swap z y * c).support = insert z c.support := by
  have hcz : c z = z := by simpa using hz
  have hcy : c y ≠ y := by simpa using hy
  set g : Perm α := swap z y * c with hg
  have hgz : g z = y := by simp [hg, hcz, swap_apply_left]
  -- For any w ∈ c.support, g w = c w unless w is the wraparound point c.symm y.
  have hgw : ∀ w : α, w ∈ c.support → w ≠ c.symm y → g w = c w := by
    intro w hw hwrap
    have hcw_mem : c w ∈ c.support := apply_mem_support.mpr hw
    have hcw_ne_z : c w ≠ z := by rintro rfl; exact hz hcw_mem
    have hcw_ne_y : c w ≠ y := by
      intro h; exact hwrap (by rw [← h, symm_apply_apply])
    simp [hg, swap_apply_of_ne_of_ne hcw_ne_z hcw_ne_y]
  -- forward step: g threads the c-orbit of y (wrapping z in before y)
  have hstep : ∀ k : ℕ, SameCycle g z ((c ^ k) y) := by
    intro k
    induction k with
    | zero => exact ⟨1, by simpa using hgz⟩
    | succ k ih =>
      by_cases hwrap : (c ^ k) y = c.symm y
      · have : (c ^ (k+1)) y = y := by
          rw [pow_succ', mul_apply, hwrap, apply_symm_apply]
        rw [this]; exact ⟨1, by simpa using hgz⟩
      · obtain ⟨n, hn⟩ := ih
        refine ⟨n + 1, ?_⟩
        have hmem : (c ^ k) y ∈ c.support := pow_apply_mem_support.mpr hy
        have hgck : g ((c ^ k) y) = (c ^ (k+1)) y := by
          rw [hgw _ hmem hwrap, pow_succ', mul_apply]
        calc (g ^ (n + 1)) z = g ((g ^ n) z) := by
                rw [add_comm, zpow_add, zpow_one, mul_apply]
          _ = g ((c ^ k) y) := by rw [hn]
          _ = (c ^ (k+1)) y := hgck
  have hsc : ∀ w : α, w ∈ c.support → SameCycle g z w := by
    intro w hw
    obtain ⟨k, hk⟩ := hc.exists_pow_eq hcy (by simpa using hw)
    rw [← hk]; exact hstep k
  have hsupp : g.support = insert z c.support := by
    ext w
    simp only [Finset.mem_insert]
    constructor
    · intro hwg
      by_cases hwz : w = z
      · left; exact hwz
      · right
        by_contra hwc
        rw [mem_support] at hwg
        have hcwfix : c w = w := by simpa using hwc
        apply hwg
        have hwy : w ≠ y := by rintro rfl; exact hcy hcwfix
        simp [hg, hcwfix, swap_apply_of_ne_of_ne hwz hwy]
    · intro hw
      rcases hw with rfl | hw
      · rw [mem_support, hgz]; exact (Ne.symm hzy)
      · rw [mem_support]
        intro hfix
        have hzw : z = w := (hsc w hw).eq_of_right (by simpa using hfix)
        rw [← hzw] at hw; exact hz hw
  refine ⟨⟨z, ?_, ?_⟩, hsupp⟩
  · rw [hgz]; exact (Ne.symm hzy)
  · intro v hv
    have hvmem : v ∈ g.support := mem_support.mpr hv
    rw [hsupp, Finset.mem_insert] at hvmem
    rcases hvmem with rfl | hvc
    · exact SameCycle.refl _ _
    · exact hsc v hvc

/-- **Splice/merge, nontrivial-cycle subcase (Wall 1, the crux).**
If `z` is a fixed point of `τ` and `y` lies in a *nontrivial* cycle of `τ`
(`y ∈ τ.support`), `z ≠ y`, then merging the singleton `{z}` into `y`'s cycle via
`swap z y * τ` leaves the *number* of cycles unchanged (the `y`-cycle is lengthened
to absorb `z`) while growing the support by one.  Proved by peeling `c := τ.cycleOf y`
off `τ` with `Disjoint.cycleType_mul` and applying `isCycle_swap_mul_insert`. -/
theorem merge_counts {τ : Perm α} {z y : α}
    (hz : τ z = z) (hy : y ∈ τ.support) (hzy : z ≠ y) :
    Multiset.card (swap z y * τ).cycleType = Multiset.card τ.cycleType ∧
      (swap z y * τ).support.card = τ.support.card + 1 := by
  classical
  set c : Perm α := τ.cycleOf y with hc_def
  have hc_mem : c ∈ τ.cycleFactorsFinset := cycleOf_mem_cycleFactorsFinset_iff.mpr hy
  have hc_cyc : c.IsCycle := isCycle_cycleOf _ (mem_support.mp hy)
  set τ' : Perm α := τ * c⁻¹ with hτ'_def
  have hdis : Disjoint τ' c := disjoint_mul_inv_of_mem_cycleFactorsFinset hc_mem
  have hτeq : τ = c * τ' := by
    rw [← hdis.commute.eq, hτ'_def, mul_assoc, inv_mul_cancel, mul_one]
  have hzτ : z ∉ τ.support := by simpa using hz
  have hy_c : y ∈ c.support := by
    rw [hc_def, mem_support_cycleOf_iff]; exact ⟨SameCycle.rfl, hy⟩
  have hz_c : z ∉ c.support := by
    rw [hc_def, mem_support_cycleOf_iff]
    rintro ⟨hsame, _⟩
    exact hzy (hsame.eq_of_right (by simpa using hz)).symm
  have hcz : c z = z := by simpa using hz_c
  have hcinvz : c⁻¹ z = z := by
    rw [Equiv.Perm.inv_eq_iff_eq]; exact hcz.symm
  have hτ'z : τ' z = z := by rw [hτ'_def, mul_apply, hcinvz, hz]
  have hz_τ' : z ∉ τ'.support := by simpa using hτ'z
  obtain ⟨hgcyc, hgsupp⟩ := isCycle_swap_mul_insert hc_cyc hy_c hz_c hzy
  set g : Perm α := swap z y * c with hg_def
  have hsplit : swap z y * τ = g * τ' := by
    rw [hτeq, hg_def, ← mul_assoc]
  have hdis_g : Disjoint g τ' := by
    rw [disjoint_iff_disjoint_support, hgsupp, Finset.disjoint_insert_left]
    exact ⟨hz_τ', hdis.symm.disjoint_support⟩
  have hcard_ct : Multiset.card (swap z y * τ).cycleType = Multiset.card τ.cycleType := by
    rw [hsplit, hdis_g.cycleType_mul, hτeq, hdis.symm.cycleType_mul,
      Multiset.card_add, Multiset.card_add,
      hgcyc.cycleType, hc_cyc.cycleType, Multiset.card_singleton, Multiset.card_singleton]
  have hcard_supp : (swap z y * τ).support.card = τ.support.card + 1 := by
    rw [hsplit, hdis_g.card_support_mul, hgsupp, Finset.card_insert_of_notMem hz_c,
      hτeq, hdis.symm.card_support_mul]
    ring
  exact ⟨hcard_ct, hcard_supp⟩

/-- **numC merge identity.**  Merging a fixed point `z` of `τ` into the nontrivial
cycle through `y` (`y ∈ τ.support`) drops the orbit count by exactly one:
`numC (swap z y * τ) + 1 = numC τ` (the singleton orbit `{z}` is absorbed). -/
theorem numC_swap_mul_merge {τ : Perm α} {z y : α}
    (hz : τ z = z) (hy : y ∈ τ.support) (hzy : z ≠ y) :
    numC (swap z y * τ) + 1 = numC τ := by
  obtain ⟨hct, hsupp⟩ := merge_counts hz hy hzy
  unfold numC
  rw [hct, hsupp]
  have hle : (swap z y * τ).support.card ≤ Fintype.card α := support_card_le _
  rw [hsupp] at hle
  omega

/-- **numC, both-fixed splice.**  Merging two fixed points `z`, `y` of `τ` into a
single transposition via `swap z y * τ` drops the orbit count by one. -/
theorem numC_swap_mul_of_both_fixed (τ : Perm α) {z y : α}
    (hz : τ z = z) (hy : τ y = y) (hzy : z ≠ y) :
    numC (swap z y * τ) + 1 = numC τ := by
  have hct := cycleType_swap_mul_of_both_fixed τ hz hy hzy
  have hdis : Disjoint (swap z y) τ := by
    rw [Equiv.Perm.disjoint_iff_eq_or_eq]
    intro w
    by_cases hw : w = z
    · subst hw; right; exact hz
    · by_cases hw2 : w = y
      · subst hw2; right; exact hy
      · left; rw [Equiv.swap_apply_of_ne_of_ne hw hw2]
  have hsupp : (swap z y * τ).support.card = τ.support.card + 2 := by
    rw [hdis.card_support_mul, Equiv.Perm.card_support_swap hzy, add_comm]
  unfold numC
  rw [hct, hsupp]
  simp only [Multiset.card_add, Multiset.insert_eq_cons, Multiset.card_cons,
    Multiset.card_singleton]
  have hle : (swap z y * τ).support.card ≤ Fintype.card α := support_card_le _
  rw [hsupp] at hle
  omega

/-- **Per-term cycle-count under `decomposeOption.symm`.**
For `i : Option α` and `σ : Perm α`, the orbit count of
`decomposeOption.symm (i, σ) = swap none i * σ.optionCongr` is `numC σ` if `i ≠ none`
and `numC σ + 1` if `i = none` (a brand-new fixed point).  Case-split: `none`
(banked `numC_optionCongr`), `some a` with `σ a = a` (`numC_swap_mul_of_both_fixed`),
and `some a` with `σ a ≠ a` (the merge crux `numC_swap_mul_merge`). -/
theorem numC_decomposeOption_symm (i : Option α) (σ : Perm α) :
    numC (decomposeOption.symm (i, σ)) =
      if i = none then numC σ + 1 else numC σ := by
  rw [Equiv.Perm.decomposeOption_symm_apply]
  cases i with
  | none =>
    rw [if_pos rfl]
    rw [show swap (none : Option α) none * σ.optionCongr = σ.optionCongr from by
      rw [swap_self]; simp]
    exact numC_optionCongr σ
  | some a =>
    simp only [if_neg (by simp : (some a : Option α) ≠ none)]
    have hnone : (σ.optionCongr) none = none := by simp
    have hzy : (none : Option α) ≠ some a := by simp
    by_cases ha : σ a = a
    · have hsa : (σ.optionCongr) (some a) = some a := by simp [ha]
      have h1 := numC_swap_mul_of_both_fixed (σ.optionCongr) hnone hsa hzy
      have h2 := numC_optionCongr σ
      omega
    · have hmem : (some a) ∈ Equiv.Perm.support (σ.optionCongr : Perm (Option α)) := by
        rw [Equiv.Perm.mem_support]; simp [ha]
      have h1 := numC_swap_mul_merge (τ := σ.optionCongr) (z := none) (y := some a)
        hnone hmem hzy
      have h2 := numC_optionCongr σ
      omega

/-- The cycle-count generating polynomial of `Perm α`:
`cycleGen R x α = ∑_{σ : Perm α} x^{numC σ}`. -/
def cycleGen (R : Type*) [CommRing R] (x : R) (α : Type*) [DecidableEq α] [Fintype α] : R :=
  ∑ σ : Perm α, x ^ numC σ

/-- **Rising-factorial recursion.**
`∑_{e : Perm (Option α)} x^{numC e} = (x + #α) · ∑_{σ : Perm α} x^{numC σ}`.
Reindex `Perm (Option α)` by `decomposeOption`, split the product sum, and apply
`numC_decomposeOption_symm`: the `none` term contributes the leading `x`, each of
the `#α` `some a` terms contributes `1`. -/
theorem cycleGen_option (R : Type*) [CommRing R] (x : R) :
    cycleGen R x (Option α) = (x + Fintype.card α) * cycleGen R x α := by
  unfold cycleGen
  rw [← Equiv.sum_comp Equiv.Perm.decomposeOption.symm (fun e => x ^ numC e)]
  rw [Fintype.sum_prod_type]
  have hterm : ∀ i : Option α, ∀ σ : Perm α,
      x ^ numC (Equiv.Perm.decomposeOption.symm (i, σ)) =
        (if i = none then x ^ (numC σ + 1) else x ^ numC σ) := by
    intro i σ
    rw [numC_decomposeOption_symm]
    split <;> rfl
  simp_rw [hterm]
  rw [Fintype.sum_option]
  simp only [↓reduceIte, Option.some_ne_none]
  rw [add_mul]
  congr 1
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro σ _
    rw [pow_succ]; ring
  · rw [Finset.sum_const, Finset.card_univ]
    simp [nsmul_eq_mul]

/-- `numC` is invariant under transporting a permutation along a type equivalence. -/
theorem numC_permCongr {β : Type*} [DecidableEq β] [Fintype β]
    (e : α ≃ β) (σ : Perm α) : numC (e.permCongr σ) = numC σ := by
  have huniv : ∀ b : β, (fun _ : β => True) b := fun _ => trivial
  set f : α ≃ {b : β // (fun _ : β => True) b} :=
    e.trans (Equiv.subtypeUnivEquiv huniv).symm with hf
  have heq : e.permCongr σ = σ.extendDomain f := by
    ext b
    rw [Equiv.Perm.extendDomain_apply_subtype σ f (huniv b)]
    simp [hf, Equiv.permCongr_apply, Equiv.subtypeUnivEquiv]
  unfold numC
  rw [heq, Equiv.Perm.cycleType_extendDomain, Equiv.Perm.card_support_extend_domain,
    Fintype.card_congr e]

/-- `cycleGen` depends only on the cardinality (transports along equivalences). -/
theorem cycleGen_congr (R : Type*) [CommRing R] (x : R) {β : Type*} [DecidableEq β] [Fintype β]
    (e : α ≃ β) : cycleGen R x α = cycleGen R x β := by
  unfold cycleGen
  rw [← Equiv.sum_comp e.permCongr (fun τ => x ^ numC τ)]
  apply Finset.sum_congr rfl
  intro σ _
  rw [numC_permCongr]

/-- **Rising-factorial cycle-count identity.**
`∑_{σ : Perm (Fin n)} x^{numC σ} = ∏_{k=0}^{n-1} (x + k)`.
This is `∑_j #{σ : numC σ = j} x^j = x^{(n)}` (unsigned Stirling numbers of the
first kind as coefficients), the uniform-permutation side of the equidistribution
bridge.  Proved by induction on `n` from `cycleGen_option`. -/
theorem cycleGen_fin (R : Type*) [CommRing R] (x : R) (n : ℕ) :
    cycleGen R x (Fin n) = ∏ k ∈ Finset.range n, (x + k) := by
  induction n with
  | zero =>
    rw [Finset.prod_range_zero]
    unfold cycleGen
    rw [Fintype.sum_unique]
    simp [numC]
  | succ n ih =>
    rw [Finset.prod_range_succ, cycleGen_congr R x (finSuccEquiv n), cycleGen_option R x,
      ih, Fintype.card_fin]
    ring

/-- `fixedPointCount = #α − #support` (number of fixed points). -/
theorem fixedPointCount_eq (n : ℕ) (σ : Perm (Fin n)) :
    FixedPointsPoissonNS.fixedPointCount n σ = Fintype.card (Fin n) - σ.support.card := by
  classical
  unfold FixedPointsPoissonNS.fixedPointCount
  have hsupp : σ.support = Finset.univ.filter (fun i => ¬ σ i = i) := by
    ext i; simp [Equiv.Perm.mem_support]
  rw [Fintype.card_subtype, hsupp]
  have := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin n))) (p := fun i => σ i = i)
  rw [Finset.card_univ] at this
  omega

/-- The sum over `r ≥ 2` of `cycleType.count r` is the number of nontrivial cycles
(all cycle lengths lie in `[2, n]`). -/
theorem sum_cycleType_count_eq_card (n : ℕ) (σ : Perm (Fin n)) :
    ∑ r ∈ Finset.Icc 2 n, σ.cycleType.count r = Multiset.card σ.cycleType := by
  rw [← Multiset.toFinset_sum_count_eq σ.cycleType]
  symm
  apply Finset.sum_subset
  · intro r hr
    rw [Multiset.mem_toFinset] at hr
    rw [Finset.mem_Icc]
    refine ⟨two_le_of_mem_cycleType hr, ?_⟩
    calc r ≤ σ.support.card := le_card_support_of_mem_cycleType hr
      _ ≤ Fintype.card (Fin n) := Finset.card_le_univ _
      _ = n := Fintype.card_fin n
  · intro r _ hr
    rw [Multiset.mem_toFinset] at hr
    exact Multiset.count_eq_zero_of_notMem hr

/-- **Orbit count = per-length cycle-count sum.**
`numC σ = totalCycleCount n σ` for `σ : Perm (Fin n)`: the orbit-count statistic
`numC` (used in the rising-factorial identity) coincides with the repo's
`RCyclesPoissonNS.totalCycleCount = ∑_{r=1}^n rCycleCount n r`, the number of
orbits including fixed points.  This wires `cycleGen_fin` to the measure-theoretic
total cycle count. -/
theorem numC_eq_totalCycleCount (n : ℕ) (σ : Perm (Fin n)) :
    numC σ = RCyclesPoissonNS.totalCycleCount n σ := by
  unfold numC RCyclesPoissonNS.totalCycleCount
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    simp only [Finset.Icc_eq_empty_of_lt (by norm_num : (1:ℕ) > 0), Finset.Icc_self]
    simp [Subsingleton.elim σ 1]
  · have hsplit : Finset.Icc 1 n = insert 1 (Finset.Icc 2 n) := by
      ext r; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
    rw [hsplit, Finset.sum_insert (by simp)]
    rw [RCyclesPoissonNS.rCycleCount_one, fixedPointCount_eq]
    have hge2 : ∑ r ∈ Finset.Icc 2 n, RCyclesPoissonNS.rCycleCount n r σ
        = ∑ r ∈ Finset.Icc 2 n, σ.cycleType.count r := by
      apply Finset.sum_congr rfl
      intro r hr
      rw [Finset.mem_Icc] at hr
      rw [RCyclesPoissonNS.rCycleCount_eq_cycleType_count_of_ne_one (by omega)]
    rw [hge2, sum_cycleType_count_eq_card]

/-! ## The equidistribution bridge and the faithful uniform-permutation Gaussian CLT

We now finish the tail.  The remaining steps are purely the standard assembly:

1. compute the characteristic function of the law of `totalCycleCount` under
   `uniformPermMeasure` from the rising-factorial identity `cycleGen_fin`;
2. match it to the Feller `cycleCount_charFun`;
3. conclude `IdentDistrib` on `ℝ` via `Measure.ext_of_charFun`;
4. transport the banked Feller Gaussian CLT across the `IdentDistrib`.
-/

open MeasureTheory ProbabilityTheory Complex Filter

/-- Algebraic normalization of a single Feller factor:
`cycleBase k z = (exp z + k) / (k + 1)`. -/
theorem cycleBase_eq_div (k : ℕ) (z : ℂ) :
    cycleBase k z = (Complex.exp z + (k : ℂ)) / ((k : ℂ) + 1) := by
  have hk : ((k : ℂ) + 1) ≠ 0 := by
    have : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    have h2 : ((k : ℝ) + 1) ≠ 0 := by positivity
    exact_mod_cast h2
  rw [cycleBase]
  rw [show ((1 - ((k : ℝ) + 1)⁻¹ : ℝ) : ℂ) = 1 - (((k : ℝ) + 1 : ℝ) : ℂ)⁻¹ by push_cast; ring]
  rw [show ((((k : ℝ) + 1)⁻¹ : ℝ) : ℂ) = (((k : ℝ) + 1 : ℝ) : ℂ)⁻¹ by push_cast; ring]
  rw [show (((k : ℝ) + 1 : ℝ) : ℂ) = (k : ℂ) + 1 by push_cast; ring]
  field_simp
  ring

/-- The Feller characteristic-function product equals the rising-factorial product
divided by `n!`:
`∏_{i<n} cycleBase i z = (∏_{k<n} (exp z + k)) / n!`. -/
theorem prod_cycleBase_eq (n : ℕ) (z : ℂ) :
    (∏ i : Fin n, cycleBase i.1 z) =
      (∏ k ∈ Finset.range n, (Complex.exp z + (k : ℂ))) / (n.factorial : ℂ) := by
  rw [show (∏ i : Fin n, cycleBase i.1 z) = ∏ k ∈ Finset.range n, cycleBase k z from
    Fin.prod_univ_eq_prod_range (fun k => cycleBase k z) n]
  have hfac : (n.factorial : ℂ) = ∏ k ∈ Finset.range n, ((k : ℂ) + 1) := by
    induction n with
    | zero => simp
    | succ m ih =>
      rw [Finset.prod_range_succ, ← ih, Nat.factorial_succ]
      push_cast; ring
  rw [hfac, ← Finset.prod_div_distrib]
  apply Finset.prod_congr rfl
  intro k _
  rw [cycleBase_eq_div]

/-- The characteristic function of the law of `totalCycleCount` under the uniform
permutation measure, computed from the rising-factorial identity:
`charFun ((uniformPermMeasure n).map (totalCycleCount n)) s = ∏_{i<n} cycleBase i (I·s)`,
i.e. exactly the Feller `cycleCount_charFun`. -/
theorem uniform_totalCycleCount_charFun (n : ℕ) (s : ℝ) :
    charFun ((RCyclesPoissonNS.uniformPermMeasure n).map
        (fun σ => (RCyclesPoissonNS.totalCycleCount n σ : ℝ))) s =
      ∏ i : Fin n, cycleBase i.1 (Complex.I * (s : ℂ)) := by
  classical
  rw [charFun_apply_real]
  rw [integral_map (by exact (measurable_of_finite _).aemeasurable) (by fun_prop)]
  unfold RCyclesPoissonNS.uniformPermMeasure
  rw [PMF.integral_eq_sum]
  -- ∑_σ (1/card)·exp(s·(numC σ)·I) = (1/n!)·∑_σ (exp(I s))^{numC σ}
  have hterm : ∀ σ : Equiv.Perm (Fin n),
      (PMF.uniformOfFintype (Equiv.Perm (Fin n)) σ).toReal •
          Complex.exp ((s : ℂ) * ((RCyclesPoissonNS.totalCycleCount n σ : ℝ) : ℂ) * Complex.I)
        = ((n.factorial : ℝ)⁻¹ : ℝ) •
          (Complex.exp (Complex.I * (s : ℂ))) ^ numC σ := by
    intro σ
    rw [PMF.uniformOfFintype_apply, Fintype.card_perm, Fintype.card_fin]
    rw [ENNReal.toReal_inv, ENNReal.toReal_natCast]
    congr 1
    rw [numC_eq_totalCycleCount]
    rw [← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  calc
    (∑ σ : Equiv.Perm (Fin n),
        (PMF.uniformOfFintype (Equiv.Perm (Fin n)) σ).toReal •
          Complex.exp ((s : ℂ) *
            ((RCyclesPoissonNS.totalCycleCount n σ : ℝ) : ℂ) * Complex.I))
        = ∑ σ : Equiv.Perm (Fin n),
            ((n.factorial : ℝ)⁻¹ : ℝ) •
              (Complex.exp (Complex.I * (s : ℂ))) ^ numC σ :=
          Finset.sum_congr rfl (fun σ (_ : σ ∈ Finset.univ) => hterm σ)
    _ = ((n.factorial : ℝ)⁻¹ : ℝ) •
          cycleGen ℂ (Complex.exp (Complex.I * (s : ℂ))) (Fin n) := by
          rw [cycleGen]; exact Finset.smul_sum.symm
    _ = ((n.factorial : ℝ)⁻¹ : ℝ) •
          ∏ k ∈ Finset.range n, (Complex.exp (Complex.I * (s : ℂ)) + (k : ℂ)) := by
          rw [cycleGen_fin]
    _ = ∏ i : Fin n, cycleBase i.1 (Complex.I * (s : ℂ)) := by
          rw [prod_cycleBase_eq, real_smul]
          rw [show ((((n.factorial : ℝ)⁻¹ : ℝ)) : ℂ) = ((n.factorial : ℂ))⁻¹ by
            push_cast; ring]
          rw [div_eq_inv_mul]

/-- **The equidistribution bridge.**
The total cycle count of a uniform random permutation of `Fin n` is identically
distributed (on `ℝ`) to the Feller-coupling cycle count `∑_{k=1}^n Bern(1/k)`.
Equal characteristic functions (`uniform_totalCycleCount_charFun` = `cycleCount_charFun`)
imply equal laws by `Measure.ext_of_charFun`. -/
theorem identDistrib_totalCycleCount_cycleCount (n : ℕ) :
    IdentDistrib (fun σ => (RCyclesPoissonNS.totalCycleCount n σ : ℝ)) (cycleCount n)
      (RCyclesPoissonNS.uniformPermMeasure n) (cycleP n) where
  aemeasurable_fst := (measurable_of_finite _).aemeasurable
  aemeasurable_snd := cycleCount_aemeasurable n
  map_eq := by
    have hu : IsProbabilityMeasure
        ((RCyclesPoissonNS.uniformPermMeasure n).map
          (fun σ => (RCyclesPoissonNS.totalCycleCount n σ : ℝ))) :=
      Measure.isProbabilityMeasure_map (measurable_of_finite _).aemeasurable
    have hc : IsProbabilityMeasure ((cycleP n).map (cycleCount n)) :=
      Measure.isProbabilityMeasure_map (cycleCount_aemeasurable n)
    refine Measure.ext_of_charFun ?_
    funext s
    rw [uniform_totalCycleCount_charFun, cycleCount_charFun]

end PermCycleCountBridge
end LimitLaws
end Ch9
end AnalyticCombinatorics
end

open AnalyticCombinatorics AnalyticCombinatorics.Ch9 AnalyticCombinatorics.Ch9.LimitLaws AnalyticCombinatorics.Ch9.LimitLaws.PermCycleCountBridge
open Equiv Equiv.Perm
variable {α : Type*} [DecidableEq α] [Fintype α]
open MeasureTheory ProbabilityTheory Complex Filter
theorem solution :
    AnalyticCombinatorics.Compatibility.TendstoInDistribution
      (fun n (σ : Equiv.Perm (Fin n)) =>
        ((RCyclesPoissonNS.totalCycleCount n σ : ℝ) - cycleH n) / Real.sqrt (cycleH n))
      atTop (fun x : ℝ => x) RCyclesPoissonNS.uniformPermMeasure (gaussianReal 0 1) := by
  -- The standardizing map applied to each side.
  set g : ℕ → ℝ → ℝ := fun n x => (x - cycleH n) / Real.sqrt (cycleH n) with hg
  have hbridge := permutationCycles_tendstoInDistribution_gaussian
  refine ⟨?_, hbridge.aemeasurable_limit, ?_⟩
  · intro n
    exact (measurable_of_finite _).aemeasurable
  · -- per-`n` laws agree: pushforward of standardized totalCycleCount = pushforward
    -- of standardized cycleCount, via the IdentDistrib + continuity of `g n`.
    convert hbridge.tendsto using 2 with n
    apply Subtype.ext
    change (RCyclesPoissonNS.uniformPermMeasure n).map
        (fun σ => g n ((RCyclesPoissonNS.totalCycleCount n σ : ℝ)))
      = (cycleP n).map (fun ω => g n (cycleCount n ω))
    have hid := identDistrib_totalCycleCount_cycleCount n
    have hmeas : Measurable (g n) := by
      simp only [hg]; fun_prop
    have h1 := (hid.comp hmeas).map_eq
    simpa [Function.comp] using h1
