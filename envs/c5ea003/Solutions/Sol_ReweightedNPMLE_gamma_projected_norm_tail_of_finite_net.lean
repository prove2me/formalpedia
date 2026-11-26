-- Prove2me | solution 1 for ReweightedNPMLE.gamma_projected_norm_tail_of_finite_net
-- status  : ACCEPTED   (prove)
-- author  : @hansheng.jiang
-- created : 2026-11-26T04:11:26.921488+00:00
-- url     : https://prove2.me/submissions/a66be251-d827-47c8-9401-a594fafa905c

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Convex.Extreme
import Mathlib.Analysis.Convex.KreinMilman
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Data.Real.Sqrt
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Group.Arithmetic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.MeasureTheory.Measure.Tilted
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Probability.Distributions.Gamma
import Mathlib.Probability.Moments.ComplexMGF
import Mathlib.Tactic
import Mathlib.Topology.MetricSpace.CoveringNumbers
import Mathlib.Topology.Order.Compact
import Definitions.Def_ReweightedNPMLE_DirichletIndependence
import Definitions.Def_ReweightedNPMLE_FiniteOptimizerFiber
import Definitions.Def_ReweightedNPMLE_Weights
import Theorems.Thm_ReweightedNPMLE_exponential_markov_upper
import Theorems.Thm_ReweightedNPMLE_gamma_linear_mgf_le
import Theorems.Thm_ReweightedNPMLE_integrable_exp_mul_gammaMeasure

-- Inline helpers preserved from ReweightedNPMLE.GammaDistribution.
section
/-!
# Gamma moment generating function and coordinate tails

The paper uses shape--rate Gamma variables.  This file connects the scalar
logarithm inequalities in `GammaBounds` to mathlib's actual
`ProbabilityTheory.gammaMeasure`.
-/

open MeasureTheory Real Set
open ProbabilityTheory

namespace ReweightedNPMLE























/-- Integrability companion to `centered_gamma_mgf`. -/
theorem integrable_centered_gamma_exp {a t : ℝ} (ha : 0 < a) (ht : t < a) :
    Integrable (fun x ↦ Real.exp (t * (x - 1))) (gammaMeasure a a) := by
  have h := (integrable_exp_mul_gammaMeasure ha ha ht).const_mul (Real.exp (-t))
  apply h.congr
  exact Filter.Eventually.of_forall fun x ↦ by
    change Real.exp (-t) * Real.exp (t * x) = Real.exp (t * (x - 1))
    rw [← Real.exp_add]
    congr 1
    ring





















end ReweightedNPMLE
end

-- Inline helpers preserved from ReweightedNPMLE.GammaProjection.
section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal NNReal

namespace ReweightedNPMLE







theorem integrable_gamma_linear_exp {n : ℕ} {α lam : ℝ} (hα : 0 < α)
    (hlam : |lam| ≤ Real.sqrt α / 2) (v : Fin n → ℝ)
    (hv : ∑ i, v i ^ 2 ≤ 1) :
    Integrable (fun w ↦
      Real.exp (lam * Real.sqrt α * ∑ i, v i * (w i - 1)))
      (gammaProductMeasure n α α) := by
  letI : IsProbabilityMeasure (gammaMeasure α α) :=
    isProbabilityMeasure_gammaMeasure hα hα
  let t : Fin n → ℝ := fun i ↦ lam * Real.sqrt α * v i
  have hαsqrt : Real.sqrt α ^ 2 = α := Real.sq_sqrt hα.le
  have habsv (i : Fin n) : |v i| ≤ 1 := by
    have hi : v i ^ 2 ≤ ∑ j, v j ^ 2 :=
      Finset.single_le_sum (fun j _ ↦ sq_nonneg (v j)) (Finset.mem_univ i)
    have hi' := hi.trans hv
    nlinarith [abs_nonneg (v i), sq_abs (v i)]
  have htlt (i : Fin n) : t i < α := by
    have ht : |t i| ≤ α / 2 := by
      rw [show |t i| = |lam| * Real.sqrt α * |v i| by
        simp [t, abs_mul, abs_of_nonneg (Real.sqrt_nonneg α)]]
      calc
        |lam| * Real.sqrt α * |v i| ≤
            (Real.sqrt α / 2) * Real.sqrt α * |v i| := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hlam (Real.sqrt_nonneg α)) (abs_nonneg _)
        _ ≤ (Real.sqrt α / 2) * Real.sqrt α * 1 := by
          exact mul_le_mul_of_nonneg_left (habsv i) (by positivity)
        _ = Real.sqrt α ^ 2 / 2 := by ring
        _ = α / 2 := by rw [hαsqrt]
    have hi := le_abs_self (t i)
    linarith
  have hprod : Integrable
      (fun w : Fin n → ℝ ↦ ∏ i, Real.exp (t i * (w i - 1)))
      (Measure.pi (fun _ : Fin n ↦ gammaMeasure α α)) := by
    exact Integrable.fintype_prod fun i ↦
      integrable_centered_gamma_exp hα (htlt i)
  apply hprod.congr
  filter_upwards with w
  rw [← Real.exp_sum]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp [t]
  ring

theorem gamma_linear_upper_tail {n : ℕ} {α u : ℝ}
    (hα : 0 < α) (hu : 0 < u) (huα : u ≤ Real.sqrt α)
    (v : Fin n → ℝ) (hv : ∑ i, v i ^ 2 ≤ 1) :
    (gammaProductMeasure n α α).real
        {w | u ≤ Real.sqrt α * ∑ i, v i * (w i - 1)} ≤
      Real.exp (-u ^ 2 / 4) := by
  letI : IsProbabilityMeasure (gammaMeasure α α) :=
    isProbabilityMeasure_gammaMeasure hα hα
  letI : IsProbabilityMeasure (gammaProductMeasure n α α) := by
    dsimp [gammaProductMeasure]
    infer_instance
  let lam : ℝ := u / 2
  have hlam : 0 < lam := by dsimp [lam]; positivity
  have hlamBound : |lam| ≤ Real.sqrt α / 2 := by
    rw [abs_of_pos hlam]
    exact div_le_div_of_nonneg_right huα (by norm_num)
  let X : (Fin n → ℝ) → ℝ := fun w ↦
    Real.sqrt α * ∑ i, v i * (w i - 1)
  have hint : Integrable (fun w ↦ Real.exp (lam * X w))
      (gammaProductMeasure n α α) := by
    simpa [X, mul_assoc] using
      integrable_gamma_linear_exp hα hlamBound v hv
  have hmark := exponential_markov_upper (gammaProductMeasure n α α)
    X hlam hint (c := u)
  have hmgf := gamma_linear_mgf_le hα hlamBound v hv
  change (gammaProductMeasure n α α).real {w | u ≤ X w} ≤ _
  calc
    (gammaProductMeasure n α α).real {w | u ≤ X w} ≤
        Real.exp (-lam * u) *
          ∫ w, Real.exp (lam * X w) ∂gammaProductMeasure n α α := hmark
    _ ≤ Real.exp (-lam * u) * Real.exp (lam ^ 2) := by
      apply mul_le_mul_of_nonneg_left
      · simpa [X, mul_assoc] using hmgf
      · positivity
    _ = Real.exp (-u ^ 2 / 4) := by
      rw [← Real.exp_add]
      congr 1
      dsimp [lam]
      ring







/-! ### A Euclidean half-net with the paper's `5 ^ r` cardinality bound -/











end ReweightedNPMLE
end

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal NNReal

open ReweightedNPMLE
open ReweightedNPMLE in
theorem solution {n : ℕ} {α R q : ℝ}
    (hα : 0 < α) (hR : 0 < R) (hRα : 4 * R ≤ α)
    (V : Submodule ℝ (EuclideanSpace ℝ (Fin n)))
    (N : Finset (EuclideanSpace ℝ (Fin n)))
    (hNunit : ∀ v ∈ N, ∑ i, (v i) ^ 2 ≤ 1)
    (hnet : ∀ y ∈ V, ∃ v ∈ N, v ∈ V ∧ ‖y‖ ≤ 2 * inner ℝ v y)
    (hcard : (N.card : ℝ) * Real.exp (-R) ≤ Real.exp (-q)) :
    (gammaProductMeasure n α α).real {w |
      4 * Real.sqrt R < Real.sqrt α *
        ‖V.starProjection (WithLp.toLp 2 (fun i ↦ w i - 1))‖} ≤
      Real.exp (-q) := by
  letI : IsProbabilityMeasure (gammaMeasure α α) :=
    isProbabilityMeasure_gammaMeasure hα hα
  letI : IsProbabilityMeasure (gammaProductMeasure n α α) := by
    dsimp [gammaProductMeasure]
    infer_instance
  let μ := gammaProductMeasure n α α
  let E : ↥N → Set (Fin n → ℝ) := fun v ↦
    {w | 2 * Real.sqrt R ≤ Real.sqrt α *
      ∑ i, v.1 i * (w i - 1)}
  have hu : 0 < 2 * Real.sqrt R := mul_pos (by norm_num) (Real.sqrt_pos.2 hR)
  have huα : 2 * Real.sqrt R ≤ Real.sqrt α := by
    have hsqR := Real.sq_sqrt hR.le
    have hsqα := Real.sq_sqrt hα.le
    nlinarith [Real.sqrt_nonneg R, Real.sqrt_nonneg α]
  have hEtail (v : ↥N) : μ.real (E v) ≤ Real.exp (-R) := by
    have hv := hNunit v.1 v.2
    have htail := gamma_linear_upper_tail hα hu huα
      (fun i ↦ v.1 i) hv
    have hexp : -(2 * Real.sqrt R) ^ 2 / 4 = -R := by
      nlinarith [Real.sq_sqrt hR.le]
    rw [hexp] at htail
    change μ.real (E v) ≤ _
    simpa [μ, E] using htail
  have hsubset : {w : Fin n → ℝ |
      4 * Real.sqrt R < Real.sqrt α *
        ‖V.starProjection (WithLp.toLp 2 (fun i ↦ w i - 1))‖} ⊆
      ⋃ v : ↥N, E v := by
    intro w hwbad
    let X : EuclideanSpace ℝ (Fin n) :=
      WithLp.toLp 2 (fun i ↦ w i - 1)
    let y : EuclideanSpace ℝ (Fin n) := V.starProjection X
    have hyV : y ∈ V := V.starProjection_apply_mem X
    obtain ⟨v, hvN, hvV, hvbound⟩ := hnet y hyV
    let vs : ↥N := ⟨v, hvN⟩
    apply Set.mem_iUnion.mpr
    refine ⟨vs, ?_⟩
    change 2 * Real.sqrt R ≤ Real.sqrt α *
      ∑ i, v i * (w i - 1)
    have hvfix : V.starProjection v = v :=
      Submodule.starProjection_eq_self_iff.mpr hvV
    have hinner : inner ℝ v y = ∑ i, v i * (w i - 1) := by
      calc
        inner ℝ v y = inner ℝ v (V.starProjection X) := rfl
        _ = inner ℝ (V.starProjection v) X :=
          (V.inner_starProjection_left_eq_right v X).symm
        _ = inner ℝ v X := by rw [hvfix]
        _ = ∑ i, v i * (w i - 1) := by
          simp [X, PiLp.inner_apply, mul_comm]
    have hscaled := mul_le_mul_of_nonneg_left hvbound (Real.sqrt_nonneg α)
    change 4 * Real.sqrt R < Real.sqrt α * ‖y‖ at hwbad
    rw [hinner] at hscaled
    nlinarith
  calc
    μ.real {w : Fin n → ℝ |
        4 * Real.sqrt R < Real.sqrt α *
          ‖V.starProjection (WithLp.toLp 2 (fun i ↦ w i - 1))‖} ≤
        μ.real (⋃ v : ↥N, E v) := measureReal_mono hsubset (by finiteness)
    _ ≤ ∑ v : ↥N, μ.real (E v) := measureReal_iUnion_fintype_le _
    _ ≤ ∑ _v : ↥N, Real.exp (-R) := Finset.sum_le_sum fun v _ ↦ hEtail v
    _ = (N.card : ℝ) * Real.exp (-R) := by simp
    _ ≤ Real.exp (-q) := hcard
