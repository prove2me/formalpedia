-- Prove2me | solution 1 for ReweightedNPMLE.gammaEffectiveEvent_failure_bound
-- status  : ACCEPTED   (prove)
-- author  : @Hansheng Jiang
-- created : 2026-11-26T04:13:44.210713+00:00
-- url     : https://prove2.me/submissions/f89b30d6-38bb-42e3-8bee-4977e128b286

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Convex.Caratheodory
import Mathlib.Analysis.Convex.Extreme
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.KreinMilman
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Data.Fin.Embedding
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Sym.Card
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
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
import Definitions.Def_ReweightedNPMLE_CompactConvexHull
import Definitions.Def_ReweightedNPMLE_DirichletIndependence
import Definitions.Def_ReweightedNPMLE_FiniteOptimizerFiber
import Definitions.Def_ReweightedNPMLE_GammaEffectiveEvent
import Definitions.Def_ReweightedNPMLE_Gaussian
import Definitions.Def_ReweightedNPMLE_GaussianWidth
import Definitions.Def_ReweightedNPMLE_PolynomialMoments
import Definitions.Def_ReweightedNPMLE_Weights
import Theorems.Thm_ReweightedNPMLE_exists_submodule_directional_net
import Theorems.Thm_ReweightedNPMLE_gamma_max_coordinate_concentration
import Theorems.Thm_ReweightedNPMLE_gamma_projected_norm_tail_of_finite_net

-- Inline helpers preserved from ReweightedNPMLE.GammaProjection.
section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal NNReal

namespace ReweightedNPMLE













theorem card_mul_exp_neg_rank_log_five
    (Ncard r : ℕ) (q : ℝ) (hcard : Ncard ≤ 5 ^ r) :
    (Ncard : ℝ) * Real.exp (-((r : ℝ) * Real.log 5 + q)) ≤
      Real.exp (-q) := by
  have hcast : (Ncard : ℝ) ≤ (5 : ℝ) ^ r := by exact_mod_cast hcard
  calc
    (Ncard : ℝ) * Real.exp (-((r : ℝ) * Real.log 5 + q)) ≤
        (5 : ℝ) ^ r * Real.exp (-((r : ℝ) * Real.log 5 + q)) :=
      mul_le_mul_of_nonneg_right hcast (Real.exp_pos _).le
    _ = Real.exp ((r : ℝ) * Real.log 5) *
        Real.exp (-((r : ℝ) * Real.log 5 + q)) := by
      rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 5)]
    _ = Real.exp (-q) := by
      rw [← Real.exp_add]
      congr 1
      ring

theorem gamma_projected_norm_tail {n r : ℕ} {α q : ℝ}
    (hα : 0 < α) (hq : 0 < (r : ℝ) * Real.log 5 + q)
    (hscale : 4 * ((r : ℝ) * Real.log 5 + q) ≤ α)
    (V : Submodule ℝ (EuclideanSpace ℝ (Fin n)))
    (N : Finset (EuclideanSpace ℝ (Fin n)))
    (hNcard : N.card ≤ 5 ^ r)
    (hNunit : ∀ v ∈ N, ∑ i, (v i) ^ 2 ≤ 1)
    (hnet : ∀ y ∈ V, ∃ v ∈ N, v ∈ V ∧ ‖y‖ ≤ 2 * inner ℝ v y) :
    (gammaProductMeasure n α α).real {w |
      4 * Real.sqrt ((r : ℝ) * Real.log 5 + q) < Real.sqrt α *
        ‖V.starProjection (WithLp.toLp 2 (fun i ↦ w i - 1))‖} ≤
      Real.exp (-q) := by
  apply gamma_projected_norm_tail_of_finite_net hα hq hscale V N
    hNunit hnet
  exact card_mul_exp_neg_rank_log_five N.card r q hNcard

/-! ### A Euclidean half-net with the paper's `5 ^ r` cardinality bound -/









/-- The paper's projected Gamma concentration bound, requiring only a subspace rank bound. -/
theorem gamma_projected_norm_tail_of_finrank {n r : ℕ} {α q : ℝ}
    (hα : 0 < α) (hq : 0 < (r : ℝ) * Real.log 5 + q)
    (hscale : 4 * ((r : ℝ) * Real.log 5 + q) ≤ α)
    (V : Submodule ℝ (EuclideanSpace ℝ (Fin n)))
    (hrank : Module.finrank ℝ V ≤ r) :
    (gammaProductMeasure n α α).real {w |
      4 * Real.sqrt ((r : ℝ) * Real.log 5 + q) < Real.sqrt α *
        ‖V.starProjection (WithLp.toLp 2 (fun i ↦ w i - 1))‖} ≤
      Real.exp (-q) := by
  obtain ⟨N, hNcard, hNunit, hnet⟩ := exists_submodule_directional_net V hrank
  exact gamma_projected_norm_tail hα hq hscale V N hNcard hNunit hnet

end ReweightedNPMLE
end

/-!
# Common Gamma concentration and localization event

The projected-energy and maximum-coordinate bounds hold jointly with
failure probability at most `2 exp(-q)`.  Explicit scale conditions imply
all radial localization hypotheses and the sharp `alpha E <= 2` width
cost bound.
-/

open Set Filter MeasureTheory ProbabilityTheory Matrix
open scoped BigOperators Topology

open ReweightedNPMLE
open ReweightedNPMLE in
theorem solution {n r : ℕ} [Nonempty (Fin n)]
    {α q : ℝ} (hα : 0 < α) (hq : 1 ≤ q)
    (hαQ : 4 * effectiveQ n q ≤ α) (hαN : 4 * effectiveN r q ≤ α)
    (V : Submodule ℝ (EuclideanSpace ℝ (Fin n))) (hrank : Module.finrank ℝ V ≤ r) :
    (gammaProductMeasure n α α).real (gammaEffectiveEvent V r α q)ᶜ ≤ 2 * Real.exp (-q) := by
  letI : IsProbabilityMeasure (gammaMeasure α α) := isProbabilityMeasure_gammaMeasure hα hα
  letI : IsProbabilityMeasure (gammaProductMeasure n α α) := by
    dsimp [gammaProductMeasure]
    infer_instance
  have hn : 0 < (n : ℝ) := by exact_mod_cast Fin.pos_iff_nonempty.mpr inferInstance
  have hQ : 0 < effectiveQ n q := by
    have hn1 : 1 ≤ (n : ℝ) := by exact_mod_cast (show 1 ≤ n from Fin.pos_iff_nonempty.mpr inferInstance)
    have hl : 0 ≤ Real.log (2 * (n : ℝ)) := Real.log_nonneg (by linarith)
    dsimp [effectiveQ]
    linarith
  have hN : 0 < effectiveN r q := by
    have hl : 0 ≤ Real.log (5 : ℝ) := Real.log_nonneg (by norm_num)
    dsimp [effectiveN]
    positivity
  let t := 2 * Real.sqrt (effectiveQ n q / α)
  have htpos : 0 < t := by dsimp [t]; positivity
  have ht1 : t ≤ 1 := by
    have hh : effectiveQ n q / α ≤ 1 / 4 := (div_le_iff₀ hα).mpr (by linarith)
    have hs := Real.sq_sqrt (div_nonneg hQ.le hα.le)
    dsimp [t]
    nlinarith [Real.sqrt_nonneg (effectiveQ n q / α)]
  let E₁ : Set (Fin n → ℝ) := {w | ∃ i, |w i - 1| > t}
  let E₂ : Set (Fin n → ℝ) := {w | 4 * Real.sqrt (effectiveN r q) <
    Real.sqrt α * ‖V.starProjection (WithLp.toLp 2 (fun i ↦ w i - 1))‖}
  have h₁ : (gammaProductMeasure n α α).real E₁ ≤ Real.exp (-q) := by
    have hh := gamma_max_coordinate_concentration (n := n) hα htpos ht1
    have hsq : α * t ^ 2 / 4 = effectiveQ n q := by
      dsimp [t]
      rw [mul_pow, Real.sq_sqrt (div_nonneg hQ.le hα.le)]
      field_simp [hα.ne']
      norm_num
    have hneg : -α * t ^ 2 / 4 = -effectiveQ n q := by linarith [hsq]
    have heq : 2 * (n : ℝ) * Real.exp (-effectiveQ n q) = Real.exp (-q) := by
      dsimp [effectiveQ]
      rw [neg_add, Real.exp_add, Real.exp_neg (Real.log (2 * (n : ℝ))),
        Real.exp_log (by positivity : 0 < 2 * (n : ℝ))]
      field_simp
    simpa only [gammaProductMeasure, E₁, hneg, heq] using hh
  have h₂ : (gammaProductMeasure n α α).real E₂ ≤ Real.exp (-q) :=
    gamma_projected_norm_tail_of_finrank hα hN hαN V hrank
  have hcover : (gammaEffectiveEvent V r α q)ᶜ ⊆ E₁ ∪ E₂ := by
    intro w hw
    by_cases hc : ∀ i, |w i - 1| ≤ t
    · right
      exact lt_of_not_ge (fun hp ↦ hw ⟨hc, hp⟩)
    · left
      simpa only [E₁, mem_setOf_eq, not_forall, not_le] using hc
  calc
    (gammaProductMeasure n α α).real (gammaEffectiveEvent V r α q)ᶜ ≤
        (gammaProductMeasure n α α).real (E₁ ∪ E₂) := measureReal_mono hcover
    _ ≤ (gammaProductMeasure n α α).real E₁ + (gammaProductMeasure n α α).real E₂ :=
      measureReal_union_le E₁ E₂
    _ ≤ 2 * Real.exp (-q) := by linarith
