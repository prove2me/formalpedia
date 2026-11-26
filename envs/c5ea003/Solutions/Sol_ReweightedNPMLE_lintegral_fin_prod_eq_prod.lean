-- Prove2me | solution 1 for ReweightedNPMLE.lintegral_fin_prod_eq_prod
-- status  : ACCEPTED   (prove)
-- author  : @Hansheng Jiang
-- created : 2026-11-26T04:02:19.588292+00:00
-- url     : https://prove2.me/submissions/3b087014-5026-4356-93b8-7259c97bf518

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Convex.Extreme
import Mathlib.Analysis.Convex.KreinMilman
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Convex.StdSimplex
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
import Mathlib.MeasureTheory.Measure.Tilted
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Probability.Distributions.Gamma
import Mathlib.Probability.Moments.ComplexMGF
import Mathlib.Tactic
import Mathlib.Topology.Order.Compact
import Definitions.Def_ReweightedNPMLE_DirichletIndependence
import Definitions.Def_ReweightedNPMLE_FiniteOptimizerFiber
import Definitions.Def_ReweightedNPMLE_Weights

/-!
# Scale invariance behind Gamma--Dirichlet independence

The normalized Gamma vector is unchanged by a common positive rescaling.
This file first proves the corresponding exact scaling laws for scalar and
finite-product Gamma measures.  These are the measure-theoretic core of the
remaining independence statement in Proposition 2.1.
-/

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators

open ReweightedNPMLE
open ReweightedNPMLE in
/-- Finite-dimensional Tonelli factorization for nonnegative coordinate
products.  This complements mathlib's real/complex Bochner version. -/
theorem solution {n : ℕ} {E : Fin n → Type*}
    {mE : ∀ i, MeasurableSpace (E i)} {μ : (i : Fin n) → Measure (E i)}
    [∀ i, SigmaFinite (μ i)] (f : (i : Fin n) → E i → ENNReal)
    (hf : ∀ i, Measurable (f i)) :
    ∫⁻ x : (i : Fin n) → E i, ∏ i, f i (x i) ∂(Measure.pi μ) =
      ∏ i, ∫⁻ x, f i x ∂(μ i) := by
  induction n with
  | zero => simp
  | succ n ih =>
      calc
        _ = ∫⁻ x : E 0 × ((i : Fin n) → E (Fin.succ i)),
            f 0 x.1 * ∏ i : Fin n, f (Fin.succ i) (x.2 i)
            ∂((μ 0).prod (Measure.pi (fun i ↦ μ i.succ))) := by
          rw [((measurePreserving_piFinSuccAbove μ 0).symm).lintegral_map_equiv]
          simp_rw [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
            Fin.prod_univ_succ, Fin.insertNth_zero, Equiv.coe_fn_mk, Fin.cons_succ,
            Fin.zero_succAbove, cast_eq, Fin.cons_zero]
          rfl
        _ = (∫⁻ x, f 0 x ∂μ 0) *
            ∏ i : Fin n, ∫⁻ x, f (Fin.succ i) x ∂(μ (Fin.succ i)) := by
          rw [lintegral_prod _ (by fun_prop)]
          have htail : Measurable
              (fun y : (i : Fin n) → E i.succ ↦ ∏ i, f i.succ (y i)) := by
            fun_prop
          calc
            (∫⁻ x : E 0, ∫⁻ y : (i : Fin n) → E i.succ,
                f 0 x * ∏ i, f i.succ (y i) ∂Measure.pi (fun i ↦ μ i.succ) ∂μ 0) =
                ∫⁻ x : E 0, f 0 x *
                  (∫⁻ y : (i : Fin n) → E i.succ, ∏ i, f i.succ (y i)
                    ∂Measure.pi (fun i ↦ μ i.succ)) ∂μ 0 := by
              apply lintegral_congr
              intro x
              exact lintegral_const_mul (f 0 x) htail
            _ = (∫⁻ x, f 0 x ∂μ 0) *
                ∏ i : Fin n, ∫⁻ x, f i.succ x ∂μ i.succ := by
              rw [ih (fun i ↦ f i.succ) (fun i ↦ hf i.succ)]
              exact lintegral_mul_const _ (hf 0)
        _ = ∏ i, ∫⁻ x, f i x ∂(μ i) := by rw [Fin.prod_univ_succ]
