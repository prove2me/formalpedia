-- Prove2me | Theorems.Thm_ReweightedNPMLE_pi_withDensity_prod_eq
-- name    : ReweightedNPMLE.pi_withDensity_prod_eq
-- status  : Proved
-- author  : @hansheng.jiang
-- created : 2026-11-26T03:40:47.084282+00:00
-- url     : https://prove2.me/theorems/b391a075-2b07-4975-89ed-76573b2e1349
-- title:
--   Density of a finite product of absolutely continuous measures
-- statement:
--   Let $(E_i,\mu_i)$, $i=1,\ldots,n$, be sigma-finite measure spaces, and let $f_i:E_i\to[0,\infty)$ be measurable and finite at every point. Define $\nu_i$ by $d\nu_i=f_i\,d\mu_i$. Then
--   $$
--   d\!\left(\bigotimes_i\nu_i\right)(x)
--   =
--   \left\{\prod_i f_i(x_i)\right\}
--   d\!\left(\bigotimes_i\mu_i\right)(x).
--   $$
--   Equivalently, forming a finite product commutes with weighting each coordinate measure by its density. No probability normalization is required. Pointwise finiteness of the densities ensures that the weighted coordinate measures remain sigma-finite.
-- source:
--   https://github.com/hanshengjiang/reweighted-npmle-lean/blob/5af8d16822c5a8a3f032b13eb95daea40f307484/ReweightedNPMLE/DirichletIndependence.lean#L160-L192

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

theorem ReweightedNPMLE.pi_withDensity_prod_eq {n : ℕ} {E : Fin n → Type*}
    {mE : ∀ i, MeasurableSpace (E i)} {μ : (i : Fin n) → Measure (E i)}
    [∀ i, SigmaFinite (μ i)] (f : (i : Fin n) → E i → ENNReal)
    (hf : ∀ i, Measurable (f i)) (hftop : ∀ i x, f i x ≠ ⊤) :
    Measure.pi (fun i ↦ (μ i).withDensity (f i)) =
      (Measure.pi μ).withDensity (fun x ↦ ∏ i, f i (x i)) := by sorry
