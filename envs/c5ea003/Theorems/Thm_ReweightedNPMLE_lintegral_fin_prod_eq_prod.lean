-- Prove2me | Theorems.Thm_ReweightedNPMLE_lintegral_fin_prod_eq_prod
-- name    : ReweightedNPMLE.lintegral_fin_prod_eq_prod
-- status  : Proved
-- author  : @Hansheng Jiang
-- created : 2026-11-26T03:40:04.264038+00:00
-- url     : https://prove2.me/theorems/4e30881f-66ba-44f0-a11b-88088edbd0d7
-- title:
--   Tonelli factorization for a finite product of nonnegative functions
-- statement:
--   For each $i=1,\ldots,n$, let $(E_i,\mu_i)$ be a sigma-finite measure space and let $f_i:E_i\to[0,\infty]$ be measurable. Then
--   $$
--   \int_{\prod_i E_i}\prod_i f_i(x_i)\,d\!\left(\bigotimes_i\mu_i\right)(x)
--   =
--   \prod_i\int_{E_i}f_i\,d\mu_i.
--   $$
--   These are nonnegative Lebesgue integrals with values in the extended nonnegative reals. No integrability or finiteness of the individual integrals is assumed. Different coordinates may use different spaces and measures; the formula also uses the usual unit value for an empty product.
-- source:
--   https://github.com/hanshengjiang/reweighted-npmle-lean/blob/5af8d16822c5a8a3f032b13eb95daea40f307484/ReweightedNPMLE/DirichletIndependence.lean#L119-L158

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

theorem ReweightedNPMLE.lintegral_fin_prod_eq_prod {n : ℕ} {E : Fin n → Type*}
    {mE : ∀ i, MeasurableSpace (E i)} {μ : (i : Fin n) → Measure (E i)}
    [∀ i, SigmaFinite (μ i)] (f : (i : Fin n) → E i → ENNReal)
    (hf : ∀ i, Measurable (f i)) :
    ∫⁻ x : (i : Fin n) → E i, ∏ i, f i (x i) ∂(Measure.pi μ) =
      ∏ i, ∫⁻ x, f i x ∂(μ i) := by sorry
