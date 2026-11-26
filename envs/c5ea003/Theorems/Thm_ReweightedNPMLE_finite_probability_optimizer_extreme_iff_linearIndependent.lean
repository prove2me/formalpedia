-- Prove2me | Theorems.Thm_ReweightedNPMLE_finite_probability_optimizer_extreme_iff_linearIndependent
-- name    : ReweightedNPMLE.finite_probability_optimizer_extreme_iff_linearIndependent
-- status  : Proved
-- author  : @Hansheng Jiang
-- created : 2026-11-26T03:39:03.942299+00:00
-- url     : https://prove2.me/theorems/efc2ec39-4716-4e55-9ef6-b419d6f69873
-- title:
--   Extremality of a finite likelihood optimizer is equivalent to evaluation independence
-- statement:
--   Let $\Theta$ be a compact metric Borel space, $n\ge1$, and $A:\Theta\to\mathbb R^n$ continuous. Choose distinct locations $\theta_j$ with positive evaluation vectors, and strictly positive coefficients $p_j$ summing to one. Set $\mu=\sum_jp_j\delta_{\theta_j}$ and $v=\sum_jp_jA(\theta_j)$, with $v_i>0$. Suppose $w_i>0$ and $v$ maximizes $\sum_iw_i\log u_i$ over $\operatorname{conv}\{A(\theta_j)\}$. Then
--   $$
--   \mu\in\operatorname{ext}\left\{\nu\in\mathcal P(\Theta):\int A\,d\nu=v\right\}
--   \quad\Longleftrightarrow\quad
--   \{A(\theta_j)\}_{j=1}^m\text{ is linearly independent}.
--   $$
--   The optimization hypothesis concerns the listed finite dictionary; extremality concerns the full probability-measure fiber.
--
--   This equivalence links the geometry of likelihood contact vectors to actual extremality of the represented mixing law.
-- source:
--   https://github.com/hanshengjiang/reweighted-npmle-lean/blob/5af8d16822c5a8a3f032b13eb95daea40f307484/ReweightedNPMLE/FiniteProbabilityExtreme.lean#L222-L244

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Convex.Caratheodory
import Mathlib.Analysis.Convex.Extreme
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.KreinMilman
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Data.Fin.Embedding
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Measure.Dirac
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.Tactic
import Mathlib.Topology.Order.Compact
import Definitions.Def_ReweightedNPMLE_CompactConvexHull
import Definitions.Def_ReweightedNPMLE_FiniteOptimizerFiber
import Definitions.Def_ReweightedNPMLE_FittedContact
import Definitions.Def_ReweightedNPMLE_ProbabilityFiberGeometry
import Definitions.Def_ReweightedNPMLE_ProbabilityOptimizerFiber
import Definitions.Def_ReweightedNPMLE_Weights

/-!
# Independent finite mixing laws are full-fiber extreme points

Finite-support representation and uniqueness are proved for arbitrary
probability measures concentrated on that finite support. Consequently,
an independent finite mixing law is extreme against decompositions into
arbitrary probability measures, not only against finite coefficient vectors.
-/

open Set MeasureTheory Filter
open scoped BigOperators Topology NNReal ENNReal

open ReweightedNPMLE

theorem ReweightedNPMLE.finite_probability_optimizer_extreme_iff_linearIndependent {Θ : Type*}
    [MetricSpace Θ] [CompactSpace Θ] [MeasurableSpace Θ] [BorelSpace Θ]
    {m n : ℕ} [Nonempty (Fin n)] (A : Θ → Fin n → ℝ) (hA : Continuous A)
    (θ : Fin m → Θ) (hθ : Function.Injective θ) (v : Fin n → ℝ)
    (p : Fin m → ℝ) (hp : p ∈ finiteMixtureFiber (A ∘ θ) v) (hpPos : ∀ j, 0 < p j)
    (w : Fin n → ℝ) (hw : ∀ i, 0 < w i) (hvpos : ∀ i, 0 < v i)
    (hApos : ∀ j i, 0 < A (θ j) i)
    (hvmax : IsMaxOn (convexHull ℝ (range (A ∘ θ))) (weightedLogLikelihood w) v) :
    IsExtremeProbabilityMixture A v (finiteProbabilityMeasure θ p hp.1) ↔
      LinearIndependent ℝ (A ∘ θ) := by sorry
