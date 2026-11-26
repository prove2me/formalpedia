-- Prove2me | Theorems.Thm_ReweightedNPMLE_finite_extreme_optimizer_weighted_tangent_finrank
-- name    : ReweightedNPMLE.finite_extreme_optimizer_weighted_tangent_finrank
-- status  : Proved
-- author  : @Hansheng Jiang
-- created : 2026-11-26T03:38:49.316025+00:00
-- url     : https://prove2.me/theorems/412e9111-0c29-4a28-84cc-5d7966cff275
-- title:
--   An extreme optimizer with full active support has tangent dimension k minus one
-- statement:
--   Let $k,n\ge1$, let $A_1,\ldots,A_k\in(0,\infty)^n$, and let $p$ be a strictly positive probability vector with $\sum_jp_jA_j=v>0$. Suppose $w_i>0$, $v$ maximizes $\sum_iw_i\log v_i$ over $\operatorname{conv}\{A_j\}$, and $p$ is an extreme point of its finite moment fiber. Define $$S=\left\{\left(\sqrt{w_i}\frac{\sum_jc_jA_{ji}}{v_i}\right)_i:\sum_jc_j=0\right\}.$$ Then $\dim S=k-1$. This identifies the number of independent support-sensitivity directions.
-- source:
--   https://github.com/hanshengjiang/reweighted-npmle-lean/blob/5af8d16822c5a8a3f032b13eb95daea40f307484/ReweightedNPMLE/SupportSensitivity.lean#L335-L355

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.Convex.Extreme
import Mathlib.Analysis.Convex.KreinMilman
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.InnerProductSpace.Subspace
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.Order.Filter.Finite
import Mathlib.Tactic
import Mathlib.Topology.Order.Compact
import Definitions.Def_ReweightedNPMLE_FiniteOptimizerFiber
import Definitions.Def_ReweightedNPMLE_FittedContact
import Definitions.Def_ReweightedNPMLE_FittedRegularity
import Definitions.Def_ReweightedNPMLE_SupportSensitivity
import Definitions.Def_ReweightedNPMLE_Weights

/-!
# Finite-support tangent directions

This file formalizes the algebraic half of the paper's matrix-sensitivity
lemma.  Mass-preserving perturbations of a `k`-atom optimizer form a
`(k - 1)`-dimensional coefficient space.  A linearly independent evaluation
dictionary maps that space injectively to relative fitted-value directions.
After the square-root weight scaling, these directions remain
`(k - 1)`-dimensional, are orthogonal to the square-root weight vector by the
likelihood contact equations, and admit an explicit orthonormal matrix.
-/

open Set
open scoped BigOperators Matrix

open ReweightedNPMLE

theorem ReweightedNPMLE.finite_extreme_optimizer_weighted_tangent_finrank
    {k n : ℕ} [Nonempty (Fin k)] [Nonempty (Fin n)]
    (A : Fin k → Fin n → ℝ) (v : Fin n → ℝ) (p : Fin k → ℝ)
    (w : Fin n → ℝ) (hw : ∀ i, 0 < w i)
    (hp : p ∈ finiteMixtureFiber A v) (hpfull : ∀ j, 0 < p j)
    (hvpos : ∀ i, 0 < v i) (hApos : ∀ j i, 0 < A j i)
    (hvmax : IsMaxOn (convexHull ℝ (Set.range A))
      (weightedLogLikelihood w) v)
    (hextreme : p ∈ (finiteMixtureFiber A v).extremePoints ℝ) :
    Module.finrank ℝ (weightedRelativeTangentSpace A v w) = k - 1 := by sorry
