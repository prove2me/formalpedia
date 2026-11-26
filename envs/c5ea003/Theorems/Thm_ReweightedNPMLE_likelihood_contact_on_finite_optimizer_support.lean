-- Prove2me | Theorems.Thm_ReweightedNPMLE_likelihood_contact_on_finite_optimizer_support
-- name    : ReweightedNPMLE.likelihood_contact_on_finite_optimizer_support
-- status  : Proved
-- author  : @hansheng.jiang
-- created : 2026-11-26T03:37:42.432842+00:00
-- url     : https://prove2.me/theorems/ea1d3f2a-1841-5396-94ea-d5ba04aa7a53
-- title:
--   Every active atom of a finite likelihood optimizer lies on its contact hyperplane
-- statement:
--   Let $n\ge1$ and let $A_1,\ldots,A_m\in(0,\infty)^n$. Suppose $p_j\ge0$, $\sum_jp_j=1$, and $v=\sum_jp_jA_j$ has positive coordinates. For weights $w_i>0$, assume $v$ maximizes $\sum_iw_i\log u_i$ over $\operatorname{conv}\{A_1,\ldots,A_m\}$. Write $W=\sum_iw_i$ and $\Lambda(a)=W^{-1}\sum_iw_i a_i/v_i$. Then
--   $$
--   p_j\ne0\quad\Longrightarrow\quad \Lambda(A_j)=1.
--   $$
--   Zero-coefficient atoms need not satisfy equality. Distinctness of the dictionary atoms is not assumed.
--
--   The result places every atom used by an optimizing mixture on a common affine contact hyperplane, the geometric constraint that strengthens support and extremality arguments.
-- source:
--   https://github.com/hanshengjiang/reweighted-npmle-lean/blob/5af8d16822c5a8a3f032b13eb95daea40f307484/ReweightedNPMLE/FittedContact.lean#L125-L147

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Convex.Extreme
import Mathlib.Analysis.Convex.KreinMilman
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.Tactic
import Mathlib.Topology.Order.Compact
import Definitions.Def_ReweightedNPMLE_FiniteOptimizerFiber
import Definitions.Def_ReweightedNPMLE_FittedContact
import Definitions.Def_ReweightedNPMLE_Weights

/-!
# Likelihood contact hyperplanes

At a positive fitted-value maximizer, differentiating toward any other
feasible fitted vector gives the supporting hyperplane used in the paper's
extreme-optimizer argument.  This file proves that first-order statement and
packages its normalized linear functional.
-/

open Set
open scoped BigOperators

open ReweightedNPMLE

theorem ReweightedNPMLE.likelihood_contact_on_finite_optimizer_support
    {m n : ℕ} [Nonempty (Fin n)]
    (A : Fin m → Fin n → ℝ) (v : Fin n → ℝ) (p : Fin m → ℝ)
    (w : Fin n → ℝ) (hw : ∀ i, 0 < w i)
    (hp : p ∈ finiteMixtureFiber A v) (hvpos : ∀ i, 0 < v i)
    (hApos : ∀ j i, 0 < A j i)
    (hvmax : IsMaxOn (convexHull ℝ (Set.range A))
      (weightedLogLikelihood w) v) :
    ∀ j ∈ coefficientSupport p,
      likelihoodContactFunctional w v (A j) = 1 := by sorry
