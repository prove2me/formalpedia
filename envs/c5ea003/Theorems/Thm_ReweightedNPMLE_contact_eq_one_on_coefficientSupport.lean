-- Prove2me | Theorems.Thm_ReweightedNPMLE_contact_eq_one_on_coefficientSupport
-- name    : ReweightedNPMLE.contact_eq_one_on_coefficientSupport
-- status  : Proved
-- author  : @hansheng.jiang
-- created : 2026-11-26T03:36:54.934856+00:00
-- url     : https://prove2.me/theorems/df0d777f-84f4-52f2-9a15-60642a0df852
-- title:
--   Every active atom lies on the supporting contact hyperplane
-- statement:
--   Let $A_1,\ldots,A_m$ lie in a real vector space, let $p_i\ge0$ with $\sum_i p_i=1$, and set $v=\sum_i p_iA_i$. Let $b$ be a linear functional satisfying $b(v)=1$ and $b(A_i)\le1$ for every dictionary element. Then
--   $$p_i>0\quad\Longrightarrow\quad b(A_i)=1.$$
--   Thus every atom carrying positive mixture weight lies on the contact hyperplane, even though inactive dictionary elements may lie strictly below it. The statement is algebraic and does not require differentiability or a probabilistic interpretation.
-- source:
--   https://github.com/hanshengjiang/reweighted-npmle-lean/blob/5af8d16822c5a8a3f032b13eb95daea40f307484/ReweightedNPMLE/FiniteOptimizerFiber.lean#L394-L426

import Mathlib.Analysis.Convex.Extreme
import Mathlib.Analysis.Convex.KreinMilman
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.Tactic
import Definitions.Def_ReweightedNPMLE_FiniteOptimizerFiber

/-!
# Extreme finite mixture fibers

This file isolates the finite-dimensional core of the paper's optimizer-fiber
lemma.  A probability vector represents a finite mixing law.  If the
dictionary vectors indexed by its nonzero masses are linearly independent,
then that representation is an extreme point of the fiber of all probability
vectors with the same fitted value.
-/

open Set
open scoped BigOperators

open ReweightedNPMLE

theorem ReweightedNPMLE.contact_eq_one_on_coefficientSupport
    {m : ℕ} {E : Type*} [AddCommGroup E] [Module ℝ E]
    (A : Fin m → E) (v : E) (p : Fin m → ℝ) (b : E →ₗ[ℝ] ℝ)
    (hp : p ∈ finiteMixtureFiber A v) (hbv : b v = 1)
    (hbA : ∀ i, b (A i) ≤ 1) :
    ∀ i ∈ coefficientSupport p, b (A i) = 1 := by sorry
