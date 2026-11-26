-- Prove2me | Theorems.Thm_ReweightedNPMLE_finiteMixtureFiber_extreme_of_augmented_linearIndepOn
-- name    : ReweightedNPMLE.finiteMixtureFiber_extreme_of_augmented_linearIndepOn
-- status  : Proved
-- author  : @hansheng.jiang
-- created : 2026-11-26T03:36:51.825799+00:00
-- url     : https://prove2.me/theorems/8576eb07-85e8-54a1-a406-b9632cde6110
-- title:
--   Affine independence of the active dictionary implies finite-fiber extremality
-- statement:
--   Let $A_1,\ldots,A_m$ lie in a real vector space $E$, and let $p$ be a probability vector with $\sum_i p_iA_i=v$. If the augmented vectors
--   $$(1,A_i)\in\mathbb R\times E,\qquad i\text{ with }p_i>0,$$
--   are linearly independent, then $p$ is an extreme point of the fiber of all probability vectors representing $v$. Equivalently, affine independence of the active dictionary suffices. The added coordinate records the total-mass constraint and makes this criterion applicable even when the unaugmented active vectors are linearly dependent.
-- source:
--   https://github.com/hanshengjiang/reweighted-npmle-lean/blob/5af8d16822c5a8a3f032b13eb95daea40f307484/ReweightedNPMLE/FiniteOptimizerFiber.lean#L164-L223

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

theorem ReweightedNPMLE.finiteMixtureFiber_extreme_of_augmented_linearIndepOn
    {m : ℕ} {E : Type*} [AddCommGroup E] [Module ℝ E]
    (A : Fin m → E) (v : E) (p : Fin m → ℝ)
    (hp : p ∈ finiteMixtureFiber A v)
    (hlin : LinearIndepOn ℝ (augmentedDictionary A)
      (coefficientSupport p : Set (Fin m))) :
    p ∈ (finiteMixtureFiber A v).extremePoints ℝ := by sorry
