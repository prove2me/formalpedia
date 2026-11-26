-- Prove2me | Theorems.Thm_ReweightedNPMLE_augmented_linearIndepOn_iff_of_contact
-- name    : ReweightedNPMLE.augmented_linearIndepOn_iff_of_contact
-- status  : Proved
-- author  : @Hansheng Jiang
-- created : 2026-11-26T03:36:25.009802+00:00
-- url     : https://prove2.me/theorems/788e241c-2c51-41d4-adf4-bc95043a2f3f
-- title:
--   Affine and linear independence coincide on a normalized contact hyperplane
-- statement:
--   Let $A_1,\ldots,A_m$ lie in a real vector space $E$, let $S$ be a set of active indices, and let $b:E\to\mathbb R$ be linear. Assume
--   $$b(A_i)=1\qquad(i\in S).$$
--   Then $(1,A_i)_{i\in S}$ is linearly independent in $\mathbb R\times E$ if and only if $(A_i)_{i\in S}$ is linearly independent in $E$. In other words, affine and ordinary linear independence agree for vectors on this contact hyperplane, whose defining functional takes the nonzero value one.
-- source:
--   https://github.com/hanshengjiang/reweighted-npmle-lean/blob/5af8d16822c5a8a3f032b13eb95daea40f307484/ReweightedNPMLE/FiniteOptimizerFiber.lean#L359-L392

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

theorem ReweightedNPMLE.augmented_linearIndepOn_iff_of_contact
    {m : ℕ} {E : Type*} [AddCommGroup E] [Module ℝ E]
    (A : Fin m → E) (S : Finset (Fin m)) (b : E →ₗ[ℝ] ℝ)
    (hcontact : ∀ i ∈ S, b (A i) = 1) :
    LinearIndepOn ℝ (augmentedDictionary A) (S : Set (Fin m)) ↔
      LinearIndepOn ℝ A (S : Set (Fin m)) := by sorry
