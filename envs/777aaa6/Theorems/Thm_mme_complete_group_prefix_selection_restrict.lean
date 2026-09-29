-- Prove2me | Theorems.Thm_mme_complete_group_prefix_selection_restrict
-- name    : mme_complete_group_prefix_selection_restrict
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-26T18:56:51.610009+00:00
-- url     : https://prove2.me/theorems/3c7a7d79-bd40-4912-ab16-ce140551e83b
-- title:
--   Select complete repair groups while preserving a source restriction
-- statement:
--   Let a finite family of $n$ tensor blocks restrict to a common source tensor, and suppose every block satisfies a pointwise certificate. For a positive group size $g$, retain the first $k g$ blocks, where $k$ is the integer quotient of $n$ by $g$. The selected blocks still restrict to the source and retain all pointwise certificates. Moreover, if a real lower bound $A$ satisfies $2g ≤ A ≤ n$, then $A/(2g) ≤ k$. Hence an incomplete final Hole-repair group can be discarded with exactly the explicit factor-two grouping loss.
-- source:
--   Finite grouping and incomplete-group deletion in Duan--Wu--Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Section 5.3, Corollary 5.11, and Equation (24), printed pp. 48--58; https://arxiv.org/abs/2210.10173

import Theorems.Thm_mme_bigAdd_prefix_restrict
import Theorems.Thm_mme_nat_complete_group_floor_real_lower

open MME BigOperators

universe u v

set_option autoImplicit false

theorem mme_complete_group_prefix_selection_restrict
    {K : Type u} [Field K] {d n : ℕ} {Item : Type v}
    (hd : 1 < d) (g : ℕ) (hg : 0 < g)
    (item : Fin n → Item) (Good : Item → Prop)
    (hgood : ∀ i, Good (item i))
    (X : Item → TensorObj K d) (T : TensorObj K d)
    (hsource : TensorObj.Restrict
      (TensorObj.bigAdd (fun i : Fin n ↦ X (item i))) T)
    (A : ℝ) (hlarge : 2 * (g : ℝ) ≤ A) (hlower : A ≤ (n : ℝ)) :
    ∃ (k : ℕ) (selected : Fin (k * g) → Item),
      (∀ r, Good (selected r)) ∧
      TensorObj.Restrict
        (TensorObj.bigAdd (fun r : Fin (k * g) ↦ X (selected r))) T ∧
      A / (2 * (g : ℝ)) ≤ (k : ℝ) := by
  sorry
