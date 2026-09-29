-- Prove2me | Theorems.Thm_mme_MMObj_rectangle_mask_cardinality_restriction
-- name    : mme_MMObj_rectangle_mask_cardinality_restriction
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-22T03:40:19.260526+00:00
-- url     : https://prove2.me/theorems/9896e681-543b-4a6a-aaf8-cf6c63ffc3f3
-- title:
--   A rectangular matrix mask retains a block with the selected cardinalities
-- statement:
--   Let $K$ be a field and $n,m,p$ be natural numbers. Choose sets $C$ of column indices among $n$ labels and $R$ of row indices among $p$ labels. In the third coordinate of $\langle n,m,p\rangle$, retain precisely the matrix units $e_{k,i}$ with $k\in R$ and $i\in C$, leaving the first two coordinates unchanged. The resulting projected tensor restricts to
--   $$\langle |C|,m,|R|\rangle.$$
--   Thus a rectangular shared-coordinate mask retains a matrix block of volume $|C|m|R|$. Empty selections and zero dimensions are allowed.
-- source:
--   Coordinate restriction along injective row and column enumerations, followed by commutation with the rectangular mask.

import Definitions.Def_mme_tensor_rank
import Definitions.Def_mme_permutation
import Mathlib.Tactic.FinCases

open MME PiTensorProduct Module BigOperators
universe u
set_option autoImplicit false

theorem mme_MMObj_rectangle_mask_cardinality_restriction
    {K : Type u} [Field K] (n m p : ℕ)
    (C : Fin n → Prop) (R : Fin p → Prop) [DecidablePred C] [DecidablePred R] :
    let P : ∀ i, (MMObj K n m p).V i →ₗ[K] (MMObj K n m p).V i :=
      Function.update (fun _ ↦ LinearMap.id) 2
        (LinearMap.pi (fun ki : Fin p × Fin n ↦
          if R ki.1 ∧ C ki.2 then LinearMap.proj ki else 0))
    TensorObj.Restrict
      (MMObj K (Fintype.card {i : Fin n // C i}) m (Fintype.card {k : Fin p // R k}))
      { MMObj K n m p with t := PiTensorProduct.map P (MMObj K n m p).t } := by sorry
