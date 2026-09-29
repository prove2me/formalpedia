-- Prove2me | Theorems.Thm_mme_kronFin_adjacent_swap_equiv_preserves_tensor_and_basis
-- name    : mme_kronFin_adjacent_swap_equiv_preserves_tensor_and_basis
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-26T20:19:31.517591+00:00
-- url     : https://prove2.me/theorems/94b75e8b-a580-4825-9b4b-53cd92781ff7
-- title:
--   Ordinary adjacent permutation exactly regroups a heterogeneous Kronecker tensor
-- statement:
--   Let $s$ exchange two adjacent positions in a heterogeneous finite Kronecker product. There are modewise linear equivalences from the product whose factor family is $T\circ s$ to the original product. They carry the literal tensor to the original tensor and, for every dependent family of factor bases, send a product-basis word to its dependent reindexing along $s$. Hence the regrouping is exact at both tensor and coordinate level, rather than merely an abstract isomorphism class.
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Definition 5.2 and Claim 5.9 (component-position regrouping); https://arxiv.org/abs/2210.10173

import Theorems.Thm_mme_kronFin_adjacent_swap_preserves_tensor_and_basis
import Theorems.Thm_mme_finAdjacentSwapVector_eq_comp_swap
import Theorems.Thm_mme_kronFin_adjacent_swap_basis_word_semantics

open MME Module PiTensorProduct

universe u

set_option autoImplicit false

theorem mme_kronFin_adjacent_swap_equiv_preserves_tensor_and_basis
    {K : Type u} [Field K] {d n : ℕ}
    (T : Fin (n + 2) → TensorObj K d) (j : Fin (n + 1)) :
    let s : Equiv.Perm (Fin (n + 2)) :=
      Equiv.swap j.castSucc j.succ
    ∃ F : ∀ i : Fin d,
        (TensorObj.kronFin (n + 2) (fun r ↦ T (s r))).V i ≃ₗ[K]
          (TensorObj.kronFin (n + 2) T).V i,
      PiTensorProduct.map (fun i ↦ (F i).toLinearMap)
          (TensorObj.kronFin (n + 2) (fun r ↦ T (s r))).t =
        (TensorObj.kronFin (n + 2) T).t ∧
      ∀ (i : Fin d) (index : Fin (n + 2) → Type u)
        (b : ∀ r, Basis (index r) K ((T r).V i))
        (w : ∀ r, index (s r)),
        F i
            (TensorObj.kronFinModePiBasis (n + 2)
              (fun r ↦ T (s r)) i (fun r ↦ b (s r)) w) =
          TensorObj.kronFinModePiBasis (n + 2) T i b
            (Equiv.piCongrLeft index s w) := by
  sorry
