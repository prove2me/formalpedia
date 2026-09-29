-- Prove2me | Theorems.Thm_mme_kronFin_rec_groups_preserves_tensor_and_basis
-- name    : mme_kronFin_rec_groups_preserves_tensor_and_basis
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-27T06:58:02.90517+00:00
-- url     : https://prove2.me/theorems/84ebc68d-29a6-4a73-818c-105713448306
-- title:
--   Exact tensor and basis semantics for grouping consecutive Kronecker fibers
-- statement:
--   Let tensor type $X_s$ occur $c_s$ times for each of finitely many labels $s$. The canonical recursive reassociation sends the flat consecutive product to the product of the individual grouped powers,
--
--   $$
--   \bigotimes_{s} \bigotimes_{r<c_s} X_s.
--   $$
--
--   It preserves the literal tensor. For arbitrary dependent bases, it also sends every flat product-basis word to the exact grouped word obtained by splitting at the prescribed fiber boundaries. This supplies coordinate-level, rather than merely isomorphism-level, regrouping for the fifteen DWZ Table-2 component powers.
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Definition 5.2, Claims 5.8--5.10, and the Table-2 component regrouping in Section 6.3; https://arxiv.org/abs/2210.10173

import Definitions.Def_mme_kronFin_rec_groups_data

open MME PiTensorProduct TensorProduct Module

universe u

set_option autoImplicit false

theorem mme_kronFin_rec_groups_preserves_tensor_and_basis
    {K : Type u} [Field K] {d : ℕ}
    (k : ℕ) (count : Fin k → ℕ)
    (X : Fin k → TensorObj K d) :
    PiTensorProduct.map
        (fun i ↦
          (MME.TensorObj.kronFinRecGroupsModeEquiv k count X i).toLinearMap)
        (TensorObj.kronFin (MME.TensorObj.recGroupLength k count)
          (MME.TensorObj.recGroupFamily k count X)).t =
      (TensorObj.kronFin k (fun s ↦
        TensorObj.kronFin (count s) (fun _ ↦ X s))).t ∧
    ∀ (i : Fin d) (index : Fin k → Type u)
      (b : ∀ s, Basis (index s) K ((X s).V i))
      (w : ∀ r,
        MME.TensorObj.recGroupFamily k count index r),
      MME.TensorObj.kronFinRecGroupsModeEquiv k count X i
          (TensorObj.kronFinModePiBasis
            (MME.TensorObj.recGroupLength k count)
            (MME.TensorObj.recGroupFamily k count X) i
            (MME.TensorObj.recGroupBasisFamily k count X i index b) w) =
        TensorObj.kronFinModePiBasis k
          (fun s ↦ TensorObj.kronFin (count s) (fun _ ↦ X s)) i
          (fun s ↦ TensorObj.kronFinModePiBasis (count s)
            (fun _ ↦ X s) i (fun _ ↦ b s))
          (MME.TensorObj.recGroupWord w) := by
  sorry
