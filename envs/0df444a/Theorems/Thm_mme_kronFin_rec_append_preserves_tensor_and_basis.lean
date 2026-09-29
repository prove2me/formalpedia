-- Prove2me | Theorems.Thm_mme_kronFin_rec_append_preserves_tensor_and_basis
-- name    : mme_kronFin_rec_append_preserves_tensor_and_basis
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-27T06:08:49.903207+00:00
-- url     : https://prove2.me/theorems/2cefb2bf-7d01-4cb6-b507-8b951956bb6e
-- title:
--   Exact tensor and dependent-basis semantics of finite Kronecker concatenation
-- statement:
--   Let $A_0,\ldots,A_{m-1}$ and $B_0,\ldots,B_{n-1}$ be two heterogeneous tensor families. The canonical modewise reassociation sends their recursion-aligned flat product to the binary product of the two finite products:
--
--   $$
--   \bigotimes_{r<m+n} (A\mathbin{+\!+}B)_r
--   \;\cong\;
--   \left(\bigotimes_{r<m}A_r\right)\otimes
--   \left(\bigotimes_{r<n}B_r\right).
--   $$
--
--   The maps preserve the literal tensor. For arbitrary dependent bases on every factor, they also send each flat product-basis word exactly to the pure tensor of its left and right split product-basis words. Thus regrouping retains exact coordinate semantics, rather than only an abstract tensor isomorphism.
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Definition 5.2 and Claim 5.9 (regrouping Table-2 component positions); https://arxiv.org/abs/2210.10173

import Definitions.Def_mme_kronFin_rec_append_data

open MME PiTensorProduct TensorProduct Module

universe u

set_option autoImplicit false

theorem mme_kronFin_rec_append_preserves_tensor_and_basis
    {K : Type u} [Field K] {d : ℕ}
    (m n : ℕ) (A : Fin m → TensorObj K d)
    (B : Fin n → TensorObj K d) :
    PiTensorProduct.map
        (fun i ↦
          (MME.TensorObj.kronFinRecAppendModeEquiv m n A B i).toLinearMap)
        (TensorObj.kronFin (MME.TensorObj.recAppendLength m n)
          (MME.TensorObj.recAppendFamily m n A B)).t =
      (TensorObj.kron (TensorObj.kronFin m A)
        (TensorObj.kronFin n B)).t ∧
    ∀ (i : Fin d) (indexA : Fin m → Type u)
      (indexB : Fin n → Type u)
      (bA : ∀ r, Basis (indexA r) K ((A r).V i))
      (bB : ∀ r, Basis (indexB r) K ((B r).V i))
      (w : ∀ r,
        MME.TensorObj.recAppendFamily m n indexA indexB r),
      MME.TensorObj.kronFinRecAppendModeEquiv m n A B i
          (TensorObj.kronFinModePiBasis
            (MME.TensorObj.recAppendLength m n)
            (MME.TensorObj.recAppendFamily m n A B) i
            (MME.TensorObj.recAppendBasisFamily m n A B i
              indexA indexB bA bB) w) =
        (TensorObj.kronFinModePiBasis m A i bA
          (MME.TensorObj.recAppendLeftWord w)) ⊗ₜ[K]
        (TensorObj.kronFinModePiBasis n B i bB
          (MME.TensorObj.recAppendRightWord w)) := by
  sorry
