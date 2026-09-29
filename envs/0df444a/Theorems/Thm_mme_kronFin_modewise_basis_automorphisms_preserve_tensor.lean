-- Prove2me | Theorems.Thm_mme_kronFin_modewise_basis_automorphisms_preserve_tensor
-- name    : mme_kronFin_modewise_basis_automorphisms_preserve_tensor
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-26T10:29:41.881035+00:00
-- url     : https://prove2.me/theorems/8ba19a01-5bd5-44c6-8988-55a9ff226969
-- title:
--   Finite Kronecker automorphisms preserve both the tensor and product basis action
-- statement:
--   Let $T_0,\ldots,T_{n-1}$ be order-$d$ tensors over a field $K$. Suppose every factor $T_r$ has mode automorphisms $E_{r,j}$ whose tensor product fixes $T_r$. Fix one mode $i$, a basis $b_r$ of that mode in every factor, and a permutation $p_r$ of each basis index set, with $E_{r,i}(b_{r,x})=b_{r,p_r(x)}$. Then there are mode automorphisms $F_j$ of the ordered finite Kronecker product such that
--
--   $$
--   \left(\bigotimes_jF_j\right)\left(\bigotimes_{r<n}T_r\right)
--   =
--   \bigotimes_{r<n}T_r,
--   $$
--
--   and on the canonical function-indexed product basis,
--
--   $$
--   F_i(B_w)=B_{r\mapsto p_r(w_r)}.
--   $$
--
--   This combines literal tensor preservation with an exact basis action in one common product automorphism. It is the reusable finite-product interface needed to assemble the fifteen componentwise position shuffles in the Duan--Wu--Zhou hole repair.
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Definition 5.7 and Claim 5.9, PDF pp. 49--50 / printed pp. 48--49; finite Kronecker-product functoriality used for the common within-component shuffle; https://arxiv.org/abs/2210.10173

import Definitions.Def_mme_CW_2376_address_block
import Definitions.Def_mme_TypeGrading_kron
import Definitions.Def_mme_kronFin_mode_pi_basis

open MME MME.TensorObj PiTensorProduct Module

universe u

set_option autoImplicit false

theorem mme_kronFin_modewise_basis_automorphisms_preserve_tensor
    {K : Type u} [Field K] {d n : ℕ}
    (T : Fin n → TensorObj K d) (i : Fin d)
    {index : Fin n → Type u}
    (b : ∀ r, Basis (index r) K ((T r).V i))
    (E : ∀ r j, (T r).V j ≃ₗ[K] (T r).V j)
    (p : ∀ r, Equiv.Perm (index r))
    (hEtensor : ∀ r,
      PiTensorProduct.map (fun j ↦ (E r j).toLinearMap) (T r).t =
        (T r).t)
    (hEb : ∀ r x, E r i (b r x) = b r (p r x)) :
    ∃ F : ∀ j,
        (TensorObj.kronFin n T).V j ≃ₗ[K]
          (TensorObj.kronFin n T).V j,
      PiTensorProduct.map (fun j ↦ (F j).toLinearMap)
          (TensorObj.kronFin n T).t =
        (TensorObj.kronFin n T).t ∧
      ∀ w : ∀ r, index r,
        F i (TensorObj.kronFinModePiBasis n T i b w) =
          TensorObj.kronFinModePiBasis n T i b
            (fun r ↦ p r (w r)) := by
  sorry
