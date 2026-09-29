-- Prove2me | Theorems.Thm_mme_basisZAllowed_blockSubtensor_inclusion_tensor
-- name    : mme_basisZAllowed_blockSubtensor_inclusion_tensor
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-26T10:24:49.01282+00:00
-- url     : https://prove2.me/theorems/04c0a679-2e02-4d18-a390-cd0102f8c2c5
-- title:
--   Exact inclusion equation for a basis-selected Z block
-- statement:
--   Let $T$ be an order-three tensor over a field $K$, let $b$ be a basis of its $Z$-mode, and let $A$ be a predicate selecting some $Z$-basis vectors. Form the two-class grading which leaves the $X$- and $Y$-modes whole and places the selected $Z$-basis vectors in grade zero. If $T_A$ is the all-zero block subtensor, then the canonical inclusions of its three mode spaces into those of $T$ satisfy
--
--   $$
--   \left(\bigotimes_{i=0}^{2}\iota_i\right)T_A
--   =
--   \left(\operatorname{id}_X\otimes\operatorname{id}_Y\otimes P_A\right)T,
--   $$
--
--   where $P_A(b_j)=b_j$ when $A(j)$ holds and $P_A(b_j)=0$ otherwise.
--
--   This gives the exact map-level inclusion equation for a basis-selected block, rather than only the existence of a tensor restriction. In the Duan--Wu--Zhou hole repair it identifies each broken standard object with the ambient standard tensor after retaining precisely its nonhole useful-block labels.
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Definition 5.7 and Claims 5.8--5.10, PDF pp. 49--50 / printed pp. 48--49; exact linear-algebra formalization of the broken-copy inclusion used before the common shuffle; https://arxiv.org/abs/2210.10173

import Definitions.Def_mme_basis_z_allowed_projection
import Definitions.Def_mme_block_subtensor

open MME Module DirectSum

universe u

set_option autoImplicit false

theorem mme_basisZAllowed_blockSubtensor_inclusion_tensor
    {K : Type u} [Field K]
    (T : TensorObj K 3) {ι : Type u}
    (bZ : Basis ι K (T.V 2)) (allowed : ι → Prop)
    [DecidablePred allowed] :
    let G := T.basisZAllowedGrading bZ allowed
    PiTensorProduct.map (fun i ↦ (G.classOf i 0).subtype)
        (G.blockSubtensor (fun _ ↦ 0)).t =
      PiTensorProduct.map
        (Function.update (fun _ ↦ LinearMap.id) 2
          (bZ.constr K (fun j ↦ if allowed j then bZ j else 0)))
        T.t := by
  sorry
