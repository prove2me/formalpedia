-- Prove2me | Theorems.Thm_mme_basisFinsetProjection_tensor_eq_sum_singleton
-- name    : mme_basisFinsetProjection_tensor_eq_sum_singleton
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-26T10:28:34.232647+00:00
-- url     : https://prove2.me/theorems/0759a943-e03c-47b0-a177-c38278b5e0fd
-- title:
--   Finite basis-label tensor projection is the sum of singleton projections
-- statement:
--   Let $T$ be an order-three tensor over a field $K$, let $b$ be a basis of its $Z$-mode, and let each basis index carry a label in a type $B$. For a finite label set $S\subseteq B$, let $P_S$ retain precisely the basis vectors whose labels lie in $S$, and let $P_{\{c\}}$ retain precisely those carrying the single label $c$. Then
--
--   $$
--   (\operatorname{id}_X\otimes\operatorname{id}_Y\otimes P_S)T
--   =
--   \sum_{c\in S}
--   (\operatorname{id}_X\otimes\operatorname{id}_Y\otimes P_{\{c\}})T.
--   $$
--
--   The theorem is a reusable exact decomposition of a basis-label projection into singleton tensor contributions. For the DWZ standard object, $B$ is the finite set of useful blocks and $S$ is one broken copys nonhole set, so it produces the exact block expansion consumed by the common shuffle and owner projection.
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Definition 5.7 and Claims 5.8--5.10, PDF pp. 49--50 / printed pp. 48--49; exact finite block decomposition underlying the broken-copy hole repair; https://arxiv.org/abs/2210.10173

import Definitions.Def_mme_basis_z_allowed_projection

open BigOperators Finset
open MME Module

universe u

set_option autoImplicit false

theorem mme_basisFinsetProjection_tensor_eq_sum_singleton
    {K : Type u} [Field K]
    (T : TensorObj K 3) {ι β : Type u} [DecidableEq β]
    (b : Basis ι K (T.V 2)) (label : ι → β) (blocks : Finset β) :
    PiTensorProduct.map
        (Function.update (fun _ ↦ LinearMap.id) 2
          (b.constr K (fun j ↦ if label j ∈ blocks then b j else 0))) T.t =
      ∑ block ∈ blocks,
        PiTensorProduct.map
          (Function.update (fun _ ↦ LinearMap.id) 2
            (b.constr K (fun j ↦ if label j = block then b j else 0))) T.t := by
  sorry
