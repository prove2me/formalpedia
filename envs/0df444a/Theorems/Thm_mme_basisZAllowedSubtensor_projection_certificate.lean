-- Prove2me | Theorems.Thm_mme_basisZAllowedSubtensor_projection_certificate
-- name    : mme_basisZAllowedSubtensor_projection_certificate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-26T07:20:18.069568+00:00
-- url     : https://prove2.me/theorems/e50ef454-71fb-45db-9509-d56507db08f4
-- title:
--   Certificate that an allowed-basis block projects only the Z mode
-- statement:
--   Let $T$ be an order-three tensor over a field, let $b_Z$ be a basis of its $Z$-mode space, and let $A$ be any predicate on the basis indices. Split the $Z$ basis into allowed and disallowed vectors, while putting every vector of the $X$ and $Y$ spaces into the selected class. If $T|_A$ denotes the all-selected block, then
--
--   $$
--   T|_A \leq T,\qquad X_A=X,\qquad Y_A=Y,\qquad Z_A=\operatorname{span}\{b_Z(a):A(a)\}.
--   $$
--
--   Thus $T|_A$ is obtained by one genuine linear projection in the $Z$ mode. In particular, it retains the shared $X$ and $Y$ variables instead of replacing the tensor by a direct sum of independently copied fine-address tensors. The statement includes the empty and full allowed sets without additional hypotheses.
--
--   This certificate is the reusable interface needed for the component tensor $T_{i,j,k}^{\otimes n}[\widetilde\alpha]$ in the DWZ standard form, where availability is imposed on small $Z$-words alone.
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Remark 5.1 and Definitions 5.2--5.4, PDF pp. 47--48 / printed pp. 46--47; https://arxiv.org/abs/2210.10173

import Definitions.Def_mme_basis_z_allowed_projection
import Definitions.Def_mme_tensor_rank

universe u

open MME Module

set_option autoImplicit false

theorem mme_basisZAllowedSubtensor_projection_certificate
    {K : Type u} [Field K]
    (T : TensorObj K 3) {ι : Type u}
    (bZ : Basis ι K (T.V 2)) (allowed : ι → Prop)
    [DecidablePred allowed] :
    TensorObj.Restrict (T.basisZAllowedSubtensor bZ allowed) T ∧
      (T.basisZAllowedGrading bZ allowed).classOf 0 0 = ⊤ ∧
      (T.basisZAllowedGrading bZ allowed).classOf 1 0 = ⊤ ∧
      (T.basisZAllowedGrading bZ allowed).classOf 2 0 =
        Submodule.span K (bZ '' {j | allowed j}) := by
  sorry
