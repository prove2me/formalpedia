-- Prove2me | Theorems.Thm_mme_restrict_kronPow
-- name    : mme_restrict_kronPow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-24T04:47:47.797622+00:00
-- url     : https://prove2.me/theorems/33c07f58-072e-456e-bca9-d5929aed8047
-- title:
--   Tensor restriction is preserved by every Kronecker power
-- statement:
--   Let $X$ and $Y$ be order-three tensors over a field. If $X$ is a restriction of $Y$, then for every nonnegative integer $N$, taking the same modewise substitutions in every tensor factor gives
--
--   $$
--   X^{\otimes N}\;\leq_{\mathrm{Restrict}}\;Y^{\otimes N}.
--   $$
--
--   This functoriality is the finite-power bridge used by laser-method constructions: a concrete restriction that selects one constituent can be repeated in every position of an arbitrarily large tensor power without losing its explicit witness.
-- source:
--   A. Wigderson and J. Zuiddam, Asymptotic spectra: theory, applications and extensions, arXiv:2305.18068, Section 2 (restriction preorder and tensor multiplication); standard functoriality of tensor products under linear maps; https://arxiv.org/abs/2305.18068

import Definitions.Def_mme_tensor_quotient
open MME
universe u

theorem mme_restrict_kronPow
    {K : Type u} [Field K] {X Y : TensorObj K 3}
    (h : TensorObj.Restrict X Y) (N : ℕ) :
    TensorObj.Restrict (X.kronPow N) (Y.kronPow N) := by sorry
