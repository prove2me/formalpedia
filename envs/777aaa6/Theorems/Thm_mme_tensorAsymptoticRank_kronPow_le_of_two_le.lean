-- Prove2me | Theorems.Thm_mme_tensorAsymptoticRank_kronPow_le_of_two_le
-- name    : mme_tensorAsymptoticRank_kronPow_le_of_two_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-24T04:27:28.439783+00:00
-- url     : https://prove2.me/theorems/ae5c2f97-be19-4816-8541-b64bc60f9128
-- title:
--   Asymptotic-rank bound for Kronecker powers of order at least two
-- statement:
--   Let $K$ be a field, let $d\ge 2$, and let $X$ be an order-$d$ tensor over $K$. For every natural number $N$, asymptotic tensor rank satisfies
--
--   $$
--   \widetilde R\!\left(X^{\otimes N}\right)\le \widetilde R(X)^N.
--   $$
--
--   For positive $N$, this is the power law for asymptotic rank arising from Fekete convergence of the submultiplicative tensor-rank sequence. The theorem also includes the tensor-unit case $N=0$. It is the sound Kronecker-power interface needed by the Coppersmith–Winograd asymptotic-rank development.
-- source:
--   Wigderson and Zuiddam, Asymptotic spectra: theory, applications and extensions, arXiv:2212.11824, Definitions 2.5 and 2.8 and the associated Fekete power law for asymptotic rank.

import Definitions.Def_mme_tensor_rank
open MME
universe u

theorem mme_tensorAsymptoticRank_kronPow_le_of_two_le
    {K : Type u} [Field K] {d : ℕ} (hd : 1 < d)
    (X : TensorObj K d) (N : ℕ) :
    tensorAsymptoticRank (X.kronPow N) ≤ tensorAsymptoticRank X ^ N := by sorry
