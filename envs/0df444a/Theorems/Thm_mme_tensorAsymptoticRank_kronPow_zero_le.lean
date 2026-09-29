-- Prove2me | Theorems.Thm_mme_tensorAsymptoticRank_kronPow_zero_le
-- name    : mme_tensorAsymptoticRank_kronPow_zero_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-24T04:22:22.806255+00:00
-- url     : https://prove2.me/theorems/424972b0-1bb2-4ff9-b266-99483eedc033
-- title:
--   The zeroth Kronecker power has asymptotic rank at most one
-- statement:
--   For every order-$d$ tensor $X$, the zeroth Kronecker power is the tensor unit and has asymptotic rank at most one: $$\widetilde R(X^{\otimes 0})\le \widetilde R(X)^0=1.$$ The statement is valid in every tensor order, including the low-order cases not covered by the tensor-quotient Strassen preorder.
-- source:
--   Wigderson and Zuiddam, Asymptotic spectra: theory, applications and extensions, arXiv:2212.11824, Definitions 2.5 and 2.8.

import Definitions.Def_mme_tensor_rank
open MME
universe u

theorem mme_tensorAsymptoticRank_kronPow_zero_le
    {K : Type u} [Field K] {d : ℕ} (X : TensorObj K d) :
    tensorAsymptoticRank (X.kronPow 0) ≤ tensorAsymptoticRank X ^ 0 := by sorry
