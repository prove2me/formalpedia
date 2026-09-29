-- Prove2me | Theorems.Thm_mme_HasTauValueAtLeast_zero_tensor_iff
-- name    : mme_HasTauValueAtLeast_zero_tensor_iff
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-22T07:51:09.002393+00:00
-- url     : https://prove2.me/theorems/f9e54b6b-8f07-498b-b6a9-636e81abebb1
-- title:
--   A zero tensor has only value zero at nonzero exponents
-- statement:
--   Let $K$ be a field and let $T$ be a three-mode tensor over $K$ whose tensor element is zero. For every real exponent $\tau\ne0$ and every real $V$, $$\operatorname{HasTauValueAtLeast}(T,\tau,V)\quad\Longleftrightarrow\quad V=0.$$ This characterizes the value predicate on zero tensors for both positive and negative exponents. The exclusion of zero is necessary under the existing convention allowing zero-volume matrix blocks: at exponent zero, every nonnegative value satisfies the predicate.
-- source:
--   Audit of zero tensors and the exponent-zero boundary in the tau-value definition.

import Definitions.Def_mme_tau_value
open MME
universe u
set_option autoImplicit false

theorem mme_HasTauValueAtLeast_zero_tensor_iff
    {K : Type u} [Field K]
    (T : TensorObj K 3) (hT : T.t = 0) (tau : ℝ) (htau : tau ≠ 0) (V : ℝ) :
    HasTauValueAtLeast T tau V ↔ V = 0 := by sorry
