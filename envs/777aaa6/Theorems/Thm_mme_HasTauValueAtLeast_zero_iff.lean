-- Prove2me | Theorems.Thm_mme_HasTauValueAtLeast_zero_iff
-- name    : mme_HasTauValueAtLeast_zero_iff
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-22T07:46:17.844849+00:00
-- url     : https://prove2.me/theorems/329c3b2d-2d85-4313-af05-1ce8e7bd3a7d
-- title:
--   The unrestricted tau-value definition degenerates at exponent zero
-- statement:
--   For every field K, every three-mode tensor T, and every real V, HasTauValueAtLeast T 0 V holds if and only if V is nonnegative. This is a boundary diagnosis of the current definition: zero-volume matrix blocks are permitted, and each contributes 0^0 = 1 at exponent zero. Arbitrarily many zero blocks restrict from any tensor, including the zero tensor. The result makes no assertion about positive exponents and does not change the shared definition.
-- source:
--   Boundary audit of the unrestricted tau-value definition.

import Definitions.Def_mme_tau_value
open MME
universe u
set_option autoImplicit false

theorem mme_HasTauValueAtLeast_zero_iff
    {K : Type u} [Field K] (T : TensorObj K 3) (V : ℝ) :
    HasTauValueAtLeast T 0 V ↔ 0 ≤ V := by sorry
