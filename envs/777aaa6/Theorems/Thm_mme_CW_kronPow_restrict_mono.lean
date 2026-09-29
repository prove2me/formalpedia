-- Prove2me | Theorems.Thm_mme_CW_kronPow_restrict_mono
-- name    : mme_CW_kronPow_restrict_mono
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-22T11:38:54.226372+00:00
-- url     : https://prove2.me/theorems/63a5885b-3735-47df-9672-8f518dbc63fe
-- title:
--   CW tensor powers are monotone under restriction
-- statement:
--   Let $K$ be a field and $q,m,n$ natural numbers with $m\le n$. Then
--   $$\mathrm{CW}_q^{\otimes m}\preceq\mathrm{CW}_q^{\otimes n}.$$
--   Here $\preceq$ denotes tensor restriction by linear maps on the three mode spaces. This permits stage sources with different elementary CW exponents to restrict from a common larger CW power, including the zeroth power.
-- source:
--   Boundary-coordinate projection of the CW tensor and multiplicativity of tensor restriction.

import Definitions.Def_mme_CW_tensor
import Definitions.Def_mme_rank_bridge

open MME PiTensorProduct
universe u
set_option autoImplicit false

theorem mme_CW_kronPow_restrict_mono
    {K : Type u} [Field K] (q : ℕ) {m n : ℕ} (h : m ≤ n) :
    TensorObj.Restrict ((CWObj K q).kronPow m) ((CWObj K q).kronPow n) := by sorry
