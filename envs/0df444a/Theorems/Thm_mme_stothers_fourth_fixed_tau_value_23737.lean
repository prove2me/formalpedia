-- Prove2me | Theorems.Thm_mme_stothers_fourth_fixed_tau_value_23737
-- name    : mme_stothers_fourth_fixed_tau_value_23737
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-29T00:21:01.285986+00:00
-- url     : https://prove2.me/theorems/62f4619c-2aa4-4c02-8b21-2742f66a9f56
-- title:
--   Table 2: exact q=6 fixed-tau surplus at 2.3737
-- statement:
--   Let $K$ be an arbitrary field. At
--
--   $$
--   \tau=\frac{23737}{30000},
--   $$
--
--   the tensor $CW_6\otimes CW_6$ has tau-value at least
--
--   $$
--   \frac{640000001}{10000000}=64.0000001>64.
--   $$
--
--   This is an exact-rational fixed-tau certificate extracted from the Davie--Stothers fourth-power calculation and Table 2. The fourth-power value has been square-rooted back to the square tensor so that the result interfaces directly with the established asymptotic-rank bound $\widetilde R(CW_6^{\otimes2})\le64$.
-- source:
--   Davie and Stothers (2013), Theorem 5.3 and Table 2, printed p. 368, reporting omega < 2.373689703, https://www.maths.ed.ac.uk/~sandy/a11164.pdf; Stothers thesis (2010), Chapter 4.2, printed pp. 80-81.

import Definitions.Def_mme_stothers_fourth_data

open MME

universe u

set_option autoImplicit false

theorem mme_stothers_fourth_fixed_tau_value_23737
    {K : Type u} [Field K] :
    HasTauValueAtLeast
      (TensorObj.kron (CWObj K 6) (CWObj K 6))
      (23737 / 30000) (640000001 / 10000000) := by
  sorry
