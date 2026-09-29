-- Prove2me | Theorems.Thm_mme_dwz_square_fixed_tau_value_23747
-- name    : mme_dwz_square_fixed_tau_value_23747
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-25T19:03:50.386651+00:00
-- url     : https://prove2.me/theorems/fbcfdad6-373b-4f93-aa6d-306e61dc0588
-- title:
--   DWZ square: fixed tau-value witness for the 2.3747 endpoint
-- statement:
--   Combine the specialized Equation (25) extraction with the exact
--   Table 2 numeric inequality to obtain the literal fixed-tau witness consumed by
--   the already-proved q=6 tensor-square rank-surplus endpoint theorem.
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, FOCS 2023, arXiv:2210.10173, Equation (25), Section 6.3 and Table 2 (printed pp. 58-59).

import Definitions.Def_mme_tau_value
import Definitions.Def_mme_CW_tensor

open MME

universe u

theorem mme_dwz_square_fixed_tau_value_23747
    {K : Type u} [Field K] :
    HasTauValueAtLeast
      (TensorObj.kron (CWObj K 6) (CWObj K 6))
      (23747 / 30000) (640001 / 10000) := by sorry
