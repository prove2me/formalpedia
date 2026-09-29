-- Prove2me | Theorems.Thm_mme_profiled_CW_tensor_restrict_power
-- name    : mme_profiled_CW_tensor_restrict_power
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-23T08:53:15.217009+00:00
-- url     : https://prove2.me/theorems/b5c48ef1-6958-4551-8947-6cc0bb2ef288
-- title:
--   Profiled CW tensors restrict the elementary tensor power
-- statement:
--   For every profile predicate on N elementary positions, the corresponding profiled tensor is an actual restriction of the Nth tensor power of CW with parameter five. The restriction is its defining mode-wise basis projection. The root exponent bound remains a separate obligation.
-- source:
--   Checked tensor restrictions and released global histogram extraction.

import Definitions.Def_mme_recursive_profiled_CW_data
open MME
universe u

theorem mme_profiled_CW_tensor_restrict_power
    {K : Type u} [Field K] {N : ℕ} (P : ProfiledCW.Predicate N) :
    TensorObj.Restrict (ProfiledCW.tensor K P) ((CWObj K 5).kronPow N) := by sorry
