-- Prove2me | Theorems.Thm_lean_workbook_plus_39062
-- name    : lean_workbook_plus_39062
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.715658+00:00
-- url     : https://prove2.me/theorems/f3a4654e-882c-4278-8a72-1549ec5436ac
-- statement:
--   Noting then that $7^4\equiv 1\pmod {10}$ , we get $7^{2003}\equiv 7^3\equiv 3\pmod {10}$ Hence the answer $\boxed{3}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_39062 : 7 ^ 2003 ≡ 3 [MOD 10]   :=  by sorry
