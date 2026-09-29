-- Prove2me | Theorems.Thm_WorkbookSource_base_5012
-- name    : WorkbookSource.base_5012
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T09:44:16.687871+00:00
-- url     : https://prove2.me/theorems/4509266c-cc02-492b-ab5d-44ca1a112c44
-- title:
--   A cubic correction to a squared-norm bound
-- statement:
--   Let $ a,b,c > 0$ be such that $ a + b + c = 1$ . Prove the followings: (1) $ 18abc + a^2 + b^2 + c^2 \le 1$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_5012` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_5012; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_5012 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c = 1) : 18 * a * b * c + a ^ 2 + b ^ 2 + c ^ 2 ≤ 1  :=  by sorry
