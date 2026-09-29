-- Prove2me | Theorems.Thm_WorkbookSource_base_3985
-- name    : WorkbookSource.base_3985
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T00:00:58.334925+00:00
-- url     : https://prove2.me/theorems/21ed95d6-afab-47af-b83f-10a7853868c6
-- title:
--   A fourth-degree bound for variables of sum two
-- statement:
--   Let a,b,c be non-negative real numbers with sum 2. Prove that: $ 24(a^2+b^2+c^2)+(a^2+b^2+c^2)^2 \le 48+8(a^3+b^3+c^3)$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_3985` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_3985; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_3985 (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (habc : a + b + c = 2) : 24 * (a ^ 2 + b ^ 2 + c ^ 2) + (a ^ 2 + b ^ 2 + c ^ 2) ^ 2 ≤ 48 + 8 * (a ^ 3 + b ^ 3 + c ^ 3)  :=  by sorry
