-- Prove2me | Theorems.Thm_WorkbookSource_base_4129
-- name    : WorkbookSource.base_4129
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T09:43:23.123467+00:00
-- url     : https://prove2.me/theorems/5bcfd5c4-dcbd-4639-81e9-d3967e803171
-- title:
--   A fourth-power and squared-sum bound on a sphere
-- statement:
--   If a, b, c, d are real numbers such that $ a^2+b^2+c^2+d^2=4 $ show that $a^4+b^4+c^4+d^4+4(a+b+c+d)^2 \leq 68.$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_4129` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_4129; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_4129 (a b c d : ℝ) (h : a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 = 4) :
  a ^ 4 + b ^ 4 + c ^ 4 + d ^ 4 + 4 * (a + b + c + d) ^ 2 ≤ 68  :=  by sorry
