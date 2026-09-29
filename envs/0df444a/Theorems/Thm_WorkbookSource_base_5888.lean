-- Prove2me | Theorems.Thm_WorkbookSource_base_5888
-- name    : WorkbookSource.base_5888
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T00:05:41.78333+00:00
-- url     : https://prove2.me/theorems/347657d4-41a2-484e-8ac8-3455fda3fa09
-- title:
--   A sixth-degree inequality with a squared difference correction
-- statement:
--   Prove that \((a+b+c)^2(a^2+b^2+c^2)^2 \geq 27abc(a^3+b^3+c^3) + 3(a-b)^2(b-c)^2(c-a)^2\) for non-negative \(a, b, c\).
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_5888` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_5888; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_5888 (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) : (a + b + c) ^ 2 * (a ^ 2 + b ^ 2 + c ^ 2) ^ 2 ≥ 27 * a * b * c * (a ^ 3 + b ^ 3 + c ^ 3) + 3 * (a - b) ^ 2 * (b - c) ^ 2 * (c - a) ^ 2  :=  by sorry
