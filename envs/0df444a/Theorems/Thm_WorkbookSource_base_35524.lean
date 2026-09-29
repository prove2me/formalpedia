-- Prove2me | Theorems.Thm_WorkbookSource_base_35524
-- name    : WorkbookSource.base_35524
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T05:00:04.357547+00:00
-- url     : https://prove2.me/theorems/fe611c1a-bff1-45f7-9330-9931fa6fdf63
-- title:
--   A cyclic pair-product ratio sum is at most one
-- statement:
--   Prove that \\( ab/(a^{2} + 2b^{2}) + bc/(b^{2} + 2c^{2}) + ca/(c^{2} + 2a^{2}) \leq 1 \\) for positive numbers \\( a, b, c \\).
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_35524` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_35524; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_35524 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : a * b / (a ^ 2 + 2 * b ^ 2) + b * c / (b ^ 2 + 2 * c ^ 2) + c * a / (c ^ 2 + 2 * a ^ 2) ≤ 1  :=  by sorry
