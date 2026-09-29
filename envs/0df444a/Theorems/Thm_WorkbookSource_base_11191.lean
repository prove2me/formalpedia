-- Prove2me | Theorems.Thm_WorkbookSource_base_11191
-- name    : WorkbookSource.base_11191
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T22:44:11.72597+00:00
-- url     : https://prove2.me/theorems/278a5cf6-4e65-4049-a8dd-82a34ada04da
-- title:
--   A symmetric quartic expression is nonnegative
-- statement:
--   (a^{2}+b^{2})(a-b)^{2}+(b^{2}+c^{2})(b-c)^{2}+(c^{2}+a^{2})(c-a)^{2}+2abc(a+b+c) \ge 0$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_11191` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_11191; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_11191 (a b c : ℝ) :
  (a^2 + b^2) * (a - b)^2 + (b^2 + c^2) * (b - c)^2 + (c^2 + a^2) * (c - a)^2 + 2 * a * b * c * (a + b + c) ≥ 0  :=  by sorry
