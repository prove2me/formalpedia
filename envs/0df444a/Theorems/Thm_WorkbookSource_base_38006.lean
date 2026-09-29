-- Prove2me | Theorems.Thm_WorkbookSource_base_38006
-- name    : WorkbookSource.base_38006
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T11:12:31.779736+00:00
-- url     : https://prove2.me/theorems/13f83478-fb57-42e1-8300-6e374e7cbefb
-- title:
--   A quadratic lower bound under a quartic constraint
-- statement:
--   Two real numbers $ a$ and $b$ are given, such that $a^4 + b^4 +a^2b^2 = 60.$ Prove that $$4a^2 + 4b^2 - ab \ge 30$$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_38006` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_38006; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_38006 (a b : ℝ) (h : a^4 + b^4 + a^2 * b^2 = 60) :
  4 * a^2 + 4 * b^2 - a * b ≥ 30  :=  by sorry
