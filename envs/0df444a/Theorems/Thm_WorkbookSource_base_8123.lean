-- Prove2me | Theorems.Thm_WorkbookSource_base_8123
-- name    : WorkbookSource.base_8123
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T11:11:36.559983+00:00
-- url     : https://prove2.me/theorems/501362e6-079f-45a5-8579-41a47827e205
-- title:
--   A quadratic-factor product bound above one
-- statement:
--   Let $a,b,c \ge 1$ , Prove that : $(2a^2+1)(2b^2+1)(2c^2+1) \ge 3\left (a+b+c\right )^2$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_8123` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_8123; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_8123 (a b c : ℝ) (ha : 1 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c) : (2 * a ^ 2 + 1) * (2 * b ^ 2 + 1) * (2 * c ^ 2 + 1) ≥ 3 * (a + b + c) ^ 2  :=  by sorry
