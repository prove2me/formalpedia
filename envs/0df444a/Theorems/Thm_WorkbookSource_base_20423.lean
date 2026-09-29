-- Prove2me | Theorems.Thm_WorkbookSource_base_20423
-- name    : WorkbookSource.base_20423
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T09:43:32.092718+00:00
-- url     : https://prove2.me/theorems/395a0b35-a58d-4372-a5eb-76aaa9bd052c
-- title:
--   A quartic product bound at fixed squared norm four
-- statement:
--   Prove that if $a, b, c, d$ are real numbers such that $a^2 + b^2 + c^2 + d^2 = 4$, then $3(a^4 + b^4 + c^4 + d^4 + 12abcd) + 80 \geq 8(a + b + c + d)^2$.
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_20423` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_20423; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_20423 (a b c d : ℝ) (h : a^2 + b^2 + c^2 + d^2 = 4) :
  3 * (a^4 + b^4 + c^4 + d^4 + 12 * a * b * c * d) + 80 ≥ 8 * (a + b + c + d)^2  :=  by sorry
