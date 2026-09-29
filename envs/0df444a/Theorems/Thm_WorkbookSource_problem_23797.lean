-- Prove2me | Theorems.Thm_WorkbookSource_problem_23797
-- name    : WorkbookSource.problem_23797
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T21:51:44.80857+00:00
-- url     : https://prove2.me/theorems/7157b81d-f442-478c-a781-9a024a2a1164
-- title:
--   Factoring a cyclic cubic expression
-- statement:
--   $\sum_{cyc}{4x^3-4x^2+x} \ge 0 \Longleftrightarrow \sum_{cyc}{x(2x-1)^2} \ge 0 $
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_23797` (Apache-2.0). The complete source proposition and explicit variable declarations are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_23797; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.problem_23797 : ∀ x y z : ℝ, (4 * x ^ 3 - 4 * x ^ 2 + x + 4 * y ^ 3 - 4 * y ^ 2 + y + 4 * z ^ 3 - 4 * z ^ 2 + z ≥ 0 ↔ x * (2 * x - 1) ^ 2 + y * (2 * y - 1) ^ 2 + z * (2 * z - 1) ^ 2 ≥ 0)  :=  by sorry
