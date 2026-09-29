-- Prove2me | Theorems.Thm_WorkbookSource_problem_31079
-- name    : WorkbookSource.problem_31079
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T21:58:49.772704+00:00
-- url     : https://prove2.me/theorems/ca0983d8-daab-4705-a541-7552630028f8
-- title:
--   A square-root bound for three positive inputs
-- statement:
--   Prove that for positive real numbers a, b, and c, the following inequality holds:
--   $$\sqrt{2(a^2+b^2)(b^2+c^2)(c^2+a^2)} \geq (a+b)(b+c)(c+a)-4abc.$$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_31079` (Apache-2.0). The complete source proposition and explicit variable declarations are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_31079; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.problem_31079 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : Real.sqrt (2 * (a^2 + b^2) * (b^2 + c^2) * (c^2 + a^2)) ≥ (a + b) * (b + c) * (c + a) - 4 * a * b * c  :=  by sorry
