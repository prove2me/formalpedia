-- Prove2me | Theorems.Thm_WorkbookSource_problem_17708
-- name    : WorkbookSource.problem_17708
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T15:04:46.639184+00:00
-- url     : https://prove2.me/theorems/e08ba234-fbc6-40f1-a2bf-1f4921de6418
-- title:
--   A five-variable quadratic as four squares
-- statement:
--   Since the sum of non-negative terms is greater than or equal to 0, it follows that $a^2 + b^2 + c^2 + d^2 + e^2 - a(b + c + d + e) \ge 0$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_17708` (Apache-2.0). The complete source proposition and explicit variable declarations are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_17708; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.problem_17708 (a b c d e : ℝ) : a^2 + b^2 + c^2 + d^2 + e^2 - a * (b + c + d + e) ≥ 0  :=  by sorry
