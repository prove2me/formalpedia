-- Prove2me | Theorems.Thm_WorkbookSource_problem_47872
-- name    : WorkbookSource.problem_47872
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T22:08:27.491423+00:00
-- url     : https://prove2.me/theorems/21c66968-aebc-42d0-b333-1ff3084d71e7
-- title:
--   A rational bound from a square
-- statement:
--   $a^4+1\ge 2a^2 \implies \dfrac{a^3}{a^4+1}\le \frac{a}{2}$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_47872` (Apache-2.0). The complete source proposition and explicit variable declarations are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_47872; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.problem_47872 (a : ℝ) (ha : a ≥ 0) : a^3 / (a^4 + 1) ≤ a / 2  :=  by sorry
