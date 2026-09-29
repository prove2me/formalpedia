-- Prove2me | Theorems.Thm_WorkbookSource_problem_17980
-- name    : WorkbookSource.problem_17980
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T12:40:34.179377+00:00
-- url     : https://prove2.me/theorems/ac6ec7e1-5919-44a7-b5bc-5a8ad7f51413
-- title:
--   A cubic bound above two
-- statement:
--   If $t > 2$, show that $t(t^2 - 3) > 2$.
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_17980` (Apache-2.0). The complete source proposition and its explicit variable declarations are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_17980; Apache-2.0

import Mathlib
open Real

theorem WorkbookSource.problem_17980 : ∀ t : ℝ, t > 2 → t * (t ^ 2 - 3) > 2  :=  by sorry
