-- Prove2me | Theorems.Thm_WorkbookSource_plus_54270
-- name    : WorkbookSource.plus_54270
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T13:11:47.249697+00:00
-- url     : https://prove2.me/theorems/3e806e9e-ee74-4b8e-a43a-cb0855d6ce85
-- title:
--   A quartic with no negative roots
-- statement:
--   Show that the equation $x^4 -x^3-6x^2-2x+9 = 0$ cannot have negative roots.
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_54270` (Apache-2.0). The complete source proposition and its explicit variable declarations are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_54270; Apache-2.0

import Mathlib
open Real

theorem WorkbookSource.plus_54270 : ¬ (∃ x : ℝ, x < 0 ∧ x^4 - x^3 - 6 * x^2 - 2 * x + 9 = 0)   :=  by sorry
