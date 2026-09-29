-- Prove2me | Theorems.Thm_WorkbookSource_problem_41109
-- name    : WorkbookSource.problem_41109
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T21:40:21.697243+00:00
-- url     : https://prove2.me/theorems/30fdeab8-6ba0-4cfe-8118-138ba3c43548
-- title:
--   Commuting two price scale factors
-- statement:
--   For any real price $p$,
--
--   $$p\cdot0.9\cdot1.2=p\cdot1.2\cdot0.9.$$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_41109` (Apache-2.0). The complete source proposition and explicit variable declarations are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_41109; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.problem_41109  (p : ℝ) :
  p * 0.9 * 1.2 = p * 1.2 * 0.9  :=  by sorry
