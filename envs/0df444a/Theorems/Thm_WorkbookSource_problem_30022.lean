-- Prove2me | Theorems.Thm_WorkbookSource_problem_30022
-- name    : WorkbookSource.problem_30022
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T22:01:38.382575+00:00
-- url     : https://prove2.me/theorems/1c7e8691-2fde-4223-83fb-a86d56dc9998
-- title:
--   A sum of powers modulo thirteen
-- statement:
--   With $\mod13, 333^{555}+555^{777}+777^{333} \equiv5+1-1\equiv5\mod13$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_30022` (Apache-2.0). The complete source proposition and explicit variable declarations are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_30022; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.problem_30022 :
  (333^555 + 555^777 + 777^333) % 13 = 5  :=  by sorry
