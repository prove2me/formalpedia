-- Prove2me | Theorems.Thm_WorkbookSource_problem_9091
-- name    : WorkbookSource.problem_9091
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T14:46:20.807363+00:00
-- url     : https://prove2.me/theorems/c7c0aa78-bc41-4b99-80e0-9985b7187728
-- title:
--   Distributing a rational factor in a pi expression
-- statement:
--   Evaluate the sum: $ \frac14(\frac{\pi^2}8 - 2(\frac{\pi}{8}))$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_9091` (Apache-2.0). The complete source proposition and explicit variable declarations are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_9091; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.problem_9091 (x : ℝ) : (1 / 4) * (π ^ 2 / 8 - 2 * (π / 8)) = π ^ 2 / 32 - π / 16  :=  by sorry
