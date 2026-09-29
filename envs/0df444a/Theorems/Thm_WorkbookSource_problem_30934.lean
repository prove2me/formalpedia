-- Prove2me | Theorems.Thm_WorkbookSource_problem_30934
-- name    : WorkbookSource.problem_30934
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T22:01:41.66242+00:00
-- url     : https://prove2.me/theorems/a411d933-1c14-4717-a373-3e8867af7dbb
-- title:
--   A quotient bound involving a square root
-- statement:
--   For the second note that: $\frac{\sqrt{1-x^2}}{1+x^2}\leq\frac{1}{1+x^2}$ .
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_30934` (Apache-2.0). The complete source proposition and explicit variable declarations are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_30934; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.problem_30934 : ∀ x, Real.sqrt (1 - x ^ 2) / (1 + x ^ 2) ≤ 1 / (1 + x ^ 2)  :=  by sorry
