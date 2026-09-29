-- Prove2me | Theorems.Thm_WorkbookSource_problem_39005
-- name    : WorkbookSource.problem_39005
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T14:13:42.830736+00:00
-- url     : https://prove2.me/theorems/f02a89bb-b11b-4ca3-9e61-b50f485bc851
-- title:
--   Two factorizations for a cubic function
-- statement:
--   Write $f(x)={{6x^2-x^3}\over 8}={{x^2(6-x)}\over 8}$ then $f(x)-x={{x(x-2)(4-x)}\over 8}$ and $4-f(x)={{(4-x)^2(2+x)}\over 8}$ .
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_39005` (Apache-2.0). The complete source proposition and explicit variable declarations are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_39005; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.problem_39005 : ∀ x : ℝ, (6 * x ^ 2 - x ^ 3) / 8 - x = (x * (x - 2) * (4 - x)) / 8 ∧ 4 - (6 * x ^ 2 - x ^ 3) / 8 = ((4 - x) ^ 2 * (2 + x)) / 8  :=  by sorry
