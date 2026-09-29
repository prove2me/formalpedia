-- Prove2me | Theorems.Thm_WorkbookSource_problem_29260
-- name    : WorkbookSource.problem_29260
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T21:56:57.994575+00:00
-- url     : https://prove2.me/theorems/febdd85a-b8fa-45fb-888e-5644de90bd44
-- title:
--   Factoring a cyclic quartic expression
-- statement:
--   The expression $f(M)$ can be factored as $f(M) = a^3(b - c) + b^3(c - a) + c^3(a - b) = c(b^3 - a^3) - ba(b^2 - a^2) - c^3(b - a) = (b - a)\left[c(b^2 + ba + a^2) - ba(b + a) - c^3\right]$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_29260` (Apache-2.0). The complete source proposition and explicit variable declarations are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_29260; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.problem_29260 : ∀ a b c : ℝ, a * b * c = b * c * a → a^3 * (b - c) + b^3 * (c - a) + c^3 * (a - b) = (b - a) * (c * (b^2 + b * a + a^2) - b * a * (b + a) - c^3)  :=  by sorry
