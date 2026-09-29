-- Prove2me | Theorems.Thm_WorkbookSource_problem_10948
-- name    : WorkbookSource.problem_10948
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T14:46:36.505276+00:00
-- url     : https://prove2.me/theorems/97f970d9-afc5-4f10-9748-7416a815391b
-- title:
--   A quadratic bound under two ratio constraints
-- statement:
--   Let $a$ and $b$ be two positive real numbers with $a \le 3b \le 5a .$ Prove that $a^2+ b^2 \le \frac{10}{3} ab$.
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_10948` (Apache-2.0). The complete source proposition and explicit variable declarations are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_10948; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.problem_10948 (a b : ℝ) (h1 : 0 < a ∧ 0 < b) (h2 : a ≤ 3 * b) (h3 : 3 * b ≤ 5 * a) : a^2 + b^2 ≤ (10/3) * a * b  :=  by sorry
