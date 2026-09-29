-- Prove2me | Theorems.Thm_WorkbookSource_problem_9858
-- name    : WorkbookSource.problem_9858
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T14:46:23.9155+00:00
-- url     : https://prove2.me/theorems/ace60ac0-eedb-4282-a1f2-b8a1367da560
-- title:
--   Averages of initial segments of a nondecreasing sequence
-- statement:
--   Prove that $\frac{x_{1}+x_{2}+\cdots+x_{6}}{6} \leq \frac{x_{1}+x_{2}+\cdots+x_{10}}{10}$ for $x_{1} \leq x_{2} \leq \cdots \leq x_{10}$.
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_9858` (Apache-2.0). The complete source proposition and explicit variable declarations are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_9858; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.problem_9858 (x : ℕ → ℝ) (hx : Monotone x) : (x 1 + x 2 + x 3 + x 4 + x 5 + x 6) / 6 ≤ (x 1 + x 2 + x 3 + x 4 + x 5 + x 6 + x 7 + x 8 + x 9 + x 10) / 10  :=  by sorry
