-- Prove2me | Theorems.Thm_WorkbookSource_problem_11015
-- name    : WorkbookSource.problem_11015
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T14:46:40.119319+00:00
-- url     : https://prove2.me/theorems/cc45af64-d3df-4e12-acb1-e9e3e802efe9
-- title:
--   A rational bound from a linear constraint
-- statement:
--   Let $x=\sum_{cyc}a^2$ and $y=\sum_{cyc}ab,$ so that we have $x+2y=9$ and $x\ge y,$ leading to $\frac{(x+y)^2}{2(x+y)+27}=\frac{x+y}{2+\frac{27}{x+y}}\geq \frac{2(x+y)}{13}$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_11015` (Apache-2.0). The complete source proposition and explicit variable declarations are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_11015; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.problem_11015 (x y : ℝ) (h₁ : x + 2 * y = 9) (h₂ : x ≥ y) : (x + y) ^ 2 / (2 * (x + y) + 27) ≥ 2 * (x + y) / 13  :=  by sorry
