-- Prove2me | Theorems.Thm_WorkbookSource_problem_8940
-- name    : WorkbookSource.problem_8940
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T14:46:19.510689+00:00
-- url     : https://prove2.me/theorems/b268b258-39e1-43a1-9e8f-823eb80a8ac2
-- title:
--   A lower bound for a sum of two squared linear forms
-- statement:
--   Actually, just the first condition $2x+y\ge2$ is sufficient: $ (2x+y)^2+(2y-x)^2\ge 4+0 \Leftrightarrow x^2+y^2 \ge \frac45$.
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_8940` (Apache-2.0). The complete source proposition and explicit variable declarations are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_8940; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.problem_8940  (x y : ℝ)
  (h₀ : 2 * x + y ≥ 2) :
  (2 * x + y)^2 + (2 * y - x)^2 ≥ 4  :=  by sorry
