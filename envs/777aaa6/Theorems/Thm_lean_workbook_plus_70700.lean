-- Prove2me | Theorems.Thm_lean_workbook_plus_70700
-- name    : lean_workbook_plus_70700
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.028831+00:00
-- url     : https://prove2.me/theorems/f353f524-46d0-4544-bf32-3231520f4ca5
-- statement:
--   Note that $(a - 1)(b - 1) \ge 0$ since $-1 \le a \le 1$ and $-1 \le b \le 1$ (so that $a - 1 \le 0$ and $b - 1 \le 0$ ). Then $ab + 1 \ge a + b$ . But also $(a + 1)(b + 1) \ge 0$ by a similar argument, so $ab + 1 \ge -(a + b)$ . Then $ab + 1 \ge |a + b|$ . But $|ab + 1| \ge ab + 1$ , so we get $|ab + 1| \ge |a + b|$ . Note that equality holds if and only if $a = b = 1$ or $a = b = -1$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_70700 (a b : ℝ) (hab : a ∈ Set.Icc (-1) 1 ∧ b ∈ Set.Icc (-1) 1) :
  |a * b + 1| ≥ |a + b|   :=  by sorry
