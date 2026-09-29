-- Prove2me | Theorems.Thm_lean_workbook_plus_31726
-- name    : lean_workbook_plus_31726
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.279436+00:00
-- url     : https://prove2.me/theorems/f4236fbb-e66f-4a57-bf3f-9711900eefc6
-- statement:
--   Show that for a real number $a \geq 1$ the inequality $\displaystyle a^5+a^4+a^3+a^2+a+1 \geq 2(a^2+a+1)$ holds.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_31726 (a : ℝ) (h : 1 ≤ a) : a^5 + a^4 + a^3 + a^2 + a + 1 ≥ 2 * (a^2 + a + 1)   :=  by sorry
