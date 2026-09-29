-- Prove2me | Theorems.Thm_lean_workbook_plus_5850
-- name    : lean_workbook_plus_5850
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.143455+00:00
-- url     : https://prove2.me/theorems/cc3bb326-097c-4441-a3c1-c08addfc6f73
-- statement:
--   Prove that for non-negative real numbers $a, b, c, d, e$, the inequality $b^4 + c^4 + d^4 + e^4 \geq 4bcde$ holds if at least one variable is equal to zero. If all variables are positive, prove that fixing $a^4 + b^4 + c^4 + d^4 + e^4$ and $\frac{1}{a} + \frac{1}{b} + \frac{1}{c} + \frac{1}{d} + \frac{1}{e}$ makes the inequality a decreasing function of $abcde$. Show that the inequality is true when four variables are equal to 1 and the fifth variable is $a$ by using AM-GM inequality.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_5850 (a b c d e : ℝ) (h : a = 0 ∨ b = 0 ∨ c = 0 ∨ d = 0 ∨ e = 0) : b^4 + c^4 + d^4 + e^4 ≥ 4 * b * c * d * e   :=  by sorry
