-- Prove2me | Theorems.Thm_lean_workbook_plus_56561
-- name    : lean_workbook_plus_56561
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.366127+00:00
-- url     : https://prove2.me/theorems/3041453f-6434-420f-9347-1b2ad68fb528
-- statement:
--   Prove that if $a + b + c = 0$, then $\frac{a^5 + b^5 + c^5}{5} = \frac{a^3 + b^3 + c^3}{3} \frac{a^2 + b^2 + c^2}{2}$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_56561 (a b c : ℝ) (hab : a + b + c = 0) : (a^5 + b^5 + c^5) / 5 = (a^3 + b^3 + c^3) / 3 * (a^2 + b^2 + c^2) / 2   :=  by sorry
