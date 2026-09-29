-- Prove2me | Theorems.Thm_lean_workbook_plus_61375
-- name    : lean_workbook_plus_61375
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.629978+00:00
-- url     : https://prove2.me/theorems/7640bb1c-a33b-4292-8a06-f14b05ea63e1
-- statement:
--   prove that $\frac{a^2+b^2+c^2}{2}\cdot\frac{a^5+b^5+c^5}{5}=\frac{a^7+b^7+c^7}{7}$ if $a+b+c=0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_61375 (a b c : ℝ) (h : a + b + c = 0) : (a^2 + b^2 + c^2) / 2 * (a^5 + b^5 + c^5) / 5 = (a^7 + b^7 + c^7) / 7   :=  by sorry
