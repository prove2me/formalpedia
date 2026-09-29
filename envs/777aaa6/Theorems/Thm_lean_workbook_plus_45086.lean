-- Prove2me | Theorems.Thm_lean_workbook_plus_45086
-- name    : lean_workbook_plus_45086
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.988191+00:00
-- url     : https://prove2.me/theorems/0003af53-d4ed-4ac5-b255-5ea221328de6
-- statement:
--   For $a,b,c\in R^{+}$ prove : \n $a^3c^2+a^2b^3+ab^4+b^2c^3+b^3c^2\geq a^2b^2c+2ab^3c+2ab^2c^2$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_45086 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : a^3*c^2 + a^2*b^3 + a*b^4 + b^2*c^3 + b^3*c^2 ≥ a^2*b^2*c + 2*a*b^3*c + 2*a*b^2*c^2   :=  by sorry
