-- Prove2me | Theorems.Thm_lean_workbook_plus_26298
-- name    : lean_workbook_plus_26298
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.025447+00:00
-- url     : https://prove2.me/theorems/e69b8892-0192-45de-ac91-d7324d518093
-- statement:
--   For $a,b>0$ prove that $\frac{a^2}{b^2}+\frac{b^2}{a^2}\ge2$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_26298 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) : (a^2 / b^2) + (b^2 / a^2) ≥ 2   :=  by sorry
