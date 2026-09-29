-- Prove2me | Theorems.Thm_lean_workbook_plus_24763
-- name    : lean_workbook_plus_24763
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.025447+00:00
-- url     : https://prove2.me/theorems/509f7984-e0cb-4d3b-a87e-54e4bf7efee4
-- statement:
--   C-S $ \geq \frac{(a+b+c)^2}{2ab+2bc+2ac-a^2-b^2-c^2} \geq 3 $ \n\n $\Longleftrightarrow 3(a^2+b^2+c^2)+(a+b+c)^2\geq 6(ab+bc+ac) $
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_24763 (a b c : ℝ) :
  3 * (a ^ 2 + b ^ 2 + c ^ 2) + (a + b + c) ^ 2 ≥ 6 * (a * b + b * c + a * c)   :=  by sorry
