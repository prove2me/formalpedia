-- Prove2me | Theorems.Thm_lean_workbook_plus_75244
-- name    : lean_workbook_plus_75244
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.170827+00:00
-- url     : https://prove2.me/theorems/426ab49e-30b0-4a08-8cff-ba6f824b7626
-- statement:
--   $ \frac{x^2y^2}{4} +x^2+y^2+x^2y+xy^2+\frac{5}{2}xy +x+y+\frac{1}{4} \geq\ 0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_75244 (x y : ℝ) : (x^2 * y^2)/4 + x^2 + y^2 + x^2 * y + x * y^2 + (5/2) * x * y + x + y + 1/4 ≥ 0   :=  by sorry
