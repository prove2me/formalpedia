-- Prove2me | Theorems.Thm_lean_workbook_plus_27827
-- name    : lean_workbook_plus_27827
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.140359+00:00
-- url     : https://prove2.me/theorems/cea437fe-11e2-4a73-b87f-afe270b128bb
-- statement:
--   Prove that \n\n $\sqrt{\frac{a^2+b^2+c^2+d^2}{4}} \ge \frac{a+b+c+d}{4}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_27827 (a b c d : ℝ) : Real.sqrt ((a^2 + b^2 + c^2 + d^2) / 4) ≥ (a + b + c + d) / 4   :=  by sorry
