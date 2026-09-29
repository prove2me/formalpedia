-- Prove2me | Theorems.Thm_lean_workbook_plus_2545
-- name    : lean_workbook_plus_2545
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:54.833458+00:00
-- url     : https://prove2.me/theorems/17d5549e-e42c-460e-a595-1daaf4d715a8
-- statement:
--   For all positive real numbers $ a,b,c$ , prove that $ \frac {a}{b + c} + \frac {b}{c + a} + \frac {c}{a + b} \geq \frac {3}{2}.$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_2545 (a b c : ℝ) (hab : 0 < a) (hbc : 0 < b) (hca : 0 < c) : (a / (b + c) + b / (c + a) + c / (a + b)) ≥ 3 / 2   :=  by sorry
