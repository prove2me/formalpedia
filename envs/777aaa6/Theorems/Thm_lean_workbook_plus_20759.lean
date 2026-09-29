-- Prove2me | Theorems.Thm_lean_workbook_plus_20759
-- name    : lean_workbook_plus_20759
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.916039+00:00
-- url     : https://prove2.me/theorems/f4765895-ecd4-415f-8d82-b7258c3489e6
-- statement:
--   $$\left(\dfrac{a}{b}\right)^2 + \left(\dfrac{b}{c}\right)^2 + \left(\dfrac{c}{a}\right)^2 \ge \dfrac{1}{3}\left(\dfrac{a}{b} + \dfrac{b}{c} + \dfrac{c}{a}\right)^2$$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_20759 (a b c : ℝ) :
  (a / b) ^ 2 + (b / c) ^ 2 + (c / a) ^ 2 ≥
    1 / 3 * (a / b + b / c + c / a) ^ 2   :=  by sorry
