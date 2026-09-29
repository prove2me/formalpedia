-- Prove2me | Theorems.Thm_lean_workbook_plus_56872
-- name    : lean_workbook_plus_56872
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.366127+00:00
-- url     : https://prove2.me/theorems/740656fb-07c2-4163-abf4-72e6fc237147
-- statement:
--   After clearing denominators and squaring both sides the inequality becomes: \((a^3+b^3+c^3)(ab+bc+ca)^2\ge 3a^2b^2c^2(\sqrt{a}+\sqrt{b}+\sqrt{c})^2\) (*)
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_56872 :
    ∀ a b c : ℝ, (a^3 + b^3 + c^3) * (a * b + b * c + c * a)^2 ≥
    3 * a^2 * b^2 * c^2 * (Real.sqrt a + Real.sqrt b + Real.sqrt c)^2   :=  by sorry
