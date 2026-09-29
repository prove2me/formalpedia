-- Prove2me | Theorems.Thm_lean_workbook_plus_50580
-- name    : lean_workbook_plus_50580
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.108955+00:00
-- url     : https://prove2.me/theorems/24862195-e1b9-42ed-9717-e529b0026fbd
-- statement:
--   If $ a \ge b \ge c > 0 $ real numbers, prove that:\n$ (a-b)(b-c)(a-c)\geq 0 $ hence $a^2b+ac^2+b^2c\geq a^2c+ab^2+bc^2$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_50580 (a b c : ℝ) (hab : a ≥ b) (hbc : b ≥ c) (hca : 0 < c) :  (a - b) * (b - c) * (a - c) ≥ 0 ∧ a^2 * b + a * c^2 + b^2 * c ≥ a^2 * c + a * b^2 + b * c^2   :=  by sorry
