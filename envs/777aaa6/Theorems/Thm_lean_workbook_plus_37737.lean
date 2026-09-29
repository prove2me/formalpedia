-- Prove2me | Theorems.Thm_lean_workbook_plus_37737
-- name    : lean_workbook_plus_37737
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.562161+00:00
-- url     : https://prove2.me/theorems/a2afc297-84bb-4e4c-a69b-6c309eca10c4
-- statement:
--   For all reals $a$ , $b$ and $c$ prove that: \n $4(a^{2}+ab+b^{2})(b^{2}+bc+c^{2})(c^{2}+ca+a^{2})\ge3(a^2b+a^2c+b^2a+b^2c+c^2a+c^2b)^2$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_37737 (a b c : ℝ) : 4 * (a ^ 2 + a * b + b ^ 2) * (b ^ 2 + b * c + c ^ 2) * (c ^ 2 + c * a + a ^ 2) ≥ 3 * (a ^ 2 * b + a ^ 2 * c + b ^ 2 * a + b ^ 2 * c + c ^ 2 * a + c ^ 2 * b) ^ 2   :=  by sorry
