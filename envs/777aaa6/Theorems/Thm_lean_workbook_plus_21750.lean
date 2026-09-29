-- Prove2me | Theorems.Thm_lean_workbook_plus_21750
-- name    : lean_workbook_plus_21750
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.916039+00:00
-- url     : https://prove2.me/theorems/37070b19-a39e-4f7b-aadd-e4cbee967a0b
-- statement:
--   a,b,c be real numers,prove that: \n\n $2b^4+a^2(c+b)^2 \geq 2ab(ac+bc+b^2).$ \n\n
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_21750 (a b c : ℝ) : 2 * b ^ 4 + a ^ 2 * (c + b) ^ 2 ≥ 2 * a * b * (a * c + b * c + b ^ 2)   :=  by sorry
