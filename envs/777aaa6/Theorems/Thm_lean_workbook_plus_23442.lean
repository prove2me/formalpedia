-- Prove2me | Theorems.Thm_lean_workbook_plus_23442
-- name    : lean_workbook_plus_23442
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.916039+00:00
-- url     : https://prove2.me/theorems/926fce71-e41b-4c14-ab0a-de8e1cfe0057
-- statement:
--   prove that: \n\n $-(acd+abd+abc+bcd)^2+4a^2c^2d^2+4a^2b^2d^2+4a^2b^2c^2+4b^2c^2d^2\geq 0$ \n\n $a,b,c,d \in R$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_23442 (a b c d : ℝ) : -(a * c * d + a * b * d + a * b * c + b * c * d) ^ 2 + 4 * a ^ 2 * c ^ 2 * d ^ 2 + 4 * a ^ 2 * b ^ 2 * d ^ 2 + 4 * a ^ 2 * b ^ 2 * c ^ 2 + 4 * b ^ 2 * c ^ 2 * d ^ 2 ≥ 0   :=  by sorry
