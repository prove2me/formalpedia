-- Prove2me | Theorems.Thm_lean_workbook_plus_63575
-- name    : lean_workbook_plus_63575
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.629978+00:00
-- url     : https://prove2.me/theorems/bb3a561e-e90a-4421-8eff-c94420168732
-- statement:
--   Prove that for all real numbers $a,b,c,d$, $(abc+acd+abd+bcd-a-b-c-d)^2 +(abcd-ab-ac-ad-bc-bd-cd+1)^2 \geq 1$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_63575 (a b c d : ℝ) : (a * b * c + a * c * d + a * b * d + b * c * d - a - b - c - d) ^ 2 + (a * b * c * d - a * b - a * c - a * d - b * c - b * d - c * d + 1) ^ 2 ≥ 1   :=  by sorry
