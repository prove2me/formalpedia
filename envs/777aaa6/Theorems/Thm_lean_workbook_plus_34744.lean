-- Prove2me | Theorems.Thm_lean_workbook_plus_34744
-- name    : lean_workbook_plus_34744
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.431937+00:00
-- url     : https://prove2.me/theorems/c9d606a4-5d54-488f-a7bd-4023aebd3942
-- statement:
--   Prove that $(4/3)(a^4+b^4+c^4-a^2b^2-b^2c^2-c^2a^2)+(4/3)(ab+bc+ca-3)^2 \geqq 0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_34744 (a b c : ℝ) : (4 / 3) * (a ^ 4 + b ^ 4 + c ^ 4 - a ^ 2 * b ^ 2 - b ^ 2 * c ^ 2 - c ^ 2 * a ^ 2) + (4 / 3) * (a * b + b * c + c * a - 3) ^ 2 ≥ 0   :=  by sorry
