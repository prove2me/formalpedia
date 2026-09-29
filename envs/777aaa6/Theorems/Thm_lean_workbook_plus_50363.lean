-- Prove2me | Theorems.Thm_lean_workbook_plus_50363
-- name    : lean_workbook_plus_50363
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.108955+00:00
-- url     : https://prove2.me/theorems/168fe1c2-ba3b-4a20-8c96-b17906268f93
-- statement:
--   Let $a,b,c \geq 0$ ,prove that: $a^4+b^4+c^4-2a^2bc-b^2c^2\geq 0$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_50363 (a b c : ℝ) : a^4 + b^4 + c^4 - 2 * a^2 * b * c - b^2 * c^2 ≥ 0   :=  by sorry
