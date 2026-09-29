-- Prove2me | Theorems.Thm_lean_workbook_plus_25368
-- name    : lean_workbook_plus_25368
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.025447+00:00
-- url     : https://prove2.me/theorems/4db6a7fd-a2ad-4a50-9d4e-d90689a59d21
-- statement:
--   Expand to get $3a^2+3b^2+3c^2\ge a^2+b^2+c^2+2ab+2bc+2ca$ which reduces to $a^2+b^2+c^2\ge ab+bc+ca$ which is true by Rearrangement.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_25368 (a b c : ℝ) : 3 * a ^ 2 + 3 * b ^ 2 + 3 * c ^ 2 ≥ a ^ 2 + b ^ 2 + c ^ 2 + 2 * a * b + 2 * b * c + 2 * c * a   :=  by sorry
