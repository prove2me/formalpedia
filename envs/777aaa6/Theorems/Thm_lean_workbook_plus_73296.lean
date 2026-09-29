-- Prove2me | Theorems.Thm_lean_workbook_plus_73296
-- name    : lean_workbook_plus_73296
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.170827+00:00
-- url     : https://prove2.me/theorems/4939fa39-25cd-4d54-a372-812be20ff101
-- statement:
--   Prove that $7(\sum_{cyc}a^6)+21a^2b^2c^2\geq 14(\sum_{cyc}a^4bc)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_73296 (a b c : ℝ) : 7 * (a ^ 6 + b ^ 6 + c ^ 6) + 21 * a ^ 2 * b ^ 2 * c ^ 2 ≥ 14 * (a ^ 4 * b * c + b ^ 4 * c * a + c ^ 4 * a * b)   :=  by sorry
