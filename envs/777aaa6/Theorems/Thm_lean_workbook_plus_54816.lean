-- Prove2me | Theorems.Thm_lean_workbook_plus_54816
-- name    : lean_workbook_plus_54816
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.366127+00:00
-- url     : https://prove2.me/theorems/8bc06879-e438-4645-90c8-d5fcdfbd8954
-- statement:
--   Factor the polynomial $x^9-37x^8-2x^7+74x^6+x^4-37x^3-2x^2+74x$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_54816 (x : ℤ) : x^9 - 37 * x^8 - 2 * x^7 + 74 * x^6 + x^4 - 37 * x^3 - 2 * x^2 + 74 * x = x * (x^8 - 37 * x^7 - 2 * x^6 + 74 * x^5 + x^3 - 37 * x^2 - 2 * x + 74)   :=  by sorry
