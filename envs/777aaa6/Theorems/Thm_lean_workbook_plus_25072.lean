-- Prove2me | Theorems.Thm_lean_workbook_plus_25072
-- name    : lean_workbook_plus_25072
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.025447+00:00
-- url     : https://prove2.me/theorems/ff0b012b-c1ef-464d-a7a9-dfdde3df377f
-- statement:
--   Prove that $(3a-5)^2((10a^2+8a)(4a-3)^2+21(a-1)^2+2a^4+4a^3+4)\geq0$ for $a\geq1$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_25072 : ∀ a ≥ 1, (3 * a - 5) ^ 2 * ((10 * a ^ 2 + 8 * a) * (4 * a - 3) ^ 2 + 21 * (a - 1) ^ 2 + 2 * a ^ 4 + 4 * a ^ 3 + 4) ≥ 0   :=  by sorry
