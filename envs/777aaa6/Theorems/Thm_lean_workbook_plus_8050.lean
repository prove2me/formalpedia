-- Prove2me | Theorems.Thm_lean_workbook_plus_8050
-- name    : lean_workbook_plus_8050
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.293252+00:00
-- url     : https://prove2.me/theorems/8ab941c3-9ba8-489a-a5f8-6a62e0f72719
-- statement:
--   Find $x$ such that $3^2 + 4^2 - 2\times3\times4x = 5^2 + 6^2 - 2\times5\times6(-x)$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_8050 (x : ℝ) : (3^2 + 4^2 - 2*3*4*x = 5^2 + 6^2 - 2*5*6*(-x)) ↔ x = -3/7   :=  by sorry
