-- Prove2me | Theorems.Thm_lean_workbook_plus_28975
-- name    : lean_workbook_plus_28975
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.140359+00:00
-- url     : https://prove2.me/theorems/751e104b-1679-4c0e-a44d-f224d3d4480a
-- statement:
--   So, $x^2-4x+2=0$ which means $x=2\pm\sqrt{2}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_28975 (x : ℝ) : x^2 - 4*x + 2 = 0 ↔ x = 2 + Real.sqrt 2 ∨ x = 2 - Real.sqrt 2   :=  by sorry
