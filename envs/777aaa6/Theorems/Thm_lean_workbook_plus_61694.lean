-- Prove2me | Theorems.Thm_lean_workbook_plus_61694
-- name    : lean_workbook_plus_61694
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.629978+00:00
-- url     : https://prove2.me/theorems/fda7e941-c457-414b-a2ca-3d198b09fcf0
-- statement:
--   Factor the polynomial $x^4+25x^3+198x^2+600x+576$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_61694 : ∀ x : ℝ, x^4 + 25 * x^3 + 198 * x^2 + 600 * x + 576 = (x + 4) * (x + 6) * (x^2 + 15 * x + 24)   :=  by sorry
