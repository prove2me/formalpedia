-- Prove2me | Theorems.Thm_lean_workbook_plus_81418
-- name    : lean_workbook_plus_81418
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.420916+00:00
-- url     : https://prove2.me/theorems/badc9cbd-3afc-487f-938d-95331f343a27
-- statement:
--   And So, $f(5)$ = $2*(5)^3$ − $12*(5)^2$ + $23(5)$ − $12$ = $53$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_81418 (f : ℝ → ℝ) (f_def : ∀ x, f x = 2 * x^3 - 12 * x^2 + 23 * x - 12) : f 5 = 53   :=  by sorry
