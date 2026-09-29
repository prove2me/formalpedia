-- Prove2me | Theorems.Thm_lean_workbook_plus_30902
-- name    : lean_workbook_plus_30902
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.279436+00:00
-- url     : https://prove2.me/theorems/bf9d2bbd-578b-495d-9fd2-52fe65f49140
-- statement:
--   If $ -a+b+c<0,a-b+c<0 $ then $ c<0 $ (the other similar )
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_30902 : ∀ a b c : ℝ,  -a+b+c<0 ∧ a-b+c<0 → c<0   :=  by sorry
