-- Prove2me | Theorems.Thm_lean_workbook_plus_33525
-- name    : lean_workbook_plus_33525
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.431937+00:00
-- url     : https://prove2.me/theorems/3e4272d7-378b-42bd-8ebc-e7df4f987bd0
-- statement:
--   Given that $$a + 2b + 3c = 5$$ $$2a + 3b + c = -2$$ $$3a + b + 2c = 3,$$ find $3a + 3b + 3c$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_33525 (a b c : ℝ) (h1 : a + 2 * b + 3 * c = 5) (h2 : 2 * a + 3 * b + c = -2) (h3 : 3 * a + b + 2 * c = 3) : 3 * a + 3 * b + 3 * c = 3   :=  by sorry
