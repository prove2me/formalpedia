-- Prove2me | Theorems.Thm_lean_workbook_plus_40695
-- name    : lean_workbook_plus_40695
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.715658+00:00
-- url     : https://prove2.me/theorems/f0d69f51-e5b0-4c86-a89c-47ccdb5bd61d
-- statement:
--   Prove that for all positive real $x$ , the following inequality holds: \n\n $$(x + 1)(x + 2)(x + 5) \geq 36x.$$ \n\n Note that \n\n $(x + 1)(x + 2)(x + 5) - 36x = (x+10)(x-1)^2.$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_40695 (x : ℝ) (h : x > 0) : (x + 1) * (x + 2) * (x + 5) ≥ 36 * x   :=  by sorry
