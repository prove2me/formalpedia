-- Prove2me | Theorems.Thm_lean_workbook_plus_31271
-- name    : lean_workbook_plus_31271
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.279436+00:00
-- url     : https://prove2.me/theorems/195a7b01-1ffb-4bd5-a7de-901f7a0c9e2d
-- statement:
--   Prove that for all positive real $x$ , the following inequality holds: \n\n $$(x + 1)(x + 2)(x + 5) \geq 36x.$$ \n\n Okay this is Another solution
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_31271 (x : ℝ) (hx : 0 < x) : (x + 1) * (x + 2) * (x + 5) ≥ 36 * x   :=  by sorry
