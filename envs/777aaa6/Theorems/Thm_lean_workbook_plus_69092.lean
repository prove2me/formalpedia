-- Prove2me | Theorems.Thm_lean_workbook_plus_69092
-- name    : lean_workbook_plus_69092
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.897675+00:00
-- url     : https://prove2.me/theorems/a8ef7157-8da9-4ce7-a2ef-b88b2c9086c4
-- statement:
--   So the solutions of $x^2-2x=0$ $\implies$ $0,2$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_69092  (S : Finset ℝ)
  (h₀ : ∀ (x : ℝ), x ∈ S ↔ x^2 - 2 * x = 0) :
  S = {0, 2}   :=  by sorry
