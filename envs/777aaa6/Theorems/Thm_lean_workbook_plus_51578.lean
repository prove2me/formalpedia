-- Prove2me | Theorems.Thm_lean_workbook_plus_51578
-- name    : lean_workbook_plus_51578
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.231389+00:00
-- url     : https://prove2.me/theorems/0a9d7a5f-f31d-4d6e-977c-37447554d3e5
-- statement:
--   By Cauchy-Schwarz inequality: $6(a^2+2b^2+3c^2)=(1+1+1+1+1+1)(a^2+b^2+b^2+c^2+c^2+c^2) \geq (a+2b+3c)^2$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_51578 (a b c : ℝ) :
  6 * (a ^ 2 + 2 * b ^ 2 + 3 * c ^ 2) ≥ (a + 2 * b + 3 * c) ^ 2   :=  by sorry
