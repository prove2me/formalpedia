-- Prove2me | Theorems.Thm_lean_workbook_plus_31156
-- name    : lean_workbook_plus_31156
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.279436+00:00
-- url     : https://prove2.me/theorems/0ae6153c-be41-4afa-95fa-874b9bf99fe1
-- statement:
--   $P(0,0): 2f(0)=0\implies f(0)=0$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_31156 (f : ℂ → ℂ) (h : 2 * f 0 = 0) : f 0 = 0   :=  by sorry
