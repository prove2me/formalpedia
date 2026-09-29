-- Prove2me | Theorems.Thm_lean_workbook_plus_26261
-- name    : lean_workbook_plus_26261
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.025447+00:00
-- url     : https://prove2.me/theorems/bad30595-cbef-4ea3-86a7-b522be70443a
-- statement:
--   For complex numbers $\alpha ,\ \beta$ , if $\alpha \beta =0$ , then prove that $\alpha =0$ or $\beta =0$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_26261 (α β : ℂ) (h : α * β = 0) : α = 0 ∨ β = 0   :=  by sorry
