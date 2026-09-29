-- Prove2me | Theorems.Thm_lean_workbook_plus_14128
-- name    : lean_workbook_plus_14128
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.554211+00:00
-- url     : https://prove2.me/theorems/47ca32ad-1b23-4987-ac51-113c08e9be2f
-- statement:
--   Find the values of $x$ that satisfy $2x-1=-25,-5,-1,1,5,25$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_14128 (x : ℤ) : (2*x-1 = -25 ∨ 2*x-1 = -5 ∨ 2*x-1 = -1 ∨ 2*x-1 = 1 ∨ 2*x-1 = 5 ∨ 2*x-1 = 25) ↔ x = -12 ∨ x = -2 ∨ x = 0 ∨ x = 1 ∨ x = 3 ∨ x = 13   :=  by sorry
