-- Prove2me | Theorems.Thm_lean_workbook_plus_32482
-- name    : lean_workbook_plus_32482
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.279436+00:00
-- url     : https://prove2.me/theorems/6a386a6a-67aa-4ebb-b73c-316cdd7bcab5
-- statement:
--   If $a + b = 13, b + c = 14, c + a = 15,$ find the value of $c$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_32482 {a b c : ℕ} (h₁ : a + b = 13) (h₂ : b + c = 14) (h₃ : c + a = 15) : c = 8   :=  by sorry
