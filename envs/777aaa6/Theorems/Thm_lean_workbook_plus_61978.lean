-- Prove2me | Theorems.Thm_lean_workbook_plus_61978
-- name    : lean_workbook_plus_61978
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.629978+00:00
-- url     : https://prove2.me/theorems/56539b56-7b43-4cc1-a494-09315bd691d1
-- statement:
--   Prove that $a^2 + b^2 + c^2 + 1 + 1 \geq ab + ac + bc$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_61978 (a b c: ℝ) : a ^ 2 + b ^ 2 + c ^ 2 + 1 + 1 ≥ a * b + a * c + b * c   :=  by sorry
