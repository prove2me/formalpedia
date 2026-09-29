-- Prove2me | Theorems.Thm_lean_workbook_plus_51895
-- name    : lean_workbook_plus_51895
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.231389+00:00
-- url     : https://prove2.me/theorems/9095bdb5-f3c0-4f64-814c-dde6e7188446
-- statement:
--   Therefore, have that $x^2-2x-48=0$ . This yields $(x+6)(x-8)=0$ , which has solutions $x=\{-6,8\}$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_51895  (x : ℝ)
  (h₀ : x^2 - 2 * x - 48 = 0) :
  x = -6 ∨ x = 8   :=  by sorry
