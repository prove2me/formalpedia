-- Prove2me | Theorems.Thm_lean_workbook_plus_6806
-- name    : lean_workbook_plus_6806
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.293252+00:00
-- url     : https://prove2.me/theorems/41e56580-1a72-4dc7-bf8c-56830052895a
-- statement:
--   Put $x=n+a$ where $n=[x], a=\{x\}$ and discuss the necessary condition $0\leqslant a<1$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_6806 (x : ℝ) (n : ℤ) (a : ℝ) (h₁ : n = Int.floor x) (h₂ : a = x - n) : 0 ≤ a ∧ a < 1   :=  by sorry
