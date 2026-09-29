-- Prove2me | Theorems.Thm_lean_workbook_plus_73335
-- name    : lean_workbook_plus_73335
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.170827+00:00
-- url     : https://prove2.me/theorems/38ad59ff-4344-40c0-9b84-ee9f1b59c4ca
-- statement:
--   $f(a)=0$ and $a\in\{0,\frac 12\}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_73335 (f : ℝ → ℝ) (a : ℝ) (h₁ : f a = 0) (h₂ : a = 0 ∨ a = 1 / 2) : a = 0 ∨ a = 1 / 2   :=  by sorry
