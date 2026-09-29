-- Prove2me | Theorems.Thm_lean_workbook_plus_36690
-- name    : lean_workbook_plus_36690
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.562161+00:00
-- url     : https://prove2.me/theorems/79325fc8-26ce-4f08-8136-2b215bdff26b
-- statement:
--   When $a=b$ , we can freely conclude $f(a)=f(b)$ (that's true for any function)
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_36690 (a b : ℕ) (f : ℕ → ℕ) (h₁ : a = b) : f a = f b   :=  by sorry
