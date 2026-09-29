-- Prove2me | Theorems.Thm_lean_workbook_plus_22011
-- name    : lean_workbook_plus_22011
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.916039+00:00
-- url     : https://prove2.me/theorems/76489246-026c-42d3-8138-39c0af72c66c
-- statement:
--   Find all functions $f:\mathbb{Q} \to \mathbb{Q}$ such that for all $a,b,c,d$ with $ab=cd$ we have: $f(a+b)-f(a)-f(b)=f(c+d)-f(c)-f(d)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_22011 (f : ℚ → ℚ) (hf: ∀ a b c d : ℚ, a * b = c * d → f (a + b) - f a - f b = f (c + d) - f c - f d) : ∃ l a : ℚ, f x = l * x + a   :=  by sorry
