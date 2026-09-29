-- Prove2me | Theorems.Thm_lean_workbook_plus_29720
-- name    : lean_workbook_plus_29720
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.140359+00:00
-- url     : https://prove2.me/theorems/da6a499d-3faf-4b57-95f8-e411215fac03
-- statement:
--   So $f(x+c)=ax+b$ $\forall x>0$ and so $f(x)=ax+d$ $\forall x>c$ (where $d=b-ac$ )
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_29720 (f : ℝ → ℝ) (a b c : ℝ) (hf: ∀ x > 0, f (x + c) = a * x + b) : ∃ d, ∀ x > c, f x = a * x + d   :=  by sorry
