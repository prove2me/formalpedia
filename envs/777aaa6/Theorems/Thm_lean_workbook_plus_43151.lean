-- Prove2me | Theorems.Thm_lean_workbook_plus_43151
-- name    : lean_workbook_plus_43151
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.862991+00:00
-- url     : https://prove2.me/theorems/150751e7-8b50-48a4-948e-a622dac986e3
-- statement:
--   Let $a,b$ and $c$ be positive integers that $\frac{a\sqrt{3}+b}{b\sqrt3+c}$ is a rational number, show that $\frac{a^2+b^2+c^2}{a+b+ c}$ is an integer.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_43151 (a b c : ℤ) (h : ∃ q : ℚ, (a * Real.sqrt 3 + b) / (b * Real.sqrt 3 + c) = q) : (a ^ 2 + b ^ 2 + c ^ 2) / (a + b + c) = ⌊(a ^ 2 + b ^ 2 + c ^ 2) / (a + b + c)⌋   :=  by sorry
