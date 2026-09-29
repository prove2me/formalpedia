-- Prove2me | Theorems.Thm_lean_workbook_plus_51285
-- name    : lean_workbook_plus_51285
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.108955+00:00
-- url     : https://prove2.me/theorems/b8dc9b3e-3e60-4dc2-9f23-fd36850c8d6c
-- statement:
--   Let $a\leq b\leq c\leq d\leq e$ and $a+b+c+d+e= 1$. Prove that: $ad+dc+cb+be+ea\leq \frac{1}{5}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_51285 (a b c d e : ℝ) (h1 : a ≤ b ∧ b ≤ c ∧ c ≤ d ∧ d ≤ e) (h2 : a + b + c + d + e = 1) : a * d + d * c + c * b + b * e + e * a ≤ 1 / 5   :=  by sorry
