-- Prove2me | Theorems.Thm_lean_workbook_plus_37505
-- name    : lean_workbook_plus_37505
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.562161+00:00
-- url     : https://prove2.me/theorems/a6607fac-b715-4132-a6f9-467876997ef1
-- statement:
--   Let $x\in ]0,1[$\n\nProve that exists $\frac{a}{b}$ rational, $a,b$ positive integers, $gcd(a,b)=1$ , such that $|x-\frac{a}{b}|<\frac{1}{b^{2}}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_37505 (x : ℝ) (hx : 0 < x ∧ x < 1) :
    ∃ a b : ℤ, a > 0 ∧ b > 0 ∧ Int.gcd a b = 1 ∧ |x - a / b| < 1 / b^2   :=  by sorry
