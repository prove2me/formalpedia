-- Prove2me | Theorems.Thm_lean_workbook_plus_35922
-- name    : lean_workbook_plus_35922
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.562161+00:00
-- url     : https://prove2.me/theorems/9cae32c8-9275-4983-998f-7920d5e1cf9e
-- statement:
--   Rewrite $x^{18}-1$ as $\left(x^9-1\right)\left(x^9+1\right)$ which further reduces to $\left(x^3-1\right)\left(x^6+x^3+1\right)\left(x^3+1\right)\left(x^6-x^3+1\right);$ dividing by $x^6-1 = \left(x^3-1\right)\left(x^3+1\right)$ leaves us with $\left(x^6+x^3+1\right)\left(x^6-x^3+1\right).$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_35922 (x : ℤ) : x^18 - 1 = (x^9 - 1) * (x^9 + 1)   :=  by sorry
