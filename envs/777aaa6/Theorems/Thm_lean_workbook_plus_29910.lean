-- Prove2me | Theorems.Thm_lean_workbook_plus_29910
-- name    : lean_workbook_plus_29910
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.279436+00:00
-- url     : https://prove2.me/theorems/e82c662d-b77f-458c-b274-4180a8726cab
-- statement:
--   Find the coefficients $A, B, C$ in the partial fraction decomposition $f(z)=1+\frac{A}{z-3}+\frac{B}{z-\sqrt{3}i}+\frac{C}{z+\sqrt{3}i}$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_29910 (A B C : ℂ) : 1 + A / (z - 3) + B / (z - √3 * Complex.I) + C / (z + √3 * Complex.I) = 1 + A / (z - 3) + B / (z - √3 * Complex.I) + C / (z + √3 * Complex.I)   :=  by sorry
