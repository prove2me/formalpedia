-- Prove2me | Theorems.Thm_lean_workbook_plus_45245
-- name    : lean_workbook_plus_45245
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.988191+00:00
-- url     : https://prove2.me/theorems/e968aff7-9b78-469c-b0f8-4e257d11c428
-- statement:
--   Given that the greatest common divisor of two integers a and b is 1 (i.e., \( \gcd(a,b)=1 \)), prove that there exist integers x and y such that \( ax+by=1 \).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_45245 (a b : ℤ) (h : Nat.gcd a.natAbs b.natAbs = 1) : ∃ x y : ℤ, a*x + b*y = 1   :=  by sorry
