-- Prove2me | Theorems.Thm_WorkbookCorrected_plus_70623
-- name    : WorkbookCorrected.plus_70623
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T13:58:21.588623+00:00
-- url     : https://prove2.me/theorems/8b14e57e-27bb-4792-b260-f261ecb95140
-- title:
--   A strict lower bound for the fractional part of a nonintegral cube root
-- statement:
--   Prove: $\{\sqrt[3]{n}\}>\frac{1}{3\sqrt[3]{n^2}}$ where $n$ is a positive integer not equal to a cube of any integer
--
--   Formalization Note: The source formalization omitted the fractional-part operation and used a square root with a natural-number fractional exponent. This correction represents the cube root by a nonnegative real r with r³=n and restores r−floor(r). Its denominator3r² equals3 times the cube root of n². The noncube condition is preserved for positive integers.
--
--   Source: InternLM Lean-Workbook, record lean_workbook_plus_70623 (Apache-2.0).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_70623; Apache-2.0

import Mathlib

theorem WorkbookCorrected.plus_70623 (n : ℕ) (hn : 0<n) (hnc : ¬ ∃ k : ℕ, k^3=n)
    (r : ℝ) (hr : 0 ≤ r) (he : r^3=(n:ℝ)) : r-(⌊r⌋₊:ℝ) > 1/(3*r^2) := by sorry
