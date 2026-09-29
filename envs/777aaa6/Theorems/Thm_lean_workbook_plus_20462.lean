-- Prove2me | Theorems.Thm_lean_workbook_plus_20462
-- name    : lean_workbook_plus_20462
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.799204+00:00
-- url     : https://prove2.me/theorems/ff59ddae-3a23-4919-91a3-9de5e4b88cd4
-- statement:
--   If $a,b\ge 1$ , prove that $ab-\frac{1}{ab}\ge a-\frac{1}{a}+b-\frac{1}{b}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_20462 (a b : ℝ) (ha : 1 ≤ a) (hb : 1 ≤ b) : a * b - 1 / (a * b) ≥ a - 1 / a + b - 1 / b   :=  by sorry
