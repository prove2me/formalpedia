-- Prove2me | Theorems.Thm_lean_workbook_plus_71322
-- name    : lean_workbook_plus_71322
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.028831+00:00
-- url     : https://prove2.me/theorems/e5003a1f-4ff0-4c87-92bd-bfb52b8a7442
-- statement:
--   Let $a, b$ be positive numbers. Prove that $$\frac{1}{a+2b}+\frac{1}{b+2a}\leq \frac{2}{3\sqrt{ab}}.$$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_71322 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) : (1 / (a + 2 * b) + 1 / (b + 2 * a) ≤ 2 / (3 * Real.sqrt (a * b)))   :=  by sorry
