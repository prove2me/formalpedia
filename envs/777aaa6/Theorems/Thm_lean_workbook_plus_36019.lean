-- Prove2me | Theorems.Thm_lean_workbook_plus_36019
-- name    : lean_workbook_plus_36019
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.562161+00:00
-- url     : https://prove2.me/theorems/2e02ad00-a42d-4e21-8ca1-2d2019f9eb6f
-- statement:
--   Let $a,b$ be positive real numbers. Prove that:\n$$\frac{1}{a}+\frac{1}{b}+\frac{k}{a+b} \ge 3\left(1+\frac{k}{4}\right)\left( \frac{1}{2a+b}+\frac{1}{2b+a}\right)$$ Where $0\le k\le 32$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_36019 (a b k : ℝ) (ha : 0 < a) (hb : 0 < b) (hk : 0 ≤ k ∧ k ≤ 32) : 1 / a + 1 / b + k / (a + b) ≥ 3 * (1 + k / 4) * (1 / (2 * a + b) + 1 / (2 * b + a))   :=  by sorry
