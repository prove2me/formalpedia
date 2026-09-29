-- Prove2me | Theorems.Thm_lean_workbook_plus_47184
-- name    : lean_workbook_plus_47184
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.988191+00:00
-- url     : https://prove2.me/theorems/34e806a4-7dbf-4eb9-9b90-60e9de7d1da7
-- statement:
--   Prove that \(\frac{a^2}{b}+\frac{b^2}{c}+\frac{c^2}{a} \geq a+b+c\) for \(a, b, c\) being the lengths of the sides of a triangle.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_47184 {a b c : ℝ} (hx: a > 0 ∧ b > 0 ∧ c > 0) (hab : a + b > c) (hbc : b + c > a) (hca : a + c > b) : a^2 / b + b^2 / c + c^2 / a ≥ a + b + c   :=  by sorry
