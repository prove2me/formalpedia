-- Prove2me | Theorems.Thm_lean_workbook_plus_17443
-- name    : lean_workbook_plus_17443
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.685829+00:00
-- url     : https://prove2.me/theorems/887c3d53-3459-4a70-b4aa-b556a34a3ac4
-- statement:
--   Let's consider the inequality $ a^3+b^3+c^3<k(a+b+c)(ab+bc+ca)$ where $ a,b,c$ are the sides of a triangle and $ k$ a real number.\n\na) Prove the inequality for $ k=1$ .\n\nb) Find the smallest value of $ k$ such that the inequality holds for all triangles.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_17443 (a b c : ℝ) (hx: a > 0 ∧ b > 0 ∧ c > 0) (hab : a + b > c) (hbc : b + c > a) (hca : a + c > b) : a^3 + b^3 + c^3 < (a + b + c) * (a * b + b * c + c * a)   :=  by sorry
