-- Prove2me | Theorems.Thm_lean_workbook_plus_59592
-- name    : lean_workbook_plus_59592
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.496679+00:00
-- url     : https://prove2.me/theorems/46bf205c-7603-4d2d-825d-d1437be77f77
-- statement:
--   Given a sequence $a_{n}$ with $a_{1}=3$ that satisfies $a_{n+1}=2(n+1)5^n\times a_{n}$ , find the general term $a_{n}$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_59592 (a : ℕ → ℝ) (a1 : a 0 = 3) (a_rec : ∀ n, a (n + 1) = (2 * (n + 1) * 5 ^ n) * a n) : ∀ n, a n = 2 ^ (n - 1) * n! * 5 ^ ((n - 1) * n / 2) * 3   :=  by sorry
