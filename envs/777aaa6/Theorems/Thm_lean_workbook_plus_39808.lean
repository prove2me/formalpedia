-- Prove2me | Theorems.Thm_lean_workbook_plus_39808
-- name    : lean_workbook_plus_39808
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.715658+00:00
-- url     : https://prove2.me/theorems/9485a193-3b57-4081-acfa-903072c30edf
-- statement:
--   Let $ a,\ b,\ c$ be real numbers such that $ a < b < c,\ a + b + c = 0.$ Prove that $ \frac {a^2 + b^2 + c^2}{(c - a)^2}< \frac{2}{3}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_39808 (a b c : ℝ) (h₁ : a < b ∧ b < c) (h₂ : a + b + c = 0) : (a^2 + b^2 + c^2) / (c - a)^2 < 2 / 3   :=  by sorry
