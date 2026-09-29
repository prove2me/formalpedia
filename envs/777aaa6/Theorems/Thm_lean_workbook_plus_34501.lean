-- Prove2me | Theorems.Thm_lean_workbook_plus_34501
-- name    : lean_workbook_plus_34501
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.431937+00:00
-- url     : https://prove2.me/theorems/f8a91a73-1710-4a6b-bbc2-2bb789080365
-- statement:
--   Using the inequality \(\frac{a}{a^{2}+bc}\leq \frac{1}{4}(\frac{1}{b}+\frac{1}{c})\), prove the given inequality.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_34501 : ∀ a b c : ℝ, a > 0 ∧ b > 0 ∧ c > 0 → a / (a ^ 2 + b * c) ≤ (1 / 4) * (1 / b + 1 / c)   :=  by sorry
