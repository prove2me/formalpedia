-- Prove2me | Theorems.Thm_lean_workbook_plus_64391
-- name    : lean_workbook_plus_64391
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.755244+00:00
-- url     : https://prove2.me/theorems/35ce997c-adc2-4f61-8b28-38329006e53c
-- statement:
--   Determine the convergence of the series $ \sum_{n=1}^{\infty}\left(a^{\frac{1}{n}}-\frac{b^{\frac{1}{n}}+c^{\frac{1}{n}}}{2}\right)$ where $ (a,b,c > 0)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_64391 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : ∃ l, ∑' n : ℕ, (a^(1/n) - (b^(1/n) + c^(1/n)) / 2) = l   :=  by sorry
