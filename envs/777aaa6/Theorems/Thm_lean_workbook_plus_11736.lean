-- Prove2me | Theorems.Thm_lean_workbook_plus_11736
-- name    : lean_workbook_plus_11736
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.412125+00:00
-- url     : https://prove2.me/theorems/f5245da7-640a-49d1-80dd-9849ed31655b
-- statement:
--   Find if the series converges or diverges and if it converges, find its value.\n$$\sum_{n=1}^{\infty}\frac1{n^2+1}$$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_11736 (f : ℕ → ℝ) (hf : ∀ n, f n = 1 / (n ^ 2 + 1)) : ∃ l, ∑' n : ℕ, f n = l   :=  by sorry
