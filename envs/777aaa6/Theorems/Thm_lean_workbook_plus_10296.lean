-- Prove2me | Theorems.Thm_lean_workbook_plus_10296
-- name    : lean_workbook_plus_10296
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.412125+00:00
-- url     : https://prove2.me/theorems/1105828c-baf4-4096-80f2-f54ad1a5a4de
-- statement:
--   $ \frac{\frac{n(n+1)}{2}}{n} \geq \sqrt[n]{n!}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_10296 : ∀ n : ℕ, ((n * (n + 1)) / 2 : ℝ) / n ≥ (n! : ℝ) ^ (1 / n)   :=  by sorry
