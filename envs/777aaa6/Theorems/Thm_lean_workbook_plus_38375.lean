-- Prove2me | Theorems.Thm_lean_workbook_plus_38375
-- name    : lean_workbook_plus_38375
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.562161+00:00
-- url     : https://prove2.me/theorems/415e691e-2ece-46ab-b8ca-b870e646606b
-- statement:
--   Use a comparison test to show the series converges: $\sum^{\infty}_{n=2}\frac{((\ln) n)^2}{n^2}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_38375 : ∀ n : ℕ, n ≥ 2 → 0 < ((Real.log n)^2)/(n^2)   :=  by sorry
