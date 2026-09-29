-- Prove2me | Theorems.Thm_lean_workbook_plus_37353
-- name    : lean_workbook_plus_37353
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.562161+00:00
-- url     : https://prove2.me/theorems/ea46c493-cced-425b-a2f1-8af8d1e62e80
-- statement:
--   Prove that if $\sum_{i=0}^\infty a_i$ converges, then $\sum_{i=0}^\infty\frac{a_i}{a_i+1}$ converges, assuming $a_i > 0$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_37353 (a : ℕ → ℝ) (ha : ∀ i, a i > 0) (h : Summable a) : Summable (λ i => a i / (a i + 1))   :=  by sorry
