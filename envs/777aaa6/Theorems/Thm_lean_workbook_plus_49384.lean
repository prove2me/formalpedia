-- Prove2me | Theorems.Thm_lean_workbook_plus_49384
-- name    : lean_workbook_plus_49384
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.108955+00:00
-- url     : https://prove2.me/theorems/efe400e8-c1c9-46f0-8f0e-fa80fc4f0a9f
-- statement:
--   Evaluate the limit: $ \lim_{n\to\infty} \sqrt[n+1] { \prod_{k=0}^{n} {n \choose k} }$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_49384 : ∃ l : ℝ, ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, n ≥ N → |(∏ k in Finset.range (n+1), (n.choose k))^(1/(n+1)) - l| < ε   :=  by sorry
