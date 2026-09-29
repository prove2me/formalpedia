-- Prove2me | Theorems.Thm_lean_workbook_plus_80406
-- name    : lean_workbook_plus_80406
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.420916+00:00
-- url     : https://prove2.me/theorems/3de9913f-a310-45f1-854e-face3a4dab25
-- statement:
--   Prove the binomial coefficient relation: $\binom{n}{r} + \binom{n}{r-1} = \binom{n+1}{r}$ where $1 \leq r \leq n$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_80406 (n r : ℕ) (h₁ : 1 ≤ r) (h₂ : r ≤ n) : choose n r + choose n (r-1) = choose (n+1) r   :=  by sorry
