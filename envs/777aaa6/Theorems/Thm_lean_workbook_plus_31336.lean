-- Prove2me | Theorems.Thm_lean_workbook_plus_31336
-- name    : lean_workbook_plus_31336
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.279436+00:00
-- url     : https://prove2.me/theorems/29883d41-0019-42fe-aebf-e7c4729955f7
-- statement:
--   Prove that if $k>1$, then $3^k>2^{k+1}$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_31336 (k : ℕ) (h : 1 < k) : (3 : ℝ) ^ k > 2 ^ (k + 1)   :=  by sorry
