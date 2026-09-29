-- Prove2me | Theorems.Thm_lean_workbook_plus_30505
-- name    : lean_workbook_plus_30505
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.279436+00:00
-- url     : https://prove2.me/theorems/0441660b-beee-4bb8-b8f2-043c1763b7f9
-- statement:
--   $f'(x)=\sum_{i=1}^n \ln (a_i) a_i^x$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_30505 (n : ℕ) (a : ℕ → ℝ) (x : ℝ) :
  (∑ i in Finset.range n, (Real.log (a i) * a i ^ x)) = ∑ i in Finset.range n, Real.log (a i) * a i ^ x   :=  by sorry
