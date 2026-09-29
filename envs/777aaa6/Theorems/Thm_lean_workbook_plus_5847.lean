-- Prove2me | Theorems.Thm_lean_workbook_plus_5847
-- name    : lean_workbook_plus_5847
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.143455+00:00
-- url     : https://prove2.me/theorems/df6a4475-7e99-45b3-9bee-3ce2fed1a538
-- statement:
--   Prove the Hockey Stick Identity: $\sum_{i=0}^k \binom{n+i}{n}=\binom{n+k+1}{n+1}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_5847 (n k : ℕ) : ∑ i in Finset.range (k+1), choose (n+i) n = choose (n+k+1) (n+1)   :=  by sorry
