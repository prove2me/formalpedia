-- Prove2me | Theorems.Thm_lean_workbook_plus_44225
-- name    : lean_workbook_plus_44225
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.862991+00:00
-- url     : https://prove2.me/theorems/2e74a78c-a2d7-445d-a2c9-9769a46345b5
-- statement:
--   Thus, the number of subsets with at least 4 elements is $ \binom{11}{4}+\binom{11}{5}+\hdots+\binom{11}{11}=2^11-\binom{11}{3}-\binom{11}{2}-\binom{11}{1}-\binom{11}{0}=2048-165-55-11-1=1806$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_44225 :
  ∑ k in Finset.Icc 4 11, (Nat.choose 11 k) = 1806   :=  by sorry
