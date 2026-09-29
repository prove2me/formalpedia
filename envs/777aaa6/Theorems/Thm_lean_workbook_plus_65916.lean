-- Prove2me | Theorems.Thm_lean_workbook_plus_65916
-- name    : lean_workbook_plus_65916
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.755244+00:00
-- url     : https://prove2.me/theorems/bb40de6e-2c7d-4a38-981b-fa7290c68998
-- statement:
--   From the hockey stick identity, we have $ \binom{2}{2}+\binom{3}{2}+\cdots+\binom{19}{2}=\binom{20}{3} $
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_65916 :
  ∑ k in (Finset.Icc 2 19), (Nat.choose k 2) = Nat.choose 20 3   :=  by sorry
