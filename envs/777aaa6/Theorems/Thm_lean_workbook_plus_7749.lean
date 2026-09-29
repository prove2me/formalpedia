-- Prove2me | Theorems.Thm_lean_workbook_plus_7749
-- name    : lean_workbook_plus_7749
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.293252+00:00
-- url     : https://prove2.me/theorems/f8a8a016-510b-47c4-b53f-25e8054e2e52
-- statement:
--   计算 $ \sum\limits_{k = 1}^{21}\binom{21}{k} k^2 $
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_7749 :
  ∑ k in Finset.Icc 1 21, (Nat.choose 21 k) * k^2 = 2310   :=  by sorry
