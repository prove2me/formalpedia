-- Prove2me | Theorems.Thm_lean_workbook_plus_15092
-- name    : lean_workbook_plus_15092
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.685829+00:00
-- url     : https://prove2.me/theorems/fff0d45e-2dd9-4900-aa50-4e64dd504d12
-- statement:
--   $ 1.\sum_{r=0}^{n}{n\choose r} =\sum_{r=0}^{n}{n\choose r}1^r1^{n-r}=(1+1)^n=2^n.$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_15092 : ∀ n : ℕ, ∑ r in Finset.range (n+1), choose n r = 2^n   :=  by sorry
