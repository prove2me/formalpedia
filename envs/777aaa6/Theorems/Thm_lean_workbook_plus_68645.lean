-- Prove2me | Theorems.Thm_lean_workbook_plus_68645
-- name    : lean_workbook_plus_68645
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.897675+00:00
-- url     : https://prove2.me/theorems/da9737cf-0a29-4b9f-bebb-ca1a4b03cae6
-- statement:
--   Yes - if you let $S$ denote the desired sum, then $\frac{S}{2} = \binom{2}{2} + \binom{3}{2} + \ldots + \binom{100}{2}$ , in which you can apply the hockey stick identity.\nIsn't the sum then $2\binom{101}{3}=333300$ ?
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_68645  (s : ℕ)
  (h₀ : s = ∑ k in (Finset.Icc (2 : ℕ) 100), (k + 1).choose 2) :
  s = 333300   :=  by sorry
