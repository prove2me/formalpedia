-- Prove2me | Theorems.Thm_lean_workbook_plus_30985
-- name    : lean_workbook_plus_30985
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.279436+00:00
-- url     : https://prove2.me/theorems/e34834ed-8e32-4d48-a7c6-0d6129f45bc8
-- statement:
--   Prove the following as a base case for induction: ${n \choose 0}+{n \choose 1}= 1+n ={n+1 \choose 1}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_30985 : ∀ n, choose n 0 + choose n 1 = choose (n + 1) 1   :=  by sorry
