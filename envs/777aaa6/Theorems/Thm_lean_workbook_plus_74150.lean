-- Prove2me | Theorems.Thm_lean_workbook_plus_74150
-- name    : lean_workbook_plus_74150
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.170827+00:00
-- url     : https://prove2.me/theorems/9b34a071-7b49-45cf-96be-14edc5c32550
-- statement:
--   Prove that $\binom{n}{2} - \binom{n-1}{2} = n-1$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_74150 (n : ℕ) : (n.choose 2) - (n - 1).choose 2 = n - 1   :=  by sorry
