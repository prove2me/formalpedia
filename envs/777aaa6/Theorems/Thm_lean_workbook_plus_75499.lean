-- Prove2me | Theorems.Thm_lean_workbook_plus_75499
-- name    : lean_workbook_plus_75499
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.170827+00:00
-- url     : https://prove2.me/theorems/a9105708-92a1-49dc-b5ca-abdd5dd923a3
-- statement:
--   Let positive integer $n>9$ We easily check that : a) $5<\\frac {n-9}{\\sqrt 2}+5<\\frac {n-1}{\\sqrt 2}<\\frac {n-8}{\\sqrt 2}+5<\\frac n{\\sqrt 2}$ b) $\\frac {n-9}{\\sqrt 2}+5<\\frac n{\\sqrt 2}-1$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_75499 (n : ℕ) (hn : 9 < n) : ((n-9) / Real.sqrt 2 + 5 < (n-1) / Real.sqrt 2 ∧ (n-1) / Real.sqrt 2 < (n-8) / Real.sqrt 2 + 5 ∧ (n-8) / Real.sqrt 2 + 5 < n / Real.sqrt 2 ) ∧ ((n-9) / Real.sqrt 2 + 5 < n / Real.sqrt 2 - 1)   :=  by sorry
