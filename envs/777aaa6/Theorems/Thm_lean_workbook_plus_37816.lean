-- Prove2me | Theorems.Thm_lean_workbook_plus_37816
-- name    : lean_workbook_plus_37816
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.562161+00:00
-- url     : https://prove2.me/theorems/bd69ae5b-881c-4a77-b6d0-c997df78ade1
-- statement:
--   We know that $ S+S+\binom{n}{0}+\binom{n}{n}=\sum_{i=0}^n \binom{n}{i}=2^n$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_37816 (n : ℕ) : (∑ i in Finset.range (n+1), choose n i) = 2^n   :=  by sorry
