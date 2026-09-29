-- Prove2me | Theorems.Thm_lean_workbook_plus_19085
-- name    : lean_workbook_plus_19085
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.799204+00:00
-- url     : https://prove2.me/theorems/12fd4118-3e98-49ae-ba6c-a686017ec146
-- statement:
--   Find all integers $x$ with $2\le x\le 199$ such that $x^3\equiv 1\pmod{199}$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_19085 (x : ℤ) (hx: 2 ≤ x ∧ x ≤ 199) (h : x^3 ≡ 1 [ZMOD 199]) : x = 92 ∨ x = 106   :=  by sorry
