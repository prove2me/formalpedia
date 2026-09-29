-- Prove2me | Theorems.Thm_lean_workbook_plus_6223
-- name    : lean_workbook_plus_6223
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.293252+00:00
-- url     : https://prove2.me/theorems/4bff75f7-fdcd-48f0-af6b-29e6abdf513b
-- statement:
--   Prove that $abc\ge 3$ while $a+b+c=5$ and $a,b,c\ge 1$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_6223 : ∀ a b c : ℝ, a ≥ 1 ∧ b ≥ 1 ∧ c ≥ 1 ∧ a + b + c = 5 → a * b * c ≥ 3   :=  by sorry
