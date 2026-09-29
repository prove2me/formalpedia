-- Prove2me | Theorems.Thm_lean_workbook_plus_5905
-- name    : lean_workbook_plus_5905
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.143455+00:00
-- url     : https://prove2.me/theorems/1b1527fb-c745-4346-b5cd-816ceaf241a5
-- statement:
--   Prove $a^{3}+b^{3}+c^{3}\ge c(a^{2}+ab+b^{2})$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_5905 : ∀ a b c : ℝ, a ^ 3 + b ^ 3 + c ^ 3 ≥ c * (a ^ 2 + a * b + b ^ 2)   :=  by sorry
