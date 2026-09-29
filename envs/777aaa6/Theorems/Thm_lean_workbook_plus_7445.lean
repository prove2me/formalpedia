-- Prove2me | Theorems.Thm_lean_workbook_plus_7445
-- name    : lean_workbook_plus_7445
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.293252+00:00
-- url     : https://prove2.me/theorems/7a228e1c-d383-409b-b7cf-f80725c37b1e
-- statement:
--   Let $S=\{a_1,a_2,...,a_{18}\}$ be a set of eighteen (not necessarily distinct) integers. Prove that there exist two elements in $S$ whose difference is divisible by $17$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_7445 (S : Finset ℤ) (hS : S.card = 18) : ∃ a b, a ∈ S ∧ b ∈ S ∧ a - b ≡ 0 [ZMOD 17]   :=  by sorry
