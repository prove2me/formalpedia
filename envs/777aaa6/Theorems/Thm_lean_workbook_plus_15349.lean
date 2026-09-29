-- Prove2me | Theorems.Thm_lean_workbook_plus_15349
-- name    : lean_workbook_plus_15349
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.685829+00:00
-- url     : https://prove2.me/theorems/fa77a322-aba0-4bfe-ac43-a4f0c4e7c035
-- statement:
--   The possible quadratic residues in $ \pmod {10}$ are: $ 0,1,4,5,6,9$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_15349 : {0, 1, 4, 5, 6, 9} = {n : ℕ | n < 10 ∧ ∃ k : ℕ, k < 10 ∧ n ≡ k ^ 2 [ZMOD 10]}   :=  by sorry
