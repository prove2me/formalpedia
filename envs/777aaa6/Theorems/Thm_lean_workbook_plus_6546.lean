-- Prove2me | Theorems.Thm_lean_workbook_plus_6546
-- name    : lean_workbook_plus_6546
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.293252+00:00
-- url     : https://prove2.me/theorems/a3fc52fa-403e-4de7-8d4e-35ca825e687d
-- statement:
--   Find the remainders of $ 5^{100}$ modulo $ 7, 11, 13$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_6546 : 5 ^ 100 ≡ 2 [ZMOD 7] ∧ 5 ^ 100 ≡ 1 [ZMOD 11] ∧ 5 ^ 100 ≡ 1 [ZMOD 13]   :=  by sorry
