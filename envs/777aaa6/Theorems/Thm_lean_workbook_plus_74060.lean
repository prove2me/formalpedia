-- Prove2me | Theorems.Thm_lean_workbook_plus_74060
-- name    : lean_workbook_plus_74060
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.170827+00:00
-- url     : https://prove2.me/theorems/2ca6ddbf-e94c-4e7b-9672-9a3abb58ee00
-- statement:
--   Prove that $x \equiv 1,3$ (mod 12) implies $x \equiv 0,1$ (mod 3) .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_74060 : ∀ x : ℤ, x ≡ 1 [ZMOD 12] ∨ x ≡ 3 [ZMOD 12] → x ≡ 0 [ZMOD 3] ∨ x ≡ 1 [ZMOD 3]   :=  by sorry
