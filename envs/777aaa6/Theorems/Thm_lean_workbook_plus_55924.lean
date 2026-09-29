-- Prove2me | Theorems.Thm_lean_workbook_plus_55924
-- name    : lean_workbook_plus_55924
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.366127+00:00
-- url     : https://prove2.me/theorems/b6aa43c0-59b3-4344-b30a-a2d83e6b7022
-- statement:
--   Prove that \(a^3+(a+1)^3+\ldots+(a+6)^3\equiv 0\,(mod\, 7)\) for any integer \(a\).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_55924 (a : ℤ) :
    ∑ i in Finset.range 7, (a + i) ^ 3 ≡ 0 [ZMOD 7]   :=  by sorry
