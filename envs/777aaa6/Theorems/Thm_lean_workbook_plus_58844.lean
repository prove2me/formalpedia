-- Prove2me | Theorems.Thm_lean_workbook_plus_58844
-- name    : lean_workbook_plus_58844
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.496679+00:00
-- url     : https://prove2.me/theorems/236e6310-c803-4ed9-9bcd-3269c8717d40
-- statement:
--   Prove that $11b\equiv 0\pmod{7}$ implies $b\equiv{0}\pmod{7}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_58844 : 11 * b ≡ 0 [ZMOD 7] → b ≡ 0 [ZMOD 7]   :=  by sorry
