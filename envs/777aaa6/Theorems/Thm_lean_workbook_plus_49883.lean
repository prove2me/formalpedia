-- Prove2me | Theorems.Thm_lean_workbook_plus_49883
-- name    : lean_workbook_plus_49883
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.108955+00:00
-- url     : https://prove2.me/theorems/0550122c-829f-4823-a71a-770ec7f512d8
-- statement:
--   Prove that if $a^3=1(mod10)$ then $a\equiv 1 \:mod\:10$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_49883 : a^3 ≡ 1 [ZMOD 10] → a ≡ 1 [ZMOD 10]   :=  by sorry
