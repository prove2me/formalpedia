-- Prove2me | Theorems.Thm_lean_workbook_plus_77103
-- name    : lean_workbook_plus_77103
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.289288+00:00
-- url     : https://prove2.me/theorems/39f87838-7a34-4f59-8854-16d59bc97950
-- statement:
--   Prove that $a^2+1\equiv 0\pmod{3}$ implies $a^2\equiv -1\pmod{3}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_77103 : a ^ 2 + 1 ≡ 0 [ZMOD 3] → a ^ 2 ≡ -1 [ZMOD 3]   :=  by sorry
