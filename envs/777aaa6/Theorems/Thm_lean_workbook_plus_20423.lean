-- Prove2me | Theorems.Thm_lean_workbook_plus_20423
-- name    : lean_workbook_plus_20423
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.799204+00:00
-- url     : https://prove2.me/theorems/751ec877-774f-43be-b8b2-d4038ce4971f
-- statement:
--   If $y-1\equiv 1\pmod 7$ then $y^4+y^3+y^2+y+1\equiv 3\pmod 7$ (contradiction)
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_20423 : y - 1 ≡ 1 [ZMOD 7] → y ^ 4 + y ^ 3 + y ^ 2 + y + 1 ≡ 3 [ZMOD 7]   :=  by sorry
