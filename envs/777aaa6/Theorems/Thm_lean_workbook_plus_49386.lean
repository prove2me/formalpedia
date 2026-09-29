-- Prove2me | Theorems.Thm_lean_workbook_plus_49386
-- name    : lean_workbook_plus_49386
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.108955+00:00
-- url     : https://prove2.me/theorems/b55e58ca-dd7f-4c74-916e-b39d71602056
-- statement:
--   For example, $7^2\equiv 2^2\:(mod\:5)\Rightarrow 7\equiv 2\:(mod\:5)$ , on the other hand $10^2\equiv 2^2\:(mod\:6)\nRightarrow 10\equiv 2\:(mod\:6)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_49386 : 7 ^ 2 ≡ 2 ^ 2 [ZMOD 5] → 7 ≡ 2 [ZMOD 5]   :=  by sorry
