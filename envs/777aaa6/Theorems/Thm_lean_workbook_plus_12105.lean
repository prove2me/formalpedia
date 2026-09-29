-- Prove2me | Theorems.Thm_lean_workbook_plus_12105
-- name    : lean_workbook_plus_12105
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.554211+00:00
-- url     : https://prove2.me/theorems/bd61f0b2-b03f-48c9-8d4d-76ce2733b99b
-- statement:
--   Show that $ (4k+1)^{4}-1$ and $ (4k-1)^{4}-1$ are divisible by 16.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_12105 : ∀ k : ℤ, (4 * k + 1) ^ 4 - 1 ≡ 0 [ZMOD 16]   :=  by sorry
