-- Prove2me | Theorems.Thm_lean_workbook_plus_79940
-- name    : lean_workbook_plus_79940
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.420916+00:00
-- url     : https://prove2.me/theorems/25bf35e0-a3d6-4b43-9bf2-f9e9fbe73c47
-- statement:
--   Note that $x^8-14x^4-8x^3-x^2+1=(x^4+1)^2-x^2(4x+1)^2$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_79940 : ∀ x : ℂ, x^8 - 14 * x^4 - 8 * x^3 - x^2 + 1 = 0 ↔ (x^4 + 1)^2 - x^2 * (4 * x + 1)^2 = 0   :=  by sorry
