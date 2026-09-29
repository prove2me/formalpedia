-- Prove2me | Theorems.Thm_lean_workbook_plus_9243
-- name    : lean_workbook_plus_9243
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.412125+00:00
-- url     : https://prove2.me/theorems/be2f3e1a-8b98-4203-9bc2-19a514343e16
-- statement:
--   Prove that $a^2bc+ab^2c+abc^2+1-bc-ac-ab-a^2b^2c^2=-(bc-1)(ac-1)(ab-1)$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_9243 a^2 * b * c + a * b^2 * c + a * b * c^2 + 1 - b * c - a * c - a * b - a^2 * b^2 * c^2 = -(b * c - 1) * (a * c - 1) * (a * b - 1)   :=  by sorry
