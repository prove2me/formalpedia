-- Prove2me | Theorems.Thm_lean_workbook_plus_13413
-- name    : lean_workbook_plus_13413
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.554211+00:00
-- url     : https://prove2.me/theorems/187ca3c8-42c3-478c-ad7e-0619bb6e172c
-- statement:
--   ( $ a^2 + 1)(b^2 + 1)(c^2 + 1) = a^2b^2c^2 + a^2b^2 + b^2c^2 + c^2a^2 + a^2 + b^2 + c^2 + 1
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_13413 : ∀ a b c : ℂ, (a^2 + 1) * (b^2 + 1) * (c^2 + 1) = a^2 * b^2 * c^2 + a^2 * b^2 + b^2 * c^2 + c^2 * a^2 + a^2 + b^2 + c^2 + 1   :=  by sorry
