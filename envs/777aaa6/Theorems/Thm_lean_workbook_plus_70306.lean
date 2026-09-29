-- Prove2me | Theorems.Thm_lean_workbook_plus_70306
-- name    : lean_workbook_plus_70306
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.028831+00:00
-- url     : https://prove2.me/theorems/65cb7eb5-f5ce-49f0-bbfa-3e06c772f8c2
-- statement:
--   We have $ 2(1 - a + a^2)^2\geq1 + a^4$ if and only if $ (1 - a)^4\geq0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_70306 :  ∀ a : ℝ, (2 * (1 - a + a ^ 2) ^ 2 ≥ 1 + a ^ 4 ↔ (1 - a) ^ 4 ≥ 0)   :=  by sorry
