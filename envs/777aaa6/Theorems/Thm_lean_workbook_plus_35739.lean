-- Prove2me | Theorems.Thm_lean_workbook_plus_35739
-- name    : lean_workbook_plus_35739
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.431937+00:00
-- url     : https://prove2.me/theorems/af83e89d-bc60-40c6-bc08-69986cb2b016
-- statement:
--   $(a^2-2)(a^2+2)(a^2-2a+2)(a^2+2a+2) = a^8 - 16$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_35739 : ∀ a : ℂ, (a^2 - 2) * (a^2 + 2) * (a^2 - 2 * a + 2) * (a^2 + 2 * a + 2) = a^8 - 16   :=  by sorry
