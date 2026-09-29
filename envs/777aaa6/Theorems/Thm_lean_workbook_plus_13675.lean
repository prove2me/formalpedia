-- Prove2me | Theorems.Thm_lean_workbook_plus_13675
-- name    : lean_workbook_plus_13675
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.554211+00:00
-- url     : https://prove2.me/theorems/c342c5e7-fe74-4642-8680-7db49f6a45d2
-- statement:
--   Correct the multiplication: $(\sqrt{5} + 3 + \sqrt{7})(\sqrt{5} + 3 - \sqrt{7})$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_13675 : (Real.sqrt 5 + 3 + Real.sqrt 7) * (Real.sqrt 5 + 3 - Real.sqrt 7) = 7 + 6 * Real.sqrt 5   :=  by sorry
