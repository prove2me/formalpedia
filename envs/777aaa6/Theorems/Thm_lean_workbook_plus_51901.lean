-- Prove2me | Theorems.Thm_lean_workbook_plus_51901
-- name    : lean_workbook_plus_51901
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.231389+00:00
-- url     : https://prove2.me/theorems/a3735312-3ce7-4a9a-b7da-9d1c5ea51299
-- statement:
--   $ \sinh(x) = \frac {e^x - e^{ - x}}{2}$, prove $ -\sinh( - x) = \sinh(x)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_51901 : ∀ x, -sinh (-x) = sinh x   :=  by sorry
