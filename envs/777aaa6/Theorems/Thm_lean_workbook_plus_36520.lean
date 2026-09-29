-- Prove2me | Theorems.Thm_lean_workbook_plus_36520
-- name    : lean_workbook_plus_36520
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.562161+00:00
-- url     : https://prove2.me/theorems/2bfef483-f456-45ce-b298-e110ceb7ce79
-- statement:
--   Notice that\n\n $9({a^2} + {b^2} + {c^2}) = {(2a + 2b - c)^2} + {(2b + 2c - a)^2} + {(2c + 2a - b)^2},$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_36520    (a b c : ℝ) :
  9 * (a^2 + b^2 + c^2) = (2 * a + 2 * b - c)^2 + (2 * b + 2 * c - a)^2 + (2 * c + 2 * a - b)^2   :=  by sorry
