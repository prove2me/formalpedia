-- Prove2me | Theorems.Thm_lean_workbook_plus_68225
-- name    : lean_workbook_plus_68225
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.897675+00:00
-- url     : https://prove2.me/theorems/7db403a3-b845-42b6-bf09-5b434e20ab96
-- statement:
--   Prove or disprove $a^4+b^4+c^4+4abc>1$ given $a^2+b^2+c^2=1$ where $a, b, c$ are positive reals.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_68225 : ∀ a b c : ℝ, a^2+b^2+c^2=1 → a^4+b^4+c^4+4*a*b*c>1   :=  by sorry
