-- Prove2me | Theorems.Thm_lean_workbook_plus_80978
-- name    : lean_workbook_plus_80978
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.420916+00:00
-- url     : https://prove2.me/theorems/2ae662e7-a5f6-441b-8e12-5ce18ddd71a9
-- statement:
--   $ r = \frac{1}{3} \cdot a = \frac{1}{3} \cdot \frac{1}{2} s\sqrt{3} = \frac{s\sqrt{3}}{6} $
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_80978 (r a s : ℝ) : r = 1 / 3 * a ∧ a = 1 / 2 * s * Real.sqrt 3 → r = s * Real.sqrt 3 / 6   :=  by sorry
