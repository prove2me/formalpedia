-- Prove2me | Theorems.Thm_lean_workbook_plus_56349
-- name    : lean_workbook_plus_56349
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.366127+00:00
-- url     : https://prove2.me/theorems/807aded9-268e-4c34-80ff-6096e33864bb
-- statement:
--   Prove that $a^4 + \frac{1}{a^4} \ge a + \frac{1}{a}$ for $a \ge 1$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_56349 (a : ℝ) (h : a >= 1) : a^4 + 1/a^4 ≥ a + 1/a   :=  by sorry
