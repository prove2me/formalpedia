-- Prove2me | Theorems.Thm_lean_workbook_plus_16774
-- name    : lean_workbook_plus_16774
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.685829+00:00
-- url     : https://prove2.me/theorems/7b430224-b25d-4773-acbf-60a9f3a56786
-- statement:
--   $a^2=1+a$ => $a=\frac{1\pm \sqrt{5}}{2}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_16774 (a : ℝ) (h : a^2 = 1 + a) : a = (1 + Real.sqrt 5) / 2 ∨ a = (1 - Real.sqrt 5) / 2   :=  by sorry
