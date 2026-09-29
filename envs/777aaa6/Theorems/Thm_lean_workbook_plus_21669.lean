-- Prove2me | Theorems.Thm_lean_workbook_plus_21669
-- name    : lean_workbook_plus_21669
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.916039+00:00
-- url     : https://prove2.me/theorems/b50520d6-0f1c-401b-b76f-8ee0308bfc9c
-- statement:
--   Deduce that $\frac{140}{99} < \sqrt{2} < \frac{99}{70}$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_21669 : (140 : ℝ) / 99 < Real.sqrt 2 ∧ Real.sqrt 2 < 99 / 70   :=  by sorry
