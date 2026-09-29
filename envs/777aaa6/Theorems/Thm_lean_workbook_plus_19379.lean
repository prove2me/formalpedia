-- Prove2me | Theorems.Thm_lean_workbook_plus_19379
-- name    : lean_workbook_plus_19379
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.799204+00:00
-- url     : https://prove2.me/theorems/29cf79bc-c978-4461-b1df-79ba1b418e31
-- statement:
--   Results $1\le 2-\sin x+\cos x\le 3, \forall x\in\left[0,\dfrac{\pi}{2} \right]\Longrightarrow$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_19379 (x: ℝ) (hx: 0 ≤ x ∧ x ≤ π/2) :
  1 ≤ 2 - Real.sin x + Real.cos x ∧ 2 - Real.sin x + Real.cos x ≤ 3   :=  by sorry
