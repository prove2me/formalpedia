-- Prove2me | Theorems.Thm_lean_workbook_plus_22423
-- name    : lean_workbook_plus_22423
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.916039+00:00
-- url     : https://prove2.me/theorems/53f7f3ff-3602-4828-b390-9add2c5d4791
-- statement:
--   ${(\sqrt{\sin^2{x}+\cos{x}}+\sqrt{\cos^2{x}+\sin{x}})^2\le 2(1+\cos{x}}+\sin{x})$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_22423 : ∀ x : ℝ, (Real.sqrt (sin x ^ 2 + cos x) + Real.sqrt (cos x ^ 2 + sin x)) ^ 2 ≤ 2 * (1 + cos x + sin x)   :=  by sorry
