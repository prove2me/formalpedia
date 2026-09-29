-- Prove2me | Theorems.Thm_lean_workbook_plus_59222
-- name    : lean_workbook_plus_59222
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.496679+00:00
-- url     : https://prove2.me/theorems/e76e4aaa-d9ea-470f-a94f-6945223e9310
-- statement:
--   Prove that the dot product of two vectors $\vec{x}$ and $\vec{y}$ is equal to the product of their magnitudes and the cosine of the angle between them, using the Law of Cosines.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_59222 (x y : ℝ) : x • y = ‖x‖ * ‖y‖ * Real.cos (Real.arccos ((x • y) / (‖x‖ * ‖y‖)))   :=  by sorry
