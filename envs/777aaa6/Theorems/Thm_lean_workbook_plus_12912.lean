-- Prove2me | Theorems.Thm_lean_workbook_plus_12912
-- name    : lean_workbook_plus_12912
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.554211+00:00
-- url     : https://prove2.me/theorems/f52b5e3f-1d38-4d3e-b360-fa1b31af8df3
-- statement:
--   $\cos^2(x) \cdot \cot(x) + \sin^2(x) \cdot \tan(x) \geq 1$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_12912 : ∀ x : ℝ, (cos x)^2 * (1 / tan x) + (sin x)^2 * tan x ≥ 1   :=  by sorry
