-- Prove2me | Theorems.Thm_lean_workbook_plus_39194
-- name    : lean_workbook_plus_39194
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.715658+00:00
-- url     : https://prove2.me/theorems/6054da69-53fe-4dd2-8a86-797c6cdee969
-- statement:
--   $a,c$ have the same imaginary parts, $b$ is purely imaginary
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_39194 (a b c : ℂ) (h₁ : a.im = c.im) (h₂ : b.im = 0) : a * b * c = a * c * b   :=  by sorry
