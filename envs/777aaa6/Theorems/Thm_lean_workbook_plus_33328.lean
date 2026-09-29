-- Prove2me | Theorems.Thm_lean_workbook_plus_33328
-- name    : lean_workbook_plus_33328
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.431937+00:00
-- url     : https://prove2.me/theorems/b5c5e56d-e073-4c1a-87f1-4de629864428
-- statement:
--   Simplify the expression: $\sin x\cdot \left(\cos^{2}x-\cos^{2}\frac{\pi}{5}\right)\cdot \left(\cos^{2}x-\cos^{2}\frac{2\pi}{5}\right)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_33328 (x : ℝ) : sin x * (cos x ^ 2 - cos (π / 5) ^ 2) * (cos x ^ 2 - cos (2 * π / 5) ^ 2) = sin x * (cos x ^ 2 - cos (π / 5) ^ 2) * (cos x ^ 2 - cos (2 * π / 5) ^ 2)   :=  by sorry
