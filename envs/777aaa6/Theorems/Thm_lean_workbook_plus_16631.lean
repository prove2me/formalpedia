-- Prove2me | Theorems.Thm_lean_workbook_plus_16631
-- name    : lean_workbook_plus_16631
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.685829+00:00
-- url     : https://prove2.me/theorems/140a39f2-ab93-48df-91af-61a3a33ebe35
-- statement:
--   Prove that \(\frac{\sqrt{2s / a}}{\sqrt{2s / a'}} = \sqrt{\frac{2s / a}{2s / a'}} = \sqrt{\frac{a'}{a}}\) for positive \(a, a', s\).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_16631 (a a' s : ℝ) (ha : 0 < a) (ha' : 0 < a') (hs : 0 < s) : √((2 * s) / a) / √((2 * s) / a') = √(a' / a)   :=  by sorry
