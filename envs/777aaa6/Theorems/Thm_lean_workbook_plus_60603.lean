-- Prove2me | Theorems.Thm_lean_workbook_plus_60603
-- name    : lean_workbook_plus_60603
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.496679+00:00
-- url     : https://prove2.me/theorems/ab2395d5-6d04-4d53-909d-bc4c8f5b75e1
-- statement:
--   Prove $\cos y - \cos x = 2 \sin{\frac{x + y}{2} \sin{\frac{x - y}{2}}}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_60603 (x y : ℝ) : Real.cos y - Real.cos x = 2 * Real.sin ((x + y) / 2) * Real.sin ((x - y) / 2)   :=  by sorry
