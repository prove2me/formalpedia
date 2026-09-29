-- Prove2me | Theorems.Thm_lean_workbook_plus_15227
-- name    : lean_workbook_plus_15227
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.685829+00:00
-- url     : https://prove2.me/theorems/2a4ed9c5-3890-4f4d-8957-a8dbf5e620b0
-- statement:
--   Let be given a triangle $ABC.$ Prove that: $1+\cos A\cos B\cos C\ge \sqrt{3}\sin A\sin B\sin C$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_15227 : ∀ A B C : ℝ, (1 + Real.cos A * Real.cos B * Real.cos C) ≥ Real.sqrt 3 * Real.sin A * Real.sin B * Real.sin C   :=  by sorry
