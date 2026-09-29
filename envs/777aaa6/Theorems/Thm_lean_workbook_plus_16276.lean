-- Prove2me | Theorems.Thm_lean_workbook_plus_16276
-- name    : lean_workbook_plus_16276
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.685829+00:00
-- url     : https://prove2.me/theorems/ea98a81c-5a2b-4951-9e28-6f3c77dc5e77
-- statement:
--   Prove that $(x-(z\cos B + y \cos C))^2 + (y \sin C - z\sin B)^2 \ge 0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_16276 (x y z : ℝ) (B C : ℝ) : (x - (z * Real.cos B + y * Real.cos C)) ^ 2 + (y * Real.sin C - z * Real.sin B) ^ 2 ≥ 0   :=  by sorry
