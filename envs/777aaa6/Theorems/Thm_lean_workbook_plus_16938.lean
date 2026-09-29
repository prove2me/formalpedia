-- Prove2me | Theorems.Thm_lean_workbook_plus_16938
-- name    : lean_workbook_plus_16938
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.685829+00:00
-- url     : https://prove2.me/theorems/cc0b9b8f-b0ba-4844-9bd2-d1fe325490ad
-- statement:
--   Prove $ a + a^3 \ge 2a^2$ given $ a > 0$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_16938 (a : ℝ) (h : a > 0) : a + a^3 ≥ 2 * a^2   :=  by sorry
