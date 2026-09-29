-- Prove2me | Theorems.Thm_lean_workbook_plus_21236
-- name    : lean_workbook_plus_21236
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.916039+00:00
-- url     : https://prove2.me/theorems/4ff313ac-ad77-4e1a-ac30-7f834c51df14
-- statement:
--   Complete the proof by squaring and showing the result is non-negative:\n$4\left(\sum_{i=1}^n u_iv_i -\frac{1}{2}\right)^2 \geqq 0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_21236 (n : ℕ) (u v : Fin n → ℝ) :
  4 * (∑ i, u i * v i - 1 / 2) ^ 2 ≥ 0   :=  by sorry
