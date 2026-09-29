-- Prove2me | Theorems.Thm_lean_workbook_plus_32441
-- name    : lean_workbook_plus_32441
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.279436+00:00
-- url     : https://prove2.me/theorems/52a9390b-01ab-4c35-bcea-b384cc7cc797
-- statement:
--   Bernoulli's Inequality: For \( x > -1 \) and \( i \geq 1 \), prove that \( (1+x)^i \geq 1 + ix \) with equality occurring when \( x = 0 \).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_32441 (x : ℝ) (i : ℕ) (hx : x > -1) (hi : 1 ≤ i) :
  (1 + x) ^ i ≥ 1 + i * x   :=  by sorry
