-- Prove2me | Theorems.Thm_lean_workbook_plus_57992
-- name    : lean_workbook_plus_57992
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.496679+00:00
-- url     : https://prove2.me/theorems/5ea9bc3b-a0e4-4d6f-9612-49d7d5b8e36e
-- statement:
--   Prove that $1-p^n<e^{-p^n}$ for $0<p\leq 1$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_57992 (n : ℕ) (p : ℝ) (hp0 : 0 < p) (hp1 : p ≤ 1) :
  (1 - p ^ n) < exp (-p ^ n)   :=  by sorry
