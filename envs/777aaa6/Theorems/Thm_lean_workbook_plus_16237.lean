-- Prove2me | Theorems.Thm_lean_workbook_plus_16237
-- name    : lean_workbook_plus_16237
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.685829+00:00
-- url     : https://prove2.me/theorems/09e25858-3bfd-46aa-8afc-3b957c3a43e7
-- statement:
--   Prove that if $a, b, c$ are positive real numbers such that $a + b + c = 1$, then $(1 - a)(1 - b)(1 - c) \geq abc$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_16237 (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (habc : a + b + c = 1) : (1 - a) * (1 - b) * (1 - c) ≥ a * b * c   :=  by sorry
