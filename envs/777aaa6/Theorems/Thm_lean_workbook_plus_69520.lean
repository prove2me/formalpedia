-- Prove2me | Theorems.Thm_lean_workbook_plus_69520
-- name    : lean_workbook_plus_69520
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.897675+00:00
-- url     : https://prove2.me/theorems/4f407d8c-9d89-4726-ab7b-3a122008a322
-- statement:
--   If $a,b\in \mathbb{R}$ have different signs (0 is allowed), then $|a+b|\le \max(|a|,|b|)$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_69520 (a b : ℝ) (hab : a * b < 0) :
  |a + b| ≤ max (|a|) (|b|)   :=  by sorry
