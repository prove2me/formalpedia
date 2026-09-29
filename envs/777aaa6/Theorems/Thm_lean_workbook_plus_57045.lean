-- Prove2me | Theorems.Thm_lean_workbook_plus_57045
-- name    : lean_workbook_plus_57045
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.366127+00:00
-- url     : https://prove2.me/theorems/8ec99af1-b468-4f61-97a3-e77ebf20599a
-- statement:
--   > $ x(x-4)\leq 0$ <-> $ 0\leq x \leq 4$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_57045 (x : ℝ) : x * (x - 4) ≤ 0 ↔ 0 ≤ x ∧ x ≤ 4   :=  by sorry
