-- Prove2me | Theorems.Thm_lean_workbook_plus_12249
-- name    : lean_workbook_plus_12249
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.554211+00:00
-- url     : https://prove2.me/theorems/e56757b1-a030-4ce6-8005-ca77b430aaa2
-- statement:
--   Prove that $ x(1 - x)(5 - x) \ge 0$ for all $ x \in (0,1)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_12249 (x : ℝ) (hx : 0 < x ∧ x < 1) :
  x * (1 - x) * (5 - x) ≥ 0   :=  by sorry
