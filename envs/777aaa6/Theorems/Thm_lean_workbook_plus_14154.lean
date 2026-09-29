-- Prove2me | Theorems.Thm_lean_workbook_plus_14154
-- name    : lean_workbook_plus_14154
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.554211+00:00
-- url     : https://prove2.me/theorems/5aa89907-de50-4330-95c1-a378f98bf756
-- statement:
--   Let $a$ and $b$ be some fixed positive real numbers. There clearly exists some rational number $Q$ such that $bQ>1$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_14154 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) : ∃ Q : ℚ, b * Q > 1   :=  by sorry
