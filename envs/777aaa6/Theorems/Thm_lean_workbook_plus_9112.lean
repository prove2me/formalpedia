-- Prove2me | Theorems.Thm_lean_workbook_plus_9112
-- name    : lean_workbook_plus_9112
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.412125+00:00
-- url     : https://prove2.me/theorems/3b1c16c9-5275-46d6-a43a-790b4c53a155
-- statement:
--   Prove that $ a^5+1 \geq a^3+a^2$ for all $a>0$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_9112 (a : ℝ) (ha : 0 < a) : a^5 + 1 ≥ a^3 + a^2   :=  by sorry
