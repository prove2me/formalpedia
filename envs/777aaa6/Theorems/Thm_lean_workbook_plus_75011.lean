-- Prove2me | Theorems.Thm_lean_workbook_plus_75011
-- name    : lean_workbook_plus_75011
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.170827+00:00
-- url     : https://prove2.me/theorems/abc90758-0952-4c93-ab1f-89054a0c16be
-- statement:
--   It suffices to prove that $ (x+y)^{2}\ge 4xy $ and $ (x+z)^{2}\ge 4xz $ <=> $ (x-y)^{2}\ge 0$ and $ (x-z)^{2}\ge0 $ It is true
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_75011 (x y z : ℝ) : (x + y) ^ 2 ≥ 4 * x * y ∧ (x + z) ^ 2 ≥ 4 * x * z ↔ (x - y) ^ 2 ≥ 0 ∧ (x - z) ^ 2 ≥ 0   :=  by sorry
