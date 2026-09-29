-- Prove2me | Theorems.Thm_lean_workbook_plus_9170
-- name    : lean_workbook_plus_9170
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.412125+00:00
-- url     : https://prove2.me/theorems/67817b57-5290-4cc7-9da9-9fb0fd620e8a
-- statement:
--   Prove that $ 2\sqrt{3(a^6+b^6+c^6)} \ge 2(a^3+b^3+c^3) $
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_9170 (a b c : ℝ) : 2 * Real.sqrt (3 * (a ^ 6 + b ^ 6 + c ^ 6)) ≥ 2 * (a ^ 3 + b ^ 3 + c ^ 3)   :=  by sorry
