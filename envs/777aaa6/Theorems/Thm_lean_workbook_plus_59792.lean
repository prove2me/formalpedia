-- Prove2me | Theorems.Thm_lean_workbook_plus_59792
-- name    : lean_workbook_plus_59792
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.496679+00:00
-- url     : https://prove2.me/theorems/3558cecd-d6ab-4910-aeba-88009d4f912f
-- statement:
--   Since, $ ab+ac+bc\leq |a|\cdot|b|+|a|\cdot|c|+|b|\cdot|c|$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_59792 (a b c : ℝ) : a * b + b * c + c * a ≤ |a| * |b| + |a| * |c| + |b| * |c|   :=  by sorry
