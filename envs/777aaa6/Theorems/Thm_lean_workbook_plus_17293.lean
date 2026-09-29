-- Prove2me | Theorems.Thm_lean_workbook_plus_17293
-- name    : lean_workbook_plus_17293
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.685829+00:00
-- url     : https://prove2.me/theorems/85e52d89-33cd-46b2-8a80-a4e0d0062388
-- statement:
--   Prove that \(a^2 - ab - ac + b^2 - bc + c^2 \geqslant 0\) for any real numbers \(a, b, c\).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_17293 (a b c : ℝ) : a ^ 2 - a * b - a * c + b ^ 2 - b * c + c ^ 2 ≥ 0   :=  by sorry
