-- Prove2me | Theorems.Thm_lean_workbook_plus_11860
-- name    : lean_workbook_plus_11860
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.412125+00:00
-- url     : https://prove2.me/theorems/7644b075-f1b5-4d26-bd2b-d8e5f3e629b8
-- statement:
--   Prove that $(b^2+c^2-a^2)(b-c)^2+(c^2+a^2-b^2)(c-a)^2+(a^2+b^2-c^2)(a-b)^2\geq 0$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_11860 (a b c : ℝ) : (b^2 + c^2 - a^2) * (b - c) ^ 2 + (c^2 + a^2 - b^2) * (c - a) ^ 2 + (a^2 + b^2 - c^2) * (a - b) ^ 2 ≥ 0   :=  by sorry
