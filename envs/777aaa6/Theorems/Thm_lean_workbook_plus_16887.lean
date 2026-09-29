-- Prove2me | Theorems.Thm_lean_workbook_plus_16887
-- name    : lean_workbook_plus_16887
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.685829+00:00
-- url     : https://prove2.me/theorems/8206a58c-3abd-42fd-a3d9-69a1b1b2614e
-- statement:
--   By Trivial Inequality, $(a-b)^2 + (b-c)^2 + (c-a)^2\ge 0 \Longleftrightarrow a^2 +b^2 + c^2\ge ab +bc+ca$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_16887 (a b c : ℝ) :  (a - b) ^ 2 + (b - c) ^ 2 + (c - a) ^ 2 ≥ 0 ↔ a ^ 2 + b ^ 2 + c ^ 2 ≥ a * b + b * c + c * a   :=  by sorry
