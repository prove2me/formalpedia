-- Prove2me | Theorems.Thm_lean_workbook_plus_63136
-- name    : lean_workbook_plus_63136
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.629978+00:00
-- url     : https://prove2.me/theorems/702f0322-e39f-4cf7-85ad-7895b715b0be
-- statement:
--   $2b\ge a+c$ (1), $2c\ge b+d$ (2), $2d\ge c+a$ (3), $2a\ge d+b$ (4)
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_63136 (a b c d : ℝ) (h1 : 2 * b ≥ a + c) (h2 : 2 * c ≥ b + d) (h3 : 2 * d ≥ c + a) (h4 : 2 * a ≥ d + b) : a + b + c + d ≤ 2 * (a + b) ∧ a + b + c + d ≤ 2 * (c + d) ∧ a + b + c + d ≤ 2 * (b + d) ∧ a + b + c + d ≤ 2 * (a + c)   :=  by sorry
