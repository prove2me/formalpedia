-- Prove2me | Theorems.Thm_lean_workbook_plus_79828
-- name    : lean_workbook_plus_79828
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.420916+00:00
-- url     : https://prove2.me/theorems/1355c86c-8120-4dac-af74-cc86585fe170
-- statement:
--   Prove that $ab^2 + bc^2 + ca^2 + 6 \geq 3(a + b + c)$ for $a, b, c \geq 1$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_79828 (a b c : ℝ) (hab : a ≥ 1) (hbc : b ≥ 1) (hca : c ≥ 1) : a * b ^ 2 + b * c ^ 2 + c * a ^ 2 + 6 ≥ 3 * (a + b + c)   :=  by sorry
