-- Prove2me | Theorems.Thm_lean_workbook_plus_76564
-- name    : lean_workbook_plus_76564
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.289288+00:00
-- url     : https://prove2.me/theorems/6a900c0c-fa6e-410c-adac-be9d65718c87
-- statement:
--   A neat way is through complex numbers. Say we have $a+bi, c+di$ . Then $|a+bi||c+di| = (a^2+b^2)(b^2+c^2) = |(ac-bd)+i(ad+bc)| = (ac-bd)^2+(ad+bc)^2$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_76564 : ∀ a b c d : ℝ, (a * c - b * d) ^ 2 + (a * d + b * c) ^ 2 = (a ^ 2 + b ^ 2) * (c ^ 2 + d ^ 2)   :=  by sorry
