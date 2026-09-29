-- Prove2me | Theorems.Thm_lean_workbook_plus_80900
-- name    : lean_workbook_plus_80900
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.420916+00:00
-- url     : https://prove2.me/theorems/e8823bd3-52d2-464c-aa88-b62b03dc7dbd
-- statement:
--   Let $ a\ge b\ge c\ge d$ be real numbers such that $ a+b+c+d=2$ . Prove that $ a^2+2bc+d^2\ge 1.$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_80900 (a b c d : ℝ) (h1 : a ≥ b ∧ b ≥ c ∧ c ≥ d) (h2 : a + b + c + d = 2) : a^2 + 2 * b * c + d^2 ≥ 1   :=  by sorry
