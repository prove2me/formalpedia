-- Prove2me | Theorems.Thm_lean_workbook_plus_62504
-- name    : lean_workbook_plus_62504
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.629978+00:00
-- url     : https://prove2.me/theorems/db0a3103-9f4e-4f03-9493-289532694e34
-- statement:
--   Let $a$ , $b$ , and $c$ be positive real numbers. Prove that $$(a+b+c)(ab+bc+ca)\ge9abc,$$ and find the equality condition.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_62504 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a + b + c) * (a * b + b * c + c * a) ≥ 9 * a * b * c   :=  by sorry
