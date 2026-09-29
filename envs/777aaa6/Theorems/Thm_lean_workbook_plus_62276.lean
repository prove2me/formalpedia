-- Prove2me | Theorems.Thm_lean_workbook_plus_62276
-- name    : lean_workbook_plus_62276
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.629978+00:00
-- url     : https://prove2.me/theorems/b98433dc-0448-4e64-b778-2f0c087e532e
-- statement:
--   If ${a\geq b\geq 0,\ c\geq d\geq 0,\ a\leq c}$ and ${ab\leq cd}$ , then prove that ${a+b\leq c+d}$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_62276 (a b c d : ℝ) (h1 : a ≥ b ∧ b ≥ 0) (h2 : c ≥ d ∧ d ≥ 0) (h3 : a ≤ c) (h4 : a * b ≤ c * d) : a + b ≤ c + d   :=  by sorry
