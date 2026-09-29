-- Prove2me | Theorems.Thm_lean_workbook_plus_61076
-- name    : lean_workbook_plus_61076
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.629978+00:00
-- url     : https://prove2.me/theorems/3369aa7c-70c6-4817-9c64-6bc9d1215831
-- statement:
--   Let $a,b,c\geq 0 $ and $\frac{a}{a+1}+\frac{2b}{b+1}+\frac{2c}{c+1}=1 .$ Prove that $abc\leq \frac{1}{48}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_61076 (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (habc : a * b * c = 1) : a / (a + 1) + 2 * b / (b + 1) + 2 * c / (c + 1) = 1 → a * b * c ≤ 1 / 48   :=  by sorry
