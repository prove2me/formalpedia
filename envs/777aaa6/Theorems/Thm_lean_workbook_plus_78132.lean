-- Prove2me | Theorems.Thm_lean_workbook_plus_78132
-- name    : lean_workbook_plus_78132
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.289288+00:00
-- url     : https://prove2.me/theorems/70d86133-79f9-4277-a3a9-21379f06f0f2
-- statement:
--   Let $a,b,c\geq \frac{3}{2}.$ Prove that $a+b+c\geq \frac{3}{2}\left( \frac{1}{a}+ \frac{1}{b}+ \frac{1}{c}+1\right) $
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_78132 (a b c : ℝ) (ha : 3 / 2 ≤ a) (hb : 3 / 2 ≤ b) (hc : 3 / 2 ≤ c) : a + b + c ≥ 3 / 2 * (1 / a + 1 / b + 1 / c + 1)   :=  by sorry
