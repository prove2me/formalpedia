-- Prove2me | Theorems.Thm_lean_workbook_plus_21575
-- name    : lean_workbook_plus_21575
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.916039+00:00
-- url     : https://prove2.me/theorems/d7d954ad-0be8-4a3c-b502-06e82ece9bfe
-- statement:
--   Let $a,b,c> 1$ three distinct natural numbers , prove that $(1+\frac{1}{a})(2+\frac{1}{b})(3+\frac{1}{c})\leq\frac{91}{8}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_21575 (a b c : ℕ) (hab : a ≠ b) (hbc : b ≠ c) (hca : c ≠ a) (ha : 1 < a) (hb : 1 < b) (hc : 1 < c) : (1 + 1 / a) * (2 + 1 / b) * (3 + 1 / c) ≤ 91 / 8   :=  by sorry
