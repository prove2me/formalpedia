-- Prove2me | Theorems.Thm_lean_workbook_plus_69971
-- name    : lean_workbook_plus_69971
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.897675+00:00
-- url     : https://prove2.me/theorems/7f615abd-7e42-4548-a1a1-00c533d21a51
-- statement:
--   Let $a,b$ be positive real numbers such that $k(a+b)=1+ab. $ $a+b+\frac{1}{a}+\frac{1}{b}\geq 4k.$ Where $k\geq 1.$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_69971 (k a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : k * (a + b) = 1 + a * b) (hk : 1 ≤ k) : a + b + 1 / a + 1 / b ≥ 4 * k   :=  by sorry
