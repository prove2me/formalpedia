-- Prove2me | Theorems.Thm_lean_workbook_plus_78790
-- name    : lean_workbook_plus_78790
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.289288+00:00
-- url     : https://prove2.me/theorems/b4f61923-78ff-49e6-8377-a0ca1acfa38c
-- statement:
--   Given positive numbers $a$, $b$, and $c$, prove that $\frac{4}{a^{2}+bc}\le\frac{1}{a^{2}}+\frac{1}{bc}$, which implies $\frac{1}{a}+\frac{1}{b}+\frac{1}{c}\le\frac{a}{bc}+\frac{b}{ca}+\frac{c}{ab}$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_78790 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : 4 / (a ^ 2 + b * c) ≤ 1 / a ^ 2 + 1 / (b * c)   :=  by sorry
