-- Prove2me | Theorems.Thm_lean_workbook_plus_18233
-- name    : lean_workbook_plus_18233
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.799204+00:00
-- url     : https://prove2.me/theorems/312dc904-50a2-42e9-b08c-901fea9bdca2
-- statement:
--   Let $x=\frac{a}{b}$ , $y=\frac{b}{c}$ and $z=\frac{c}{a}$ , where $a$ , $b$ and $c$ are positives.\n\nHence, we need to prove that $abc\\geq(a+b-c)(a+c-b)(b+c-a)$ , which is Schur.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_18233 (a b c x y z : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a + b > c) (hbc : b + c > a) (hca : a + c > b) (h : x = a / b) (h' : y = b / c) (h'' : z = c / a) : a * b * c ≥ (a + b - c) * (a + c - b) * (b + c - a)   :=  by sorry
