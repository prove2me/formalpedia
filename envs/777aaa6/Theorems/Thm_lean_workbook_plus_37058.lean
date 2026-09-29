-- Prove2me | Theorems.Thm_lean_workbook_plus_37058
-- name    : lean_workbook_plus_37058
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.562161+00:00
-- url     : https://prove2.me/theorems/d5208295-197e-451a-8bed-b343ef811c78
-- statement:
--   Let $a,b,c> 0 .$ Prove that $$ \dfrac{1}{\dfrac{a}{b+c}+\dfrac{1}{ 2}}+\dfrac{1}{\dfrac{b}{c+a}+\dfrac{1}{4}}+\dfrac{1}{\dfrac{c}{a+b}+\dfrac{1}{ 2}}\geq \dfrac{16}{5}$$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_37058 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (1 / (a / (b + c) + 1 / 2) + 1 / (b / (c + a) + 1 / 4) + 1 / (c / (a + b) + 1 / 2)) ≥ 16 / 5   :=  by sorry
