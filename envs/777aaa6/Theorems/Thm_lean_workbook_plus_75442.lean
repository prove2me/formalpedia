-- Prove2me | Theorems.Thm_lean_workbook_plus_75442
-- name    : lean_workbook_plus_75442
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.170827+00:00
-- url     : https://prove2.me/theorems/87f0c8aa-1022-45b4-b79b-324b55c576de
-- statement:
--   <1> Given positive real numbers $a,\ b,\ c$ . Prove that : $\frac{a^2}{a+b}+\frac{b^2}{b+c}+\frac{c^2}{c+a}\geq \frac{a+b+c}{2}.$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_75442 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a^2 / (a + b) + b^2 / (b + c) + c^2 / (c + a)) ≥ (a + b + c) / 2   :=  by sorry
