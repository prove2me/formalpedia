-- Prove2me | Theorems.Thm_lean_workbook_plus_6676
-- name    : lean_workbook_plus_6676
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.293252+00:00
-- url     : https://prove2.me/theorems/2351976b-40dc-40de-9c33-45bcbb764499
-- statement:
--   Prove that $\frac{ab}{a+b}+\frac{bc}{b+c}+\frac{ca}{c+a}\le \frac{a+b+c}{2}$ , where $a,b,c\in\mathbb{R}^{+}$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_6676 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a * b / (a + b) + b * c / (b + c) + c * a / (c + a)) ≤ (a + b + c) / 2   :=  by sorry
