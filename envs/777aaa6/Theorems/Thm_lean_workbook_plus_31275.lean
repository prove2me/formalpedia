-- Prove2me | Theorems.Thm_lean_workbook_plus_31275
-- name    : lean_workbook_plus_31275
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.279436+00:00
-- url     : https://prove2.me/theorems/475cb488-4392-40f0-8352-43356ad80a1d
-- statement:
--   Let $a,b,c$ be positive real numbers. Prove that:\n $$\frac{1}{2a}+\frac{1}{2b} +\frac{1}{2c} \geq \frac{1}{a+b} +\frac{1}{b+c} +\frac{1}{c+a}$$\n\nUse this lemma \n $\frac{1}{a}+\frac{1}{b}\geq \frac{4}{a+b}$ for all $a,b>0$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_31275 (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) : (1 / (2 * a) + 1 / (2 * b) + 1 / (2 * c)) ≥ (1 / (a + b) + 1 / (b + c) + 1 / (c + a))   :=  by sorry
