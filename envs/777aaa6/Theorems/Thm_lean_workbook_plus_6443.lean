-- Prove2me | Theorems.Thm_lean_workbook_plus_6443
-- name    : lean_workbook_plus_6443
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.293252+00:00
-- url     : https://prove2.me/theorems/3ad54d10-a142-468e-9c86-4720ff712982
-- statement:
--   Given $a,b,c>0$ . Prove that $\frac{1}{a(b+1)}+\frac{1}{b(c+1)}+\frac{1}{c(a+1)}\ge \frac{1}{1+abc}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_6443 (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) : (1 / (a * (b + 1)) + 1 / (b * (c + 1)) + 1 / (c * (a + 1))) ≥ 1 / (1 + a * b * c)   :=  by sorry
