-- Prove2me | Theorems.Thm_lean_workbook_plus_26459
-- name    : lean_workbook_plus_26459
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.025447+00:00
-- url     : https://prove2.me/theorems/4273d5f5-48c7-45de-b54f-ace2e47d78de
-- statement:
--   Let $a,b,c>0$ and $a^2+b^2+c^2=2(ab+bc+ca).$ Prove that \n $$ \frac{a+kb}{c} \geq \frac{k}{k+1} $$ Where $k>0 .$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_26459 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a + b > c) (h : a^2 + b^2 + c^2 = 2 * (a * b + b * c + c * a)) (k : ℝ) (hk : k > 0) : (a + k * b) / c ≥ k / (k + 1)   :=  by sorry
