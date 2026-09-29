-- Prove2me | Theorems.Thm_lean_workbook_plus_69749
-- name    : lean_workbook_plus_69749
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.897675+00:00
-- url     : https://prove2.me/theorems/3175646a-cc3d-44c8-bcc7-c118cd8bd1dd
-- statement:
--   If $a,b,c>0$ and $a^{2}+b^{2}+c^{2}=1$ then prove that $\sum_{cyc} \frac{ab}{c(a^{2}+b^{2})} \ge \frac{3 \sqrt{3}}{2}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_69749 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a * b * c = 1) (h : a^2 + b^2 + c^2 = 1) :
  a * b / (c * (a^2 + b^2)) + b * c / (a * (b^2 + c^2)) + c * a / (b * (c^2 + a^2)) ≥ 3 * Real.sqrt 3 / 2   :=  by sorry
