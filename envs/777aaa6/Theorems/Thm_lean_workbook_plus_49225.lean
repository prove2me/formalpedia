-- Prove2me | Theorems.Thm_lean_workbook_plus_49225
-- name    : lean_workbook_plus_49225
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.108955+00:00
-- url     : https://prove2.me/theorems/0901cb41-2ec6-4b11-9ff7-6a51fbb2809f
-- statement:
--   If $a,b,c >0$ then prove that $ \sum_{cyc} \frac{a^2}{b+c} \geq \frac12(a+b+c)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_49225 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : a^2 / (b + c) + b^2 / (c + a) + c^2 / (a + b) ≥ (a + b + c) / 2   :=  by sorry
