-- Prove2me | Theorems.Thm_lean_workbook_plus_68809
-- name    : lean_workbook_plus_68809
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.897675+00:00
-- url     : https://prove2.me/theorems/cfe24282-9b4b-4c4e-8def-b067128ea428
-- statement:
--   Let $a,b,c>0$ Prove that: $ \frac{a-b}{b+c }+ \frac{b-c}{c+a } \geq \frac{a-c}{a+b } $
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_68809 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a - b) / (b + c) + (b - c) / (c + a) ≥ (a - c) / (a + b)   :=  by sorry
