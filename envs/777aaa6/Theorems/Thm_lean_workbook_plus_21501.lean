-- Prove2me | Theorems.Thm_lean_workbook_plus_21501
-- name    : lean_workbook_plus_21501
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.916039+00:00
-- url     : https://prove2.me/theorems/ed229252-a0f6-478f-92e4-2e5925e592c5
-- statement:
--   Let $a,b,c$ be positive real numbers . Prove that $ \frac{b}{a}+\frac{a}{b+c}+\frac{c}{a}\ge 2.$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_21501 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (b / a + a / (b + c) + c / a) ≥ 2   :=  by sorry
