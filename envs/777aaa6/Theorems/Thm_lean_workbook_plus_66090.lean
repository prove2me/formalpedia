-- Prove2me | Theorems.Thm_lean_workbook_plus_66090
-- name    : lean_workbook_plus_66090
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.755244+00:00
-- url     : https://prove2.me/theorems/3715f390-7a31-47d6-877f-3a0453b2f011
-- statement:
--   For positive $a$ , $b$ and real $k$ : \n\n $\frac{(1+k)a+b(k-2+\\frac{b}{a})}{a+b} \geq k$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_66090 (a b k : ℝ) (ha : 0 < a) (hb : 0 < b) : (1 + k) * a + b * (k - 2 + b / a) ≥ k * (a + b)   :=  by sorry
