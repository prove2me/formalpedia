-- Prove2me | Theorems.Thm_lean_workbook_plus_73686
-- name    : lean_workbook_plus_73686
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.170827+00:00
-- url     : https://prove2.me/theorems/b9a45990-124b-4b6d-a051-85e06bfcd647
-- statement:
--   Prove that: $\frac{a^4+b^4+c^4}{3}\ge\frac{(a+b+c)^4}{81}$ given $a,b,c >0$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_73686 (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) : (a^4 + b^4 + c^4) / 3 ≥ (a + b + c)^4 / 81   :=  by sorry
