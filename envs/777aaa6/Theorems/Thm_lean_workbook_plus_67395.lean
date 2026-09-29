-- Prove2me | Theorems.Thm_lean_workbook_plus_67395
-- name    : lean_workbook_plus_67395
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.897675+00:00
-- url     : https://prove2.me/theorems/618f37f1-2210-4113-8af7-1597f821673a
-- statement:
--   Let $a, b, c$ be positive real number such that: $a^2+b^2+c^2=1$ . Prove that:\n $\frac{a+b}{1-ab} +\frac{b+c}{1-bc} +\frac{a+c}{1-ac} \leq 3(a+b+c)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_67395 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a * b * c = 1) (h : a^2 + b^2 + c^2 = 1) :
  (a + b) / (1 - a * b) + (b + c) / (1 - b * c) + (a + c) / (1 - a * c) ≤ 3 * (a + b + c)   :=  by sorry
