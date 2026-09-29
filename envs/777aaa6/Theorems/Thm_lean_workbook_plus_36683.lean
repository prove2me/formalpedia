-- Prove2me | Theorems.Thm_lean_workbook_plus_36683
-- name    : lean_workbook_plus_36683
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.562161+00:00
-- url     : https://prove2.me/theorems/70123f0a-e03f-4e7c-83b2-f078dfe84ef4
-- statement:
--   Using the same substitution as above. We have $0 < z \leq y \leq x$ , and\n\n$\sum_{\mathrm{cyc}}(s-a)\frac{c-b}{a} = \sum_{\mathrm{cyc}}x\frac{y-z}{y+z} = \frac{(x-y)(x-z)(y-z)(x+y+z)}{(x+y)(x+z)(y+z)}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_36683 :
  ∀ x y z : ℝ,
    0 < x ∧ 0 < y ∧ 0 < z →
    x ≤ y ∧ y ≤ z ∧ z ≤ x →
    0 ≤ (x - y) * (x - z) * (y - z) * (x + y + z) / (x + y) / (x + z) / (y + z)   :=  by sorry
