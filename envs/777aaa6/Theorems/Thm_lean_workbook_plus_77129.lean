-- Prove2me | Theorems.Thm_lean_workbook_plus_77129
-- name    : lean_workbook_plus_77129
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.289288+00:00
-- url     : https://prove2.me/theorems/ad186df6-3925-4391-bfb6-b22e49ef2ef6
-- statement:
--   Let $a,b\geq 0$ and $a+b=4.$ Prove that:\n $$a+ab \leq \frac{25}{4}$$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_77129 (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab: a + b = 4) : a + a * b ≤ 25 / 4   :=  by sorry
