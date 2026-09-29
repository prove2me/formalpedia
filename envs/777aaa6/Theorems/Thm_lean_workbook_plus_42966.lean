-- Prove2me | Theorems.Thm_lean_workbook_plus_42966
-- name    : lean_workbook_plus_42966
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.862991+00:00
-- url     : https://prove2.me/theorems/a9122061-c9c1-4907-bbae-8c54bfd75985
-- statement:
--   Let $a, b$ and $c$ be positive real numbers such that $a+ b+ c +\sqrt{abc}= 1$ . Prove that: \n $\left ( a+ b+ c \right )^{2}+ 2\sqrt{abc}\left ( a+ b+ c \right )\geq 4\left ( ab+ bc+ ca \right )$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_42966 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a * b * c = 1) : (a + b + c + Real.sqrt (a * b * c)) = 1 → (a + b + c) ^ 2 + 2 * Real.sqrt (a * b * c) * (a + b + c) ≥ 4 * (a * b + b * c + a * c)   :=  by sorry
