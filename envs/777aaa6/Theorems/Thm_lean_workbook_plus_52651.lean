-- Prove2me | Theorems.Thm_lean_workbook_plus_52651
-- name    : lean_workbook_plus_52651
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.231389+00:00
-- url     : https://prove2.me/theorems/cafd14ad-aff3-4093-8a0c-f11b5cc14faa
-- statement:
--   Arithmetic Mean - Quadratic Mean (or Root-Mean Square, you might know it as that) $\frac{a+b+c}{3} \le \sqrt{\frac{a^2+b^2+c^2}{3}}$ exactly as used above.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_52651 (a b c : ℝ) : (a + b + c) / 3 ≤ Real.sqrt ((a ^ 2 + b ^ 2 + c ^ 2) / 3)   :=  by sorry
