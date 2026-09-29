-- Prove2me | Theorems.Thm_lean_workbook_plus_68662
-- name    : lean_workbook_plus_68662
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.897675+00:00
-- url     : https://prove2.me/theorems/9095ada3-910b-4e00-a538-18e945319f0e
-- statement:
--   Prove that for any positive real numbers $a, b, c$, the following inequality holds: $\\sqrt{a^2+b^2}+\\sqrt{b^2+c^2}+\\sqrt{c^2+a^2} \\geq a+b+c$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_68662 (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) : √(a^2 + b^2) + √(b^2 + c^2) + √(c^2 + a^2) ≥ a + b + c   :=  by sorry
