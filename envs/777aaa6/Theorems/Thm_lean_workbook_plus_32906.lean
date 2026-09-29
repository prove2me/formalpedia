-- Prove2me | Theorems.Thm_lean_workbook_plus_32906
-- name    : lean_workbook_plus_32906
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.431937+00:00
-- url     : https://prove2.me/theorems/7b09cc4c-8d28-4278-aefd-0f9757d4b2cf
-- statement:
--   If $a, b, c, d$ are real positives that satisfy: $a + b + c + d = \frac{1}{a} + \frac{1}{b} + \frac{1}{c} + \frac{1}{d}$.\nProve that $ab + ac + ad + bc + bd + cd \geq 6abcd$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_32906 (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) (hab : a + b + c + d = 1 / a + 1 / b + 1 / c + 1 / d) : a * b + a * c + a * d + b * c + b * d + c * d ≥ 6 * a * b * c * d   :=  by sorry
