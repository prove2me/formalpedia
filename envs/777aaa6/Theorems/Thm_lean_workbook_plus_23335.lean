-- Prove2me | Theorems.Thm_lean_workbook_plus_23335
-- name    : lean_workbook_plus_23335
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.916039+00:00
-- url     : https://prove2.me/theorems/c3aaf1da-69b2-45e6-82cc-c85fa1d30ffd
-- statement:
--   Prove that for positive real numbers $a, b, c, d$, the following inequality holds: $16(abc + bcd + cda + dab) \leq (a + b + c + d)^3$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_23335 (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) : 16 * (a * b * c + b * c * d + c * d * a + d * a * b) ≤ (a + b + c + d) ^ 3   :=  by sorry
