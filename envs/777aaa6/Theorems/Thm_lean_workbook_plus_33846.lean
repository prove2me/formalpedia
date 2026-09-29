-- Prove2me | Theorems.Thm_lean_workbook_plus_33846
-- name    : lean_workbook_plus_33846
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.431937+00:00
-- url     : https://prove2.me/theorems/f0225396-9596-4f12-978e-276a65513b7d
-- statement:
--   Prove that for all positive real numbers $a$, $b$, and $c$, the following inequality holds: $\frac{a+b}{3a+2b+c}+\frac{b+c}{3b+2c+a}+\frac{c+a}{3c+2a+b} \leq 1$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_33846 (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) : (a + b) / (3 * a + 2 * b + c) + (b + c) / (3 * b + 2 * c + a) + (c + a) / (3 * c + 2 * a + b) ≤ 1   :=  by sorry
