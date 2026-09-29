-- Prove2me | Theorems.Thm_lean_workbook_plus_61018
-- name    : lean_workbook_plus_61018
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.629978+00:00
-- url     : https://prove2.me/theorems/2a70731e-a321-4b64-a0c3-20f07f86febc
-- statement:
--   Prove that $\frac{a^3}{a^2+ab+b^2} \ge \frac{2a-b}{3}$ for positive reals $a$ and $b$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_61018 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) : (a^3 / (a^2 + a * b + b^2) : ℝ) ≥ (2 * a - b) / 3   :=  by sorry
