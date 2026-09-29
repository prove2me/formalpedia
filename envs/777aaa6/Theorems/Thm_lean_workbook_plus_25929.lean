-- Prove2me | Theorems.Thm_lean_workbook_plus_25929
-- name    : lean_workbook_plus_25929
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.025447+00:00
-- url     : https://prove2.me/theorems/432b6289-f029-4f2d-8575-acd1145a9514
-- statement:
--   Identify the inequality used to prove the statement: $9(a^3 + b^3 + c^3) \geq (a + b + c)^3$ for nonnegative variables $a$, $b$, $c$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_25929 (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) : 9 * (a^3 + b^3 + c^3) ≥ (a + b + c)^3   :=  by sorry
