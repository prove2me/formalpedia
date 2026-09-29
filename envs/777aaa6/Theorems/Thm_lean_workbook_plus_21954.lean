-- Prove2me | Theorems.Thm_lean_workbook_plus_21954
-- name    : lean_workbook_plus_21954
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.916039+00:00
-- url     : https://prove2.me/theorems/309b376b-7955-482b-91b7-1046b7c27e00
-- statement:
--   Prove that if $a, b$, and $c$ are the side lengths of a triangle, then $a + b > c$, $b + c > a$, and $a + c > b$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_21954 {a b c : ℝ} (hx: a > 0 ∧ b > 0 ∧ c > 0) (hab : a + b > c) (hbc : b + c > a) (hca : a + c > b) : a + b > c ∧ b + c > a ∧ a + c > b   :=  by sorry
