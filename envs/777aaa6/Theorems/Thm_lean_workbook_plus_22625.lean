-- Prove2me | Theorems.Thm_lean_workbook_plus_22625
-- name    : lean_workbook_plus_22625
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.916039+00:00
-- url     : https://prove2.me/theorems/979ad4f2-afc3-44a3-90be-2c20606c1a40
-- statement:
--   Solve $(a-1)x+(b-1)z = a+b$ given $ax = z+b$ and $bz = x+a$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_22625 (a b x z : ℝ) : a * x = z + b ∧ b * z = x + a → (a - 1) * x + (b - 1) * z = a + b   :=  by sorry
