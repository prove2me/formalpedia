-- Prove2me | Theorems.Thm_lean_workbook_plus_14940
-- name    : lean_workbook_plus_14940
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.554211+00:00
-- url     : https://prove2.me/theorems/781f8b3b-abe8-4022-9f90-e92f78752691
-- statement:
--   Prove the lemma: If $a$ and $b$ are non-negative reals, with $a+b \leq 1$ , then $a^2+b^2 \leq 1$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_14940 (a b : ℝ) (h1 : 0 ≤ a ∧ 0 ≤ b) (h2 : a + b ≤ 1) : a^2 + b^2 ≤ 1   :=  by sorry
