-- Prove2me | Theorems.Thm_lean_workbook_plus_67811
-- name    : lean_workbook_plus_67811
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.897675+00:00
-- url     : https://prove2.me/theorems/73c037b6-04e7-498d-998a-083fd7a9225a
-- statement:
--   Prove that $\forall n \in N, 11^{n}-4^{n}$ is divisible by 7.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_67811 : ∀ n : ℕ, 7 ∣ (11^n - 4^n)   :=  by sorry
