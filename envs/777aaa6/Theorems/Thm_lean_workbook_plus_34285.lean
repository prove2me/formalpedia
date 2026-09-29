-- Prove2me | Theorems.Thm_lean_workbook_plus_34285
-- name    : lean_workbook_plus_34285
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.431937+00:00
-- url     : https://prove2.me/theorems/2e0396a4-2840-4fa9-aeb7-6a5eced4a2cb
-- statement:
--   Prove that $[n + m]!$ is divisible by $ [n]! \times [m]!$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_34285 : ∀ n m : ℕ, n.factorial * m.factorial ∣ (n + m).factorial   :=  by sorry
