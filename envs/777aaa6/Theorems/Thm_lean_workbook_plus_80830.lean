-- Prove2me | Theorems.Thm_lean_workbook_plus_80830
-- name    : lean_workbook_plus_80830
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.420916+00:00
-- url     : https://prove2.me/theorems/c55e957d-b443-4e5f-b2c5-030e1a5bd0d6
-- statement:
--   Prove the given algebraic identity: $(n+1)^2 = n^2 + 2n + 1 = n^2 + n + (n+1)$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_80830 (n : ℕ) : (n+1)^2 = n^2 + 2*n + 1 ∧ (n+1)^2 = n^2 + n + (n+1)   :=  by sorry
