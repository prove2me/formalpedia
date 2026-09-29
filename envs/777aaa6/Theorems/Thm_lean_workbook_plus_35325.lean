-- Prove2me | Theorems.Thm_lean_workbook_plus_35325
-- name    : lean_workbook_plus_35325
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.431937+00:00
-- url     : https://prove2.me/theorems/10efc124-29d6-40db-b6f7-4708529c7486
-- statement:
--   Prove that if $ n^2 - 1$ is a factor of $ 2010$, then $ n$ cannot be 1.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_35325 (n : ℕ) : n^2 - 1 ∣ 2010 → n ≠ 1   :=  by sorry
