-- Prove2me | Theorems.Thm_lean_workbook_plus_51564
-- name    : lean_workbook_plus_51564
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.231389+00:00
-- url     : https://prove2.me/theorems/eed219fd-9fe2-4c1d-bdc9-5bbdeda0f160
-- statement:
--   Illustrate that $_nC_0$ represents choosing 0 things, which can only be done in 1 way
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_51564 : ∀ n : ℕ, choose n 0 = 1   :=  by sorry
