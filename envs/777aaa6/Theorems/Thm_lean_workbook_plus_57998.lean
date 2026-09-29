-- Prove2me | Theorems.Thm_lean_workbook_plus_57998
-- name    : lean_workbook_plus_57998
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.496679+00:00
-- url     : https://prove2.me/theorems/55e6b113-ed98-4000-8875-87a4e5c014b6
-- statement:
--   The least multiple of $56$ greater than $1000$ is $1008$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_57998 : IsLeast { n : ℕ | 1000 < n ∧ 56∣n } 1008   :=  by sorry
