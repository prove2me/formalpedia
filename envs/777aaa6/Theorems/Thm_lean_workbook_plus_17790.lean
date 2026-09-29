-- Prove2me | Theorems.Thm_lean_workbook_plus_17790
-- name    : lean_workbook_plus_17790
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.799204+00:00
-- url     : https://prove2.me/theorems/728fd823-2986-4add-a92f-29766f8ef420
-- statement:
--   Prove that if $b > 0$ then $b|a \Longleftrightarrow a \mod b = 0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_17790 (a b : ℤ) (h : b > 0) : b ∣ a ↔ a % b = 0   :=  by sorry
