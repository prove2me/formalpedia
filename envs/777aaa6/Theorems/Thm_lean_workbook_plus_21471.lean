-- Prove2me | Theorems.Thm_lean_workbook_plus_21471
-- name    : lean_workbook_plus_21471
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.916039+00:00
-- url     : https://prove2.me/theorems/d5cdc899-3d9b-4068-bb83-7a986049060f
-- statement:
--   If $u<v$ are real, then by density of the rational numbers, there is some rational $q$ such that $u<q<v$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_21471 (u v : ℝ) (huv : u < v) : ∃ q : ℚ, u < q ∧ q < v   :=  by sorry
