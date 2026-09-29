-- Prove2me | Theorems.Thm_lean_workbook_plus_33486
-- name    : lean_workbook_plus_33486
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.431937+00:00
-- url     : https://prove2.me/theorems/8735538b-2114-4ba0-bcd5-25200271e2bf
-- statement:
--   Prove by induction that $2^n > n^3$ for all $n > 9$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_33486 (n : ℕ) (hn : 9 < n) : 2^n > n^3   :=  by sorry
