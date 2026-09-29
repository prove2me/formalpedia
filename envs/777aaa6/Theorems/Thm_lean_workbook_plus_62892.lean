-- Prove2me | Theorems.Thm_lean_workbook_plus_62892
-- name    : lean_workbook_plus_62892
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.629978+00:00
-- url     : https://prove2.me/theorems/ab7ac15c-a643-4d30-ab52-04fd8369dcbc
-- statement:
--   Prove that $a^3-a^4\le\frac{27}{256}$ for $a>0$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_62892 (a : ℝ) (ha : 0 < a) : a^3 - a^4 ≤ 27 / 256   :=  by sorry
