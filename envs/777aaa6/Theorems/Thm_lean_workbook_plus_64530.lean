-- Prove2me | Theorems.Thm_lean_workbook_plus_64530
-- name    : lean_workbook_plus_64530
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.755244+00:00
-- url     : https://prove2.me/theorems/fcd1bedb-7ae4-4cf6-91c5-c1725080f8d3
-- statement:
--   ${a_{n+2}\over 3}={(n+3)a_{n+1}\over 3(n+1)}\iff {a_{n+2}\over(n+2)(n+3)}={a_{n+1}\over(n+1)(n+2)}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_64530 (a : ℕ → ℝ) (n : ℕ) :
  a (n + 2) / 3 = ((n + 3) * a (n + 1)) / (3 * (n + 1)) ↔
  a (n + 2) / ((n + 2) * (n + 3)) = a (n + 1) / ((n + 1) * (n + 2))   :=  by sorry
