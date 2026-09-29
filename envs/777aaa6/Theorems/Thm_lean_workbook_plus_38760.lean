-- Prove2me | Theorems.Thm_lean_workbook_plus_38760
-- name    : lean_workbook_plus_38760
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.562161+00:00
-- url     : https://prove2.me/theorems/1e68af6e-3c9b-44db-94a2-5f7ad2731097
-- statement:
--   A natural number $n$ has a units digit of 5 when expressed base 8. What is the remainder when $n$ is divided by 8?
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_38760 (n : ℕ) (h : n % 8 = 5) : n % 8 = 5   :=  by sorry
