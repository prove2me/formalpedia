-- Prove2me | Theorems.Thm_lean_workbook_plus_65698
-- name    : lean_workbook_plus_65698
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.755244+00:00
-- url     : https://prove2.me/theorems/7e1a2af5-2b17-4811-ad19-5413d0c41943
-- statement:
--   Find an example of a pair $(6n-1, 6n+1)$ where neither number is prime.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_65698 : ∃ n, ¬ Nat.Prime (6 * n - 1) ∧ ¬ Nat.Prime (6 * n + 1)   :=  by sorry
