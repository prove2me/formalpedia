-- Prove2me | Theorems.Thm_lean_workbook_plus_24186
-- name    : lean_workbook_plus_24186
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.025447+00:00
-- url     : https://prove2.me/theorems/369366a0-b1c5-407c-9f29-29910389145e
-- statement:
--   The sequence $1$ , $\tfrac12$ , $\tfrac14$ , $\tfrac18$ , ... is bounded (lying in the closed interval $[0,1]$ ).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_24186 : BddAbove (Set.range (fun n : ℕ => (1/2)^n))   :=  by sorry
