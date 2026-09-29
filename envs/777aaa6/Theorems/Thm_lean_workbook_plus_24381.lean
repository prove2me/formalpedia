-- Prove2me | Theorems.Thm_lean_workbook_plus_24381
-- name    : lean_workbook_plus_24381
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.025447+00:00
-- url     : https://prove2.me/theorems/f7ffb59b-1f12-404f-8be4-6289c5a0f667
-- statement:
--   Prove the committee forming solution: If we want to choose $k+1$ people from a committee of $n+1$ people, one of them being named Joe, we can either include Joe and choose $k$ others from the remaining $n$, or exclude Joe and choose $k+1$ from the remaining $n$. This results in ${n \choose k} + {n \choose k + 1} = {n + 1 \choose k + 1}$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_24381 (n k : ℕ) : (n.choose k) + (n.choose (k + 1)) = (n + 1).choose (k + 1)   :=  by sorry
