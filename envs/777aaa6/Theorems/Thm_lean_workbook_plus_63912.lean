-- Prove2me | Theorems.Thm_lean_workbook_plus_63912
-- name    : lean_workbook_plus_63912
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.755244+00:00
-- url     : https://prove2.me/theorems/ab9380ff-ff7c-4185-95e8-669198fa0c29
-- statement:
--   Prove $F_{2n+1}^2+F_{2n+1}F_{2n+2}-F_{2n+2}^2=1$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_63912 (n : ℕ) : (fib (2 * n + 1))^2 + fib (2 * n + 1) * fib (2 * n + 2) - (fib (2 * n + 2))^2 = 1   :=  by sorry
