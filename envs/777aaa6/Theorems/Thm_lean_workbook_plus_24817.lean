-- Prove2me | Theorems.Thm_lean_workbook_plus_24817
-- name    : lean_workbook_plus_24817
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.025447+00:00
-- url     : https://prove2.me/theorems/b4ceff73-7a02-44e1-9a8e-83433bf060e6
-- statement:
--   Let f be a function from the set of Natural numbers to real numbers. If $f(n+9)=f(n)$ and $f(n+16)= f(n)$ for every n then show that f is a constant function.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_24817 (f : ℕ → ℝ) (h9 : ∀ n, f (n + 9) = f n) (h16 : ∀ n, f (n + 16) = f n) : ∀ n, f n = f 0   :=  by sorry
