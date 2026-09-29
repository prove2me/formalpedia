-- Prove2me | Theorems.Thm_lean_workbook_plus_81719
-- name    : lean_workbook_plus_81719
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.420916+00:00
-- url     : https://prove2.me/theorems/dc1ffab6-4c2b-419d-804c-aa89dee4c4af
-- statement:
--   We have $25x + 5y = 275$, $x+y=15$ for some $x$ and $y$. If we substitute $x$ for $15-y$ in our first equation, we get $25(15-y) + 5y = 275$. We can simplify this to $y=5$. Substituting $y=5$ into our second equation, we get $x=10$. So Batman is pretty broke. He has $\boxed{\text{10 quarters and 5 nickels}}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_81719 (x y : ℕ) (h₁ : 25 * x + 5 * y = 275) (h₂ : x + y = 15) : x = 10 ∧ y = 5   :=  by sorry
