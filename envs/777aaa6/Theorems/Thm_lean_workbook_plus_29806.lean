-- Prove2me | Theorems.Thm_lean_workbook_plus_29806
-- name    : lean_workbook_plus_29806
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.279436+00:00
-- url     : https://prove2.me/theorems/cd1393cf-1643-48c0-901a-decf6c1059c3
-- statement:
--   We really just care if it divisible by 3 or not. We want $2^n\equiv1\, (\textrm{mod 3})$ .\n\n $2^1\equiv2\,(\textrm{mod 3})$ \n $2^2\equiv1\,(\textrm{mod 3})$ \n $2^3\equiv2\,(\textrm{mod 3})$ \nBecause it keeps repeating, you see that $2^n-1\equiv0\,(\textrm{mod 3})$ is true for all positive even $n$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_29806  (n : ℕ)
  (h₀ : Even n) :
  3 ∣ (2^n - 1)   :=  by sorry
