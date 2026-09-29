-- Prove2me | Theorems.Thm_lean_workbook_plus_25367
-- name    : lean_workbook_plus_25367
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.025447+00:00
-- url     : https://prove2.me/theorems/1875960e-094c-4070-91a5-149d47b2ffb8
-- statement:
--   So, it is equivalent to proving that there does not exist an integer k, such that $ k^2 = mn(m^2 - n^2)$ for integers m and n such that $ gcd(m,n) = 1$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_25367 : ¬∃ (k m n : ℤ), k^2 = m*n*(m^2-n^2) ∧  Int.gcd m n = 1   :=  by sorry
