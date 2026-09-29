-- Prove2me | Theorems.Thm_waring_g_verification
-- name    : waring_g_verification
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-06-01T01:57:29.225659+00:00
-- url     : https://prove2.me/theorems/6cc5ec3d-6f60-43bb-ad0a-834106d7a4de
-- statement:
--   Waring's problem for cubes: g(3) = 9, meaning every natural number is a sum of 9 cubes. Proved by Dickson (1939). The stronger result that every sufficiently large n is a sum of 7 cubes is also known. This captures g(3) = 9 (actually the bound 19 is generous).
-- source:
--   https://en.wikipedia.org/wiki/Waring%27s_problem

import Mathlib

import Mathlib

theorem waring_g_verification :
    ∀ n : ℕ, ∃ (a : Fin 19 → ℕ), n = ∑ i, (a i) ^ 3 := by
  sorry
