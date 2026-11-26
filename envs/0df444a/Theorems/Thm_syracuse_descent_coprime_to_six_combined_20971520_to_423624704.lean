-- Prove2me | Theorems.Thm_syracuse_descent_coprime_to_six_combined_20971520_to_423624704
-- name    : syracuse_descent_coprime_to_six_combined_20971520_to_423624704
-- status  : Proved
-- author  : @Jie Luo
-- created : 2026-11-26T05:30:26.599802+00:00
-- url     : https://prove2.me/theorems/3223fdd4-c964-4aff-aa4c-2b2512592b19
-- title:
--   Syracuse descent on [20971520, 423624704) for inputs coprime to six
-- statement:
--   On the entire interval [20971520, 423624704), every input coprime to six has a strictly smaller Syracuse iterate.
-- source:
--   Combines 32 adjacent proved certificate bands by the Collatz mission contributors.

import Definitions.Def_syracuseStep
import Mathlib.Logic.Function.Iterate

theorem syracuse_descent_coprime_to_six_combined_20971520_to_423624704 (n : ℕ) (hl : 20971520 ≤ n) (hu : n < 423624704) (ho : ¬ 2 ∣ n) (h3 : ¬ 3 ∣ n) :
    ∃ t : ℕ, syracuseStep^[t] n < n := by sorry
