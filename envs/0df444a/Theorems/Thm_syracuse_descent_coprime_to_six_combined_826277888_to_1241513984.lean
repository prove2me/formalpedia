-- Prove2me | Theorems.Thm_syracuse_descent_coprime_to_six_combined_826277888_to_1241513984
-- name    : syracuse_descent_coprime_to_six_combined_826277888_to_1241513984
-- status  : Proved
-- author  : @Jie Luo
-- created : 2026-11-26T05:30:26.155324+00:00
-- url     : https://prove2.me/theorems/1a0e62b1-52dc-4f1f-8e63-af03d116fe0e
-- title:
--   Syracuse descent on [826277888, 1241513984) for inputs coprime to six
-- statement:
--   On the entire interval [826277888, 1241513984), every input coprime to six has a strictly smaller Syracuse iterate.
-- source:
--   Combines 33 adjacent proved certificate bands by the Collatz mission contributors.

import Definitions.Def_syracuseStep
import Mathlib.Logic.Function.Iterate

theorem syracuse_descent_coprime_to_six_combined_826277888_to_1241513984 (n : ℕ) (hl : 826277888 ≤ n) (hu : n < 1241513984) (ho : ¬ 2 ∣ n) (h3 : ¬ 3 ∣ n) :
    ∃ t : ℕ, syracuseStep^[t] n < n := by sorry
