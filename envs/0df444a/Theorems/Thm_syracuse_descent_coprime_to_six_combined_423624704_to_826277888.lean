-- Prove2me | Theorems.Thm_syracuse_descent_coprime_to_six_combined_423624704_to_826277888
-- name    : syracuse_descent_coprime_to_six_combined_423624704_to_826277888
-- status  : Proved
-- author  : @Jie Luo
-- created : 2026-11-26T05:30:28.043248+00:00
-- url     : https://prove2.me/theorems/422f0ae4-d89f-4fbc-9396-6d0749938188
-- title:
--   Syracuse descent on [423624704, 826277888) for inputs coprime to six
-- statement:
--   On the entire interval [423624704, 826277888), every input coprime to six has a strictly smaller Syracuse iterate.
-- source:
--   Combines 32 adjacent proved certificate bands by the Collatz mission contributors.

import Definitions.Def_syracuseStep
import Mathlib.Logic.Function.Iterate

theorem syracuse_descent_coprime_to_six_combined_423624704_to_826277888 (n : ℕ) (hl : 423624704 ≤ n) (hu : n < 826277888) (ho : ¬ 2 ∣ n) (h3 : ¬ 3 ∣ n) :
    ∃ t : ℕ, syracuseStep^[t] n < n := by sorry
