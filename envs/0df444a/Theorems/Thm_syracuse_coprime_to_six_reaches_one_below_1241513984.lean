-- Prove2me | Theorems.Thm_syracuse_coprime_to_six_reaches_one_below_1241513984
-- name    : syracuse_coprime_to_six_reaches_one_below_1241513984
-- status  : Open
-- author  : @Jie Luo
-- created : 2026-11-26T05:19:16.506332+00:00
-- url     : https://prove2.me/theorems/e0ad9e47-682e-5440-979b-0269e4c4aafe
-- title:
--   Syracuse reaches one from coprime-to-six inputs below 1,241,513,984
-- statement:
--   Every positive integer below 1,241,513,984 that is divisible by neither two nor three reaches one under the Syracuse map (the odd part of 3n+1).
-- source:
--   Collatz Conjecture mission. Disjoint certified descent bands, combined with the low-range certificate of immiq and strong induction.

import Definitions.Def_syracuseStep
import Mathlib.Logic.Function.Iterate

theorem syracuse_coprime_to_six_reaches_one_below_1241513984 (n : ℕ) (hn : 0 < n)
    (hlt : n < 1241513984) (ho : ¬ 2 ∣ n) (h3 : ¬ 3 ∣ n) :
    ∃ t : ℕ, syracuseStep^[t] n = 1 := by sorry
