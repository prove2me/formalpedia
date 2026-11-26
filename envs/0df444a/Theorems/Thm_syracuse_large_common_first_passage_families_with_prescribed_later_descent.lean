-- Prove2me | Theorems.Thm_syracuse_large_common_first_passage_families_with_prescribed_later_descent
-- name    : syracuse_large_common_first_passage_families_with_prescribed_later_descent
-- status  : Proved
-- author  : @Jie Luo
-- created : 2026-11-26T11:10:49.752478+00:00
-- url     : https://prove2.me/theorems/4a81311b-d812-48f7-b3f9-8bd19bf4aa27
-- title:
--   Arbitrarily large Syracuse first-passage families with prescribed later descent
-- statement:
--   For every prescribed later descent time L at least two and every d, there are arbitrarily large barriers B equal to 11 modulo 12 and families of 2^d distinct starts bounded by (3/2) times 43^(d+1) times B. They first pass below 2B at step d+1, all landing at B. Their common tail stays at least B in all of the first L states, and descends below B exactly L steps after landing.
-- source:
--   Prescribed odd-run descent at a CRT-selected coprime target, followed backwards by the same strictly increasing inverse construction as the common-first-passage family.

import Definitions.Def_syracuseStep
import Mathlib.Logic.Function.Iterate
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Finset.Card

theorem syracuse_large_common_first_passage_families_with_prescribed_later_descent
    (L d N : ℕ) (hL : 2 ≤ L) :
    ∃ B : ℕ, N < B ∧ 1 < B ∧ B%12=11 ∧ ∃ S : Finset ℕ, S.card=2^d ∧
      ∀ b ∈ S, 2*b ≤ 3*43^(d+1)*B ∧ b%2=1 ∧ ¬ 3 ∣ b ∧
        syracuseStep^[d+1] b = B ∧
        (∀ i ≤ d, 2*B ≤ syracuseStep^[i] b) ∧
        (∀ i < L, B ≤ syracuseStep^[i+(d+1)] b) ∧
        syracuseStep^[L+(d+1)] b < B := by sorry
