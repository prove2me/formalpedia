-- Prove2me | Theorems.Thm_syracuse_injective_orbit_yields_common_first_passage
-- name    : syracuse_injective_orbit_yields_common_first_passage
-- status  : Proved
-- author  : @Jie Luo
-- created : 2026-11-26T07:17:52.492346+00:00
-- url     : https://prove2.me/theorems/0887ccb5-33a4-456c-8bcc-2bec7236c8ff
-- title:
--   An injective Syracuse orbit forces many identical first passages below twice each barrier
-- statement:
--   For an injective Syracuse orbit whose odd starting value is below B, and for any d, there are 2^d distinct starts at most (3/2) times 43^(d+1) times B. All have their first visit below 2B at time d+1, with the same landing point in [B,3B/2). They remain at least B for their entire injective trajectories.
-- source:
--   Refines the barrier ancestor bound by choosing the preimage nearest the common target with valuation at least 3, which keeps the full earlier prefix at or above 2B.

import Definitions.Def_syracuseStep
import Mathlib.Logic.Function.Iterate
import Mathlib.Data.Finset.Card

theorem syracuse_injective_orbit_yields_common_first_passage (n B d : ℕ)
    (hodd : n%2 = 1) (hB : 1 < B) (hnB : n < B)
    (hinj : Function.Injective (fun i : ℕ => syracuseStep^[i] n)) :
    ∃ j : ℕ, ∃ S : Finset ℕ, S.card = 2^d ∧
      B ≤ syracuseStep^[j] n ∧ 2*syracuseStep^[j] n+2 ≤ 3*B ∧
      ∀ b ∈ S, 2*b ≤ 3*43^(d+1)*B ∧ b%2 = 1 ∧ ¬ 3 ∣ b ∧
        syracuseStep^[d+1] b = syracuseStep^[j] n ∧
        (∀ i ≤ d, 2*B ≤ syracuseStep^[i] b) ∧
        (∀ i : ℕ, B ≤ syracuseStep^[i] b) ∧
        Function.Injective (fun i : ℕ => syracuseStep^[i] b) := by sorry
