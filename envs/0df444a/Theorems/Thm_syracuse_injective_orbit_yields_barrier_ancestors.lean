-- Prove2me | Theorems.Thm_syracuse_injective_orbit_yields_barrier_ancestors
-- name    : syracuse_injective_orbit_yields_barrier_ancestors
-- status  : Proved
-- author  : @Jie Luo
-- created : 2026-11-26T07:13:43.731211+00:00
-- url     : https://prove2.me/theorems/273b4bb9-3928-51a5-9850-a4c92c98c9c4
-- title:
--   An injective Syracuse orbit forces families of ancestors staying above every barrier
-- statement:
--   Given an injective Syracuse orbit starting at an odd n below B, for every depth d there are 2^d distinct starts coprime to six below (3/2) 43^d B. Their orbits all stay above or at B, are injective, and merge into the same state of the given orbit after exactly d steps.
-- source:
--   Use the certified last-exit theorem to find a tail minimum below 3B/2, and build a two-child inverse tree on the six units modulo 9 with strictly increasing inverse edges.

import Definitions.Def_syracuseStep
import Mathlib.Logic.Function.Iterate
import Mathlib.Data.Finset.Card

theorem syracuse_injective_orbit_yields_barrier_ancestors (n B d : ℕ)
    (hodd : n % 2 = 1) (hB : 1 < B) (hnB : n < B)
    (hinj : Function.Injective (fun i : ℕ => syracuseStep^[i] n)) :
    ∃ j : ℕ, ∃ S : Finset ℕ, S.card = 2^d ∧
      ∀ b ∈ S, 2*b ≤ 3*43^d*B ∧ b%2 = 1 ∧ ¬ 3 ∣ b ∧
        syracuseStep^[d] b = syracuseStep^[j] n ∧
        (∀ i : ℕ, B ≤ syracuseStep^[i] b) ∧
        Function.Injective (fun i : ℕ => syracuseStep^[i] b) := by sorry
