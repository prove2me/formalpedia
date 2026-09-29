-- Prove2me | solution 1 for Bridges.InfiniteCubicMatchings.Ladder.cutEdgesSet_leftPlus
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T03:26:06.737423+00:00
-- url     : https://prove2.me/submissions/80dc41d9-7a6b-4db5-a62a-06a0afe434f4

-- Sol generated from Bridges/InfiniteCubicMatchingsParitySharp.lean
import Mathlib
import Definitions.Def_Bridges_InfiniteCubicMatchings
import Definitions.Def_Bridges_InfiniteCubicMatchingsLadder
import Definitions.Def_Bridges_InfiniteCubicMatchingsParitySharp
/-
# Sharpness of the parity lemma in the infinite setting

The parity lemma `PerfectMatching.card_inter_cutEdges_odd` says that a perfect matching meets
every edge cut of odd size **with a finite side** in an odd number of edges.  In finite graphs
the finiteness assumption is vacuous.  Here we prove that in infinite graphs it cannot be
dropped: the infinite ladder has an edge cut of size `3` (odd), both sides of which are
infinite, that is *disjoint* from a perfect matching.

This is the fundamental new phenomenon of the infinite theory: parity arguments are only
available for cuts with a finite side, which is why `IsOddCut` is defined via a `Finset`.
-/

open Bridges.InfiniteCubicMatchings

open Ladder












open Bridges.InfiniteCubicMatchings.Ladder in
theorem solution:
    cutEdgesSet ladder leftPlus =
      {s(((0 : ℤ), true), ((1 : ℤ), true)), s(((1 : ℤ), false), ((1 : ℤ), true)),
        s(((1 : ℤ), false), ((2 : ℤ), false))} := by
  ext e
  constructor
  · rintro ⟨hE, ⟨n, b⟩, ⟨m, c⟩, rfl, hu, hw⟩
    have hadj : ladder.Adj ((n, b) : ℤ × Bool) ((m, c) : ℤ × Bool) := by simpa using hE
    simp only [leftPlus, Set.mem_setOf_eq, Prod.mk.injEq, not_or, not_and] at hu hw
    obtain ⟨hw1, hw2⟩ := hw
    have hm1 : 1 ≤ m := by omega
    rcases hu with hn | hn
    · -- the `n ≤ 0` side
      rcases hadj with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · simp only at h1
        omega
      · simp only at h1 h2
        rcases h2 with h2 | h2
        · have hm : m = 1 := by omega
          have hn0 : n = 0 := by omega
          subst hm; subst hn0
          have hc : c = true := by
            cases c
            · exact absurd rfl (hw2 rfl)
            · rfl
          subst hc
          simp [h1]
        · omega
    · -- the extra vertex `(1, false)`
      obtain ⟨hn1, hb⟩ := hn
      subst hn1; subst hb
      rcases hadj with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · simp only at h1 h2
        subst h1
        have hc : c = true := by
          cases c
          · exact absurd rfl h2
          · rfl
        subst hc
        simp
      · simp only at h1 h2
        subst h1
        rcases h2 with h2 | h2
        · subst h2
          simp
        · omega
  · intro he
    have h0 : ¬ ((1 : ℤ), true) ∈ leftPlus := by simp [leftPlus]
    have h2 : ¬ ((2 : ℤ), false) ∈ leftPlus := by simp [leftPlus]
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at he
    rcases he with rfl | rfl | rfl
    · exact ⟨by simpa using adj_rail (0 : ℤ) true, (0, true), (1, true), rfl,
        by simp [leftPlus], h0⟩
    · exact ⟨by simpa using adj_rung (1 : ℤ) false, (1, false), (1, true), rfl,
        by simp [leftPlus], h0⟩
    · exact ⟨by simpa using adj_rail (1 : ℤ) false, (1, false), (2, false), rfl,
        by simp [leftPlus], h2⟩
