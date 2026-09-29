-- Prove2me | solution 2 for Hashimoto.revWalk_ne
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-18T15:32:33.979479+00:00
-- url     : https://prove2.me/submissions/c03d1e50-a0d9-4c9b-a07c-c3865a55c111

import Mathlib
import Definitions.Def_Algebra_NonBacktracking_HashimotoTrace
import Definitions.Def_Algebra_NonBacktracking_ReversalParity
import Definitions.Def_Algebra_NonBacktracking_RelWalkCount
open Finset SimpleGraph List Hashimoto RelWalkCount in
theorem solution {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
    {n : ℕ} {l : List G.Dart} (hl : l ∈ closedNBWalks G n) : revWalk l ≠ l := by
  -- walks of `NBAdj G` are exactly the chains with the right ends and length
  have hmemW : ∀ (n : ℕ) (a b : G.Dart) (l : List G.Dart), l ∈ walks (NBAdj G) n a b ↔
      l.length = n + 1 ∧ l.head? = some a ∧ l.getLast? = some b ∧ List.IsChain (NBAdj G) l := by
    intro n
    induction n with
    | zero =>
      intro a b l
      simp only [walks]
      constructor
      · intro hl
        split_ifs at hl with hab
        · rw [Finset.mem_singleton] at hl
          subst hl
          subst hab
          exact ⟨rfl, rfl, rfl, List.isChain_singleton a⟩
        · simp at hl
      · rintro ⟨hlen, hhead, hlast, -⟩
        obtain ⟨x, rfl⟩ : ∃ x, l = [x] := List.length_eq_one_iff.mp hlen
        simp only [List.head?_cons, List.getLast?_singleton, Option.some.injEq] at hhead hlast
        subst hhead
        subst hlast
        simp
    | succ n ih =>
      intro a b l
      simp only [walks, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_image]
      constructor
      · rintro ⟨c, hac, l', hl', rfl⟩
        obtain ⟨hlen, hhead, hlast, hchain⟩ := (ih c b l').mp hl'
        obtain ⟨y, t, rfl⟩ : ∃ y t, l' = y :: t := List.exists_cons_of_ne_nil (by
          intro h; rw [h] at hlen; simp at hlen)
        simp only [List.head?_cons, Option.some.injEq] at hhead
        subst hhead
        refine ⟨by simp [hlen], rfl, ?_, ?_⟩
        · rw [List.getLast?_cons_cons]
          exact hlast
        · exact List.isChain_cons_cons.mpr ⟨hac, hchain⟩
      · rintro ⟨hlen, hhead, hlast, hchain⟩
        obtain ⟨x, l', rfl⟩ : ∃ x l', l = x :: l' := List.exists_cons_of_ne_nil (by
          intro h; rw [h] at hlen; simp at hlen)
        simp only [List.head?_cons, Option.some.injEq] at hhead
        subst hhead
        obtain ⟨c, t, rfl⟩ : ∃ c t, l' = c :: t := List.exists_cons_of_ne_nil (by
          intro h; rw [h] at hlen; simp at hlen)
        obtain ⟨hxc, hchain'⟩ := List.isChain_cons_cons.mp hchain
        refine ⟨c, hxc, c :: t, (ih c b (c :: t)).mpr ⟨?_, rfl, ?_, hchain'⟩, rfl⟩
        · simpa using hlen
        · rw [List.getLast?_cons_cons] at hlast
          exact hlast
  -- closed walks: chains of length `n + 1` whose two ends agree
  have hmemC : ∀ (n : ℕ) (l : List G.Dart), l ∈ closedNBWalks G n ↔
      l.length = n + 1 ∧ List.IsChain (NBAdj G) l ∧ l.head? = l.getLast? := by
    intro n l
    simp only [closedNBWalks, closedWalks, Finset.mem_biUnion, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨a, ha⟩
      obtain ⟨hlen, hh, hl, hc⟩ := (hmemW n a a l).mp ha
      exact ⟨hlen, hc, by rw [hh, hl]⟩
    · rintro ⟨hlen, hc, hhl⟩
      obtain ⟨x, t, rfl⟩ : ∃ x t, l = x :: t := List.exists_cons_of_ne_nil (by
        intro h; rw [h] at hlen; simp at hlen)
      refine ⟨x, (hmemW n x x _).mpr ⟨hlen, rfl, ?_, hc⟩⟩
      rw [← hhl]
      rfl
  obtain ⟨hlen, hc, -⟩ := (hmemC n l).mp hl
  intro heq
  -- position `i` of a reversal-fixed walk is the flip of position `len - 1 - i`
  have hpos : ∀ i j (hi : i < l.length) (hj : j < l.length), i + j + 1 = l.length →
      l[i] = (l[j]).symm := by
    intro i j hi hj hij
    obtain rfl : j = l.length - 1 - i := by omega
    have h1 := List.getElem_of_eq heq (i := i) (by simp [revWalk]; omega)
    rw [← h1]
    simp [revWalk, List.getElem_reverse, List.getElem_map]
  obtain ⟨k, hk | hk⟩ := Nat.even_or_odd' l.length
  · -- even length `2k = 2(j+1)`: the middle pair is a dart followed by its reversal
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    have hmid := hpos (j + 1) j (by omega) (by omega) (by omega)
    have hadj := hc.getElem j (by omega)
    rw [hmid] at hadj
    exact hadj.2 (by simp [SimpleGraph.Dart.symm])
  · -- odd length `2k + 1`: the middle dart equals its own reversal
    have hmid := hpos k k (by omega) (by omega) (by omega)
    exact SimpleGraph.Dart.symm_ne _ hmid.symm
