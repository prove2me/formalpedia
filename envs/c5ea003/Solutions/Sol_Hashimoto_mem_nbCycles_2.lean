-- Prove2me | solution 2 for Hashimoto.mem_nbCycles
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-18T15:37:07.322483+00:00
-- url     : https://prove2.me/submissions/6e502464-3bf6-4377-8ba9-3ac6b94b21b1

import Mathlib
import Definitions.Def_Algebra_NonBacktracking_HashimotoTrace
import Definitions.Def_Algebra_NonBacktracking_RelWalkCount
open Finset RelWalkCount SimpleGraph Hashimoto in
theorem solution {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
    {n : ℕ} (hn : 1 ≤ n) {c : List G.Dart} :
    c ∈ nbCycles G n ↔
      c.length = n ∧ List.IsChain (NBAdj G) c ∧
        ∀ x ∈ c.getLast?, ∀ y ∈ c.head?, NBAdj G x y := by
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
  simp only [nbCycles, Finset.mem_image]
  constructor
  · rintro ⟨l, hl, rfl⟩
    obtain ⟨hlen, hch, hhl⟩ := (hmemC n l).mp hl
    rcases List.eq_nil_or_concat l with rfl | ⟨c, d, rfl⟩
    · simp at hlen
    rw [List.concat_eq_append] at hlen hch hhl ⊢
    rw [List.dropLast_concat]
    have hclen : c.length = n := by simpa using hlen
    have hcne : c ≠ [] := by intro h; rw [h] at hclen; simp at hclen; omega
    obtain ⟨hc1, -, hseam⟩ := List.isChain_append.mp hch
    refine ⟨hclen, hc1, ?_⟩
    intro x hx y hy
    -- the head of `c` is the repeated root `d`
    have hhead : c.head? = some d := by
      rw [List.getLast?_concat] at hhl
      cases c with
      | nil => exact absurd rfl hcne
      | cons z t =>
        simp at hhl
        simpa using hhl
    rw [hhead] at hy
    obtain rfl : d = y := by simpa using hy
    exact hseam x hx d (by simp)
  · rintro ⟨hclen, hc1, hseam⟩
    have hcne : c ≠ [] := by intro h; rw [h] at hclen; simp at hclen; omega
    obtain ⟨d, t, rfl⟩ := List.exists_cons_of_ne_nil hcne
    refine ⟨d :: t ++ [d], (hmemC n _).mpr ⟨by simp at hclen ⊢; omega, ?_, ?_⟩, List.dropLast_concat⟩
    · refine List.isChain_append.mpr ⟨hc1, List.isChain_singleton d, ?_⟩
      intro x hx y hy
      obtain rfl : d = y := by simpa using hy
      exact hseam x hx d (by simp)
    · rw [List.getLast?_concat]
      rfl
