-- Prove2me | solution 2 for Hashimoto.trace_hashimoto_pow_eq_card_nbCycles
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-18T20:17:33.721923+00:00
-- url     : https://prove2.me/submissions/4e35e908-fe30-4b44-afc3-0e18316ddcf0

import Mathlib
import Definitions.Def_Algebra_NonBacktracking_HashimotoTrace
import Definitions.Def_Algebra_NonBacktracking_RelWalkCount
open Finset RelWalkCount SimpleGraph Hashimoto in
theorem solution {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {n : ℕ} (hn : 1 ≤ n) : (hashimoto G ^ n).trace = (nbCycles G n).card := by
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
  -- entries of `Bⁿ` count non-backtracking walks
  have hpow : ∀ (n : ℕ) (a b : G.Dart),
      (relMatrix (NBAdj G) ^ n) a b = (walks (NBAdj G) n a b).card := by
    -- every walk starts at its source
    have hhead : ∀ (n : ℕ) (a b : G.Dart) (l : List G.Dart), l ∈ walks (NBAdj G) n a b → l.head? = some a := by
      intro n a b l hl
      cases n with
      | zero =>
        simp only [walks] at hl
        split_ifs at hl with hab
        · rw [Finset.mem_singleton] at hl
          rw [hl]
          rfl
        · simp at hl
      | succ n =>
        simp only [walks, Finset.mem_biUnion, Finset.mem_image] at hl
        obtain ⟨c, -, l', -, rfl⟩ := hl
        rfl
    intro n
    induction n with
    | zero =>
      intro a b
      rw [pow_zero, Matrix.one_apply]
      simp only [walks]
      split_ifs <;> simp
    | succ n ih =>
      intro a b
      rw [pow_succ', Matrix.mul_apply]
      simp only [walks]
      -- the images for different second vertices are disjoint
      rw [Finset.card_biUnion]
      · rw [Finset.sum_filter]
        refine Finset.sum_congr rfl fun c _ => ?_
        rw [ih c b, Finset.card_image_of_injective _ (List.cons_injective)]
        simp only [relMatrix, Matrix.of_apply]
        split_ifs <;> simp
      · intro c _ c' _ hcc'
        show Disjoint _ _
        rw [Finset.disjoint_left]
        intro l hl hl'
        rw [Finset.mem_image] at hl hl'
        obtain ⟨l₁, h₁, rfl⟩ := hl
        obtain ⟨l₂, h₂, heq⟩ := hl'
        have h12 : l₂ = l₁ := List.cons_injective heq
        subst h12
        have e1 := hhead n c b _ h₁
        have e2 := hhead n c' b _ h₂
        rw [e1] at e2
        exact hcc' (Option.some_injective _ e2)
  -- so the trace counts rooted closed walks (walks with different roots are different)
  have htrace : (hashimoto G ^ n).trace = (closedNBWalks G n).card := by
    unfold hashimoto closedNBWalks closedWalks
    rw [Matrix.trace, Finset.card_biUnion]
    · simp only [Matrix.diag, hpow]
    · intro a _ b _ hab
      show Disjoint _ _
      rw [Finset.disjoint_left]
      intro l ha hb
      have h1 := ((hmemW n a a l).mp ha).2.1
      have h2 := ((hmemW n b b l).mp hb).2.1
      rw [h1] at h2
      exact hab (Option.some_injective _ h2)
  -- and `dropLast` matches rooted closed walks with cyclic sequences
  have hcard : (nbCycles G n).card = (closedNBWalks G n).card := by
    -- a closed walk `c ++ [d]` has `d = head c`, so `dropLast` loses nothing
    have hsplit : ∀ l ∈ closedNBWalks G n, ∃ c d, l = c ++ [d] ∧ c.head? = some d := by
      intro l hl
      obtain ⟨hlen, -, hhl⟩ := (hmemC n l).mp hl
      rcases List.eq_nil_or_concat l with rfl | ⟨c, d, rfl⟩
      · simp at hlen
      rw [List.concat_eq_append] at hlen hhl
      have hcne : c ≠ [] := by
        intro h; rw [h] at hlen; simp at hlen; omega
      refine ⟨c, d, List.concat_eq_append, ?_⟩
      rw [List.getLast?_concat] at hhl
      cases c with
      | nil => exact absurd rfl hcne
      | cons z t =>
        simp at hhl
        simpa using hhl
    unfold nbCycles
    refine Finset.card_image_of_injOn ?_
    intro l₁ h₁ l₂ h₂ heq
    obtain ⟨c₁, d₁, rfl, hd₁⟩ := hsplit l₁ h₁
    obtain ⟨c₂, d₂, rfl, hd₂⟩ := hsplit l₂ h₂
    simp only [List.dropLast_concat] at heq
    subst heq
    rw [hd₁] at hd₂
    cases hd₂
    rfl
  rw [htrace, hcard]
