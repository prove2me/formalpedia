-- Prove2me | solution 1 for Hashimoto.trace_hashimoto_pow_eq_card_cyclicNBVertexSeqs
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-24T05:38:20.521895+00:00
-- url     : https://prove2.me/submissions/6071a7f2-7206-4b5a-89c4-ab905be20b85

import Mathlib
import Definitions.Def_Algebra_NonBacktracking_RelWalkCount
import Definitions.Def_Algebra_NonBacktracking_HashimotoTrace
import Definitions.Def_Algebra_NonBacktracking_VertexCycles

open Finset RelWalkCount SimpleGraph Hashimoto in
theorem e036_mem_nbCycles {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
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

open Finset RelWalkCount SimpleGraph Hashimoto in
theorem e036_trace_nbCycles {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
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

theorem e036_dartList_ext {V : Type*} {G : SimpleGraph V} : ∀ {c c' : List G.Dart},
    c.map (fun d => d.toProd.1) = c'.map (fun d => d.toProd.1) →
    c.map (fun d => d.toProd.2) = c'.map (fun d => d.toProd.2) → c = c' := by
  intro c
  induction c with
  | nil =>
    intro c' h1 _
    cases c' with
    | nil => rfl
    | cons _ _ => simp at h1
  | cons a t ih =>
    intro c' h1 h2
    cases c' with
    | nil => simp at h1
    | cons b t' =>
      simp only [List.map_cons, List.cons.injEq] at h1 h2
      have hab : a = b := (SimpleGraph.Dart.ext_iff a b).mpr (Prod.ext h1.1 h2.1)
      rw [hab, ih h1.2 h2.2]

theorem e036_chain_aux {α : Type*} {R : α → α → Prop} (a' : α) : ∀ (a : α) (t : List α),
    (List.IsChain R (a :: t) ∧ R ((a :: t).getLast (List.cons_ne_nil a t)) a') ↔
      List.Forall₂ R (a :: t) (t ++ [a']) := by
  intro a t
  induction t generalizing a with
  | nil => simp
  | cons b t ih =>
    rw [List.isChain_cons_cons, List.getLast_cons_cons, List.cons_append, List.forall₂_cons,
      ← ih b]
    tauto

theorem e036_isChain_seam {α : Type*} {R : α → α → Prop} {l : List α} (hne : l ≠ []) :
    (List.IsChain R l ∧ ∀ x ∈ l.getLast?, ∀ y ∈ l.head?, R x y) ↔
      List.Forall₂ R l (l.rotate 1) := by
  obtain ⟨a, t, rfl⟩ := List.exists_cons_of_ne_nil hne
  have hrot : (a :: t).rotate 1 = t ++ [a] := by
    simp [List.rotate_cons_succ]
  rw [hrot, ← e036_chain_aux a a t, List.getLast?_eq_some_getLast (List.cons_ne_nil a t)]
  simp

set_option maxHeartbeats 4000000 in
open Finset RelWalkCount SimpleGraph List Hashimoto in
theorem solution {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {n : ℕ} (hn : 1 ≤ n) :
    (hashimoto G ^ n).trace = (cyclicNBVertexSeqs G n).card := by
  -- a pointwise equality along `Forall₂` is an equality of the two mapped lists
  have hmapeq : ∀ {l₁ l₂ : List G.Dart},
      Forall₂ (fun a b : G.Dart => a.toProd.2 = b.toProd.1) l₁ l₂ →
      l₁.map (fun d => d.toProd.2) = l₂.map (fun d => d.toProd.1) := by
    intro l₁ l₂ h
    induction h with
    | nil => rfl
    | cons hab _ ih => simp [hab, ih]
  -- on a dart cycle, the head vertices already determine the tail vertices
  have hproj : ∀ c ∈ nbCycles G n,
      c.map (fun d => d.toProd.2) = (c.map (fun d => d.toProd.1)).rotate 1 := by
    intro c hc
    rw [e036_mem_nbCycles hn] at hc
    obtain ⟨hlen, hchain, hseam⟩ := hc
    have hne : c ≠ [] := by
      intro h
      rw [h] at hlen
      simp at hlen
      omega
    have hf2 : Forall₂ (NBAdj G) c (c.rotate 1) :=
      (e036_isChain_seam hne).mp ⟨hchain, hseam⟩
    have hsnd : Forall₂ (fun a b : G.Dart => a.toProd.2 = b.toProd.1) c (c.rotate 1) :=
      hf2.imp (fun _ _ h => h.1)
    rw [hmapeq hsnd, List.map_rotate]
  -- hence the vertex projection is injective on dart cycles
  have hinj : Set.InjOn (List.map fun d : G.Dart => d.toProd.1)
      (nbCycles G n : Set (List G.Dart)) := by
    intro c hc c' hc' hcc
    refine e036_dartList_ext hcc ?_
    rw [hproj c (by simpa using hc), hproj c' (by simpa using hc'), hcc]
  have htr : (hashimoto G ^ n).trace = (nbCycles G n).card :=
    e036_trace_nbCycles G hn
  rw [htr]
  simp only [cyclicNBVertexSeqs]
  rw [Finset.card_image_of_injOn hinj]
