-- Prove2me | solution 1 for Hashimoto.isAcyclic_of_trace_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-24T05:35:01.314686+00:00
-- url     : https://prove2.me/submissions/c2b96dea-7423-48c4-ad1f-00bf8db5e0c5

import Mathlib
import Definitions.Def_Algebra_NonBacktracking_RelWalkCount
import Definitions.Def_Algebra_NonBacktracking_HashimotoTrace
import Definitions.Def_Algebra_NonBacktracking_VertexCycles

open Finset RelWalkCount SimpleGraph Hashimoto in
theorem sv6573_mem_nbCycles {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
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
theorem sv6573_trace_eq_card_nbCycles {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
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

open SimpleGraph in
theorem sv6573_getLast_q_support {V : Type*} {G : SimpleGraph V} {u v : V} (p : G.Walk u v) :
    p.support.getLast? = some v := by
  rw [List.getLast?_eq_some_getLast (by simp), p.getLast_support]

set_option maxHeartbeats 4000000 in
open Finset SimpleGraph List Hashimoto in
theorem solution {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
    (h : ∀ n : ℕ, 1 ≤ n → (hashimoto G ^ n).trace = 0) : G.IsAcyclic := by
  intro v c hc
  have hlen3 : 3 ≤ c.length := hc.three_le_length
  have hn1 : 1 ≤ c.length := by omega
  -- `DartAdj` together with distinct edges is exactly non-backtracking adjacency
  have hkey : ∀ d d' : G.Dart, G.DartAdj d d' → d.edge ≠ d'.edge → NBAdj G d d' := by
    intro d d' hadj hedge
    refine ⟨hadj, ?_⟩
    intro hcon
    apply hedge
    have hd' : d' = d.symm := by
      apply SimpleGraph.Dart.ext
      rw [Prod.ext_iff]
      exact ⟨hadj.symm, hcon⟩
    rw [hd', SimpleGraph.Dart.edge_symm]
  have hedges : c.edges.Nodup := hc.edges_nodup
  have hmapedge : c.darts.map SimpleGraph.Dart.edge = c.edges := rfl
  have hdne : c.darts ≠ [] := by
    intro hd
    have hl := c.length_darts
    rw [hd] at hl
    simp at hl
    omega
  have htne : c.support.tail ≠ [] := by
    intro hT
    rw [← c.map_snd_darts, List.map_eq_nil_iff] at hT
    exact hdne hT
  -- the interior of the dart list is a non-backtracking chain
  have hchain : List.IsChain (NBAdj G) c.darts := by
    have hne : List.IsChain (fun d d' : G.Dart => d.edge ≠ d'.edge) c.darts := by
      have h1 : List.IsChain (· ≠ ·) (c.darts.map SimpleGraph.Dart.edge) := by
        rw [hmapedge]
        exact hedges.isChain
      exact (List.isChain_map _).mp h1
    have hcomb : ∀ l : List G.Dart, List.IsChain G.DartAdj l →
        List.IsChain (fun d d' : G.Dart => d.edge ≠ d'.edge) l →
        List.IsChain (NBAdj G) l := by
      intro l
      induction l with
      | nil => intro _ _; simp
      | cons a s ih =>
        intro h1 h2
        rw [List.isChain_cons] at h1 h2 ⊢
        refine ⟨?_, ih h1.2 h2.2⟩
        intro y hy
        exact hkey a y (h1.1 y hy) (h2.1 y hy)
    exact hcomb c.darts c.isChain_dartAdj_darts hne
  -- the seam: the last dart runs non-backtracking into the first
  have hseam : ∀ x ∈ c.darts.getLast?, ∀ y ∈ c.darts.head?, NBAdj G x y := by
    intro x hx y hy
    rw [Option.mem_def] at hx hy
    -- both meet at the basepoint `v`
    have hxsnd : x.snd = v := by
      have h1 : (c.darts.map (fun d : G.Dart => d.snd)).getLast? = some x.snd := by
        rw [List.getLast?_map, hx]; rfl
      rw [c.map_snd_darts] at h1
      have h2 : c.support.getLast? = some v := sv6573_getLast_q_support c
      rw [← c.cons_tail_support, List.getLast?_cons_of_ne_nil htne, h1] at h2
      exact Option.some_inj.mp h2
    have hyfst : y.fst = v := by
      have h1 : (c.darts.map (fun d : G.Dart => d.fst)).head? = some y.fst := by
        rw [List.head?_map, hy]; rfl
      rw [c.map_fst_darts, ← c.cons_tail_support,
        List.dropLast_cons_of_ne_nil htne, List.head?_cons] at h1
      exact (Option.some_inj.mp h1).symm
    refine hkey x y (by show x.toProd.2 = y.toProd.1; rw [hxsnd, hyfst]) ?_
    -- distinct positions of a Nodup edge list carry distinct edges
    have hex : c.edges.getLast? = some x.edge := by
      rw [← hmapedge, List.getLast?_map, hx]; rfl
    have hey : c.edges.head? = some y.edge := by
      rw [← hmapedge, List.head?_map, hy]; rfl
    have hene : c.edges ≠ [] := by
      intro he
      rw [he] at hey
      simp at hey
    obtain ⟨e, s, hes⟩ : ∃ e s, c.edges = e :: s := by
      cases hce : c.edges with
      | nil => exact absurd hce hene
      | cons e s => exact ⟨e, s, rfl⟩
    rw [hes, List.head?_cons, Option.some_inj] at hey
    have hsne : s ≠ [] := by
      intro hs
      have hlen : c.edges.length = c.length := c.length_edges
      rw [hes, hs] at hlen
      simp at hlen
      omega
    rw [hes, List.getLast?_cons_of_ne_nil hsne] at hex
    have hxmem : x.edge ∈ s := List.mem_of_getLast? hex
    rw [hes, List.nodup_cons] at hedges
    intro hxy
    exact hedges.1 (by rw [hey, ← hxy]; exact hxmem)
  -- so the cycle's darts witness a non-empty `nbCycles`, contradicting the vanishing trace
  have hmem : c.darts ∈ nbCycles G c.length := by
    rw [sv6573_mem_nbCycles hn1]
    exact ⟨c.length_darts, hchain, hseam⟩
  have h0 : (nbCycles G c.length).card = 0 :=
    (sv6573_trace_eq_card_nbCycles G hn1).symm.trans (h c.length hn1)
  rw [Finset.card_eq_zero] at h0
  rw [h0] at hmem
  simp at hmem
