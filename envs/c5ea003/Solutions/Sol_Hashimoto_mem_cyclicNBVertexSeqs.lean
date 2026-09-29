-- Prove2me | solution 1 for Hashimoto.mem_cyclicNBVertexSeqs
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-20T22:31:38.08898+00:00
-- url     : https://prove2.me/submissions/f132d125-3555-4dd1-b88a-2047e487c56d

import Mathlib
import Definitions.Def_Algebra_NonBacktracking_HashimotoTrace
import Definitions.Def_Algebra_NonBacktracking_RelWalkCount
import Definitions.Def_Algebra_NonBacktracking_VertexCycles

set_option maxHeartbeats 1000000 in
open Finset RelWalkCount SimpleGraph List Hashimoto in
theorem solution {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
    {n : ℕ} (hn : 1 ≤ n) {u : List V} :
    u ∈ cyclicNBVertexSeqs G n ↔
      u.length = n ∧ List.Forall₂ G.Adj u (u.rotate 1) ∧
        List.Forall₂ (· ≠ ·) (u.rotate 2) u := by
  classical
  -- generic list plumbing
  have hkey : ∀ (R : G.Dart → G.Dart → Prop) (l : List G.Dart) (a : G.Dart), l ≠ [] →
      ((List.IsChain R l ∧ ∀ z ∈ l.getLast?, R z a) ↔ List.Forall₂ R l (l.tail ++ [a])) := by
    intro R l
    induction l with
    | nil => intro a h; exact absurd rfl h
    | cons x t ih =>
      intro a _
      cases t with
      | nil =>
        simp only [List.tail_cons, List.nil_append, List.getLast?_singleton,
          Option.mem_def, Option.some.injEq, forall_eq']
        constructor
        · rintro ⟨-, h⟩
          exact List.forall₂_cons.mpr ⟨h, List.Forall₂.nil⟩
        · intro h
          exact ⟨List.isChain_singleton x, (List.forall₂_cons.mp h).1⟩
      | cons y s =>
        have hrest := ih a (by simp)
        simp only [List.tail_cons] at hrest ⊢
        rw [List.cons_append, List.forall₂_cons, List.isChain_cons_cons,
          List.getLast?_cons_cons]
        constructor
        · rintro ⟨⟨hxy, hch⟩, hseam⟩
          exact ⟨hxy, hrest.mp ⟨hch, hseam⟩⟩
        · rintro ⟨hxy, hf⟩
          obtain ⟨hch, hseam⟩ := hrest.mpr hf
          exact ⟨⟨hxy, hch⟩, hseam⟩
  have hcyc : ∀ (R : G.Dart → G.Dart → Prop) (c : List G.Dart), c ≠ [] →
      ((List.IsChain R c ∧ ∀ x ∈ c.getLast?, ∀ y ∈ c.head?, R x y)
        ↔ List.Forall₂ R c (c.rotate 1)) := by
    intro R c hc
    obtain ⟨x, t, rfl⟩ := List.exists_cons_of_ne_nil hc
    have h := hkey R (x :: t) x (by simp)
    simp only [List.tail_cons] at h
    have hrot : (x :: t).rotate 1 = t ++ [x] := by simp
    rw [hrot, ← h]
    simp only [List.head?_cons, Option.mem_def, Option.some.injEq]
    constructor
    · rintro ⟨hch, hseam⟩
      exact ⟨hch, fun z hz => hseam z hz x rfl⟩
    · rintro ⟨hch, hseam⟩
      refine ⟨hch, ?_⟩
      rintro z hz y rfl
      exact hseam z hz
  have hand : ∀ (R S : G.Dart → G.Dart → Prop) (l₁ l₂ : List G.Dart),
      List.Forall₂ R l₁ l₂ → List.Forall₂ S l₁ l₂ →
      List.Forall₂ (fun a b => R a b ∧ S a b) l₁ l₂ := by
    intro R S l₁ l₂ h₁ h₂
    induction h₁ with
    | nil => exact List.Forall₂.nil
    | cons hab _ ih =>
      rcases List.forall₂_cons.mp h₂ with ⟨hab2, htl2⟩
      exact List.forall₂_cons.mpr ⟨⟨hab, hab2⟩, ih htl2⟩
  have hmapF : ∀ (f g : G.Dart → V) (l₁ l₂ : List G.Dart),
      l₁.length = l₂.length → l₁.map f = l₂.map g →
      List.Forall₂ (fun a b => f a = g b) l₁ l₂ := by
    intro f g l₁
    induction l₁ with
    | nil =>
      intro l₂ hlen _
      cases l₂ with
      | nil => exact List.Forall₂.nil
      | cons _ _ => simp at hlen
    | cons x t ih =>
      intro l₂ hlen hmap
      cases l₂ with
      | nil => simp at hlen
      | cons y s =>
        simp only [List.map_cons, List.cons.injEq] at hmap
        exact List.forall₂_cons.mpr ⟨hmap.1, ih s (by simpa using hlen) hmap.2⟩
  have hfun : ∀ (l₁ l₂ : List G.Dart),
      List.Forall₂ (fun d d' => d.toProd.2 = d'.toProd.1) l₁ l₂ →
      l₁.map (fun d => d.toProd.2) = l₂.map (fun d => d.toProd.1) := by
    intro l₁ l₂ h
    induction h with
    | nil => rfl
    | cons hab _ ih => simp [hab, ih]
  -- membership in `nbCycles` (re-proved here; the walk lemmas are the shipped ones)
  have hmemN : ∀ c : List G.Dart, c ∈ nbCycles G n ↔
      c.length = n ∧ List.IsChain (NBAdj G) c ∧
        ∀ x ∈ c.getLast?, ∀ y ∈ c.head?, NBAdj G x y := by
    intro c
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

  have hmemF : ∀ c : List G.Dart, c ∈ nbCycles G n ↔
      c.length = n ∧ List.Forall₂ (NBAdj G) c (c.rotate 1) := by
    intro c
    rw [hmemN c]
    constructor
    · rintro ⟨hlen, hch, hseam⟩
      have hne : c ≠ [] := by
        intro h; rw [h] at hlen; simp at hlen; omega
      exact ⟨hlen, (hcyc (NBAdj G) c hne).mp ⟨hch, hseam⟩⟩
    · rintro ⟨hlen, hf⟩
      have hne : c ≠ [] := by
        intro h; rw [h] at hlen; simp at hlen; omega
      obtain ⟨hch, hseam⟩ := (hcyc (NBAdj G) c hne).mpr hf
      exact ⟨hlen, hch, hseam⟩
  rw [cyclicNBVertexSeqs, Finset.mem_image]
  constructor
  · rintro ⟨c, hc, rfl⟩
    obtain ⟨hlen, hf⟩ := (hmemF c).mp hc
    have hsnd : c.map (fun d => d.toProd.2) = (c.map (fun d => d.toProd.1)).rotate 1 := by
      rw [← List.map_rotate]
      exact hfun c (c.rotate 1) (hf.imp (fun _ _ h => h.1))
    refine ⟨by simpa using hlen, ?_, ?_⟩
    · rw [← hsnd]
      refine List.forall₂_map_left_iff.mpr (List.forall₂_map_right_iff.mpr ?_)
      exact List.forall₂_same.mpr (fun d _ => d.adj)
    · have hmaps : List.Forall₂ (· ≠ ·) ((c.rotate 1).map (fun d => d.toProd.2))
          (c.map (fun d => d.toProd.1)) := by
        rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff]
        exact (hf.imp (fun _ _ h => h.2)).flip
      have hrot2 : (c.map (fun d => d.toProd.1)).rotate 2
          = (c.rotate 1).map (fun d => d.toProd.2) := by
        rw [List.map_rotate, hsnd, List.rotate_rotate]
      rw [hrot2]
      exact hmaps
  · rintro ⟨hlen, hadj, hnb⟩
    have hzadj : ∀ p ∈ u.zip (u.rotate 1), G.Adj p.1 p.2 := by
      intro p hp
      obtain ⟨-, hall⟩ := List.forall₂_iff_zip.mp hadj
      exact hall (by simpa using hp)
    refine ⟨(u.zip (u.rotate 1)).pmap (fun p hp => (⟨p, hp⟩ : G.Dart)) hzadj, ?_, ?_⟩
    · -- it is a cyclic non-backtracking dart word
      set c : List G.Dart :=
        (u.zip (u.rotate 1)).pmap (fun p hp => (⟨p, hp⟩ : G.Dart)) hzadj with hcdef
      have hcfst : c.map (fun d => d.toProd.1) = u := by
        rw [hcdef, List.map_pmap]
        have e : (u.zip (u.rotate 1)).pmap (fun p (_ : G.Adj p.1 p.2) => p.1) hzadj
            = (u.zip (u.rotate 1)).map Prod.fst := by rw [List.pmap_eq_map]
        rw [e, List.map_fst_zip]
        simp
      have hcsnd : c.map (fun d => d.toProd.2) = u.rotate 1 := by
        rw [hcdef, List.map_pmap]
        have e : (u.zip (u.rotate 1)).pmap (fun p (_ : G.Adj p.1 p.2) => p.2) hzadj
            = (u.zip (u.rotate 1)).map Prod.snd := by rw [List.pmap_eq_map]
        rw [e, List.map_snd_zip]
        simp
      have hclen : c.length = n := by
        have hl : c.length = u.length := by
          have := congrArg List.length hcfst
          simpa using this
        rw [hl, hlen]
      refine (hmemF c).mpr ⟨hclen, ?_⟩
      have h1 : List.Forall₂ (fun d d' : G.Dart => d.toProd.2 = d'.toProd.1) c (c.rotate 1) := by
        refine hmapF _ _ c (c.rotate 1) (by simp) ?_
        rw [hcsnd, List.map_rotate, hcfst]
      have h2 : List.Forall₂ (fun d d' : G.Dart => d'.toProd.2 ≠ d.toProd.1) c (c.rotate 1) := by
        have hmaps : List.Forall₂ (· ≠ ·) ((c.rotate 1).map (fun d => d.toProd.2))
            (c.map (fun d => d.toProd.1)) := by
          rw [List.map_rotate, hcsnd, hcfst, List.rotate_rotate]
          exact hnb
        rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff] at hmaps
        exact hmaps.flip
      exact (hand _ _ c (c.rotate 1) h1 h2).imp (fun _ _ h => h)
    · -- its vertex trace is `u`
      rw [List.map_pmap]
      have e : (u.zip (u.rotate 1)).pmap (fun p (_ : G.Adj p.1 p.2) => p.1) hzadj
          = (u.zip (u.rotate 1)).map Prod.fst := by rw [List.pmap_eq_map]
      rw [e, List.map_fst_zip]
      simp
