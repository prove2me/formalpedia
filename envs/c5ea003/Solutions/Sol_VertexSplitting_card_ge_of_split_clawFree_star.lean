-- Prove2me | solution 1 for VertexSplitting.card_ge_of_split_clawFree_star
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T07:52:17.958449+00:00
-- url     : https://prove2.me/submissions/d3deb4ba-62e4-4aa6-9b56-0c9272983fbd

-- Sol generated from Bridges/VertexSplittingExact.lean
import Mathlib
import Definitions.Def_Bridges_VertexSplitting
import Definitions.Def_Bridges_VertexSplittingExact
/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/

/-!
# Exact splitting numbers for the smallest obstructions

This file complements `Bridges.VertexSplitting`, where the general theory of the vertex
splitting operation of *Hardness of Vertex Splitting: Cographs, Chordal Graphs, and Beyond*
is developed, with **exact** values of the splitting number for the smallest obstructions of
each of the three target classes studied there.

Main results:

* `isChordal_of_unitIntervalRep`: unit interval graphs are chordal (so the unit-interval
  splitting number always dominates the chordal one).
* `cograph_split_pathP4_exact`: the cograph splitting number of `P₄` is exactly one, and the
  single split can be taken exclusive.
* `chordal_split_cycleC4_exact`: the chordal splitting number of `C₄` is exactly one.
* `unitInterval_split_starK13_exact`: the unit-interval splitting number of the claw `K_{1,3}`
  is exactly one.
* `unitInterval_split_starK14_exact`: the unit-interval splitting number of `K_{1,4}` is also
  exactly one.  In particular the guess that `K_{1,n}` needs `n - 2` splits is false already
  for `n = 4`: pairing the leaves shows `⌈n/2⌉ - 1` splits suffice.
* `card_ge_of_split_clawFree_star` and `unitInterval_split_star_exact`: for every `n ≥ 1` the
  unit-interval splitting number of the star `K_{1,n}` is exactly `⌈n/2⌉ - 1`, by an exclusive
  splitting into `⌈n/2⌉` disjoint short paths, and a matching counting lower bound valid for
  every claw-free target.
-/

open VertexSplitting

open SimpleGraph

/-! ## Unit interval graphs are chordal -/


/-! ## `P₄`: one split makes a cograph -/








/-! ## `C₄`: one split makes a chordal graph -/









/-! ## Stars: one split makes `K_{1,3}` and `K_{1,4}` unit interval graphs -/


















/-! ## A general lower bound for stars

The claw `K_{1,3}` is the smallest obstruction to being a unit interval graph, and a star
`K_{1,n}` contains many of them.  Since claw-free graphs let every copy of the centre keep at
most two leaves, at least `⌈n/2⌉` copies of the centre are needed.
-/


theorem starGraph_adj_ne_zero {n : ℕ} {u v : Fin (n + 1)} (h : (starGraph n).Adj u v) :
    u = 0 ∨ v = 0 := by
  rw [starGraph, SimpleGraph.fromRel_adj] at h
  rcases h.2 with ⟨h1, -⟩ | ⟨h1, -⟩
  · exact Or.inl h1
  · exact Or.inr h1

theorem starGraph_adj_zero {n : ℕ} {v : Fin (n + 1)} (hv : v ≠ 0) :
    (starGraph n).Adj 0 v := by
  rw [starGraph, SimpleGraph.fromRel_adj]
  exact ⟨Ne.symm hv, Or.inl ⟨rfl, hv⟩⟩



/-! ### The matching upper bound for stars

Pairing up the leaves gives a splitting of `K_{1,n}` into `⌈n/2⌉` disjoint paths (`P₃`s, and one
`P₂` if `n` is odd), which is a unit interval graph.  Together with
`card_ge_of_split_clawFree_star` this determines the unit-interval splitting number of every
star exactly.
-/









open VertexSplitting in
theorem solution{n : ℕ} {W : Type*} [Fintype W]
    {H : SimpleGraph W} {f : W → Fin (n + 1)} (h : IsSplit (starGraph n) H f)
    (hclaw : ¬ HasInducedClaw H) : n + (n + 1) / 2 ≤ Fintype.card W := by
  classical
  have key : ∀ v : Fin (n + 1), ∃ x y : W, v ≠ 0 → (f x = 0 ∧ f y = v ∧ H.Adj x y) := by
    intro v
    by_cases hv : v = 0
    · obtain ⟨x, -⟩ := h.surj 0
      exact ⟨x, x, fun hc => absurd hv hc⟩
    · obtain ⟨x, y, hx, hy, hxy⟩ := h.cover 0 v (starGraph_adj_zero hv)
      exact ⟨x, y, fun _ => ⟨hx, hy, hxy⟩⟩
  choose X Y hXY using key
  set S : Finset (Fin (n + 1)) := Finset.univ.filter (fun v => v ≠ 0) with hSdef
  set C : Finset W := Finset.univ.filter (fun x => f x = 0) with hCdef
  set L : Finset W := Finset.univ.filter (fun x => ¬ f x = 0) with hLdef
  have hScard : S.card = n := by
    have : S = Finset.univ.erase (0 : Fin (n + 1)) := by
      ext v; simp [hSdef, Finset.mem_erase]
    rw [this, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
    omega
  have hsum : C.card + L.card = Fintype.card W := by
    rw [hCdef, hLdef, Finset.card_filter_add_card_filter_not, Finset.card_univ]
  have hLcard : n ≤ L.card := by
    rw [← hScard]
    refine Finset.card_le_card_of_surjOn f ?_
    intro v hv
    simp only [hSdef, Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_univ, true_and] at hv
    obtain ⟨x, hx⟩ := h.surj v
    exact ⟨x, by simp [hLdef, hx, hv], hx⟩
  have hfib : ∀ c ∈ S.image X, (S.filter (fun v => X v = c)).card ≤ 2 := by
    intro c _
    by_contra hlt
    push_neg at hlt
    obtain ⟨a, b, d, ha, hb, hd, hab, had, hbd⟩ := Finset.two_lt_card_iff.mp hlt
    simp only [Finset.mem_filter, hSdef, Finset.mem_univ, true_and] at ha hb hd
    obtain ⟨ha0, haX⟩ := ha
    obtain ⟨hb0, hbX⟩ := hb
    obtain ⟨hd0, hdX⟩ := hd
    obtain ⟨-, hYa, hadja⟩ := hXY a ha0
    obtain ⟨-, hYb, hadjb⟩ := hXY b hb0
    obtain ⟨-, hYd, hadjd⟩ := hXY d hd0
    have hne : ∀ u v : Fin (n + 1), u ≠ v → f (Y u) = u → f (Y v) = v → Y u ≠ Y v := by
      intro u v huv hu hv hcc
      exact huv (by rw [← hu, ← hv, hcc])
    have hnadj : ∀ u v : Fin (n + 1), u ≠ 0 → v ≠ 0 → f (Y u) = u → f (Y v) = v →
        ¬ H.Adj (Y u) (Y v) := by
      intro u v hu0 hv0 hu hv hcc
      rcases starGraph_adj_ne_zero (h.adj_proj _ _ hcc) with hz | hz
      · exact hu0 (by rw [← hu, hz])
      · exact hv0 (by rw [← hv, hz])
    refine hclaw ⟨c, Y a, Y b, Y d, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact haX ▸ hadja
    · exact hbX ▸ hadjb
    · exact hdX ▸ hadjd
    · exact hne a b hab hYa hYb
    · exact hne a d had hYa hYd
    · exact hne b d hbd hYb hYd
    · exact hnadj a b ha0 hb0 hYa hYb
    · exact hnadj a d ha0 hd0 hYa hYd
    · exact hnadj b d hb0 hd0 hYb hYd
  have hSle : S.card ≤ 2 * (S.image X).card := Finset.card_le_mul_card_image S 2 hfib
  have himg : S.image X ⊆ C := by
    intro c hc
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hc
    simp only [Finset.mem_filter, hSdef, Finset.mem_univ, true_and] at hv
    simp [hCdef, (hXY v hv).1]
  have hCle : (S.image X).card ≤ C.card := Finset.card_le_card himg
  omega
