-- Prove2me | solution 1 for VertexSplitting.isChordal_of_unitIntervalRep
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T07:56:48.436498+00:00
-- url     : https://prove2.me/submissions/7fd3057b-b4fe-4f6f-98e1-b3c97bef77b3

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






/-! ### The matching upper bound for stars

Pairing up the leaves gives a splitting of `K_{1,n}` into `⌈n/2⌉` disjoint paths (`P₃`s, and one
`P₂` if `n` is odd), which is a unit interval graph.  Together with
`card_ge_of_split_clawFree_star` this determines the unit-interval splitting number of every
star exactly.
-/









open VertexSplitting in
theorem solution{W : Type*} {H : SimpleGraph W}
    (h : HasUnitIntervalRep H) : IsChordal H := by
  obtain ⟨p, hp⟩ := h
  rintro ⟨k, hk, c, hinj, hc⟩
  haveI : NeZero k := ⟨by omega⟩
  have hzero : ∀ n : ℕ, 0 < n → n < k → ((n : ℕ) : ZMod k) ≠ 0 := by
    intro n hn hnk hcontra
    rw [ZMod.natCast_eq_zero_iff] at hcontra
    exact absurd (Nat.le_of_dvd hn hcontra) (by omega)
  have h1 : (1 : ZMod k) ≠ 0 := by
    have := hzero 1 (by omega) (by omega); simpa using this
  have h2 : (2 : ZMod k) ≠ 0 := by
    have := hzero 2 (by omega) (by omega); simpa using this
  have h3 : (3 : ZMod k) ≠ 0 := by
    have := hzero 3 (by omega) (by omega); simpa using this
  obtain ⟨i, -, hmin⟩ := Finset.exists_min_image (Finset.univ : Finset (ZMod k))
    (fun i => p (c i)) ⟨0, Finset.mem_univ 0⟩
  have hadj1 : H.Adj (c i) (c (i + 1)) := (hc i (i + 1)).mpr (Or.inl rfl)
  have hadj2 : H.Adj (c i) (c (i - 1)) := (hc i (i - 1)).mpr (Or.inr (by ring))
  have hb1 := ((hp _ _).mp hadj1).2
  have hb2 := ((hp _ _).mp hadj2).2
  rw [abs_le] at hb1 hb2
  have hm1 := hmin (i + 1) (Finset.mem_univ _)
  have hm2 := hmin (i - 1) (Finset.mem_univ _)
  simp only at hm1 hm2
  have hne : c (i - 1) ≠ c (i + 1) := by
    intro hcc
    exact h2 (by linear_combination -hinj hcc)
  have hadj3 : H.Adj (c (i - 1)) (c (i + 1)) :=
    (hp _ _).mpr ⟨hne, abs_le.mpr ⟨by linarith, by linarith⟩⟩
  rcases (hc (i - 1) (i + 1)).mp hadj3 with heq | heq
  · exact h1 (by linear_combination heq)
  · exact h3 (by linear_combination -heq)
