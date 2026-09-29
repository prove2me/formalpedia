-- Prove2me | solution 1 for GreedyIndependentSet.caro_wei_finset
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T14:08:35.302592+00:00
-- url     : https://prove2.me/submissions/d22cbda5-07ba-4f63-875b-0e51e3b348a3

-- Sol generated from Bridges/CaroWeiGreedy.lean
import Mathlib
import Definitions.Def_Bridges_CaroWeiGreedy
/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Bridge: the probabilistic Caro–Wei bound ↔ a greedy (constructive) independent set

The Caro–Wei inequality
`α(G) ≥ ∑_v 1 / (deg v + 1)`
is the textbook example of the *probabilistic method with alterations*: order the vertices
uniformly at random and keep the vertices that precede all of their neighbours; the expected
number of kept vertices is `∑_v 1/(deg v + 1)`.

This file proves the inequality **without any probability space at all**: the whole content is a
strong induction that repeatedly deletes the closed neighbourhood of a vertex of *minimum*
degree, i.e. the greedy algorithm.  This is the constructive shadow of the expectation argument,
in the exact spirit of the mission ("Erdős's existence proofs are algorithms in disguise").

Main results:

* `GreedyIndependentSet.caro_wei_finset` — the induction engine, relativised to an arbitrary
  vertex subset `t`: there is an independent `s ⊆ t` with `∑_{v ∈ t} 1/(deg_t v + 1) ≤ #s`.
* `GreedyIndependentSet.caro_wei` — `∑_v 1/(deg v + 1) ≤ α(G)`.
* `GreedyIndependentSet.card_div_maxDegree_succ_le_indepNum` — the Turán-type corollary
  `n / (Δ + 1) ≤ α(G)`.
* `GreedyIndependentSet.turan_bound_of_cliqueFree` — Turán's theorem
  `#edges ≤ (1 - 1/r) n² / 2` for `K_{r+1}`-free graphs, on an *arbitrary* finite vertex type
  and with **no divisibility hypothesis**, obtained by applying Caro–Wei to the complement and
  Sedrakyan's (Cauchy–Schwarz) inequality.

## Catalog connections
* `Bridges/TuranExplicitCount.lean` : the explicit Turán graph attains this bound.
* `Bridges/ErdosProbabilisticRamsey.lean`, `Bridges/LovaszLocalLemmaFinite.lean` : the other
  members of the probabilistic-method trio.
-/

open Finset SimpleGraph

open GreedyIndependentSet

variable {V : Type*} [DecidableEq V] [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Closed neighbourhood of `v` inside `t` (local copy; the definition module's
version is private). -/
private def closedNbhd (t : Finset V) (v : V) : Finset V :=
  insert v (t.filter fun w => G.Adj v w)


omit [DecidableEq V] [Fintype V] in
lemma degIn_mono {t t' : Finset V} (h : t' ⊆ t) (v : V) : degIn G t' v ≤ degIn G t v :=
  card_le_card (filter_subset_filter _ h)



omit [Fintype V] in
private lemma card_closedNbhd (t : Finset V) (v : V) :
    #(closedNbhd G t v) = degIn G t v + 1 := by
  rw [closedNbhd, card_insert_of_notMem, degIn]
  simp [SimpleGraph.irrefl]

omit [Fintype V] in
private lemma closedNbhd_subset {t : Finset V} {v : V} (hv : v ∈ t) :
    closedNbhd G t v ⊆ t := by
  intro u hu
  rcases mem_insert.mp hu with h | h
  · exact h ▸ hv
  · exact (mem_filter.mp h).1







/-! ## From greedy independence to the off-diagonal Ramsey bound `R(3, k+1) > k²`

A triangle-free graph has independent neighbourhoods, so `Δ ≤ α`; combined with the greedy bound
`n ≤ α(Δ+1)` this gives `n ≤ α(α+1)`.  Contrapositively, a graph on more than `k(k+1)` vertices
contains a triangle or an independent set of size `k+1` — a verified lower bound for the
off-diagonal Ramsey number `R(3, k+1)`, obtained with no probability at all. -/





/-! ## Lab notes: sharpness of the two bounds

Experimental data (all checked by `decide` below, on the four-vertex Turán graph
`turanGraph 4 2`, which is the 4-cycle):

| quantity                       | value | source                            |
|--------------------------------|-------|-----------------------------------|
| `#edges`                       | `4`   | `card_edges_turanGraph_four_two`  |
| Turán bound `(1-1/2)·4²/2`     | `4`   | `turan_bound_sharp_four_two`      |
| `maxDegree`                    | `2`   | `maxDegree_turanGraph_four_two`   |
| greedy bound `n/(Δ+1) = 4/3`   | `1.33`| `card_div_maxDegree_succ_le_indepNum` |
| true independence number       | `2`   | the two colour classes            |

So the Turán inequality proved above is *attained* (it is not merely an upper bound), while the
`n/(Δ+1)` corollary is strict here — the loss is exactly the convexity slack in
Cauchy–Schwarz. -/






open GreedyIndependentSet in
omit [Fintype V] in
theorem solution(t : Finset V) :
    ∃ s ⊆ t, G.IsIndepSet (s : Set V) ∧
      ∑ v ∈ t, (1 : ℝ) / (degIn G t v + 1) ≤ #s := by
  induction t using Finset.strongInduction with
  | _ t ih =>
    rcases t.eq_empty_or_nonempty with rfl | hne
    · exact ⟨∅, by simp, by simp [SimpleGraph.IsIndepSet], by simp⟩
    obtain ⟨v, hv, hmin⟩ := t.exists_min_image (degIn G t) hne
    set B := closedNbhd G t v with hB
    have hBt : B ⊆ t := closedNbhd_subset G hv
    have hvB : v ∈ B := mem_insert_self _ _
    have hsub : t \ B ⊂ t := by
      refine ⟨sdiff_subset, fun hcon => ?_⟩
      have := hcon hv
      simp [mem_sdiff, hvB] at this
    obtain ⟨s', hs't', hind', hsum'⟩ := ih (t \ B) hsub
    have hvs' : v ∉ s' := fun h => by
      have := hs't' h
      rw [mem_sdiff] at this
      exact this.2 hvB
    refine ⟨insert v s', ?_, ?_, ?_⟩
    · intro u hu
      rcases mem_insert.mp hu with rfl | h
      · exact hv
      · exact (mem_sdiff.mp (hs't' h)).1
    · -- independence
      have key : ∀ u ∈ s', u ≠ v ∧ ¬ G.Adj v u := by
        intro u hu
        have hu' := hs't' hu
        rw [mem_sdiff] at hu'
        refine ⟨fun h => hu'.2 (h ▸ hvB), fun hadj => hu'.2 ?_⟩
        exact mem_insert_of_mem (mem_filter.mpr ⟨hu'.1, hadj⟩)
      have hsymm : Symmetric (fun v w : V => ¬ G.Adj v w) := fun a b hab hba => hab hba.symm
      rw [SimpleGraph.isIndepSet_iff, coe_insert,
        Set.pairwise_insert_of_symmetric hsymm]
      refine ⟨hind', fun u hu _ => (key u hu).2⟩
    · -- the counting step
      have hsplit : ∑ u ∈ t \ B, (1 : ℝ) / (degIn G t u + 1)
          + ∑ u ∈ B, (1 : ℝ) / (degIn G t u + 1)
          = ∑ u ∈ t, (1 : ℝ) / (degIn G t u + 1) := sum_sdiff hBt
      have hB_le : ∑ u ∈ B, (1 : ℝ) / (degIn G t u + 1) ≤ 1 := by
        have hbound : ∀ u ∈ B, (1 : ℝ) / (degIn G t u + 1) ≤ 1 / (degIn G t v + 1) := by
          intro u hu
          have hut : u ∈ t := hBt hu
          have := hmin u hut
          apply one_div_le_one_div_of_le
          · positivity
          · exact_mod_cast Nat.add_le_add_right this 1
        calc ∑ u ∈ B, (1 : ℝ) / (degIn G t u + 1)
            ≤ ∑ _u ∈ B, (1 : ℝ) / (degIn G t v + 1) := sum_le_sum hbound
          _ = (#B : ℝ) * (1 / (degIn G t v + 1)) := by rw [sum_const, nsmul_eq_mul]
          _ = 1 := by
              rw [card_closedNbhd]
              push_cast
              field_simp
      have hrest : ∑ u ∈ t \ B, (1 : ℝ) / (degIn G t u + 1) ≤ (#s' : ℝ) := by
        refine le_trans (sum_le_sum ?_) hsum'
        intro u _
        apply one_div_le_one_div_of_le
        · positivity
        · have := degIn_mono G (sdiff_subset (s := t) (t := B)) u
          exact_mod_cast Nat.add_le_add_right this 1
      have hcard : (#(insert v s') : ℝ) = (#s' : ℝ) + 1 := by
        rw [card_insert_of_notMem hvs']
        push_cast
        ring
      rw [hcard, ← hsplit]
      linarith
