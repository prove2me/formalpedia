-- Prove2me | solution 2 for SimpleGraph.IsStarSum.sum_card_le_indepNum_of_notMem
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-20T21:11:46.894979+00:00
-- url     : https://prove2.me/submissions/bd374c94-bf05-4eac-977d-60db76a1e65c

import Mathlib
import Definitions.Def_Novelty_IndependenceRatioChromatic
import Definitions.Def_Novelty_OneSumEqualityAnalysis
import Definitions.Def_Novelty_OneSumStarAmalgam
import Definitions.Def_Novelty_StarAmalgamThresholdFamily

open Finset SimpleGraph SimpleGraph.IsStarSum in
theorem solution {V ι : Type*} {G : SimpleGraph V} {H : ι → SimpleGraph V} {A : ι → Set V} {v : V}
    (h : IsStarSum G H A v) [Fintype V] [DecidableEq V] [Fintype ι] {t : ι → Finset V}
    (ht : ∀ i, ↑(t i) ⊆ A i) (hti : ∀ i, (H i).IsIndepSet ↑(t i)) (htv : ∀ i, v ∉ t i) :
    ∑ i, (t i).card ≤ G.indepNum := by
  classical
  -- two distinct sides meet only at the cut vertex
  have hmeet : ∀ (i j : ι), i ≠ j → ∀ x, x ∈ A i → x ∈ A j → x = v := by
    intro i j hij x hxi hxj
    have hx : x ∈ A i ∩ A j := ⟨hxi, hxj⟩
    rw [h.inter_eq i j hij] at hx
    exact hx
  -- every edge of `G` is an edge of some part
  have hadj : ∀ x y : V, G.Adj x y → ∃ i, (H i).Adj x y := by
    intro x y hxy
    rw [h.sup_eq] at hxy
    exact SimpleGraph.iSup_adj.1 hxy
  -- a family of independent sets avoiding the cut vertex unions to an independent set
  have hindep : ∀ u : ι → Finset V, (∀ i, ↑(u i) ⊆ A i) → (∀ i, (H i).IsIndepSet ↑(u i)) →
      (∀ i, v ∉ u i) → G.IsIndepSet ↑(Finset.univ.biUnion u) := by
    intro u hu hui huv x hx y hy hne hG
    simp only [Finset.coe_biUnion, Set.mem_iUnion, Finset.mem_coe] at hx hy
    obtain ⟨j, -, hxj⟩ := hx
    obtain ⟨k, -, hyk⟩ := hy
    obtain ⟨i, hHi⟩ := hadj x y hG
    have hxA : x ∈ A i := (h.support i hHi).1
    have hyA : y ∈ A i := (h.support i hHi).2
    have hxi : x ∈ u i := by
      by_cases hji : j = i
      · exact hji ▸ hxj
      · have hxv : x = v := hmeet j i hji x (hu j (Finset.mem_coe.2 hxj)) hxA
        rw [hxv] at hxj
        exact absurd hxj (huv j)
    have hyi : y ∈ u i := by
      by_cases hki : k = i
      · exact hki ▸ hyk
      · have hyv : y = v := hmeet k i hki y (hu k (Finset.mem_coe.2 hyk)) hyA
        rw [hyv] at hyk
        exact absurd hyk (huv k)
    exact (hui i) (Finset.mem_coe.2 hxi) (Finset.mem_coe.2 hyi) hne hHi
  have hU : G.IsIndepSet ↑(Finset.univ.biUnion t) := hindep t ht hti htv
  have hdisj : (Finset.univ.biUnion t).card = ∑ i, (t i).card := by
    refine Finset.card_biUnion ?_
    intro i _ j _ hij
    refine Finset.disjoint_left.2 ?_
    intro x hxi hxj
    have hxv : x = v := hmeet i j hij x (ht i (Finset.mem_coe.2 hxi)) (ht j (Finset.mem_coe.2 hxj))
    rw [hxv] at hxi
    exact htv i hxi
  rw [← hdisj]
  exact hU.card_le_indepNum
