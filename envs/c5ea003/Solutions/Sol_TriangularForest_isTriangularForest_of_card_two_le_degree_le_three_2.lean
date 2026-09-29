-- Prove2me | solution 2 for TriangularForest.isTriangularForest_of_card_two_le_degree_le_three
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-17T07:36:51.770578+00:00
-- url     : https://prove2.me/submissions/d9fa618d-cab5-4c3e-825f-bf60bb369a48

import Definitions.Def_Logic_TriangularForest_Defs

open SimpleGraph TriangularForest Finset

open SimpleGraph TriangularForest Finset in
/-- **A graph with at most three vertices of degree ≥ 2 is a triangular forest.** -/
theorem solution {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableRel G.Adj] [DecidableEq V]
    (h : #{x ∈ (univ : Finset V) | 2 ≤ G.degree x} ≤ 3) : IsTriangularForest G := by
  have two_le : ∀ {v : V} {c : G.Walk v v}, c.IsCycle → ∀ {x : V}, x ∈ c.support → 2 ≤ G.degree x := by
    intro v c hc x hx
    have hc' := hc.rotate hx
    have hnn := hc'.not_nil
    have h1 : G.Adj x (c.rotate x hx).snd := Walk.adj_snd hnn
    have h2 : G.Adj x (c.rotate x hx).penultimate := (Walk.adj_penultimate hnn).symm
    have hne := hc'.snd_ne_penultimate
    rw [← G.card_neighborFinset_eq_degree x]
    have hsub : ({(c.rotate x hx).snd, (c.rotate x hx).penultimate} : Finset V) ⊆ G.neighborFinset x := by
      intro y hy
      simp only [Finset.mem_insert, Finset.mem_singleton] at hy
      rcases hy with rfl | rfl
      · exact (G.mem_neighborFinset x _).mpr h1
      · exact (G.mem_neighborFinset x _).mpr h2
    calc 2 = ({(c.rotate x hx).snd, (c.rotate x hx).penultimate} : Finset V).card :=
          (Finset.card_pair hne).symm
      _ ≤ _ := Finset.card_le_card hsub
  have len_le : ∀ {v : V} {c : G.Walk v v}, c.IsCycle → c.length ≤ #{x ∈ (univ : Finset V) | 2 ≤ G.degree x} := by
    intro v c hc
    have hnd := hc.support_nodup
    have hlen : c.support.tail.length = c.length := by
      have h := c.length_support
      rw [List.length_tail]
      omega
    rw [← hlen, ← List.toFinset_card_of_nodup hnd]
    apply Finset.card_le_card
    intro x hx
    rw [List.mem_toFinset] at hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact two_le hc (List.mem_of_mem_tail hx)
  intro v c hc
  have h1 := len_le hc
  have h2 := hc.three_le_length
  omega
