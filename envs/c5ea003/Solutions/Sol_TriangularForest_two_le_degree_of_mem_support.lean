-- Prove2me | solution 1 for TriangularForest.two_le_degree_of_mem_support
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-17T07:43:58.845158+00:00
-- url     : https://prove2.me/submissions/2fabe377-4c65-4358-83ba-e1943910eb9a

import Definitions.Def_Logic_TriangularForest_Defs

open SimpleGraph TriangularForest Finset

open SimpleGraph TriangularForest Finset in
/-- **Every vertex on a cycle has degree at least 2.** -/
theorem solution {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableRel G.Adj]
    {v : V} {c : G.Walk v v} (hc : c.IsCycle) {x : V} (hx : x ∈ c.support) : 2 ≤ G.degree x := by
  classical
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
  exact two_le hc hx
