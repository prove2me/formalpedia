-- Prove2me | solution 2 for TriangularForest.completeGraph_decomposesIntoTwo_five
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-17T07:29:50.384461+00:00
-- url     : https://prove2.me/submissions/15655362-de24-4e07-85b6-3d87a240f5fb

import Definitions.Def_Logic_TriangularForest_Decomposition

open SimpleGraph TriangularForest Finset

open SimpleGraph TriangularForest Finset in
/-- **`K₅` decomposes into two triangular forests.** -/
theorem solution : DecomposesIntoTwo (⊤ : SimpleGraph (Fin 5)) := by
  classical
  have two_le : ∀ (G : SimpleGraph (Fin 5)) [DecidableRel G.Adj] {v : Fin 5} {c : G.Walk v v},
      c.IsCycle → ∀ {x : Fin 5}, x ∈ c.support → 2 ≤ G.degree x := by
    intro G _ v c hc x hx
    have hc' := hc.rotate hx
    have hnn := hc'.not_nil
    have h1 : G.Adj x (c.rotate x hx).snd := Walk.adj_snd hnn
    have h2 : G.Adj x (c.rotate x hx).penultimate := (Walk.adj_penultimate hnn).symm
    have hne := hc'.snd_ne_penultimate
    rw [← G.card_neighborFinset_eq_degree x]
    have hsub : ({(c.rotate x hx).snd, (c.rotate x hx).penultimate} : Finset (Fin 5))
        ⊆ G.neighborFinset x := by
      intro y hy
      simp only [Finset.mem_insert, Finset.mem_singleton] at hy
      rcases hy with rfl | rfl
      · exact (G.mem_neighborFinset x _).mpr h1
      · exact (G.mem_neighborFinset x _).mpr h2
    calc 2 = ({(c.rotate x hx).snd, (c.rotate x hx).penultimate} : Finset (Fin 5)).card :=
          (Finset.card_pair hne).symm
      _ ≤ _ := Finset.card_le_card hsub
  have len_le : ∀ (G : SimpleGraph (Fin 5)) [DecidableRel G.Adj] {v : Fin 5} {c : G.Walk v v},
      c.IsCycle → c.length ≤ #{x ∈ (univ : Finset (Fin 5)) | 2 ≤ G.degree x} := by
    intro G _ v c hc
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
    exact two_le G hc (List.mem_of_mem_tail hx)
  have isTF : ∀ (G : SimpleGraph (Fin 5)) [DecidableRel G.Adj],
      #{x ∈ (univ : Finset (Fin 5)) | 2 ≤ G.degree x} ≤ 3 → IsTriangularForest G := by
    intro G _ h v c hc
    have h1 := len_le G hc
    have h2 := hc.three_le_length
    omega
  refine ⟨K5part1, K5part2, isTF K5part1 (by decide), isTF K5part2 (by decide), ?_, ?_⟩
  · rw [disjoint_iff]
    ext a b
    fin_cases a <;> fin_cases b <;> decide
  · ext a b
    fin_cases a <;> fin_cases b <;> decide
