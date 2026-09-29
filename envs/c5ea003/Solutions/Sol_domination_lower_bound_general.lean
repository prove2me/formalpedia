-- Prove2me | solution 1 for domination_lower_bound_general
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-19T05:56:50.345985+00:00
-- url     : https://prove2.me/submissions/1f5da5cc-1108-4a96-93d5-83dfc231b871

import Mathlib
import Definitions.Def_Novelty_TransmissionDominationTree
theorem solution {V} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (D : Finset V) (h : IsDominatingSet G D) :
    Fintype.card V ≤ (G.maxDegree + 1) * D.card := by
  -- the closed neighbourhoods of `D` cover every vertex
  have hsub : (Finset.univ : Finset V) ⊆ D.biUnion (fun d => insert d (G.neighborFinset d)) := by
    intro v _
    rw [Finset.mem_biUnion]
    rcases h v with hv | ⟨d, hd, hadj⟩
    · exact ⟨v, hv, Finset.mem_insert_self _ _⟩
    · exact ⟨d, hd, Finset.mem_insert_of_mem ((G.mem_neighborFinset d v).mpr hadj)⟩
  -- and each has at most `Δ + 1` vertices
  calc Fintype.card V = (Finset.univ : Finset V).card := Finset.card_univ.symm
    _ ≤ (D.biUnion (fun d => insert d (G.neighborFinset d))).card := Finset.card_le_card hsub
    _ ≤ ∑ d ∈ D, (insert d (G.neighborFinset d)).card := Finset.card_biUnion_le
    _ ≤ ∑ _d ∈ D, (G.maxDegree + 1) := by
        refine Finset.sum_le_sum fun d _ => (Finset.card_insert_le _ _).trans ?_
        rw [SimpleGraph.card_neighborFinset_eq_degree]
        exact Nat.add_le_add_right (G.degree_le_maxDegree d) 1
    _ = (G.maxDegree + 1) * D.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
