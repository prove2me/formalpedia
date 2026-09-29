-- Prove2me | solution 1 for TuranExplicitCount.two_mul_card_edgeFinset_turanGraph_general
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-19T17:28:09.886998+00:00
-- url     : https://prove2.me/submissions/9e06de04-6051-4bdb-be9f-9aff6598344e

import Mathlib
import Definitions.Def_Bridges_TuranExplicitCount
open TuranExplicitCount Finset SimpleGraph in
theorem solution {n r : ℕ} (hr : 0 < r) :
    2 * #(turanGraph n r).edgeFinset + ∑ i ∈ range r, (classSize n r i) ^ 2 = n ^ 2 := by
  rw [← sum_degrees_eq_twice_card_edges]
  -- each vertex is adjacent exactly to the vertices outside its own residue class
  have hdeg : ∀ v : Fin n, (turanGraph n r).degree v + classSize n r ((v : ℕ) % r) = n := by
    intro v
    rw [← card_neighborFinset_eq_degree, neighborFinset_eq_filter, classSize]
    have h := card_filter_add_card_filter_not (s := (univ : Finset (Fin n)))
      (fun w : Fin n => (w : ℕ) % r = (v : ℕ) % r)
    rw [card_univ, Fintype.card_fin] at h
    rw [add_comm]
    convert h using 3
    ext w
    simp [turanGraph_adj, eq_comm]
  -- grouping vertices by residue class
  have hsum : ∑ v : Fin n, classSize n r ((v : ℕ) % r) = ∑ i ∈ range r, classSize n r i ^ 2 := by
    rw [← sum_fiberwise_of_maps_to (g := fun v : Fin n => (v : ℕ) % r) (t := range r)
      (fun v _ => mem_range.2 (Nat.mod_lt _ hr))]
    refine sum_congr rfl (fun i _ => ?_)
    rw [sum_congr rfl (fun v hv => by rw [(mem_filter.1 hv).2]), sum_const, smul_eq_mul, sq]
    rfl
  have htot : ∑ v : Fin n, ((turanGraph n r).degree v + classSize n r ((v : ℕ) % r)) = n ^ 2 := by
    rw [sum_congr rfl (fun v _ => hdeg v), sum_const, card_univ, Fintype.card_fin, smul_eq_mul, sq]
  rw [sum_add_distrib, hsum] at htot
  exact htot
