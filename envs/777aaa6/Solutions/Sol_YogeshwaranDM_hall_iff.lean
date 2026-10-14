-- Prove2me | solution 1 for YogeshwaranDM.hall_iff
-- status  : ACCEPTED   (prove)
-- author  : @Wenqian Xing
-- created : 2026-09-06T12:29:40.921198+00:00
-- url     : https://prove2.me/submissions/740eb8a5-dbe0-4e71-aec2-52bb8557eb61

import Definitions.Def_YogeshwaranDM_CompleteMatching
import Mathlib.Combinatorics.SimpleGraph.Hall

open Set

theorem solution {V : Type*} [Fintype V] (G : SimpleGraph V)
    [G.LocallyFinite] (L R : Set V) (hG : G.IsBipartiteWith L R)
    (_hcover : L ∪ R = Set.univ) :
    (∃ M : G.Subgraph, YogeshwaranDM.CompleteMatching M L) ↔
      ∀ S ⊆ L, S.ncard ≤ (⋃ v ∈ S, G.neighborSet v).ncard := by
  classical
  constructor
  · rintro ⟨M, hM, hL⟩ S hS
    let f : V → V := fun v => if hv : v ∈ M.verts then (hM hv).choose else v
    have hf {v : V} (hv : v ∈ M.verts) : M.Adj v (f v) := by
      simp only [f, dif_pos hv]
      exact (hM hv).choose_spec.1
    apply Set.ncard_le_ncard_of_injOn f
    · intro v hv
      exact mem_iUnion.2 ⟨v, mem_iUnion.2 ⟨hv, M.adj_sub (hf (hL (hS hv)))⟩⟩
    · intro v hv w hw heq
      apply hM.eq_of_adj_right (hf (hL (hS hv)))
      rw [heq]
      exact hf (hL (hS hw))
  · intro h
    obtain ⟨M, hL, hM⟩ := SimpleGraph.exists_isMatching_of_forall_ncard_le hG h
    exact ⟨M, hM, hL⟩

