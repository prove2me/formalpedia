-- Prove2me | solution 1 for K2UnionIndependentFree.free_iff_antineighborhood_independent
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T05:52:19.347194+00:00
-- url     : https://prove2.me/submissions/516d8381-b335-4d1d-92fb-12f8cadda4f6

-- Sol generated from Bridges/GraphTheory/K2UnionIndependentFree.lean
import Mathlib
import Definitions.Def_Bridges_GraphTheory_K2UnionIndependentFree

/-!
# A structural lemma for `(K₂ ∪ kK₁)`-free graphs

The forbidden induced subgraph condition has a useful equivalent local form: after fixing
an independent `k`-set, the vertices with no neighbour in that set induce an edgeless graph.
This is one of the elementary reductions used in Hamilton-connectivity arguments for this
graph class.
-/

open Finset

open K2UnionIndependentFree

variable {V : Type*}



/-- **Main structural theorem.** In a `(K₂ ∪ kK₁)`-free graph, the common
antineighbourhood of every independent set of size at least `k` is independent. -/
theorem antiNeighborhood_isIndepSet {G : SimpleGraph V} {k : ℕ}
    (hfree : IsK2UnionK1Free G k) {I : Finset V}
    (hI : G.IsIndepSet (I : Set V)) (hk : k ≤ I.card) :
    G.IsIndepSet (antiNeighborhood G (I : Set V)) := by
  refine fun v hv w hw hne => ?_
  simp only [antiNeighborhood] at hv hw
  intro hadj
  have h_exists : ∃ J : Finset V, J ⊆ I ∧ J.card = k := Finset.exists_subset_card_eq hk
  obtain ⟨J, hJI, hJcard⟩ := h_exists
  exact hfree hadj J hJcard (hI.mono (fun z hz => hJI hz))
    (fun z hz => ⟨hv z (hJI hz), hw z (hJI hz)⟩)







open K2UnionIndependentFree in
theorem solution{G : SimpleGraph V} {k : ℕ} :
    IsK2UnionK1Free G k ↔
      ∀ I : Finset V, I.card = k → G.IsIndepSet (I : Set V) →
        G.IsIndepSet (antiNeighborhood G (I : Set V)) := by
  constructor
  · intro hfree I hcard hI
    exact antiNeighborhood_isIndepSet hfree hI hcard.ge
  · intro hlocal u v huv I hcard hI hanti
    have hu : u ∈ antiNeighborhood G (I : Set V) := by
      intro x hx
      exact (hanti x hx).1
    have hv : v ∈ antiNeighborhood G (I : Set V) := by
      intro x hx
      exact (hanti x hx).2
    exact hlocal I hcard hI hu hv huv.ne huv
