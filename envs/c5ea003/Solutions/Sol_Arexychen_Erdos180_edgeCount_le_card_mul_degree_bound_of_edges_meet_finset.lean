-- Prove2me | solution 1 for Arexychen.Erdos180.edgeCount_le_card_mul_degree_bound_of_edges_meet_finset
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-09-09T07:31:31.904687+00:00
-- url     : https://prove2.me/submissions/eef63a2c-8807-4051-9ddb-974382c550ba

import Definitions.Def_arexychen_erdos180_core
import Mathlib.Analysis.Asymptotics.Theta
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Combinatorics.SimpleGraph.Matching
import Mathlib.Combinatorics.SimpleGraph.Subgraph
import Mathlib.Tactic

namespace Arexychen


open Filter
open Asymptotics

noncomputable section

namespace Erdos180

attribute [local instance] SimpleGraph.neighborSetFintype

universe u v w

end Erdos180
end
end Arexychen

section
open Filter
open Asymptotics
attribute [local instance] SimpleGraph.neighborSetFintype
universe u v w
open Arexychen.Erdos180 in
/--
If every edge of a finite graph meets a finite vertex set `T`, and every vertex
of `T` has degree at most `A`, then the number of edges is at most `#T * A`.

This is the counting core of the star/matching obstruction: take `T` to be the
vertices saturated by a maximal matching.
-/
theorem solution
    {V : Type u} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (T : Finset V) (A : ℕ)
    (hdeg : ∀ v ∈ T, G.degree v ≤ A)
    (hcover : ∀ ⦃x y : V⦄, G.Adj x y → x ∈ T ∨ y ∈ T) :
    edgeCount G ≤ T.card * A := by
  classical
  have hedge : edgeCount G = G.edgeFinset.card := by
    rw [edgeCount, Nat.card_eq_fintype_card, ← SimpleGraph.edgeFinset_card]
  have h_edges_subset :
      G.edgeFinset ⊆ T.biUnion (fun v => G.incidenceFinset v) := by
    intro e he
    induction e using Sym2.ind with
    | h x y =>
        rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at he
        rw [Finset.mem_biUnion]
        rcases hcover he with hx | hy
        · refine ⟨x, hx, ?_⟩
          rw [SimpleGraph.mem_incidenceFinset]
          exact (G.mk'_mem_incidenceSet_left_iff).2 he
        · refine ⟨y, hy, ?_⟩
          rw [SimpleGraph.mem_incidenceFinset]
          exact (G.mk'_mem_incidenceSet_right_iff).2 he
  rw [hedge]
  refine (Finset.card_le_card h_edges_subset).trans ?_
  refine Finset.card_biUnion_le_card_mul T (fun v => G.incidenceFinset v) A ?_
  intro v hv
  simpa [SimpleGraph.card_incidenceFinset_eq_degree] using hdeg v hv
end
namespace Arexychen
noncomputable section
namespace Erdos180


















end Erdos180

end
end Arexychen
