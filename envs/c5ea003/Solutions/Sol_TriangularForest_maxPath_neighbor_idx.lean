-- Prove2me | solution 1 for TriangularForest.maxPath_neighbor_idx
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T18:47:35.203708+00:00
-- url     : https://prove2.me/submissions/c20e2846-a405-4274-9b01-5685ab4123b5

-- Sol generated from Logic/TriangularForest/Sparsity.lean
import Mathlib
import Definitions.Def_Logic_TriangularForest_Defs
import Theorems.Thm_TriangularForest_length_eq_one_of_mem_edges
import Theorems.Thm_TriangularForest_maxPath_neighbor_mem_support

/-!
# Sparsity of triangular forests

The main result of this file is that triangular forests are *sparse*: a triangular forest on
`n ≥ 2` vertices has at most `2n - 3` edges (`TriangularForest.card_edgeFinset_add_three_le`).

The proof runs through a longest-path argument, which is the combinatorial heart of the file:

* `TriangularForest.exists_maxPath` — a finite nonempty graph has a path of maximum length;
* `TriangularForest.degree_le_two_of_maxPath_endpoint` — in a triangular forest the endpoint of
  a maximum length path has degree at most two.  Indeed all its neighbours lie on the path (else
  the path could be extended), and a neighbour sitting at distance `ℓ ≥ 2` along the path closes
  a cycle of length `ℓ + 1`, which must be `3`;
* `TriangularForest.exists_degree_le_two` — hence every finite nonempty triangular forest has a
  vertex of degree at most two (triangular forests are `2`-degenerate);
* the edge bound then follows by induction on the number of vertices, deleting a vertex of
  degree at most two.
-/

open TriangularForest

open SimpleGraph Finset

variable {V : Type*} {G : SimpleGraph V}




variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]










open TriangularForest in
theorem solution{a b : V} (hG : IsTriangularForest G) (p : G.Walk a b)
    (hp : p.IsPath) (hmax : ∀ (x y : V) (q : G.Walk x y), q.IsPath → q.length ≤ p.length)
    {x : V} (hx : x ∈ G.neighborFinset a) :
    p.support.idxOf x = 1 ∨ p.support.idxOf x = 2 := by
  have hxs : x ∈ p.support := maxPath_neighbor_mem_support p hp hmax hx
  have hadj : G.Adj a x := (G.mem_neighborFinset a x).1 hx
  set q := p.takeUntil x hxs with hq
  have hqp : q.IsPath := hp.takeUntil hxs
  have hqlen : q.length = p.support.idxOf x := p.length_takeUntil hxs
  have hne0 : q.length ≠ 0 := by
    intro h0
    have : q.Nil := Walk.nil_iff_length_eq.2 h0
    exact hadj.ne ((p.nil_takeUntil hxs).1 this)
  have hle2 : q.length ≤ 2 := by
    by_contra hgt
    push_neg at hgt
    have hnotedge : s(x, a) ∉ q.edges := fun hmem' => by
      have := length_eq_one_of_mem_edges q hqp hmem'
      omega
    have hcyc : (Walk.cons hadj.symm q).IsCycle :=
      SimpleGraph.Path.cons_isCycle ⟨q, hqp⟩ hadj.symm hnotedge
    have := hG _ hcyc
    rw [Walk.length_cons] at this
    omega
  rw [← hqlen]
  omega
