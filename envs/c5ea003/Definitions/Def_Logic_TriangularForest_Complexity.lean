-- Prove2me | Definitions.Def_Logic_TriangularForest_Complexity
-- name    : Logic_TriangularForest_Complexity
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-17T12:21:32.231374+00:00
-- url     : https://prove2.me/theorems/3302f57c-d962-4866-b3c0-16829ef7daca
-- title:
--   Aether Catalog definitions — Logic_TriangularForest_Complexity
-- statement:
--   Definition bundle for the Aether Catalog module `Logic.TriangularForest.Complexity`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Logic/TriangularForest/Complexity.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Logic_TriangularForest_ClassProperties
import Definitions.Def_Logic_TriangularForest_Decomposition
import Definitions.Def_Logic_TriangularForest_Defs

/-!
# The decision problem: certificates and decidability

The paper *Edge-decomposition into Two Triangular Forests is NP-complete* proves that the
decision problem

> given a graph `G`, can `E(G)` be partitioned into two triangular forests?

is NP-complete.  Membership in NP is the easy half: a decomposition is witnessed by a
**2-colouring of the edges**, an object of size linear in the number of edges, and both colour
classes can be checked to be triangular forests in polynomial time.  This file formalises that
half of the statement structurally:

* `TriangularForest.colorPart` — the colour class of an edge 2-colouring `f : Sym2 V → Bool`;
* `TriangularForest.decomposesIntoTwo_iff_exists_edgeColoring` — a graph decomposes into two
  triangular forests **iff** some edge 2-colouring has both colour classes triangular forests;
  so the search space for a witness is `2^{|E|}` rather than all pairs of graphs;
* `TriangularForest.instDecidableDecomposesIntoTwo` — consequently the decision problem is
  decidable (by a finite search over colourings, each test being decidable by
  `TriangularForest.instDecidableIsTriangularForest`).

Decidability of the *class* `F` and of the *decomposition problem* over `F` are exactly the
hypotheses under which the Lee–Liu–Tsai framework places the problem in NP.
-/

namespace TriangularForest

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

/-- The colour class of colour `b` of the edge 2-colouring `f` of `G`. -/
def colorPart (G : SimpleGraph V) (f : Sym2 V → Bool) (b : Bool) : SimpleGraph V :=
  SimpleGraph.fromEdgeSet {e | e ∈ G.edgeSet ∧ f e = b}

@[simp] theorem colorPart_adj {f : Sym2 V → Bool} {b : Bool} {u v : V} :
    (colorPart G f b).Adj u v ↔ G.Adj u v ∧ f s(u, v) = b := by
  simp only [colorPart, fromEdgeSet_adj, Set.mem_setOf_eq, mem_edgeSet]
  exact ⟨fun h => h.1, fun h => ⟨h, h.1.ne⟩⟩


/-- The two colour classes of an edge 2-colouring are edge-disjoint. -/
theorem colorPart_disjoint (f : Sym2 V → Bool) :
    Disjoint (colorPart G f true) (colorPart G f false) := by
  rw [disjoint_left]
  intro u v h1 h2
  have e1 := (colorPart_adj.1 h1).2
  have e2 := (colorPart_adj.1 h2).2
  rw [e1] at e2
  exact Bool.noConfusion e2

/-- The two colour classes of an edge 2-colouring cover the graph. -/
theorem colorPart_sup (f : Sym2 V → Bool) :
    colorPart G f true ⊔ colorPart G f false = G := by
  ext u v
  rw [sup_adj, colorPart_adj, colorPart_adj]
  cases f s(u, v) <;> simp

/-- **The decision problem has succinct certificates.**  A graph decomposes into two triangular
forests exactly when its edges can be 2-coloured so that each colour class is a triangular
forest.  This is the NP-membership half of the paper's main theorem: the witness is an edge
colouring (linear in the size of the input) and, by
`TriangularForest.instDecidableIsTriangularForest`, verifying it is an effective test. -/
theorem decomposesIntoTwo_iff_exists_edgeColoring :
    DecomposesIntoTwo G ↔ ∃ f : Sym2 V → Bool,
      IsTriangularForest (colorPart G f true) ∧ IsTriangularForest (colorPart G f false) := by
  classical
  constructor
  · rintro ⟨G₁, G₂, h₁, h₂, hd, hsup⟩
    refine ⟨fun e => decide (e ∈ G₁.edgeSet), ?_, ?_⟩
    · have hEq : colorPart G (fun e => decide (e ∈ G₁.edgeSet)) true = G₁ := by
        ext u v
        rw [colorPart_adj]
        simp only [decide_eq_true_eq, mem_edgeSet]
        refine ⟨fun h => h.2, fun h => ⟨?_, h⟩⟩
        rw [← hsup]
        exact Or.inl h
      rw [hEq]; exact h₁
    · have hEq : colorPart G (fun e => decide (e ∈ G₁.edgeSet)) false = G₂ := by
        ext u v
        rw [colorPart_adj]
        simp only [decide_eq_false_iff_not, mem_edgeSet]
        constructor
        · rintro ⟨hG, hn⟩
          rw [← hsup, sup_adj] at hG
          exact hG.resolve_left hn
        · intro h
          refine ⟨?_, fun hc => disjoint_left.1 hd u v hc h⟩
          rw [← hsup]
          exact Or.inr h
      rw [hEq]; exact h₂
  · rintro ⟨f, h₁, h₂⟩
    exact ⟨colorPart G f true, colorPart G f false, h₁, h₂, colorPart_disjoint f,
      colorPart_sup f⟩


section Decidable

variable [Fintype V] [DecidableEq V]

instance instDecidableRelColorPartAdj (G : SimpleGraph V) [DecidableRel G.Adj]
    (f : Sym2 V → Bool) (b : Bool) : DecidableRel (colorPart G f b).Adj := fun _ _ =>
  decidable_of_iff _ colorPart_adj.symm

/-- **The decomposition problem is decidable.**  Combined with
`decomposesIntoTwo_iff_exists_edgeColoring`, the search is over the finitely many edge
2-colourings, and each colour class is tested by the decision procedure for the class. -/
instance instDecidableDecomposesIntoTwo (G : SimpleGraph V) [DecidableRel G.Adj] :
    Decidable (DecomposesIntoTwo G) :=
  decidable_of_iff _ decomposesIntoTwo_iff_exists_edgeColoring.symm

end Decidable

end TriangularForest


