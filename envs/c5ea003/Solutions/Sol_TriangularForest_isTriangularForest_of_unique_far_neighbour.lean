-- Prove2me | solution 1 for TriangularForest.isTriangularForest_of_unique_far_neighbour
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-17T12:56:20.144491+00:00
-- url     : https://prove2.me/submissions/9c67081b-fadf-41e6-98dc-4f76afbee4fa

-- Sol generated from Logic/TriangularForest/Extremal.lean
import Mathlib
import Definitions.Def_Logic_TriangularForest_Complexity
import Definitions.Def_Logic_TriangularForest_Defs
import Definitions.Def_Logic_TriangularForest_Extremal

/-!
# The sparsity bound is attained for every odd order

`TriangularForest.two_mul_card_edgeFinset_le` says that a triangular forest on `n ≥ 1` vertices
satisfies `2e ≤ 3(n-1)`.  Here we show that this is *sharp for every odd `n`*, by exhibiting the
friendship (windmill) graphs `Fₖ`: `k` triangles glued at a common centre.

* `TriangularForest.isTriangularForest_of_unique_far_neighbour` — a structural membership
  criterion: if every vertex other than a fixed vertex `x` has at most one neighbour besides
  `x`, then the graph is a triangular forest.  This is the "windmill" criterion, and it is proved
  by a rotation argument on cycles rather than by a finite check;
* `TriangularForest.fan` — the friendship graph `Fₖ` on `2k+1` vertices;
* `TriangularForest.isTriangularForest_fan` — `Fₖ` is a triangular forest;
* `TriangularForest.card_edgeFinset_fan` — `Fₖ` has exactly `3k` edges;
* `TriangularForest.sparsity_bound_attained` — hence `2e = 3(n-1)` for `n = 2k+1`: the bound of
  `two_mul_card_edgeFinset_le` cannot be improved for any odd order.
-/

open TriangularForest

open SimpleGraph Finset

variable {V : Type*} {G : SimpleGraph V}


/-- Rotating a closed walk preserves its length. -/
theorem length_rotate [DecidableEq V] {v x : V} (c : G.Walk v v) (h : x ∈ c.support) :
    (c.rotate x h).length = c.length := by
  obtain ⟨n, hn⟩ := c.rotate_edges x h
  have hlen : (c.rotate x h).edges.length = c.edges.length := by
    rw [← hn, List.length_rotate]
  simpa [Walk.length_edges] using hlen























/-!
## Lab notes (cycle 3)

Hypotheses entering this cycle, and their fate.

* **H20** *(the sparsity bound `2e ≤ 3(n-1)` is attained only by the triangle)* — **false**.
  A brute-force enumeration of all graphs on `n ≤ 7` vertices (see `ComputationalEvidence.md`)
  gives maxima `e = 1, 3, 4, 6, 7, 9` for `n = 2,…,7`, i.e. exactly `⌊3(n-1)/2⌋`; the maximisers
  for odd `n` are the windmills.  Formalised here as `sparsity_bound_attained`, which upgrades
  the single example `triangle_tight` to an infinite family.
* **H21** *(windmills are triangular forests)* — **true**, and the proof generalises: what is
  really needed is only that every vertex other than the hub has at most one further neighbour
  (`isTriangularForest_of_unique_far_neighbour`).  The rotation trick used for 1-sums
  (`Logic.TriangularForest.OneSum`) is what makes this a three-line cycle analysis instead of an
  induction on block decompositions.
* **H22** *(the thickness bound `n - 1 ≤ 4k` of cycle 1 is not optimal)* — **true**: replacing
  the input `e ≤ 2n - 3` by the sharp `2e ≤ 3(n-1)` yields `n ≤ 3k`
  (`triangularThickness_lower_bound_sharp`), asymptotically a factor `4/3` better, and by H20
  the counting input is now optimal.  Any further improvement must therefore come from a global
  obstruction rather than from edge counting.  A randomised search (unverified, recorded in
  `ComputationalEvidence.md`) finds covers of `Kₙ` by exactly `⌈n/3⌉` triangular forests for
  every `n ≤ 11` **except** `n = 6`, where the counting bound allows `k = 2` but
  `completeGraph_not_decomposesIntoTwo_six` rules it out.  So the counting bound is essentially
  tight, with a single small exception.
* **H23** *(decomposability into two triangular forests has succinct certificates)* — **true**
  (`decomposesIntoTwo_iff_exists_edgeColoring`), and the certificate view makes the problem
  decidable (`instDecidableDecomposesIntoTwo`); evaluating that decision procedure on `K₄`
  returns `true`, matching the explicit `K₅` decomposition of cycle 1.
-/
open TriangularForest in
theorem solution(x : V)
    (h : ∀ a b c : V, a ≠ x → b ≠ x → c ≠ x → G.Adj a b → G.Adj a c → b = c) :
    IsTriangularForest G := by
  classical
  intro v c hc
  by_contra hlen
  have h3 := hc.three_le_length
  by_cases hx : x ∈ c.support
  · -- rotate so that the cycle starts at `x`; then `getVert 1, 2, 3` avoid `x`
    set c' := c.rotate x hx with hc'def
    have hc' : c'.IsCycle := hc.rotate hx
    have hL : c'.length = c.length := length_rotate c hx
    have h4 : 4 ≤ c'.length := by omega
    have hne : ∀ i, 1 ≤ i → i < c'.length → c'.getVert i ≠ x := by
      intro i hi1 hi2 hcon
      have := (hc'.getVert_endpoint_iff (le_of_lt hi2)).1 hcon
      omega
    have h12 : G.Adj (c'.getVert 1) (c'.getVert 2) := c'.adj_getVert_succ (by omega)
    have h23 : G.Adj (c'.getVert 2) (c'.getVert 3) := c'.adj_getVert_succ (by omega)
    have hmid := h (c'.getVert 2) (c'.getVert 1) (c'.getVert 3) (hne 2 (by omega) (by omega))
      (hne 1 (by omega) (by omega)) (hne 3 (by omega) (by omega)) h12.symm h23
    have := hc'.getVert_injOn' (by simp only [Set.mem_setOf_eq]; omega)
      (by simp only [Set.mem_setOf_eq]; omega : (3 : ℕ) ∈ {i | i ≤ c'.length - 1}) hmid
    omega
  · -- the cycle avoids `x` entirely, so its second vertex has two distinct far neighbours
    have hne : ∀ i, c.getVert i ≠ x := fun i hcon => hx (hcon ▸ c.getVert_mem_support i)
    have h01 : G.Adj (c.getVert 0) (c.getVert 1) := c.adj_getVert_succ (by omega)
    have h12 : G.Adj (c.getVert 1) (c.getVert 2) := c.adj_getVert_succ (by omega)
    have hmid := h (c.getVert 1) (c.getVert 0) (c.getVert 2) (hne 1) (hne 0) (hne 2) h01.symm h12
    have := hc.getVert_injOn' (by simp only [Set.mem_setOf_eq]; omega)
      (by simp only [Set.mem_setOf_eq]; omega : (2 : ℕ) ∈ {i | i ≤ c.length - 1}) hmid
    omega
