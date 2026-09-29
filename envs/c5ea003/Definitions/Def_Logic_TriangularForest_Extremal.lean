-- Prove2me | Definitions.Def_Logic_TriangularForest_Extremal
-- name    : Logic_TriangularForest_Extremal
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-17T12:22:11.617698+00:00
-- url     : https://prove2.me/theorems/3b185f55-8271-4d9b-a602-e413c4045a6b
-- title:
--   Aether Catalog definitions — Logic_TriangularForest_Extremal
-- statement:
--   Definition bundle for the Aether Catalog module `Logic.TriangularForest.Extremal`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Logic/TriangularForest/Extremal.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Logic_TriangularForest_Complexity

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

namespace TriangularForest

open SimpleGraph Finset

variable {V : Type*} {G : SimpleGraph V}

section Criterion



end Criterion

section Fan

/-- Adjacency of the friendship graph on `{0, 1, …, 2k}`: the centre `0` is adjacent to
everything, and `2i-1` is matched with `2i`. -/
def FanAdj (a b : ℕ) : Prop :=
  a ≠ b ∧ (a = 0 ∨ b = 0 ∨ (a + 1 = b ∧ a % 2 = 1) ∨ (b + 1 = a ∧ b % 2 = 1))

instance : DecidableRel FanAdj := fun a b => by unfold FanAdj; infer_instance

/-- The friendship (windmill) graph `Fₖ`: `k` triangles glued at the centre `0`. -/
def fan (k : ℕ) : SimpleGraph (Fin (2 * k + 1)) where
  Adj a b := FanAdj a.val b.val
  symm := by
    intro a b hab
    unfold FanAdj at hab ⊢
    omega
  loopless := ⟨fun a ha => by unfold FanAdj at ha; omega⟩

instance (k : ℕ) : DecidableRel (fan k).Adj := fun a b =>
  inferInstanceAs (Decidable (FanAdj a.val b.val))




/-- Away from the centre, the friendship graph is a perfect matching: the partner of `a`. -/
def fanPartner {k : ℕ} (a : Fin (2 * k + 1)) : Fin (2 * k + 1) :=
  ⟨if a.val % 2 = 1 then a.val + 1 else a.val - 1, by
    have h := a.isLt
    split_ifs <;> omega⟩







end Fan

section Thickness


end Thickness

end TriangularForest

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


