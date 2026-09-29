-- Prove2me | solution 1 for TriangularForest.triangularThickness_lower_bound_sharp
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-17T12:56:20.765523+00:00
-- url     : https://prove2.me/submissions/be09a654-2851-4d71-8cc3-d7b9d4f053da

-- Sol generated from Logic/TriangularForest/Extremal.lean
import Mathlib
import Definitions.Def_Logic_TriangularForest_Complexity
import Definitions.Def_Logic_TriangularForest_Defs
import Definitions.Def_Logic_TriangularForest_Extremal
import Theorems.Thm_TriangularForest_card_edgeFinset_le_sum_of_cover
import Theorems.Thm_TriangularForest_two_mul_card_edgeFinset_le

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
theorem solution{n k : ℕ} (hn : 2 ≤ n)
    (H : Fin k → SimpleGraph (Fin n)) [∀ i, DecidableRel (H i).Adj]
    (hTF : ∀ i, IsTriangularForest (H i))
    (hcov : ∀ x y : Fin n, x ≠ y → ∃ i, (H i).Adj x y) :
    n ≤ 3 * k := by
  classical
  have hcard : 1 ≤ Fintype.card (Fin n) := by simpa using Nat.one_le_of_lt hn
  have hsum : #(⊤ : SimpleGraph (Fin n)).edgeFinset ≤ ∑ i, #(H i).edgeFinset :=
    card_edgeFinset_le_sum_of_cover _ H fun x y hxy => hcov x y (by simpa using hxy)
  have hbound : ∀ i, 2 * #(H i).edgeFinset ≤ 3 * (n - 1) := fun i => by
    have := two_mul_card_edgeFinset_le (H i) (hTF i) hcard
    simpa using this
  have hsum2 : ∑ i, 2 * #(H i).edgeFinset ≤ ∑ _i : Fin k, (3 * (n - 1)) :=
    Finset.sum_le_sum fun i _ => hbound i
  rw [← Finset.mul_sum] at hsum2
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at hsum2
  have htop : #(⊤ : SimpleGraph (Fin n)).edgeFinset = n.choose 2 := by
    rw [SimpleGraph.card_edgeFinset_top_eq_card_choose_two]
    simp
  have hchoose : 2 * n.choose 2 = n * (n - 1) := by
    obtain ⟨r, hr⟩ := Nat.even_mul_pred_self n
    rw [Nat.choose_two_right, hr]
    omega
  rw [htop] at hsum
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  have hsub : m + 2 - 1 = m + 1 := by omega
  rw [hsub] at hsum2 hchoose
  nlinarith [hsum, hsum2, hchoose]
