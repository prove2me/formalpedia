-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.exists_uniformDenseAPCount_of_simplexRemoval
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T10:56:24.30995+00:00
-- url     : https://prove2.me/submissions/7a67e4d2-a217-4e5d-89b9-7ad3f0ce72f2

/- Mechanically transplanted from https://github.com/plby/lean-proofs.git at 8822f7ddef30fadbd92e1c6ab4ed897af356af5e. Original scopes and proof bytes are oracle-derived. -/
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_ArithmeticProgression_Count
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Finite_Mean
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_APCorrespondence
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_APRemoval
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_ConditionalAverage
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_Energy
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_FacePartition
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_Removal
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_Simplex
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_Unweighted
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_LinearForms_Basic
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Szemeredi_Weighted
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Transference_APCut
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Transference_CutDiscrepancy
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Transference_CutTransport
import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Int.Lemmas
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.Units
import Mathlib.Order.Partition.Finpartition
import Mathlib.RingTheory.Int.Basic
import Mathlib.Tactic
import Theorems.Thm_Wikipedia_SzemeredisTheorem_apSimplexSystem_simplexCount_eq_cyclicAPCount
import Theorems.Thm_Wikipedia_SzemeredisTheorem_mean_finsetIndicator_div_le_normalizedDeletionCost

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3

section


/-!
# Unweighted partite simplex hypergraphs

The removal argument uses a `(k - 1)`-uniform, `k`-partite hypergraph whose
edge of colour `j` depends on every vertex coordinate except `j`.  This file
gives the finite predicate-valued interface and connects its labelled
simplices exactly to the weighted counting API.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators



namespace SimplexHypergraph











@[simp]
theorem toWeighted_edgeWeight_of_edge {k : ℕ}
    {V : Fin k → Type*} (H : SimplexHypergraph V)
    {j : Fin k} {x : DeletedVector V j}
    (hx : H.edge j x) :
    H.toWeighted.edgeWeight j x = 1 := by
  classical
  simp [toWeighted, hx]

@[simp]
theorem toWeighted_edgeWeight_of_not_edge {k : ℕ}
    {V : Fin k → Type*} (H : SimplexHypergraph V)
    {j : Fin k} {x : DeletedVector V j}
    (hx : ¬H.edge j x) :
    H.toWeighted.edgeWeight j x = 0 := by
  classical
  simp [toWeighted, hx]













end SimplexHypergraph

end Wikipedia.SzemeredisTheorem

end

section





/-!
# From partite simplex removal to dense arithmetic progressions

For a finite set `A ⊆ ZMod N`, its arithmetic-progression hypergraph has
one edge of colour `j` whenever the `j`th AP form belongs to `A`.  The
degenerate progressions of common difference zero give a large,
edge-disjoint family of labelled simplices.  Consequently every simplex
cover has normalized deletion cost at least `mean (1_A) / k`.

This is the elementary half of the standard deduction of dense
Szemerédi from the partite simplex-removal lemma.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators





/-- The zero-one weight of the AP-set hypergraph is exactly the set
indicator evaluated on the corresponding AP form. -/
@[simp]
theorem apSetHypergraph_toWeighted_edgeWeight
    (k N : ℕ) (A : Finset (ZMod N))
    (j : Fin k)
    (x : DeletedVector (fun _ : Fin k => ZMod N) j) :
    (apSetHypergraph k N A).toWeighted.edgeWeight j x =
      finsetIndicator A (apSimplexForm k N j x) := by
  classical
  by_cases hx : apSimplexForm k N j x ∈ A
  · rw [SimplexHypergraph.toWeighted_edgeWeight_of_edge]
    · exact (finsetIndicator_of_mem hx).symm
    · exact hx
  · rw [SimplexHypergraph.toWeighted_edgeWeight_of_not_edge]
    · exact (finsetIndicator_of_not_mem hx).symm
    · exact hx

/-- The labelled simplex density of the AP-set hypergraph is its normalized
cyclic arithmetic-progression count. -/
theorem apSetHypergraph_simplexCount_eq_cyclicAPCount
    (r N : ℕ) [NeZero N] (A : Finset (ZMod N)) :
    (apSetHypergraph (r + 2) N A).toWeighted.simplexCount =
      cyclicAPCount (r + 2) N (finsetIndicator A) := by
  rw [← apSimplexSystem_simplexCount_eq_cyclicAPCount
    r N (finsetIndicator A)]
  simp only [WeightedSimplexSystem.simplexCount]
  apply congrArg mean
  funext x
  apply Finset.prod_congr rfl
  intro j _
  exact apSetHypergraph_toWeighted_edgeWeight
    (r + 2) N A j (deleteCoordinate x j)





















namespace SimplexHypergraph







end SimplexHypergraph

























end Wikipedia.SzemeredisTheorem

end
/-!
# From partite simplex removal to dense arithmetic progressions

For a finite set `A ⊆ ZMod N`, its arithmetic-progression hypergraph has
one edge of colour `j` whenever the `j`th AP form belongs to `A`.  The
degenerate progressions of common difference zero give a large,
edge-disjoint family of labelled simplices.  Consequently every simplex
cover has normalized deletion cost at least `mean (1_A) / k`.

This is the elementary half of the standard deduction of dense
Szemerédi from the partite simplex-removal lemma.
-/
open Wikipedia.SzemeredisTheorem
open scoped BigOperators

open Wikipedia.SzemeredisTheorem in
/-- Uniform partite simplex removal implies a uniform quantitative dense
Szemerédi theorem.  The proof is the standard contrapositive: a set whose AP
hypergraph has too few simplices admits a cheap cover, while the
edge-disjoint degenerate simplices force every cover to cost at least
`density / k`. -/
theorem solution
    (r : ℕ)
    (hrem :
      HasUniformCyclicPartiteSimplexRemoval (r + 2))
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ c : ℝ, 0 < c ∧
      HasUniformDenseAPCount (r + 2) δ c := by
  let ε : ℝ := (δ / (r + 2 : ℝ)) / 2
  have hk : 0 < (r + 2 : ℝ) := by positivity
  have hbase : 0 < δ / (r + 2 : ℝ) :=
    div_pos hδ hk
  have hε : 0 < ε := by
    exact div_pos hbase (by norm_num)
  obtain ⟨c, hc, hremove⟩ := hrem ε hε
  refine ⟨c, hc, ?_⟩
  intro N inst A hA
  by_contra hcount
  have hcount_lt :
      cyclicAPCount (r + 2) N (finsetIndicator A) < c :=
    lt_of_not_ge hcount
  have hsimplex_lt :
      (apSetHypergraph (r + 2) N A).toWeighted.simplexCount <
        c := by
    simpa [apSetHypergraph_simplexCount_eq_cyclicAPCount]
      using hcount_lt
  obtain ⟨deleted, hcover, hcost⟩ :=
    hremove N (apSetHypergraph (r + 2) N A) hsimplex_lt
  have hlower :
      mean (finsetIndicator A) / (r + 2 : ℝ) ≤
        SimplexHypergraph.normalizedDeletionCost deleted :=
    mean_finsetIndicator_div_le_normalizedDeletionCost
      r N A deleted hcover
  have hdensity :
      δ / (r + 2 : ℝ) ≤
        mean (finsetIndicator A) / (r + 2 : ℝ) :=
    div_le_div_of_nonneg_right hA hk.le
  have hε_lt : ε < δ / (r + 2 : ℝ) := by
    dsimp [ε]
    linarith
  linarith
