-- Prove2me | Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_HypergraphBundleConfigurationBridge
-- name    : GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_HypergraphBundleConfigurationBridge
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-11-14T09:08:14.738205+00:00
-- url     : https://prove2.me/theorems/eda81691-d46a-4ecc-86fc-31ecec863aa6
-- title:
--   Representing closed ordered atom configurations as initial bundles
-- statement:
--   A positive ordered face has an unordered range edge, and every nonempty base edge of cardinality at most the rank bound has its canonical increasing ordered face. The base hypergraph consists of all such edges together with the empty edge. Its initial occurrence bundle uses one vertex per base label and the identity projection.
--
--   Edge tuples are reindexed by their increasing enumeration. A closed atom configuration then gives indicator base weights on the relevant nonempty edges; the empty and irrelevant edges receive weight one. The corresponding base main density is the mixed coarse conditional density at that positive face, again extended by one on neutral edges. This realizes ordered configuration data in the generic bundle interface.
-- source:
--   https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/Wikipedia/SzemeredisTheorem/Hypergraph/HypergraphBundleConfigurationBridge.lean#L28-L485

import Mathlib.Data.Fin.Tuple.Finset
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_CoarseConfigurationCounting
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_HypergraphBundleFiltration
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_HypergraphBundleIndicatorDuplication
import Lean
import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Int.Lemmas
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.Units
import Mathlib.Order.Partition.Finpartition
import Mathlib.RingTheory.Int.Basic
import Mathlib.Tactic
import Mathlib.Topology.ContinuousMap.Weierstrass

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3


/-!
# The ordered configuration as an initial hypergraph bundle

The generalized bundle counting lemma starts from the bundle having one
occurrence vertex above each vertex class.  Its edges are the empty edge
and the ranges of all positive ordered faces.  This file identifies that
initial bundle, its indicator weights, and its main-density product with
the ordered-configuration objects used by the removal argument.

The only small bookkeeping issue is that an ordered face is an increasing
map `Fin n ↪o Fin k`, whereas a bundle edge is a `Finset (Fin k)`.  A
nonempty finite set has a unique increasing enumeration, supplied by
`Finset.orderEmbOfFin`; the equivalence below packages this canonical
change of indices.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

/-! ## Positive ordered faces as nonempty finite edges -/

/-- The (unordered) range edge of a positive ordered face. -/
def positiveOrderedFaceEdge
    {k r : ℕ} (e : PositiveOrderedFace k r) :
    Finset (Fin k) :=
  Finset.univ.map e.face.toEmbedding

@[simp]
theorem positiveOrderedFaceEdge_card
    {k r : ℕ} (e : PositiveOrderedFace k r) :
    (positiveOrderedFaceEdge e).card = e.rank := by
  simp [positiveOrderedFaceEdge, PositiveOrderedFace.rank]



theorem positiveOrderedFaceEdge_card_le
    {k r : ℕ} (e : PositiveOrderedFace k r) :
    (positiveOrderedFaceEdge e).card ≤ r := by
  rw [positiveOrderedFaceEdge_card]
  unfold PositiveOrderedFace.rank
  omega



/-- The positive ordered face obtained by increasingly enumerating a
nonempty edge of cardinality at most `r`. -/
noncomputable def positiveOrderedFaceOfEdge
    {k r : ℕ} (t : Finset (Fin k))
    (ht : t.Nonempty) (htr : t.card ≤ r) :
    PositiveOrderedFace k r := by
  let j : Fin r :=
    ⟨t.card - 1, by
      have htcard : 0 < t.card :=
        Finset.card_pos.mpr ht
      omega⟩
  refine ⟨j, ?_⟩
  have hcard : t.card = j.1 + 1 := by
    dsimp [j]
    have htcard : 0 < t.card :=
      Finset.card_pos.mpr ht
    omega
  exact t.orderEmbOfFin hcard

@[simp]
theorem positiveOrderedFaceEdge_ofEdge
    {k r : ℕ} (t : Finset (Fin k))
    (ht : t.Nonempty) (htr : t.card ≤ r) :
    positiveOrderedFaceEdge
        (positiveOrderedFaceOfEdge t ht htr) = t := by
  dsimp only [positiveOrderedFaceEdge, positiveOrderedFaceOfEdge]
  exact Finset.map_orderEmbOfFin_univ t _









/-! ## The complete initial bundle -/

/-- The base hypergraph consisting of the empty edge and every positive
ordered edge of rank at most `r`. -/
noncomputable def orderedConfigurationBaseEdges
    (k r : ℕ) : Finset (Finset (Fin k)) :=
  insert ∅
    (Finset.univ.image
      (positiveOrderedFaceEdge :
        PositiveOrderedFace k r → Finset (Fin k)))

@[simp]
theorem empty_mem_orderedConfigurationBaseEdges
    (k r : ℕ) :
    ∅ ∈ orderedConfigurationBaseEdges k r := by
  simp [orderedConfigurationBaseEdges]



/-- The explicit edge family is exactly the family of subsets of
cardinality at most `r`. -/
@[simp]
theorem mem_orderedConfigurationBaseEdges_iff
    {k r : ℕ} (t : Finset (Fin k)) :
    t ∈ orderedConfigurationBaseEdges k r ↔
      t.card ≤ r := by
  constructor
  · intro ht
    rw [orderedConfigurationBaseEdges,
      Finset.mem_insert] at ht
    rcases ht with rfl | ht
    · simp
    · obtain ⟨e, _he, rfl⟩ :=
        Finset.mem_image.mp ht
      exact positiveOrderedFaceEdge_card_le e
  · intro htr
    by_cases ht0 : t = ∅
    · subst t
      exact empty_mem_orderedConfigurationBaseEdges k r
    · have ht : t.Nonempty :=
        Finset.nonempty_iff_ne_empty.mpr ht0
      rw [orderedConfigurationBaseEdges,
        Finset.mem_insert]
      right
      apply Finset.mem_image.mpr
      refine
        ⟨positiveOrderedFaceOfEdge t ht htr,
          Finset.mem_univ _, ?_⟩
      exact positiveOrderedFaceEdge_ofEdge t ht htr

/-- The initial bundle has one occurrence vertex above each base vertex
and uses the identity projection. -/
noncomputable def orderedConfigurationInitialBundle
    (k r : ℕ) :
    HypergraphBundle (Fin k) (Fin k)
      (orderedConfigurationBaseEdges k r) where
  edges := orderedConfigurationBaseEdges k r
  projection := id
  projection_injective_on_edge := by
    intro g hg x hx y hy hxy
    exact hxy
  projection_mem_base := by
    intro g hg
    simpa using hg







/-! ## Canonical local tuples and base weights -/

/-- Reindex a tuple on a nonempty finite edge by its increasing
enumeration. -/
noncomputable def orderedConfigurationEdgeTuple
    {G : Type*} {k r : ℕ}
    (t : Finset (Fin k))
    (ht : t.Nonempty) (htr : t.card ≤ r)
    (y : {v : Fin k // v ∈ t} → G) :
    Fin ((positiveOrderedFaceOfEdge t ht htr).lowerRank.1 + 1) → G := by
  let e := positiveOrderedFaceOfEdge t ht htr
  have hcard : t.card = e.lowerRank.1 + 1 := by
    dsimp [e, positiveOrderedFaceOfEdge]
    have htcard : 0 < t.card :=
      Finset.card_pos.mpr ht
    omega
  exact fun i => y (t.orderIsoOfFin hcard i)



/-- Indicator base weights corresponding to a closed ordered atom
configuration.  The empty edge and irrelevant edges carry weight one. -/
noncomputable def orderedConfigurationBaseWeight
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    {C : OrderedPartitionComplex G k r}
    (A : ClosedOrderedAtomConfiguration G k r C) :
    HypergraphBundle.BaseEdgeWeight (Fin k) G := by
  classical
  intro t y
  by_cases ht : t.Nonempty
  · by_cases htr : t.card ≤ r
    · exact configurationFaceWeight A
        (positiveOrderedFaceOfEdge t ht htr)
        (orderedConfigurationEdgeTuple t ht htr y)
    · exact 1
  · exact 1









/-! ## Main densities -/

/-- The base main density attached to a mixed coarse configuration.  As
for the weight, the empty and irrelevant edges carry the neutral value
one. -/
noncomputable def orderedConfigurationBaseDensity
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse) :
    Finset (Fin k) → ℝ := by
  classical
  intro t
  by_cases ht : t.Nonempty
  · by_cases htr : t.card ≤ r
    · exact mixedConfigurationCoarseDensity P A
        (positiveOrderedFaceOfEdge t ht htr)
    · exact 1
  · exact 1







/-! ## Exact initial count and product identities -/













end Wikipedia.SzemeredisTheorem


/- Materialize compiler-generated declarations promised by this bundle. -/
run_meta do
  for requiredName in #[
    `Wikipedia.SzemeredisTheorem.orderedConfigurationBaseDensity.eq_1,
    `Wikipedia.SzemeredisTheorem.orderedConfigurationBaseEdges.eq_1,
    `Wikipedia.SzemeredisTheorem.orderedConfigurationBaseWeight.eq_1,
    `Wikipedia.SzemeredisTheorem.positiveOrderedFaceEdge.eq_1,
    `Wikipedia.SzemeredisTheorem.positiveOrderedFaceOfEdge.congr_simp
  ] do
    let actualName ← Lean.realizeGlobalConstNoOverloadCore requiredName
    unless actualName == requiredName do
      throwError "Generated companion resolved to an unexpected name"


