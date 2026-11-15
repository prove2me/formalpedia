-- Prove2me | Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_HypergraphBundleSourceGoodnessBridge
-- name    : GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_HypergraphBundleSourceGoodnessBridge
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-11-14T09:10:23.878197+00:00
-- url     : https://prove2.me/theorems/6cf89977-f907-48db-9b61-d4dfca0c7ab4
-- title:
--   Reindexing bundle edges into source-good ordered faces
-- statement:
--   A nonempty occurrence edge projects bijectively onto its finite base edge. The bundle provides the increasing enumeration of that projected edge and the resulting equivalence from occurrence-edge assignments to the canonical tuple coordinates of its positive ordered face.
--
--   A proper positive local subface is transported to its ambient face, and the finite strict-face family collects all positive ambient faces properly below a selected face. A local tuple can be extended to a full assignment by retaining the closed configuration's witness on complementary coordinates. Conversely, a projected subset lifts to the occurrence subedge inside a chosen edge by filtering its vertices through the projection. These exact coordinate constructions connect localized source-goodness conditions with bundle-counting inputs.
-- source:
--   https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/Wikipedia/SzemeredisTheorem/Hypergraph/HypergraphBundleSourceGoodnessBridge.lean#L28-L445

import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_OrderedFullBoundary
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_HypergraphBundleConfigurationStep
import Lean
import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fin.Tuple.Finset
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
# Source-full goodness supplies the bundle-localized defect bound

For a maximal nonempty occurrence edge of a closed bundle, projection is a
bijection onto the corresponding base edge.  Consequently its strict
occurrence boundary is just another indexing of all proper subsets of that
base edge.  The product of the configuration indicators on those subsets is
the indicator of the full lower atom used in `OrderedFullBoundary`.

This file makes that reindexing explicit.  It then transports the source-full
localized square estimate along the induced equivalence of tuple spaces.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

namespace HypergraphBundle

variable {G : Type*} [Fintype G] [DecidableEq G]
  {k r : ℕ}

/-! ## Tuple reindexing -/

/-- The canonical enumeration of the projected edge. -/
noncomputable def projectedEdgeOrderIso
    {K : Type*} [Fintype K] [DecidableEq K]
    (B : HypergraphBundle (Fin k) K
      (orderedConfigurationBaseEdges k r))
    {g : Finset K} (hg : g ∈ B.edges)
    (hne : g.Nonempty) :
    Fin ((B.orderedConfigurationBundleFace hg hne).lowerRank.1 + 1) ≃
      {j : Fin k // j ∈ g.image B.projection} := by
  let t := g.image B.projection
  let e := B.orderedConfigurationBundleFace hg hne
  have hcard : t.card = e.lowerRank.1 + 1 := by
    have hedge :
        positiveOrderedFaceEdge e = t := by
      dsimp [e, orderedConfigurationBundleFace, t]
      exact positiveOrderedFaceEdge_ofEdge
        (g.image B.projection)
        (B.projectedEdge_nonempty hg hne)
        (B.projectedEdge_card_le hg)
    calc
      t.card = (positiveOrderedFaceEdge e).card :=
        congrArg Finset.card hedge.symm
      _ = e.rank := positiveOrderedFaceEdge_card e
      _ = e.lowerRank.1 + 1 := rfl
  exact (t.orderIsoOfFin hcard).toEquiv



/-- Reindex occurrence-edge assignments by the increasing enumeration of
their projected base edge. -/
noncomputable def orderedConfigurationBundleFaceTupleEquiv
    {K : Type*} [Fintype K] [DecidableEq K]
    (B : HypergraphBundle (Fin k) K
      (orderedConfigurationBaseEdges k r))
    {g : Finset K} (hg : g ∈ B.edges)
    (hne : g.Nonempty) :
    ({v : K // v ∈ g} → G) ≃
      (Fin ((B.orderedConfigurationBundleFace hg hne).lowerRank.1 + 1) → G) :=
  (Equiv.arrowCongr
      (B.projectionEquiv hg)
      (Equiv.refl G)).trans
    (Equiv.arrowCongr
      (B.projectedEdgeOrderIso hg hne).symm
      (Equiv.refl G))



/-! ## Proper subfaces -/

/-- The positive ambient face obtained from a proper positive local
subface. -/
def ambientPositiveFaceOfProperSubface
    (e : PositiveOrderedFace k r)
    (d : ProperPositiveOrderedSubface e.lowerRank.1) :
    PositiveOrderedFace k r where
  lowerRank :=
    ⟨d.lowerRank.1,
      lt_trans d.lowerRank.2 e.lowerRank.2⟩
  face := orderedFullLowerAmbientFace e d







/-- The finite family of all positive ambient faces strictly below `e`. -/
noncomputable def orderedConfigurationStrictFaceFamily
    (e : PositiveOrderedFace k r) :
    Finset (PositiveOrderedFace k r) :=
  Finset.univ.filter fun f =>
    positiveOrderedFaceEdge f ⊂ positiveOrderedFaceEdge e





/-! ## The full-lower atom as a strict-face product -/

/-- Extend a selected upper-face tuple by the configuration witness on
the complementary coordinates. -/
noncomputable def extendConfigurationFaceTuple
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse)
    (e : PositiveOrderedFace k r)
    (y : Fin (e.lowerRank.1 + 1) → G) :
    Fin k → G :=
  (splitOrderedFaceEquiv e.face).symm
    (y, orderedFaceComplementTuple e.face A.witness)







/-! ## Reindexing a closed bundle boundary -/

/-- Lift a projected subset back to the unique occurrence subedge inside
`g₀`. -/
def liftProjectedSubedge
    {K : Type*} [Fintype K] [DecidableEq K]
    (B : HypergraphBundle (Fin k) K
      (orderedConfigurationBaseEdges k r))
    (g₀ : Finset K) (t : Finset (Fin k)) :
    Finset K :=
  g₀.filter fun v => B.projection v ∈ t







/-! The substantial pointwise identity. -/



/-! ## Transport of the localized estimate -/





end HypergraphBundle

end Wikipedia.SzemeredisTheorem


/- Materialize compiler-generated declarations promised by this bundle. -/
run_meta do
  for requiredName in #[
    `Wikipedia.SzemeredisTheorem.HypergraphBundle.orderedConfigurationStrictFaceFamily.eq_1
  ] do
    let actualName ← Lean.realizeGlobalConstNoOverloadCore requiredName
    unless actualName == requiredName do
      throwError "Generated companion resolved to an unexpected name"


