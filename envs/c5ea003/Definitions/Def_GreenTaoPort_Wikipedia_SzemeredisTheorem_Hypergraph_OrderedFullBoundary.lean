-- Prove2me | Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_OrderedFullBoundary
-- name    : GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_OrderedFullBoundary
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-11-14T09:08:42.601388+00:00
-- url     : https://prove2.me/theorems/826acc6c-1081-482a-9309-90732337f963
-- title:
--   Full lower-boundary localization and source mixed goodness
-- statement:
--   For a positive ordered face, the full positive lower partition is the common refinement of the pullbacks from all nonempty proper ordered subfaces. The full lower-boundary partition also explicitly joins the immediate boundary, retaining the rank-zero boundary contribution at rank one.
--
--   The bundle supplies the selected full-lower atom and its indicator. For a coarse/fine complex and a closed coarse atom configuration, the density term remains the immediate coarse-boundary conditional density at the configuration witness, and the defect remains the immediate fine-density function minus that fixed coarse density.
--
--   Source mixed goodness at a face requires a coarse density floor $\alpha$ and a conditional mean-square defect at most $\beta$ on the selected full-lower coarse atom. The all-face version uses rank-dependent thresholds. A separate quantity is the global square-defect mass multiplied by that atom's indicator. The extra full-boundary conditioning localizes the defect without changing the underlying density decomposition.
-- source:
--   https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/Wikipedia/SzemeredisTheorem/Hypergraph/OrderedFullBoundary.lean#L28-L588

import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_CoarseConfigurationCounting
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
# Full lower boundaries of ordered faces

The source hypergraph regularity argument conditions an upper face on the
join of the partitions carried by *all* of its nonempty proper subfaces.
The adjacent-rank boundary in `OrderedBoundaryPartition` is enough to encode
closedness, but it does not expose this source-level sigma algebra directly.

This file constructs that full lower boundary.  A proper positive subface of
an `n + 1` tuple is represented by a positive ordered face of that tuple
whose rank is at most `n`.  Each genuine partition in the ambient ordered
complex is pulled back to the selected upper tuple space, and the full lower
boundary is their finite common refinement.

The last section packages the coarse/fine defect and the corresponding
source mixed-goodness condition.  Its principal consequence is the localized
weighted square-defect estimate on the selected full-lower atom.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

/-! ## Proper positive subfaces -/

/-- Every nonempty proper ordered subface of an `n + 1` tuple.

The `lowerRank` field of `PositiveOrderedFace (n + 1) n` ranges over
`0, ..., n - 1`, so its actual rank ranges over `1, ..., n`. -/
abbrev ProperPositiveOrderedSubface (n : ℕ) :=
  PositiveOrderedFace (n + 1) n

@[simp]
theorem properPositiveOrderedSubface_rank_lt_upper {n : ℕ}
    (d : ProperPositiveOrderedSubface n) :
    d.rank < n + 1 := by
  simp only [PositiveOrderedFace.rank]
  exact Nat.succ_lt_succ d.lowerRank.2

/-! ## The full lower partition -/

/-- The layer of the ambient complex carrying a proper positive subface. -/
abbrev orderedFullLowerComplexRank
    {k r : ℕ}
    (e : PositiveOrderedFace k r)
    (d : ProperPositiveOrderedSubface e.lowerRank.1) :
    Fin (r + 1) :=
  ⟨d.lowerRank.1 + 1, by
    have hd : d.rank < e.rank := by
      exact properPositiveOrderedSubface_rank_lt_upper d
    have he : e.rank ≤ r := by
      simp only [PositiveOrderedFace.rank]
      exact e.lowerRank.2
    omega⟩



/-- A local proper subface, transported into the ambient labelled face. -/
abbrev orderedFullLowerAmbientFace
    {k r : ℕ}
    (e : PositiveOrderedFace k r)
    (d : ProperPositiveOrderedSubface e.lowerRank.1) :
    OrderedFace k (d.lowerRank.1 + 1) :=
  d.face.trans e.face



/-- Pull the genuine partition on one proper ambient subface back to the
selected upper tuple space. -/
noncomputable def orderedFullLowerConstituentPartition
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (C : OrderedPartitionComplex G k r)
    (e : PositiveOrderedFace k r)
    (d : ProperPositiveOrderedSubface e.lowerRank.1) :
    FacePartition (Fin (e.lowerRank.1 + 1) → G) :=
  FacePartition.pullback
    (orderedFaceTuple d.face)
    (C.partition
      (orderedFullLowerComplexRank e d)
      (orderedFullLowerAmbientFace e d))

/-- Common refinement of the pullbacks from every nonempty proper ordered
subface. -/
noncomputable def orderedFullLowerPositivePartition
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (C : OrderedPartitionComplex G k r)
    (e : PositiveOrderedFace k r) :
    FacePartition (Fin (e.lowerRank.1 + 1) → G) :=
  FacePartition.joinFinset
    (Finset.univ :
      Finset (ProperPositiveOrderedSubface e.lowerRank.1))
    (orderedFullLowerConstituentPartition C e)





/-- The source-faithful full lower boundary.  We explicitly join the
ordinary immediate boundary with the positive strict-subface join.  For
rank greater than one the immediate constituents already occur in the
positive join; for rank one the immediate rank-zero face space is a
singleton.  Keeping this harmless factor explicit makes the refinement to
the boundary used by the counting decomposition definitional. -/
noncomputable def orderedFullLowerBoundaryPartition
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (C : OrderedPartitionComplex G k r)
    (e : PositiveOrderedFace k r) :
    FacePartition (Fin (e.lowerRank.1 + 1) → G) :=
  FacePartition.join
    (orderedBoundaryPartition
      (positiveFaceLowerLayer C e) e.face)
    (orderedFullLowerPositivePartition C e)













/-! ## Selected full-lower atoms and their weights -/

/-- Canonical full-lower atom containing a selected upper tuple. -/
noncomputable def orderedFullLowerBoundaryAtomAt
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (C : OrderedPartitionComplex G k r)
    (e : PositiveOrderedFace k r)
    (x : Fin (e.lowerRank.1 + 1) → G) :
    (orderedFullLowerBoundaryPartition C e).parts :=
  partitionAtomAt (orderedFullLowerBoundaryPartition C e) x



/-- Indicator of the full-lower atom selected by `x`. -/
noncomputable def orderedFullLowerBoundaryWeight
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (C : OrderedPartitionComplex G k r)
    (e : PositiveOrderedFace k r)
    (x y : Fin (e.lowerRank.1 + 1) → G) : ℝ :=
  partitionAtomIndicator
    (orderedFullLowerBoundaryPartition C e)
    (orderedFullLowerBoundaryAtomAt C e x)
    y















/-! ## Source full-lower goodness -/



/-- The source density term is the existing immediate-boundary coarse
conditional density.  The full lower boundary is used to localize its
fine--coarse defect, not to alter the three-term counting decomposition. -/
noncomputable def sourceFullMixedCoarseDensity
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse)
    (e : PositiveOrderedFace k r) : ℝ :=
  mixedConfigurationCoarseDensity P A e

/-- The defect in the source-goodness test is the existing immediate
fine-boundary density minus immediate coarse-boundary density.  Conditioning
its square on the full strict lower atom is the extra source-faithful
localization. -/
noncomputable def sourceFullMixedDefect
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse)
    (e : PositiveOrderedFace k r)
    (y : Fin (e.lowerRank.1 + 1) → G) : ℝ :=
  mixedConfigurationDefect P A e y

/-- The coarse full-lower atom selected by a closed configuration. -/
noncomputable def sourceFullMixedBoundaryWeight
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse)
    (e : PositiveOrderedFace k r)
    (y : Fin (e.lowerRank.1 + 1) → G) : ℝ :=
  orderedFullLowerBoundaryWeight P.coarse e
    (orderedFaceTuple e.face A.witness) y





/-- Source mixed goodness at one positive face.  The first clause is the
coarse density floor.  The second is the conditional square average of the
fine--coarse defect on the selected full-lower coarse atom. -/
def SourceFullMixedGoodAtFace
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse)
    (e : PositiveOrderedFace k r)
    (α β : ℝ) : Prop :=
  α ≤ sourceFullMixedCoarseDensity P A e ∧
    conditionalMean
        (orderedFullLowerBoundaryPartition P.coarse e)
        (fun y => sourceFullMixedDefect P A e y ^ 2)
        (orderedFaceTuple e.face A.witness) ≤
      β

/-- Source mixed goodness simultaneously at every positive ordered face. -/
def ClosedOrderedAtomConfiguration.IsSourceFullMixedGood
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse)
    (α β : ℕ → ℝ) : Prop :=
  ∀ e : PositiveOrderedFace k r,
    SourceFullMixedGoodAtFace P A e
      (α e.rank) (β e.rank)

/-- The global square-defect mass localized by the selected full-lower
coarse atom. -/
noncomputable def sourceFullMixedLocalizedDefectSq
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse)
    (e : PositiveOrderedFace k r) : ℝ :=
  mean fun y =>
    sourceFullMixedDefect P A e y ^ 2 *
      sourceFullMixedBoundaryWeight P A e y





end Wikipedia.SzemeredisTheorem


/- Materialize compiler-generated declarations promised by this bundle. -/
run_meta do
  for requiredName in #[
    `Wikipedia.SzemeredisTheorem.orderedFullLowerBoundaryPartition.eq_1,
    `Wikipedia.SzemeredisTheorem.orderedFullLowerConstituentPartition.eq_1,
    `Wikipedia.SzemeredisTheorem.orderedFullLowerPositivePartition.eq_1
  ] do
    let actualName ← Lean.realizeGlobalConstNoOverloadCore requiredName
    unless actualName == requiredName do
      throwError "Generated companion resolved to an unexpected name"


