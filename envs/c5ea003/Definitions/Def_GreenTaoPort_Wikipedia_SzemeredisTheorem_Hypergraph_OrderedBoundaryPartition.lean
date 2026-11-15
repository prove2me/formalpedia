-- Prove2me | Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_OrderedBoundaryPartition
-- name    : GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_OrderedBoundaryPartition
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-11-14T08:59:51.968589+00:00
-- url     : https://prove2.me/theorems/2c4e15a8-b826-453d-beeb-310324fd032a
-- title:
--   Shared immediate-boundary partitions and ordered partition complexes
-- statement:
--   A rank-$j$ ordered face-partition system assigns one finite partition to each ordered $j$-face. For an upper face of rank $j+1$, each immediate subface partition is pulled back by the corresponding coordinate-deletion map. Their common refinement is its shared boundary partition.
--
--   The bundle supplies the boundary atom containing a tuple and the conditional mean of an upper-face function on that boundary. An ordered partition complex records such shared partitions at every rank from zero through a fixed top rank. Refinement is pointwise refinement on every face, both for a single layer and for the full complex.
-- source:
--   https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/Wikipedia/SzemeredisTheorem/Hypergraph/OrderedBoundaryPartition.lean#L23-L403

import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_WeakRegularity
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_OrderedPattern
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_WeakCounting
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Transference_SimplexTelescoping
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_Removal
import Lean
import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
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
# Shared ordered-face partitions and boundary pullbacks

The hypergraph-complex regularity proof uses one genuine partition on every
ordered lower face.  If `e` is an upper face, its boundary partition is not
an independently generated partition of the whole upper tuple space.  It is
the common refinement of the pullbacks of the shared partitions on the
immediate subfaces `eraseOrderedFace e i`.

This file implements that architecture.  Its central membership theorem says
that two upper tuples lie in the same boundary atom exactly when every pair
of erased tuples lies in the same atom of the corresponding genuine lower
face partition.  This is the compatibility needed for closed atom
configurations and localized energy estimates.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

/-- Coordinate deletion specialized to a successor arity.  This
definition has codomain `Fin j → G` on the nose, avoiding transports through
the propositionally equal expression `Fin (j + 1 - 1) → G`. -/
def eraseBoundaryCoordinate
    {G : Type*} {j : ℕ}
    (i : Fin (j + 1)) (x : Fin (j + 1) → G) :
    Fin j → G :=
  fun q => x (i.succAbove q)

/-- Immediate ordered subface specialized to a successor rank. -/
def eraseBoundaryFace
    {k j : ℕ}
    (e : OrderedFace k (j + 1)) (i : Fin (j + 1)) :
    OrderedFace k j :=
  (Fin.succAboveOrderEmb i).trans e



/-- A shared partition on every ordered face of one fixed rank. -/
abbrev OrderedFacePartitionSystem
    (G : Type*) [Fintype G] [DecidableEq G]
    (k j : ℕ) :=
  (e : OrderedFace k j) → FacePartition (Fin j → G)

/-- Pointwise refinement of shared ordered-face partitions. -/
def OrderedFacePartitionRefines
    {G : Type*} [Fintype G] [DecidableEq G]
    {k j : ℕ}
    (fine coarse : OrderedFacePartitionSystem G k j) : Prop :=
  ∀ e, fine e ≤ coarse e

namespace OrderedFacePartitionRefines

theorem refl
    {G : Type*} [Fintype G] [DecidableEq G]
    {k j : ℕ}
    (P : OrderedFacePartitionSystem G k j) :
    OrderedFacePartitionRefines P P :=
  fun _ => le_rfl

theorem trans
    {G : Type*} [Fintype G] [DecidableEq G]
    {k j : ℕ}
    {P Q R : OrderedFacePartitionSystem G k j}
    (hPQ : OrderedFacePartitionRefines P Q)
    (hQR : OrderedFacePartitionRefines Q R) :
    OrderedFacePartitionRefines P R :=
  fun e => le_trans (hPQ e) (hQR e)

end OrderedFacePartitionRefines



/-- Pull one actual lower-face partition back to an upper tuple space. -/
def orderedImmediateBoundaryPartition
    {G : Type*} [Fintype G] [DecidableEq G]
    {k j : ℕ}
    (P : OrderedFacePartitionSystem G k j)
    (e : OrderedFace k (j + 1)) (i : Fin (j + 1)) :
    FacePartition (Fin (j + 1) → G) :=
  FacePartition.pullback (eraseBoundaryCoordinate i)
    (P (eraseBoundaryFace e i))

/-- Common refinement of the pullbacks from every immediate subface. -/
def orderedBoundaryPartition
    {G : Type*} [Fintype G] [DecidableEq G]
    {k j : ℕ}
    (P : OrderedFacePartitionSystem G k j)
    (e : OrderedFace k (j + 1)) :
    FacePartition (Fin (j + 1) → G) :=
  FacePartition.joinFinset
    (Finset.univ : Finset (Fin (j + 1)))
    (orderedImmediateBoundaryPartition P e)

/-- The full boundary partition refines each one-coordinate pullback. -/
theorem orderedBoundaryPartition_le_immediate
    {G : Type*} [Fintype G] [DecidableEq G]
    {k j : ℕ}
    (P : OrderedFacePartitionSystem G k j)
    (e : OrderedFace k (j + 1)) (i : Fin (j + 1)) :
    orderedBoundaryPartition P e ≤
      orderedImmediateBoundaryPartition P e i := by
  exact FacePartition.joinFinset_le_of_mem
    (orderedImmediateBoundaryPartition P e)
    (Finset.mem_univ i)

/-- Refining all genuine lower-face partitions refines every induced
boundary partition. -/
theorem orderedBoundaryPartition_mono
    {G : Type*} [Fintype G] [DecidableEq G]
    {k j : ℕ}
    {fine coarse : OrderedFacePartitionSystem G k j}
    (hfc : OrderedFacePartitionRefines fine coarse)
    (e : OrderedFace k (j + 1)) :
    orderedBoundaryPartition fine e ≤
      orderedBoundaryPartition coarse e := by
  unfold orderedBoundaryPartition
  apply FacePartition.le_joinFinset_iff.mpr
  intro i _
  exact le_trans
    (orderedBoundaryPartition_le_immediate fine e i)
    (FacePartition.pullback_mono (eraseBoundaryCoordinate i)
      (hfc (eraseBoundaryFace e i)))

/-- Exact boundary-atom membership: every erased upper tuple must belong to
the corresponding shared lower-face atom. -/
theorem mem_orderedBoundaryPartition_part_iff
    {G : Type*} [Fintype G] [DecidableEq G]
    {k j : ℕ}
    (P : OrderedFacePartitionSystem G k j)
    (e : OrderedFace k (j + 1))
    (x y : Fin (j + 1) → G) :
    y ∈ (orderedBoundaryPartition P e).part x ↔
      ∀ i : Fin (j + 1),
        eraseBoundaryCoordinate i y ∈
          (P (eraseBoundaryFace e i)).part
            (eraseBoundaryCoordinate i x) := by
  rw [orderedBoundaryPartition,
    FacePartition.mem_part_joinFinset_iff]
  simp only [Finset.mem_univ, forall_const,
    orderedImmediateBoundaryPartition,
    FacePartition.mem_part_pullback_iff_image_mem]









/-- Canonical boundary atom containing an upper tuple. -/
noncomputable def orderedBoundaryAtomAt
    {G : Type*} [Fintype G] [DecidableEq G]
    {k j : ℕ}
    (P : OrderedFacePartitionSystem G k j)
    (e : OrderedFace k (j + 1))
    (x : Fin (j + 1) → G) :
    (orderedBoundaryPartition P e).parts :=
  ⟨(orderedBoundaryPartition P e).part x,
    (orderedBoundaryPartition P e).part_mem.2
      (Finset.mem_univ x)⟩





/-- Conditional mean of an upper-face function relative to its shared
immediate boundary. -/
noncomputable def orderedBoundaryStructured
    {G : Type*} [Fintype G] [DecidableEq G]
    {k j : ℕ}
    (P : OrderedFacePartitionSystem G k j)
    (e : OrderedFace k (j + 1))
    (f : (Fin (j + 1) → G) → ℝ) :
    (Fin (j + 1) → G) → ℝ :=
  conditionalMean (orderedBoundaryPartition P e) f







/-- A bounded hierarchy of shared partitions, one layer for every rank from
zero through `r`. -/
structure OrderedPartitionComplex
    (G : Type*) [Fintype G] [DecidableEq G]
    (k r : ℕ) where
  partition :
    (j : Fin (r + 1)) →
      (e : OrderedFace k j.1) →
        FacePartition (Fin j.1 → G)

namespace OrderedPartitionComplex





/-- Pointwise refinement at every rank of two partition complexes. -/
def Refines
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (fine coarse : OrderedPartitionComplex G k r) : Prop :=
  ∀ j e, fine.partition j e ≤ coarse.partition j e

theorem Refines.refl
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (C : OrderedPartitionComplex G k r) :
    C.Refines C :=
  fun _ _ => le_rfl





end OrderedPartitionComplex

end Wikipedia.SzemeredisTheorem


/- Materialize compiler-generated declarations promised by this bundle. -/
run_meta do
  for requiredName in #[
    `Wikipedia.SzemeredisTheorem.OrderedPartitionComplex.ctorIdx,
    `Wikipedia.SzemeredisTheorem.OrderedPartitionComplex.mk.inj,
    `Wikipedia.SzemeredisTheorem.OrderedPartitionComplex.mk.injEq,
    `Wikipedia.SzemeredisTheorem.OrderedPartitionComplex.mk.sizeOf_spec,
    `Wikipedia.SzemeredisTheorem.OrderedPartitionComplex.noConfusionType,
    `Wikipedia.SzemeredisTheorem.orderedBoundaryPartition.eq_1,
    `Wikipedia.SzemeredisTheorem.orderedImmediateBoundaryPartition.eq_1
  ] do
    let actualName ← Lean.realizeGlobalConstNoOverloadCore requiredName
    unless actualName == requiredName do
      throwError "Generated companion resolved to an unexpected name"


