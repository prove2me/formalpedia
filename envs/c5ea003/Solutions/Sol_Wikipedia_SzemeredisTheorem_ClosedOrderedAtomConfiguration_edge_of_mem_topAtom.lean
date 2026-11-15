-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.ClosedOrderedAtomConfiguration.edge_of_mem_topAtom
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T10:36:30.776613+00:00
-- url     : https://prove2.me/submissions/9d688572-d401-461e-8e0e-35a71eee6fd3

/- Mechanically transplanted from https://github.com/plby/lean-proofs.git at 8822f7ddef30fadbd92e1c6ab4ed897af356af5e. Original scopes and proof bytes are oracle-derived. -/
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_ArithmeticProgression_Count
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Finite_Mean
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_APCorrespondence
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_ConditionalAverage
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_Energy
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_FacePartition
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_FullOrderedRegularity
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_OrderedAtomEnergy
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_OrderedBoundaryPartition
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_OrderedGoodAtoms
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_OrderedPattern
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_OrderedPatternPartition
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_PreliminaryOrderedRegularity
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_Regularity
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_Removal
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_Simplex
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_Unweighted
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_WeakCounting
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_WeakRegularity
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_LinearForms_Basic
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Transference_APCut
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Transference_BooleanCutReduction
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Transference_CutDiscrepancy
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Transference_CutTransport
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Transference_DenseModel
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Transference_GeneralizedConvolution
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Transference_PolynomialApproximation
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Transference_SimplexCounting
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Transference_SimplexTelescoping
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

section



/-!
# Ordered pattern edge partitions

The top layer used in ordered removal must remember the original
hypergraph.  For every top face we therefore generate a two-cell partition
from its edge set.  Any later refinement of that layer has atoms which are
monochromatic for the original edge predicate.

The lower layers of `orderedPatternInitialComplex` are indiscrete.  This is
the canonical starting complex for the all-rank regularity argument.
-/

namespace Wikipedia.SzemeredisTheorem

/-! ## Edge supports and their two-cell partitions -/



@[simp]
theorem OrderedPattern.mem_edgeFinset
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ} (H : OrderedPattern G k r)
    (e : OrderedFace k r) (y : Fin r → G) :
    y ∈ H.edgeFinset e ↔ H.edge e y := by
  simp [OrderedPattern.edgeFinset]





/-- Membership in an atom of a refinement of a two-cell partition
preserves membership in its generating set. -/
theorem mem_of_mem_part_of_le_generatedBy_singleton
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    {P : FacePartition Ω} {S : Finset Ω}
    (hP : P ≤ FacePartition.generatedBy
      ({S} : Finset (Finset Ω)))
    {x y : Ω} (hx : x ∈ S) (hy : y ∈ P.part x) :
    y ∈ S := by
  have hyGenerated :
      y ∈
        (FacePartition.generatedBy
          ({S} : Finset (Finset Ω))).part x :=
    FacePartition.part_subset_of_le hP x hy
  have hsignature :=
    (FacePartition.mem_part_generatedBy_iff
      ({S} : Finset (Finset Ω)) x y).1 hyGenerated
  exact (hsignature S (by simp)).1 hx

/-- A refinement of the pattern top partition cannot move an edge tuple
into a nonedge within the same atom. -/
theorem orderedPattern_edge_of_mem_refinedTopAtom
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ} (H : OrderedPattern G k r)
    {P : OrderedFacePartitionSystem G k r}
    (hP : OrderedFacePartitionRefines P
      (orderedPatternTopPartition H))
    (e : OrderedFace k r) {x y : Fin r → G}
    (hx : H.edge e x) (hy : y ∈ (P e).part x) :
    H.edge e y := by
  rw [← H.mem_edgeFinset e y]
  exact
    mem_of_mem_part_of_le_generatedBy_singleton
      (hP e)
      ((H.mem_edgeFinset e x).2 hx) hy

/-! ## Canonical initial complex -/









/-! ## Closed configurations contained in the original pattern -/





end Wikipedia.SzemeredisTheorem

end
/-!
# Ordered pattern edge partitions

The top layer used in ordered removal must remember the original
hypergraph.  For every top face we therefore generate a two-cell partition
from its edge set.  Any later refinement of that layer has atoms which are
monochromatic for the original edge predicate.

The lower layers of `orderedPatternInitialComplex` are indiscrete.  This is
the canonical starting complex for the all-rank regularity argument.
-/
open Wikipedia.SzemeredisTheorem
/-! ## Edge supports and their two-cell partitions -/
/-! ## Canonical initial complex -/
/-! ## Closed configurations contained in the original pattern -/

open Wikipedia.SzemeredisTheorem.ClosedOrderedAtomConfiguration in
/-- If the witness of a closed configuration is an occurrence, then every
tuple in each of its selected top atoms remains an edge. -/
theorem solution
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ} (H : OrderedPattern G k r)
    {C : OrderedPartitionComplex G k r}
    (hC : OrderedFacePartitionRefines C.topLayer
      (orderedPatternTopPartition H))
    (A : ClosedOrderedAtomConfiguration G k r C)
    (hA : H.IsOccurrence A.witness)
    (e : OrderedFace k r) (y : Fin r → G)
    (hy : y ∈ (A.atom (Fin.last r) e).1) :
    H.edge e y := by
  apply
    orderedPattern_edge_of_mem_refinedTopAtom
      H hC e (hA e)
  have hw :
      orderedFaceTuple e A.witness ∈
        (A.atom (Fin.last r) e).1 :=
    A.mem_atom (Fin.last r) e
  have hpart :
      (C.topLayer e).part
          (orderedFaceTuple e A.witness) =
        (A.atom (Fin.last r) e).1 := by
    exact
      (C.topLayer e).part_eq_of_mem
        (A.atom (Fin.last r) e).2 hw
  rwa [hpart]
