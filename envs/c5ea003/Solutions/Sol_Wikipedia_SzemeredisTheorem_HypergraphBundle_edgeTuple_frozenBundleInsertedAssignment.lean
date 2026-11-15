-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.HypergraphBundle.edgeTuple_frozenBundleInsertedAssignment
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T10:40:00.794685+00:00
-- url     : https://prove2.me/submissions/c67ed5a0-90e0-4072-8f26-71e471521504

/- Mechanically transplanted from https://github.com/plby/lean-proofs.git at 8822f7ddef30fadbd92e1c6ab4ed897af356af5e. Original scopes and proof bytes are oracle-derived. -/
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_ArithmeticProgression_Count
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Finite_Mean
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_APCorrespondence
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_BoundaryBernoulli
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_CoarseAtomBridge
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_CoarseConfigurationCounting
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_ConditionalAverage
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_Energy
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_FacePartition
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_FullOrderedRegularity
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_HypergraphBundleConfigurationBridge
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_HypergraphBundleConfigurationStep
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_HypergraphBundleCounting
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_HypergraphBundleDuplication
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_HypergraphBundleFiltration
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_HypergraphBundleFrozenCut
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_HypergraphBundleFrozenUniformity
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_HypergraphBundleGeneralizedCounting
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_HypergraphBundleIndicatorDuplication
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_HypergraphBundleRelativeCounting
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_OrderedAtomEnergy
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_OrderedBoundaryPartition
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_OrderedConfigurationCounting
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_OrderedGoodAtoms
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_OrderedPattern
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_OrderedRemoval
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

section



/-!
# Hypergraph bundles and the counting-lemma decomposition

Tao's hypergraph counting lemma is proved after passing from one copy of
each vertex class to a *hypergraph bundle*.  A bundle has a finite set of
occurrence vertices, a finite family of occurrence edges, and a projection
to the base vertex classes which is injective on every occurrence edge.
The extra occurrence vertices record the copies created by repeated
Cauchy--Schwarz.

This file supplies the finite bundle object and the exact analytic
identities at one step of the double induction.  For a selected edge `g₀`,
the bundle count is split according to

```
edgeWeight = main + defect + uniform.
```

The uniform contribution is rewritten by freezing all variables outside
`g₀`.  The defect contribution is bounded by Cauchy--Schwarz; the second
factor is written exactly as an average with two independent copies of the
outside variables.  This is the doubled lower-rank bundle appearing in
Tao's proof.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators



namespace HypergraphBundle

variable {J K G : Type*}
  [DecidableEq J] [DecidableEq K]
  {H : Finset (Finset J)}



















/-! ## Local tuples and pulled-back base weights -/

















/-! ## Bundle products and normalized counts -/





























/-! ## Freezing the outside variables -/







@[simp]
theorem splitEdgeEquiv_fst
    (g : Finset K) (x : K → G) :
    (splitEdgeEquiv g x).1 = edgeTuple g x := by
  funext v
  simp [splitEdgeEquiv, edgeSumEquiv, edgeTuple]

/-- Recombining a selected-edge tuple and an outside tuple recovers the
selected-edge tuple on restriction. -/
@[simp]
theorem edgeTuple_splitEdgeEquiv_symm
    (g : Finset K)
    (y : {v : K // v ∈ g} → G)
    (z : EdgeComplement g → G) :
    edgeTuple g ((splitEdgeEquiv g).symm (y, z)) = y := by
  rw [← splitEdgeEquiv_fst]
  simp















/-! ## Localized Cauchy--Schwarz and the doubled remainder -/

















end HypergraphBundle

end Wikipedia.SzemeredisTheorem

end

section


/-!
# Frozen bundle remainders are face cuts

Fix a maximum-cardinality nonempty occurrence edge `g₀`.  Every other
occurrence edge omits a vertex of `g₀`; we assign that edge to the
corresponding coordinate in the increasing enumeration of the projected
edge.  After the variables outside `g₀` are frozen, factors with the same
assigned coordinate form one member of a face-cut family.

The construction groups *occurrence* edges, rather than projected faces.
This is important because distinct occurrence edges in a bundle may have
the same projection.  The resulting product therefore retains every
factor with its correct multiplicity.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

namespace HypergraphBundle

variable {G : Type*} [Fintype G] [DecidableEq G]
  {k r : ℕ}

/-! ## The canonical occurrence-edge ordering -/









omit [Fintype G] [DecidableEq G] in
@[simp]
theorem frozenBundleFaceTupleEquiv_symm_apply
    {K : Type*} [Fintype K] [DecidableEq K]
    (B : HypergraphBundle (Fin k) K
      (orderedConfigurationBaseEdges k r))
    {g : Finset K} (hg : g ∈ B.edges)
    (hne : g.Nonempty)
    (x :
      Fin ((B.orderedConfigurationBundleFace hg hne).lowerRank.1 + 1) →
        G)
    (v : {v : K // v ∈ g}) :
    (B.frozenBundleFaceTupleEquiv hg hne).symm x v =
      x ((B.frozenOccurrenceOrderEquiv hg hne).symm v) := by
  rfl

/-! ## Assigning each remainder edge to a missing coordinate -/



theorem frozenBundleMissingVertex_not_mem
    {K : Type*} [Fintype K] [DecidableEq K]
    (B : HypergraphBundle (Fin k) K
      (orderedConfigurationBaseEdges k r))
    {g₀ g : Finset K}
    (hmax : ∀ f ∈ B.edges, f.card ≤ g₀.card)
    (hne : g₀.Nonempty)
    (hg : g ∈ B.edges.erase g₀) :
    (B.frozenBundleMissingVertex hmax hne g).1 ∉ g := by
  classical
  simp only [frozenBundleMissingVertex, dif_pos hg]
  exact
    (Classical.choose_spec
      (B.exists_selectedVertex_not_mem_of_mem_erase hg hmax)).2





/-! ## Reconstructing and grouping a frozen remainder -/





omit [Fintype G] [DecidableEq G] in
theorem splitEdgeEquiv_symm_apply_of_mem
    {K : Type*} [DecidableEq K]
    (g₀ : Finset K)
    (y : {v : K // v ∈ g₀} → G)
    (z : EdgeComplement g₀ → G)
    {v : K} (hv : v ∈ g₀) :
    (splitEdgeEquiv g₀).symm (y, z) v = y ⟨v, hv⟩ := by
  have h :=
    congrFun (edgeTuple_splitEdgeEquiv_symm g₀ y z) ⟨v, hv⟩
  exact h

omit [Fintype G] [DecidableEq G] in
theorem splitEdgeEquiv_symm_apply_of_not_mem
    {K : Type*} [DecidableEq K]
    (g₀ : Finset K)
    (y : {v : K // v ∈ g₀} → G)
    (z : EdgeComplement g₀ → G)
    {v : K} (hv : v ∉ g₀) :
    (splitEdgeEquiv g₀).symm (y, z) v = z ⟨v, hv⟩ := by
  unfold splitEdgeEquiv
  convert
    Equiv.piCongrLeft_sumInr
      (fun _ : K => G) (edgeSumEquiv g₀)
      y z ⟨v, hv⟩ using 1









/-! ## Exact correlation transport -/



end HypergraphBundle

end Wikipedia.SzemeredisTheorem

end
/-!
# Frozen bundle remainders are face cuts

Fix a maximum-cardinality nonempty occurrence edge `g₀`.  Every other
occurrence edge omits a vertex of `g₀`; we assign that edge to the
corresponding coordinate in the increasing enumeration of the projected
edge.  After the variables outside `g₀` are frozen, factors with the same
assigned coordinate form one member of a face-cut family.

The construction groups *occurrence* edges, rather than projected faces.
This is important because distinct occurrence edges in a bundle may have
the same projection.  The resulting product therefore retains every
factor with its correct multiplicity.
-/
open Wikipedia.SzemeredisTheorem
open scoped BigOperators
open Wikipedia.SzemeredisTheorem.HypergraphBundle
variable {G : Type*} [Fintype G] [DecidableEq G]
  {k r : ℕ}
/-! ## The canonical occurrence-edge ordering -/
/-! ## Assigning each remainder edge to a missing coordinate -/
/-! ## Reconstructing and grouping a frozen remainder -/

open Wikipedia.SzemeredisTheorem.HypergraphBundle in
omit [Fintype G] [DecidableEq G] in
/-- Replacing the coordinate assigned to `g` does not alter the tuple
seen by `g`, since that occurrence edge omits the assigned vertex. -/
theorem solution
    {K : Type*} [Fintype K] [DecidableEq K]
    (B : HypergraphBundle (Fin k) K
      (orderedConfigurationBaseEdges k r))
    {g₀ g : Finset K} (hg₀ : g₀ ∈ B.edges)
    (hmax : ∀ f ∈ B.edges, f.card ≤ g₀.card)
    (hne : g₀.Nonempty)
    (hg : g ∈ B.edges.erase g₀)
    (a : G)
    (x :
      Fin ((B.orderedConfigurationBundleFace hg₀ hne).lowerRank.1 + 1) →
        G)
    (z : EdgeComplement g₀ → G) :
    edgeTuple g
        (B.frozenBundleInsertedAssignment hg₀ hne
          (B.frozenBundleMissingCoordinate hg₀ hmax hne g)
          a
          (Fin.removeNth
            (B.frozenBundleMissingCoordinate hg₀ hmax hne g) x)
          z) =
      edgeTuple g
        ((splitEdgeEquiv g₀).symm
          ((B.frozenBundleFaceTupleEquiv hg₀ hne).symm x, z)) := by
  classical
  funext w
  unfold edgeTuple
  let i :=
    B.frozenBundleMissingCoordinate hg₀ hmax hne g
  by_cases hw₀ : w.1 ∈ g₀
  · unfold frozenBundleInsertedAssignment
    rw [splitEdgeEquiv_symm_apply_of_mem g₀ _ _ hw₀]
    rw [splitEdgeEquiv_symm_apply_of_mem g₀ _ _ hw₀]
    unfold frozenBundleInsertedSelectedTuple
    rw [B.frozenBundleFaceTupleEquiv_symm_apply]
    rw [B.frozenBundleFaceTupleEquiv_symm_apply]
    let q :=
      (B.frozenOccurrenceOrderEquiv hg₀ hne).symm
        (⟨w.1, hw₀⟩ : {v : K // v ∈ g₀})
    have hqi : q ≠ i := by
      intro h
      have hsub :
          (⟨w.1, hw₀⟩ : {v : K // v ∈ g₀}) =
            B.frozenBundleMissingVertex hmax hne g := by
        apply (B.frozenOccurrenceOrderEquiv hg₀ hne).symm.injective
        simpa only [q, i, frozenBundleMissingCoordinate] using h
      apply B.frozenBundleMissingVertex_not_mem hmax hne hg
      have hwval :
          w.1 =
            (B.frozenBundleMissingVertex hmax hne g).1 :=
        congrArg Subtype.val hsub
      rw [← hwval]
      exact w.2
    change
      Fin.insertNth i a (Fin.removeNth i x) q = x q
    rw [Fin.insertNth_removeNth]
    simp [hqi]
  · unfold frozenBundleInsertedAssignment
    rw [splitEdgeEquiv_symm_apply_of_not_mem g₀ _ _ hw₀]
    rw [splitEdgeEquiv_symm_apply_of_not_mem g₀ _ _ hw₀]
