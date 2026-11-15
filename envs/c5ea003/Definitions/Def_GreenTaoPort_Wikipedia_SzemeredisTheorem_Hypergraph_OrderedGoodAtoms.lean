-- Prove2me | Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_OrderedGoodAtoms
-- name    : GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_OrderedGoodAtoms
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-11-14T09:02:49.832423+00:00
-- url     : https://prove2.me/theorems/dd910979-0aa4-44f4-8da4-3bebf69a73e5
-- title:
--   Thresholded partition atoms and realizable closed configurations
-- statement:
--   For a finite face partition, the canonical atom at a point is its genuine containing cell, and a selected finite family of atoms has its finite union. Small-average and large-average atom sets are selected by strict inequalities for the conditional mean, below $\alpha$ or above $\beta$ respectively; their supports are the corresponding unions.
--
--   The coarse–fine boundary defect of an upper atom is the fine conditional mean of its indicator minus the coarse conditional mean, and its square is also supplied. The ordered version uses the shared boundary partitions.
--
--   A closed ordered atom configuration records one atom at every face and rank together with a full tuple lying in each selected atom after restriction. This witness enforces simultaneous realizability. Every full tuple produces its canonical closed configuration.
-- source:
--   https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/Wikipedia/SzemeredisTheorem/Hypergraph/OrderedGoodAtoms.lean#L32-L983

import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_OrderedAtomEnergy
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
# Good ordered atoms and localized bad-base accounting

The hypergraph removal argument must localize a global coarse--fine energy
gap to genuine boundary atoms.  This file supplies the finite bookkeeping
for that step.

For an arbitrary finite partition we define the union of a selected family
of atoms and prove that its normalized mass is the sum of the atom masses.
Sublevel atoms charge only a small part of a target atom, while atoms on
which a nonnegative local average is large satisfy a finite Markov bound.
Applying this to the square of a coarse--fine conditional-density defect
gives the headline estimate

```text
mass (upperAtom ∩ badBase) ≤
  densityThreshold + atomEnergyGap / defectThreshold.
```

The final section specializes these definitions to shared ordered
boundaries and packages realizable closed atom configurations.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

/-! ## Canonical atoms and unions of genuine partition atoms -/

/-- The canonical genuine atom containing `x`. -/
def partitionAtomAt
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (P : FacePartition Ω) (x : Ω) :
    P.parts :=
  ⟨P.part x, P.part_mem.2 (Finset.mem_univ x)⟩









/-- Union of a selected finite family of genuine partition atoms. -/
def partitionAtomUnion
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (P : FacePartition Ω) (s : Finset P.parts) :
    Finset Ω :=
  s.biUnion fun a => a.1



















/-! ## Sublevel atoms and low-density charging -/

/-- Atoms on which the conditional average of `f` is below `α`. -/
noncomputable def smallAverageBaseAtoms
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (P : FacePartition Ω) (f : Ω → ℝ) (α : ℝ) :
    Finset P.parts := by
  classical
  exact (Finset.univ : Finset P.parts).filter fun b =>
    conditionalMean P f (P.representative b) < α

/-- Union of the atoms on which the conditional average is below `α`. -/
noncomputable def smallAverageBaseSupport
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (P : FacePartition Ω) (f : Ω → ℝ) (α : ℝ) :
    Finset Ω :=
  partitionAtomUnion P (smallAverageBaseAtoms P f α)





/-! ## Large local averages and finite Markov bounds -/

/-- Atoms on which the conditional average of `f` exceeds `β`. -/
noncomputable def largeAverageBaseAtoms
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (P : FacePartition Ω) (f : Ω → ℝ) (β : ℝ) :
    Finset P.parts := by
  classical
  exact (Finset.univ : Finset P.parts).filter fun b =>
    β < conditionalMean P f (P.representative b)

/-- Union of atoms on which the conditional average of `f` exceeds `β`. -/
noncomputable def largeAverageBaseSupport
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (P : FacePartition Ω) (f : Ω → ℝ) (β : ℝ) :
    Finset Ω :=
  partitionAtomUnion P (largeAverageBaseAtoms P f β)







/-! ## Coarse--fine defect bases -/

/-- Change in the conditional density of one upper atom between a fine and
a coarse observing partition. -/
noncomputable def atomBoundaryDefect
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (fine coarse upper : FacePartition Ω)
    (a : upper.parts) (x : Ω) : ℝ :=
  conditionalMean fine (partitionAtomIndicator upper a) x -
    conditionalMean coarse (partitionAtomIndicator upper a) x

/-- Squared coarse--fine conditional-density defect of one upper atom. -/
noncomputable def atomBoundaryDefectSq
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (fine coarse upper : FacePartition Ω)
    (a : upper.parts) (x : Ω) : ℝ :=
  atomBoundaryDefect fine coarse upper a x ^ 2





















/-! ## Ordered boundary specialization -/







/-- Ordered version of the coarse--fine conditional-density defect. -/
noncomputable def orderedAtomBoundaryDefect
    {G : Type*} [Fintype G] [DecidableEq G]
    {k j : ℕ}
    (fine coarse : OrderedFacePartitionSystem G k j)
    (e : OrderedFace k (j + 1))
    (upper : FacePartition (Fin (j + 1) → G))
    (a : upper.parts) (x : Fin (j + 1) → G) : ℝ :=
  atomBoundaryDefect
    (orderedBoundaryPartition fine e)
    (orderedBoundaryPartition coarse e)
    upper a x



















/-! ## Good local configurations and closed atom configurations -/







/-- A realizable closed atom configuration for all ranks of an ordered
partition complex.  The witness ensures that all chosen atoms are
compatible under restriction. -/
structure ClosedOrderedAtomConfiguration
    (G : Type*) [Fintype G] [DecidableEq G]
    (k r : ℕ) (C : OrderedPartitionComplex G k r) where
  witness : Fin k → G
  atom :
    (j : Fin (r + 1)) →
      (e : OrderedFace k j.1) →
        (C.partition j e).parts
  mem_atom :
    ∀ (j : Fin (r + 1)) (e : OrderedFace k j.1),
      orderedFaceTuple e witness ∈ (atom j e).1

namespace ClosedOrderedAtomConfiguration

/-- The canonical closed configuration realized by a full ordered tuple. -/
def ofTuple
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ} (C : OrderedPartitionComplex G k r)
    (x : Fin k → G) :
    ClosedOrderedAtomConfiguration G k r C where
  witness := x
  atom j e :=
    partitionAtomAt (C.partition j e)
      (orderedFaceTuple e x)
  mem_atom j e :=
    (C.partition j e).mem_part
      (Finset.mem_univ (orderedFaceTuple e x))











end ClosedOrderedAtomConfiguration

end Wikipedia.SzemeredisTheorem


/- Materialize compiler-generated declarations promised by this bundle. -/
run_meta do
  for requiredName in #[
    `Wikipedia.SzemeredisTheorem.ClosedOrderedAtomConfiguration.ctorIdx,
    `Wikipedia.SzemeredisTheorem.ClosedOrderedAtomConfiguration.mk.inj,
    `Wikipedia.SzemeredisTheorem.ClosedOrderedAtomConfiguration.mk.injEq,
    `Wikipedia.SzemeredisTheorem.ClosedOrderedAtomConfiguration.mk.sizeOf_spec,
    `Wikipedia.SzemeredisTheorem.ClosedOrderedAtomConfiguration.noConfusionType,
    `Wikipedia.SzemeredisTheorem.largeAverageBaseAtoms.eq_1,
    `Wikipedia.SzemeredisTheorem.largeAverageBaseSupport.eq_1,
    `Wikipedia.SzemeredisTheorem.partitionAtomUnion.eq_1,
    `Wikipedia.SzemeredisTheorem.smallAverageBaseAtoms.eq_1,
    `Wikipedia.SzemeredisTheorem.smallAverageBaseSupport.eq_1
  ] do
    let actualName ← Lean.realizeGlobalConstNoOverloadCore requiredName
    unless actualName == requiredName do
      throwError "Generated companion resolved to an unexpected name"


