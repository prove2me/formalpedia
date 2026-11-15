-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.partitionAtomIndicator_measurable
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T11:26:26.538087+00:00
-- url     : https://prove2.me/submissions/8c09dbd3-609b-49bd-a7d6-9042d877c3a1

/- Mechanically transplanted from https://github.com/plby/lean-proofs.git at 8822f7ddef30fadbd92e1c6ab4ed897af356af5e. Original scopes and proof bytes are oracle-derived. -/
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_ArithmeticProgression_Count
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Finite_Mean
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_APCorrespondence
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_ConditionalAverage
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_Energy
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_FacePartition
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_OrderedAtomEnergy
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_OrderedBoundaryPartition
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_OrderedGoodAtoms
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_OrderedPattern
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





@[simp]
theorem partitionAtomAt_eq_iff_mem
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (P : FacePartition Ω) (x : Ω) (a : P.parts) :
    partitionAtomAt P x = a ↔ x ∈ a.1 := by
  constructor
  · intro h
    rw [← h]
    exact P.mem_part (Finset.mem_univ x)
  · intro hx
    apply Subtype.ext
    exact P.part_eq_of_mem a.2 hx

theorem partitionAtomAt_eq_iff_mem_part
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (P : FacePartition Ω) (x y : Ω) :
    partitionAtomAt P y = partitionAtomAt P x ↔
      y ∈ P.part x := by
  rw [partitionAtomAt_eq_iff_mem]
  rfl























/-! ## Sublevel atoms and low-density charging -/









/-! ## Large local averages and finite Markov bounds -/











/-! ## Coarse--fine defect bases -/

























/-! ## Ordered boundary specialization -/



























/-! ## Good local configurations and closed atom configurations -/









namespace ClosedOrderedAtomConfiguration













end ClosedOrderedAtomConfiguration

end Wikipedia.SzemeredisTheorem

end
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
open Wikipedia.SzemeredisTheorem
open scoped BigOperators
/-! ## Canonical atoms and unions of genuine partition atoms -/

open Wikipedia.SzemeredisTheorem in
/-- The indicator of a genuine partition atom is measurable for that
partition. -/
theorem solution
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (P : FacePartition Ω) (a : P.parts) :
    IsPartitionMeasurable P (partitionAtomIndicator P a) := by
  intro x y hy
  have hxy :
      partitionAtomAt P y = partitionAtomAt P x :=
    (partitionAtomAt_eq_iff_mem_part P x y).2 hy
  by_cases hx : x ∈ a.1
  · have hax : partitionAtomAt P x = a :=
      (partitionAtomAt_eq_iff_mem P x a).2 hx
    have hay : partitionAtomAt P y = a := hxy.trans hax
    have hy' : y ∈ a.1 :=
      (partitionAtomAt_eq_iff_mem P y a).1 hay
    simp [partitionAtomIndicator_of_mem P a hx,
      partitionAtomIndicator_of_mem P a hy']
  · have hy' : y ∉ a.1 := by
      intro hya
      have hay : partitionAtomAt P y = a :=
        (partitionAtomAt_eq_iff_mem P y a).2 hya
      have hax : partitionAtomAt P x = a :=
        hxy.symm.trans hay
      exact hx ((partitionAtomAt_eq_iff_mem P x a).1 hax)
    simp [partitionAtomIndicator_of_not_mem P a hx,
      partitionAtomIndicator_of_not_mem P a hy']
