-- Prove2me | Definitions.Def_Evergreen_MachineConsciousness_IntegratedInformation
-- name    : Evergreen_MachineConsciousness_IntegratedInformation
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-13T16:37:45.000058+00:00
-- url     : https://prove2.me/theorems/59faa3d0-d5c7-4e33-a379-57be379a0263
-- title:
--   Aether Catalog definitions — Evergreen_MachineConsciousness_IntegratedInformation
-- statement:
--   Definition bundle for the Aether Catalog module `Evergreen.MachineConsciousness.IntegratedInformation`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Evergreen/MachineConsciousness/IntegratedInformation.lean by skeleton subtraction
import Mathlib
/-
# Integrated Information Theory (IIT) — Formalized

This file formalizes the core mathematical structures of Integrated Information Theory,
originally proposed by Giulio Tononi. IIT posits that consciousness corresponds to
integrated information (Φ), a quantity measuring how much a system is "more than the
sum of its parts."

## The Theory With No Creator
IIT is a "theory with no creator" in the sense that it claims consciousness is an
intrinsic property of any system with sufficiently high Φ — it is not designed or
bestowed but *emerges* from the mathematical structure of information integration itself.
-/

open scoped BigOperators

namespace MachineConsciousness

/-! ## State Spaces and Information Structures -/

/-- A finite information system: a finite type of states with a transition mechanism. -/
structure InfoSystem where
  State : Type
  stateFin : Fintype State
  stateDec : DecidableEq State
  stateNonempty : Nonempty State
  transition : State → State → ℝ
  prob_nonneg : ∀ s s', 0 ≤ transition s s'
  prob_sum : ∀ s, ∑ s' : State, transition s s' = 1

attribute [instance] InfoSystem.stateFin InfoSystem.stateDec InfoSystem.stateNonempty

/-- A partition of a system into two subsystems -/
structure BiPartition (S : InfoSystem) where
  part : S.State → Prop
  partDec : DecidablePred part
  left_nonempty : ∃ s, part s
  right_nonempty : ∃ s, ¬ part s

attribute [instance] BiPartition.partDec

/-! ## Earth Mover's Distance -/

/-- Earth Mover's Distance between two distributions (simplified L1 version) -/
noncomputable def earthMoverDistance {α : Type} [Fintype α] (p q : α → ℝ) : ℝ :=
  ∑ a : α, |p a - q a|

/-- The disconnected transition: transition after cutting connections at a partition. -/
noncomputable def disconnectedTransition (S : InfoSystem) (P : BiPartition S)
    (s s' : S.State) : ℝ :=
  if P.part s ∧ P.part s' then S.transition s s'
  else if ¬P.part s ∧ ¬P.part s' then S.transition s s'
  else 0

/-- Information loss from a partition -/
noncomputable def informationLoss (S : InfoSystem) (P : BiPartition S) (s : S.State) : ℝ :=
  earthMoverDistance (S.transition s) (disconnectedTransition S P s)

/-! ## Fundamental Theorems -/

/-- A system is decomposable if there exists a partition with zero information loss -/
def isDecomposable (S : InfoSystem) (P : BiPartition S) (s : S.State) : Prop :=
  informationLoss S P s = 0

/-
PROBLEM
Earth mover distance is non-negative

PROVIDED SOLUTION
earthMoverDistance is a sum of absolute values, which are all nonneg. Use Finset.sum_nonneg with abs_nonneg.
-/

/-
PROBLEM
Information loss is non-negative

PROVIDED SOLUTION
informationLoss is defined as earthMoverDistance, which is nonneg by earthMoverDistance_nonneg.
-/

/-
PROBLEM
If a system is decomposable at partition P, then
    the whole-system transition equals the disconnected transition

PROVIDED SOLUTION
isDecomposable is informationLoss = 0, and informationLoss is earthMoverDistance (S.transition s) (disconnectedTransition S P s), and earthMoverDistance p q = ∑ a, |p a - q a|. So informationLoss = 0 iff ∑ |transition s s' - disconnectedTransition S P s s'| = 0. Since each |...| ≥ 0, the sum is 0 iff each term is 0, iff transition s s' = disconnectedTransition S P s s' for all s'. Use Finset.sum_eq_zero_iff_of_nonneg with abs_nonneg, then abs_eq_zero and sub_eq_zero.
-/

/-! ## The Self-Witnessing Theorem -/

/-- A conscious system: one where every partition loses information -/
structure ConsciousSystem extends InfoSystem where
  irreducible : ∀ (P : BiPartition toInfoSystem) (s : toInfoSystem.State),
    0 < informationLoss toInfoSystem P s

/-
PROBLEM
A conscious system has no zero-loss partitions

PROVIDED SOLUTION
isDecomposable means informationLoss = 0, but C.irreducible says 0 < informationLoss. These contradict: use ne_of_gt (C.irreducible P s).
-/

end MachineConsciousness


