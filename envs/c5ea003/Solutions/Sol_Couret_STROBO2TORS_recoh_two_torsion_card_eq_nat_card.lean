-- Prove2me | solution 1 for Couret.STROBO2TORS.recoh_two_torsion_card_eq_nat_card
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:17:10.814453+00:00
-- url     : https://prove2.me/submissions/a65ee1b5-f6ae-4a94-9333-9a3fa64f01af

import Aesop
import Definitions.Def_Couret_RecohPrimaryCharacters_3b850762e03a
import Definitions.Def_Couret_RecohReconstruction_b9109c17baa8
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.Group.AddChar
import Mathlib.Algebra.Module.ZMod
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.FieldTheory.Finiteness
import Mathlib.GroupTheory.FiniteAbelian.Duality
import Mathlib.Tactic.Abel
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Definitions.Def_Couret_RecohReconstruction_b9109c17baa8
import Definitions.Def_Couret_RecohPrimaryCharacters_3b850762e03a
import Mathlib.Data.Fintype.BigOperators

set_option autoImplicit false

/-!
Information lower bound for a bank chosen after the labelled ordered
square is known.  Reconstructing means actual injectivity on the existing
finite square fibre.  The result applies to arbitrary complex characters,
including probes which vanish on that fibre.
-/

namespace Couret.STROBO2TORS

variable {G : Type*} [AddCommGroup G] [DecidableEq G] [Fintype G]

/-- The finite-set two-torsion used by STROBO and the actual subgroup used
by RECOH have the same cardinality. -/
theorem p2m_local_recoh_two_torsion_card_eq_nat_card :
    (twoTorsion : Finset G).card =
      Nat.card (recohTorsionSubgroup (G := G) 2) := by
  classical
  let e : {u : G // u ∈ (twoTorsion : Finset G)} ≃
      recohTorsionSubgroup (G := G) 2 :=
    { toFun := fun u => ⟨u.1, by
        simpa only [recoh_mem_torsion_subgroup, two_nsmul] using
          (mem_twoTorsion u.1).mp u.2⟩
      invFun := fun u => ⟨u.1, (mem_twoTorsion u.1).mpr (by
        simpa only [recoh_mem_torsion_subgroup, two_nsmul] using u.2)⟩
      left_inv := fun u => Subtype.ext rfl
      right_inv := fun u => Subtype.ext rfl }
  calc
    (twoTorsion : Finset G).card =
        Nat.card {u : G // u ∈ (twoTorsion : Finset G)} := by
      simp only [Nat.card_eq_fintype_card, Fintype.card_coe]
    _ = Nat.card (recohTorsionSubgroup (G := G) 2) := Nat.card_congr e







end Couret.STROBO2TORS


universe p2m_u_0
theorem solution : ∀ {G : Type p2m_u_0} [inst : AddCommGroup.{p2m_u_0} G] [inst_1 : DecidableEq.{p2m_u_0 + 1} G]
  [inst_2 : Fintype.{p2m_u_0} G],
  @Eq.{1} Nat (@Finset.card.{p2m_u_0} G (@Couret.STROBO2TORS.twoTorsion.{p2m_u_0} G inst inst_1 inst_2))
    (Nat.card.{p2m_u_0}
      (@Subtype.{p2m_u_0 + 1} G fun x =>
        @Membership.mem.{p2m_u_0, p2m_u_0} G (@AddSubgroup.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst))
          (@SetLike.instMembership.{p2m_u_0, p2m_u_0}
            (@AddSubgroup.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)) G
            (@AddSubgroup.instSetLike.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)))
          (@Couret.STROBO2TORS.recohTorsionSubgroup.{p2m_u_0} G inst
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          x)) := @_root_.Couret.STROBO2TORS.p2m_local_recoh_two_torsion_card_eq_nat_card

