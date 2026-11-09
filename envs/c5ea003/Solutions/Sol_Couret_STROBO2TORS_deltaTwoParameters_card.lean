-- Prove2me | solution 1 for Couret.STROBO2TORS.deltaTwoParameters_card
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:01:03.096915+00:00
-- url     : https://prove2.me/submissions/4ca8314f-574b-4269-a25e-60a5f91c3bc2

import Aesop
import Definitions.Def_Couret_Strobo2TorsDeltaTwoCount_96c8f007ba6a
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.SymmDiff
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Tauto
import Definitions.Def_Couret_Strobo2TorsDeltaOrdinaryCount_91279c99d3e0

set_option autoImplicit false

open scoped BigOperators symmDiff

/-!
Exact count of the ordinary delta-two edges, with zero allowed.

Parameters (a,u,b) have u a nonzero element of G[2] and b outside
{a,a+u}. They represent the ordered pair
({a,a+u,b}, {a,a+u,b+u}). Each ordered pair has precisely two
parameters, according to the choice a or a+u in its common pair.
The graph handshake supplies the second factor of two.
-/

namespace Couret.STROBO2TORS

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

private theorem deltaTwo_ne_add_self (a u : G) (hu0 : u ≠ 0) :
    a ≠ a + u := by
  intro h
  apply hu0
  exact (add_left_cancel (show a + 0 = a + u by simpa using h)).symm











variable [Fintype G]









theorem p2m_local_deltaTwoParameters_card :
    (deltaTwoParameters : Finset (DeltaTwoParameter G)).card =
      Fintype.card G * (Fintype.card G - 2) *
        ((twoTorsion : Finset G).card - 1) := by
  unfold deltaTwoParameters
  rw [Finset.card_sigma]
  calc
    _ = ∑ _au ∈ ((Finset.univ : Finset G) ×ˢ ((twoTorsion : Finset G).erase 0)),
        (Fintype.card G - 2) := by
      apply Finset.sum_congr rfl
      rintro ⟨a,u⟩ hau
      have hu0 : u ≠ 0 := (Finset.mem_erase.mp (Finset.mem_product.mp hau).2).1
      rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ]
      simp [deltaTwo_ne_add_self a u hu0]
    _ = _ := by
      have h0 : (0 : G) ∈ twoTorsion := (mem_twoTorsion _).mpr (by simp)
      simp [Finset.card_erase_of_mem h0, Nat.mul_comm, Nat.mul_assoc, Nat.mul_left_comm]

attribute [local instance] Classical.propDecidable






















end Couret.STROBO2TORS

universe p2m_u_0
theorem solution : ∀ {G : Type p2m_u_0} [inst : AddCommGroup.{p2m_u_0} G] [inst_1 : DecidableEq.{p2m_u_0 + 1} G]
  [inst_2 : Fintype.{p2m_u_0} G],
  @Eq.{1} Nat
    (@Finset.card.{p2m_u_0} (Couret.STROBO2TORS.DeltaTwoParameter.{p2m_u_0} G)
      (@Couret.STROBO2TORS.deltaTwoParameters.{p2m_u_0} G inst inst_1 inst_2))
    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) (@Fintype.card.{p2m_u_0} G inst_2)
        (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) (@Fintype.card.{p2m_u_0} G inst_2)
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
        (@Finset.card.{p2m_u_0} G (@Couret.STROBO2TORS.twoTorsion.{p2m_u_0} G inst inst_1 inst_2))
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) := @_root_.Couret.STROBO2TORS.p2m_local_deltaTwoParameters_card

