-- Prove2me | solution 1 for Couret.STROBO2TORS.twice_deltaTwoOrderedPairs_card
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:16:52.376683+00:00
-- url     : https://prove2.me/submissions/c7f26d65-461b-446e-92e3-ec2a50b0bf3f

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
import Theorems.Thm_Couret_STROBO2TORS_deltaTwoParameters_card
import Theorems.Thm_Couret_STROBO2TORS_deltaTwoRealization_image
import Theorems.Thm_Couret_STROBO2TORS_deltaTwoRealization_preimage
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













variable [Fintype G]











attribute [local instance] Classical.propDecidable













theorem p2m_local_twice_deltaTwoOrderedPairs_card :
    2 * (deltaTwoOrderedPairs : Finset (Finset G × Finset G)).card =
      Fintype.card G * (Fintype.card G - 2) *
        ((twoTorsion : Finset G).card - 1) := by
  have hcount : (deltaTwoParameters : Finset (DeltaTwoParameter G)).card =
      2 * (deltaTwoOrderedPairs : Finset (Finset G × Finset G)).card := by
    calc
      _ = ∑ P ∈ (deltaTwoOrderedPairs : Finset (Finset G × Finset G)),
          ((deltaTwoParameters : Finset (DeltaTwoParameter G)).filter
            (fun p => deltaTwoRealization p = P)).card := by
        rw [← deltaTwoRealization_image]
        exact Finset.card_eq_sum_card_image deltaTwoRealization deltaTwoParameters
      _ = ∑ _P ∈ (deltaTwoOrderedPairs : Finset (Finset G × Finset G)), 2 := by
        apply Finset.sum_congr rfl
        exact deltaTwoRealization_preimage
      _ = _ := by simp [Nat.mul_comm]
  rw [← hcount, deltaTwoParameters_card]








end Couret.STROBO2TORS

universe p2m_u_0
theorem solution : ∀ {G : Type p2m_u_0} [inst : AddCommGroup.{p2m_u_0} G] [inst_1 : DecidableEq.{p2m_u_0 + 1} G]
  [inst_2 : Fintype.{p2m_u_0} G],
  @Eq.{1} Nat
    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
      (@Finset.card.{p2m_u_0} (Prod.{p2m_u_0, p2m_u_0} (Finset.{p2m_u_0} G) (Finset.{p2m_u_0} G))
        (@Couret.STROBO2TORS.deltaTwoOrderedPairs.{p2m_u_0} G inst inst_1 inst_2)))
    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) (@Fintype.card.{p2m_u_0} G inst_2)
        (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) (@Fintype.card.{p2m_u_0} G inst_2)
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
        (@Finset.card.{p2m_u_0} G (@Couret.STROBO2TORS.twoTorsion.{p2m_u_0} G inst inst_1 inst_2))
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) := @_root_.Couret.STROBO2TORS.p2m_local_twice_deltaTwoOrderedPairs_card

