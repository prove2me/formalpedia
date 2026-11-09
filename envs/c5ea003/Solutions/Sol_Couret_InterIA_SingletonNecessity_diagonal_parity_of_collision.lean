-- Prove2me | solution 1 for Couret.InterIA.SingletonNecessity.diagonal_parity_of_collision
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:05:34.224547+00:00
-- url     : https://prove2.me/submissions/da304a1b-d5b4-44fe-9726-b03ab4a4d614

import Definitions.Def_Couret_ExtractionBasics_37ec1603f738
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Group.Pi.Basic
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.SymmDiff
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Int.Basic
import Mathlib.Data.List.Permutation
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Definitions.Def_Couret_CertificateSoundness_1059e04412f7
import Definitions.Def_Couret_SingletonNormalization_99875800f8c3
import Mathlib.Tactic.FinCases

set_option autoImplicit false
namespace Couret.InterIA.SingletonNecessity
open Finset Couret.InterIA.Parity
variable {G : Type*} [AddCommGroup G] [DecidableEq G]


















theorem p2m_local_diagonal_parity_of_collision (A B : Finset G)
    (hc : ∀ z, orderedSquare A z=orderedSquare B z) (z : G) :
    diagonalCount A z % 2 = diagonalCount B z % 2 := by
  rw [← ordered_square_parity_nat,← ordered_square_parity_nat,hc]

end Couret.InterIA.SingletonNecessity

universe p2m_u_0
theorem solution : ∀ {G : Type p2m_u_0} [inst : AddCommGroup.{p2m_u_0} G] [inst_1 : DecidableEq.{p2m_u_0 + 1} G]
  (A B : Finset.{p2m_u_0} G),
  (∀ (z : G),
      @Eq.{1} Nat (@Couret.InterIA.Parity.orderedSquare.{p2m_u_0} G inst inst_1 A z)
        (@Couret.InterIA.Parity.orderedSquare.{p2m_u_0} G inst inst_1 B z)) →
    ∀ (z : G),
      @Eq.{1} Nat
        (@HMod.hMod.{0, 0, 0} Nat Nat Nat (@instHMod.{0} Nat Nat.instMod)
          (@Couret.InterIA.Parity.diagonalCount.{p2m_u_0} G inst inst_1 A z)
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@HMod.hMod.{0, 0, 0} Nat Nat Nat (@instHMod.{0} Nat Nat.instMod)
          (@Couret.InterIA.Parity.diagonalCount.{p2m_u_0} G inst inst_1 B z)
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) := @_root_.Couret.InterIA.SingletonNecessity.p2m_local_diagonal_parity_of_collision

