-- Prove2me | solution 1 for Couret.InterIA.SingletonNecessity.four_torsion_trivial_of_odd_annihilator
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:51:23.813457+00:00
-- url     : https://prove2.me/submissions/92788913-72e7-4c71-ab03-a622d9b1d348

import Definitions.Def_Couret_C4SquareAlgebra_06ed7b10cc0e
import Definitions.Def_Couret_CertificateSoundness_1059e04412f7
import Definitions.Def_Couret_ExtractionBasics_37ec1603f738
import Definitions.Def_Couret_MatchingElimination_8675038abe55
import Definitions.Def_Couret_RelabelBasics_a474d20b9d5f
import Definitions.Def_Couret_SixDoublePairing_42d09f1cbb6a
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
import Definitions.Def_Couret_MatchingElimination_8675038abe55
import Definitions.Def_Couret_C4SquareAlgebra_06ed7b10cc0e
import Definitions.Def_Couret_ExtractionBasics_37ec1603f738
import Definitions.Def_Couret_RelabelBasics_a474d20b9d5f
import Definitions.Def_Couret_SixDoublePairing_42d09f1cbb6a
import Definitions.Def_Couret_CertificateSoundness_1059e04412f7

set_option autoImplicit false
namespace Couret.InterIA.SingletonNecessity
open Couret.InterIA.AbelianBoundary Couret.InterIA.Parity
variable {P H : Type*} [AddCommGroup P] [AddCommGroup H]



theorem p2m_local_four_torsion_trivial_of_odd_annihilator (k : ℕ)
    (hH : ∀ y : H, (2*k+1) • y=0) :
    ∀ y : H, (4:ℕ) • y=0 → y=0 := by
  intro y h4
  have h2 : (2:ℕ) • y=0 := by
    have hm := hH ((2:ℕ) • y)
    have hz : (2*k) • ((2:ℕ) • y)=0 := by
      calc
        (2*k) • ((2:ℕ) • y)=k • ((4:ℕ) • y) := by
          simp only [smul_smul]
          congr 1
          omega
        _ = 0 := by rw [h4,nsmul_zero]
    simpa only [add_nsmul,one_nsmul,hz,zero_add] using hm
  have hm := hH y
  have hz : (2*k) • y=0 := by
    calc
      (2*k) • y=k • ((2:ℕ) • y) := by rw [smul_smul,Nat.mul_comm]
      _ = 0 := by rw [h2,nsmul_zero]
  simpa only [add_nsmul,one_nsmul,hz,zero_add] using hm









end Couret.InterIA.SingletonNecessity

universe p2m_u_0
theorem solution : ∀ {H : Type p2m_u_0} [inst : AddCommGroup.{p2m_u_0} H] (k : Nat),
  (∀ (y : H),
      @Eq.{p2m_u_0 + 1} H
        (@HSMul.hSMul.{0, p2m_u_0, p2m_u_0} Nat H H
          (@instHSMul.{0, p2m_u_0} Nat H
            (@AddMonoid.toNSMul.{p2m_u_0} H
              (@SubNegMonoid.toAddMonoid.{p2m_u_0} H
                (@AddGroup.toSubNegMonoid.{p2m_u_0} H (@AddCommGroup.toAddGroup.{p2m_u_0} H inst)))))
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) k)
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          y)
        (@OfNat.ofNat.{p2m_u_0} H (nat_lit 0)
          (@Zero.toOfNat0.{p2m_u_0} H
            (@NegZeroClass.toZero.{p2m_u_0} H
              (@SubNegZeroMonoid.toNegZeroClass.{p2m_u_0} H
                (@SubtractionMonoid.toSubNegZeroMonoid.{p2m_u_0} H
                  (@SubtractionCommMonoid.toSubtractionMonoid.{p2m_u_0} H
                    (@AddCommGroup.toDivisionAddCommMonoid.{p2m_u_0} H inst)))))))) →
    ∀ (y : H),
      @Eq.{p2m_u_0 + 1} H
          (@HSMul.hSMul.{0, p2m_u_0, p2m_u_0} Nat H H
            (@instHSMul.{0, p2m_u_0} Nat H
              (@AddMonoid.toNSMul.{p2m_u_0} H
                (@SubNegMonoid.toAddMonoid.{p2m_u_0} H
                  (@AddGroup.toSubNegMonoid.{p2m_u_0} H (@AddCommGroup.toAddGroup.{p2m_u_0} H inst)))))
            (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) y)
          (@OfNat.ofNat.{p2m_u_0} H (nat_lit 0)
            (@Zero.toOfNat0.{p2m_u_0} H
              (@NegZeroClass.toZero.{p2m_u_0} H
                (@SubNegZeroMonoid.toNegZeroClass.{p2m_u_0} H
                  (@SubtractionMonoid.toSubNegZeroMonoid.{p2m_u_0} H
                    (@SubtractionCommMonoid.toSubtractionMonoid.{p2m_u_0} H
                      (@AddCommGroup.toDivisionAddCommMonoid.{p2m_u_0} H inst))))))) →
        @Eq.{p2m_u_0 + 1} H y
          (@OfNat.ofNat.{p2m_u_0} H (nat_lit 0)
            (@Zero.toOfNat0.{p2m_u_0} H
              (@NegZeroClass.toZero.{p2m_u_0} H
                (@SubNegZeroMonoid.toNegZeroClass.{p2m_u_0} H
                  (@SubtractionMonoid.toSubNegZeroMonoid.{p2m_u_0} H
                    (@SubtractionCommMonoid.toSubtractionMonoid.{p2m_u_0} H
                      (@AddCommGroup.toDivisionAddCommMonoid.{p2m_u_0} H inst))))))) := @_root_.Couret.InterIA.SingletonNecessity.p2m_local_four_torsion_trivial_of_odd_annihilator

