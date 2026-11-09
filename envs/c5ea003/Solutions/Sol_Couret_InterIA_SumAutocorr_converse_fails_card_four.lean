-- Prove2me | solution 1 for Couret.InterIA.SumAutocorr.converse_fails_card_four
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:51:44.344582+00:00
-- url     : https://prove2.me/submissions/9616783f-d1bd-4115-9f2c-c067aa6a1081

import Definitions.Def_Couret_SumAutocorr_074e6f9ba1f0
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Analysis.Fourier.ZMod
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.SymmDiff
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Definitions.Def_Couret_ConvolutionParity_aa654fd002fc
import Mathlib.Analysis.Fourier.ZMod

set_option autoImplicit false
namespace Couret.InterIA.SumAutocorr
open Finset Couret.InterIA.Parity

variable {n : ℕ} [NeZero n]





















/-- Same-cardinality counterexample: the converse fails even for four-point supports. -/
theorem p2m_local_converse_fails_card_four :
    ∃ S T : Finset (ZMod 9), S.card=4 ∧ T.card=4 ∧
      (∀ z, orderedDifference S z=orderedDifference T z) ∧
      ¬ (∀ z, orderedSquare S z=orderedSquare T z) := by
  refine ⟨{0,1,2,3},{1,2,3,4},?_,?_,?_,?_⟩
  · decide
  · decide
  · decide
  · decide

end Couret.InterIA.SumAutocorr

theorem solution : @Exists.{1} (Finset.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 9) (instOfNatNat (nat_lit 9))))) fun S =>
  @Exists.{1} (Finset.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 9) (instOfNatNat (nat_lit 9))))) fun T =>
    And
      (@Eq.{1} Nat (@Finset.card.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 9) (instOfNatNat (nat_lit 9)))) S)
        (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
      (And
        (@Eq.{1} Nat (@Finset.card.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 9) (instOfNatNat (nat_lit 9)))) T)
          (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
        (And
          (∀ (z : ZMod (@OfNat.ofNat.{0} Nat (nat_lit 9) (instOfNatNat (nat_lit 9)))),
            @Eq.{1} Nat
              (@Couret.InterIA.SumAutocorr.orderedDifference
                (@OfNat.ofNat.{0} Nat (nat_lit 9) (instOfNatNat (nat_lit 9))) S z)
              (@Couret.InterIA.SumAutocorr.orderedDifference
                (@OfNat.ofNat.{0} Nat (nat_lit 9) (instOfNatNat (nat_lit 9))) T z))
          (Not
            (∀ (z : ZMod (@OfNat.ofNat.{0} Nat (nat_lit 9) (instOfNatNat (nat_lit 9)))),
              @Eq.{1} Nat
                (@Couret.InterIA.Parity.orderedSquare.{0}
                  (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 9) (instOfNatNat (nat_lit 9))))
                  (@Ring.toAddCommGroup.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 9) (instOfNatNat (nat_lit 9))))
                    (@CommRing.toRing.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 9) (instOfNatNat (nat_lit 9))))
                      (ZMod.commRing (@OfNat.ofNat.{0} Nat (nat_lit 9) (instOfNatNat (nat_lit 9))))))
                  (ZMod.decidableEq (@OfNat.ofNat.{0} Nat (nat_lit 9) (instOfNatNat (nat_lit 9)))) S z)
                (@Couret.InterIA.Parity.orderedSquare.{0}
                  (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 9) (instOfNatNat (nat_lit 9))))
                  (@Ring.toAddCommGroup.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 9) (instOfNatNat (nat_lit 9))))
                    (@CommRing.toRing.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 9) (instOfNatNat (nat_lit 9))))
                      (ZMod.commRing (@OfNat.ofNat.{0} Nat (nat_lit 9) (instOfNatNat (nat_lit 9))))))
                  (ZMod.decidableEq (@OfNat.ofNat.{0} Nat (nat_lit 9) (instOfNatNat (nat_lit 9)))) T z))))) := @_root_.Couret.InterIA.SumAutocorr.p2m_local_converse_fails_card_four

