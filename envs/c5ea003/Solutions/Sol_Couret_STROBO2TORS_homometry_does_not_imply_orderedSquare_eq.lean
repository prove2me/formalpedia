-- Prove2me | solution 1 for Couret.STROBO2TORS.homometry_does_not_imply_orderedSquare_eq
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:52:33.980841+00:00
-- url     : https://prove2.me/submissions/d233a6ac-ecb5-449f-b5fb-8251d0ec8682

import Aesop
import Definitions.Def_Couret_StroboHomometry_90864170804d
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality
import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Definitions.Def_Couret_RecohFourierBridge_5b164a1abe76
import Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality
import Mathlib.Tactic.Ring

set_option autoImplicit false

/-!
Classical Fourier implication, made explicit for the existing STROBO observable:
equal labelled ordered convolution squares imply equal difference multiplicities.
No converse and no novelty claim. See Lev (2004), section 3, Problem 2, p. 5,
and Riley Casper's observation of 2026-10-15.
-/

open scoped BigOperators ComplexConjugate

namespace Couret.STROBO2TORS

variable {G : Type*} [AddCommGroup G] [DecidableEq G]







section Finite
variable [Fintype G]





















end Finite

/-- A counterexample to the converse, already among triples in Z/7Z.
The two supports are translates, but their labelled ordered squares differ. -/
theorem p2m_local_homometry_does_not_imply_orderedSquare_eq :
    ∃ S T : Finset (ZMod 7), S.card = 3 ∧ T.card = 3 ∧
      (∀ z, differenceAutocorrelation S z = differenceAutocorrelation T z) ∧
      ¬ (∀ z, orderedSquare S z = orderedSquare T z) := by
  refine ⟨{0, 1, 2}, {1, 2, 3}, ?_, ?_, ?_, ?_⟩
  · decide
  · decide
  · decide
  · decide

end Couret.STROBO2TORS


theorem solution : @Exists.{1} (Finset.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7))))) fun S =>
  @Exists.{1} (Finset.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7))))) fun T =>
    And
      (@Eq.{1} Nat (@Finset.card.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))) S)
        (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
      (And
        (@Eq.{1} Nat (@Finset.card.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))) T)
          (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
        (And
          (∀ (z : ZMod (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))),
            @Eq.{1} Nat
              (@Couret.STROBO2TORS.differenceAutocorrelation.{0}
                (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7))))
                (@Ring.toAddCommGroup.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7))))
                  (@CommRing.toRing.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7))))
                    (ZMod.commRing (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7))))))
                (ZMod.decidableEq (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))) S z)
              (@Couret.STROBO2TORS.differenceAutocorrelation.{0}
                (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7))))
                (@Ring.toAddCommGroup.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7))))
                  (@CommRing.toRing.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7))))
                    (ZMod.commRing (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7))))))
                (ZMod.decidableEq (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))) T z))
          (Not
            (∀ (z : ZMod (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))),
              @Eq.{1} Nat
                (@Couret.STROBO2TORS.orderedSquare.{0}
                  (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7))))
                  (@Ring.toAddCommGroup.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7))))
                    (@CommRing.toRing.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7))))
                      (ZMod.commRing (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7))))))
                  (ZMod.decidableEq (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))) S z)
                (@Couret.STROBO2TORS.orderedSquare.{0}
                  (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7))))
                  (@Ring.toAddCommGroup.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7))))
                    (@CommRing.toRing.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7))))
                      (ZMod.commRing (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7))))))
                  (ZMod.decidableEq (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))) T z))))) := @_root_.Couret.STROBO2TORS.p2m_local_homometry_does_not_imply_orderedSquare_eq

