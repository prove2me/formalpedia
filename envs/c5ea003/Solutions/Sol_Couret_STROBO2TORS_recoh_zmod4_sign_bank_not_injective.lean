-- Prove2me | solution 1 for Couret.STROBO2TORS.recoh_zmod4_sign_bank_not_injective
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:57:31.024774+00:00
-- url     : https://prove2.me/submissions/e8c161a2-32b0-4573-a8f6-3587064798e9

import Aesop
import Definitions.Def_Couret_RecohFourierBridge_5b164a1abe76
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_STROBO2TORS_recoh_zmod4_sign_bank_blind_involution
import Definitions.Def_Couret_RecohFourierBridge_5b164a1abe76
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false

/-!
RECOH upper-bank prerequisite: sign-only character probes cannot suffice
in general. On ZMod 4, every multiplicative character valued in {1,-1}
annihilates the nonzero involution 2.

This is a formal obstruction, not a construction of the required
2-primary and 3-primary characters. No global B(G) theorem is claimed.
-/

namespace Couret.STROBO2TORS

variable {G : Type*} [AddCommGroup G] [DecidableEq G]









/-- No finite bank composed ONLY of sign-valued multiplicative
characters can be injective on ZMod 4. Primary order four is
already necessary in this minimal counterexample. -/
theorem p2m_local_recoh_zmod4_sign_bank_not_injective
    (k : ℕ)
    (bank : Fin k → ZMod 4 → ℂ)
    (hadd : ∀ i : Fin k, ∀ a b : ZMod 4,
      bank i (a + b) = bank i a * bank i b)
    (hsign : ∀ i : Fin k, ∀ a : ZMod 4,
      bank i a = 1 ∨ bank i a = -1) :
    ¬ Function.Injective
      (fun a : ZMod 4 => fun i : Fin k => bank i a) := by
  intro hinj
  obtain ⟨hneq, _, hblind⟩ :=
    recoh_zmod4_sign_bank_blind_involution k bank hadd hsign
  have heq :
      (fun i : Fin k => bank i (2 : ZMod 4)) =
        (fun i : Fin k => bank i (0 : ZMod 4)) := by
    funext i
    exact hblind i
  exact hneq (hinj heq)

end Couret.STROBO2TORS


theorem solution : ∀ (k : Nat) (bank : Fin k → ZMod (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) → Complex),
  (∀ (i : Fin k) (a b : ZMod (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))),
      @Eq.{1} Complex
        (bank i
          (@HAdd.hAdd.{0, 0, 0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
            (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
            (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
            (@instHAdd.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
              (@Distrib.toAdd.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
                (@instDistribOfSemiring.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
                  (@CommSemiring.toSemiring.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
                    (@CommRing.toCommSemiring.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
                      (ZMod.commRing (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))))))
            a b))
        (@HMul.hMul.{0, 0, 0} Complex Complex Complex (@instHMul.{0} Complex Complex.instMul) (bank i a) (bank i b))) →
    (∀ (i : Fin k) (a : ZMod (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))),
        Or
          (@Eq.{1} Complex (bank i a)
            (@OfNat.ofNat.{0} Complex (nat_lit 1) (@One.toOfNat1.{0} Complex Complex.instOne)))
          (@Eq.{1} Complex (bank i a)
            (@Neg.neg.{0} Complex Complex.instNeg
              (@OfNat.ofNat.{0} Complex (nat_lit 1) (@One.toOfNat1.{0} Complex Complex.instOne))))) →
      Not
        (@Function.Injective.{1, 1} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
          (Fin k → Complex) fun a i => bank i a) := @_root_.Couret.STROBO2TORS.p2m_local_recoh_zmod4_sign_bank_not_injective

