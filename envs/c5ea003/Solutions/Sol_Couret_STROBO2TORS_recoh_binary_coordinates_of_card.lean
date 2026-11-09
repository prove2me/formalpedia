-- Prove2me | solution 1 for Couret.STROBO2TORS.recoh_binary_coordinates_of_card
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T19:49:02.089553+00:00
-- url     : https://prove2.me/submissions/27af49a8-03b0-4985-9a7e-e9efce4bd77e

import Aesop
import Definitions.Def_Couret_RecohBinaryLinearTransport_ea1ab9036ae4
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Module.ZMod
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finiteness
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Definitions.Def_Couret_RecohRankKernel_9b83850e485b
import Mathlib.Algebra.Module.ZMod
import Mathlib.FieldTheory.Finiteness

set_option autoImplicit false

/-!
RECOH: transport of binary additive characters to linear probes.
Research candidate. No global B(G) claim. The additive equivalence
assumption is essential: do not apply this to C2 × C4 as a whole.
-/

namespace Couret.STROBO2TORS







/-- Cardinality determines the binary dimension. The scalar structure is
constructed from the exponent condition, not assumed independently. -/
theorem p2m_local_recoh_binary_coordinates_of_card
    {H : Type*} [AddCommGroup H] [Fintype H]
    (r : ℕ) (h2 : ∀ a : H, a + a = 0)
    (hcardH : Fintype.card H = 2 ^ r) :
    Nonempty (H ≃+ (Fin r → ZMod 2)) := by
  classical
  letI : Module (ZMod 2) H := AddCommGroup.zmodModule
    (n := 2) (fun a => by simpa only [two_nsmul] using h2 a)
  have hdim : Module.finrank (ZMod 2) H = r := by
    apply Nat.pow_right_injective (by decide : 2 ≤ 2)
    calc
      2 ^ Module.finrank (ZMod 2) H = Fintype.card H := by
        simpa only [ZMod.card] using
          (Module.card_eq_pow_finrank (K := ZMod 2) (V := H)).symm
      _ = 2 ^ r := hcardH
  exact ⟨(Module.finBasisOfFinrankEq (ZMod 2) H hdim).equivFun.toAddEquiv⟩



end Couret.STROBO2TORS



universe p2m_u_0
theorem solution : ∀ {H : Type p2m_u_0} [inst : AddCommGroup.{p2m_u_0} H] [inst_1 : Fintype.{p2m_u_0} H] (r : Nat),
  (∀ (a : H),
      @Eq.{p2m_u_0 + 1} H
        (@HAdd.hAdd.{p2m_u_0, p2m_u_0, p2m_u_0} H H H
          (@instHAdd.{p2m_u_0} H
            (@AddCommMagma.toAdd.{p2m_u_0} H
              (@AddCommSemigroup.toAddCommMagma.{p2m_u_0} H
                (@AddCommMonoid.toAddCommSemigroup.{p2m_u_0} H (@AddCommGroup.toAddCommMonoid.{p2m_u_0} H inst)))))
          a a)
        (@OfNat.ofNat.{p2m_u_0} H (nat_lit 0)
          (@Zero.toOfNat0.{p2m_u_0} H
            (@NegZeroClass.toZero.{p2m_u_0} H
              (@SubNegZeroMonoid.toNegZeroClass.{p2m_u_0} H
                (@SubtractionMonoid.toSubNegZeroMonoid.{p2m_u_0} H
                  (@SubtractionCommMonoid.toSubtractionMonoid.{p2m_u_0} H
                    (@AddCommGroup.toDivisionAddCommMonoid.{p2m_u_0} H inst)))))))) →
    @Eq.{1} Nat (@Fintype.card.{p2m_u_0} H inst_1)
        (@HPow.hPow.{0, 0, 0} Nat Nat Nat (@instHPow.{0, 0} Nat Nat (@Monoid.toPow.{0} Nat Nat.instMonoid))
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) r) →
      Nonempty.{p2m_u_0 + 1}
        (@AddEquiv.{p2m_u_0, 0} H (Fin r → ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@AddCommMagma.toAdd.{p2m_u_0} H
            (@AddCommSemigroup.toAddCommMagma.{p2m_u_0} H
              (@AddCommMonoid.toAddCommSemigroup.{p2m_u_0} H (@AddCommGroup.toAddCommMonoid.{p2m_u_0} H inst))))
          (@Pi.instAdd.{0, 0} (Fin r) (fun a => ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
            fun i =>
            @Distrib.toAdd.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
              (@instDistribOfSemiring.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                (@DivisionSemiring.toSemiring.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                  (@Semifield.toDivisionSemiring.{0}
                    (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                    (@Field.toSemifield.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                      (@ZMod.instField (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                        Nat.fact_prime_two))))))) := @_root_.Couret.STROBO2TORS.p2m_local_recoh_binary_coordinates_of_card

