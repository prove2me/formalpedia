-- Prove2me | solution 1 for Couret.STROBO2TORS.recoh_binary_information_set_additive
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T19:49:12.957253+00:00
-- url     : https://prove2.me/submissions/95ce0f4c-1e98-4542-bbc4-01ace0cdb385

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
import Theorems.Thm_Couret_STROBO2TORS_recoh_binary_information_set_linear
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





/-- The binary information-set theorem transports back to any
elementary abelian 2-group with an explicit coordinate equivalence. -/
theorem p2m_local_recoh_binary_information_set_additive
    {H : Type*} [AddCommGroup H]
    (r k : ℕ)
    (e : H ≃+ (Fin r → ZMod 2))
    (binary : Fin k → H →+ ZMod 2)
    (hinj : Function.Injective
      (fun a : H => fun i : Fin k => binary i a)) :
    ∃ pivot : Fin r → Fin k,
      Function.Injective pivot ∧
      Function.Surjective
        (fun a : H => fun j : Fin r => binary (pivot j) a) := by
  classical
  let bank := recoh_binary_bank_linear r k e binary
  have hlin : Function.Injective
      (fun x : Fin r → ZMod 2 => fun i : Fin k => bank i x) := by
    intro x y hxy
    have h : e.symm x = e.symm y := hinj (by
      funext i
      have hi := congrArg (fun f : Fin k → ZMod 2 => f i) hxy
      exact hi)
    exact e.symm.injective h
  obtain ⟨pivot, hpiv, hsurj⟩ :=
    recoh_binary_information_set_linear r k bank hlin
  refine ⟨pivot, hpiv, ?_⟩
  intro target
  obtain ⟨x, hx⟩ := hsurj target
  refine ⟨e.symm x, ?_⟩
  exact hx





end Couret.STROBO2TORS



universe p2m_u_0
theorem solution : ∀ {H : Type p2m_u_0} [inst : AddCommGroup.{p2m_u_0} H] (r k : Nat)
  (e :
    @AddEquiv.{p2m_u_0, 0} H (Fin r → ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@AddCommMagma.toAdd.{p2m_u_0} H
        (@AddCommSemigroup.toAddCommMagma.{p2m_u_0} H
          (@AddCommMonoid.toAddCommSemigroup.{p2m_u_0} H (@AddCommGroup.toAddCommMonoid.{p2m_u_0} H inst))))
      (@Pi.instAdd.{0, 0} (Fin r) (fun a => ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) fun i =>
        @Distrib.toAdd.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@instDistribOfSemiring.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
            (@DivisionSemiring.toSemiring.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
              (@Semifield.toDivisionSemiring.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                (@Field.toSemifield.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                  (@ZMod.instField (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                    Nat.fact_prime_two)))))))
  (binary :
    Fin k →
      @AddMonoidHom.{p2m_u_0, 0} H (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@AddZeroClass.toAddZero.{p2m_u_0} H
          (@AddMonoid.toAddZeroClass.{p2m_u_0} H
            (@SubNegMonoid.toAddMonoid.{p2m_u_0} H
              (@AddGroup.toSubNegMonoid.{p2m_u_0} H (@AddCommGroup.toAddGroup.{p2m_u_0} H inst)))))
        (@AddZeroClass.toAddZero.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@AddMonoid.toAddZeroClass.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
            (@AddMonoidWithOne.toAddMonoid.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
              (@AddGroupWithOne.toAddMonoidWithOne.{0}
                (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                (@Ring.toAddGroupWithOne.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                  (@DivisionRing.toRing.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                    (@Field.toDivisionRing.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                      (@ZMod.instField (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                        Nat.fact_prime_two))))))))),
  (@Function.Injective.{p2m_u_0 + 1, 1} H (Fin k → ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      fun a i =>
      @DFunLike.coe.{p2m_u_0 + 1, p2m_u_0 + 1, 1}
        (@AddMonoidHom.{p2m_u_0, 0} H (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@AddZeroClass.toAddZero.{p2m_u_0} H
            (@AddMonoid.toAddZeroClass.{p2m_u_0} H
              (@SubNegMonoid.toAddMonoid.{p2m_u_0} H
                (@AddGroup.toSubNegMonoid.{p2m_u_0} H (@AddCommGroup.toAddGroup.{p2m_u_0} H inst)))))
          (@AddZeroClass.toAddZero.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
            (@AddMonoid.toAddZeroClass.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
              (@AddMonoidWithOne.toAddMonoid.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                (@AddGroupWithOne.toAddMonoidWithOne.{0}
                  (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                  (@Ring.toAddGroupWithOne.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                    (@DivisionRing.toRing.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                      (@Field.toDivisionRing.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                        (@ZMod.instField (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                          Nat.fact_prime_two)))))))))
        H (fun x => ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@AddMonoidHom.instFunLike.{p2m_u_0, 0} H (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@AddZeroClass.toAddZero.{p2m_u_0} H
            (@AddMonoid.toAddZeroClass.{p2m_u_0} H
              (@SubNegMonoid.toAddMonoid.{p2m_u_0} H
                (@AddGroup.toSubNegMonoid.{p2m_u_0} H (@AddCommGroup.toAddGroup.{p2m_u_0} H inst)))))
          (@AddZeroClass.toAddZero.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
            (@AddMonoid.toAddZeroClass.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
              (@AddMonoidWithOne.toAddMonoid.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                (@AddGroupWithOne.toAddMonoidWithOne.{0}
                  (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                  (@Ring.toAddGroupWithOne.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                    (@DivisionRing.toRing.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                      (@Field.toDivisionRing.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                        (@ZMod.instField (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                          Nat.fact_prime_two)))))))))
        (binary i) a) →
    @Exists.{1} (Fin r → Fin k) fun pivot =>
      And (@Function.Injective.{1, 1} (Fin r) (Fin k) pivot)
        (@Function.Surjective.{p2m_u_0 + 1, 1} H
          (Fin r → ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) fun a j =>
          @DFunLike.coe.{p2m_u_0 + 1, p2m_u_0 + 1, 1}
            (@AddMonoidHom.{p2m_u_0, 0} H (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
              (@AddZeroClass.toAddZero.{p2m_u_0} H
                (@AddMonoid.toAddZeroClass.{p2m_u_0} H
                  (@SubNegMonoid.toAddMonoid.{p2m_u_0} H
                    (@AddGroup.toSubNegMonoid.{p2m_u_0} H (@AddCommGroup.toAddGroup.{p2m_u_0} H inst)))))
              (@AddZeroClass.toAddZero.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                (@AddMonoid.toAddZeroClass.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                  (@AddMonoidWithOne.toAddMonoid.{0}
                    (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                    (@AddGroupWithOne.toAddMonoidWithOne.{0}
                      (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                      (@Ring.toAddGroupWithOne.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                        (@DivisionRing.toRing.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                          (@Field.toDivisionRing.{0}
                            (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                            (@ZMod.instField (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                              Nat.fact_prime_two)))))))))
            H (fun x => ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
            (@AddMonoidHom.instFunLike.{p2m_u_0, 0} H
              (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
              (@AddZeroClass.toAddZero.{p2m_u_0} H
                (@AddMonoid.toAddZeroClass.{p2m_u_0} H
                  (@SubNegMonoid.toAddMonoid.{p2m_u_0} H
                    (@AddGroup.toSubNegMonoid.{p2m_u_0} H (@AddCommGroup.toAddGroup.{p2m_u_0} H inst)))))
              (@AddZeroClass.toAddZero.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                (@AddMonoid.toAddZeroClass.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                  (@AddMonoidWithOne.toAddMonoid.{0}
                    (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                    (@AddGroupWithOne.toAddMonoidWithOne.{0}
                      (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                      (@Ring.toAddGroupWithOne.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                        (@DivisionRing.toRing.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                          (@Field.toDivisionRing.{0}
                            (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                            (@ZMod.instField (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                              Nat.fact_prime_two)))))))))
            (binary (pivot j)) a) := @_root_.Couret.STROBO2TORS.p2m_local_recoh_binary_information_set_additive

