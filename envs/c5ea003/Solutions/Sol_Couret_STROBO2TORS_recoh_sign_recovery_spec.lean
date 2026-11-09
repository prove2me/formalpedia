-- Prove2me | solution 1 for Couret.STROBO2TORS.recoh_sign_recovery_spec
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:42:39.562049+00:00
-- url     : https://prove2.me/submissions/1501532e-caf8-4a1c-9535-ad35254ddb08

import Aesop
import Definitions.Def_Couret_RecohFastDecoder_5bb89f11acce
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Group.AddChar
import Mathlib.Algebra.Module.ZMod
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finiteness
import Mathlib.GroupTheory.FiniteAbelian.Duality
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Choose
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_STROBO2TORS_recoh_recover_translation_eq
import Definitions.Def_Couret_RecohDecoderBounds_60ec29457baa
import Definitions.Def_Couret_RecohCyclicHalves_383c4510168a
import Definitions.Def_Couret_RecohSignRecovery_71a8a4a1ce8a

set_option autoImplicit false

/-!
One-representative RECOH decoder on an explicitly supplied finite support.

The construction visits only the three-element subsets of U.  A supplied
doubling solver chooses one half-sum for each feasible edge set, and a
translation-recovery function turns the corresponding representative into
one candidate.  The final filter uses the complete labelled observation.
No enumeration of the ambient group or its two-torsion subgroup occurs in
these definitions.  Their construction needs no Fintype instance on G.

The refinement theorem proves equality with recohExactDecoder, provided U
covers the observed square support and the half-sum and recovery contracts
hold.  Sign recovery supplies the recovery contract for binary coordinates
inside any larger labelled character bank.  Complex equality remains
noncomputable here: this is a Lean refinement of the mathematical decoder,
not a verification of the external Python parser or arithmetic runtime.
-/

namespace Couret.STROBO2TORS

open scoped BigOperators

variable {G : Type*} [AddCommGroup G] [DecidableEq G]





































section FiniteRefinement

variable [Fintype G]









end FiniteRefinement

variable {r : ℕ}

local notation "H₂" => recohTorsionSubgroup (G := G) 2



theorem recoh_sign_recover_support_card
    (bank : Fin r → AddChar G ℂ) (e : H₂ ≃+ (Fin r → ZMod 2))
    (obs : Fin r → ℂ) (B : Finset G) :
    (recohSignRecoverSupport bank e obs B).card = B.card :=
  translateSupport_card B _

theorem recoh_sign_recover_support_of_readings
    (bank : Fin r → AddChar G ℂ) (e : H₂ ≃+ (Fin r → ZMod 2))
    (hcoord : ∀ (u : H₂) (i : Fin r),
      bank i (u : G) = if e u i = 0 then 1 else -1)
    (B : Finset G) (hnonzero : ∀ i, recohSupportProbe (bank i) B ≠ 0)
    (u : H₂) (obs : Fin r → ℂ)
    (hobs : ∀ i, recohSupportProbe (bank i) (translateSupport B (u : G)) = obs i) :
    recohSignRecoverSupport bank e obs B = translateSupport B (u : G) := by
  have hfun : obs =
      (fun i => recohSupportProbe (bank i) (translateSupport B (u : G))) :=
    funext (fun i => (hobs i).symm)
  unfold recohSignRecoverSupport
  rw [hfun, recoh_recover_translation_eq bank e hcoord B hnonzero u]

/-- Binary coordinates may occur at any specified indices of the full
labelled bank.  Their sign recovery satisfies the generic recovery contract;
all remaining readings are retained in the decoder's final exact filter. -/
theorem p2m_local_recoh_sign_recovery_spec {I : Type*}
    (bank : I → AddChar G ℂ) (obs : (G → ℕ) × (I → ℂ))
    (index : Fin r → I) (e : H₂ ≃+ (Fin r → ZMod 2))
    (hcoord : ∀ (u : H₂) (i : Fin r),
      bank (index i) (u : G) = if e u i = 0 then 1 else -1)
    (hnonzero : ∀ i (B : Finset G), B.card = 3 →
      recohSupportProbe (bank (index i)) B ≠ 0) :
    RecohTranslationRecoverySpec bank obs
      (recohSignRecoverSupport (fun i => bank (index i)) e (fun i => obs.2 (index i))) := by
  constructor
  · intro B hB
    rw [recoh_sign_recover_support_card, hB]
  · intro B hB u hu hobs
    let u2 : H₂ := ⟨u, by simpa only [recoh_mem_torsion_subgroup, two_nsmul] using hu⟩
    apply recoh_sign_recover_support_of_readings (fun i => bank (index i)) e hcoord B
      (fun i => hnonzero i B hB) u2 (fun i => obs.2 (index i))
    intro i
    exact congrFun (congrArg Prod.snd hobs) (index i)



end Couret.STROBO2TORS


universe p2m_u_0 p2m_u_1
theorem solution : ∀ {G : Type p2m_u_0} [inst : AddCommGroup.{p2m_u_0} G] [inst_1 : DecidableEq.{p2m_u_0 + 1} G] {r : Nat}
  {I : Type p2m_u_1}
  (bank :
    I →
      @AddChar.{p2m_u_0, 0} G
        (@SubNegMonoid.toAddMonoid.{p2m_u_0} G
          (@AddGroup.toSubNegMonoid.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)))
        Complex (@Semiring.toMonoid.{0} Complex Complex.instSemiring))
  (obs : Prod.{p2m_u_0, p2m_u_1} (G → Nat) (I → Complex)) (index : Fin r → I)
  (e :
    @AddEquiv.{p2m_u_0, 0}
      (@Subtype.{p2m_u_0 + 1} G fun x =>
        @Membership.mem.{p2m_u_0, p2m_u_0} G (@AddSubgroup.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst))
          (@SetLike.instMembership.{p2m_u_0, p2m_u_0}
            (@AddSubgroup.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)) G
            (@AddSubgroup.instSetLike.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)))
          (@Couret.STROBO2TORS.recohTorsionSubgroup.{p2m_u_0} G inst
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          x)
      (Fin r → ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@AddSubgroup.add.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)
        (@Couret.STROBO2TORS.recohTorsionSubgroup.{p2m_u_0} G inst
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@Pi.instAdd.{0, 0} (Fin r) (fun a => ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) fun i =>
        @Distrib.toAdd.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@instDistribOfSemiring.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
            (@DivisionSemiring.toSemiring.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
              (@Semifield.toDivisionSemiring.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                (@Field.toSemifield.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                  (@ZMod.instField (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                    Nat.fact_prime_two))))))),
  (∀
      (u :
        @Subtype.{p2m_u_0 + 1} G fun x =>
          @Membership.mem.{p2m_u_0, p2m_u_0} G (@AddSubgroup.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst))
            (@SetLike.instMembership.{p2m_u_0, p2m_u_0}
              (@AddSubgroup.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)) G
              (@AddSubgroup.instSetLike.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)))
            (@Couret.STROBO2TORS.recohTorsionSubgroup.{p2m_u_0} G inst
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
            x)
      (i : Fin r),
      @Eq.{1} Complex
        (@DFunLike.coe.{p2m_u_0 + 1, p2m_u_0 + 1, 1}
          (@AddChar.{p2m_u_0, 0} G
            (@SubNegMonoid.toAddMonoid.{p2m_u_0} G
              (@AddGroup.toSubNegMonoid.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)))
            Complex (@Semiring.toMonoid.{0} Complex Complex.instSemiring))
          G (fun x => Complex)
          (@AddChar.instFunLike.{p2m_u_0, 0} G Complex
            (@SubNegMonoid.toAddMonoid.{p2m_u_0} G
              (@AddGroup.toSubNegMonoid.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)))
            (@Semiring.toMonoid.{0} Complex Complex.instSemiring))
          (bank (index i))
          (@Subtype.val.{p2m_u_0 + 1} G
            (fun x =>
              @Membership.mem.{p2m_u_0, p2m_u_0} G
                (@AddSubgroup.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst))
                (@SetLike.instMembership.{p2m_u_0, p2m_u_0}
                  (@AddSubgroup.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)) G
                  (@AddSubgroup.instSetLike.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)))
                (@Couret.STROBO2TORS.recohTorsionSubgroup.{p2m_u_0} G inst
                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                x)
            u))
        (@ite.{1} Complex
          (@Eq.{1} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
            (@DFunLike.coe.{p2m_u_0 + 1, p2m_u_0 + 1, 1}
              (@AddEquiv.{p2m_u_0, 0}
                (@Subtype.{p2m_u_0 + 1} G fun x =>
                  @Membership.mem.{p2m_u_0, p2m_u_0} G
                    (@AddSubgroup.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst))
                    (@SetLike.instMembership.{p2m_u_0, p2m_u_0}
                      (@AddSubgroup.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)) G
                      (@AddSubgroup.instSetLike.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)))
                    (@Couret.STROBO2TORS.recohTorsionSubgroup.{p2m_u_0} G inst
                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                    x)
                (Fin r → ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                (@AddSubgroup.add.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)
                  (@Couret.STROBO2TORS.recohTorsionSubgroup.{p2m_u_0} G inst
                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                (@Pi.instAdd.{0, 0} (Fin r)
                  (fun a => ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) fun i =>
                  @Distrib.toAdd.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                    (@instDistribOfSemiring.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                      (@DivisionSemiring.toSemiring.{0}
                        (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                        (@Semifield.toDivisionSemiring.{0}
                          (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                          (@Field.toSemifield.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                            (@ZMod.instField (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                              Nat.fact_prime_two)))))))
              (@Subtype.{p2m_u_0 + 1} G fun x =>
                @Membership.mem.{p2m_u_0, p2m_u_0} G
                  (@AddSubgroup.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst))
                  (@SetLike.instMembership.{p2m_u_0, p2m_u_0}
                    (@AddSubgroup.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)) G
                    (@AddSubgroup.instSetLike.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)))
                  (@Couret.STROBO2TORS.recohTorsionSubgroup.{p2m_u_0} G inst
                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                  x)
              (fun x => Fin r → ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
              (@EquivLike.toFunLike.{p2m_u_0 + 1, p2m_u_0 + 1, 1}
                (@AddEquiv.{p2m_u_0, 0}
                  (@Subtype.{p2m_u_0 + 1} G fun x =>
                    @Membership.mem.{p2m_u_0, p2m_u_0} G
                      (@AddSubgroup.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst))
                      (@SetLike.instMembership.{p2m_u_0, p2m_u_0}
                        (@AddSubgroup.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)) G
                        (@AddSubgroup.instSetLike.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)))
                      (@Couret.STROBO2TORS.recohTorsionSubgroup.{p2m_u_0} G inst
                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                      x)
                  (Fin r → ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                  (@AddSubgroup.add.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)
                    (@Couret.STROBO2TORS.recohTorsionSubgroup.{p2m_u_0} G inst
                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                  (@Pi.instAdd.{0, 0} (Fin r)
                    (fun a => ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) fun i =>
                    @Distrib.toAdd.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                      (@instDistribOfSemiring.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                        (@DivisionSemiring.toSemiring.{0}
                          (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                          (@Semifield.toDivisionSemiring.{0}
                            (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                            (@Field.toSemifield.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                              (@ZMod.instField (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                Nat.fact_prime_two)))))))
                (@Subtype.{p2m_u_0 + 1} G fun x =>
                  @Membership.mem.{p2m_u_0, p2m_u_0} G
                    (@AddSubgroup.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst))
                    (@SetLike.instMembership.{p2m_u_0, p2m_u_0}
                      (@AddSubgroup.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)) G
                      (@AddSubgroup.instSetLike.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)))
                    (@Couret.STROBO2TORS.recohTorsionSubgroup.{p2m_u_0} G inst
                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                    x)
                (Fin r → ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                (@AddEquiv.instEquivLike.{p2m_u_0, 0}
                  (@Subtype.{p2m_u_0 + 1} G fun x =>
                    @Membership.mem.{p2m_u_0, p2m_u_0} G
                      (@AddSubgroup.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst))
                      (@SetLike.instMembership.{p2m_u_0, p2m_u_0}
                        (@AddSubgroup.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)) G
                        (@AddSubgroup.instSetLike.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)))
                      (@Couret.STROBO2TORS.recohTorsionSubgroup.{p2m_u_0} G inst
                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                      x)
                  (Fin r → ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                  (@AddSubgroup.add.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)
                    (@Couret.STROBO2TORS.recohTorsionSubgroup.{p2m_u_0} G inst
                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                  (@Pi.instAdd.{0, 0} (Fin r)
                    (fun a => ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) fun i =>
                    @Distrib.toAdd.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                      (@instDistribOfSemiring.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                        (@DivisionSemiring.toSemiring.{0}
                          (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                          (@Semifield.toDivisionSemiring.{0}
                            (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                            (@Field.toSemifield.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                              (@ZMod.instField (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                Nat.fact_prime_two))))))))
              e u i)
            (@OfNat.ofNat.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) (nat_lit 0)
              (@Zero.toOfNat0.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                (@MulZeroClass.toZero.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                  (@instMulZeroClassOfSemiring.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                    (@DivisionSemiring.toSemiring.{0}
                      (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                      (@Semifield.toDivisionSemiring.{0}
                        (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                        (@Field.toSemifield.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                          (@ZMod.instField (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                            Nat.fact_prime_two)))))))))
          (ZMod.decidableEq (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
            (@DFunLike.coe.{p2m_u_0 + 1, p2m_u_0 + 1, 1}
              (@AddEquiv.{p2m_u_0, 0}
                (@Subtype.{p2m_u_0 + 1} G fun x =>
                  @Membership.mem.{p2m_u_0, p2m_u_0} G
                    (@AddSubgroup.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst))
                    (@SetLike.instMembership.{p2m_u_0, p2m_u_0}
                      (@AddSubgroup.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)) G
                      (@AddSubgroup.instSetLike.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)))
                    (@Couret.STROBO2TORS.recohTorsionSubgroup.{p2m_u_0} G inst
                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                    x)
                (Fin r → ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                (@AddSubgroup.add.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)
                  (@Couret.STROBO2TORS.recohTorsionSubgroup.{p2m_u_0} G inst
                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                (@Pi.instAdd.{0, 0} (Fin r)
                  (fun a => ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) fun i =>
                  @Distrib.toAdd.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                    (@instDistribOfSemiring.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                      (@DivisionSemiring.toSemiring.{0}
                        (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                        (@Semifield.toDivisionSemiring.{0}
                          (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                          (@Field.toSemifield.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                            (@ZMod.instField (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                              Nat.fact_prime_two)))))))
              (@Subtype.{p2m_u_0 + 1} G fun x =>
                @Membership.mem.{p2m_u_0, p2m_u_0} G
                  (@AddSubgroup.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst))
                  (@SetLike.instMembership.{p2m_u_0, p2m_u_0}
                    (@AddSubgroup.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)) G
                    (@AddSubgroup.instSetLike.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)))
                  (@Couret.STROBO2TORS.recohTorsionSubgroup.{p2m_u_0} G inst
                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                  x)
              (fun x => Fin r → ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
              (@EquivLike.toFunLike.{p2m_u_0 + 1, p2m_u_0 + 1, 1}
                (@AddEquiv.{p2m_u_0, 0}
                  (@Subtype.{p2m_u_0 + 1} G fun x =>
                    @Membership.mem.{p2m_u_0, p2m_u_0} G
                      (@AddSubgroup.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst))
                      (@SetLike.instMembership.{p2m_u_0, p2m_u_0}
                        (@AddSubgroup.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)) G
                        (@AddSubgroup.instSetLike.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)))
                      (@Couret.STROBO2TORS.recohTorsionSubgroup.{p2m_u_0} G inst
                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                      x)
                  (Fin r → ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                  (@AddSubgroup.add.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)
                    (@Couret.STROBO2TORS.recohTorsionSubgroup.{p2m_u_0} G inst
                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                  (@Pi.instAdd.{0, 0} (Fin r)
                    (fun a => ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) fun i =>
                    @Distrib.toAdd.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                      (@instDistribOfSemiring.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                        (@DivisionSemiring.toSemiring.{0}
                          (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                          (@Semifield.toDivisionSemiring.{0}
                            (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                            (@Field.toSemifield.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                              (@ZMod.instField (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                Nat.fact_prime_two)))))))
                (@Subtype.{p2m_u_0 + 1} G fun x =>
                  @Membership.mem.{p2m_u_0, p2m_u_0} G
                    (@AddSubgroup.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst))
                    (@SetLike.instMembership.{p2m_u_0, p2m_u_0}
                      (@AddSubgroup.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)) G
                      (@AddSubgroup.instSetLike.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)))
                    (@Couret.STROBO2TORS.recohTorsionSubgroup.{p2m_u_0} G inst
                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                    x)
                (Fin r → ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                (@AddEquiv.instEquivLike.{p2m_u_0, 0}
                  (@Subtype.{p2m_u_0 + 1} G fun x =>
                    @Membership.mem.{p2m_u_0, p2m_u_0} G
                      (@AddSubgroup.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst))
                      (@SetLike.instMembership.{p2m_u_0, p2m_u_0}
                        (@AddSubgroup.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)) G
                        (@AddSubgroup.instSetLike.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)))
                      (@Couret.STROBO2TORS.recohTorsionSubgroup.{p2m_u_0} G inst
                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                      x)
                  (Fin r → ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                  (@AddSubgroup.add.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)
                    (@Couret.STROBO2TORS.recohTorsionSubgroup.{p2m_u_0} G inst
                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                  (@Pi.instAdd.{0, 0} (Fin r)
                    (fun a => ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) fun i =>
                    @Distrib.toAdd.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                      (@instDistribOfSemiring.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                        (@DivisionSemiring.toSemiring.{0}
                          (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                          (@Semifield.toDivisionSemiring.{0}
                            (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                            (@Field.toSemifield.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                              (@ZMod.instField (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                Nat.fact_prime_two))))))))
              e u i)
            (@OfNat.ofNat.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) (nat_lit 0)
              (@Zero.toOfNat0.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                (@MulZeroClass.toZero.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                  (@instMulZeroClassOfSemiring.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                    (@DivisionSemiring.toSemiring.{0}
                      (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                      (@Semifield.toDivisionSemiring.{0}
                        (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                        (@Field.toSemifield.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                          (@ZMod.instField (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                            Nat.fact_prime_two)))))))))
          (@OfNat.ofNat.{0} Complex (nat_lit 1) (@One.toOfNat1.{0} Complex Complex.instOne))
          (@Neg.neg.{0} Complex Complex.instNeg
            (@OfNat.ofNat.{0} Complex (nat_lit 1) (@One.toOfNat1.{0} Complex Complex.instOne))))) →
    (∀ (i : Fin r) (B : Finset.{p2m_u_0} G),
        @Eq.{1} Nat (@Finset.card.{p2m_u_0} G B) (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) →
          @Ne.{1} Complex (@Couret.STROBO2TORS.recohSupportProbe.{p2m_u_0} G inst (bank (index i)) B)
            (@OfNat.ofNat.{0} Complex (nat_lit 0) (@Zero.toOfNat0.{0} Complex Complex.instZero))) →
      @Couret.STROBO2TORS.RecohTranslationRecoverySpec.{p2m_u_0, p2m_u_1} G inst inst_1 I bank obs
        (@Couret.STROBO2TORS.recohSignRecoverSupport.{p2m_u_0} G inst inst_1 r (fun i => bank (index i)) e fun i =>
          @Prod.snd.{p2m_u_0, p2m_u_1} (G → Nat) (I → Complex) obs (index i)) := @_root_.Couret.STROBO2TORS.p2m_local_recoh_sign_recovery_spec

