-- Prove2me | solution 1 for Couret.STROBO2TORS.recoh_exists_primary_translation_recovery
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:54:41.778117+00:00
-- url     : https://prove2.me/submissions/9774fcea-623b-4668-9f03-00bb6f77a16e

import Aesop
import Definitions.Def_Couret_RecohSignRecovery_71a8a4a1ce8a
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
import Theorems.Thm_Couret_STROBO2TORS_recoh_sign_coordinates_of_separating_bank
import Theorems.Thm_Couret_STROBO2TORS_recoh_two_primary_characters_of_card
import Theorems.Thm_Couret_STROBO2TORS_recoh_two_primary_support_probe_nonzero
import Definitions.Def_Couret_RecohOptimalBank_e8b60aaa0883
import Mathlib.Tactic.FinCases

set_option autoImplicit false

/-!
Direct recovery of the unknown two-torsion translation from the signs of
nonzero character readings.  The recovered coordinates are explicit: a
coordinate is zero when the observed and base readings agree, and one
otherwise.  Accepted readings must equal the base reading or its negative.

This module proves both completeness for actual translated observations and
soundness for accepted signs.  It also constructs compatible coordinates for
a separating bank of the minimum size, and instantiates such a bank with the
already proved two-primary character construction.  Three-primary readings
are proved invariant under every recovered two-torsion translation.

Equality of complex values and the inverse coordinate map are noncomputable
here.  No executable arithmetic on cyclotomic representations, running-time
bound, or extraction of a Python implementation is claimed by this module.
-/

namespace Couret.STROBO2TORS







variable {G : Type*} [AddCommGroup G] {r : ℕ}

local notation "H₂" => recohTorsionSubgroup (G := G) 2





variable [DecidableEq G]











variable [Fintype G]





/-- The previously proved primary-character construction provides both
nonvanishing triple readings and compatible sign coordinates. -/
theorem recoh_exists_primary_sign_coordinates
    (r : ℕ) (hcard : Nat.card H₂ = 2 ^ r) :
    ∃ (bank : Fin r → AddChar G ℂ) (e : H₂ ≃+ (Fin r → ZMod 2)),
      (∀ i x, ∃ n : ℕ, (bank i x) ^ (2 ^ n) = 1) ∧
      (∀ (u : H₂) (i : Fin r),
        bank i (u : G) = if e u i = 0 then 1 else -1) ∧
      (∀ i (S : Finset G), S.card = 3 → recohSupportProbe (bank i) S ≠ 0) := by
  obtain ⟨bank, hprimary, hsep⟩ := recoh_two_primary_characters_of_card r hcard
  obtain ⟨e, hcoord⟩ := recoh_sign_coordinates_of_separating_bank r hcard bank hsep
  exact ⟨bank, e, hprimary, hcoord,
    fun i S hS => recoh_two_primary_support_probe_nonzero (bank i) (hprimary i) S hS⟩

/-- Direct sign recovery is available for every finite abelian group from
the two-torsion cardinality alone, including the zero-rank case. -/
theorem p2m_local_recoh_exists_primary_translation_recovery
    (r : ℕ) (hcard : Nat.card H₂ = 2 ^ r) :
    ∃ (bank : Fin r → AddChar G ℂ) (e : H₂ ≃+ (Fin r → ZMod 2)),
      (∀ i x, ∃ n : ℕ, (bank i x) ^ (2 ^ n) = 1) ∧
      (∀ (u : H₂) (i : Fin r),
        bank i (u : G) = if e u i = 0 then 1 else -1) ∧
      (∀ (S : Finset G), S.card = 3 → ∀ u : H₂,
        recohRecoverTranslation e
          (fun i => recohSupportProbe (bank i) S)
          (fun i => recohSupportProbe (bank i) (translateSupport S (u : G))) = u) := by
  obtain ⟨bank, e, hprimary, hcoord, hnonzero⟩ :=
    recoh_exists_primary_sign_coordinates r hcard
  exact ⟨bank, e, hprimary, hcoord,
    fun S hS u => recoh_recover_translation_eq bank e hcoord S
      (fun i => hnonzero i S hS) u⟩

end Couret.STROBO2TORS


universe p2m_u_0
theorem solution : ∀ {G : Type p2m_u_0} [inst : AddCommGroup.{p2m_u_0} G] [inst_1 : DecidableEq.{p2m_u_0 + 1} G] [Fintype.{p2m_u_0} G]
  (r : Nat),
  @Eq.{1} Nat
      (Nat.card.{p2m_u_0}
        (@Subtype.{p2m_u_0 + 1} G fun x =>
          @Membership.mem.{p2m_u_0, p2m_u_0} G (@AddSubgroup.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst))
            (@SetLike.instMembership.{p2m_u_0, p2m_u_0}
              (@AddSubgroup.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)) G
              (@AddSubgroup.instSetLike.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)))
            (@Couret.STROBO2TORS.recohTorsionSubgroup.{p2m_u_0} G inst
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
            x))
      (@HPow.hPow.{0, 0, 0} Nat Nat Nat (@instHPow.{0, 0} Nat Nat (@Monoid.toPow.{0} Nat Nat.instMonoid))
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) r) →
    @Exists.{p2m_u_0 + 1}
      (Fin r →
        @AddChar.{p2m_u_0, 0} G
          (@SubNegMonoid.toAddMonoid.{p2m_u_0} G
            (@AddGroup.toSubNegMonoid.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)))
          Complex (@Semiring.toMonoid.{0} Complex Complex.instSemiring))
      fun bank =>
      @Exists.{p2m_u_0 + 1}
        (@AddEquiv.{p2m_u_0, 0}
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
          (@Pi.instAdd.{0, 0} (Fin r) (fun a => ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
            fun i =>
            @Distrib.toAdd.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
              (@instDistribOfSemiring.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                (@DivisionSemiring.toSemiring.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                  (@Semifield.toDivisionSemiring.{0}
                    (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                    (@Field.toSemifield.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                      (@ZMod.instField (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                        Nat.fact_prime_two)))))))
        fun e =>
        And
          (∀ (i : Fin r) (x : G),
            @Exists.{1} Nat fun n =>
              @Eq.{1} Complex
                (@HPow.hPow.{0, 0, 0} Complex Nat Complex
                  (@instHPow.{0, 0} Complex Nat
                    (@Monoid.toPow.{0} Complex (@Semiring.toMonoid.{0} Complex Complex.instSemiring)))
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
                    (bank i) x)
                  (@HPow.hPow.{0, 0, 0} Nat Nat Nat (@instHPow.{0, 0} Nat Nat (@Monoid.toPow.{0} Nat Nat.instMonoid))
                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) n))
                (@OfNat.ofNat.{0} Complex (nat_lit 1) (@One.toOfNat1.{0} Complex Complex.instOne)))
          (And
            (∀
              (u :
                @Subtype.{p2m_u_0 + 1} G fun x =>
                  @Membership.mem.{p2m_u_0, p2m_u_0} G
                    (@AddSubgroup.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst))
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
                  (bank i)
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
                            (@instDistribOfSemiring.{0}
                              (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                              (@DivisionSemiring.toSemiring.{0}
                                (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                (@Semifield.toDivisionSemiring.{0}
                                  (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                  (@Field.toSemifield.{0}
                                    (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
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
                              (@instDistribOfSemiring.{0}
                                (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                (@DivisionSemiring.toSemiring.{0}
                                  (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                  (@Semifield.toDivisionSemiring.{0}
                                    (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                    (@Field.toSemifield.{0}
                                      (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
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
                              (@instDistribOfSemiring.{0}
                                (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                (@DivisionSemiring.toSemiring.{0}
                                  (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                  (@Semifield.toDivisionSemiring.{0}
                                    (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                    (@Field.toSemifield.{0}
                                      (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                      (@ZMod.instField (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                        Nat.fact_prime_two))))))))
                      e u i)
                    (@OfNat.ofNat.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) (nat_lit 0)
                      (@Zero.toOfNat0.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                        (@MulZeroClass.toZero.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                          (@instMulZeroClassOfSemiring.{0}
                            (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                            (@DivisionSemiring.toSemiring.{0}
                              (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                              (@Semifield.toDivisionSemiring.{0}
                                (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                (@Field.toSemifield.{0}
                                  (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
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
                            (@instDistribOfSemiring.{0}
                              (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                              (@DivisionSemiring.toSemiring.{0}
                                (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                (@Semifield.toDivisionSemiring.{0}
                                  (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                  (@Field.toSemifield.{0}
                                    (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
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
                              (@instDistribOfSemiring.{0}
                                (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                (@DivisionSemiring.toSemiring.{0}
                                  (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                  (@Semifield.toDivisionSemiring.{0}
                                    (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                    (@Field.toSemifield.{0}
                                      (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
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
                              (@instDistribOfSemiring.{0}
                                (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                (@DivisionSemiring.toSemiring.{0}
                                  (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                  (@Semifield.toDivisionSemiring.{0}
                                    (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                    (@Field.toSemifield.{0}
                                      (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                      (@ZMod.instField (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                        Nat.fact_prime_two))))))))
                      e u i)
                    (@OfNat.ofNat.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) (nat_lit 0)
                      (@Zero.toOfNat0.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                        (@MulZeroClass.toZero.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                          (@instMulZeroClassOfSemiring.{0}
                            (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                            (@DivisionSemiring.toSemiring.{0}
                              (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                              (@Semifield.toDivisionSemiring.{0}
                                (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                (@Field.toSemifield.{0}
                                  (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                  (@ZMod.instField (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                    Nat.fact_prime_two)))))))))
                  (@OfNat.ofNat.{0} Complex (nat_lit 1) (@One.toOfNat1.{0} Complex Complex.instOne))
                  (@Neg.neg.{0} Complex Complex.instNeg
                    (@OfNat.ofNat.{0} Complex (nat_lit 1) (@One.toOfNat1.{0} Complex Complex.instOne)))))
            (∀ (S : Finset.{p2m_u_0} G),
              @Eq.{1} Nat (@Finset.card.{p2m_u_0} G S) (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) →
                ∀
                  (u :
                    @Subtype.{p2m_u_0 + 1} G fun x =>
                      @Membership.mem.{p2m_u_0, p2m_u_0} G
                        (@AddSubgroup.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst))
                        (@SetLike.instMembership.{p2m_u_0, p2m_u_0}
                          (@AddSubgroup.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)) G
                          (@AddSubgroup.instSetLike.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)))
                        (@Couret.STROBO2TORS.recohTorsionSubgroup.{p2m_u_0} G inst
                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                        x),
                  @Eq.{p2m_u_0 + 1}
                    (@Subtype.{p2m_u_0 + 1} G fun x =>
                      @Membership.mem.{p2m_u_0, p2m_u_0} G
                        (@AddSubgroup.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst))
                        (@SetLike.instMembership.{p2m_u_0, p2m_u_0}
                          (@AddSubgroup.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)) G
                          (@AddSubgroup.instSetLike.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)))
                        (@Couret.STROBO2TORS.recohTorsionSubgroup.{p2m_u_0} G inst
                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                        x)
                    (@Couret.STROBO2TORS.recohRecoverTranslation.{p2m_u_0} G inst r e
                      (fun i => @Couret.STROBO2TORS.recohSupportProbe.{p2m_u_0} G inst (bank i) S) fun i =>
                      @Couret.STROBO2TORS.recohSupportProbe.{p2m_u_0} G inst (bank i)
                        (@Couret.STROBO2TORS.translateSupport.{p2m_u_0} G inst inst_1 S
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
                            u)))
                    u)) := @_root_.Couret.STROBO2TORS.p2m_local_recoh_exists_primary_translation_recovery

