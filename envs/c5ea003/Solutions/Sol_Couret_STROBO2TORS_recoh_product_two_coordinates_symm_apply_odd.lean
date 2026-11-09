-- Prove2me | solution 1 for Couret.STROBO2TORS.recoh_product_two_coordinates_symm_apply_odd
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:56:40.501515+00:00
-- url     : https://prove2.me/submissions/7e0bee46-7e72-4dae-a494-9c184d6ba0ad

import Aesop
import Definitions.Def_Couret_RecohCyclicCoordinates_d669b2caaf1a
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
import Definitions.Def_Couret_RecohCyclicHalves_383c4510168a
import Mathlib.Tactic.FinCases

set_option autoImplicit false

/-!
Executable binary coordinates on the two-torsion of a product of cyclic
groups.  The coordinate type is the subtype of even factors.  Encoding tests
whether a cyclic coordinate is zero; decoding uses zero on odd factors and
either zero or q / 2 on even factors.  Neither direction chooses a basis or
enumerates the ambient group or its torsion subgroup.

The definitions below are computable Lean definitions.  Their formulas are
the coordinate shift formulas of the separate Python decoder; this module
does not certify the Python runtime or a parser for its input values.
-/

namespace Couret.STROBO2TORS























variable {d : ℕ} (q : Fin d → ℕ)





@[simp] theorem recoh_product_torsion_shift_odd
    (bits : RecohEvenCoordinate q → ZMod 2) (i : Fin d) (hi : ¬ 2 ∣ q i) :
    recohProductTorsionShift q bits i = 0 := by
  simp [recohProductTorsionShift, hi]











variable [∀ i, NeZero (q i)]













@[simp] theorem p2m_local_recoh_product_two_coordinates_symm_apply_odd
    (bits : RecohEvenCoordinate q → ZMod 2) (i : Fin d) (hi : ¬ 2 ∣ q i) :
    ((recohProductTwoCoordinates q).symm bits : (j : Fin d) → ZMod (q j)) i = 0 :=
  recoh_product_torsion_shift_odd q bits i hi

end Couret.STROBO2TORS


theorem solution : ∀ {d : Nat} (q : Fin d → Nat)
  [inst : ∀ (i : Fin d), @NeZero.{0} Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass) (q i)]
  (bits :
    @Couret.STROBO2TORS.RecohEvenCoordinate d q → ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
  (i : Fin d),
  Not (@Dvd.dvd.{0} Nat Nat.instDvd (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (q i)) →
    @Eq.{1} (ZMod (q i))
      (@Subtype.val.{1} ((i : Fin d) → ZMod (q i))
        (fun x =>
          @Membership.mem.{0, 0} ((i : Fin d) → ZMod (q i))
            (@AddSubgroup.{0} ((i : Fin d) → ZMod (q i))
              (@AddCommGroup.toAddGroup.{0} ((i : Fin d) → ZMod (q i))
                (@Pi.addCommGroup.{0, 0} (Fin d) (fun i => ZMod (q i)) fun i =>
                  @Ring.toAddCommGroup.{0} (ZMod (q i)) (@CommRing.toRing.{0} (ZMod (q i)) (ZMod.commRing (q i))))))
            (@SetLike.instMembership.{0, 0}
              (@AddSubgroup.{0} ((i : Fin d) → ZMod (q i))
                (@AddCommGroup.toAddGroup.{0} ((i : Fin d) → ZMod (q i))
                  (@Pi.addCommGroup.{0, 0} (Fin d) (fun i => ZMod (q i)) fun i =>
                    @Ring.toAddCommGroup.{0} (ZMod (q i)) (@CommRing.toRing.{0} (ZMod (q i)) (ZMod.commRing (q i))))))
              ((i : Fin d) → ZMod (q i))
              (@AddSubgroup.instSetLike.{0} ((i : Fin d) → ZMod (q i))
                (@AddCommGroup.toAddGroup.{0} ((i : Fin d) → ZMod (q i))
                  (@Pi.addCommGroup.{0, 0} (Fin d) (fun i => ZMod (q i)) fun i =>
                    @Ring.toAddCommGroup.{0} (ZMod (q i)) (@CommRing.toRing.{0} (ZMod (q i)) (ZMod.commRing (q i)))))))
            (@Couret.STROBO2TORS.recohTorsionSubgroup.{0} ((i : Fin d) → ZMod (q i))
              (@Pi.addCommGroup.{0, 0} (Fin d) (fun i => ZMod (q i)) fun i =>
                @Ring.toAddCommGroup.{0} (ZMod (q i)) (@CommRing.toRing.{0} (ZMod (q i)) (ZMod.commRing (q i))))
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
            x)
        (@DFunLike.coe.{1, 1, 1}
          (@AddEquiv.{0, 0}
            (@Couret.STROBO2TORS.RecohEvenCoordinate d q →
              ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
            (@Subtype.{1} ((i : Fin d) → ZMod (q i)) fun x =>
              @Membership.mem.{0, 0} ((i : Fin d) → ZMod (q i))
                (@AddSubgroup.{0} ((i : Fin d) → ZMod (q i))
                  (@AddCommGroup.toAddGroup.{0} ((i : Fin d) → ZMod (q i))
                    (@Pi.addCommGroup.{0, 0} (Fin d) (fun i => ZMod (q i)) fun i =>
                      @Ring.toAddCommGroup.{0} (ZMod (q i)) (@CommRing.toRing.{0} (ZMod (q i)) (ZMod.commRing (q i))))))
                (@SetLike.instMembership.{0, 0}
                  (@AddSubgroup.{0} ((i : Fin d) → ZMod (q i))
                    (@AddCommGroup.toAddGroup.{0} ((i : Fin d) → ZMod (q i))
                      (@Pi.addCommGroup.{0, 0} (Fin d) (fun i => ZMod (q i)) fun i =>
                        @Ring.toAddCommGroup.{0} (ZMod (q i))
                          (@CommRing.toRing.{0} (ZMod (q i)) (ZMod.commRing (q i))))))
                  ((i : Fin d) → ZMod (q i))
                  (@AddSubgroup.instSetLike.{0} ((i : Fin d) → ZMod (q i))
                    (@AddCommGroup.toAddGroup.{0} ((i : Fin d) → ZMod (q i))
                      (@Pi.addCommGroup.{0, 0} (Fin d) (fun i => ZMod (q i)) fun i =>
                        @Ring.toAddCommGroup.{0} (ZMod (q i))
                          (@CommRing.toRing.{0} (ZMod (q i)) (ZMod.commRing (q i)))))))
                (@Couret.STROBO2TORS.recohTorsionSubgroup.{0} ((i : Fin d) → ZMod (q i))
                  (@Pi.addCommGroup.{0, 0} (Fin d) (fun i => ZMod (q i)) fun i =>
                    @Ring.toAddCommGroup.{0} (ZMod (q i)) (@CommRing.toRing.{0} (ZMod (q i)) (ZMod.commRing (q i))))
                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                x)
            (@Pi.instAdd.{0, 0} (@Couret.STROBO2TORS.RecohEvenCoordinate d q)
              (fun a => ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) fun i =>
              @Distrib.toAdd.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                (@instDistribOfSemiring.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                  (@DivisionSemiring.toSemiring.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                    (@Semifield.toDivisionSemiring.{0}
                      (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                      (@Field.toSemifield.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                        (@ZMod.instField (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                          Nat.fact_prime_two))))))
            (@AddSubgroup.add.{0} ((i : Fin d) → ZMod (q i))
              (@AddCommGroup.toAddGroup.{0} ((i : Fin d) → ZMod (q i))
                (@Pi.addCommGroup.{0, 0} (Fin d) (fun i => ZMod (q i)) fun i =>
                  @Ring.toAddCommGroup.{0} (ZMod (q i)) (@CommRing.toRing.{0} (ZMod (q i)) (ZMod.commRing (q i)))))
              (@Couret.STROBO2TORS.recohTorsionSubgroup.{0} ((i : Fin d) → ZMod (q i))
                (@Pi.addCommGroup.{0, 0} (Fin d) (fun i => ZMod (q i)) fun i =>
                  @Ring.toAddCommGroup.{0} (ZMod (q i)) (@CommRing.toRing.{0} (ZMod (q i)) (ZMod.commRing (q i))))
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
          (@Couret.STROBO2TORS.RecohEvenCoordinate d q →
            ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (fun x =>
            @Subtype.{1} ((i : Fin d) → ZMod (q i)) fun x =>
              @Membership.mem.{0, 0} ((i : Fin d) → ZMod (q i))
                (@AddSubgroup.{0} ((i : Fin d) → ZMod (q i))
                  (@AddCommGroup.toAddGroup.{0} ((i : Fin d) → ZMod (q i))
                    (@Pi.addCommGroup.{0, 0} (Fin d) (fun i => ZMod (q i)) fun i =>
                      @Ring.toAddCommGroup.{0} (ZMod (q i)) (@CommRing.toRing.{0} (ZMod (q i)) (ZMod.commRing (q i))))))
                (@SetLike.instMembership.{0, 0}
                  (@AddSubgroup.{0} ((i : Fin d) → ZMod (q i))
                    (@AddCommGroup.toAddGroup.{0} ((i : Fin d) → ZMod (q i))
                      (@Pi.addCommGroup.{0, 0} (Fin d) (fun i => ZMod (q i)) fun i =>
                        @Ring.toAddCommGroup.{0} (ZMod (q i))
                          (@CommRing.toRing.{0} (ZMod (q i)) (ZMod.commRing (q i))))))
                  ((i : Fin d) → ZMod (q i))
                  (@AddSubgroup.instSetLike.{0} ((i : Fin d) → ZMod (q i))
                    (@AddCommGroup.toAddGroup.{0} ((i : Fin d) → ZMod (q i))
                      (@Pi.addCommGroup.{0, 0} (Fin d) (fun i => ZMod (q i)) fun i =>
                        @Ring.toAddCommGroup.{0} (ZMod (q i))
                          (@CommRing.toRing.{0} (ZMod (q i)) (ZMod.commRing (q i)))))))
                (@Couret.STROBO2TORS.recohTorsionSubgroup.{0} ((i : Fin d) → ZMod (q i))
                  (@Pi.addCommGroup.{0, 0} (Fin d) (fun i => ZMod (q i)) fun i =>
                    @Ring.toAddCommGroup.{0} (ZMod (q i)) (@CommRing.toRing.{0} (ZMod (q i)) (ZMod.commRing (q i))))
                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                x)
          (@EquivLike.toFunLike.{1, 1, 1}
            (@AddEquiv.{0, 0}
              (@Couret.STROBO2TORS.RecohEvenCoordinate d q →
                ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
              (@Subtype.{1} ((i : Fin d) → ZMod (q i)) fun x =>
                @Membership.mem.{0, 0} ((i : Fin d) → ZMod (q i))
                  (@AddSubgroup.{0} ((i : Fin d) → ZMod (q i))
                    (@AddCommGroup.toAddGroup.{0} ((i : Fin d) → ZMod (q i))
                      (@Pi.addCommGroup.{0, 0} (Fin d) (fun i => ZMod (q i)) fun i =>
                        @Ring.toAddCommGroup.{0} (ZMod (q i))
                          (@CommRing.toRing.{0} (ZMod (q i)) (ZMod.commRing (q i))))))
                  (@SetLike.instMembership.{0, 0}
                    (@AddSubgroup.{0} ((i : Fin d) → ZMod (q i))
                      (@AddCommGroup.toAddGroup.{0} ((i : Fin d) → ZMod (q i))
                        (@Pi.addCommGroup.{0, 0} (Fin d) (fun i => ZMod (q i)) fun i =>
                          @Ring.toAddCommGroup.{0} (ZMod (q i))
                            (@CommRing.toRing.{0} (ZMod (q i)) (ZMod.commRing (q i))))))
                    ((i : Fin d) → ZMod (q i))
                    (@AddSubgroup.instSetLike.{0} ((i : Fin d) → ZMod (q i))
                      (@AddCommGroup.toAddGroup.{0} ((i : Fin d) → ZMod (q i))
                        (@Pi.addCommGroup.{0, 0} (Fin d) (fun i => ZMod (q i)) fun i =>
                          @Ring.toAddCommGroup.{0} (ZMod (q i))
                            (@CommRing.toRing.{0} (ZMod (q i)) (ZMod.commRing (q i)))))))
                  (@Couret.STROBO2TORS.recohTorsionSubgroup.{0} ((i : Fin d) → ZMod (q i))
                    (@Pi.addCommGroup.{0, 0} (Fin d) (fun i => ZMod (q i)) fun i =>
                      @Ring.toAddCommGroup.{0} (ZMod (q i)) (@CommRing.toRing.{0} (ZMod (q i)) (ZMod.commRing (q i))))
                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                  x)
              (@Pi.instAdd.{0, 0} (@Couret.STROBO2TORS.RecohEvenCoordinate d q)
                (fun a => ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) fun i =>
                @Distrib.toAdd.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                  (@instDistribOfSemiring.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                    (@DivisionSemiring.toSemiring.{0}
                      (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                      (@Semifield.toDivisionSemiring.{0}
                        (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                        (@Field.toSemifield.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                          (@ZMod.instField (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                            Nat.fact_prime_two))))))
              (@AddSubgroup.add.{0} ((i : Fin d) → ZMod (q i))
                (@AddCommGroup.toAddGroup.{0} ((i : Fin d) → ZMod (q i))
                  (@Pi.addCommGroup.{0, 0} (Fin d) (fun i => ZMod (q i)) fun i =>
                    @Ring.toAddCommGroup.{0} (ZMod (q i)) (@CommRing.toRing.{0} (ZMod (q i)) (ZMod.commRing (q i)))))
                (@Couret.STROBO2TORS.recohTorsionSubgroup.{0} ((i : Fin d) → ZMod (q i))
                  (@Pi.addCommGroup.{0, 0} (Fin d) (fun i => ZMod (q i)) fun i =>
                    @Ring.toAddCommGroup.{0} (ZMod (q i)) (@CommRing.toRing.{0} (ZMod (q i)) (ZMod.commRing (q i))))
                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
            (@Couret.STROBO2TORS.RecohEvenCoordinate d q →
              ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
            (@Subtype.{1} ((i : Fin d) → ZMod (q i)) fun x =>
              @Membership.mem.{0, 0} ((i : Fin d) → ZMod (q i))
                (@AddSubgroup.{0} ((i : Fin d) → ZMod (q i))
                  (@AddCommGroup.toAddGroup.{0} ((i : Fin d) → ZMod (q i))
                    (@Pi.addCommGroup.{0, 0} (Fin d) (fun i => ZMod (q i)) fun i =>
                      @Ring.toAddCommGroup.{0} (ZMod (q i)) (@CommRing.toRing.{0} (ZMod (q i)) (ZMod.commRing (q i))))))
                (@SetLike.instMembership.{0, 0}
                  (@AddSubgroup.{0} ((i : Fin d) → ZMod (q i))
                    (@AddCommGroup.toAddGroup.{0} ((i : Fin d) → ZMod (q i))
                      (@Pi.addCommGroup.{0, 0} (Fin d) (fun i => ZMod (q i)) fun i =>
                        @Ring.toAddCommGroup.{0} (ZMod (q i))
                          (@CommRing.toRing.{0} (ZMod (q i)) (ZMod.commRing (q i))))))
                  ((i : Fin d) → ZMod (q i))
                  (@AddSubgroup.instSetLike.{0} ((i : Fin d) → ZMod (q i))
                    (@AddCommGroup.toAddGroup.{0} ((i : Fin d) → ZMod (q i))
                      (@Pi.addCommGroup.{0, 0} (Fin d) (fun i => ZMod (q i)) fun i =>
                        @Ring.toAddCommGroup.{0} (ZMod (q i))
                          (@CommRing.toRing.{0} (ZMod (q i)) (ZMod.commRing (q i)))))))
                (@Couret.STROBO2TORS.recohTorsionSubgroup.{0} ((i : Fin d) → ZMod (q i))
                  (@Pi.addCommGroup.{0, 0} (Fin d) (fun i => ZMod (q i)) fun i =>
                    @Ring.toAddCommGroup.{0} (ZMod (q i)) (@CommRing.toRing.{0} (ZMod (q i)) (ZMod.commRing (q i))))
                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                x)
            (@AddEquiv.instEquivLike.{0, 0}
              (@Couret.STROBO2TORS.RecohEvenCoordinate d q →
                ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
              (@Subtype.{1} ((i : Fin d) → ZMod (q i)) fun x =>
                @Membership.mem.{0, 0} ((i : Fin d) → ZMod (q i))
                  (@AddSubgroup.{0} ((i : Fin d) → ZMod (q i))
                    (@AddCommGroup.toAddGroup.{0} ((i : Fin d) → ZMod (q i))
                      (@Pi.addCommGroup.{0, 0} (Fin d) (fun i => ZMod (q i)) fun i =>
                        @Ring.toAddCommGroup.{0} (ZMod (q i))
                          (@CommRing.toRing.{0} (ZMod (q i)) (ZMod.commRing (q i))))))
                  (@SetLike.instMembership.{0, 0}
                    (@AddSubgroup.{0} ((i : Fin d) → ZMod (q i))
                      (@AddCommGroup.toAddGroup.{0} ((i : Fin d) → ZMod (q i))
                        (@Pi.addCommGroup.{0, 0} (Fin d) (fun i => ZMod (q i)) fun i =>
                          @Ring.toAddCommGroup.{0} (ZMod (q i))
                            (@CommRing.toRing.{0} (ZMod (q i)) (ZMod.commRing (q i))))))
                    ((i : Fin d) → ZMod (q i))
                    (@AddSubgroup.instSetLike.{0} ((i : Fin d) → ZMod (q i))
                      (@AddCommGroup.toAddGroup.{0} ((i : Fin d) → ZMod (q i))
                        (@Pi.addCommGroup.{0, 0} (Fin d) (fun i => ZMod (q i)) fun i =>
                          @Ring.toAddCommGroup.{0} (ZMod (q i))
                            (@CommRing.toRing.{0} (ZMod (q i)) (ZMod.commRing (q i)))))))
                  (@Couret.STROBO2TORS.recohTorsionSubgroup.{0} ((i : Fin d) → ZMod (q i))
                    (@Pi.addCommGroup.{0, 0} (Fin d) (fun i => ZMod (q i)) fun i =>
                      @Ring.toAddCommGroup.{0} (ZMod (q i)) (@CommRing.toRing.{0} (ZMod (q i)) (ZMod.commRing (q i))))
                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                  x)
              (@Pi.instAdd.{0, 0} (@Couret.STROBO2TORS.RecohEvenCoordinate d q)
                (fun a => ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) fun i =>
                @Distrib.toAdd.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                  (@instDistribOfSemiring.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                    (@DivisionSemiring.toSemiring.{0}
                      (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                      (@Semifield.toDivisionSemiring.{0}
                        (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                        (@Field.toSemifield.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                          (@ZMod.instField (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                            Nat.fact_prime_two))))))
              (@AddSubgroup.add.{0} ((i : Fin d) → ZMod (q i))
                (@AddCommGroup.toAddGroup.{0} ((i : Fin d) → ZMod (q i))
                  (@Pi.addCommGroup.{0, 0} (Fin d) (fun i => ZMod (q i)) fun i =>
                    @Ring.toAddCommGroup.{0} (ZMod (q i)) (@CommRing.toRing.{0} (ZMod (q i)) (ZMod.commRing (q i)))))
                (@Couret.STROBO2TORS.recohTorsionSubgroup.{0} ((i : Fin d) → ZMod (q i))
                  (@Pi.addCommGroup.{0, 0} (Fin d) (fun i => ZMod (q i)) fun i =>
                    @Ring.toAddCommGroup.{0} (ZMod (q i)) (@CommRing.toRing.{0} (ZMod (q i)) (ZMod.commRing (q i))))
                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))
          (@AddEquiv.symm.{0, 0}
            (@Subtype.{1} ((i : Fin d) → ZMod (q i)) fun x =>
              @Membership.mem.{0, 0} ((i : Fin d) → ZMod (q i))
                (@AddSubgroup.{0} ((i : Fin d) → ZMod (q i))
                  (@AddCommGroup.toAddGroup.{0} ((i : Fin d) → ZMod (q i))
                    (@Pi.addCommGroup.{0, 0} (Fin d) (fun i => ZMod (q i)) fun i =>
                      @Ring.toAddCommGroup.{0} (ZMod (q i)) (@CommRing.toRing.{0} (ZMod (q i)) (ZMod.commRing (q i))))))
                (@SetLike.instMembership.{0, 0}
                  (@AddSubgroup.{0} ((i : Fin d) → ZMod (q i))
                    (@AddCommGroup.toAddGroup.{0} ((i : Fin d) → ZMod (q i))
                      (@Pi.addCommGroup.{0, 0} (Fin d) (fun i => ZMod (q i)) fun i =>
                        @Ring.toAddCommGroup.{0} (ZMod (q i))
                          (@CommRing.toRing.{0} (ZMod (q i)) (ZMod.commRing (q i))))))
                  ((i : Fin d) → ZMod (q i))
                  (@AddSubgroup.instSetLike.{0} ((i : Fin d) → ZMod (q i))
                    (@AddCommGroup.toAddGroup.{0} ((i : Fin d) → ZMod (q i))
                      (@Pi.addCommGroup.{0, 0} (Fin d) (fun i => ZMod (q i)) fun i =>
                        @Ring.toAddCommGroup.{0} (ZMod (q i))
                          (@CommRing.toRing.{0} (ZMod (q i)) (ZMod.commRing (q i)))))))
                (@Couret.STROBO2TORS.recohTorsionSubgroup.{0} ((i : Fin d) → ZMod (q i))
                  (@Pi.addCommGroup.{0, 0} (Fin d) (fun i => ZMod (q i)) fun i =>
                    @Ring.toAddCommGroup.{0} (ZMod (q i)) (@CommRing.toRing.{0} (ZMod (q i)) (ZMod.commRing (q i))))
                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                x)
            (@Couret.STROBO2TORS.RecohEvenCoordinate d q →
              ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
            (@AddSubgroup.add.{0} ((i : Fin d) → ZMod (q i))
              (@AddCommGroup.toAddGroup.{0} ((i : Fin d) → ZMod (q i))
                (@Pi.addCommGroup.{0, 0} (Fin d) (fun i => ZMod (q i)) fun i =>
                  @Ring.toAddCommGroup.{0} (ZMod (q i)) (@CommRing.toRing.{0} (ZMod (q i)) (ZMod.commRing (q i)))))
              (@Couret.STROBO2TORS.recohTorsionSubgroup.{0} ((i : Fin d) → ZMod (q i))
                (@Pi.addCommGroup.{0, 0} (Fin d) (fun i => ZMod (q i)) fun i =>
                  @Ring.toAddCommGroup.{0} (ZMod (q i)) (@CommRing.toRing.{0} (ZMod (q i)) (ZMod.commRing (q i))))
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
            (@Pi.instAdd.{0, 0} (@Couret.STROBO2TORS.RecohEvenCoordinate d q)
              (fun a => ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) fun i =>
              @Distrib.toAdd.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                (@instDistribOfSemiring.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                  (@DivisionSemiring.toSemiring.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                    (@Semifield.toDivisionSemiring.{0}
                      (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                      (@Field.toSemifield.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                        (@ZMod.instField (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                          Nat.fact_prime_two))))))
            (@Couret.STROBO2TORS.recohProductTwoCoordinates d q inst))
          bits)
        i)
      (@OfNat.ofNat.{0} (ZMod (q i)) (nat_lit 0)
        (@Zero.toOfNat0.{0} (ZMod (q i))
          (@MulZeroClass.toZero.{0} (ZMod (q i))
            (@instMulZeroClassOfSemiring.{0} (ZMod (q i))
              (@CommSemiring.toSemiring.{0} (ZMod (q i))
                (@CommRing.toCommSemiring.{0} (ZMod (q i)) (ZMod.commRing (q i)))))))) := @_root_.Couret.STROBO2TORS.p2m_local_recoh_product_two_coordinates_symm_apply_odd

