-- Prove2me | solution 1 for Couret.STROBO2TORS.recoh_cyclic_binary_bank_sign_coordinates
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T19:56:12.602844+00:00
-- url     : https://prove2.me/submissions/d802e3df-bff5-4cf8-a401-35bb30b073d3

import Aesop
import Definitions.Def_Couret_RecohCyclicPrimaryBank_92b8732c410a
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
import Mathlib.Data.Multiset.Sort
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finiteness
import Mathlib.GroupTheory.FiniteAbelian.Duality
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Choose
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_STROBO2TORS_recoh_cyclic_primary_coordinate_kernel
import Theorems.Thm_Couret_STROBO2TORS_recoh_product_two_coordinates_eq_zero_iff
import Definitions.Def_Couret_RecohOptimalBank_e8b60aaa0883
import Definitions.Def_Couret_RecohSignRecovery_71a8a4a1ce8a
import Definitions.Def_Couret_RecohCyclicCoordinates_d669b2caaf1a
import Mathlib.Data.Multiset.Sort
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.RingTheory.RootsOfUnity.Complex

set_option autoImplicit false

/-!
Coordinate primary characters and executable exponent encodings for finite
products of cyclic groups. The encoding sorts the multiset of coordinate
values, so multiplicities are retained and no enumeration of the ambient
group is used. Complex roots and characters are semantic objects; exponent
lists and primary-factor data are the inputs used by the exact backend.
-/

namespace Couret.STROBO2TORS





variable {d : ℕ} (q : Fin d → ℕ) [∀ i, NeZero (q i)]











































/-- The coordinate bank agrees with the explicitly computed binary
equivalence, so the recovery compatibility contract is discharged. -/
theorem p2m_local_recoh_cyclic_binary_bank_sign_coordinates
    (data : RecohPrimaryFactorData q 2)
    (u : recohTorsionSubgroup (G := (j : Fin d) → ZMod (q j)) 2)
    (i : RecohEvenCoordinate q) :
    recohCyclicPrimaryBank q 2 data i u.val =
      if recohProductTwoCoordinates q u i = 0 then 1 else -1 := by
  have hui : 2 • u.val i.val = 0 := by
    simpa only [Pi.smul_apply, Pi.zero_apply] using congrFun u.property i.val
  have hker := recoh_cyclic_primary_coordinate_kernel q 2 data i u.val hui
  by_cases hbit : recohProductTwoCoordinates q u i = 0
  · rw [if_pos hbit]
    exact hker.mpr ((recoh_product_two_coordinates_eq_zero_iff q u i).mp hbit)
  · rw [if_neg hbit]
    have hne : recohCyclicPrimaryBank q 2 data i u.val ≠ 1 := by
      intro hone
      exact hbit ((recoh_product_two_coordinates_eq_zero_iff q u i).mpr (hker.mp hone))
    have htwo : (recohCyclicPrimaryBank q 2 data i u.val) ^ 2 = 1 := by
      rw [← AddChar.map_nsmul_eq_pow, u.property, AddChar.map_zero_eq_one]
    exact (sq_eq_one_iff.mp htwo).resolve_left hne















end Couret.STROBO2TORS


theorem solution : ∀ {d : Nat} (q : Fin d → Nat)
  [inst : ∀ (i : Fin d), @NeZero.{0} Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass) (q i)]
  (data : @Couret.STROBO2TORS.RecohPrimaryFactorData d q (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
  (u :
    @Subtype.{1} ((j : Fin d) → ZMod (q j)) fun x =>
      @Membership.mem.{0, 0} ((j : Fin d) → ZMod (q j))
        (@AddSubgroup.{0} ((j : Fin d) → ZMod (q j))
          (@AddCommGroup.toAddGroup.{0} ((j : Fin d) → ZMod (q j))
            (@Pi.addCommGroup.{0, 0} (Fin d) (fun j => ZMod (q j)) fun i =>
              @Ring.toAddCommGroup.{0} (ZMod (q i)) (@CommRing.toRing.{0} (ZMod (q i)) (ZMod.commRing (q i))))))
        (@SetLike.instMembership.{0, 0}
          (@AddSubgroup.{0} ((j : Fin d) → ZMod (q j))
            (@AddCommGroup.toAddGroup.{0} ((j : Fin d) → ZMod (q j))
              (@Pi.addCommGroup.{0, 0} (Fin d) (fun j => ZMod (q j)) fun i =>
                @Ring.toAddCommGroup.{0} (ZMod (q i)) (@CommRing.toRing.{0} (ZMod (q i)) (ZMod.commRing (q i))))))
          ((j : Fin d) → ZMod (q j))
          (@AddSubgroup.instSetLike.{0} ((j : Fin d) → ZMod (q j))
            (@AddCommGroup.toAddGroup.{0} ((j : Fin d) → ZMod (q j))
              (@Pi.addCommGroup.{0, 0} (Fin d) (fun j => ZMod (q j)) fun i =>
                @Ring.toAddCommGroup.{0} (ZMod (q i)) (@CommRing.toRing.{0} (ZMod (q i)) (ZMod.commRing (q i)))))))
        (@Couret.STROBO2TORS.recohTorsionSubgroup.{0} ((j : Fin d) → ZMod (q j))
          (@Pi.addCommGroup.{0, 0} (Fin d) (fun j => ZMod (q j)) fun i =>
            @Ring.toAddCommGroup.{0} (ZMod (q i)) (@CommRing.toRing.{0} (ZMod (q i)) (ZMod.commRing (q i))))
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        x)
  (i : @Couret.STROBO2TORS.RecohEvenCoordinate d q),
  @Eq.{1} Complex
    (@DFunLike.coe.{1, 1, 1}
      (@AddChar.{0, 0} ((j : Fin d) → ZMod (q j))
        (@Pi.addMonoid.{0, 0} (Fin d) (fun j => ZMod (q j)) fun i =>
          @AddMonoidWithOne.toAddMonoid.{0} (ZMod (q i))
            (@AddGroupWithOne.toAddMonoidWithOne.{0} (ZMod (q i))
              (@Ring.toAddGroupWithOne.{0} (ZMod (q i)) (@CommRing.toRing.{0} (ZMod (q i)) (ZMod.commRing (q i))))))
        Complex (@Semiring.toMonoid.{0} Complex Complex.instSemiring))
      ((j : Fin d) → ZMod (q j)) (fun x => Complex)
      (@AddChar.instFunLike.{0, 0} ((j : Fin d) → ZMod (q j)) Complex
        (@Pi.addMonoid.{0, 0} (Fin d) (fun j => ZMod (q j)) fun i =>
          @AddMonoidWithOne.toAddMonoid.{0} (ZMod (q i))
            (@AddGroupWithOne.toAddMonoidWithOne.{0} (ZMod (q i))
              (@Ring.toAddGroupWithOne.{0} (ZMod (q i)) (@CommRing.toRing.{0} (ZMod (q i)) (ZMod.commRing (q i))))))
        (@Semiring.toMonoid.{0} Complex Complex.instSemiring))
      (@Couret.STROBO2TORS.recohCyclicPrimaryBank d q (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
        Nat.fact_prime_two data i)
      (@Subtype.val.{1} ((j : Fin d) → ZMod (q j))
        (fun x =>
          @Membership.mem.{0, 0} ((j : Fin d) → ZMod (q j))
            (@AddSubgroup.{0} ((j : Fin d) → ZMod (q j))
              (@AddCommGroup.toAddGroup.{0} ((j : Fin d) → ZMod (q j))
                (@Pi.addCommGroup.{0, 0} (Fin d) (fun j => ZMod (q j)) fun i =>
                  @Ring.toAddCommGroup.{0} (ZMod (q i)) (@CommRing.toRing.{0} (ZMod (q i)) (ZMod.commRing (q i))))))
            (@SetLike.instMembership.{0, 0}
              (@AddSubgroup.{0} ((j : Fin d) → ZMod (q j))
                (@AddCommGroup.toAddGroup.{0} ((j : Fin d) → ZMod (q j))
                  (@Pi.addCommGroup.{0, 0} (Fin d) (fun j => ZMod (q j)) fun i =>
                    @Ring.toAddCommGroup.{0} (ZMod (q i)) (@CommRing.toRing.{0} (ZMod (q i)) (ZMod.commRing (q i))))))
              ((j : Fin d) → ZMod (q j))
              (@AddSubgroup.instSetLike.{0} ((j : Fin d) → ZMod (q j))
                (@AddCommGroup.toAddGroup.{0} ((j : Fin d) → ZMod (q j))
                  (@Pi.addCommGroup.{0, 0} (Fin d) (fun j => ZMod (q j)) fun i =>
                    @Ring.toAddCommGroup.{0} (ZMod (q i)) (@CommRing.toRing.{0} (ZMod (q i)) (ZMod.commRing (q i)))))))
            (@Couret.STROBO2TORS.recohTorsionSubgroup.{0} ((j : Fin d) → ZMod (q j))
              (@Pi.addCommGroup.{0, 0} (Fin d) (fun j => ZMod (q j)) fun i =>
                @Ring.toAddCommGroup.{0} (ZMod (q i)) (@CommRing.toRing.{0} (ZMod (q i)) (ZMod.commRing (q i))))
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
            x)
        u))
    (@ite.{1} Complex
      (@Eq.{1} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@DFunLike.coe.{1, 1, 1}
          (@AddEquiv.{0, 0}
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
                          Nat.fact_prime_two)))))))
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
                      @Ring.toAddCommGroup.{0} (ZMod (q i)) (@CommRing.toRing.{0} (ZMod (q i)) (ZMod.commRing (q i))))))
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
          (fun x =>
            @Couret.STROBO2TORS.RecohEvenCoordinate d q →
              ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@EquivLike.toFunLike.{1, 1, 1}
            (@AddEquiv.{0, 0}
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
                    (@DivisionSemiring.toSemiring.{0}
                      (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                      (@Semifield.toDivisionSemiring.{0}
                        (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                        (@Field.toSemifield.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                          (@ZMod.instField (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                            Nat.fact_prime_two)))))))
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
            (@AddEquiv.instEquivLike.{0, 0}
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
                    (@DivisionSemiring.toSemiring.{0}
                      (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                      (@Semifield.toDivisionSemiring.{0}
                        (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                        (@Field.toSemifield.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                          (@ZMod.instField (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                            Nat.fact_prime_two))))))))
          (@Couret.STROBO2TORS.recohProductTwoCoordinates d q inst) u i)
        (@OfNat.ofNat.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) (nat_lit 0)
          (@Zero.toOfNat0.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
            (@MulZeroClass.toZero.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
              (@instMulZeroClassOfSemiring.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                (@DivisionSemiring.toSemiring.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                  (@Semifield.toDivisionSemiring.{0}
                    (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                    (@Field.toSemifield.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                      (@ZMod.instField (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                        Nat.fact_prime_two)))))))))
      (ZMod.decidableEq (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
        (@DFunLike.coe.{1, 1, 1}
          (@AddEquiv.{0, 0}
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
                          Nat.fact_prime_two)))))))
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
                      @Ring.toAddCommGroup.{0} (ZMod (q i)) (@CommRing.toRing.{0} (ZMod (q i)) (ZMod.commRing (q i))))))
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
          (fun x =>
            @Couret.STROBO2TORS.RecohEvenCoordinate d q →
              ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@EquivLike.toFunLike.{1, 1, 1}
            (@AddEquiv.{0, 0}
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
                    (@DivisionSemiring.toSemiring.{0}
                      (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                      (@Semifield.toDivisionSemiring.{0}
                        (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                        (@Field.toSemifield.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                          (@ZMod.instField (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                            Nat.fact_prime_two)))))))
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
            (@AddEquiv.instEquivLike.{0, 0}
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
                    (@DivisionSemiring.toSemiring.{0}
                      (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                      (@Semifield.toDivisionSemiring.{0}
                        (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                        (@Field.toSemifield.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                          (@ZMod.instField (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                            Nat.fact_prime_two))))))))
          (@Couret.STROBO2TORS.recohProductTwoCoordinates d q inst) u i)
        (@OfNat.ofNat.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) (nat_lit 0)
          (@Zero.toOfNat0.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
            (@MulZeroClass.toZero.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
              (@instMulZeroClassOfSemiring.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                (@DivisionSemiring.toSemiring.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                  (@Semifield.toDivisionSemiring.{0}
                    (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                    (@Field.toSemifield.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                      (@ZMod.instField (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                        Nat.fact_prime_two)))))))))
      (@OfNat.ofNat.{0} Complex (nat_lit 1) (@One.toOfNat1.{0} Complex Complex.instOne))
      (@Neg.neg.{0} Complex Complex.instNeg
        (@OfNat.ofNat.{0} Complex (nat_lit 1) (@One.toOfNat1.{0} Complex Complex.instOne)))) := @_root_.Couret.STROBO2TORS.p2m_local_recoh_cyclic_binary_bank_sign_coordinates

