-- Prove2me | solution 1 for Couret.STROBO2TORS.recoh_stable_binary_bank_sign_coordinates
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:29:37.581591+00:00
-- url     : https://prove2.me/submissions/9c2b2a3b-b43a-4961-a4e4-d1b4c6cf5fbb

import Aesop
import Definitions.Def_Couret_RecohStableBank_b01db9b053a3
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Group.AddChar
import Mathlib.Algebra.Module.ZMod
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Finite.Card
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Multiset.Sort
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finiteness
import Mathlib.GroupTheory.FiniteAbelian.Duality
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.Tactic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Choose
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_STROBO2TORS_recoh_cyclic_binary_bank_sign_coordinates
import Theorems.Thm_Couret_STROBO2TORS_recoh_two_torsion_probe_is_sign
import Definitions.Def_Couret_RecohSelectedDecoder_a1594570d3fe
import Definitions.Def_Couret_RecohProbeStability_e389a2280f15
import Definitions.Def_Couret_RecohNoisyUniqueness_7e21ca0c53e8

set_option autoImplicit false

/-!
Quantitative reconstruction with the square-selected minimum-size bank.
Each binary character is replaced by a prescribed odd power; the selected
ternary character and the measurement index type are unchanged.

The multipliers are parameters of the bank and are fixed before readings are
received. The quantitative theorems require a certified amplitude bound on
the square fibre. A separate square-only selector supplies these parameters
and that bound.

The rational-decoder bridges use a supplied candidate set contained in the
fibre. They do not introduce an executable enumeration of the ambient group
or its powerset. Prediction error is included in the uniqueness budget.
-/

namespace Couret.STROBO2TORS

/-- Odd powers leave the restriction of any character to two-torsion
unchanged. -/
theorem recoh_character_odd_power_on_two
    {G : Type*} [AddCommGroup G] (chi : AddChar G ℂ)
    (k : ℕ) (hk : Odd k) (u : G) (hu : u + u = 0) :
    (chi ^ k) u = chi u := by
  classical
  rw [AddChar.pow_apply]
  rcases recoh_two_torsion_probe_is_sign chi chi.map_add_eq_mul
    chi.map_zero_eq_one u hu with h | h
  · simp [h]
  · rw [h, hk.neg_one_pow]

variable {d : ℕ} (q : Fin d → ℕ) [∀ i, NeZero (q i)]









theorem recoh_stable_binary_bank_on_two (multipliers : RecohEvenCoordinate q → ℕ)
    (hodd : ∀ i, Odd (multipliers i)) (i : RecohEvenCoordinate q)
    (u : (j : Fin d) → ZMod (q j)) (hu : u + u = 0) :
    recohStableBinaryBank q multipliers i u =
      recohCyclicPrimaryBank q 2 (recohCanonicalPrimaryData q 2) i u :=
  recoh_character_odd_power_on_two
    (recohCyclicPrimaryBank q 2 (recohCanonicalPrimaryData q 2) i)
    (multipliers i) (hodd i) u hu

/-- Every original binary coordinate is preserved exactly, not merely
the joint kernel of the bank. -/
theorem p2m_local_recoh_stable_binary_bank_sign_coordinates
    (multipliers : RecohEvenCoordinate q → ℕ) (hodd : ∀ i, Odd (multipliers i))
    (u : recohTorsionSubgroup (G := (j : Fin d) → ZMod (q j)) 2)
    (i : RecohEvenCoordinate q) :
    recohStableBinaryBank q multipliers i u.val =
      if recohProductTwoCoordinates q u i = 0 then 1 else -1 := by
  rw [recoh_stable_binary_bank_on_two q multipliers hodd i u.val
    (by simpa only [recoh_mem_torsion_subgroup, two_nsmul] using u.property)]
  exact recoh_cyclic_binary_bank_sign_coordinates q (recohCanonicalPrimaryData q 2) u i























end Couret.STROBO2TORS


theorem solution : ∀ {d : Nat} (q : Fin d → Nat)
  [inst : ∀ (i : Fin d), @NeZero.{0} Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass) (q i)]
  (multipliers : @Couret.STROBO2TORS.RecohEvenCoordinate d q → Nat),
  (∀ (i : @Couret.STROBO2TORS.RecohEvenCoordinate d q), @Odd.{0} Nat Nat.instSemiring (multipliers i)) →
    ∀
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
          (@AddChar.{0, 0} ((i : Fin d) → ZMod (q i))
            (@Pi.addMonoid.{0, 0} (Fin d) (fun i => ZMod (q i)) fun i =>
              @AddMonoidWithOne.toAddMonoid.{0} (ZMod (q i))
                (@AddGroupWithOne.toAddMonoidWithOne.{0} (ZMod (q i))
                  (@Ring.toAddGroupWithOne.{0} (ZMod (q i)) (@CommRing.toRing.{0} (ZMod (q i)) (ZMod.commRing (q i))))))
            Complex (@Semiring.toMonoid.{0} Complex Complex.instSemiring))
          ((i : Fin d) → ZMod (q i)) (fun x => Complex)
          (@AddChar.instFunLike.{0, 0} ((i : Fin d) → ZMod (q i)) Complex
            (@Pi.addMonoid.{0, 0} (Fin d) (fun i => ZMod (q i)) fun i =>
              @AddMonoidWithOne.toAddMonoid.{0} (ZMod (q i))
                (@AddGroupWithOne.toAddMonoidWithOne.{0} (ZMod (q i))
                  (@Ring.toAddGroupWithOne.{0} (ZMod (q i)) (@CommRing.toRing.{0} (ZMod (q i)) (ZMod.commRing (q i))))))
            (@Semiring.toMonoid.{0} Complex Complex.instSemiring))
          (@Couret.STROBO2TORS.recohStableBinaryBank d q inst multipliers i)
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
                        @Ring.toAddCommGroup.{0} (ZMod (q i))
                          (@CommRing.toRing.{0} (ZMod (q i)) (ZMod.commRing (q i))))))
                  ((j : Fin d) → ZMod (q j))
                  (@AddSubgroup.instSetLike.{0} ((j : Fin d) → ZMod (q j))
                    (@AddCommGroup.toAddGroup.{0} ((j : Fin d) → ZMod (q j))
                      (@Pi.addCommGroup.{0, 0} (Fin d) (fun j => ZMod (q j)) fun i =>
                        @Ring.toAddCommGroup.{0} (ZMod (q i))
                          (@CommRing.toRing.{0} (ZMod (q i)) (ZMod.commRing (q i)))))))
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
                          @Ring.toAddCommGroup.{0} (ZMod (q i))
                            (@CommRing.toRing.{0} (ZMod (q i)) (ZMod.commRing (q i))))
                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                      x)
                  (@Couret.STROBO2TORS.RecohEvenCoordinate d q →
                    ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                  (@AddSubgroup.add.{0} ((i : Fin d) → ZMod (q i))
                    (@AddCommGroup.toAddGroup.{0} ((i : Fin d) → ZMod (q i))
                      (@Pi.addCommGroup.{0, 0} (Fin d) (fun i => ZMod (q i)) fun i =>
                        @Ring.toAddCommGroup.{0} (ZMod (q i))
                          (@CommRing.toRing.{0} (ZMod (q i)) (ZMod.commRing (q i)))))
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
                          @Ring.toAddCommGroup.{0} (ZMod (q i))
                            (@CommRing.toRing.{0} (ZMod (q i)) (ZMod.commRing (q i))))
                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                      x)
                  (@Couret.STROBO2TORS.RecohEvenCoordinate d q →
                    ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                  (@AddSubgroup.add.{0} ((i : Fin d) → ZMod (q i))
                    (@AddCommGroup.toAddGroup.{0} ((i : Fin d) → ZMod (q i))
                      (@Pi.addCommGroup.{0, 0} (Fin d) (fun i => ZMod (q i)) fun i =>
                        @Ring.toAddCommGroup.{0} (ZMod (q i))
                          (@CommRing.toRing.{0} (ZMod (q i)) (ZMod.commRing (q i)))))
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
                    (@DivisionSemiring.toSemiring.{0}
                      (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
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
                          @Ring.toAddCommGroup.{0} (ZMod (q i))
                            (@CommRing.toRing.{0} (ZMod (q i)) (ZMod.commRing (q i))))
                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                      x)
                  (@Couret.STROBO2TORS.RecohEvenCoordinate d q →
                    ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                  (@AddSubgroup.add.{0} ((i : Fin d) → ZMod (q i))
                    (@AddCommGroup.toAddGroup.{0} ((i : Fin d) → ZMod (q i))
                      (@Pi.addCommGroup.{0, 0} (Fin d) (fun i => ZMod (q i)) fun i =>
                        @Ring.toAddCommGroup.{0} (ZMod (q i))
                          (@CommRing.toRing.{0} (ZMod (q i)) (ZMod.commRing (q i)))))
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
                          @Ring.toAddCommGroup.{0} (ZMod (q i))
                            (@CommRing.toRing.{0} (ZMod (q i)) (ZMod.commRing (q i))))
                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                      x)
                  (@Couret.STROBO2TORS.RecohEvenCoordinate d q →
                    ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                  (@AddSubgroup.add.{0} ((i : Fin d) → ZMod (q i))
                    (@AddCommGroup.toAddGroup.{0} ((i : Fin d) → ZMod (q i))
                      (@Pi.addCommGroup.{0, 0} (Fin d) (fun i => ZMod (q i)) fun i =>
                        @Ring.toAddCommGroup.{0} (ZMod (q i))
                          (@CommRing.toRing.{0} (ZMod (q i)) (ZMod.commRing (q i)))))
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
                    (@DivisionSemiring.toSemiring.{0}
                      (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                      (@Semifield.toDivisionSemiring.{0}
                        (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                        (@Field.toSemifield.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                          (@ZMod.instField (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                            Nat.fact_prime_two)))))))))
          (@OfNat.ofNat.{0} Complex (nat_lit 1) (@One.toOfNat1.{0} Complex Complex.instOne))
          (@Neg.neg.{0} Complex Complex.instNeg
            (@OfNat.ofNat.{0} Complex (nat_lit 1) (@One.toOfNat1.{0} Complex Complex.instOne)))) := @_root_.Couret.STROBO2TORS.p2m_local_recoh_stable_binary_bank_sign_coordinates

