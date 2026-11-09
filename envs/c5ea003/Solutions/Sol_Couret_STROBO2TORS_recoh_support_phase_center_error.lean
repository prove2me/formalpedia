-- Prove2me | solution 1 for Couret.STROBO2TORS.recoh_support_phase_center_error
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:18:33.745886+00:00
-- url     : https://prove2.me/submissions/caf9530b-dd15-45a9-82b4-0b4d1fd71af0

import Aesop
import Definitions.Def_Couret_RecohStableReconstruction_da64f089b51e
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Group.AddChar
import Mathlib.Algebra.Module.ZMod
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Complex.Arctan
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Complex.BigOperators
import Mathlib.Data.Finite.Card
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Multiset.Sort
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Data.Rat.Cast.Order
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
import Mathlib.Topology.Algebra.Order.Floor
import Theorems.Thm_Couret_STROBO2TORS_recoh_rational_root_power_error
import Definitions.Def_Couret_RecohStableSquareSelection_4ccedec76589
import Definitions.Def_Couret_RecohStableBank_b01db9b053a3
import Definitions.Def_Couret_RecohNoisySignRecovery_25d41afc9bfe
import Definitions.Def_Couret_RecohRationalRoots_2e1442988636

set_option autoImplicit false

/-!
End-to-end stable reconstruction on explicit cyclic products.  The square
determines the bank, rational series determine the prediction centres, and
the decoder generates at most one candidate per square representative.
Precision is supplied by two natural numbers and checked by rational guards.
No complex comparison occurs in the executable definitions.
-/

namespace Couret.STROBO2TORS

open scoped BigOperators

variable {d : ℕ} (q : Fin d → ℕ) [∀ i, NeZero (q i)]









/-- The three rational root centres approximate the actual support reading. -/
theorem p2m_local_recoh_support_phase_center_error
    (S : Finset ((i : Fin d) → ZMod (q i))) (hS : S.card = 3)
    (coordinate : Fin d) (N : ℕ) [NeZero N] (hN : N ∣ q coordinate)
    (multiplier machinTerms taylorTerms : ℕ)
    (hpi : |recohPiPartial machinTerms| ≤ 4) (htaylor : 15 ≤ taylorTerms) :
    ‖recohRationalComplexValue
        (recohSupportPhaseCenter q S coordinate N multiplier machinTerms taylorTerms) -
      recohSupportProbe ((recohCyclicCoordinateCharacter q coordinate N hN) ^ multiplier) S‖ ≤
        3 * (recohRationalPhaseError machinTerms taylorTerms : ℝ) := by
  have hvalue : recohRationalComplexValue
      (recohSupportPhaseCenter q S coordinate N multiplier machinTerms taylorTerms) =
      ∑ x ∈ S, recohRationalComplexValue
        (recohRationalRootPower N ((x coordinate).val * multiplier) machinTerms taylorTerms) := by
    change recohRationalComplexAddHom _ = _
    rw [recohSupportPhaseCenter, map_sum]
    rfl
  rw [hvalue, recohSupportProbe, ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ x ∈ S, ‖recohRationalComplexValue
        (recohRationalRootPower N ((x coordinate).val * multiplier) machinTerms taylorTerms) -
        ((recohCyclicCoordinateCharacter q coordinate N hN) ^ multiplier) x‖ := norm_sum_le _ _
    _ ≤ ∑ _x ∈ S, (recohRationalPhaseError machinTerms taylorTerms : ℝ) := by
      apply Finset.sum_le_sum
      intro x hx
      rw [AddChar.pow_apply, recoh_cyclic_coordinate_character_apply, ← pow_mul]
      exact recoh_rational_root_power_error N _ machinTerms taylorTerms hpi htaylor
    _ = _ := by simp [hS]







































end Couret.STROBO2TORS


theorem solution : ∀ {d : Nat} (q : Fin d → Nat) [∀ (i : Fin d), @NeZero.{0} Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass) (q i)]
  (S : Finset.{0} ((i : Fin d) → ZMod (q i))),
  @Eq.{1} Nat (@Finset.card.{0} ((i : Fin d) → ZMod (q i)) S)
      (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) →
    ∀ (coordinate : Fin d) (N : Nat) [inst : @NeZero.{0} Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass) N]
      (hN : @Dvd.dvd.{0} Nat Nat.instDvd N (q coordinate)) (multiplier machinTerms taylorTerms : Nat),
      @LE.le.{0} Rat Rat.instLE
          (@abs.{0} Rat Rat.instLattice Rat.addGroup (Couret.STROBO2TORS.recohPiPartial machinTerms))
          (@OfNat.ofNat.{0} Rat (nat_lit 4) (@Rat.instOfNat (nat_lit 4))) →
        @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 15) (instOfNatNat (nat_lit 15))) taylorTerms →
          @LE.le.{0} Real Real.instLE
            (@Norm.norm.{0} Complex Complex.instNorm
              (@HSub.hSub.{0, 0, 0} Complex Complex Complex (@instHSub.{0} Complex Complex.instSub)
                (Couret.STROBO2TORS.recohRationalComplexValue
                  (@Couret.STROBO2TORS.recohSupportPhaseCenter d q S coordinate N multiplier machinTerms taylorTerms))
                (@Couret.STROBO2TORS.recohSupportProbe.{0} ((j : Fin d) → ZMod (q j))
                  (@Pi.addCommGroup.{0, 0} (Fin d) (fun j => ZMod (q j)) fun i =>
                    @Ring.toAddCommGroup.{0} (ZMod (q i)) (@CommRing.toRing.{0} (ZMod (q i)) (ZMod.commRing (q i))))
                  (@HPow.hPow.{0, 0, 0}
                    (@AddChar.{0, 0} ((j : Fin d) → ZMod (q j))
                      (@Pi.addMonoid.{0, 0} (Fin d) (fun j => ZMod (q j)) fun i =>
                        @AddMonoidWithOne.toAddMonoid.{0} (ZMod (q i))
                          (@AddGroupWithOne.toAddMonoidWithOne.{0} (ZMod (q i))
                            (@Ring.toAddGroupWithOne.{0} (ZMod (q i))
                              (@CommRing.toRing.{0} (ZMod (q i)) (ZMod.commRing (q i))))))
                      Complex (@Semiring.toMonoid.{0} Complex Complex.instSemiring))
                    Nat
                    (@AddChar.{0, 0} ((j : Fin d) → ZMod (q j))
                      (@Pi.addMonoid.{0, 0} (Fin d) (fun j => ZMod (q j)) fun i =>
                        @AddMonoidWithOne.toAddMonoid.{0} (ZMod (q i))
                          (@AddGroupWithOne.toAddMonoidWithOne.{0} (ZMod (q i))
                            (@Ring.toAddGroupWithOne.{0} (ZMod (q i))
                              (@CommRing.toRing.{0} (ZMod (q i)) (ZMod.commRing (q i))))))
                      Complex (@Semiring.toMonoid.{0} Complex Complex.instSemiring))
                    (@instHPow.{0, 0}
                      (@AddChar.{0, 0} ((j : Fin d) → ZMod (q j))
                        (@Pi.addMonoid.{0, 0} (Fin d) (fun j => ZMod (q j)) fun i =>
                          @AddMonoidWithOne.toAddMonoid.{0} (ZMod (q i))
                            (@AddGroupWithOne.toAddMonoidWithOne.{0} (ZMod (q i))
                              (@Ring.toAddGroupWithOne.{0} (ZMod (q i))
                                (@CommRing.toRing.{0} (ZMod (q i)) (ZMod.commRing (q i))))))
                        Complex (@Semiring.toMonoid.{0} Complex Complex.instSemiring))
                      Nat
                      (@Monoid.toPow.{0}
                        (@AddChar.{0, 0} ((j : Fin d) → ZMod (q j))
                          (@Pi.addMonoid.{0, 0} (Fin d) (fun j => ZMod (q j)) fun i =>
                            @AddMonoidWithOne.toAddMonoid.{0} (ZMod (q i))
                              (@AddGroupWithOne.toAddMonoidWithOne.{0} (ZMod (q i))
                                (@Ring.toAddGroupWithOne.{0} (ZMod (q i))
                                  (@CommRing.toRing.{0} (ZMod (q i)) (ZMod.commRing (q i))))))
                          Complex (@Semiring.toMonoid.{0} Complex Complex.instSemiring))
                        (@DivInvMonoid.toMonoid.{0}
                          (@AddChar.{0, 0} ((j : Fin d) → ZMod (q j))
                            (@Pi.addMonoid.{0, 0} (Fin d) (fun j => ZMod (q j)) fun i =>
                              @AddMonoidWithOne.toAddMonoid.{0} (ZMod (q i))
                                (@AddGroupWithOne.toAddMonoidWithOne.{0} (ZMod (q i))
                                  (@Ring.toAddGroupWithOne.{0} (ZMod (q i))
                                    (@CommRing.toRing.{0} (ZMod (q i)) (ZMod.commRing (q i))))))
                            Complex (@Semiring.toMonoid.{0} Complex Complex.instSemiring))
                          (@Group.toDivInvMonoid.{0}
                            (@AddChar.{0, 0} ((j : Fin d) → ZMod (q j))
                              (@Pi.addMonoid.{0, 0} (Fin d) (fun j => ZMod (q j)) fun i =>
                                @AddMonoidWithOne.toAddMonoid.{0} (ZMod (q i))
                                  (@AddGroupWithOne.toAddMonoidWithOne.{0} (ZMod (q i))
                                    (@Ring.toAddGroupWithOne.{0} (ZMod (q i))
                                      (@CommRing.toRing.{0} (ZMod (q i)) (ZMod.commRing (q i))))))
                              Complex (@Semiring.toMonoid.{0} Complex Complex.instSemiring))
                            (@CommGroup.toGroup.{0}
                              (@AddChar.{0, 0} ((j : Fin d) → ZMod (q j))
                                (@Pi.addMonoid.{0, 0} (Fin d) (fun j => ZMod (q j)) fun i =>
                                  @AddMonoidWithOne.toAddMonoid.{0} (ZMod (q i))
                                    (@AddGroupWithOne.toAddMonoidWithOne.{0} (ZMod (q i))
                                      (@Ring.toAddGroupWithOne.{0} (ZMod (q i))
                                        (@CommRing.toRing.{0} (ZMod (q i)) (ZMod.commRing (q i))))))
                                Complex (@Semiring.toMonoid.{0} Complex Complex.instSemiring))
                              (@AddChar.instCommGroup.{0, 0} ((j : Fin d) → ZMod (q j)) Complex
                                (@Pi.addCommGroup.{0, 0} (Fin d) (fun j => ZMod (q j)) fun i =>
                                  @Ring.toAddCommGroup.{0} (ZMod (q i))
                                    (@CommRing.toRing.{0} (ZMod (q i)) (ZMod.commRing (q i))))
                                (@CommRing.toCommMonoid.{0} Complex Complex.commRing)))))))
                    (@Couret.STROBO2TORS.recohCyclicCoordinateCharacter d q coordinate N inst hN) multiplier)
                  S)))
            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
              (@OfNat.ofNat.{0} Real (nat_lit 3)
                (@instOfNatAtLeastTwo.{0} Real (nat_lit 3) Real.instNatCast
                  (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                    (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
              (@Rat.cast.{0} Real Real.instRatCast
                (Couret.STROBO2TORS.recohRationalPhaseError machinTerms taylorTerms))) := @_root_.Couret.STROBO2TORS.p2m_local_recoh_support_phase_center_error

