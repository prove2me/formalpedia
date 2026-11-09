-- Prove2me | solution 1 for Couret.STROBO2TORS.recoh_square_phase_center_error
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:18:13.44558+00:00
-- url     : https://prove2.me/submissions/f4a11ddd-813a-4ec1-b212-add50c4a0714

import Aesop
import Definitions.Def_Couret_RecohStableSquareSelection_4ccedec76589
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
import Theorems.Thm_Couret_STROBO2TORS_recoh_rational_complex_scale_value
import Theorems.Thm_Couret_STROBO2TORS_recoh_rational_root_power_error
import Theorems.Thm_Couret_STROBO2TORS_recoh_support_probe_sq
import Definitions.Def_Couret_RecohRationalRoots_2e1442988636
import Definitions.Def_Couret_RecohOddPowerRuntime_8c8d44664d18
import Definitions.Def_Couret_RecohSquareSelector_3b7a2954c02a
import Definitions.Def_Couret_RecohReconstruction_b9109c17baa8

set_option autoImplicit false

/-!
The robust binary multipliers are computed from the exact labelled square.
Rational phase centres have a proved error budget.  The finite odd-power
search compares their squared norms to 9/4 and falls back to exponent one.
No support or measured character value is an input to this computation.
-/

namespace Couret.STROBO2TORS

open scoped BigOperators









variable {d : ℕ} (q : Fin d → ℕ) [∀ i, NeZero (q i)]





omit [∀ i, NeZero (q i)] in
theorem recoh_square_phase_center_value
    (entries : List (((i : Fin d) → ZMod (q i)) × ℕ))
    (coordinate : Fin d) (N multiplier machinTerms taylorTerms : ℕ) :
    recohRationalComplexValue
      (recohSquarePhaseCenter q entries coordinate N multiplier machinTerms taylorTerms) =
      ∑ z ∈ recohSelectedSquareSupport q entries,
        (recohTypedSquareValue entries z : ℂ) *
          recohRationalComplexValue
            (recohRationalRootPower N ((z coordinate).val * multiplier) machinTerms taylorTerms) := by
  change recohRationalComplexAddHom _ = _
  rw [recohSquarePhaseCenter, map_sum]
  apply Finset.sum_congr rfl
  intro z hz
  change recohRationalComplexValue _ = _
  rw [recoh_rational_complex_scale_value]
  simp

theorem recoh_square_phase_sparse_sum
    (entries : List (((i : Fin d) → ZMod (q i)) × ℕ))
    (f : ((i : Fin d) → ZMod (q i)) → ℂ) :
    (∑ z ∈ recohSelectedSquareSupport q entries, (recohTypedSquareValue entries z : ℂ) * f z) =
      ∑ z, (recohTypedSquareValue entries z : ℂ) * f z := by
  apply Finset.sum_subset (Finset.subset_univ _)
  intro z hz hnot
  have hzero : recohTypedSquareValue entries z = 0 := by
    by_contra hne
    exact hnot ((recoh_mem_selected_square_support q entries z).mpr hne)
  simp [hzero]

theorem recoh_square_phase_mass
    (entries : List (((i : Fin d) → ZMod (q i)) × ℕ))
    (S : Finset ((i : Fin d) → ZMod (q i))) (hS : S.card = 3)
    (hR : orderedSquare S = recohTypedSquareValue entries) :
    (∑ z ∈ recohSelectedSquareSupport q entries, (recohTypedSquareValue entries z : ℝ)) = 9 := by
  have h := recoh_support_probe_sq (1 : AddChar ((i : Fin d) → ZMod (q i)) ℂ) S
  simp only [recohSupportProbe, AddChar.one_apply, Finset.sum_const, nsmul_eq_mul,
    mul_one, hS] at h
  have he : (∑ z ∈ recohSelectedSquareSupport q entries,
      (recohTypedSquareValue entries z : ℂ)) = 9 := by
    have hu := recoh_square_phase_sparse_sum q entries (fun _ => (1 : ℂ))
    simp only [mul_one] at hu
    rw [hu, ← hR, ← h]
    norm_num
  exact_mod_cast he

/-- Sparse approximation of the Fourier transform of the observed square. -/
theorem p2m_local_recoh_square_phase_center_error
    (entries : List (((i : Fin d) → ZMod (q i)) × ℕ))
    (S : Finset ((i : Fin d) → ZMod (q i))) (hS : S.card = 3)
    (hR : orderedSquare S = recohTypedSquareValue entries)
    (coordinate : Fin d) (N : ℕ) [NeZero N] (hN : N ∣ q coordinate)
    (multiplier machinTerms taylorTerms : ℕ)
    (hpi : |recohPiPartial machinTerms| ≤ 4) (htaylor : 15 ≤ taylorTerms) :
    ‖recohRationalComplexValue
        (recohSquarePhaseCenter q entries coordinate N multiplier machinTerms taylorTerms) -
      (recohSupportProbe ((recohCyclicCoordinateCharacter q coordinate N hN) ^ multiplier) S) ^ 2‖ ≤
        9 * (recohRationalPhaseError machinTerms taylorTerms : ℝ) := by
  rw [recoh_square_phase_center_value, recoh_support_probe_sq, hR]
  rw [← recoh_square_phase_sparse_sum q entries]
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ z ∈ recohSelectedSquareSupport q entries,
        ‖(recohTypedSquareValue entries z : ℂ) *
          (recohRationalComplexValue
            (recohRationalRootPower N ((z coordinate).val * multiplier) machinTerms taylorTerms) -
            ((recohCyclicCoordinateCharacter q coordinate N hN) ^ multiplier) z)‖ := by
      simpa only [mul_sub] using norm_sum_le
        (recohSelectedSquareSupport q entries)
        (fun z => (recohTypedSquareValue entries z : ℂ) *
          (recohRationalComplexValue
            (recohRationalRootPower N ((z coordinate).val * multiplier) machinTerms taylorTerms) -
            ((recohCyclicCoordinateCharacter q coordinate N hN) ^ multiplier) z))
    _ ≤ ∑ z ∈ recohSelectedSquareSupport q entries,
        (recohTypedSquareValue entries z : ℝ) *
          (recohRationalPhaseError machinTerms taylorTerms : ℝ) := by
      apply Finset.sum_le_sum
      intro z hz
      rw [norm_mul, Complex.norm_natCast, AddChar.pow_apply,
        recoh_cyclic_coordinate_character_apply, ← pow_mul]
      exact mul_le_mul_of_nonneg_left
        (recoh_rational_root_power_error N _ machinTerms taylorTerms hpi htaylor) (by positivity)
    _ = _ := by rw [← Finset.sum_mul, recoh_square_phase_mass q entries S hS hR]













end Couret.STROBO2TORS


theorem solution : ∀ {d : Nat} (q : Fin d → Nat) [∀ (i : Fin d), @NeZero.{0} Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass) (q i)]
  (entries : List.{0} (Prod.{0, 0} ((i : Fin d) → ZMod (q i)) Nat)) (S : Finset.{0} ((i : Fin d) → ZMod (q i))),
  @Eq.{1} Nat (@Finset.card.{0} ((i : Fin d) → ZMod (q i)) S)
      (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) →
    @Eq.{1} (((i : Fin d) → ZMod (q i)) → Nat)
        (@Couret.STROBO2TORS.orderedSquare.{0} ((i : Fin d) → ZMod (q i))
          (@Pi.addCommGroup.{0, 0} (Fin d) (fun i => ZMod (q i)) fun i =>
            @Ring.toAddCommGroup.{0} (ZMod (q i)) (@CommRing.toRing.{0} (ZMod (q i)) (ZMod.commRing (q i))))
          (fun a b =>
            @Fintype.decidablePiFintype.{0, 0} (Fin d) (fun a => ZMod (q a)) (fun a => ZMod.decidableEq (q a))
              (Fin.fintype d) a b)
          S)
        (@Couret.STROBO2TORS.recohTypedSquareValue.{0} ((i : Fin d) → ZMod (q i))
          (fun a b =>
            @Fintype.decidablePiFintype.{0, 0} (Fin d) (fun a => ZMod (q a)) (fun a => ZMod.decidableEq (q a))
              (Fin.fintype d) a b)
          entries) →
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
                    (@Couret.STROBO2TORS.recohSquarePhaseCenter d q entries coordinate N multiplier machinTerms
                      taylorTerms))
                  (@HPow.hPow.{0, 0, 0} Complex Nat Complex
                    (@instHPow.{0, 0} Complex Nat
                      (@Monoid.toPow.{0} Complex (@Semiring.toMonoid.{0} Complex Complex.instSemiring)))
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
                      S)
                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
              (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                (@OfNat.ofNat.{0} Real (nat_lit 9)
                  (@instOfNatAtLeastTwo.{0} Real (nat_lit 9) Real.instNatCast
                    (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
                      (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))))))
                (@Rat.cast.{0} Real Real.instRatCast
                  (Couret.STROBO2TORS.recohRationalPhaseError machinTerms taylorTerms))) := @_root_.Couret.STROBO2TORS.p2m_local_recoh_square_phase_center_error

