-- Prove2me | solution 1 for Couret.STROBO2TORS.recoh_stable_binary_amplitude
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:29:41.935087+00:00
-- url     : https://prove2.me/submissions/2c53c2ac-1188-4062-a19a-aa406825ce82

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
import Theorems.Thm_Couret_STROBO2TORS_recoh_odd_squared_selected_energy_ge_one
import Theorems.Thm_Couret_STROBO2TORS_recoh_rational_squared_distance_exact
import Theorems.Thm_Couret_STROBO2TORS_recoh_square_phase_center_error
import Theorems.Thm_Couret_STROBO2TORS_recoh_support_probe_three
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







/-- The fixed selection precision meets the complex square-transform budget. -/
theorem recoh_stable_selection_precision :
    |recohPiPartial 4| ≤ 4 ∧ 15 ≤ (48 : ℕ) ∧
      9 * recohRationalPhaseError 4 48 ≤ (1 / 2 : ℚ) := by
  norm_num [recohPiPartial, recohArctanPartial, recohRationalPhaseError,
    recohPiError, recohArctanError, recohTaylorError, Finset.sum_range_succ,
    Nat.factorial]

variable {d : ℕ} (q : Fin d → ℕ) [∀ i, NeZero (q i)]























/-- The binary reading selected using only R has amplitude at least one
for every support triple with that square. -/
theorem p2m_local_recoh_stable_binary_amplitude
    (entries : List (((i : Fin d) → ZMod (q i)) × ℕ))
    (S : Finset ((i : Fin d) → ZMod (q i))) (hS : S.card = 3)
    (hR : orderedSquare S = recohTypedSquareValue entries)
    (i : RecohEvenCoordinate q) :
    1 ≤ ‖recohSupportProbe
      ((recohCyclicPrimaryBank q 2 (recohCanonicalPrimaryData q 2) i) ^
        recohStableBinaryMultiplier q entries i) S‖ := by
  let chi := recohCyclicPrimaryBank q 2 (recohCanonicalPrimaryData q 2) i
  let m := 2 ^ (recohCanonicalPrimaryData q 2).exponent i
  have hm : 0 < m := by dsimp [m]; positivity
  have hpow (x : (i : Fin d) → ZMod (q i)) : (chi x) ^ (2 * m) = 1 := by
    simpa [chi, m, pow_succ, Nat.mul_comm] using
      recoh_cyclic_primary_bank_pow q 2 (recohCanonicalPrimaryData q 2) i x
  obtain ⟨a, b, c, hab, hac, hbc, hdisplay⟩ := Finset.card_eq_three.mp hS
  let actual := fun j => (recohSupportProbe (chi ^ (2 * j + 1)) S) ^ 2
  let centre := fun j => recohRationalComplexValue
    (recohSquarePhaseCenter q entries i.val
      (2 ^ ((recohCanonicalPrimaryData q 2).exponent i + 1)) (2 * j + 1) 4 48)
  have henergy (j : ℕ) : ‖actual j‖ = recohOddPowerEnergy (chi a) (chi b) (chi c) j := by
    dsimp [actual, recohOddPowerEnergy]
    rw [norm_pow, hdisplay, recoh_support_probe_three _ _ _ _ hab hac hbc]
    simp only [AddChar.pow_apply]
  have hsq (j : ℕ) : (recohStableBinarySquareNorm q entries i j : ℝ) = ‖centre j‖ ^ 2 := by
    have h := recoh_rational_squared_distance_exact
      (recohSquarePhaseCenter q entries i.val
        (2 ^ ((recohCanonicalPrimaryData q 2).exponent i + 1)) (2 * j + 1) 4 48) (0, 0)
    have hz : recohRationalComplexValue (0, 0) = 0 := by
      apply Complex.ext <;> simp [recohRationalComplexValue]
    rw [hz, sub_zero] at h
    simpa only [recohStableBinarySquareNorm, centre] using h.symm
  have herr (j : ℕ) : ‖centre j - actual j‖ ≤ (1 / 2 : ℝ) := by
    have h := recoh_square_phase_center_error q entries S hS hR i.val
      (2 ^ ((recohCanonicalPrimaryData q 2).exponent i + 1))
      (recoh_primary_factor_dvd q 2 (recohCanonicalPrimaryData q 2) i)
      (2 * j + 1) 4 48 recoh_stable_selection_precision.1 recoh_stable_selection_precision.2.1
    have he : 9 * (recohRationalPhaseError 4 48 : ℝ) ≤ (1 / 2 : ℝ) := by
      simpa only [Rat.cast_mul, Rat.cast_div, Rat.cast_ofNat, Rat.cast_one] using
        (Rat.cast_le (K := ℝ)).mpr recoh_stable_selection_precision.2.2
    exact h.trans he
  have henergySelected := recoh_odd_squared_selected_energy_ge_one m hm
    (chi a) (chi b) (chi c) (hpow a) (hpow b) (hpow c)
    actual centre (recohStableBinarySquareNorm q entries i)
    (fun j _ => henergy j) (fun j _ => hsq j) (fun j _ => herr j)
  rw [← henergy] at henergySelected
  change 1 ≤ ‖recohSupportProbe (chi ^ recohStableBinaryMultiplier q entries i) S‖
  have hnorm : 0 ≤ ‖recohSupportProbe (chi ^ recohStableBinaryMultiplier q entries i) S‖ := norm_nonneg _
  change 1 ≤ ‖recohSupportProbe
    (chi ^ (2 * recohOddSquaredChoice m (recohStableBinarySquareNorm q entries i) + 1)) S ^ 2‖ at henergySelected
  rw [norm_pow] at henergySelected
  change 1 ≤ ‖recohSupportProbe
    (chi ^ recohStableBinaryMultiplier q entries i) S‖ ^ 2 at henergySelected
  nlinarith only [henergySelected, hnorm]

end Couret.STROBO2TORS


theorem solution : ∀ {d : Nat} (q : Fin d → Nat)
  [inst : ∀ (i : Fin d), @NeZero.{0} Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass) (q i)]
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
      ∀ (i : @Couret.STROBO2TORS.RecohEvenCoordinate d q),
        @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
          (@Norm.norm.{0} Complex Complex.instNorm
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
                (@Couret.STROBO2TORS.recohCyclicPrimaryBank d q
                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) Nat.fact_prime_two
                  (@Couret.STROBO2TORS.recohCanonicalPrimaryData d q inst
                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) Nat.fact_prime_two)
                  i)
                (@Couret.STROBO2TORS.recohStableBinaryMultiplier d q inst entries i))
              S)) := @_root_.Couret.STROBO2TORS.p2m_local_recoh_stable_binary_amplitude

