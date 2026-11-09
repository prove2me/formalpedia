-- Prove2me | solution 1 for Couret.STROBO2TORS.recoh_rational_root_power_error
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:04:28.504005+00:00
-- url     : https://prove2.me/submissions/9a9b9d8d-1f01-494c-aa04-5b554f5322b3

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
import Theorems.Thm_Couret_STROBO2TORS_recoh_rational_phase_error
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

theorem recoh_cyclic_root_pow_phase (N e : ℕ) [NeZero N] :
    recohCyclicRoot N ^ e =
      Complex.exp (Complex.I * ((2 * Real.pi * (((e % N : ℕ) : ℚ) / N : ℚ) : ℝ) : ℂ)) := by
  have hroot : recohCyclicRoot N = Complex.exp (2 * Real.pi * Complex.I / N) := by
    simpa only [recohCyclicRoot, Int.cast_one, mul_one] using
      (ZMod.stdAddChar_coe (N := N) (1 : ℤ))
  calc
    recohCyclicRoot N ^ e = recohCyclicRoot N ^ (e % N) := by
      simpa only [← (recoh_cyclic_root_primitive N).eq_orderOf] using
        (pow_mod_orderOf (recohCyclicRoot N) e).symm
    _ = Complex.exp ((e % N : ℕ) * (2 * Real.pi * Complex.I / N)) := by
      rw [hroot, Complex.exp_nat_mul]
    _ = _ := by congr 1; push_cast; ring



/-- The rational centre approximates the actual canonical cyclic root. -/
theorem p2m_local_recoh_rational_root_power_error (N e machinTerms taylorTerms : ℕ) [NeZero N]
    (hpi : |recohPiPartial machinTerms| ≤ 4) (htaylor : 15 ≤ taylorTerms) :
    ‖recohRationalComplexValue (recohRationalRootPower N e machinTerms taylorTerms) -
      recohCyclicRoot N ^ e‖ ≤ (recohRationalPhaseError machinTerms taylorTerms : ℝ) := by
  rw [norm_sub_rev, recoh_cyclic_root_pow_phase]
  apply recoh_rational_phase_error _ _ _ _ hpi htaylor
  have hN : (0 : ℚ) < N := by exact_mod_cast (NeZero.pos N)
  rw [abs_of_nonneg (by positivity)]
  apply (div_le_one hN).mpr
  exact_mod_cast (Nat.le_of_lt (Nat.mod_lt e (NeZero.pos N)))



variable {d : ℕ} (q : Fin d → ℕ) [∀ i, NeZero (q i)]

























end Couret.STROBO2TORS


theorem solution : ∀ (N e machinTerms taylorTerms : Nat) [inst : @NeZero.{0} Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass) N],
  @LE.le.{0} Rat Rat.instLE (@abs.{0} Rat Rat.instLattice Rat.addGroup (Couret.STROBO2TORS.recohPiPartial machinTerms))
      (@OfNat.ofNat.{0} Rat (nat_lit 4) (@Rat.instOfNat (nat_lit 4))) →
    @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 15) (instOfNatNat (nat_lit 15))) taylorTerms →
      @LE.le.{0} Real Real.instLE
        (@Norm.norm.{0} Complex Complex.instNorm
          (@HSub.hSub.{0, 0, 0} Complex Complex Complex (@instHSub.{0} Complex Complex.instSub)
            (Couret.STROBO2TORS.recohRationalComplexValue
              (Couret.STROBO2TORS.recohRationalRootPower N e machinTerms taylorTerms))
            (@HPow.hPow.{0, 0, 0} Complex Nat Complex
              (@instHPow.{0, 0} Complex Nat
                (@Monoid.toPow.{0} Complex (@Semiring.toMonoid.{0} Complex Complex.instSemiring)))
              (@Couret.STROBO2TORS.recohCyclicRoot N inst) e)))
        (@Rat.cast.{0} Real Real.instRatCast (Couret.STROBO2TORS.recohRationalPhaseError machinTerms taylorTerms)) := @_root_.Couret.STROBO2TORS.p2m_local_recoh_rational_root_power_error

