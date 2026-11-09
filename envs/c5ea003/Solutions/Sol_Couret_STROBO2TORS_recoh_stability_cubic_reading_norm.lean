-- Prove2me | solution 1 for Couret.STROBO2TORS.recoh_stability_cubic_reading_norm
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T19:52:33.906348+00:00
-- url     : https://prove2.me/submissions/453dd733-6203-42ad-98e5-2528349935d9

import Aesop
import Definitions.Def_Couret_RecohProbeStability_e389a2280f15
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Group.AddChar
import Mathlib.Algebra.Module.ZMod
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Finite.Card
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
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Definitions.Def_Couret_RecohProbeStability_e389a2280f15

set_option autoImplicit false

/-!
Exact separation constants in the exceptional normal form.  Binary probes
have amplitudes one or three, and a detecting ternary probe separates the
two orbits by exactly twice the square root of three.  The two-torsion pair
inside the normal form supplies a matching universal upper bound of two.
-/

namespace Couret.STROBO2TORS

/-- A nontrivial cubic root satisfies its quadratic cyclotomic relation. -/
theorem recoh_stability_cubic_relation (z : ℂ) (hz : z ^ 3 = 1) (hne : z ≠ 1) :
    z ^ 2 + z + 1 = 0 := by
  have hprod : (z - 1) * (z ^ 2 + z + 1) = 0 := by
    calc
      (z - 1) * (z ^ 2 + z + 1) = z ^ 3 - 1 := by ring
      _ = 0 := by rw [hz]; ring
  exact (mul_eq_zero.mp hprod).resolve_left (sub_ne_zero.mpr hne)

/-- The exceptional three-primary coefficient has exact amplitude sqrt 3. -/
theorem p2m_local_recoh_stability_cubic_reading_norm (z : ℂ) (hz : z ^ 3 = 1) (hne : z ≠ 1) :
    ‖1 + 2 * z‖ = Real.sqrt 3 := by
  have hnorm : ‖z‖ = 1 := Complex.norm_eq_one_of_pow_eq_one hz (by decide)
  have hunit : z * star z = 1 := by
    simpa [hnorm] using Complex.mul_conj' z
  have hstar : star z = z ^ 2 := by
    calc
      star z = z ^ 3 * star z := by rw [hz, one_mul]
      _ = z ^ 2 * (z * star z) := by ring
      _ = z ^ 2 := by rw [hunit, mul_one]
  have hsum : z + star z = -1 := by
    rw [hstar]
    linear_combination recoh_stability_cubic_relation z hz hne
  have hmul : (1 + 2 * z) * star (1 + 2 * z) = (3 : ℂ) := by
    change (1 + 2 * z) * (starRingEnd ℂ) (1 + 2 * z) = (3 : ℂ)
    simp only [map_add, map_one, map_mul, map_ofNat]
    calc
      (1 + 2 * z) * (1 + 2 * star z) =
          1 + 2 * (z + star z) + 4 * (z * star z) := by ring
      _ = 3 := by rw [hsum, hunit]; ring
  have hsq : ‖1 + 2 * z‖ ^ 2 = (3 : ℝ) := by
    have h := (Complex.mul_conj' (1 + 2 * z)).symm.trans hmul
    have hre := congrArg Complex.re h
    simpa [← Complex.ofReal_pow] using hre
  have hsqrt := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
  nlinarith [norm_nonneg (1 + 2 * z), Real.sqrt_nonneg (3 : ℝ)]

variable {G : Type*} [AddCommGroup G] [DecidableEq G]





variable [Fintype G]





















end Couret.STROBO2TORS


theorem solution : ∀ (z : Complex),
  @Eq.{1} Complex
      (@HPow.hPow.{0, 0, 0} Complex Nat Complex
        (@instHPow.{0, 0} Complex Nat (@Monoid.toPow.{0} Complex (@Semiring.toMonoid.{0} Complex Complex.instSemiring)))
        z (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
      (@OfNat.ofNat.{0} Complex (nat_lit 1) (@One.toOfNat1.{0} Complex Complex.instOne)) →
    @Ne.{1} Complex z (@OfNat.ofNat.{0} Complex (nat_lit 1) (@One.toOfNat1.{0} Complex Complex.instOne)) →
      @Eq.{1} Real
        (@Norm.norm.{0} Complex Complex.instNorm
          (@HAdd.hAdd.{0, 0, 0} Complex Complex Complex (@instHAdd.{0} Complex Complex.instAdd)
            (@OfNat.ofNat.{0} Complex (nat_lit 1) (@One.toOfNat1.{0} Complex Complex.instOne))
            (@HMul.hMul.{0, 0, 0} Complex Complex Complex (@instHMul.{0} Complex Complex.instMul)
              (@OfNat.ofNat.{0} Complex (nat_lit 2)
                (@instOfNatAtLeastTwo.{0} Complex (nat_lit 2) Complex.instNatCast
                  (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                    (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
              z)))
        (Real.sqrt
          (@OfNat.ofNat.{0} Real (nat_lit 3)
            (@instOfNatAtLeastTwo.{0} Real (nat_lit 3) Real.instNatCast
              (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))) := @_root_.Couret.STROBO2TORS.p2m_local_recoh_stability_cubic_reading_norm

