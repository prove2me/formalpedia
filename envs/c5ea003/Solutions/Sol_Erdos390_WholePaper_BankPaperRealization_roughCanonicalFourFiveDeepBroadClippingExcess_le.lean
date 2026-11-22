-- Prove2me | solution 1 for Erdos390.WholePaper.BankPaperRealization.roughCanonicalFourFiveDeepBroadClippingExcess_le
-- status  : ACCEPTED   (prove)
-- author  : @doctosil
-- created : 2026-09-17T15:58:54.519877+00:00
-- url     : https://prove2.me/submissions/7bc114a1-9081-4bb8-8a01-bdba170bae2b

import Mathlib
import Definitions.Def_erdos390_source_bank_interface
import Definitions.Def_erdos390_dickman_step_function
import Theorems.Thm_MediumPNT
import Definitions.Def_erdos390_analytic_foundations_001
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_product_bound
import Theorems.Thm_Erdos390_Full_DickmanBasic_rho_pos_on_zero_five
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_secondDerivative_first_bound
import Definitions.Def_erdos390_analytic_foundations_008
import Definitions.Def_erdos390_analytic_foundations_009

/- Source module: Erdos390.WholePaper.TangentPaperCleanListAbsorption -/
section


/-!
# Closing the paper-scale tangent clean-list inequality

This file fixes the moving parameters used in Section 9 of the paper:

* `h = upperTailLength c n = ceil(c n / log n)`;
* `Phead = roughHeadModulus W`;
* `X0 = ceil(n ^ deltaStar)`;
* `y = yNat n = floor(n ^ (2/9))`;
* `W < v <= u <= y` and `u / v <= r0 < 3/2`.

For fixed `W`, `K`, `c`, `r0`, and `deltaStar`, the head-density gap is

`roughHeadDensity W * (2 - r0)`.

We reserve one sixteenth of that gap as the effective list density.  A
slightly conservative explicit version of the paper's one-time cutoff makes
the canonical Selberg main term at most one quarter of the gap.  The
Lambda-squared endpoint remainder and the sharp bank deletion census are
then `o(n/u)`, uniformly for `u <= yNat n`.  The fixed-modulus endpoint loss,
the natural floors and ceilings, and `K*h` are absorbed at the same scale.

Consequently the final candidate-floor-versus-loss inequality is proved
eventually; it is not retained as a premise of the paper-facing wrapper.
-/

open Filter Topology Asymptotics
open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel
open Erdos390.Full.Scale

noncomputable section

/-! ## Literal Section 9 parameters -/













/-- The safe ceiling changes the paper's real cutoff by strictly less than
one. -/
theorem tangentPaperExceptionalCutoff_cast_lt_add_one
    (deltaStar : ℝ) (n : ℕ) :
    (tangentPaperExceptionalCutoff deltaStar n : ℝ) <
      (n : ℝ) ^ deltaStar + 1 := by
  unfold tangentPaperExceptionalCutoff
  exact Nat.ceil_lt_add_one
    (Real.rpow_nonneg (Nat.cast_nonneg n) deltaStar)







/-! ## The harmonic main term -/





/-! ## Moving-scale negligibility -/





/-! ## Eventual exceptional-loss absorption -/





/-! ## The fixed-head candidate at the paper endpoints -/





/-! ## The literal candidate floor absorbs every canonical loss -/



/-! ## Paper-facing clean-list theorem with no arithmetic loss premise -/

namespace BankPaperRealization



end BankPaperRealization

end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.RoughSaiasSharpCanonicalRowPaperScale -/
section


/-!
# Canonical sharp Saias row-scale geometry

This file specializes the closed sharp endpoint and fixed-head estimates to
the paper's literal balanced raw point.  The high-block multiplicity is
written as `K0 + 1`, so its positivity is built into the data rather than
assumed separately.
-/

open Filter Topology
open scoped BigOperators ArithmeticFunction.Moebius

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.DickmanBasic
open Erdos390.Full.Scale
open Erdos390.Full.StructuredCells

noncomputable section

/-! ## Uniform control of the literal balanced coefficient -/







/-! ## Fixed constants for the three row ledgers -/















/-! ## Quotient and logarithmic geometry -/

/-- A natural quotient differs from the corresponding real quotient by
strictly less than one. -/
theorem roughNatQuotient_sub_realQuotient_abs_lt_one
    {N r : ℕ} (hr : 0 < r) :
    |(((N / r : ℕ) : ℝ)) - (N : ℝ) / (r : ℝ)| < 1 := by
  have hrReal : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr
  have hle :
      (((N / r : ℕ) : ℝ)) ≤ (N : ℝ) / (r : ℝ) :=
    Nat.cast_div_le
  rw [abs_of_nonpos (sub_nonpos.mpr hle), neg_sub]
  have hdecomp :=
    congrArg (fun z : ℕ ↦ (z : ℝ)) (Nat.div_add_mod N r)
  norm_num only [Nat.cast_add, Nat.cast_mul] at hdecomp
  have hmod : (((N % r : ℕ) : ℝ)) < (r : ℝ) := by
    exact_mod_cast Nat.mod_lt N hr
  calc
    (N : ℝ) / (r : ℝ) - ((N / r : ℕ) : ℝ) =
        ((N % r : ℕ) : ℝ) / (r : ℝ) := by
      field_simp [hrReal.ne']
      nlinarith
    _ < 1 := (div_lt_one hrReal).2 hmod

/-- The real quotient lies below the natural quotient plus one. -/
theorem roughRealQuotient_lt_natQuotient_add_one
    {N r : ℕ} (hr : 0 < r) :
    (N : ℝ) / (r : ℝ) < ((N / r : ℕ) : ℝ) + 1 := by
  have hfloor :=
    roughNatQuotient_sub_realQuotient_abs_lt_one
      (N := N) hr
  rw [abs_lt] at hfloor
  linarith

























/-! ## The balanced Dickman main ledger -/





/-! ## The weighted sharp Saias transition ledger -/



/-! ## Absorption of the sharp fixed-head divisor sum -/



/-! ## One unified canonical raw-row allowance -/













end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankPaperCanonicalSignedExceptionalFourFiveDeepEndpointErrorConnector -/
section


/-!
# Endpoint-length errors on the deep exceptional core

The three physical intervals use natural quotient endpoints.  Their lower
endpoints are additionally clipped by the literal real exceptional floor.
This file separates the two effects at a deep smooth core.

* The upper and high lower endpoints are eventually not moved by clipping.
  Their literal lengths therefore differ from the ideal quotient lengths by
  at most one.
* The broad lower endpoint remains clipped.  Its clipping excess is bounded
  directly, and its complete endpoint-length error is
  `O(Z / L + 1)`, where
  `Z = roughCanonicalExceptionalPhysicalRateScale n b`.

The broad statement deliberately retains the `max` in the literal endpoint.
No eventual broad no-clipping assertion is made.
-/

open Filter Topology

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel
open Erdos390.Full.Scale

noncomputable section

namespace BankPaperRealization

/-! ## A generic clipping triangle -/



/-! ## Deep upper/high no-clipping -/









/-! ## The clipped broad endpoint -/

/-- On a deep core, the amount by which the exceptional floor moves the
broad lower quotient endpoint is `O(Z/L+1)`.

The hypothesis `L n <= n^deltaStar` is the only asymptotic comparison used
here.  The `max` is retained in the conclusion. -/
theorem roughCanonicalFourFiveDeepBroadClippingExcess_le
    {n b : Nat} {deltaStar : Real}
    (hn : 0 < n)
    (hLone : 1 <= L n)
    (hLpower : L n <= (n : Real) ^ deltaStar)
    (hb :
      b ∈ Finset.Icc 1
        (tangentPaperExceptionalCutoff deltaStar n / 2)) :
    ((max (n / b)
          (roughCanonicalRealExceptionalRoughCutoff n deltaStar) -
        n / b : Nat) : Real) <=
      roughCanonicalExceptionalPhysicalRateScale n b / L n + 1 := by
  have hbData := Finset.mem_Icc.mp hb
  have hbPosNat : 0 < b := by omega
  have hbPos : (0 : Real) < (b : Real) := by
    exact_mod_cast hbPosNat
  have hnReal : (0 : Real) < (n : Real) := by
    exact_mod_cast hn
  have hL : 0 < L n := zero_lt_one.trans_le hLone
  have hpowerPos : 0 < (n : Real) ^ deltaStar :=
    Real.rpow_pos_of_pos hnReal deltaStar
  have hbTwoNat :
      2 * b <= tangentPaperExceptionalCutoff deltaStar n := by
    omega
  have hbTwo :
      2 * (b : Real) <=
        (tangentPaperExceptionalCutoff deltaStar n : Real) := by
    exact_mod_cast hbTwoNat
  have hcutCeil :=
    tangentPaperExceptionalCutoff_cast_lt_add_one deltaStar n
  have hbPower :
      2 * (b : Real) <= (n : Real) ^ deltaStar + 1 :=
    hbTwo.trans hcutCeil.le
  have hcutFloor :
      (roughCanonicalRealExceptionalRoughCutoff n deltaStar : Real) <=
        2 * (n : Real) / (n : Real) ^ deltaStar := by
    unfold roughCanonicalRealExceptionalRoughCutoff
    exact
      Nat.floor_le
        (div_nonneg (by positivity) hpowerPos.le)
  have hquotientRound :
      (n : Real) / (b : Real) <
        ((n / b : Nat) : Real) + 1 :=
    roughRealQuotient_lt_natQuotient_add_one
      (N := n) hbPosNat
  have hquotientLower :
      (n : Real) / (b : Real) - 1 <=
        ((n / b : Nat) : Real) := by
    linarith
  have hproduct :
      (2 * (b : Real)) * L n <=
        ((n : Real) ^ deltaStar + 1) *
          (n : Real) ^ deltaStar :=
    mul_le_mul hbPower hLpower hL.le (by positivity)
  have hsmall :
      2 * (n : Real) /
            ((n : Real) ^ deltaStar *
              ((n : Real) ^ deltaStar + 1)) <=
        (n : Real) / ((b : Real) * L n) := by
    apply
      (div_le_div_iff₀
        (mul_pos hpowerPos (by positivity))
        (mul_pos hbPos hL)).2
    calc
      (2 * (n : Real)) * ((b : Real) * L n) =
          (n : Real) * ((2 * (b : Real)) * L n) := by ring
      _ <=
          (n : Real) *
            (((n : Real) ^ deltaStar + 1) *
              (n : Real) ^ deltaStar) :=
        mul_le_mul_of_nonneg_left hproduct hnReal.le
      _ =
          (n : Real) *
            ((n : Real) ^ deltaStar *
              ((n : Real) ^ deltaStar + 1)) := by ring
  have hbDenominator :
      (b : Real) <= ((n : Real) ^ deltaStar + 1) / 2 := by
    linarith
  have hpowerAddOneNe :
      (n : Real) ^ deltaStar + 1 ≠ 0 := by
    positivity
  have hquotientModelLower :
      2 * (n : Real) / ((n : Real) ^ deltaStar + 1) <=
        (n : Real) / (b : Real) := by
    calc
      2 * (n : Real) / ((n : Real) ^ deltaStar + 1) =
          (n : Real) /
            (((n : Real) ^ deltaStar + 1) / 2) := by
        field_simp [hpowerAddOneNe]
      _ <= (n : Real) / (b : Real) :=
        div_le_div_of_nonneg_left hnReal.le hbPos hbDenominator
  have hdifference :
      2 * (n : Real) / (n : Real) ^ deltaStar -
          (n : Real) / (b : Real) <=
        (n : Real) / ((b : Real) * L n) := by
    calc
      2 * (n : Real) / (n : Real) ^ deltaStar -
          (n : Real) / (b : Real) <=
        2 * (n : Real) / (n : Real) ^ deltaStar -
          2 * (n : Real) / ((n : Real) ^ deltaStar + 1) :=
        sub_le_sub_left hquotientModelLower _
      _ =
          2 * (n : Real) /
            ((n : Real) ^ deltaStar *
              ((n : Real) ^ deltaStar + 1)) := by
        field_simp [hpowerPos.ne', hpowerAddOneNe]
        ; ring
      _ <= (n : Real) / ((b : Real) * L n) := hsmall
  have hquotientRate :
      (n : Real) / (b : Real) <=
        roughCanonicalExceptionalPhysicalRateScale n b := by
    have hrateNat :
        n / b + 1 <= 3 * n / b + 1 := by
      exact
        Nat.add_le_add_right
          (Nat.div_le_div_right (by omega : n <= 3 * n)) 1
    calc
      (n : Real) / (b : Real) <=
          ((n / b : Nat) : Real) + 1 :=
        hquotientRound.le
      _ = ((n / b + 1 : Nat) : Real) := by norm_num
      _ <= ((3 * n / b + 1 : Nat) : Real) := by
        exact_mod_cast hrateNat
      _ = roughCanonicalExceptionalPhysicalRateScale n b := by
        rfl
  have hquotientRateDiv :
      (n : Real) / ((b : Real) * L n) <=
        roughCanonicalExceptionalPhysicalRateScale n b / L n := by
    calc
      (n : Real) / ((b : Real) * L n) =
          ((n : Real) / (b : Real)) / L n := by ring
      _ <= roughCanonicalExceptionalPhysicalRateScale n b / L n :=
        div_le_div_of_nonneg_right hquotientRate hL.le
  by_cases hclip :
      roughCanonicalRealExceptionalRoughCutoff n deltaStar <= n / b
  · rw [max_eq_left hclip, Nat.sub_self, Nat.cast_zero]
    have hrateNonneg :
        0 <= roughCanonicalExceptionalPhysicalRateScale n b := by
      unfold roughCanonicalExceptionalPhysicalRateScale
      exact_mod_cast (Nat.zero_le (3 * n / b + 1))
    exact add_nonneg
      (div_nonneg hrateNonneg hL.le) (by norm_num)
  · have hquotientCutoff :
        n / b <=
          roughCanonicalRealExceptionalRoughCutoff n deltaStar := by
      omega
    rw [max_eq_right hquotientCutoff,
      Nat.cast_sub hquotientCutoff]
    calc
      (roughCanonicalRealExceptionalRoughCutoff n deltaStar : Real) -
          (n / b : Nat) <=
        2 * (n : Real) / (n : Real) ^ deltaStar -
          ((n : Real) / (b : Real) - 1) :=
        sub_le_sub hcutFloor hquotientLower
      _ =
          (2 * (n : Real) / (n : Real) ^ deltaStar -
            (n : Real) / (b : Real)) + 1 := by ring
      _ <= (n : Real) / ((b : Real) * L n) + 1 :=
        by linarith
      _ <=
          roughCanonicalExceptionalPhysicalRateScale n b / L n + 1 :=
        by linarith



/-! ## Adapter-facing package -/











/-! ## Eventual deep-core form -/







end BankPaperRealization

end

end Erdos390.WholePaper

end

theorem solution :
∀ {n b : Nat} {deltaStar : Real},
  @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) n →
    @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
        (Erdos390.Full.Scale.L n) →
      @LE.le.{0} Real Real.instLE (Erdos390.Full.Scale.L n)
          (@HPow.hPow.{0, 0, 0} Real Real Real (@instHPow.{0, 0} Real Real Real.instPow)
            (@Nat.cast.{0} Real Real.instNatCast n) deltaStar) →
        @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
            (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat))
            (@Finset.Icc.{0} Nat Nat.instPreorder Nat.instLocallyFiniteOrder
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
              (@HDiv.hDiv.{0, 0, 0} Nat Nat Nat (@instHDiv.{0} Nat Nat.instDiv)
                (Erdos390.WholePaper.tangentPaperExceptionalCutoff deltaStar n)
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
            b →
          @LE.le.{0} Real Real.instLE
            (@Nat.cast.{0} Real Real.instNatCast
              (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
                (@Max.max.{0} Nat Nat.instMax (@HDiv.hDiv.{0, 0, 0} Nat Nat Nat (@instHDiv.{0} Nat Nat.instDiv) n b)
                  (Erdos390.WholePaper.BankPaperRealization.roughCanonicalRealExceptionalRoughCutoff n deltaStar))
                (@HDiv.hDiv.{0, 0, 0} Nat Nat Nat (@instHDiv.{0} Nat Nat.instDiv) n b)))
            (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
              (@HDiv.hDiv.{0, 0, 0} Real Real Real
                (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                (Erdos390.WholePaper.BankPaperRealization.roughCanonicalExceptionalPhysicalRateScale n b)
                (Erdos390.Full.Scale.L n))
              (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))) := by
  exact @Erdos390.WholePaper.BankPaperRealization.roughCanonicalFourFiveDeepBroadClippingExcess_le
