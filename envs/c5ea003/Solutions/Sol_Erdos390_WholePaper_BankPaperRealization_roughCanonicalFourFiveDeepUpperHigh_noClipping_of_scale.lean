-- Prove2me | solution 1 for Erdos390.WholePaper.BankPaperRealization.roughCanonicalFourFiveDeepUpperHigh_noClipping_of_scale
-- status  : ACCEPTED   (prove)
-- author  : @doctosil
-- created : 2026-09-17T15:59:07.316876+00:00
-- url     : https://prove2.me/submissions/99ca5010-816e-44c9-9f05-6e7ea5f602fa

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

/-- A real comparison between the literal exceptional threshold and a
quotient descends to the corresponding natural floors. -/
theorem roughCanonicalRealExceptionalRoughCutoff_le_natQuotient_of_real_le
    {n N b : Nat} {deltaStar : Real}
    (hreal :
      2 * (n : Real) / (n : Real) ^ deltaStar <=
        (N : Real) / (b : Real)) :
    roughCanonicalRealExceptionalRoughCutoff n deltaStar <= N / b := by
  unfold roughCanonicalRealExceptionalRoughCutoff
  rw [← Nat.floor_div_eq_div (K := Real)]
  exact Nat.floor_mono hreal

/-- On a deep core, once `n^deltaStar >= 2` and the high displacement has
length at most `n/2`, clipping moves neither the upper nor the high lower
quotient endpoint. -/
theorem roughCanonicalFourFiveDeepUpperHigh_noClipping_of_scale
    {K0 n b : Nat} {c deltaStar : Real}
    (hn : 0 < n)
    (hpowerTwo : 2 <= (n : Real) ^ deltaStar)
    (hdepth :
      (K0 + 1) * upperTailLength c n <= n / 2)
    (hb :
      b ∈ Finset.Icc 1
        (tangentPaperExceptionalCutoff deltaStar n / 2)) :
    roughCanonicalRealExceptionalRoughCutoff n deltaStar <=
        (2 * n) / b ∧
      roughCanonicalRealExceptionalRoughCutoff n deltaStar <=
        (2 * n - (K0 + 1) * upperTailLength c n) / b := by
  have hbData := Finset.mem_Icc.mp hb
  have hbPosNat : 0 < b := by omega
  have hbPos : (0 : Real) < (b : Real) := by
    exact_mod_cast hbPosNat
  have hnReal : (0 : Real) < (n : Real) := by
    exact_mod_cast hn
  have hpowerPos : 0 < (n : Real) ^ deltaStar :=
    Real.rpow_pos_of_pos hnReal deltaStar
  have hbTwoNat :
      2 * b <= tangentPaperExceptionalCutoff deltaStar n := by
    omega
  have hbTwo :
      (2 : Real) * (b : Real) <=
        (tangentPaperExceptionalCutoff deltaStar n : Real) := by
    exact_mod_cast hbTwoNat
  have hcutUpper :=
    tangentPaperExceptionalCutoff_cast_lt_add_one deltaStar n
  have hbPower :
      2 * (b : Real) <= (n : Real) ^ deltaStar + 1 :=
    hbTwo.trans hcutUpper.le
  have hbLePower :
      (b : Real) <= (n : Real) ^ deltaStar := by
    nlinarith
  have hupperReal :
      2 * (n : Real) / (n : Real) ^ deltaStar <=
        ((2 * n : Nat) : Real) / (b : Real) := by
    norm_num only [Nat.cast_mul, Nat.cast_ofNat]
    exact
      div_le_div_of_nonneg_left
        (by positivity) hbPos hbLePower
  have hdepthTwo :
      (K0 + 1) * upperTailLength c n <= 2 * n := by
    omega
  have hdepthReal :
      (((K0 + 1) * upperTailLength c n : Nat) : Real) <=
        (n : Real) / 2 := by
    calc
      (((K0 + 1) * upperTailLength c n : Nat) : Real) <=
          ((n / 2 : Nat) : Real) := by exact_mod_cast hdepth
      _ <= (n : Real) / 2 := Nat.cast_div_le (α := Real)
  have hleft :
      2 * (n : Real) * (b : Real) <=
        (n : Real) * ((n : Real) ^ deltaStar + 1) := by
    calc
      2 * (n : Real) * (b : Real) =
          (n : Real) * (2 * (b : Real)) := by ring
      _ <= (n : Real) * ((n : Real) ^ deltaStar + 1) :=
        mul_le_mul_of_nonneg_left hbPower hnReal.le
  have hpowerThreeHalves :
      (n : Real) ^ deltaStar + 1 <=
        (3 / 2 : Real) * (n : Real) ^ deltaStar := by
    nlinarith
  have hmiddle :
      (n : Real) * ((n : Real) ^ deltaStar + 1) <=
        (n : Real) * ((3 / 2 : Real) * (n : Real) ^ deltaStar) :=
    mul_le_mul_of_nonneg_left hpowerThreeHalves hnReal.le
  have hremaining :
      (3 / 2 : Real) * (n : Real) <=
        (2 * n - (K0 + 1) * upperTailLength c n : Nat) := by
    rw [Nat.cast_sub hdepthTwo]
    rw [show ((2 * n : Nat) : Real) =
        2 * (n : Real) by norm_num]
    linarith
  have hright :
      (n : Real) * ((3 / 2 : Real) * (n : Real) ^ deltaStar) <=
        (n : Real) ^ deltaStar *
          (2 * n - (K0 + 1) * upperTailLength c n : Nat) := by
    calc
      (n : Real) * ((3 / 2 : Real) * (n : Real) ^ deltaStar) =
          (n : Real) ^ deltaStar * ((3 / 2 : Real) * (n : Real)) := by
        ring
      _ <=
          (n : Real) ^ deltaStar *
            (2 * n - (K0 + 1) * upperTailLength c n : Nat) :=
        mul_le_mul_of_nonneg_left hremaining hpowerPos.le
  have hhighCross :
      2 * (n : Real) * (b : Real) <=
        (n : Real) ^ deltaStar *
          (2 * n - (K0 + 1) * upperTailLength c n : Nat) :=
    hleft.trans (hmiddle.trans hright)
  have hhighReal :
      2 * (n : Real) / (n : Real) ^ deltaStar <=
        ((2 * n - (K0 + 1) * upperTailLength c n : Nat) : Real) /
          (b : Real) := by
    apply (div_le_div_iff₀ hpowerPos hbPos).2
    simpa only [mul_comm] using hhighCross
  exact
    ⟨roughCanonicalRealExceptionalRoughCutoff_le_natQuotient_of_real_le
        hupperReal,
      roughCanonicalRealExceptionalRoughCutoff_le_natQuotient_of_real_le
        hhighReal⟩





/-! ## The clipped broad endpoint -/





/-! ## Adapter-facing package -/











/-! ## Eventual deep-core form -/







end BankPaperRealization

end

end Erdos390.WholePaper

end

theorem solution :
∀ {K0 n b : Nat} {c deltaStar : Real},
  @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) n →
    @LE.le.{0} Real Real.instLE
        (@OfNat.ofNat.{0} Real (nat_lit 2)
          (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
            (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
              (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
        (@HPow.hPow.{0, 0, 0} Real Real Real (@instHPow.{0, 0} Real Real Real.instPow)
          (@Nat.cast.{0} Real Real.instNatCast n) deltaStar) →
      @LE.le.{0} Nat instLENat
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) K0
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
            (Erdos390.WholePaper.upperTailLength c n))
          (@HDiv.hDiv.{0, 0, 0} Nat Nat Nat (@instHDiv.{0} Nat Nat.instDiv) n
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) →
        @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
            (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat))
            (@Finset.Icc.{0} Nat Nat.instPreorder Nat.instLocallyFiniteOrder
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
              (@HDiv.hDiv.{0, 0, 0} Nat Nat Nat (@instHDiv.{0} Nat Nat.instDiv)
                (Erdos390.WholePaper.tangentPaperExceptionalCutoff deltaStar n)
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
            b →
          And
            (@LE.le.{0} Nat instLENat
              (Erdos390.WholePaper.BankPaperRealization.roughCanonicalRealExceptionalRoughCutoff n deltaStar)
              (@HDiv.hDiv.{0, 0, 0} Nat Nat Nat (@instHDiv.{0} Nat Nat.instDiv)
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) n)
                b))
            (@LE.le.{0} Nat instLENat
              (Erdos390.WholePaper.BankPaperRealization.roughCanonicalRealExceptionalRoughCutoff n deltaStar)
              (@HDiv.hDiv.{0, 0, 0} Nat Nat Nat (@instHDiv.{0} Nat Nat.instDiv)
                (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) n)
                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) K0
                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                    (Erdos390.WholePaper.upperTailLength c n)))
                b)) := by
  exact @Erdos390.WholePaper.BankPaperRealization.roughCanonicalFourFiveDeepUpperHigh_noClipping_of_scale
