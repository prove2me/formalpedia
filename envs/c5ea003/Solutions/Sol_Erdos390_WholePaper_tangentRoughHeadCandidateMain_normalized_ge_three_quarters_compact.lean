-- Prove2me | solution 1 for Erdos390.WholePaper.tangentRoughHeadCandidateMain_normalized_ge_three_quarters_compact
-- status  : ACCEPTED   (prove)
-- author  : @doctosil
-- created : 2026-09-17T17:52:54.114591+00:00
-- url     : https://prove2.me/submissions/660089cf-323a-4764-b9f7-cb5a0277c3be

import Definitions.Def_erdos390_remaining_analytic_propositions_008
import Mathlib
import Definitions.Def_erdos390_source_bank_interface
import Definitions.Def_erdos390_dickman_step_function
import Theorems.Thm_MediumPNT
import Definitions.Def_erdos390_analytic_foundations_001
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_product_bound
import Theorems.Thm_Erdos390_Full_DickmanBasic_rho_pos_on_zero_five
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_secondDerivative_first_bound
import Definitions.Def_erdos390_analytic_foundations_006
import Definitions.Def_erdos390_analytic_foundations_007
import Definitions.Def_erdos390_analytic_foundations_008

/- Source module: Erdos390.Full.HeadPattern -/
section


/-!
# Exact finite head patterns

The marked smooth cells impose exact valuations at finitely many fixed head
primes.  This file records their integral factor and modulus and proves the
factorization/divisibility part of the inclusion--exclusion reduction.  No
smooth-number asymptotic is used here.
-/

open scoped BigOperators
open scoped ArithmeticFunction.Moebius

namespace Erdos390.Full.HeadPattern



namespace Pattern

variable (P : Pattern)











theorem modulus_ne_zero : P.modulus ≠ 0 := by
  rw [modulus]
  apply Finset.prod_ne_zero_iff.mpr
  intro p hp
  exact (P.prime_mem p hp).ne_zero























end Pattern

end Erdos390.Full.HeadPattern

end

/- Source module: Erdos390.WholePaper.RoughHeadCompatibleFinitePoint -/
section


/-!
# The literal head-compatible finite raw point

This file constructs the first finite point in the guarded rough selector.
The upper block `E`, the high lower block `H`, and the broad lower block `J`
are literal natural-number half-open intervals.  Head freedom is imposed by
coprimality with the product of all primes up to `W`, and the raw weight is
defined pointwise from those finite sets.

The second half proves the exact deterministic identities used before any
HT--Saias or prime-number estimate: finite Möbius inclusion--exclusion,
reindexing of smooth multiples by division, and the resulting physical-block
shift through every divisor of the head modulus.
-/

open scoped BigOperators ArithmeticFunction.Moebius

namespace Erdos390.WholePaper

open Erdos390.Full.HeadPattern
open Erdos390.Full.StructuredCells

noncomputable section

/-! ## Literal physical intervals -/





















/-! ## The finite head and raw weights -/









/-- The head modulus is always positive, including for an empty head. -/
theorem roughHeadModulus_pos (W : ℕ) :
    0 < roughHeadModulus W := by
  rw [← roughHeadZeroPattern_modulus]
  exact Nat.pos_of_ne_zero (roughHeadZeroPattern W).modulus_ne_zero



/-- The complete zero-head stratum has strictly positive density. -/
theorem roughHeadDensity_pos (W : ℕ) :
    0 < roughHeadDensity W := by
  have hmod : (0 : ℝ) < (roughHeadModulus W : ℝ) := by
    exact_mod_cast roughHeadModulus_pos W
  have htot : (0 : ℝ) < ((roughHeadModulus W).totient : ℝ) := by
    exact_mod_cast Nat.totient_pos.mpr (roughHeadModulus_pos W)
  exact div_pos htot hmod



































/-! ## Exact head inclusion--exclusion and smooth physical shifts -/

















end

end Erdos390.WholePaper

end

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





















/-! ## The harmonic main term -/





/-! ## Moving-scale negligibility -/





/-! ## Eventual exceptional-loss absorption -/





/-! ## The fixed-head candidate at the paper endpoints -/

/-- Pointwise normalized candidate estimate.  The two hypotheses are exactly
the moving `K*h` loss and the fixed-modulus/floor loss; the eventual theorem
below proves both from the literal paper scales. -/
theorem tangentRoughHeadCandidateMain_normalized_ge_three_quarters
    {W n K h u v : ℕ} {r0 : ℝ}
    (hn : 0 < n) (hu : 0 < u) (hv : 0 < v)
    (hr0one : 1 < r0) (hr0two : r0 < 2)
    (hratio : (u : ℝ) / (v : ℝ) ≤ r0)
    (htail :
      roughHeadDensity W *
          (((K * h : ℕ) : ℝ) / (n : ℝ)) ≤
        tangentPaperHeadGap W r0 / 16)
    (hhead :
      (u : ℝ) / (n : ℝ) *
          (roughHeadDensity W + (roughHeadModulus W : ℝ)) ≤
        tangentPaperHeadGap W r0 / 16) :
    n / v ≤ tangentBroadUpper n K h / u ∧
      3 * tangentPaperHeadGap W r0 / 4 ≤
        (u : ℝ) / (n : ℝ) *
          tangentRoughHeadCandidateMain W n K h u v := by
  let d : ℝ := roughHeadDensity W
  let P : ℝ := roughHeadModulus W
  let gap : ℝ := tangentPaperHeadGap W r0
  have hd : 0 < d := by
    dsimp only [d]
    exact roughHeadDensity_pos W
  have hP : 0 < P := by
    dsimp only [P]
    exact_mod_cast roughHeadModulus_pos W
  have hgap : 0 < gap := by
    dsimp only [gap, tangentPaperHeadGap]
    exact mul_pos (roughHeadDensity_pos W) (sub_pos.mpr hr0two)
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have huR : (0 : ℝ) < u := by exact_mod_cast hu
  have hvR : (0 : ℝ) < v := by exact_mod_cast hv
  have htail' :
      d * (((K * h : ℕ) : ℝ) / (n : ℝ)) ≤ gap / 16 := by
    simpa only [d, gap] using htail
  have hhead' :
      (u : ℝ) / (n : ℝ) * (d + P) ≤ gap / 16 := by
    simpa only [d, P, gap] using hhead
  have hgapIdentity : gap = d * (2 - r0) := by
    simp only [gap, d, tangentPaperHeadGap]
  have htailRatio :
      (((K * h : ℕ) : ℝ) / (n : ℝ)) ≤ (2 - r0) / 16 := by
    refine le_of_mul_le_mul_left ?_ hd
    calc
      d * (((K * h : ℕ) : ℝ) / (n : ℝ)) ≤ gap / 16 := htail'
      _ = d * ((2 - r0) / 16) := by
        rw [hgapIdentity]
        ring
  have huRatio : (u : ℝ) / (n : ℝ) ≤ (2 - r0) / 16 := by
    have hscaled :
        (u : ℝ) / (n : ℝ) * d ≤ gap / 16 := by
      exact (mul_le_mul_of_nonneg_left
        (show d ≤ d + P by linarith) (div_nonneg huR.le hnR.le)).trans hhead'
    refine le_of_mul_le_mul_right ?_ hd
    calc
      (u : ℝ) / (n : ℝ) * d ≤ gap / 16 := hscaled
      _ = (2 - r0) / 16 * d := by
        rw [hgapIdentity]
        ring
  have htailLtOne : (((K * h : ℕ) : ℝ) / (n : ℝ)) < 1 :=
    htailRatio.trans_lt (by linarith)
  have hKhLt : K * h < n := by
    have hcast : (((K * h : ℕ) : ℝ)) < (n : ℝ) :=
      (div_lt_one hnR).mp htailLtOne
    exact_mod_cast hcast
  have hKhTwo : K * h ≤ 2 * n := by omega
  have hbroadCast : (tangentBroadUpper n K h : ℝ) =
      2 * (n : ℝ) - ((K * h : ℕ) : ℝ) := by
    unfold tangentBroadUpper
    rw [Nat.cast_sub hKhTwo]
    push_cast
    ring
  have hratioScaled :
      (n : ℝ) / (v : ℝ) ≤
        r0 * ((n : ℝ) / (u : ℝ)) := by
    calc
      (n : ℝ) / (v : ℝ) =
          ((n : ℝ) / (u : ℝ)) *
            ((u : ℝ) / (v : ℝ)) := by
        field_simp [huR.ne', hvR.ne']
      _ ≤ ((n : ℝ) / (u : ℝ)) * r0 :=
        mul_le_mul_of_nonneg_left hratio
          (div_nonneg hnR.le huR.le)
      _ = r0 * ((n : ℝ) / (u : ℝ)) := by ring
  have hcoefficient :
      r0 < 2 -
          (((K * h : ℕ) : ℝ) / (n : ℝ)) -
          ((u : ℝ) / (n : ℝ)) := by
    nlinarith
  have hrealGap :
      r0 * ((n : ℝ) / (u : ℝ)) <
        (tangentBroadUpper n K h : ℝ) / (u : ℝ) - 1 := by
    calc
      r0 * ((n : ℝ) / (u : ℝ)) <
          ((n : ℝ) / (u : ℝ)) *
            (2 - (((K * h : ℕ) : ℝ) / (n : ℝ)) -
              ((u : ℝ) / (n : ℝ))) := by
        simpa only [mul_comm] using
          mul_lt_mul_of_pos_left hcoefficient (div_pos hnR huR)
      _ = (tangentBroadUpper n K h : ℝ) / (u : ℝ) - 1 := by
        rw [hbroadCast]
        field_simp [hnR.ne', huR.ne']
  have hquotientLower :
      (tangentBroadUpper n K h : ℝ) / (u : ℝ) - 1 <
        ((tangentBroadUpper n K h / u : ℕ) : ℝ) := by
    rw [sub_lt_iff_lt_add]
    apply (div_lt_iff₀ huR).2
    have hnat := (Nat.div_lt_iff_lt_mul hu).mp
      (Nat.lt_succ_self (tangentBroadUpper n K h / u))
    exact_mod_cast hnat
  have hlowerQuotient :
      ((n / v : ℕ) : ℝ) ≤ (n : ℝ) / (v : ℝ) :=
    Nat.cast_div_le
  have hinterval : n / v ≤ tangentBroadUpper n K h / u := by
    have hcastInterval :
        ((n / v : ℕ) : ℝ) ≤
          ((tangentBroadUpper n K h / u : ℕ) : ℝ) :=
      (hlowerQuotient.trans_lt
        (hratioScaled.trans_lt (hrealGap.trans hquotientLower))).le
    exact_mod_cast hcastInterval
  have hsubLower :
      (2 - r0) * ((n : ℝ) / (u : ℝ)) -
          (((K * h : ℕ) : ℝ) / (u : ℝ)) - 1 ≤
        (((tangentBroadUpper n K h / u - n / v : ℕ) : ℝ)) := by
    rw [Nat.cast_sub hinterval]
    calc
      (2 - r0) * ((n : ℝ) / (u : ℝ)) -
          (((K * h : ℕ) : ℝ) / (u : ℝ)) - 1 ≤
        (tangentBroadUpper n K h : ℝ) / (u : ℝ) - 1 -
          (n : ℝ) / (v : ℝ) := by
        calc
          (2 - r0) * ((n : ℝ) / (u : ℝ)) -
              (((K * h : ℕ) : ℝ) / (u : ℝ)) - 1 =
            (tangentBroadUpper n K h : ℝ) / (u : ℝ) - 1 -
              r0 * ((n : ℝ) / (u : ℝ)) := by
                rw [hbroadCast]
                ring
          _ ≤ (tangentBroadUpper n K h : ℝ) / (u : ℝ) - 1 -
              (n : ℝ) / (v : ℝ) := by linarith
      _ ≤ ((tangentBroadUpper n K h / u : ℕ) : ℝ) -
          ((n / v : ℕ) : ℝ) := by
        linarith
  have halgebra :
      (u : ℝ) / (n : ℝ) *
          (d * ((2 - r0) * ((n : ℝ) / (u : ℝ)) -
              (((K * h : ℕ) : ℝ) / (u : ℝ)) - 1) - P) =
        gap - d * (((K * h : ℕ) : ℝ) / (n : ℝ)) -
          (u : ℝ) / (n : ℝ) * (d + P) := by
    rw [hgapIdentity]
    field_simp [hnR.ne', huR.ne']
    ring
  constructor
  · exact hinterval
  · calc
      3 * gap / 4 ≤ gap - gap / 16 - gap / 16 := by linarith
      _ ≤ gap - d * (((K * h : ℕ) : ℝ) / (n : ℝ)) -
          (u : ℝ) / (n : ℝ) * (d + P) := by linarith
      _ = (u : ℝ) / (n : ℝ) *
          (d * ((2 - r0) * ((n : ℝ) / (u : ℝ)) -
              (((K * h : ℕ) : ℝ) / (u : ℝ)) - 1) - P) :=
        halgebra.symm
      _ ≤ (u : ℝ) / (n : ℝ) *
          (d * (((tangentBroadUpper n K h / u - n / v : ℕ) : ℝ)) - P) := by
        exact mul_le_mul_of_nonneg_left
          (sub_le_sub_right (mul_le_mul_of_nonneg_left hsubLower hd.le) P)
          (div_nonneg huR.le hnR.le)
      _ = (u : ℝ) / (n : ℝ) *
          tangentRoughHeadCandidateMain W n K h u v := by
        simp only [tangentRoughHeadCandidateMain, d, P]



/-! ## The literal candidate floor absorbs every canonical loss -/



/-! ## Paper-facing clean-list theorem with no arithmetic loss premise -/

namespace BankPaperRealization



end BankPaperRealization

end

end Erdos390.WholePaper

end

theorem solution : Erdos390.RemainingAnalyticGoal008_040 := by
  exact @Erdos390.WholePaper.tangentRoughHeadCandidateMain_normalized_ge_three_quarters
