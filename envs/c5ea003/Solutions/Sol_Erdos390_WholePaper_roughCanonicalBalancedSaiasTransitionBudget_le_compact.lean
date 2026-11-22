-- Prove2me | solution 1 for Erdos390.WholePaper.roughCanonicalBalancedSaiasTransitionBudget_le_compact
-- status  : ACCEPTED   (prove)
-- author  : @doctosil
-- created : 2026-09-17T17:41:36.924987+00:00
-- url     : https://prove2.me/submissions/3a5a53ed-80c6-4626-be78-f7b611e1dc1c

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
import Definitions.Def_erdos390_analytic_foundations_008
import Definitions.Def_erdos390_analytic_foundations_009

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

/- Source module: Erdos390.WholePaper.FixedModulusReducedResidueCount -/
section


/-!
# Fixed-modulus reduced-residue counts

This file proves the elementary `O_W(1)` input used in the rough selector
and in the tangent-list census.  A reduced-residue predicate is counted on
literal finite intervals by splitting the interval into complete periods
and one remainder.  Multiples of a number coprime to the fixed modulus are
then reindexed exactly by division.

There is no prime-number theorem, smooth-number estimate, or asymptotic
hypothesis in this module.  The final CRT-style error constant is the
explicit number `M + 1`, independent of the multiplier and the interval.
-/

namespace Erdos390.WholePaper

noncomputable section









/-! ## Exact periodic decomposition -/

















/-! ## Explicit fixed-period error -/







/-! ## Exact CRT reindexing and multiplier-independent error -/



/-- Integer quotient lengths differ from real division by less than one.
This is the only extra endpoint cost after the exact multiplication
reindexing. -/
theorem quotientIocLength_sub_realLengthDiv_abs_lt_one
    {D lo hi : ℕ} (hD : 0 < D) (hlohi : lo ≤ hi) :
    |(((hi / D - lo / D : ℕ) : ℝ)) -
        ((hi - lo : ℕ) : ℝ) / (D : ℝ)| < 1 := by
  have hquotient : lo / D ≤ hi / D := Nat.div_le_div_right hlohi
  have hDRealPos : (0 : ℝ) < (D : ℝ) := by
    exact_mod_cast hD
  have hDReal : (D : ℝ) ≠ 0 := hDRealPos.ne'
  have hhi := congrArg (fun z : ℕ ↦ (z : ℝ)) (Nat.mod_add_div hi D)
  have hlo := congrArg (fun z : ℕ ↦ (z : ℝ)) (Nat.mod_add_div lo D)
  simp only [Nat.cast_add, Nat.cast_mul] at hhi hlo
  have herror :
      (((hi / D - lo / D : ℕ) : ℝ)) -
          ((hi - lo : ℕ) : ℝ) / (D : ℝ) =
        ((lo % D : ℕ) : ℝ) / (D : ℝ) -
          ((hi % D : ℕ) : ℝ) / (D : ℝ) := by
    rw [Nat.cast_sub hquotient, Nat.cast_sub hlohi]
    field_simp [hDReal]
    nlinarith [hhi, hlo]
  have hloMod : ((lo % D : ℕ) : ℝ) / (D : ℝ) < 1 := by
    apply (div_lt_one hDRealPos).2
    exact_mod_cast Nat.mod_lt lo hD
  have hhiMod : ((hi % D : ℕ) : ℝ) / (D : ℝ) < 1 := by
    apply (div_lt_one hDRealPos).2
    exact_mod_cast Nat.mod_lt hi hD
  have hloModNonneg :
      0 ≤ ((lo % D : ℕ) : ℝ) / (D : ℝ) :=
    div_nonneg (Nat.cast_nonneg _) hDRealPos.le
  have hhiModNonneg :
      0 ≤ ((hi % D : ℕ) : ℝ) / (D : ℝ) :=
    div_nonneg (Nat.cast_nonneg _) hDRealPos.le
  rw [herror, abs_lt]
  constructor <;> linarith



/-! ## Paper-head specializations -/









end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.RoughSaiasSignedFractionalAbel -/
section


/-!
# Signed fractional correction and finite Abel decomposition for the Saias defect

This file goes one level below
`RoughSaiasReverseNormalFormDefectInvLogSqBound`.  It never assumes a bound
for that defect.  Instead it keeps the quotient fractional correction with
its sign, separates the reverse defect into a continuous normal-form prime
sum and that signed correction, and applies the project's existing finite
theta Abel identity to the continuous prime sum.

The resulting quantitative theorem assumes only a cumulative theta-error
bound.  Its right side is the explicit endpoint-plus-variation ledger for the
Saias theta weight.  Thus the remaining inverse-log-square problem is a
deterministic estimate for the displayed signed Abel center, not a renamed
copy of the original defect bound.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full

noncomputable section

/-! ## One quotient: retain the fractional correction with its sign -/











/-! ## The reverse defect as continuous part plus signed correction -/







/-! ## Exact finite theta Abel identity -/

















/-! ## The floor/frac-paired natural theta weight -/



























/-! ## Quantitative theta transfer, without a defect-bound premise -/













/-! ## Closed fourth-power theta specialization -/



theorem roughSaiasThetaFourthPowerConstant_pos :
    0 < roughSaiasThetaFourthPowerConstant :=
  (Classical.choose_spec
    (FriableAsymptotic.exists_primeLogSumUpTo_error_bound (4 : ℝ))).1









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

/-- The fixed head density is at most one. -/
theorem roughHeadDensity_le_one (W : ℕ) :
    roughHeadDensity W ≤ 1 := by
  have hmod : (0 : ℝ) < (roughHeadModulus W : ℝ) := by
    exact_mod_cast roughHeadModulus_pos W
  have htot :
      ((roughHeadModulus W).totient : ℝ) ≤
        (roughHeadModulus W : ℝ) := by
    exact_mod_cast Nat.totient_le (roughHeadModulus W)
  unfold roughHeadDensity
  exact (div_le_one hmod).2 htot

/-- A lower bound for the integral tail gives a constant bound for the
balanced high-block coefficient. -/
theorem roughHeadBalancedAlpha_abs_le_of_tail_lower
    {W n h K : ℕ} {beta L c : ℝ}
    (hc : 0 < c) (hn : 0 < n) (hK : 0 < K) (hL : 0 < L)
    (htail : c * (n : ℝ) / L ≤ (h : ℝ)) :
    |roughHeadBalancedAlpha W n h K beta L| ≤
      1 / ((K : ℝ) * roughHeadDensity W) +
        |beta| / ((K : ℝ) * c) := by
  have hdelta : 0 < roughHeadDensity W := roughHeadDensity_pos W
  have hnReal : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hKReal : (0 : ℝ) < (K : ℝ) := by exact_mod_cast hK
  have htailPos : 0 < c * (n : ℝ) / L := by positivity
  have hhReal : (0 : ℝ) < (h : ℝ) := htailPos.trans_le htail
  have hden :
      0 < (K : ℝ) * (h : ℝ) := mul_pos hKReal hhReal
  have hsubCast :
      (((n - K * h : ℕ) : ℝ)) ≤ (n : ℝ) := by
    exact_mod_cast Nat.sub_le n (K * h)
  have hsubCastNonneg :
      (0 : ℝ) ≤ (((n - K * h : ℕ) : ℝ)) := by
    positivity
  have hnum :
      |(h : ℝ) / roughHeadDensity W -
          (beta / L) * (((n - K * h : ℕ) : ℝ))| ≤
        (h : ℝ) / roughHeadDensity W +
          |beta| / L * (n : ℝ) := by
    calc
      |(h : ℝ) / roughHeadDensity W -
          (beta / L) * (((n - K * h : ℕ) : ℝ))| ≤
        |(h : ℝ) / roughHeadDensity W| +
          |(beta / L) * (((n - K * h : ℕ) : ℝ))| :=
        abs_sub _ _
      _ = (h : ℝ) / roughHeadDensity W +
          (|beta| / L) * (((n - K * h : ℕ) : ℝ)) := by
        rw [abs_div, abs_of_pos hdelta, abs_of_nonneg hhReal.le,
          abs_mul, abs_div, abs_of_pos hL,
          abs_of_nonneg hsubCastNonneg]
      _ ≤ (h : ℝ) / roughHeadDensity W +
          |beta| / L * (n : ℝ) := by
        exact add_le_add le_rfl
          (mul_le_mul_of_nonneg_left hsubCast
            (div_nonneg (abs_nonneg beta) hL.le))
  have hcross : c * (n : ℝ) ≤ (h : ℝ) * L := by
    have := (div_le_iff₀ hL).mp htail
    simpa only [mul_comm] using this
  have hnDiv : (n : ℝ) ≤ ((h : ℝ) * L) / c :=
    (le_div_iff₀ hc).2 (by
      calc
        (n : ℝ) * c = c * (n : ℝ) := by ring
        _ ≤ (h : ℝ) * L := hcross)
  have hratio :
      (n : ℝ) / ((h : ℝ) * L) ≤ 1 / c := by
    calc
      (n : ℝ) / ((h : ℝ) * L) ≤
          (((h : ℝ) * L) / c) / ((h : ℝ) * L) :=
        div_le_div_of_nonneg_right hnDiv
          (mul_nonneg hhReal.le hL.le)
      _ = 1 / c := by field_simp
  unfold roughHeadBalancedAlpha
  norm_num only [Nat.cast_mul]
  rw [abs_div, abs_of_pos hden]
  calc
    |(h : ℝ) / roughHeadDensity W -
        (beta / L) * (((n - K * h : ℕ) : ℝ))| /
          ((K : ℝ) * (h : ℝ)) ≤
      ((h : ℝ) / roughHeadDensity W +
        |beta| / L * (n : ℝ)) /
          ((K : ℝ) * (h : ℝ)) :=
        (div_le_div_iff_of_pos_right hden).2 hnum
    _ = 1 / ((K : ℝ) * roughHeadDensity W) +
        (|beta| / (K : ℝ)) *
          ((n : ℝ) / ((h : ℝ) * L)) := by
      field_simp [hdelta.ne', hKReal.ne', hhReal.ne', hL.ne']
    _ ≤ 1 / ((K : ℝ) * roughHeadDensity W) +
        (|beta| / (K : ℝ)) * (1 / c) := by
      exact add_le_add le_rfl
        (mul_le_mul_of_nonneg_left hratio
          (div_nonneg (abs_nonneg beta) hKReal.le))
    _ = 1 / ((K : ℝ) * roughHeadDensity W) +
        |beta| / ((K : ℝ) * c) := by
      field_simp [hKReal.ne', hc.ne']

/-- With the paper tail and the positive multiplicity `K0+1`, the
balanced coefficient is uniformly bounded by a constant chosen before
`n`. -/
theorem roughHeadBalancedAlpha_succ_abs_le
    (W K0 : ℕ) {c beta : ℝ} (hc : 0 < c)
    {n : ℕ} (hn : 2 ≤ n) :
    |roughHeadBalancedAlpha W n (upperTailLength c n) (K0 + 1)
        beta (L n)| ≤
      1 / (((K0 + 1 : ℕ) : ℝ) * roughHeadDensity W) +
        |beta| / (((K0 + 1 : ℕ) : ℝ) * c) := by
  have hL : 0 < L n := L_pos (by omega)
  have htail :
      c * (n : ℝ) / L n ≤ (upperTailLength c n : ℝ) := by
    rw [upperTailLength]
    calc
      c * (n : ℝ) / L n = c * secondOrderScale n := by
        unfold secondOrderScale L
        ring
      _ ≤ (Nat.ceil (c * secondOrderScale n) : ℝ) :=
        Nat.le_ceil (c * secondOrderScale n)
  exact roughHeadBalancedAlpha_abs_le_of_tail_lower
    hc (by omega) (by omega) hL htail

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

/-- The length of a quotient interval is bounded by its real length plus
one. -/
theorem roughQuotientGap_cast_le
    {A B r : ℕ} (hr : 0 < r) (hAB : A ≤ B) :
    (((B / r - A / r : ℕ) : ℝ)) ≤
      (((B - A : ℕ) : ℝ)) / (r : ℝ) + 1 := by
  have hfloor :=
    quotientIocLength_sub_realLengthDiv_abs_lt_one hr hAB
  rw [abs_lt] at hfloor
  linarith

/-- For an active row, the doubled quotient is at most three times the
half-scale quotient. -/
theorem roughTwoQuotient_le_three_halfQuotient
    {n r : ℕ} (hr : 0 < r) (hrn : r ≤ n) :
    (2 * n) / r ≤ 3 * (n / r) := by
  have hx : 0 < n / r := Nat.div_pos hrn hr
  have htwo :
      (2 * n) / r ≤ 2 * (n / r) + 1 := by
    have hadd :
        (n + n) / r ≤ n / r + n / r + 1 := by
      rw [Nat.add_div hr]
      split_ifs <;> omega
    simpa only [two_mul] using hadd
  omega

/-- If the upper tail is no longer than `n`, its quotient endpoint is at
most three times the central quotient endpoint. -/
theorem roughUpperQuotient_le_three_centralQuotient
    {n h r : ℕ} (hr : 0 < r) (hrn : r ≤ n) (hh : h ≤ n) :
    (2 * n + h) / r ≤ 3 * ((2 * n) / r) := by
  let X := (2 * n) / r
  have hdecomp := Nat.div_add_mod (2 * n) r
  have hmod := Nat.mod_lt (2 * n) hr
  have hXr : n ≤ X * r := by
    have hdecompX :
        X * r + (2 * n) % r = 2 * n := by
      simpa only [X, Nat.mul_comm] using hdecomp
    have hremLe : (2 * n) % r ≤ n :=
      (Nat.le_of_lt hmod).trans hrn
    omega
  have hnum : 2 * n + h ≤ (3 * X) * r := by
    nlinarith
  have hlt : 2 * n + h < (3 * X + 1) * r := by
    nlinarith
  have hquot :
      (2 * n + h) / r < 3 * X + 1 :=
    (Nat.div_lt_iff_lt_mul hr).2 hlt
  dsimp only [X] at hquot ⊢
  omega









/-- Dividing the paper tail bound by an active row label replaces the real
row scale by the natural row scale plus one. -/
theorem roughTail_div_row_cast_le
    {n h r : ℕ} {c L : ℝ}
    (hr : 0 < r) (hc : 0 ≤ c) (hL : 0 < L)
    (htail : (h : ℝ) ≤ 2 * c * (n : ℝ) / L) :
    (h : ℝ) / (r : ℝ) ≤
      2 * c * (((n / r : ℕ) : ℝ) + 1) / L := by
  have hrReal : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr
  have hnQuot :
      (n : ℝ) / (r : ℝ) ≤
        ((n / r : ℕ) : ℝ) + 1 :=
    (roughRealQuotient_lt_natQuotient_add_one hr).le
  calc
    (h : ℝ) / (r : ℝ) ≤
        (2 * c * (n : ℝ) / L) / (r : ℝ) :=
      div_le_div_of_nonneg_right htail hrReal.le
    _ = 2 * c * ((n : ℝ) / (r : ℝ)) / L := by ring
    _ ≤ 2 * c * (((n / r : ℕ) : ℝ) + 1) / L := by
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hnQuot
          (mul_nonneg (by norm_num) hc))
        hL.le

/-- The elementary scale comparisons repeatedly used below. -/
theorem roughRowScale_elementary
    {x L : ℝ} (hx : 0 ≤ x) (hL : 1 ≤ L) :
    1 ≤ x / L ^ 2 + 1 ∧
    1 / L ≤ x / L ^ 2 + 1 ∧
    (x + 1) / L ^ 2 ≤ x / L ^ 2 + 1 := by
  have hLPos : 0 < L := zero_lt_one.trans_le hL
  have hLSq : 1 ≤ L ^ 2 := by nlinarith
  have hinvL : 1 / L ≤ 1 := (div_le_one hLPos).2 hL
  have hinvLSq : 1 / L ^ 2 ≤ 1 :=
    (div_le_one (sq_pos_of_pos hLPos)).2 hLSq
  have hxScale : 0 ≤ x / L ^ 2 :=
    div_nonneg hx (sq_nonneg L)
  constructor
  · linarith
  constructor
  · exact hinvL.trans (by linarith)
  · calc
      (x + 1) / L ^ 2 =
          x / L ^ 2 + 1 / L ^ 2 := by ring
      _ ≤ x / L ^ 2 + 1 :=
        add_le_add le_rfl hinvLSq







/-! ## The balanced Dickman main ledger -/





/-! ## The weighted sharp Saias transition ledger -/

/-- The three literal weighted sharp Saias pair budgets have the same
canonical row scale. -/
theorem roughCanonicalBalancedSaiasTransitionBudget_le
    (W K0 : ℕ) {c beta : ℝ} (hc : 0 < c)
    {n r y : ℕ} (hn : 2 ≤ n) (hr : 0 < r) (hrn : r ≤ n)
    (_hy : 2 ≤ y)
    (hLone : 1 ≤ L n)
    (hlogY : L n / 5 ≤ Real.log (y : ℝ))
    (htail :
      (upperTailLength c n : ℝ) ≤
        2 * c * (n : ℝ) / L n)
    (hKh :
      (K0 + 1) * upperTailLength c n ≤ n) :
    roughPhysicalSaiasTransitionBudget
        (roughSaiasInvLogSqEndpointRate
          roughSaiasSharpDefectConstant)
        (roughHeadDensity W)
        (roughHeadBalancedAlpha W n (upperTailLength c n)
          (K0 + 1) beta (L n))
        beta (L n)
        ((2 * n + upperTailLength c n) / r)
        ((2 * n) / r)
        ((2 * n - (K0 + 1) * upperTailLength c n) / r)
        (n / r) y ≤
      roughCanonicalSharpTransitionRowScaleConstant W K0 c beta *
        (((n / r : ℕ) : ℝ) / L n ^ 2 + 1) := by
  let K : ℕ := K0 + 1
  let h : ℕ := upperTailLength c n
  let alpha : ℝ :=
    roughHeadBalancedAlpha W n h K beta (L n)
  let x : ℝ := ((n / r : ℕ) : ℝ)
  let S : ℝ := x / L n ^ 2 + 1
  let C : ℝ := roughSaiasSharpDefectConstant
  have hK : 0 < K := by simp [K]
  have hKReal : (0 : ℝ) < (K : ℝ) := by exact_mod_cast hK
  have hLPos : 0 < L n := zero_lt_one.trans_le hLone
  have hlogPos : 0 < Real.log (y : ℝ) := by
    have : 0 < L n / 5 := by positivity
    exact this.trans_le hlogY
  have hdelta0 : 0 ≤ roughHeadDensity W :=
    (roughHeadDensity_pos W).le
  have hdelta1 : roughHeadDensity W ≤ 1 :=
    roughHeadDensity_le_one W
  have hC : 0 ≤ C := by
    dsimp only [C]
    unfold roughSaiasSharpDefectConstant
    have htheta : 0 ≤ roughSaiasThetaFourthPowerConstant :=
      roughSaiasThetaFourthPowerConstant_pos.le
    positivity
  have hxNat : 0 < n / r := Nat.div_pos hrn hr
  have hx : 0 < x := by
    dsimp only [x]
    exact_mod_cast hxNat
  have hscale := roughRowScale_elementary hx.le hLone
  have hSinv : 1 / L n ≤ S := by
    simpa only [S] using hscale.2.1
  have hSplus :
      (x + 1) / L n ^ 2 ≤ S := by
    simpa only [S] using hscale.2.2
  have hSone : 1 ≤ S := by simpa only [S] using hscale.1
  have hSnonneg : 0 ≤ S := le_trans (by norm_num) hSone
  have hinvLSq : 1 / L n ^ 2 ≤ S := by
    have hLSq : 1 ≤ L n ^ 2 := by nlinarith
    exact ((div_le_one (sq_pos_of_pos hLPos)).2 hLSq).trans hSone
  have hxScale : x / L n ^ 2 ≤ S := by
    dsimp only [S]
    linarith
  have hinvL : 1 / L n ≤ 1 :=
    (div_le_one hLPos).2 hLone
  have hinvLog : 1 / Real.log (y : ℝ) ≤ 5 / L n := by
    apply (div_le_div_iff₀ hlogPos hLPos).2
    nlinarith [hlogY]
  have hinvLogSq :
      1 / Real.log (y : ℝ) ^ 2 ≤ 25 / L n ^ 2 := by
    have hsquare :=
      (sq_le_sq₀
        (by positivity :
          0 ≤ 1 / Real.log (y : ℝ))
        (by positivity : 0 ≤ 5 / L n)).2 hinvLog
    calc
      1 / Real.log (y : ℝ) ^ 2 =
          (1 / Real.log (y : ℝ)) ^ 2 := by ring
      _ ≤ (5 / L n) ^ 2 := hsquare
      _ = 25 / L n ^ 2 := by ring
  have htailRow :
      (h : ℝ) / (r : ℝ) ≤ 2 * c * (x + 1) / L n := by
    simpa only [h, x] using
      roughTail_div_row_cast_le hr hc.le hLPos htail
  have hKh' : K * h ≤ n := by
    simpa only [K, h] using hKh
  have hh : h ≤ n :=
    (Nat.le_mul_of_pos_left h hK).trans hKh'
  have hhalfMinus :
      n / r ≤ (2 * n - K * h) / r := by
    apply Nat.div_le_div_right
    omega
  have hminusX :
      (2 * n - K * h) / r ≤ (2 * n) / r :=
    Nat.div_le_div_right (Nat.sub_le _ _)
  have hxPlus :
      (2 * n) / r ≤ (2 * n + h) / r :=
    Nat.div_le_div_right (by omega)
  have hXthree :
      (2 * n) / r ≤ 3 * (n / r) :=
    roughTwoQuotient_le_three_halfQuotient hr hrn
  have hPlusThree :
      (2 * n + h) / r ≤ 3 * ((2 * n) / r) :=
    roughUpperQuotient_le_three_centralQuotient hr hrn hh
  have hgapUpper :
      ((((2 * n + h) / r - (2 * n) / r : ℕ) : ℝ)) ≤
        2 * c * (x + 1) / L n + 1 := by
    have hq := roughQuotientGap_cast_le
      (r := r) hr (show 2 * n ≤ 2 * n + h by omega)
    rw [show 2 * n + h - 2 * n = h by omega] at hq
    exact hq.trans (add_le_add htailRow le_rfl)
  have hgapLower :
      ((((2 * n) / r -
          (2 * n - K * h) / r : ℕ) : ℝ)) ≤
        2 * (K : ℝ) * c * (x + 1) / L n + 1 := by
    have hq := roughQuotientGap_cast_le
      (r := r) hr (show 2 * n - K * h ≤ 2 * n by omega)
    rw [show 2 * n - (2 * n - K * h) = K * h by omega,
      Nat.cast_mul] at hq
    calc
      ((((2 * n) / r -
          (2 * n - K * h) / r : ℕ) : ℝ)) ≤
          ((K : ℝ) * (h : ℝ)) / (r : ℝ) + 1 := hq
      _ = (K : ℝ) * ((h : ℝ) / (r : ℝ)) + 1 := by ring
      _ ≤ (K : ℝ) * (2 * c * (x + 1) / L n) + 1 :=
        add_le_add
          (mul_le_mul_of_nonneg_left htailRow hKReal.le) le_rfl
      _ = 2 * (K : ℝ) * c * (x + 1) / L n + 1 := by ring
  have hgapBroad :
      ((((2 * n - K * h) / r - n / r : ℕ) : ℝ)) ≤
        2 * x := by
    rw [Nat.cast_sub hhalfMinus]
    have hminusThree :
        ((2 * n - K * h) / r : ℕ) ≤ 3 * (n / r) :=
      hminusX.trans hXthree
    dsimp only [x]
    exact_mod_cast (show
      (2 * n - K * h) / r - n / r ≤ 2 * (n / r) by omega)
  have hupperEndpoints :
      (((2 * n) / r : ℕ) : ℝ) +
          (((2 * n + h) / r : ℕ) : ℝ) ≤ 12 * x := by
    dsimp only [x]
    exact_mod_cast (show
      (2 * n) / r + (2 * n + h) / r ≤
        12 * (n / r) by omega)
  have hlowerEndpoints :
      (((2 * n - K * h) / r : ℕ) : ℝ) +
          (((2 * n) / r : ℕ) : ℝ) ≤ 6 * x := by
    dsimp only [x]
    exact_mod_cast (show
      (2 * n - K * h) / r + (2 * n) / r ≤
        6 * (n / r) by omega)
  have hbroadEndpoints :
      (((n / r : ℕ) : ℝ)) +
          (((2 * n - K * h) / r : ℕ) : ℝ) ≤ 4 * x := by
    dsimp only [x]
    exact_mod_cast (show
      n / r + (2 * n - K * h) / r ≤
        4 * (n / r) by omega)
  have halpha :
      |alpha| ≤ roughBalancedAlphaConstant W K0 c beta := by
    dsimp only [alpha, h, K, roughBalancedAlphaConstant]
    exact roughHeadBalancedAlpha_succ_abs_le W K0 hc hn
  have hdeltaAlpha :
      |roughHeadDensity W * alpha| ≤
        roughBalancedAlphaConstant W K0 c beta := by
    rw [abs_mul, abs_of_nonneg hdelta0]
    exact (mul_le_mul_of_nonneg_right hdelta1
      (abs_nonneg alpha)).trans (by simpa using halpha)
  have hdeltaBeta :
      |roughHeadDensity W * (beta / L n)| ≤ |beta| / L n := by
    rw [abs_mul, abs_of_nonneg hdelta0, abs_div,
      abs_of_pos hLPos]
    simpa only [one_mul] using
      mul_le_mul_of_nonneg_right hdelta1
        (div_nonneg (abs_nonneg beta) hLPos.le)
  have heta :
      roughSaiasInvLogSqEndpointRate C y =
        10 * C / Real.log (y : ℝ) ^ 2 := rfl
  have hupperEta :
      roughSaiasInvLogSqEndpointRate C y *
          ((((2 * n) / r : ℕ) : ℝ) +
            (((2 * n + h) / r : ℕ) : ℝ)) ≤
        3000 * C * (x / L n ^ 2) := by
    rw [heta]
    calc
      (10 * C / Real.log (y : ℝ) ^ 2) *
          ((((2 * n) / r : ℕ) : ℝ) +
            (((2 * n + h) / r : ℕ) : ℝ)) ≤
        (10 * C / Real.log (y : ℝ) ^ 2) * (12 * x) :=
          mul_le_mul_of_nonneg_left hupperEndpoints (by positivity)
      _ = 120 * C * x *
          (1 / Real.log (y : ℝ) ^ 2) := by ring
      _ ≤ 120 * C * x * (25 / L n ^ 2) := by
        exact mul_le_mul_of_nonneg_left hinvLogSq
          (mul_nonneg
            (mul_nonneg (by norm_num) hC) hx.le)
      _ = 3000 * C * (x / L n ^ 2) := by ring
  have hupperGap :
      5 * ((((2 * n + h) / r -
          (2 * n) / r : ℕ) : ℝ)) /
        Real.log (y : ℝ) ≤
      (50 * c + 25) * S := by
    calc
      5 * ((((2 * n + h) / r -
          (2 * n) / r : ℕ) : ℝ)) /
          Real.log (y : ℝ) =
        (5 * ((((2 * n + h) / r -
          (2 * n) / r : ℕ) : ℝ))) *
          (1 / Real.log (y : ℝ)) := by ring
      _ ≤ (5 * (2 * c * (x + 1) / L n + 1)) *
          (5 / L n) := by
        exact mul_le_mul
          (mul_le_mul_of_nonneg_left hgapUpper (by norm_num))
          hinvLog (by positivity) (by positivity)
      _ = 50 * c * ((x + 1) / L n ^ 2) +
          25 * (1 / L n) := by ring
      _ ≤ 50 * c * S + 25 * S :=
        add_le_add
          (mul_le_mul_of_nonneg_left hSplus
            (mul_nonneg (by norm_num) hc.le))
          (mul_le_mul_of_nonneg_left hSinv (by norm_num))
      _ = (50 * c + 25) * S := by ring
  have hupperPair :
      roughSaiasPairTransitionBudget
          (roughSaiasInvLogSqEndpointRate C)
          ((2 * n) / r) ((2 * n + h) / r) y ≤
        (3000 * C + 50 * c + 25) * S := by
    unfold roughSaiasPairTransitionBudget
    calc
      _ ≤ 3000 * C * (x / L n ^ 2) +
          (50 * c + 25) * S :=
        add_le_add hupperEta hupperGap
      _ ≤ 3000 * C * S + (50 * c + 25) * S :=
        add_le_add
          (mul_le_mul_of_nonneg_left hxScale
            (mul_nonneg (by norm_num : (0 : ℝ) ≤ 3000) hC)) le_rfl
      _ = (3000 * C + 50 * c + 25) * S := by ring
  have hlowerEta :
      roughSaiasInvLogSqEndpointRate C y *
          ((((2 * n - K * h) / r : ℕ) : ℝ) +
            (((2 * n) / r : ℕ) : ℝ)) ≤
        1500 * C * (x / L n ^ 2) := by
    rw [heta]
    calc
      (10 * C / Real.log (y : ℝ) ^ 2) *
          ((((2 * n - K * h) / r : ℕ) : ℝ) +
            (((2 * n) / r : ℕ) : ℝ)) ≤
        (10 * C / Real.log (y : ℝ) ^ 2) * (6 * x) :=
          mul_le_mul_of_nonneg_left hlowerEndpoints (by positivity)
      _ = 60 * C * x *
          (1 / Real.log (y : ℝ) ^ 2) := by ring
      _ ≤ 60 * C * x * (25 / L n ^ 2) := by
        exact mul_le_mul_of_nonneg_left hinvLogSq
          (mul_nonneg
            (mul_nonneg (by norm_num) hC) hx.le)
      _ = 1500 * C * (x / L n ^ 2) := by ring
  have hlowerGap :
      5 * ((((2 * n) / r -
          (2 * n - K * h) / r : ℕ) : ℝ)) /
        Real.log (y : ℝ) ≤
      (50 * (K : ℝ) * c + 25) * S := by
    calc
      5 * ((((2 * n) / r -
          (2 * n - K * h) / r : ℕ) : ℝ)) /
          Real.log (y : ℝ) =
        (5 * ((((2 * n) / r -
          (2 * n - K * h) / r : ℕ) : ℝ))) *
          (1 / Real.log (y : ℝ)) := by ring
      _ ≤
          (5 * (2 * (K : ℝ) * c * (x + 1) / L n + 1)) *
            (5 / L n) := by
        exact mul_le_mul
          (mul_le_mul_of_nonneg_left hgapLower (by norm_num))
          hinvLog (by positivity) (by positivity)
      _ = 50 * (K : ℝ) * c *
          ((x + 1) / L n ^ 2) + 25 * (1 / L n) := by ring
      _ ≤ 50 * (K : ℝ) * c * S + 25 * S :=
        add_le_add
          (mul_le_mul_of_nonneg_left hSplus
            (mul_nonneg
              (mul_nonneg (by norm_num) hKReal.le) hc.le))
          (mul_le_mul_of_nonneg_left hSinv (by norm_num))
      _ = (50 * (K : ℝ) * c + 25) * S := by ring
  have hlowerPair :
      roughSaiasPairTransitionBudget
          (roughSaiasInvLogSqEndpointRate C)
          ((2 * n - K * h) / r) ((2 * n) / r) y ≤
        (1500 * C + 50 * (K : ℝ) * c + 25) * S := by
    unfold roughSaiasPairTransitionBudget
    calc
      _ ≤ 1500 * C * (x / L n ^ 2) +
          (50 * (K : ℝ) * c + 25) * S :=
        add_le_add hlowerEta hlowerGap
      _ ≤ 1500 * C * S +
          (50 * (K : ℝ) * c + 25) * S :=
        add_le_add
          (mul_le_mul_of_nonneg_left hxScale
            (mul_nonneg (by norm_num : (0 : ℝ) ≤ 1500) hC)) le_rfl
      _ = (1500 * C + 50 * (K : ℝ) * c + 25) * S := by ring
  have hbroadEta :
      roughSaiasInvLogSqEndpointRate C y *
          ((((n / r : ℕ) : ℝ)) +
            (((2 * n - K * h) / r : ℕ) : ℝ)) ≤
        1000 * C * (x / L n ^ 2) := by
    rw [heta]
    calc
      (10 * C / Real.log (y : ℝ) ^ 2) *
          ((((n / r : ℕ) : ℝ)) +
            (((2 * n - K * h) / r : ℕ) : ℝ)) ≤
        (10 * C / Real.log (y : ℝ) ^ 2) * (4 * x) :=
          mul_le_mul_of_nonneg_left hbroadEndpoints (by positivity)
      _ = 40 * C * x *
          (1 / Real.log (y : ℝ) ^ 2) := by ring
      _ ≤ 40 * C * x * (25 / L n ^ 2) := by
        exact mul_le_mul_of_nonneg_left hinvLogSq
          (mul_nonneg
            (mul_nonneg (by norm_num) hC) hx.le)
      _ = 1000 * C * (x / L n ^ 2) := by ring
  have hbroadGap :
      5 * ((((2 * n - K * h) / r -
          n / r : ℕ) : ℝ)) / Real.log (y : ℝ) ≤
        50 * (x / L n) := by
    calc
      5 * ((((2 * n - K * h) / r -
          n / r : ℕ) : ℝ)) / Real.log (y : ℝ) =
        (5 * ((((2 * n - K * h) / r -
          n / r : ℕ) : ℝ))) *
          (1 / Real.log (y : ℝ)) := by ring
      _ ≤ (5 * (2 * x)) * (5 / L n) := by
        exact mul_le_mul
          (mul_le_mul_of_nonneg_left hgapBroad (by norm_num))
          hinvLog (by positivity) (by positivity)
      _ = 50 * (x / L n) := by ring
  have hbroadWeighted :
      |roughHeadDensity W * (beta / L n)| *
          roughSaiasPairTransitionBudget
            (roughSaiasInvLogSqEndpointRate C)
            (n / r) ((2 * n - K * h) / r) y ≤
        |beta| * (1000 * C + 75) * S := by
    unfold roughSaiasPairTransitionBudget
    calc
      |roughHeadDensity W * (beta / L n)| *
          (roughSaiasInvLogSqEndpointRate C y *
              ((((n / r : ℕ) : ℝ)) +
                (((2 * n - K * h) / r : ℕ) : ℝ)) +
            5 * ((((2 * n - K * h) / r -
                n / r : ℕ) : ℝ)) /
              Real.log (y : ℝ)) ≤
        (|beta| / L n) *
          (1000 * C * (x / L n ^ 2) +
            50 * (x / L n)) := by
        have hbudgetNonneg :
            0 ≤ 1000 * C * (x / L n ^ 2) +
                50 * (x / L n) :=
          add_nonneg
            (mul_nonneg
              (mul_nonneg (by norm_num : (0 : ℝ) ≤ 1000) hC)
              (div_nonneg hx.le (sq_nonneg (L n))))
            (mul_nonneg (by norm_num : (0 : ℝ) ≤ 50)
              (div_nonneg hx.le hLPos.le))
        exact
          (mul_le_mul_of_nonneg_left
              (add_le_add hbroadEta hbroadGap) (abs_nonneg _)).trans
            (mul_le_mul_of_nonneg_right hdeltaBeta hbudgetNonneg)
      _ = |beta| *
          (1000 * C * (x / L n ^ 2) * (1 / L n) +
            50 * (x / L n ^ 2)) := by ring
      _ ≤ |beta| *
          (1000 * C * (x / L n ^ 2) +
            50 * (x / L n ^ 2)) := by
        apply mul_le_mul_of_nonneg_left
        · have hmul :
              1000 * C * (x / L n ^ 2) * (1 / L n) ≤
                1000 * C * (x / L n ^ 2) := by
            have hraw :=
              mul_le_mul_of_nonneg_left hinvL
                (mul_nonneg
                  (mul_nonneg (by norm_num : (0 : ℝ) ≤ 1000) hC)
                  (div_nonneg hx.le (sq_nonneg (L n))))
            simpa only [mul_one] using hraw
          exact add_le_add hmul le_rfl
        · exact abs_nonneg beta
      _ ≤ |beta| * ((1000 * C + 50) * S) := by
        rw [show
          1000 * C * (x / L n ^ 2) +
              50 * (x / L n ^ 2) =
            (1000 * C + 50) * (x / L n ^ 2) by ring]
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hxScale
            (add_nonneg
              (mul_nonneg (by norm_num) hC) (by norm_num)))
          (abs_nonneg beta)
      _ ≤ |beta| * ((1000 * C + 75) * S) := by
        apply mul_le_mul_of_nonneg_left
        · exact mul_le_mul_of_nonneg_right
            (by norm_num : (1000 * C + 50) ≤ 1000 * C + 75)
            hSnonneg
        · exact abs_nonneg beta
      _ = |beta| * (1000 * C + 75) * S := by ring
  unfold roughPhysicalSaiasTransitionBudget
  calc
    roughSaiasPairTransitionBudget
          (roughSaiasInvLogSqEndpointRate C)
          ((2 * n) / r) ((2 * n + h) / r) y +
        |roughHeadDensity W * alpha| *
          roughSaiasPairTransitionBudget
            (roughSaiasInvLogSqEndpointRate C)
            ((2 * n - K * h) / r) ((2 * n) / r) y +
        |roughHeadDensity W * (beta / L n)| *
          roughSaiasPairTransitionBudget
            (roughSaiasInvLogSqEndpointRate C)
            (n / r) ((2 * n - K * h) / r) y ≤
      (3000 * C + 50 * c + 25) * S +
        roughBalancedAlphaConstant W K0 c beta *
          (1500 * C + 50 * (K : ℝ) * c + 25) * S +
        |beta| * (1000 * C + 75) * S := by
      have hlowerBoundNonneg :
          0 ≤ (1500 * C + 50 * (K : ℝ) * c + 25) * S :=
        mul_nonneg
          (add_nonneg
            (add_nonneg
              (mul_nonneg (by norm_num : (0 : ℝ) ≤ 1500) hC)
              (mul_nonneg
                (mul_nonneg (by norm_num : (0 : ℝ) ≤ 50)
                  hKReal.le)
                hc.le))
            (by norm_num))
          hSnonneg
      exact add_le_add
        (add_le_add hupperPair
          (by
            simpa only [mul_assoc] using
              ((mul_le_mul_of_nonneg_left hlowerPair (abs_nonneg _)).trans
                (mul_le_mul_of_nonneg_right hdeltaAlpha
                  hlowerBoundNonneg))))
        hbroadWeighted
    _ = roughCanonicalSharpTransitionRowScaleConstant
          W K0 c beta * S := by
      unfold roughCanonicalSharpTransitionRowScaleConstant
      dsimp only [K, C]
      ring

/-! ## Absorption of the sharp fixed-head divisor sum -/



/-! ## One unified canonical raw-row allowance -/













end

end Erdos390.WholePaper

end

theorem solution : Erdos390.RemainingAnalyticGoal008_015 := by
  exact @Erdos390.WholePaper.roughCanonicalBalancedSaiasTransitionBudget_le
