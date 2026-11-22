-- Prove2me | solution 1 for Erdos390.WholePaper.roughCanonicalBalancedSharpFixedHeadBudget_le_compact
-- status  : ACCEPTED   (prove)
-- author  : @doctosil
-- created : 2026-09-17T17:42:05.549974+00:00
-- url     : https://prove2.me/submissions/a474fc47-2add-460c-a191-eb532946f416

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

/- Source module: Erdos390.WholePaper.CanonicalCompleteRoughRows -/
section


/-!
# Canonical complete rough rows for exactification

A finite candidate set itself supplies the coordinate type used by floating
rounding.  Its attained complete rough labels supply a canonical finite row
type.  The row signature is simply factorization of the label; positivity
of attained labels and uniqueness of factorization make this signature map
injective.

This file also identifies `rowSet` with the literal complete-rough fiber and
provides the value, interval, summation, and row-integrality bridges required
by the exactification interface.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

noncomputable section

/-! ## Canonical finite types and maps -/



















/-! ## Signature and value interfaces -/

/-- An attained complete rough label is positive. -/
theorem canonicalCompleteRoughRow_label_pos
    (y : ℕ) (A : Finset ℕ)
    (row : CanonicalCompleteRoughRow y A) :
    0 < row.1 := by
  obtain ⟨a, _ha, hlabel⟩ :=
    mem_completeRoughLabelSet.mp row.property
  rw [← hlabel, completeRoughLabel]
  apply Nat.prod_pow_pos_of_zero_notMem_support
  rw [Finsupp.notMem_support_iff, completeRoughSignature_apply]
  simp









/-! ## Literal subtype fibers and `rowSet` -/











/-! ## Summation and integrality bridges -/











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



theorem roughBalancedAlphaConstant_nonneg
    (W K0 : ℕ) {c beta : ℝ} (hc : 0 < c) :
    0 ≤ roughBalancedAlphaConstant W K0 c beta := by
  unfold roughBalancedAlphaConstant
  have hK : (0 : ℝ) <
      (((K0 + 1 : ℕ) : ℝ)) := by positivity
  have hdelta : 0 < roughHeadDensity W :=
    roughHeadDensity_pos W
  positivity











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



/-! ## Absorption of the sharp fixed-head divisor sum -/

set_option maxHeartbeats 4000000 in
/-- The all-row sharp fixed-head budget is bounded by the fixed divisor
constant at the same canonical row scale. -/
theorem roughCanonicalBalancedSharpFixedHeadBudget_le
    (W K0 : ℕ) {c beta : ℝ} (hc : 0 < c)
    {n y : ℕ} (hn : 2 ≤ n) (_hy : 2 ≤ y)
    (row : CanonicalCompleteRoughRow y
      (roughRawCandidateSet n (upperTailLength c n) (K0 + 1)))
    (hrowN : row.1 ≤ n)
    (hLone : 1 ≤ L n)
    (hlogY : L n / 5 ≤ Real.log (y : ℝ))
    (htail :
      (upperTailLength c n : ℝ) ≤
        2 * c * (n : ℝ) / L n)
    (hKh :
      (K0 + 1) * upperTailLength c n ≤ n) :
    roughCanonicalSharpFixedHeadShiftBudgetAllRows
        W n (upperTailLength c n) (K0 + 1) y
        (roughHeadBalancedAlpha W n (upperTailLength c n)
          (K0 + 1) beta (L n))
        beta (L n) row ≤
      roughCanonicalSharpHeadRowScaleConstant W K0 c beta *
        (((n / row.1 : ℕ) : ℝ) / L n ^ 2 + 1) := by
  let K : ℕ := K0 + 1
  let h : ℕ := upperTailLength c n
  let alpha : ℝ :=
    roughHeadBalancedAlpha W n h K beta (L n)
  let x : ℝ := ((n / row.1 : ℕ) : ℝ)
  let S : ℝ := x / L n ^ 2 + 1
  let C : ℝ := roughSaiasSharpDefectConstant
  have hr : 0 < row.1 :=
    canonicalCompleteRoughRow_label_pos y
      (roughRawCandidateSet n (upperTailLength c n) (K0 + 1)) row
  have hK : 0 < K := by simp [K]
  have hKReal : (0 : ℝ) < (K : ℝ) := by exact_mod_cast hK
  have hLPos : 0 < L n := zero_lt_one.trans_le hLone
  have hlogPos : 0 < Real.log (y : ℝ) := by
    have : 0 < L n / 5 := by positivity
    exact this.trans_le hlogY
  have hC : 0 ≤ C := by
    dsimp only [C]
    unfold roughSaiasSharpDefectConstant
    have htheta : 0 ≤ roughSaiasThetaFourthPowerConstant :=
      roughSaiasThetaFourthPowerConstant_pos.le
    positivity
  have hxNat : 0 < n / row.1 := Nat.div_pos hrowN hr
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
      (h : ℝ) / (row.1 : ℝ) ≤
        2 * c * (x + 1) / L n := by
    simpa only [h, x] using
      roughTail_div_row_cast_le hr hc.le hLPos htail
  have hKh' : K * h ≤ n := by
    simpa only [K, h] using hKh
  have hhalfMinus :
      n / row.1 ≤ (2 * n - K * h) / row.1 := by
    apply Nat.div_le_div_right
    omega
  have hminusX :
      (2 * n - K * h) / row.1 ≤ (2 * n) / row.1 :=
    Nat.div_le_div_right (Nat.sub_le _ _)
  have hXthree :
      (2 * n) / row.1 ≤ 3 * (n / row.1) :=
    roughTwoQuotient_le_three_halfQuotient hr hrowN
  have hgapHigh :
      ((((2 * n) / row.1 -
          (2 * n - K * h) / row.1 : ℕ) : ℝ)) ≤
        2 * (K : ℝ) * c * (x + 1) / L n + 1 := by
    have hq := roughQuotientGap_cast_le
      (r := row.1) hr
      (show 2 * n - K * h ≤ 2 * n by omega)
    rw [show 2 * n - (2 * n - K * h) = K * h by omega,
      Nat.cast_mul] at hq
    calc
      ((((2 * n) / row.1 -
          (2 * n - K * h) / row.1 : ℕ) : ℝ)) ≤
          ((K : ℝ) * (h : ℝ)) / (row.1 : ℝ) + 1 := hq
      _ = (K : ℝ) * ((h : ℝ) / (row.1 : ℝ)) + 1 := by ring
      _ ≤ (K : ℝ) * (2 * c * (x + 1) / L n) + 1 :=
        add_le_add
          (mul_le_mul_of_nonneg_left htailRow hKReal.le) le_rfl
      _ = 2 * (K : ℝ) * c * (x + 1) / L n + 1 := by ring
  have hgapBroad :
      ((((2 * n - K * h) / row.1 -
          n / row.1 : ℕ) : ℝ)) ≤ 2 * x := by
    rw [Nat.cast_sub hhalfMinus]
    have hminusThree :
        ((2 * n - K * h) / row.1 : ℕ) ≤
          3 * (n / row.1) :=
      hminusX.trans hXthree
    dsimp only [x]
    exact_mod_cast (show
      (2 * n - K * h) / row.1 - n / row.1 ≤
        2 * (n / row.1) by omega)
  have hhighEndpoints :
      (((2 * n - K * h) / row.1 : ℕ) : ℝ) +
          (((2 * n) / row.1 : ℕ) : ℝ) ≤ 6 * x := by
    dsimp only [x]
    exact_mod_cast (show
      (2 * n - K * h) / row.1 + (2 * n) / row.1 ≤
        6 * (n / row.1) by omega)
  have hbroadEndpoints :
      (((n / row.1 : ℕ) : ℝ)) +
          (((2 * n - K * h) / row.1 : ℕ) : ℝ) ≤ 4 * x := by
    dsimp only [x]
    exact_mod_cast (show
      n / row.1 + (2 * n - K * h) / row.1 ≤
        4 * (n / row.1) by omega)
  have halpha :
      |alpha| ≤ roughBalancedAlphaConstant W K0 c beta := by
    dsimp only [alpha, h, K, roughBalancedAlphaConstant]
    exact roughHeadBalancedAlpha_succ_abs_le W K0 hc hn
  unfold roughCanonicalSharpFixedHeadShiftBudgetAllRows
    roughCanonicalSharpHeadRowScaleConstant
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro d hdMem
  have hd : 0 < d := Nat.pos_of_mem_divisors hdMem
  have hdReal : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hlogd : 0 ≤ Real.log (d : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hd)
  let G : ℝ := (Real.log (d : ℝ) + 12) / (d : ℝ)
  have hG : 0 ≤ G := by
    dsimp only [G]
    positivity
  let Hhigh : ℝ :=
    31 + G * (10 * (K : ℝ) * c + 5) +
      3000 * C / (d : ℝ)
  let Hbroad : ℝ :=
    31 + 10 * G + 2000 * C / (d : ℝ)
  have hHhigh : 0 ≤ Hhigh := by
    dsimp only [Hhigh]
    positivity
  have hHbroad : 0 ≤ Hbroad := by
    dsimp only [Hbroad]
    positivity
  have hhighBudget :
      roughSaiasSharpIntervalFixedDivisorBudget
          ((2 * n - K * h) / row.1)
          ((2 * n) / row.1) y d ≤
        Hhigh * S := by
    unfold roughSaiasSharpIntervalFixedDivisorBudget
    have hconst :
        6 + 5 / Real.log (y : ℝ) ≤ 31 * S := by
      calc
        6 + 5 / Real.log (y : ℝ) =
            6 + 5 * (1 / Real.log (y : ℝ)) := by ring
        _ ≤ 6 + 5 * (5 / L n) :=
          add_le_add_right
            (mul_le_mul_of_nonneg_left hinvLog
              (by norm_num : (0 : ℝ) ≤ 5)) 6
        _ = 6 + 25 * (1 / L n) := by ring
        _ ≤ 6 * S + 25 * S :=
          add_le_add
            (by
              simpa only [mul_one] using
                mul_le_mul_of_nonneg_left hSone
                  (by norm_num : (0 : ℝ) ≤ 6))
            (mul_le_mul_of_nonneg_left hSinv
              (by norm_num : (0 : ℝ) ≤ 25))
        _ = 31 * S := by ring
    have hgapTerm :
        ((((2 * n) / row.1 -
            (2 * n - K * h) / row.1 : ℕ) : ℝ)) *
            (Real.log (d : ℝ) + 12) /
              ((d : ℝ) * Real.log (y : ℝ)) ≤
          (G * (10 * (K : ℝ) * c + 5)) * S := by
      calc
        ((((2 * n) / row.1 -
            (2 * n - K * h) / row.1 : ℕ) : ℝ)) *
            (Real.log (d : ℝ) + 12) /
              ((d : ℝ) * Real.log (y : ℝ)) =
          ((((2 * n) / row.1 -
              (2 * n - K * h) / row.1 : ℕ) : ℝ)) *
            G * (1 / Real.log (y : ℝ)) := by
              dsimp only [G]
              ring
        _ ≤ (2 * (K : ℝ) * c * (x + 1) / L n + 1) *
            G * (5 / L n) := by
          exact mul_le_mul
            (mul_le_mul_of_nonneg_right hgapHigh hG)
            hinvLog (by positivity) (by positivity)
        _ = G *
            (10 * (K : ℝ) * c *
                ((x + 1) / L n ^ 2) +
              5 * (1 / L n)) := by ring
        _ ≤ G * (10 * (K : ℝ) * c * S + 5 * S) := by
          apply mul_le_mul_of_nonneg_left
          · exact add_le_add
              (mul_le_mul_of_nonneg_left hSplus
                (mul_nonneg
                  (mul_nonneg (by norm_num) hKReal.le) hc.le))
              (mul_le_mul_of_nonneg_left hSinv (by norm_num))
          · exact hG
        _ = (G * (10 * (K : ℝ) * c + 5)) * S := by ring
    have hendpointTerm :
        20 * C *
            ((((2 * n - K * h) / row.1 : ℕ) : ℝ) +
              (((2 * n) / row.1 : ℕ) : ℝ)) /
              ((d : ℝ) * Real.log (y : ℝ) ^ 2) ≤
          (3000 * C / (d : ℝ)) * S := by
      calc
        20 * C *
            ((((2 * n - K * h) / row.1 : ℕ) : ℝ) +
              (((2 * n) / row.1 : ℕ) : ℝ)) /
              ((d : ℝ) * Real.log (y : ℝ) ^ 2) ≤
          20 * C * (6 * x) /
              ((d : ℝ) * Real.log (y : ℝ) ^ 2) := by
            exact div_le_div_of_nonneg_right
              (mul_le_mul_of_nonneg_left hhighEndpoints
                (mul_nonneg (by norm_num) hC))
              (mul_nonneg hdReal.le (sq_nonneg _))
        _ = (120 * C * x / (d : ℝ)) *
            (1 / Real.log (y : ℝ) ^ 2) := by ring
        _ ≤ (120 * C * x / (d : ℝ)) *
            (25 / L n ^ 2) := by
          exact mul_le_mul_of_nonneg_left hinvLogSq (by positivity)
        _ = (3000 * C / (d : ℝ)) *
            (x / L n ^ 2) := by ring
        _ ≤ (3000 * C / (d : ℝ)) * S :=
          mul_le_mul_of_nonneg_left hxScale (by positivity)
    calc
      6 + 5 / Real.log (y : ℝ) +
          ((((2 * n) / row.1 -
              (2 * n - K * h) / row.1 : ℕ) : ℝ)) *
            (Real.log (d : ℝ) + 12) /
              ((d : ℝ) * Real.log (y : ℝ)) +
          20 * C *
            ((((2 * n - K * h) / row.1 : ℕ) : ℝ) +
              (((2 * n) / row.1 : ℕ) : ℝ)) /
              ((d : ℝ) * Real.log (y : ℝ) ^ 2) ≤
        31 * S +
          (G * (10 * (K : ℝ) * c + 5)) * S +
          (3000 * C / (d : ℝ)) * S :=
        add_le_add (add_le_add hconst hgapTerm) hendpointTerm
      _ = Hhigh * S := by
        dsimp only [Hhigh]
        ring
  have hhighWeighted :
      |alpha| *
          roughSaiasSharpIntervalFixedDivisorBudget
            ((2 * n - K * h) / row.1)
            ((2 * n) / row.1) y d ≤
        roughBalancedAlphaConstant W K0 c beta *
          Hhigh * S := by
    have hbudget0 : 0 ≤
        roughSaiasSharpIntervalFixedDivisorBudget
          ((2 * n - K * h) / row.1)
          ((2 * n) / row.1) y d := by
      unfold roughSaiasSharpIntervalFixedDivisorBudget
      positivity
    calc
      |alpha| * roughSaiasSharpIntervalFixedDivisorBudget
          ((2 * n - K * h) / row.1)
          ((2 * n) / row.1) y d ≤
        roughBalancedAlphaConstant W K0 c beta *
          roughSaiasSharpIntervalFixedDivisorBudget
            ((2 * n - K * h) / row.1)
            ((2 * n) / row.1) y d :=
          mul_le_mul_of_nonneg_right halpha hbudget0
      _ ≤ roughBalancedAlphaConstant W K0 c beta *
          (Hhigh * S) :=
        mul_le_mul_of_nonneg_left hhighBudget
          (roughBalancedAlphaConstant_nonneg
            W K0 (beta := beta) hc)
      _ = roughBalancedAlphaConstant W K0 c beta *
          Hhigh * S := by ring
  have hbroadWeighted :
      |beta / L n| *
          roughSaiasSharpIntervalFixedDivisorBudget
            (n / row.1) ((2 * n - K * h) / row.1) y d ≤
        |beta| * Hbroad * S := by
    unfold roughSaiasSharpIntervalFixedDivisorBudget
    rw [abs_div, abs_of_pos hLPos]
    have hconst :
        (|beta| / L n) *
            (6 + 5 / Real.log (y : ℝ)) ≤
          |beta| * 31 * S := by
      calc
        (|beta| / L n) *
            (6 + 5 / Real.log (y : ℝ)) =
          |beta| *
            (6 * (1 / L n) +
              5 * (1 / L n) *
                (1 / Real.log (y : ℝ))) := by ring
        _ ≤ |beta| *
            (6 * (1 / L n) +
              5 * (1 / L n) * (5 / L n)) := by
          apply mul_le_mul_of_nonneg_left
          · exact add_le_add_right
              (mul_le_mul_of_nonneg_left hinvLog
                (mul_nonneg
                  (by norm_num : (0 : ℝ) ≤ 5)
                  (div_nonneg
                    (by norm_num : (0 : ℝ) ≤ 1) hLPos.le)))
              (6 * (1 / L n))
          · exact abs_nonneg beta
        _ = |beta| *
            (6 * (1 / L n) + 25 * (1 / L n ^ 2)) := by ring
        _ ≤ |beta| * (6 * S + 25 * S) := by
          apply mul_le_mul_of_nonneg_left
          · exact add_le_add
              (mul_le_mul_of_nonneg_left hSinv (by norm_num))
              (mul_le_mul_of_nonneg_left hinvLSq (by norm_num))
          · exact abs_nonneg beta
        _ = |beta| * 31 * S := by ring
    have hgapTerm :
        (|beta| / L n) *
          (((((2 * n - K * h) / row.1 -
              n / row.1 : ℕ) : ℝ)) *
            (Real.log (d : ℝ) + 12) /
              ((d : ℝ) * Real.log (y : ℝ))) ≤
          |beta| * (10 * G) * S := by
      calc
        (|beta| / L n) *
          (((((2 * n - K * h) / row.1 -
              n / row.1 : ℕ) : ℝ)) *
            (Real.log (d : ℝ) + 12) /
              ((d : ℝ) * Real.log (y : ℝ))) =
          |beta| * ((((2 * n - K * h) / row.1 -
              n / row.1 : ℕ) : ℝ)) * G *
            (1 / Real.log (y : ℝ)) * (1 / L n) := by
              dsimp only [G]
              ring
        _ ≤ |beta| * (2 * x) * G *
            (5 / L n) * (1 / L n) := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul
              (mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_left hgapBroad
                  (abs_nonneg beta)) hG)
              hinvLog
              (div_nonneg
                (by norm_num : (0 : ℝ) ≤ 1) hlogPos.le)
              (mul_nonneg
                (mul_nonneg (abs_nonneg beta)
                  (mul_nonneg
                    (by norm_num : (0 : ℝ) ≤ 2) hx.le)) hG))
            (div_nonneg
              (by norm_num : (0 : ℝ) ≤ 1) hLPos.le)
        _ = |beta| * (10 * G) * (x / L n ^ 2) := by ring
        _ ≤ |beta| * (10 * G) * S :=
          mul_le_mul_of_nonneg_left hxScale
            (mul_nonneg (abs_nonneg beta)
              (mul_nonneg
                (by norm_num : (0 : ℝ) ≤ 10) hG))
    have hendpointTerm :
        (|beta| / L n) *
          (20 * C *
            ((((n / row.1 : ℕ) : ℝ)) +
              (((2 * n - K * h) / row.1 : ℕ) : ℝ)) /
              ((d : ℝ) * Real.log (y : ℝ) ^ 2)) ≤
          |beta| * (2000 * C / (d : ℝ)) * S := by
      calc
        (|beta| / L n) *
          (20 * C *
            ((((n / row.1 : ℕ) : ℝ)) +
              (((2 * n - K * h) / row.1 : ℕ) : ℝ)) /
              ((d : ℝ) * Real.log (y : ℝ) ^ 2)) ≤
          (|beta| / L n) *
            (20 * C * (4 * x) /
              ((d : ℝ) * Real.log (y : ℝ) ^ 2)) := by
            exact mul_le_mul_of_nonneg_left
              (div_le_div_of_nonneg_right
                (mul_le_mul_of_nonneg_left hbroadEndpoints
                  (mul_nonneg (by norm_num) hC))
                (mul_nonneg hdReal.le (sq_nonneg _)))
              (div_nonneg (abs_nonneg beta) hLPos.le)
        _ = |beta| * (80 * C * x / (d : ℝ)) *
            (1 / Real.log (y : ℝ) ^ 2) *
            (1 / L n) := by ring
        _ ≤ |beta| * (80 * C * x / (d : ℝ)) *
            (25 / L n ^ 2) * (1 / L n) := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hinvLogSq (by positivity))
            (div_nonneg (by norm_num) hLPos.le)
        _ = |beta| * (2000 * C / (d : ℝ)) *
            (x / L n ^ 2) * (1 / L n) := by ring
        _ ≤ |beta| * (2000 * C / (d : ℝ)) *
            (x / L n ^ 2) := by
          have hmul :=
            mul_le_mul_of_nonneg_left hinvL
              (show 0 ≤ |beta| * (2000 * C / (d : ℝ)) *
                (x / L n ^ 2) by positivity)
          simpa only [mul_one] using hmul
        _ ≤ |beta| * (2000 * C / (d : ℝ)) * S :=
          mul_le_mul_of_nonneg_left hxScale (by positivity)
    calc
      (|beta| / L n) *
          (6 + 5 / Real.log (y : ℝ) +
            ((((2 * n - K * h) / row.1 -
                n / row.1 : ℕ) : ℝ)) *
              (Real.log (d : ℝ) + 12) /
                ((d : ℝ) * Real.log (y : ℝ)) +
            20 * C *
              ((((n / row.1 : ℕ) : ℝ)) +
                (((2 * n - K * h) / row.1 : ℕ) : ℝ)) /
                ((d : ℝ) * Real.log (y : ℝ) ^ 2)) =
        (|beta| / L n) *
            (6 + 5 / Real.log (y : ℝ)) +
          (|beta| / L n) *
            (((((2 * n - K * h) / row.1 -
                n / row.1 : ℕ) : ℝ)) *
              (Real.log (d : ℝ) + 12) /
                ((d : ℝ) * Real.log (y : ℝ))) +
          (|beta| / L n) *
            (20 * C *
              ((((n / row.1 : ℕ) : ℝ)) +
                (((2 * n - K * h) / row.1 : ℕ) : ℝ)) /
                ((d : ℝ) * Real.log (y : ℝ) ^ 2)) := by ring
      _ ≤ |beta| * 31 * S +
          |beta| * (10 * G) * S +
          |beta| * (2000 * C / (d : ℝ)) * S :=
        add_le_add (add_le_add hconst hgapTerm) hendpointTerm
      _ = |beta| * Hbroad * S := by
        dsimp only [Hbroad]
        ring
  rw [mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
  by_cases hdLo : d ≤ n / row.1
  · rw [if_pos hdLo]
    calc
      |alpha| *
            roughSaiasSharpIntervalFixedDivisorBudget
              ((2 * n - K * h) / row.1)
              ((2 * n) / row.1) y d +
          |beta / L n| *
            roughSaiasSharpIntervalFixedDivisorBudget
              (n / row.1) ((2 * n - K * h) / row.1) y d ≤
        roughBalancedAlphaConstant W K0 c beta * Hhigh * S +
          |beta| * Hbroad * S :=
        add_le_add hhighWeighted hbroadWeighted
      _ ≤
        (roughBalancedAlphaConstant W K0 c beta * Hhigh +
          |beta| * Hbroad +
          4 * (roughBalancedAlphaConstant W K0 c beta + |beta|)) *
            S := by
        have hsmall0 :
            0 ≤ 4 *
              (roughBalancedAlphaConstant W K0 c beta + |beta|) :=
          mul_nonneg (by norm_num)
            (add_nonneg
              (roughBalancedAlphaConstant_nonneg
                W K0 (beta := beta) hc)
              (abs_nonneg beta))
        calc
          roughBalancedAlphaConstant W K0 c beta * Hhigh * S +
                |beta| * Hbroad * S =
              (roughBalancedAlphaConstant W K0 c beta * Hhigh +
                |beta| * Hbroad) * S := by ring
          _ ≤
              (roughBalancedAlphaConstant W K0 c beta * Hhigh +
                |beta| * Hbroad +
                4 * (roughBalancedAlphaConstant W K0 c beta + |beta|)) *
                  S :=
            mul_le_mul_of_nonneg_right
              (by
                simpa only [add_zero] using
                  add_le_add_right hsmall0
                    (roughBalancedAlphaConstant W K0 c beta * Hhigh +
                      |beta| * Hbroad))
              hSnonneg
      _ =
        roughCanonicalSharpHeadDivisorRowScaleConstant
          W K0 d c beta * S := by
        unfold roughCanonicalSharpHeadDivisorRowScaleConstant
        dsimp only [Hhigh, Hbroad, G, C]
        ring
  · rw [if_neg hdLo]
    have hsmall :
        4 * (|alpha| + |beta / L n|) ≤
          4 * (roughBalancedAlphaConstant W K0 c beta + |beta|) := by
      have hbetaAbs : |beta / L n| ≤ |beta| := by
        rw [abs_div, abs_of_pos hLPos]
        exact (div_le_iff₀ hLPos).2
          (by
            have := mul_le_mul_of_nonneg_left hLone (abs_nonneg beta)
            simpa only [mul_one] using this)
      exact mul_le_mul_of_nonneg_left
        (add_le_add halpha hbetaAbs) (by norm_num)
    calc
      4 * (|alpha| + |beta / L n|) ≤
          4 * (roughBalancedAlphaConstant W K0 c beta + |beta|) :=
        hsmall
      _ ≤
        (roughBalancedAlphaConstant W K0 c beta * Hhigh +
          |beta| * Hbroad +
          4 * (roughBalancedAlphaConstant W K0 c beta + |beta|)) *
            S := by
        have hbase0 :
            0 ≤ roughBalancedAlphaConstant W K0 c beta * Hhigh +
              |beta| * Hbroad := by
          exact add_nonneg
            (mul_nonneg
              (roughBalancedAlphaConstant_nonneg
                W K0 (beta := beta) hc) hHhigh)
            (mul_nonneg (abs_nonneg beta) hHbroad)
        have hsmall0 :
            0 ≤ 4 *
              (roughBalancedAlphaConstant W K0 c beta + |beta|) := by
          exact mul_nonneg (by norm_num)
            (add_nonneg
              (roughBalancedAlphaConstant_nonneg
                W K0 (beta := beta) hc)
              (abs_nonneg beta))
        calc
          4 * (roughBalancedAlphaConstant W K0 c beta + |beta|) ≤
              4 * (roughBalancedAlphaConstant W K0 c beta + |beta|) * S := by
            simpa only [mul_one] using
              mul_le_mul_of_nonneg_left hSone hsmall0
          _ ≤
              (roughBalancedAlphaConstant W K0 c beta * Hhigh +
                |beta| * Hbroad +
                4 * (roughBalancedAlphaConstant W K0 c beta + |beta|)) *
                  S :=
            mul_le_mul_of_nonneg_right
              (by
                simpa only [zero_add] using
                  add_le_add_left hbase0
                    (4 * (roughBalancedAlphaConstant W K0 c beta +
                      |beta|)))
              hSnonneg
      _ =
        roughCanonicalSharpHeadDivisorRowScaleConstant
          W K0 d c beta * S := by
        unfold roughCanonicalSharpHeadDivisorRowScaleConstant
        dsimp only [Hhigh, Hbroad, G, C]
        ring

/-! ## One unified canonical raw-row allowance -/













end

end Erdos390.WholePaper

end

theorem solution : Erdos390.RemainingAnalyticGoal008_016 := by
  exact @Erdos390.WholePaper.roughCanonicalBalancedSharpFixedHeadBudget_le
