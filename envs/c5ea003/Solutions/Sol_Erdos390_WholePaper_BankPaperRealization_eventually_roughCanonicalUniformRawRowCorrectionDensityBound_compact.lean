-- Prove2me | solution 1 for Erdos390.WholePaper.BankPaperRealization.eventually_roughCanonicalUniformRawRowCorrectionDensityBound_compact
-- status  : ACCEPTED   (prove)
-- author  : @doctosil
-- created : 2026-09-17T17:38:06.15046+00:00
-- url     : https://prove2.me/submissions/de98d9c3-b614-4920-ace4-ec09bab7efce

import Definitions.Def_erdos390_remaining_analytic_propositions_004
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
import Definitions.Def_erdos390_analytic_foundations_009
import Theorems.Thm_Erdos390_WholePaper_eventually_roughCanonicalBalancedRawRowQuotaError_abs_le_unified_active_compact
import Theorems.Thm_Erdos390_WholePaper_eventually_roughCanonical_activeRawBroadPool_linear_lower_compact



section
theorem Erdos390.WholePaper.eventually_roughCanonical_activeRawBroadPool_linear_lower : Erdos390.RemainingAnalyticGoal008_008 := @Erdos390.WholePaper.eventually_roughCanonical_activeRawBroadPool_linear_lower_compact
end
section
theorem Erdos390.WholePaper.eventually_roughCanonicalBalancedRawRowQuotaError_abs_le_unified_active : Erdos390.RemainingAnalyticGoal008_007 := @Erdos390.WholePaper.eventually_roughCanonicalBalancedRawRowQuotaError_abs_le_unified_active_compact
end
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

/- Source module: Erdos390.WholePaper.CompleteRoughDecomposition -/
section


/-!
# Complete rough/smooth decomposition

The complete rough label retains exactly the prime-power coordinates above
`y`.  This file defines the complementary literal quotient and proves that
the two pieces recover the original natural number, with exact complementary
factorizations and no auxiliary decomposition hypothesis.
-/

namespace Erdos390.WholePaper

noncomputable section



/-! ## Positivity, divisibility, and product recovery -/





/-- Literal Finsupp form of the high-prime factorization. -/
theorem completeRoughLabel_factorization_eq_filter_gt (y a : ℕ) :
    (completeRoughLabel y a).factorization =
      a.factorization.filter (fun p ↦ y < p) := by
  simpa only [completeRoughSignature] using
    completeRoughLabel_factorization y a

/-- Coordinate form of the exact high-prime factorization. -/
theorem completeRoughLabel_factorization_apply (y a p : ℕ) :
    (completeRoughLabel y a).factorization p =
      if y < p then a.factorization p else 0 := by
  have h := congrArg (fun f : ℕ →₀ ℕ ↦ f p)
    (completeRoughLabel_factorization_eq_filter_gt y a)
  simpa only [Finsupp.filter_apply] using h







/-! ## The complementary low-prime factorization -/





/-- Nonzero high-part coordinates lie strictly above the cutoff. -/
theorem completeRoughLabel_factorization_support
    {y a p : ℕ}
    (hp : (completeRoughLabel y a).factorization p ≠ 0) :
    y < p := by
  rw [completeRoughLabel_factorization_apply] at hp
  by_contra hpHigh
  simp [hpHigh] at hp









/-! ## Uniqueness and the smooth-label criterion -/







end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.FloatingRoundingRows -/
section


/-!
# Integer row sums force two fractional coordinates

After integral coordinates are frozen, an active row cannot contain exactly
one fractional coordinate: the whole row sum is an integer and every other
entry is zero or one.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

noncomputable section



@[simp]
theorem mem_rowSet {A R : Type*} [Fintype A]
    {row : A → R} {r : R} {a : A} :
    a ∈ rowSet row r ↔ row a = r := by
  classical
  simp [rowSet]





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





/-- The underlying-value map on the candidate subtype is injective. -/
theorem canonicalCompleteRoughCandidateValue_injective
    (A : Finset ℕ) :
    Function.Injective (canonicalCompleteRoughCandidateValue A) := by
  intro a b hab
  apply Subtype.ext
  exact hab



/-! ## Literal subtype fibers and `rowSet` -/







/-- Membership in the floating-rounding `rowSet` is exactly ambient row
fiber membership of the candidate value. -/
theorem mem_canonicalCompleteRoughRowSet_iff
    {y : ℕ} {A : Finset ℕ}
    {row : CanonicalCompleteRoughRow y A}
    {a : CompleteRoughCandidate A} :
    a ∈ rowSet (canonicalCompleteRoughRow y A) row ↔
      canonicalCompleteRoughCandidateValue A a ∈
        completeRoughRowFiber y A row.1 := by
  rw [mem_rowSet, mem_completeRoughRowFiber]
  constructor
  · intro hrow
    refine ⟨a.property, ?_⟩
    have hval := congrArg Subtype.val hrow
    simpa only [canonicalCompleteRoughRow,
      canonicalCompleteRoughCandidateValue] using hval
  · rintro ⟨_ha, hlabel⟩
    apply Subtype.ext
    simpa only [canonicalCompleteRoughRow,
      canonicalCompleteRoughCandidateValue] using hlabel



/-! ## Summation and integrality bridges -/

/-- Reindexing a canonical `rowSet` by underlying candidate values gives
the sum over the literal ambient complete rough fiber. -/
theorem sum_canonicalCompleteRoughRowSet_eq_sum_completeRoughRowFiber
    {W : Type*} [AddCommMonoid W]
    (y : ℕ) (A : Finset ℕ) (weight : ℕ → W)
    (row : CanonicalCompleteRoughRow y A) :
    ∑ a ∈ rowSet (canonicalCompleteRoughRow y A) row,
        weight (canonicalCompleteRoughCandidateValue A a) =
      ∑ value ∈ completeRoughRowFiber y A row.1,
        weight value := by
  classical
  apply Finset.sum_bij
    (fun a _ha ↦ canonicalCompleteRoughCandidateValue A a)
  · intro a ha
    exact mem_canonicalCompleteRoughRowSet_iff.mp ha
  · intro a₁ _ha₁ a₂ _ha₂ hvalue
    exact canonicalCompleteRoughCandidateValue_injective A hvalue
  · intro value hvalue
    let a : CompleteRoughCandidate A :=
      ⟨value, (mem_completeRoughRowFiber.mp hvalue).1⟩
    refine ⟨a, ?_, ?_⟩
    · apply mem_canonicalCompleteRoughRowSet_iff.mpr
      simpa only [a, canonicalCompleteRoughCandidateValue] using hvalue
    · simp only [a, canonicalCompleteRoughCandidateValue]
  · intro a _ha
    rfl









end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.RoughSaiasCanonicalRowBridge -/
section


/-!
# Canonical-row consumer for the weighted Saias block

The analytic four-endpoint expression is useful to the construction only
after it is tied back to the literal complete-rough row used by floating
rounding.  This file supplies that consumer-facing bridge.  The sum over a
canonical `rowSet` is identified unconditionally with the already-defined
literal raw row mass.  The upper quota minus that mass is then connected to
`roughPhysicalFriableCombination` and hence to the weighted Saias bound.

The upper endpoint identification is an exact equality.  Finite head
inclusion--exclusion and the fixed-head physical shift occur between the
literal raw mass and the density-scaled four-endpoint block in the paper,
so their error is retained as a separate explicit allowance.  It is not
silently folded into the HT--Saias hypothesis.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full

noncomputable section







/-- Every attained canonical row label has the intrinsic complete-rough
support property. -/
theorem isCompleteRoughLabel_of_canonicalCompleteRoughRow
    {y : ℕ} {A : Finset ℕ}
    (row : CanonicalCompleteRoughRow y A) :
    IsCompleteRoughLabel y row.1 := by
  constructor
  · exact canonicalCompleteRoughRow_label_pos y A row
  · obtain ⟨a, _ha, hlabel⟩ := mem_completeRoughLabelSet.mp row.2
    intro p hp
    rw [← hlabel] at hp
    exact completeRoughLabel_factorization_support hp























/-- The canonical row sum of the head-compatible raw weight is exactly the
ambient raw row mass.  This is the literal bridge from the finite point to
the canonical row type consumed by exactification. -/
theorem sum_canonicalCompleteRoughRowSet_rawWeight_eq_rawRowMass
    (W n h K y : ℕ) (α β L : ℝ)
    (row : CanonicalCompleteRoughRow y
      (roughRawCandidateSet n h K)) :
    ∑ a ∈ rowSet
        (canonicalCompleteRoughRow y (roughRawCandidateSet n h K)) row,
      roughHeadCompatibleRawWeight W n h K α β L
        (canonicalCompleteRoughCandidateValue
          (roughRawCandidateSet n h K) a) =
      roughHeadCompatibleRawRowMass W n h K y row.1 α β L := by
  simpa only [roughHeadCompatibleRawRowMass] using
    sum_canonicalCompleteRoughRowSet_eq_sum_completeRoughRowFiber
      y (roughRawCandidateSet n h K)
        (roughHeadCompatibleRawWeight W n h K α β L) row



/-- Ambient form of the canonical quota error. -/
theorem roughCanonicalRawRowQuotaError_eq_target_sub_rawRowMass
    (W n h K y : ℕ) (α β L : ℝ)
    (row : CanonicalCompleteRoughRow y
      (roughRawCandidateSet n h K)) :
    roughCanonicalRawRowQuotaError W n h K y α β L row =
      (roughUpperCompleteRoughRowTarget n h y row.1 : ℝ) -
        roughHeadCompatibleRawRowMass W n h K y row.1 α β L := by
  rw [roughCanonicalRawRowQuotaError,
    sum_canonicalCompleteRoughRowSet_rawWeight_eq_rawRowMass]













end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankPaperCanonicalRoughRowCorrection -/
section


/-!
# Finite constant-pool correction of one canonical rough row

The Saias-facing quantity `roughCanonicalRawRowQuotaError` is a row-mass
error.  The paper corrects such an error by spreading it uniformly over a
nonempty clean broad subpool in the same complete-signature row.  This file
formalizes that finite operation directly.

No selector handoff, feasibility conclusion, prime-residual estimate, or
asymptotic pool lower bound is assumed.  Exact row mass is an algebraic
consequence of nonemptiness and containment of the correction pool.
Feasibility is then *derived* from two explicit numerical facts: the raw
coordinates have a stated two-sided margin and the constant correction
density is no larger than that margin.

The final specialization uses the literal upper-row cardinality as target,
the literal head-compatible raw weight as baseline, and the head-free broad
fiber as correction pool.  Establishing the paper's uniform lower bound for
that pool after all guards, and the corresponding `o(1 / log n)` density
bound, remains a separate arithmetic task.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

noncomputable section

/-! ## Generic finite constant-pool correction -/















/-! ## Literal canonical rough-row specialization -/









/-- On a canonical row, the constant correction density is exactly the
Saias-facing quota error divided by the literal broad-pool cardinality. -/
theorem roughCanonicalRawRowCorrectionDensity_eq_quotaError_div
    (W n h K y : ℕ) (alpha beta L : ℝ)
    (row : CanonicalCompleteRoughRow y
      (roughRawCandidateSet n h K)) :
    bankPaperConstantPoolCorrectionDensity
        (completeRoughRowFiber y (roughRawCandidateSet n h K) row.1)
        (roughCanonicalBroadCorrectionPool W n h K y row.1)
        (roughHeadCompatibleRawWeight W n h K alpha beta L)
        (roughUpperCompleteRoughRowTarget n h y row.1 : ℝ) =
      roughCanonicalRawRowQuotaError W n h K y alpha beta L row /
        ((roughCanonicalBroadCorrectionPool W n h K y row.1).card : ℝ) := by
  rw [bankPaperConstantPoolCorrectionDensity,
    roughCanonicalRawRowQuotaError_eq_target_sub_rawRowMass]
  rfl







/-! ## Assembly over all attained complete rough rows -/













/-! ## Unconditional capped-quota selector -/





















end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankPaperCanonicalRawBroadSurplusAsymptotic -/
section


/-!
# Eventual raw broad-pool surplus on every active rough row

The tangent clean-list estimate is global in the common multiplier and
therefore cannot by itself give a lower bound in each complete rough row.
The rowwise input needed by the guard-capacity reduction is instead the
`active-clean-pool` estimate from Section 6 of the paper.  This file derives
that estimate from the already proved uniform de Bruijn bound and the
already proved fixed-head endpoint shift.

The proof has three quantitative layers.

* On a fixed-ratio interval `(A,B]`, the Dickman endpoint main term grows by
  a fixed positive multiple of `B-A`.  The uniform friable error is absorbed
  once `log y` is large.
* Exact head Möbius inversion and the fixed-divisor endpoint shift retain a
  fixed multiple of `A` in the head-free smooth interval.
* For an active label, `A = n / label` tends to infinity uniformly, while
  both `label / n` and `upperTailLength c n / n` tend to zero.  Consequently
  the broad pool dominates the literal upper-row quota and the three local
  guards.

The final theorem constructs
`RoughCanonicalActiveRawBroadSurplus ... 3 poolMinimum` for every fixed
`poolMinimum`, without a selector premise or an additional analytic
assumption.  The stronger linear real lower bound used to absorb that
constant is retained separately below.
-/

open Filter Topology
open scoped BigOperators ArithmeticFunction.Moebius

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.DickmanBasic
open Erdos390.Full.Scale
open Erdos390.Full.StructuredCells
open BankPaperRealization

noncomputable section

/-! ## A positive Dickman floor -/



/-- The fixed Dickman floor is strictly positive. -/
theorem roughCanonicalPoolDickmanFloor_pos :
    0 < roughCanonicalPoolDickmanFloor := by
  unfold roughCanonicalPoolDickmanFloor
  exact rho_pos_on_zero_five (by norm_num) le_rfl



/-! ## Growth of the unrestricted smooth interval -/





/-! ## Closing the fixed head -/









/-! ## Literal rough-row adapters -/



/-- The retained raw broad-pool density is strictly positive. -/
theorem roughCanonicalRawBroadPoolDensity_pos (W : Nat) :
    0 < roughCanonicalRawBroadPoolDensity W := by
  unfold roughCanonicalRawBroadPoolDensity
  exact div_pos
    (mul_pos (roughHeadDensity_pos W)
      roughCanonicalPoolDickmanFloor_pos) (by norm_num)









/-! ## Uniform paper-scale choices -/























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





























/-! ## The balanced Dickman main ledger -/





/-! ## The weighted sharp Saias transition ledger -/



/-! ## Absorption of the sharp fixed-head divisor sum -/



/-! ## One unified canonical raw-row allowance -/

theorem roughCanonicalSharpMainRowScaleConstant_nonneg
    (W K0 : ℕ) {c beta : ℝ} (hc : 0 < c) :
    0 ≤ roughCanonicalSharpMainRowScaleConstant W K0 c beta := by
  unfold roughCanonicalSharpMainRowScaleConstant
  have hA :=
    roughBalancedAlphaConstant_nonneg W K0 (beta := beta) hc
  have hK : (0 : ℝ) ≤ (((K0 + 1 : ℕ) : ℝ)) := by positivity
  positivity

theorem roughCanonicalSharpTransitionRowScaleConstant_nonneg
    (W K0 : ℕ) {c beta : ℝ} (hc : 0 < c) :
    0 ≤ roughCanonicalSharpTransitionRowScaleConstant W K0 c beta := by
  unfold roughCanonicalSharpTransitionRowScaleConstant
  have hA :=
    roughBalancedAlphaConstant_nonneg W K0 (beta := beta) hc
  have hC : 0 ≤ roughSaiasSharpDefectConstant := by
    unfold roughSaiasSharpDefectConstant
    have htheta : 0 ≤ roughSaiasThetaFourthPowerConstant :=
      roughSaiasThetaFourthPowerConstant_pos.le
    positivity
  positivity

theorem roughCanonicalSharpHeadDivisorRowScaleConstant_nonneg
    (W K0 : ℕ) {c beta : ℝ} (hc : 0 < c)
    {d : ℕ} (hd : 0 < d) :
    0 ≤ roughCanonicalSharpHeadDivisorRowScaleConstant
      W K0 d c beta := by
  unfold roughCanonicalSharpHeadDivisorRowScaleConstant
  have hA :=
    roughBalancedAlphaConstant_nonneg W K0 (beta := beta) hc
  have hC : 0 ≤ roughSaiasSharpDefectConstant := by
    unfold roughSaiasSharpDefectConstant
    have htheta : 0 ≤ roughSaiasThetaFourthPowerConstant :=
      roughSaiasThetaFourthPowerConstant_pos.le
    positivity
  have hdReal : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hlogd : 0 ≤ Real.log (d : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hd)
  positivity

theorem roughCanonicalSharpHeadRowScaleConstant_nonneg
    (W K0 : ℕ) {c beta : ℝ} (hc : 0 < c) :
    0 ≤ roughCanonicalSharpHeadRowScaleConstant W K0 c beta := by
  unfold roughCanonicalSharpHeadRowScaleConstant
  apply Finset.sum_nonneg
  intro d hdMem
  exact mul_nonneg (abs_nonneg _)
    (roughCanonicalSharpHeadDivisorRowScaleConstant_nonneg
      W K0 (beta := beta) hc (Nat.pos_of_mem_divisors hdMem))

theorem roughCanonicalSharpUnifiedRowScaleConstant_nonneg
    (W K0 : ℕ) {c beta : ℝ} (hc : 0 < c) :
    0 ≤ roughCanonicalSharpUnifiedRowScaleConstant W K0 c beta := by
  unfold roughCanonicalSharpUnifiedRowScaleConstant
  exact add_nonneg
    (add_nonneg
      (roughCanonicalSharpMainRowScaleConstant_nonneg
        W K0 (beta := beta) hc)
      (roughCanonicalSharpTransitionRowScaleConstant_nonneg
        W K0 (beta := beta) hc))
    (roughCanonicalSharpHeadRowScaleConstant_nonneg
      W K0 (beta := beta) hc)



end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankPaperCanonicalSignedGuardResidual -/
section


/-!
# Signed exceptional and guard residual ledger

This module gives literal names to the two signed terms in the final rough
residual identity.  They are intentionally separate from the nonnegative
fixed-factor charge used for divisibility.

`roughCanonicalSignedExceptionalResidual` is the exceptional-row portion of
the raw upper-minus-lower comparison.  The order of its two finite sums is
not replaced by a sum of absolute values.  `roughCanonicalAggregateGuardResidual`
is the paper's three-term guard difference: restored raw weights deleted in
nonexceptional rows, restored exceptional donors, and the negative bank-base
charge.

The exact four-term sign convention and its triangle reduction are proved at
the end.  The aggregate guard term is bounded and absorbed unconditionally
from the literal finite census, and the correction-pool valuation census is
also closed by the global Legendre prefix bound.  The genuinely signed
exceptional estimate and the uniform correction-density estimate remain
exposed as named propositions rather than being confused with the already
proved nonnegative exceptional charge bound.
-/

open Filter Topology Asymptotics
open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel
open Erdos390.Full.Scale

noncomputable section

namespace BankPaperRealization

/-! ## Elementary finite valuation envelopes -/







/-! ## Literal signed exceptional term -/











/-! ## Literal aggregate guard difference -/

















/-! ## A uniform finite guard-profile bound -/











/-! ## Uniform absorption of the guard majorant -/















/-! ## Literal aggregate nonsmooth row correction -/









/-- On an attained active label, the literal density is the already
formalized row-quota error divided by the broad-pool cardinality. -/
theorem roughCanonicalRawCorrectionDensityAtLabel_eq_quotaError_div
    {W n h K label : Nat} {alpha beta logScale deltaStar : Real}
    (hlabel : label ∈
      roughCanonicalActiveRawCorrectionLabels n h K deltaStar) :
    roughCanonicalRawCorrectionDensityAtLabel
        W n h K alpha beta logScale label =
      roughCanonicalRawRowQuotaError W n h K (yNat n)
          alpha beta logScale
          ⟨label, (mem_roughCanonicalActiveRawCorrectionLabels.mp
            hlabel).1⟩ /
        ((roughCanonicalBroadCorrectionPool
          W n h K (yNat n) label).card : Real) := by
  simpa only [roughCanonicalRawCorrectionDensityAtLabel] using
    roughCanonicalRawRowCorrectionDensity_eq_quotaError_div
      W n h K (yNat n) alpha beta logScale
        ⟨label, (mem_roughCanonicalActiveRawCorrectionLabels.mp
          hlabel).1⟩











/-! ## Exact final sign ledger and quantitative reduction -/





























end BankPaperRealization

end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankPaperCanonicalRawRowCorrectionRateClosure -/
section


/-!
# Paper-rate closure for the raw nonsmooth row correction

The signed residual ledger isolates a uniform bound for the literal raw
row-correction density.  That bound is not an additional analytic input.
The sharp row theorem gives a numerator

`O_W((n / label) / L^2 + 1)`,

while the raw broad-pool theorem gives a denominator bounded below by a
fixed positive multiple of `n / label`.  On active nonexceptional rows the
same real cutoff in the definition of the row implies, uniformly,
`L^2 <= n / label`; hence the endpoint `+1` is absorbed.

This file records that conversion and then invokes the global valuation
census already proved in `BankPaperCanonicalSignedGuardResidual`.
-/

open Filter Topology

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel
open Erdos390.Full.Scale

noncomputable section

namespace BankPaperRealization





private theorem rawRowCorrectionRate_L_sq_div_rpow_tendsto_zero
    {deltaStar : Real} (hdelta : 0 < deltaStar) :
    Tendsto (fun n : Nat => L n ^ 2 / (n : Real) ^ deltaStar)
      atTop (nhds 0) := by
  have hreal : Tendsto
      (fun x : Real =>
        Real.log x ^ (2 : Real) / x ^ deltaStar)
      atTop (nhds 0) :=
    (isLittleO_log_rpow_rpow_atTop (2 : Real) hdelta).tendsto_div_nhds_zero
  have hnat := hreal.comp tendsto_natCast_atTop_atTop
  change Tendsto
    (fun n : Nat =>
      Real.log (n : Real) ^ (2 : Real) / (n : Real) ^ deltaStar)
      atTop (nhds 0) at hnat
  simpa [L, Real.rpow_natCast] using hnat

private theorem rawRowCorrectionRate_rpow_tendsto_atTop
    {deltaStar : Real} (hdelta : 0 < deltaStar) :
    Tendsto (fun n : Nat => (n : Real) ^ deltaStar) atTop atTop := by
  exact (tendsto_rpow_atTop hdelta).comp tendsto_natCast_atTop_atTop

/-- The literal balanced raw correction density has the strict
`constant/(4 L^2)` scale, eventually and uniformly over every attained
active nonexceptional label. -/
theorem eventually_roughCanonicalUniformRawRowCorrectionDensityBound
    (W K0 : Nat) {c beta deltaStar : Real}
    (hc : 0 < c) (hdelta : 0 < deltaStar) :
    ∀ᶠ n : Nat in atTop,
      RoughCanonicalUniformRawRowCorrectionDensityBound
        W n (upperTailLength c n) (K0 + 1) deltaStar
        (roughHeadBalancedAlpha W n (upperTailLength c n)
          (K0 + 1) beta (L n))
        beta (L n)
        (roughCanonicalUniformRawRowCorrectionDensityConstant
          W K0 c beta / (4 * L n ^ 2)) := by
  let C := roughCanonicalSharpUnifiedRowScaleConstant W K0 c beta
  let d := roughCanonicalRawBroadPoolDensity W
  have hC : 0 <= C := by
    dsimp only [C]
    exact roughCanonicalSharpUnifiedRowScaleConstant_nonneg
      W K0 (beta := beta) hc
  have hd : 0 < d := by
    dsimp only [d]
    exact roughCanonicalRawBroadPoolDensity_pos W
  have hraw :=
    Erdos390.WholePaper.eventually_roughCanonicalBalancedRawRowQuotaError_abs_le_unified_active
      W K0 (beta := beta) hc hdelta
  have hpool :=
    eventually_roughCanonical_activeRawBroadPool_linear_lower
      W (K0 + 1) hc hdelta
  have hratio : ∀ᶠ n : Nat in atTop,
      L n ^ 2 / (n : Real) ^ deltaStar < 1 / 4 :=
    (rawRowCorrectionRate_L_sq_div_rpow_tendsto_zero hdelta).eventually
      (eventually_lt_nhds (by norm_num : (0 : Real) < 1 / 4))
  have hpower : ∀ᶠ n : Nat in atTop,
      (4 : Real) <= (n : Real) ^ deltaStar :=
    (rawRowCorrectionRate_rpow_tendsto_atTop hdelta).eventually
      (eventually_ge_atTop 4)
  filter_upwards [eventually_gt_atTop 1, hraw, hpool, hratio, hpower]
      with n hn hrawN hpoolN hratioN hpowerN
  unfold RoughCanonicalUniformRawRowCorrectionDensityBound
  intro label hlabel
  have hlabelParts :=
    mem_roughCanonicalActiveRawCorrectionLabels.mp hlabel
  let row : CanonicalCompleteRoughRow (yNat n)
      (roughRawCandidateSet n (upperTailLength c n) (K0 + 1)) :=
    ⟨label, hlabelParts.1⟩
  have hlabelData : IsCompleteRoughLabel (yNat n) label := by
    simpa only [row] using
      (isCompleteRoughLabel_of_canonicalCompleteRoughRow row)
  have hlabelPos : 0 < label := hlabelData.1
  have hlabelReal : (0 : Real) < (label : Real) := by
    exact_mod_cast hlabelPos
  have hnReal : (0 : Real) < (n : Real) := by
    exact_mod_cast (show 0 < n by omega)
  have hpowPos : (0 : Real) < (n : Real) ^ deltaStar :=
    Real.rpow_pos_of_pos hnReal deltaStar
  have hL : 0 < L n := L_pos hn
  let X : Real := ((n / label : Nat) : Real)
  have hquotient :
      (n : Real) ^ deltaStar / 2 <=
        (n : Real) / (label : Real) := by
    apply (div_le_iff₀ (by norm_num : (0 : Real) < 2)).2
    calc
      (n : Real) ^ deltaStar <=
          2 * (n : Real) / (label : Real) := hlabelParts.2.2
      _ = (n : Real) / (label : Real) * 2 := by ring
  have hnatUpper :
      (n : Real) / (label : Real) < X + 1 := by
    dsimp only [X]
    apply (div_lt_iff₀ hlabelReal).2
    have hnat := (Nat.div_lt_iff_lt_mul hlabelPos).mp
      (Nat.lt_succ_self (n / label))
    exact_mod_cast hnat
  have hlogSmall :
      L n ^ 2 < (n : Real) ^ deltaStar / 4 := by
    have hcross := (div_lt_iff₀ hpowPos).mp hratioN
    nlinarith
  have hpowerAbsorb :
      2 * (L n ^ 2 + 1) <= (n : Real) ^ deltaStar := by
    nlinarith
  have hX : L n ^ 2 <= X := by
    have hstrict : L n ^ 2 < X := by
      nlinarith
    exact hstrict.le
  have hXPos : 0 < X := (sq_pos_of_pos hL).trans_le hX
  have hpoolLower :
      d * X <=
        ((roughCanonicalBroadCorrectionPool W n (upperTailLength c n)
          (K0 + 1) (yNat n) label).card : Real) := by
    simpa only [d, X] using hpoolN label hlabelData hlabelParts.2
  have hpoolPos :
      (0 : Real) <
        ((roughCanonicalBroadCorrectionPool W n (upperTailLength c n)
          (K0 + 1) (yNat n) label).card : Real) :=
    (mul_pos hd hXPos).trans_le hpoolLower
  have hone : (1 : Real) <= X / L n ^ 2 := by
    exact (le_div_iff₀ (sq_pos_of_pos hL)).2 (by simpa using hX)
  have hrawRow :
      |roughCanonicalRawRowQuotaError W n (upperTailLength c n)
          (K0 + 1) (yNat n)
          (roughHeadBalancedAlpha W n (upperTailLength c n)
            (K0 + 1) beta (L n))
          beta (L n) row| <=
        3 * (C * (X / L n ^ 2 + 1)) := by
    simpa only [C, X, row] using hrawN row hlabelParts.2
  have hquota :
      |roughCanonicalRawRowQuotaError W n (upperTailLength c n)
          (K0 + 1) (yNat n)
          (roughHeadBalancedAlpha W n (upperTailLength c n)
            (K0 + 1) beta (L n))
          beta (L n) row| <=
        6 * C * X / L n ^ 2 := by
    calc
      _ <= 3 * (C * (X / L n ^ 2 + 1)) := hrawRow
      _ <= 3 * (C * (X / L n ^ 2 + X / L n ^ 2)) := by
        gcongr
      _ = 6 * C * X / L n ^ 2 := by ring
  have hcoefficient :
      0 <= (24 * C / d) / (4 * L n ^ 2) := by positivity
  have hdensity :
      |roughCanonicalRawCorrectionDensityAtLabel
          W n (upperTailLength c n) (K0 + 1)
          (roughHeadBalancedAlpha W n (upperTailLength c n)
            (K0 + 1) beta (L n))
          beta (L n) label| <=
        (24 * C / d) / (4 * L n ^ 2) := by
    have hpoolNonneg :
        (0 : Real) <=
          ((roughCanonicalBroadCorrectionPool W n (upperTailLength c n)
            (K0 + 1) (yNat n) label).card : Real) :=
      Nat.cast_nonneg _
    rw [roughCanonicalRawCorrectionDensityAtLabel_eq_quotaError_div hlabel,
      abs_div, abs_of_nonneg hpoolNonneg]
    apply (div_le_iff₀ hpoolPos).2
    calc
      |roughCanonicalRawRowQuotaError W n (upperTailLength c n)
          (K0 + 1) (yNat n)
          (roughHeadBalancedAlpha W n (upperTailLength c n)
            (K0 + 1) beta (L n))
          beta (L n)
          ⟨label, hlabelParts.1⟩| <=
          6 * C * X / L n ^ 2 := by
        simpa only [row] using hquota
      _ = ((24 * C / d) / (4 * L n ^ 2)) * (d * X) := by
        field_simp [hd.ne', hL.ne']; ring
      _ <= ((24 * C / d) / (4 * L n ^ 2)) *
          ((roughCanonicalBroadCorrectionPool W n
            (upperTailLength c n) (K0 + 1) (yNat n) label).card : Real) :=
        mul_le_mul_of_nonneg_left hpoolLower hcoefficient
  simpa only [
    roughCanonicalUniformRawRowCorrectionDensityConstant, C, d] using
      hdensity



end BankPaperRealization

end

end Erdos390.WholePaper

end

theorem solution : Erdos390.RemainingAnalyticGoal004_018 := by
  exact @Erdos390.WholePaper.BankPaperRealization.eventually_roughCanonicalUniformRawRowCorrectionDensityBound
