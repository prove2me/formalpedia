-- Prove2me | solution 1 for Erdos390.WholePaper.BankPaperRealization.eventually_roughCanonicalUniformGuardedPostchargeCorrectionDensityBound_compact
-- status  : ACCEPTED   (prove)
-- author  : @doctosil
-- created : 2026-09-17T17:38:06.184015+00:00
-- url     : https://prove2.me/submissions/9d26dbdc-cdf2-4ddd-af22-a450a26f7d74

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
import Definitions.Def_erdos390_analytic_foundations_010
import Theorems.Thm_Erdos390_WholePaper_eventually_roughCanonicalBalancedRawRowQuotaError_abs_le_unified_active_compact
import Theorems.Thm_Erdos390_WholePaper_eventually_roughCanonical_activeRawBroadPool_linear_lower_compact
import Theorems.Thm_Erdos390_WholePaper_fullCentralAnchors_completeRoughLabel_injective_of_ne_one



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













/-- The upper tail is disjoint from every raw lower candidate. -/
theorem roughUpperBlock_disjoint_rawCandidateSet
    (n h K : ℕ) :
    Disjoint (roughUpperBlock n h) (roughRawCandidateSet n h K) := by
  rw [Finset.disjoint_left]
  intro a haUpper haLower
  simp only [roughUpperBlock, roughRawCandidateSet,
    roughHighLowerBlock, roughBroadLowerBlock, Finset.mem_Ioc,
    Finset.mem_union] at haUpper haLower
  rcases haLower with haHigh | haBroad <;> omega







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

/-- A complete rough label is always positive, including for `a = 0`, when
the empty factorization gives label `1`. -/
theorem completeRoughLabel_pos (y a : ℕ) :
    0 < completeRoughLabel y a := by
  rw [completeRoughLabel]
  apply Nat.prod_pow_pos_of_zero_notMem_support
  rw [Finsupp.notMem_support_iff, completeRoughSignature_apply]
  simp

theorem completeRoughLabel_ne_zero (y a : ℕ) :
    completeRoughLabel y a ≠ 0 :=
  (completeRoughLabel_pos y a).ne'

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

/-- The retained high-prime product is a literal divisor of the original
number. -/
theorem completeRoughLabel_dvd (y a : ℕ) :
    completeRoughLabel y a ∣ a := by
  by_cases ha : a = 0
  · rw [ha]
    exact dvd_zero _
  · rw [← Nat.factorization_le_iff_dvd
      (completeRoughLabel_ne_zero y a) ha,
      completeRoughLabel_factorization_eq_filter_gt]
    intro p
    rw [Finsupp.filter_apply]
    split_ifs <;> simp





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

/- Source module: Erdos390.WholePaper.BankBottomMarkerPools -/
section


/-!
# Literal marker pools for the four bottom bank moves

The four rows below are the natural-number half-open intervals appearing in
the paper.  Each is split at its integer midpoint into two fixed one-half
orientation subintervals.  This file proves only exact finite interval and
factor arithmetic; prime supply is deliberately kept separate.
-/

namespace Erdos390.WholePaper

noncomputable section











































/-- A marker in its row makes both endpoint states and the donor lie in
the factor interval `(n,M]`. -/
theorem bankBottom_states_donor_mem_factorInterval
    {n M marker : ℕ} {move : BankBottomMove}
    (hmarker : marker ∈ bankBottomMarkerInterval n M move) :
    bankBottomLowerState move marker ∈ factorInterval n M ∧
      bankBottomUpperState move marker ∈ factorInterval n M ∧
      bankBottomDonor move marker ∈ factorInterval n M := by
  cases move <;>
    simp only [bankBottomMarkerInterval, bankBottomMarkerLower,
      bankBottomMarkerUpper, Finset.mem_Ioc, bankBottomLowerState,
      bankBottomUpperState, bankBottomDonor,
      bankBottomLowerStateMultiplier, bankBottomUpperStateMultiplier,
      bankBottomDonorMultiplier, factorInterval] at hmarker ⊢ <;>
    omega



















end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankBottomPaperComponents -/
section


/-!
# Actual bottom-bank components from the concrete marker matching

The capacity argument deliberately matches the rectangular upper-bound family
consisting of every signed slot and all four bottom rows.  The path belonging
to a small source prime does not use every one of those rows: source `3` uses
only `3→2→1`, and source `2` uses only `2→1`.  This file therefore separates
the full matched family from the literal relevant subfamily before forming any
set of used occurrences.

For every matched request we retain its actual prime marker, the two state
factors in the corresponding row, and its donor occurrence.  A finite set of
occurrence values is used, so in the last two rows the donor and the upper
state are literally one occurrence, rather than two tagged copies.  The only
global input is the already constructed injective marker matching.  All other
claims below are explicit interval, factorization, and large-prime arithmetic.
-/

open Filter Topology
open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel
open Erdos390.Full.Scale

noncomputable section

/-! ## The literal relevant subfamily -/





















































/-! ## The deterministic truncated bottom path -/

























/-! ## A realization obtained from the actual matching -/





namespace BankBottomPaperRealization

variable {n M : ℕ} (realization : BankBottomPaperRealization n M)





















/-- Both row endpoints and the donor are actual factors in `(n,M]`. -/
theorem states_donor_mem_factorInterval (hTwoN : 2 * n ≤ M)
    (request : ↑(bankBottomPaperRequests n)) :
    realization.lowerStateFactor request ∈ factorInterval n M ∧
      realization.upperStateFactor request ∈ factorInterval n M ∧
      realization.donorFactor request ∈ factorInterval n M := by
  simpa only [lowerStateFactor, upperStateFactor, donorFactor] using
    bankBottom_states_donor_mem_factorInterval
      (realization.marker_mem_row hTwoN request)







/-! The four paper rows, with the marker made explicit. -/













/-! ## Orientation-aware realized row and slot changes -/























end BankBottomPaperRealization

/-! ## Complete occurrence sets and rough signatures -/









namespace BankBottomPaperRealization

variable {n M : ℕ} (realization : BankBottomPaperRealization n M)























































end BankBottomPaperRealization

/-! ## Explicit local geometry and collision freedom -/



namespace BankBottomPaperRealization

variable {n M : ℕ} (realization : BankBottomPaperRealization n M)









/-! ## Relevant markers and marker-to-component uniqueness -/



























end BankBottomPaperRealization

/-! ## Cardinality bound for the actual relevant marker set -/







/-! ## Eventual local geometry and the terminal realized family -/









end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankOrdinaryPaperComponents -/
section


/-!
# Realized ordinary bank components

An ordinary matching supplies an actual pair `(P,u)` to every concrete path
request `q→b`.  This file materializes the three factor occurrences

* source state `P*q`,
* target state `P*b`, and
* backing donor `P*u`.

All three lie in `(n,M]` and have the same complete rough signature.  The
large prime marker is recovered uniquely from any realized occurrence, which
gives marker injectivity, donor-product injectivity, and collision-freedom
across requests, scales, and orientations.  Finally, cancellation of the
common marker turns the realized component changes back into the actual
finite path telescope.

The public names intentionally mirror `BankBottomPaperComponents`: a
realization object, factor-valued methods, an occurrence-kind enumeration,
and `occurrenceValue`.
-/

open Filter Topology Asymptotics
open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel
open Erdos390.Full.Scale

noncomputable section

/-! ## Coarse global size bounds -/













/-! ## Arithmetic helpers for rough signatures -/









/-! ## Marker injectivity inherited from the orientation pools -/









/-! ## The public realization object and its actual factors -/



namespace BankOrdinaryPaperRealization





































theorem donorValue_mem_factorInterval
    {n M : ℕ} (R : BankOrdinaryPaperRealization n M)
    (request : ↑(bankOrdinaryPaperRequests n)) :
    R.donorValue request ∈ factorInterval n M := by
  have heligible := mem_bankOrdinaryEligibleRelation.mp
    (R.markerDonorPair_mem request)
  simp only [donorValue, factorInterval, Finset.mem_Ioc]
  have hlower := heligible.2.2.2.2.2.2.1
  change 2 * n < R.marker request * R.donorCore request at hlower
  exact ⟨by omega, heligible.2.2.2.2.2.2.2⟩





































/-! ## The three actual occurrences and global collision-freedom -/





theorem two_mul_n_lt_donorValue
    {n M : ℕ} (R : BankOrdinaryPaperRealization n M)
    (request : ↑(bankOrdinaryPaperRequests n)) :
    2 * n < R.donorValue request :=
  (mem_bankOrdinaryEligibleRelation.mp
    (R.markerDonorPair_mem request)).2.2.2.2.2.2.1

































/-! ## Realized component and signed-slot changes -/























end BankOrdinaryPaperRealization

/-! ## Eventual realized allocation -/



end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankPaperComponents -/
section


/-!
# Combined bottom and ordinary bank realization

This file is only the composition layer.  The two allocation mechanisms stay
independent, but their marker ranges are strictly separated:

`3 * ordinaryMarker < n < 3 * bottomMarker`.

Consequently the marker maps remain injective after the two request families
are joined.  Prime-marker recovery also turns this strict separation into
cross-family disjointness of the actual state/donor occurrence sets.
-/

open Filter Topology
open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel
open Erdos390.Full.Scale

noncomputable section





namespace BankPaperRealization





/-- Marker assignment is globally injective after adjoining the relevant
bottom requests and all ordinary requests. -/
theorem marker_injective
    {n M : ℕ} (R : BankPaperRealization n M) :
    Function.Injective R.marker := by
  intro request request' hmarker
  cases request with
  | inl bottomRequest =>
      cases request' with
      | inl bottomRequest' =>
          have hrequest : bottomRequest = bottomRequest' :=
            R.bottom.relevantMarkerMap_injective
              (by simpa only [marker] using hmarker)
          exact congrArg Sum.inl hrequest
      | inr ordinaryRequest =>
          exfalso
          have hlt := R.ordinaryMarker_lt_bottomMarker ordinaryRequest
            (bankBottomRelevantRequestToPaperRequest bottomRequest)
          simp only [marker] at hmarker
          omega
  | inr ordinaryRequest =>
      cases request' with
      | inl bottomRequest =>
          exfalso
          have hlt := R.ordinaryMarker_lt_bottomMarker ordinaryRequest
            (bankBottomRelevantRequestToPaperRequest bottomRequest)
          simp only [marker] at hmarker
          omega
      | inr ordinaryRequest' =>
          have hrequest : ordinaryRequest = ordinaryRequest' :=
            R.ordinary.marker_injective
              (by simpa only [marker] using hmarker)
          exact congrArg Sum.inr hrequest











/-! ## Cross-family actual occurrence disjointness -/

















end BankPaperRealization

/-! ## Terminal combined realization -/



end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankPaperPrecharge -/
section


/-!
# The actual precharged bank state

This module is independent of the eventual path selector.  Its component
index is the already realized global request type: every relevant bottom row
and every ordinary row occurs exactly once.  For each component we expose its
orientation-aware base and alternate states and its actual donor occurrence.

The proofs below use only the explicit component geometry.  In particular,
there is no abstract capacity or compatibility hypothesis: global
injectivity follows from the realized occurrence-set disjointness, and the
donor tail is the literal interval `(2n,M]`.
-/

open Filter Topology Asymptotics
open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel
open Erdos390.Full.Scale

noncomputable section



namespace BankBottomPaperRealization

/-- Every actual bottom donor is in the strict tail above `2n`. -/
theorem two_mul_n_lt_donorFactor
    {n M : ℕ} (R : BankBottomPaperRealization n M)
    (hTwoN : 2 * n ≤ M)
    (request : ↑(bankBottomPaperRequests n)) :
    2 * n < R.donorFactor request := by
  have hrow := R.marker_mem_row hTwoN request
  cases hmove : R.move request <;>
    simp only [hmove, bankBottomMarkerInterval, bankBottomMarkerLower,
      bankBottomMarkerUpper, Finset.mem_Ioc, donorFactor,
      bankBottomDonor, bankBottomDonorMultiplier] at hrow ⊢ <;> omega

end BankBottomPaperRealization

namespace BankPaperRealization

attribute [local instance] Erdos390.WholePaper.BankPaperRealization.bankPaperMarkerRequestDecidableEq

/-! ## Global component data -/

























/-! ## Complete rough signatures -/







/-! ## Endpoint and donor injectivity -/





















/-! ## Literal finite states, donor tail, and replacement map -/

























/-- Every donor, ordinary or bottom, is an actual factor in `(2n,M]`. -/
theorem prechargeDonorValue_mem_tail
    {n M : ℕ} (R : BankPaperRealization n M)
    (request : BankPaperMarkerRequest n) :
    R.prechargeDonorValue request ∈ Finset.Ioc (2 * n) M := by
  cases request with
  | inl request =>
      let fullRequest := bankBottomRelevantRequestToPaperRequest request
      have hlower := R.bottom.two_mul_n_lt_donorFactor
        R.ordinary.two_mul_n_le_M fullRequest
      have hupper : R.bottom.donorFactor fullRequest ≤ M := by
        have hdata : n < R.bottom.donorFactor fullRequest ∧
            R.bottom.donorFactor fullRequest ≤ M := by
          simpa only [factorInterval, Finset.mem_Ioc] using
            (R.bottom.states_donor_mem_factorInterval
              R.ordinary.two_mul_n_le_M fullRequest).2.2
        exact hdata.2
      simpa only [prechargeDonorValue, fullRequest,
        Finset.mem_Ioc] using And.intro hlower hupper
  | inr request =>
      have hlower := R.ordinary.two_mul_n_lt_donorValue request
      have hupper : R.ordinary.donorValue request ≤ M := by
        have hdata : n < R.ordinary.donorValue request ∧
            R.ordinary.donorValue request ≤ M := by
          simpa only [factorInterval, Finset.mem_Ioc] using
            (R.ordinary.donorValue_mem_factorInterval request)
        exact hdata.2
      simpa only [prechargeDonorValue, Finset.mem_Ioc] using
        And.intro hlower hupper

theorem prechargeDonorSet_subset_tail
    {n M : ℕ} (R : BankPaperRealization n M) :
    R.prechargeDonorSet ⊆ Finset.Ioc (2 * n) M := by
  intro donor hdonor
  rw [prechargeDonorSet, indexedPathState, Finset.mem_image] at hdonor
  obtain ⟨request, _hrequest, rfl⟩ := hdonor
  exact R.prechargeDonorValue_mem_tail request





















/-! ## Component counts and the base product -/























end BankPaperRealization

end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankPaperFixedExceptionalBacking -/
section


/-!
# The literal fixed exceptional factors and their high-prime backing

The paper fixes every upper-tail factor whose complete rough row has real
scale `2n / R_y(a) < n ^ deltaStar`, except for the actual donor occurrences
already withheld for the precharged bank.  This file makes that set literal.

The definition deliberately uses the displayed real quotient and real power.
It is not the larger integral test obtained by flooring the rough scale and
ceiling the exceptional cutoff.

At every prime above the rough cutoff, replacing the donor set by the bank's
base state preserves factorization coordinatewise.  The fixed exceptional
factors and donors are disjoint subsets of the literal tail, so their union
is an unconditional backing product for the complete selector charge in
all such coordinates.  No small-prime charge estimate is asserted here.
-/

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel

noncomputable section







namespace BankPaperRealization





theorem paperFixedExceptionalFactors_subset_upperBlock
    {n h : ℕ}
    (R : BankPaperRealization n (upperEndpoint n h))
    (deltaStar : ℝ) :
    R.paperFixedExceptionalFactors deltaStar ⊆ roughUpperBlock n h := by
  intro a ha
  rw [paperFixedExceptionalFactors, Finset.mem_sdiff] at ha
  exact (mem_paperExceptionalUpperFactors.mp ha.1).1





















end BankPaperRealization

end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankPaperCanonicalGuardLocalRowLedger -/
section


/-!
# Guard-local canonical rough-row ledger

This module isolates the finite bookkeeping that occurs when the paper
passes from the raw canonical rough candidates to the candidates left after
the numerical guards

`Gamma_num = anchors ∪ G_fix ∪ E_donor ∪ G_bank^0 ∪ G_bank^1`.

Only literal finite-set identities are proved here.  In particular, this
file does **not** assume or assert a local guard census, a lower bound for a
guarded broad pool, or enough guarded-row capacity for a corrected selector.
Those still-missing estimates are exposed at the end as named propositions.

The postcharge target is kept in `Real` form for the correction algebra and
in `Int` form for its exact integrality witness.  Its nonnegativity is a
finite consequence of the actual donor/base row-preserving bijection and of
the disjoint upper-tail backing of the fixed exceptional factors and donors.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel

noncomputable section

namespace BankPaperRealization

/-! ## Literal guarded candidates and row pieces -/



















/-- Filtering after deleting the guards is the same as deleting the guards
inside each raw complete rough row. -/
theorem roughCanonicalGuardedRow_eq_rawRow_sdiff_guardSet
    {c : ℝ} {depth n h : ℕ} {left right : ℕ → ℕ}
    {changed : Finset ℕ}
    (R : BankPaperRealization n (upperEndpoint n h))
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (deltaStar : ℝ) (K label : ℕ) :
    R.roughCanonicalGuardedRow certificate deltaStar K label =
      completeRoughRowFiber (yNat n)
          (roughRawCandidateSet n h K) label \
        R.roughCanonicalGuardSet certificate deltaStar := by
  ext a
  simp only [roughCanonicalGuardedRow,
    roughCanonicalGuardedCandidateSet, mem_completeRoughRowFiber,
    Finset.mem_sdiff]
  tauto

/-- The surviving and deleted parts are disjoint. -/
theorem roughCanonicalGuardedRow_disjoint_guardDeletedRow
    {c : ℝ} {depth n h : ℕ} {left right : ℕ → ℕ}
    {changed : Finset ℕ}
    (R : BankPaperRealization n (upperEndpoint n h))
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (deltaStar : ℝ) (K label : ℕ) :
    Disjoint
      (R.roughCanonicalGuardedRow certificate deltaStar K label)
      (R.roughCanonicalGuardDeletedRow certificate deltaStar K label) := by
  rw [Finset.disjoint_left]
  intro a haGuarded haDeleted
  rw [R.roughCanonicalGuardedRow_eq_rawRow_sdiff_guardSet
    certificate deltaStar K label, Finset.mem_sdiff] at haGuarded
  rw [roughCanonicalGuardDeletedRow, Finset.mem_inter] at haDeleted
  exact haGuarded.2 haDeleted.2

/-- The two row pieces exhaust the original raw row. -/
theorem roughCanonicalGuardedRow_union_guardDeletedRow
    {c : ℝ} {depth n h : ℕ} {left right : ℕ → ℕ}
    {changed : Finset ℕ}
    (R : BankPaperRealization n (upperEndpoint n h))
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (deltaStar : ℝ) (K label : ℕ) :
    R.roughCanonicalGuardedRow certificate deltaStar K label ∪
        R.roughCanonicalGuardDeletedRow certificate deltaStar K label =
      completeRoughRowFiber (yNat n)
        (roughRawCandidateSet n h K) label := by
  rw [R.roughCanonicalGuardedRow_eq_rawRow_sdiff_guardSet
    certificate deltaStar K label]
  ext a
  simp only [roughCanonicalGuardDeletedRow, Finset.mem_union,
    Finset.mem_sdiff, Finset.mem_inter]
  tauto

/-- Exact additive decomposition of any real row mass into its surviving
and guard-deleted parts. -/
theorem sum_roughCanonicalGuardedRow_add_sum_guardDeletedRow
    {c : ℝ} {depth n h : ℕ} {left right : ℕ → ℕ}
    {changed : Finset ℕ}
    (R : BankPaperRealization n (upperEndpoint n h))
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (deltaStar : ℝ) (K label : ℕ) (x : ℕ → ℝ) :
    (∑ a ∈ R.roughCanonicalGuardedRow certificate deltaStar K label,
        x a) +
      ∑ a ∈ R.roughCanonicalGuardDeletedRow certificate deltaStar
        K label, x a =
      ∑ a ∈ completeRoughRowFiber (yNat n)
        (roughRawCandidateSet n h K) label, x a := by
  rw [← Finset.sum_union
      (R.roughCanonicalGuardedRow_disjoint_guardDeletedRow
        certificate deltaStar K label),
    R.roughCanonicalGuardedRow_union_guardDeletedRow
      certificate deltaStar K label]

/-! ## The donor/base row-preserving bijection -/









/-! ## Upper-tail ownership and the postcharge target -/





























/-! ## Exact local discrepancy ledger -/





/-- Exact guard-local ledger.  It is purely the identity
`raw row = surviving row ⊔ deleted row` together with the definition of
the postcharge quota. -/
theorem roughCanonicalGuardLocalDiscrepancyLedger
    {c : ℝ} {depth n h : ℕ} {left right : ℕ → ℕ}
    {changed : Finset ℕ}
    (R : BankPaperRealization n (upperEndpoint n h))
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (deltaStar : ℝ) (K label : ℕ) (x : ℕ → ℝ) :
    R.roughCanonicalPostchargeRowDiscrepancy certificate deltaStar
        K label x -
      roughCanonicalRawRowDiscrepancy n h K label x =
      -(completeLabelMultiplicity (yNat n)
          (R.paperFixedExceptionalFactors deltaStar) label : ℝ) -
        (completeLabelMultiplicity (yNat n)
          R.prechargeBaseState label : ℝ) +
        ∑ a ∈ R.roughCanonicalGuardDeletedRow certificate deltaStar
          K label, x a := by
  rw [roughCanonicalPostchargeRowDiscrepancy,
    roughCanonicalRawRowDiscrepancy,
    roughCanonicalPostchargeRowTarget,
    ← R.sum_roughCanonicalGuardedRow_add_sum_guardDeletedRow
      certificate deltaStar K label x]
  ring

/-! ## Exact support reduction for the local deletion set -/

/-- Fixed exceptional factors cannot themselves be raw lower candidates. -/
theorem roughRawCandidateSet_disjoint_paperFixedExceptionalFactors
    {n h K : ℕ}
    (R : BankPaperRealization n (upperEndpoint n h))
    (deltaStar : ℝ) :
    Disjoint (roughRawCandidateSet n h K)
      (R.paperFixedExceptionalFactors deltaStar) := by
  exact (roughUpperBlock_disjoint_rawCandidateSet n h K).symm.mono
    (by rfl) (R.paperFixedExceptionalFactors_subset_upperBlock deltaStar)

/-- Actual donors also lie strictly above every raw lower candidate. -/
theorem roughRawCandidateSet_disjoint_prechargeDonorSet
    {n h K : ℕ}
    (R : BankPaperRealization n (upperEndpoint n h)) :
    Disjoint (roughRawCandidateSet n h K) R.prechargeDonorSet := by
  have hdonor : R.prechargeDonorSet ⊆ roughUpperBlock n h := by
    simpa only [roughUpperBlock, upperEndpoint] using
      R.prechargeDonorSet_subset_tail
  exact (roughUpperBlock_disjoint_rawCandidateSet n h K).symm.mono
    (by rfl) hdonor

/-- Consequently, the only guard families which can delete a raw lower
coordinate are anchors and the two bank endpoint states.  This is a support
statement, not the still-missing per-row cardinality census. -/
theorem roughCanonicalGuardDeletedRow_subset_anchors_union_bankStates
    {c : ℝ} {depth n h : ℕ} {left right : ℕ → ℕ}
    {changed : Finset ℕ}
    (R : BankPaperRealization n (upperEndpoint n h))
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (deltaStar : ℝ) (K label : ℕ) :
    R.roughCanonicalGuardDeletedRow certificate deltaStar K label ⊆
      certificate.anchors ∪ R.prechargeBaseState ∪
        R.prechargeAlternateState := by
  intro a ha
  have haData := Finset.mem_inter.mp ha
  have haRaw := (mem_completeRoughRowFiber.mp haData.1).1
  have haGuard := haData.2
  simp only [roughCanonicalGuardSet, tangentPaperNumericalGuardSet,
    Finset.mem_union] at haGuard
  simp only [Finset.mem_union]
  rcases haGuard with (((haAnchor | haFixed) | haDonor) | haBase) | haAlt
  · exact Or.inl (Or.inl haAnchor)
  · exact ((Finset.disjoint_left.mp
      (R.roughRawCandidateSet_disjoint_paperFixedExceptionalFactors
        deltaStar)) haRaw haFixed).elim
  · exact ((Finset.disjoint_left.mp
      (R.roughRawCandidateSet_disjoint_prechargeDonorSet
        (K := K))) haRaw haDonor).elim
  · exact Or.inl (Or.inr haBase)
  · exact Or.inr haAlt

/-! ## Explicit remaining finite/analytic obligations -/







end BankPaperRealization

end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankPaperCanonicalGuardCapacityReduction -/
section


/-!
# Canonical rough-row guard capacity reduction

This file closes the finite part of the three guard-local obligations exposed
by `BankPaperCanonicalGuardLocalRowLedger`.

For every non-smooth complete rough row, at most one central anchor, one bank
base, and one bank alternate can occur.  Thus the literal local guard census
is at most three.  Removing those three possible coordinates from a raw broad
pool gives the guarded-pool capacity, and containment of the guarded broad
pool in the guarded row gives the postcharge capacity.

The only non-finite input left visible is `RoughCanonicalActiveRawBroadSurplus`:
the raw broad pool must contain the larger of the requested pool minimum and
the literal upper-row target, plus the three-coordinate guard slack.  This is
the exact de Bruijn--Saias lower-bound consequence still needed from the
analytic rough-row argument; it contains no selector or bookkeeping premise.
-/

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel

noncomputable section

/-! ## Complete rough labels remember retained prime divisors -/

/-- A prime divisor above the smooth cutoff is retained in the complete
rough label. -/
theorem prime_dvd_completeRoughLabel_of_cutoff_lt
    {y a p : Nat} (hp : p.Prime) (hyp : y < p)
    (ha : a ≠ 0) (hpa : p ∣ a) :
    p ∣ completeRoughLabel y a := by
  apply (hp.dvd_iff_one_le_factorization
    (completeRoughLabel_ne_zero y a)).mpr
  rw [completeRoughLabel_factorization_apply, if_pos hyp]
  exact (hp.dvd_iff_one_le_factorization ha).mp hpa



/-! ## One central anchor in every non-smooth row -/



/-- Consequently, one fixed non-smooth rough row meets the guarded central
anchor set in at most one coordinate. -/
theorem completeRoughRowFiber_inter_guardedCentralAnchors_card_le_one
    {c : Real} {depth n y : Nat} {left right : Nat -> Nat}
    {changed candidates : Finset Nat}
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (hnCutoff : centralAnchorCutoffThreshold depth <= n)
    (hyTwo : 2 <= y)
    (hyCutoff : y < centralAnchorCutoff depth n)
    (label : Nat) (hlabel : label ≠ 1) :
    (completeRoughRowFiber y candidates label ∩
      certificate.anchors).card <= 1 := by
  rw [Finset.card_le_one_iff]
  intro a b ha hb
  have haData := Finset.mem_inter.mp ha
  have hbData := Finset.mem_inter.mp hb
  have haLabel := (mem_completeRoughRowFiber.mp haData.1).2
  have hbLabel := (mem_completeRoughRowFiber.mp hbData.1).2
  apply fullCentralAnchors_completeRoughLabel_injective_of_ne_one
    hnCutoff hyTwo hyCutoff certificate.isCofactorChoice
  · simpa only [certificate.anchors_eq] using haData.2
  · simpa only [certificate.anchors_eq] using hbData.2
  · simpa only [haLabel] using hlabel
  · rw [haLabel, hbLabel]

namespace BankPaperRealization

/-! ## One base and one alternate in every bank row -/

/-- The global bank marker is prime. -/
theorem paperMarker_prime
    {n M : Nat} (R : BankPaperRealization n M)
    (request : BankPaperMarkerRequest n) :
    (R.marker request).Prime := by
  cases request with
  | inl request =>
      exact R.bottom.marker_prime
        (bankBottomRelevantRequestToPaperRequest request)
  | inr request => exact R.ordinary.marker_prime request

/-- Every global bank marker lies above the complete rough cutoff. -/
theorem yNat_lt_paperMarker
    {n M : Nat} (R : BankPaperRealization n M)
    (request : BankPaperMarkerRequest n) :
    yNat n < R.marker request := by
  cases request with
  | inl request =>
      exact R.bottom.yNat_lt_marker R.ordinary.two_mul_n_le_M
        R.three_mul_yNat_le_n
        (bankBottomRelevantRequestToPaperRequest request)
  | inr request => exact R.ordinary.yNat_lt_marker request

/-- The actual donor has the same complete rough signature as its global
marker. -/
theorem prechargeDonor_completeRoughSignature_eq_marker
    {n M : Nat} (R : BankPaperRealization n M)
    (request : BankPaperMarkerRequest n) :
    completeRoughSignature (yNat n) (R.prechargeDonorValue request) =
      completeRoughSignature (yNat n) (R.marker request) := by
  cases request with
  | inl request =>
      let fullRequest := bankBottomRelevantRequestToPaperRequest request
      simpa only [prechargeDonorValue, marker, fullRequest,
        BankBottomPaperRealization.occurrenceValue_donor] using
        (R.bottom.occurrenceValue_completeRoughSignature R.six_le_yNat
          fullRequest .donor)
  | inr request =>
      have hsignature := completeRoughSignature_marker_mul_smooth_eq
        (y := yNat n) (P := R.ordinary.marker request)
        (a := R.ordinary.donorCore request) (b := 1)
        (R.ordinary.marker_prime request).ne_zero
        (R.ordinary.donorCore_smooth request)
        (by simp [Nat.mem_smoothNumbers])
      simpa only [prechargeDonorValue, marker,
        BankOrdinaryPaperRealization.donorValue, mul_one] using hsignature

theorem prechargeBase_completeRoughSignature_eq_marker
    {n M : Nat} (R : BankPaperRealization n M)
    (request : BankPaperMarkerRequest n) :
    completeRoughSignature (yNat n)
        (R.prechargeBaseStateValue request) =
      completeRoughSignature (yNat n) (R.marker request) := by
  exact (R.prechargeBase_donor_completeRoughSignature_eq request).trans
    (R.prechargeDonor_completeRoughSignature_eq_marker request)

theorem prechargeAlternate_completeRoughSignature_eq_marker
    {n M : Nat} (R : BankPaperRealization n M)
    (request : BankPaperMarkerRequest n) :
    completeRoughSignature (yNat n)
        (R.prechargeAlternateStateValue request) =
      completeRoughSignature (yNat n) (R.marker request) := by
  exact (R.precharge_completeRoughSignature_eq request).2.trans
    (R.prechargeDonor_completeRoughSignature_eq_marker request)

/-- A prime above the cutoff is its own complete rough label. -/
theorem completeRoughLabel_paperMarker
    {n M : Nat} (R : BankPaperRealization n M)
    (request : BankPaperMarkerRequest n) :
    completeRoughLabel (yNat n) (R.marker request) = R.marker request := by
  have hprime := R.paperMarker_prime request
  have hhigh := R.yNat_lt_paperMarker request
  apply Nat.dvd_antisymm
  · exact completeRoughLabel_dvd (yNat n) (R.marker request)
  · exact prime_dvd_completeRoughLabel_of_cutoff_lt hprime hhigh
      hprime.ne_zero (dvd_refl (R.marker request))

theorem prechargeBase_completeRoughLabel_eq_marker
    {n M : Nat} (R : BankPaperRealization n M)
    (request : BankPaperMarkerRequest n) :
    completeRoughLabel (yNat n) (R.prechargeBaseStateValue request) =
      R.marker request := by
  calc
    completeRoughLabel (yNat n) (R.prechargeBaseStateValue request) =
        completeRoughLabel (yNat n) (R.marker request) :=
      completeRoughSignature_eq_iff_label_eq.mp
        (R.prechargeBase_completeRoughSignature_eq_marker request)
    _ = R.marker request := R.completeRoughLabel_paperMarker request

theorem prechargeAlternate_completeRoughLabel_eq_marker
    {n M : Nat} (R : BankPaperRealization n M)
    (request : BankPaperMarkerRequest n) :
    completeRoughLabel (yNat n)
        (R.prechargeAlternateStateValue request) = R.marker request := by
  calc
    completeRoughLabel (yNat n)
        (R.prechargeAlternateStateValue request) =
        completeRoughLabel (yNat n) (R.marker request) :=
      completeRoughSignature_eq_iff_label_eq.mp
        (R.prechargeAlternate_completeRoughSignature_eq_marker request)
    _ = R.marker request := R.completeRoughLabel_paperMarker request

theorem prechargeBase_completeRoughLabel_injective
    {n M : Nat} (R : BankPaperRealization n M) :
    Function.Injective (fun request : BankPaperMarkerRequest n =>
      completeRoughLabel (yNat n) (R.prechargeBaseStateValue request)) := by
  intro request request' heq
  apply R.marker_injective
  change
    completeRoughLabel (yNat n) (R.prechargeBaseStateValue request) =
      completeRoughLabel (yNat n)
        (R.prechargeBaseStateValue request') at heq
  simpa only [R.prechargeBase_completeRoughLabel_eq_marker] using heq

theorem prechargeAlternate_completeRoughLabel_injective
    {n M : Nat} (R : BankPaperRealization n M) :
    Function.Injective (fun request : BankPaperMarkerRequest n =>
      completeRoughLabel (yNat n)
        (R.prechargeAlternateStateValue request)) := by
  intro request request' heq
  apply R.marker_injective
  change
    completeRoughLabel (yNat n)
        (R.prechargeAlternateStateValue request) =
      completeRoughLabel (yNat n)
        (R.prechargeAlternateStateValue request') at heq
  simpa only [R.prechargeAlternate_completeRoughLabel_eq_marker] using heq

private theorem completeRoughRowFiber_inter_indexedPathState_card_le_one
    {C : Type*} [Fintype C] [DecidableEq C]
    {y label : Nat} {candidates : Finset Nat} (state : C -> Nat)
    (hinjective : Function.Injective
      (fun component => completeRoughLabel y (state component))) :
    (completeRoughRowFiber y candidates label ∩
      indexedPathState state).card <= 1 := by
  rw [Finset.card_le_one_iff]
  intro a b ha hb
  have haData := Finset.mem_inter.mp ha
  have hbData := Finset.mem_inter.mp hb
  have haLabel := (mem_completeRoughRowFiber.mp haData.1).2
  have hbLabel := (mem_completeRoughRowFiber.mp hbData.1).2
  rw [indexedPathState, Finset.mem_image] at haData hbData
  obtain ⟨component, _hcomponent, rfl⟩ := haData.2
  obtain ⟨component', _hcomponent', rfl⟩ := hbData.2
  apply congrArg state
  apply hinjective
  change completeRoughLabel y (state component) =
    completeRoughLabel y (state component')
  rw [haLabel, hbLabel]

theorem completeRoughRowFiber_inter_prechargeBaseState_card_le_one
    {n M label : Nat} (R : BankPaperRealization n M)
    (candidates : Finset Nat) :
    (completeRoughRowFiber (yNat n) candidates label ∩
      R.prechargeBaseState).card <= 1 := by
  classical
  rw [prechargeBaseState]
  exact completeRoughRowFiber_inter_indexedPathState_card_le_one
    R.prechargeBaseStateValue
    R.prechargeBase_completeRoughLabel_injective

theorem completeRoughRowFiber_inter_prechargeAlternateState_card_le_one
    {n M label : Nat} (R : BankPaperRealization n M)
    (candidates : Finset Nat) :
    (completeRoughRowFiber (yNat n) candidates label ∩
      R.prechargeAlternateState).card <= 1 := by
  classical
  rw [prechargeAlternateState]
  exact completeRoughRowFiber_inter_indexedPathState_card_le_one
    R.prechargeAlternateStateValue
    R.prechargeAlternate_completeRoughLabel_injective

/-! ## The literal three-coordinate local census -/

/-- In every non-smooth complete rough row, the numerical guards delete at
most one anchor, one bank base, and one bank alternate.  Fixed exceptional
factors and donors are in the upper tail and were already removed by the
support theorem in the local ledger. -/
theorem roughCanonicalGuardLocalCensusBound_three_of_ne_one
    {c : Real} {depth n h : Nat} {left right : Nat -> Nat}
    {changed : Finset Nat}
    (R : BankPaperRealization n (upperEndpoint n h))
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (deltaStar : Real) (K label : Nat)
    (hnCutoff : centralAnchorCutoffThreshold depth <= n)
    (hyCutoff : yNat n < centralAnchorCutoff depth n)
    (hlabel : label ≠ 1) :
    RoughCanonicalGuardLocalCensusBound R certificate deltaStar K label 3 := by
  let rawRow := completeRoughRowFiber (yNat n)
    (roughRawCandidateSet n h K) label
  have hsubset :
      R.roughCanonicalGuardDeletedRow certificate deltaStar K label ⊆
        (rawRow ∩ certificate.anchors) ∪
          (rawRow ∩ R.prechargeBaseState) ∪
            (rawRow ∩ R.prechargeAlternateState) := by
    intro a ha
    have haDeleted := ha
    change a ∈ rawRow ∩
      R.roughCanonicalGuardSet certificate deltaStar at haDeleted
    have haRaw : a ∈ rawRow := by
      exact (Finset.mem_inter.mp haDeleted).1
    have haSupport :=
      R.roughCanonicalGuardDeletedRow_subset_anchors_union_bankStates
        certificate deltaStar K label ha
    rcases Finset.mem_union.mp haSupport with haBefore | haAlternate
    · rcases Finset.mem_union.mp haBefore with haAnchor | haBase
      · exact Finset.mem_union.mpr <| Or.inl <|
          Finset.mem_union.mpr <| Or.inl <|
            Finset.mem_inter.mpr ⟨haRaw, haAnchor⟩
      · exact Finset.mem_union.mpr <| Or.inl <|
          Finset.mem_union.mpr <| Or.inr <|
            Finset.mem_inter.mpr ⟨haRaw, haBase⟩
    · exact Finset.mem_union.mpr <| Or.inr <|
        Finset.mem_inter.mpr ⟨haRaw, haAlternate⟩
  have hanchor : (rawRow ∩ certificate.anchors).card <= 1 := by
    have hyTwo : 2 <= yNat n := by
      have hySix := R.six_le_yNat
      omega
    exact completeRoughRowFiber_inter_guardedCentralAnchors_card_le_one
      certificate hnCutoff hyTwo hyCutoff label hlabel
  have hbase : (rawRow ∩ R.prechargeBaseState).card <= 1 := by
    exact R.completeRoughRowFiber_inter_prechargeBaseState_card_le_one
      (roughRawCandidateSet n h K)
  have halternate :
      (rawRow ∩ R.prechargeAlternateState).card <= 1 := by
    exact R.completeRoughRowFiber_inter_prechargeAlternateState_card_le_one
      (roughRawCandidateSet n h K)
  have hfirst := Finset.card_union_le
    (rawRow ∩ certificate.anchors) (rawRow ∩ R.prechargeBaseState)
  have hall := Finset.card_union_le
    ((rawRow ∩ certificate.anchors) ∪
      (rawRow ∩ R.prechargeBaseState))
    (rawRow ∩ R.prechargeAlternateState)
  have hcard := Finset.card_le_card hsubset
  exact show
    (R.roughCanonicalGuardDeletedRow certificate deltaStar K label).card <= 3
    by omega

/-- Active nonexceptional rows are non-smooth, so the preceding census
directly supplies the first Section 9 guard-local input. -/
theorem roughCanonicalGuardLocalCensusBound_three_of_active
    {c : Real} {depth n h : Nat} {left right : Nat -> Nat}
    {changed : Finset Nat}
    (R : BankPaperRealization n (upperEndpoint n h))
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (deltaStar : Real) (K label : Nat)
    (hnCutoff : centralAnchorCutoffThreshold depth <= n)
    (hyCutoff : yNat n < centralAnchorCutoff depth n)
    (hactive : RoughCanonicalActiveNonexceptionalLabel n deltaStar label) :
    RoughCanonicalGuardLocalCensusBound R certificate deltaStar K label 3 :=
  R.roughCanonicalGuardLocalCensusBound_three_of_ne_one certificate
    deltaStar K label hnCutoff hyCutoff hactive.1

/-! ## Guarded broad-pool and postcharge capacities -/







/-! ## The single remaining analytic raw-pool input -/





end BankPaperRealization

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

/- Source module: Erdos390.WholePaper.BankPaperCanonicalNonsmoothSlackClosure -/
section


/-!
# Canonical nonsmooth endpoint-slack closure

This module connects the sharp balanced raw-row estimate to the literal
guarded constant-pool correction used at the actual Proposition 8.7
endpoint.

There are two finite guard estimates.  The sharp one assumes the usual
raw-point box and proves that passing through all numerical guards changes
one active row discrepancy by at most `2`.  The assumption-free one uses
the already proved uniform absolute bound for the balanced coefficient and
gives a fixed (slightly larger) numerator constant.  The latter is the
version used in the eventual theorem, so no unproved eventual feasibility
of `roughHeadBalancedAlpha` is hidden in the endpoint-slack conclusion.

The final bounds use the paper split

`beta = betaProt + betaAct`, `0 < betaAct`, `sigma <= betaProt`.

Thus the lower nonsmooth margin has the fixed strict reserve `betaAct/L`.
The upper margin follows once `L` exceeds the fixed sum of the parameters.
-/

namespace Erdos390.WholePaper

open Erdos390.Full.Scale
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.PaperBridgeFit
open Filter Topology
open scoped BigOperators

noncomputable section

namespace BankPaperRealization

/-! ## Active rows contain no fixed exceptional factor -/

/-- A fixed exceptional factor has the strict exceptional inequality, so
its complete-row multiplicity vanishes on an active nonexceptional row. -/
theorem paperFixedExceptionalFactors_completeLabelMultiplicity_eq_zero_of_active
    {n h : Nat}
    (R : BankPaperRealization n (upperEndpoint n h))
    (deltaStar : Real) (label : Nat)
    (hactive : RoughCanonicalActiveNonexceptionalLabel n deltaStar label) :
    completeLabelMultiplicity (yNat n)
      (R.paperFixedExceptionalFactors deltaStar) label = 0 := by
  unfold completeLabelMultiplicity
  apply Finset.card_eq_zero.mpr
  apply Finset.filter_eq_empty_iff.mpr
  intro a haFixed haLabel
  have haData := (R.mem_paperFixedExceptionalFactors (a := a)).mp haFixed
  have hexceptional :
      2 * (n : Real) / (label : Real) < (n : Real) ^ deltaStar := by
    simpa only [haLabel] using haData.2.1
  exact (not_lt_of_ge hactive.2) hexceptional

/-- Injectivity of the base marker map gives at most one bank base in each
complete rough row. -/
theorem prechargeBaseState_completeLabelMultiplicity_le_one
    {n M label : Nat} (R : BankPaperRealization n M) :
    completeLabelMultiplicity (yNat n) R.prechargeBaseState label <= 1 := by
  have hcard :=
    R.completeRoughRowFiber_inter_prechargeBaseState_card_le_one
      (label := label) R.prechargeBaseState
  change
    ((R.prechargeBaseState.filter
        (fun a => completeRoughLabel (yNat n) a = label)) ∩
      R.prechargeBaseState).card <= 1 at hcard
  rw [Finset.inter_eq_left.mpr (Finset.filter_subset _ _)] at hcard
  simpa only [completeLabelMultiplicity] using hcard





/-! ## The sharp finite `+2` guard numerator -/



/-! ## An assumption-free fixed guard numerator -/



theorem roughCanonicalBalancedRawWeightGuardBound_nonneg
    (W K0 : Nat) {c beta : Real} (hc : 0 < c) :
    0 <= roughCanonicalBalancedRawWeightGuardBound W K0 c beta := by
  unfold roughCanonicalBalancedRawWeightGuardBound
  exact add_nonneg
    (roughBalancedAlphaConstant_nonneg W K0 (beta := beta) hc)
    (abs_nonneg beta)

/-- The raw weight is bounded without assuming that the balanced high level
already lies in `[0,1]`. -/
theorem roughHeadCompatibleBalancedRawWeight_abs_le_guardBound
    (W K0 n : Nat) {c beta : Real} (hc : 0 < c)
    (hn : 2 <= n) (hL : 1 <= L n) (a : Nat) :
    |roughHeadCompatibleRawWeight W n (upperTailLength c n) (K0 + 1)
        (roughHeadBalancedAlpha W n (upperTailLength c n) (K0 + 1)
          beta (L n))
        beta (L n) a| <=
      roughCanonicalBalancedRawWeightGuardBound W K0 c beta := by
  let alpha :=
    roughHeadBalancedAlpha W n (upperTailLength c n) (K0 + 1)
      beta (L n)
  change
    |roughHeadCompatibleRawWeight W n (upperTailLength c n) (K0 + 1)
        alpha beta (L n) a| <=
      roughCanonicalBalancedRawWeightGuardBound W K0 c beta
  have halpha :
      |alpha| <= roughBalancedAlphaConstant W K0 c beta := by
    simpa only [alpha, roughBalancedAlphaConstant] using
      roughHeadBalancedAlpha_succ_abs_le W K0 (beta := beta) hc hn
  have hLPos : 0 < L n := zero_lt_one.trans_le hL
  have hbetaDiv : |beta / L n| <= |beta| := by
    rw [abs_div, abs_of_pos hLPos]
    apply (div_le_iff₀ hLPos).2
    nlinarith [abs_nonneg beta]
  by_cases hcop : Nat.Coprime a (roughHeadModulus W)
  · by_cases hhigh : a ∈
        roughHighLowerBlock n (upperTailLength c n) (K0 + 1)
    · have hbroad : a ∉
          roughBroadLowerBlock n (upperTailLength c n) (K0 + 1) := by
        intro hbroad
        exact Finset.disjoint_left.mp
          (roughHighLowerBlock_disjoint_roughBroadLowerBlock
            n (upperTailLength c n) (K0 + 1)) hhigh hbroad
      have hweight :
          roughHeadCompatibleRawWeight W n (upperTailLength c n) (K0 + 1)
              alpha beta (L n) a = alpha := by
        simp [roughHeadCompatibleRawWeight, roughFiniteIndicator,
          hcop, hhigh, hbroad]
      rw [hweight]
      unfold roughCanonicalBalancedRawWeightGuardBound
      exact halpha.trans (le_add_of_nonneg_right (abs_nonneg beta))
    · by_cases hbroad : a ∈
          roughBroadLowerBlock n (upperTailLength c n) (K0 + 1)
      · have hweight :
            roughHeadCompatibleRawWeight W n (upperTailLength c n) (K0 + 1)
                alpha beta (L n) a = beta / L n := by
          simp [roughHeadCompatibleRawWeight, roughFiniteIndicator,
            hcop, hhigh, hbroad]
        rw [hweight]
        unfold roughCanonicalBalancedRawWeightGuardBound
        exact hbetaDiv.trans
          (le_add_of_nonneg_left
            (roughBalancedAlphaConstant_nonneg W K0 (beta := beta) hc))
      · simp [roughHeadCompatibleRawWeight, roughFiniteIndicator,
          hhigh, hbroad,
          roughCanonicalBalancedRawWeightGuardBound_nonneg
            W K0 (beta := beta) hc]
  · simp [roughHeadCompatibleRawWeight, hcop,
      roughCanonicalBalancedRawWeightGuardBound_nonneg
        W K0 (beta := beta) hc]



theorem roughCanonicalBalancedGuardNumeratorConstant_pos
    (W K0 : Nat) {c beta : Real} (hc : 0 < c) :
    0 < roughCanonicalBalancedGuardNumeratorConstant W K0 c beta := by
  unfold roughCanonicalBalancedGuardNumeratorConstant
  have hbound :=
    roughCanonicalBalancedRawWeightGuardBound_nonneg
      W K0 (beta := beta) hc
  positivity

/-- With only an absolute coordinate bound `M`, the active guard ledger has
fixed size `1+3M`: one possible base token and at most three deleted
coordinates. -/
theorem roughCanonicalGuardLocalDiscrepancyIncrement_abs_le_fixed
    {c : Real} {depth n h K label : Nat}
    {left right : Nat -> Nat} {changed : Finset Nat}
    (R : BankPaperRealization n (upperEndpoint n h))
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (deltaStar M : Real) (x : Nat -> Real)
    (hnCutoff : centralAnchorCutoffThreshold depth <= n)
    (hyCutoff : yNat n < centralAnchorCutoff depth n)
    (hactive : RoughCanonicalActiveNonexceptionalLabel n deltaStar label)
    (hM : 0 <= M)
    (hx : ∀ a ∈ completeRoughRowFiber (yNat n)
        (roughRawCandidateSet n h K) label, |x a| <= M) :
    |R.roughCanonicalPostchargeRowDiscrepancy certificate deltaStar
        K label x -
      roughCanonicalRawRowDiscrepancy n h K label x| <= 1 + 3 * M := by
  let D :=
    R.roughCanonicalGuardDeletedRow certificate deltaStar K label
  let m :=
    completeLabelMultiplicity (yNat n) R.prechargeBaseState label
  have hfixed :=
    R.paperFixedExceptionalFactors_completeLabelMultiplicity_eq_zero_of_active
      deltaStar label hactive
  have hmLeNat : m <= 1 := by
    dsimp only [m]
    exact
      R.prechargeBaseState_completeLabelMultiplicity_le_one
        (label := label)
  have hmLe : (m : Real) <= 1 := by exact_mod_cast hmLeNat
  have hcensus :
      RoughCanonicalGuardLocalCensusBound R certificate deltaStar
        K label 3 :=
    R.roughCanonicalGuardLocalCensusBound_three_of_active certificate
      deltaStar K label hnCutoff hyCutoff hactive
  have hcensusNat : D.card <= 3 := by
    simpa only [D, RoughCanonicalGuardLocalCensusBound] using hcensus
  have hcensusReal : (D.card : Real) <= 3 := by
    exact_mod_cast hcensusNat
  have hsumAbs : |∑ a ∈ D, x a| <= 3 * M := by
    calc
      |∑ a ∈ D, x a| <= ∑ a ∈ D, |x a| :=
        Finset.abs_sum_le_sum_abs _ _
      _ <= ∑ _a ∈ D, M := by
        exact Finset.sum_le_sum fun a ha =>
          hx a (Finset.mem_inter.mp ha).1
      _ = (D.card : Real) * M := by simp
      _ <= 3 * M := mul_le_mul_of_nonneg_right hcensusReal hM
  have hledger :=
    R.roughCanonicalGuardLocalDiscrepancyLedger certificate deltaStar
      K label x
  rw [hfixed, Nat.cast_zero, neg_zero, zero_sub] at hledger
  rw [hledger]
  calc
    |-(m : Real) + ∑ a ∈ D, x a| <=
        |-(m : Real)| + |∑ a ∈ D, x a| := abs_add_le _ _
    _ = (m : Real) + |∑ a ∈ D, x a| := by
      rw [abs_neg, abs_of_nonneg (Nat.cast_nonneg m)]
    _ <= 1 + 3 * M := add_le_add hmLe hsumAbs

end BankPaperRealization

/-! ## Eventual sharp raw-row estimate on every active canonical row -/









namespace BankPaperRealization

/-! ## From the raw numerator to the guarded correction density -/

/-- The guarded correction density is literally the postcharge discrepancy
divided by the guarded broad-pool cardinality. -/
theorem roughCanonicalGuardedPostchargeCorrectionDensity_eq_discrepancy_div
    {c : Real} {depth n W K label : Nat}
    (R : BankPaperRealization n
      (upperEndpoint n (upperTailLength c n)))
    (certificate : GuardedCentralAnchorCertificate c depth n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (deltaStar alpha beta ell : Real) :
    R.roughCanonicalGuardedPostchargeCorrectionDensity certificate
        deltaStar W K label alpha beta ell =
      R.roughCanonicalPostchargeRowDiscrepancy certificate deltaStar
          K label
          (roughHeadCompatibleRawWeight W n (upperTailLength c n) K
            alpha beta ell) /
        ((R.roughCanonicalGuardedBroadCorrectionPool certificate deltaStar
          W K label).card : Real) := by
  rfl

/-- The raw discrepancy notation in the guard ledger is the same quantity
as the Saias-facing quota error. -/
theorem roughCanonicalRawRowDiscrepancy_eq_quotaError
    (W n h K : Nat) (alpha beta ell : Real)
    (row : CanonicalCompleteRoughRow (yNat n)
      (roughRawCandidateSet n h K)) :
    roughCanonicalRawRowDiscrepancy n h K row.1
        (roughHeadCompatibleRawWeight W n h K alpha beta ell) =
      roughCanonicalRawRowQuotaError W n h K (yNat n)
        alpha beta ell row := by
  rw [roughCanonicalRawRowDiscrepancy,
    roughCanonicalRawRowQuotaError_eq_target_sub_rawRowMass]
  rfl

/-- Assumption-free balanced postcharge numerator bound: the sharp raw
quota error plus one fixed guard constant. -/
theorem roughCanonicalBalancedPostchargeRowDiscrepancy_abs_le_raw_add_guard
    {c deltaStar beta : Real} {depth n W K0 : Nat}
    (R : BankPaperRealization n
      (upperEndpoint n (upperTailLength c n)))
    (certificate : GuardedCentralAnchorCertificate c depth n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (row : CanonicalCompleteRoughRow (yNat n)
      (roughRawCandidateSet n (upperTailLength c n) (K0 + 1)))
    (hc : 0 < c) (hn : 2 <= n) (hL : 1 <= L n)
    (hnCutoff : centralAnchorCutoffThreshold depth <= n)
    (hyCutoff : yNat n < centralAnchorCutoff depth n)
    (hactive :
      RoughCanonicalActiveNonexceptionalLabel n deltaStar row.1) :
    |R.roughCanonicalPostchargeRowDiscrepancy certificate deltaStar
        (K0 + 1) row.1
        (roughHeadCompatibleRawWeight W n (upperTailLength c n) (K0 + 1)
          (roughHeadBalancedAlpha W n (upperTailLength c n) (K0 + 1)
            beta (L n))
          beta (L n))| <=
      |roughCanonicalRawRowQuotaError W n (upperTailLength c n)
          (K0 + 1) (yNat n)
          (roughHeadBalancedAlpha W n (upperTailLength c n) (K0 + 1)
            beta (L n))
          beta (L n) row| +
        roughCanonicalBalancedGuardNumeratorConstant W K0 c beta := by
  let x :=
    roughHeadCompatibleRawWeight W n (upperTailLength c n) (K0 + 1)
      (roughHeadBalancedAlpha W n (upperTailLength c n) (K0 + 1)
        beta (L n))
      beta (L n)
  let M := roughCanonicalBalancedRawWeightGuardBound W K0 c beta
  have hM : 0 <= M := by
    dsimp only [M]
    exact
      roughCanonicalBalancedRawWeightGuardBound_nonneg
        W K0 (beta := beta) hc
  have hx : ∀ a ∈ completeRoughRowFiber (yNat n)
      (roughRawCandidateSet n (upperTailLength c n) (K0 + 1)) row.1,
      |x a| <= M := by
    intro a _ha
    dsimp only [x, M]
    exact roughHeadCompatibleBalancedRawWeight_abs_le_guardBound
      W K0 n (beta := beta) hc hn hL a
  have hincrement :=
    R.roughCanonicalGuardLocalDiscrepancyIncrement_abs_le_fixed
      certificate deltaStar M x hnCutoff hyCutoff hactive hM hx
  have hraw :
      roughCanonicalRawRowDiscrepancy n (upperTailLength c n) (K0 + 1)
          row.1 x =
        roughCanonicalRawRowQuotaError W n (upperTailLength c n)
          (K0 + 1) (yNat n)
          (roughHeadBalancedAlpha W n (upperTailLength c n) (K0 + 1)
            beta (L n))
          beta (L n) row := by
    dsimp only [x]
    exact roughCanonicalRawRowDiscrepancy_eq_quotaError
      W n (upperTailLength c n) (K0 + 1)
        (roughHeadBalancedAlpha W n (upperTailLength c n) (K0 + 1)
          beta (L n))
        beta (L n) row
  have htriangle :
      |R.roughCanonicalPostchargeRowDiscrepancy certificate deltaStar
          (K0 + 1) row.1 x| <=
        |roughCanonicalRawRowDiscrepancy n (upperTailLength c n)
            (K0 + 1) row.1 x| +
          |R.roughCanonicalPostchargeRowDiscrepancy certificate deltaStar
              (K0 + 1) row.1 x -
            roughCanonicalRawRowDiscrepancy n (upperTailLength c n)
              (K0 + 1) row.1 x| := by
    have hadd := abs_add_le
      (roughCanonicalRawRowDiscrepancy n (upperTailLength c n)
        (K0 + 1) row.1 x)
      (R.roughCanonicalPostchargeRowDiscrepancy certificate deltaStar
          (K0 + 1) row.1 x -
        roughCanonicalRawRowDiscrepancy n (upperTailLength c n)
          (K0 + 1) row.1 x)
    convert hadd using 1; ring
  dsimp only [roughCanonicalBalancedGuardNumeratorConstant]
  have hbound :=
    htriangle.trans (add_le_add (le_refl _) hincrement)
  rw [hraw] at hbound
  exact hbound

/-- Removing at most three guarded coordinates from a raw pool of density
`d` retains half of that linear density as soon as `d*X >= 6`. -/
theorem roughCanonicalGuardedBroadCorrectionPool_linear_half_lower
    {c deltaStar d : Real} {depth n W K label : Nat}
    (R : BankPaperRealization n
      (upperEndpoint n (upperTailLength c n)))
    (certificate : GuardedCentralAnchorCertificate c depth n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (hnCutoff : centralAnchorCutoffThreshold depth <= n)
    (hyCutoff : yNat n < centralAnchorCutoff depth n)
    (hactive :
      RoughCanonicalActiveNonexceptionalLabel n deltaStar label)
    (hraw :
      d * ((n / label : Nat) : Real) <=
        (roughCanonicalBroadCorrectionPool W n (upperTailLength c n) K
          (yNat n) label).card)
    (hsix : 6 <= d * ((n / label : Nat) : Real)) :
    d / 2 * ((n / label : Nat) : Real) <=
      (R.roughCanonicalGuardedBroadCorrectionPool certificate deltaStar
        W K label).card := by
  let rawPool :=
    roughCanonicalBroadCorrectionPool W n (upperTailLength c n) K
      (yNat n) label
  let guard := R.roughCanonicalGuardSet certificate deltaStar
  have hinterSubset :
      guard ∩ rawPool ⊆
        R.roughCanonicalGuardDeletedRow certificate deltaStar K label := by
    intro a ha
    have haData := Finset.mem_inter.mp ha
    exact Finset.mem_inter.mpr
      ⟨roughCanonicalBroadCorrectionPool_subset_rawRow
        W n (upperTailLength c n) K (yNat n) label haData.2,
        haData.1⟩
  have hcensus :
      RoughCanonicalGuardLocalCensusBound R certificate deltaStar
        K label 3 :=
    R.roughCanonicalGuardLocalCensusBound_three_of_active certificate
      deltaStar K label hnCutoff hyCutoff hactive
  have hinterNat : (guard ∩ rawPool).card <= 3 :=
    (Finset.card_le_card hinterSubset).trans hcensus
  have hinter : ((guard ∩ rawPool).card : Real) <= 3 := by
    exact_mod_cast hinterNat
  have hinterRight : (guard ∩ rawPool).card <= rawPool.card :=
    Finset.card_le_card Finset.inter_subset_right
  have hcard :
      ((rawPool \ guard).card : Real) =
        (rawPool.card : Real) - ((guard ∩ rawPool).card : Real) := by
    rw [Finset.card_sdiff, Nat.cast_sub hinterRight]
  change
    d / 2 * ((n / label : Nat) : Real) <=
      ((rawPool \ guard).card : Real)
  rw [hcard]
  have hraw' :
      d * ((n / label : Nat) : Real) <= (rawPool.card : Real) := by
    simpa only [rawPool] using hraw
  linarith

/-- Pointwise analytic conversion from a unified raw-row numerator and a
linear raw broad-pool lower bound to the active reserve `betaAct/L`. -/
theorem roughCanonicalBalancedGuardedPostchargeCorrectionDensity_abs_le_reserve
    {c deltaStar beta betaAct C d G : Real}
    {depth n W K0 : Nat}
    (R : BankPaperRealization n
      (upperEndpoint n (upperTailLength c n)))
    (certificate : GuardedCentralAnchorCertificate c depth n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (row : CanonicalCompleteRoughRow (yNat n)
      (roughRawCandidateSet n (upperTailLength c n) (K0 + 1)))
    (hc : 0 < c) (hn : 2 <= n) (hLone : 1 <= L n)
    (hnCutoff : centralAnchorCutoffThreshold depth <= n)
    (hyCutoff : yNat n < centralAnchorCutoff depth n)
    (hactive :
      RoughCanonicalActiveNonexceptionalLabel n deltaStar row.1)
    (hd : 0 < d) (hbetaAct : 0 < betaAct)
    (_hC : 0 <= C)
    (hG :
      G = roughCanonicalBalancedGuardNumeratorConstant W K0 c beta)
    (hrawQuota :
      |roughCanonicalRawRowQuotaError W n (upperTailLength c n)
          (K0 + 1) (yNat n)
          (roughHeadBalancedAlpha W n (upperTailLength c n) (K0 + 1)
            beta (L n))
          beta (L n) row| <=
        3 * (C *
          ((((n / row.1 : Nat) : Real)) / L n ^ 2 + 1)))
    (hrawPool :
      d * ((n / row.1 : Nat) : Real) <=
        (roughCanonicalBroadCorrectionPool W n (upperTailLength c n)
          (K0 + 1) (yNat n) row.1).card)
    (hsix : 6 <= d * ((n / row.1 : Nat) : Real))
    (hfirst : 12 * C <= d * betaAct * L n)
    (hsecond :
      4 * (3 * C + G) * L n <=
        d * betaAct * ((n / row.1 : Nat) : Real)) :
    |R.roughCanonicalGuardedPostchargeCorrectionDensity certificate
        deltaStar W (K0 + 1) row.1
        (roughHeadBalancedAlpha W n (upperTailLength c n) (K0 + 1)
          beta (L n))
        beta (L n)| <= betaAct / L n := by
  let X : Real := ((n / row.1 : Nat) : Real)
  let pool :=
    R.roughCanonicalGuardedBroadCorrectionPool certificate deltaStar
      W (K0 + 1) row.1
  have hL : 0 < L n := zero_lt_one.trans_le hLone
  have hX : 0 < X := by
    by_contra hnot
    have hXle : X <= 0 := le_of_not_gt hnot
    have hdXle : d * X <= 0 :=
      mul_nonpos_of_nonneg_of_nonpos hd.le hXle
    dsimp only [X] at hsix hdXle
    linarith
  have hpoolLower :
      d / 2 * X <= (pool.card : Real) := by
    dsimp only [pool, X]
    exact R.roughCanonicalGuardedBroadCorrectionPool_linear_half_lower
      certificate hnCutoff hyCutoff hactive hrawPool hsix
  have hpoolPos : (0 : Real) < (pool.card : Real) :=
    (mul_pos (div_pos hd (by norm_num)) hX).trans_le hpoolLower
  have hpost :
      |R.roughCanonicalPostchargeRowDiscrepancy certificate deltaStar
          (K0 + 1) row.1
          (roughHeadCompatibleRawWeight W n (upperTailLength c n)
            (K0 + 1)
            (roughHeadBalancedAlpha W n (upperTailLength c n) (K0 + 1)
              beta (L n))
            beta (L n))| <=
        3 * (C * (X / L n ^ 2 + 1)) + G := by
    have hguard :=
      R.roughCanonicalBalancedPostchargeRowDiscrepancy_abs_le_raw_add_guard
        (W := W) (beta := beta)
        certificate row hc hn hLone hnCutoff hyCutoff hactive
    rw [← hG] at hguard
    exact hguard.trans (add_le_add (by
      simpa only [X] using hrawQuota) (le_refl G))
  have hmain :
      3 * C * (X / L n ^ 2) <=
        betaAct / L n * (d / 4 * X) := by
    have hfactor : 0 <= X / (4 * L n ^ 2) := by positivity
    have hmul := mul_le_mul_of_nonneg_right hfirst hfactor
    calc
      3 * C * (X / L n ^ 2) =
          (12 * C) * (X / (4 * L n ^ 2)) := by ring
      _ <= (d * betaAct * L n) * (X / (4 * L n ^ 2)) := hmul
      _ = betaAct / L n * (d / 4 * X) := by
        field_simp [hL.ne']
  have hconstant :
      3 * C + G <= betaAct / L n * (d / 4 * X) := by
    have hden : 0 < 4 * L n := mul_pos (by norm_num) hL
    rw [show betaAct / L n * (d / 4 * X) =
        (d * betaAct * X) / (4 * L n) by
      field_simp [hL.ne']]
    apply (le_div_iff₀ hden).2
    convert hsecond using 1; ring
  have hnumerator :
      3 * (C * (X / L n ^ 2 + 1)) + G <=
        betaAct / L n * (d / 2 * X) := by
    calc
      3 * (C * (X / L n ^ 2 + 1)) + G =
          3 * C * (X / L n ^ 2) + (3 * C + G) := by ring
      _ <= betaAct / L n * (d / 4 * X) +
          betaAct / L n * (d / 4 * X) :=
        add_le_add hmain hconstant
      _ = betaAct / L n * (d / 2 * X) := by ring
  rw [
    R.roughCanonicalGuardedPostchargeCorrectionDensity_eq_discrepancy_div
      (W := W) (K := K0 + 1) (label := row.1) certificate,
    abs_div, abs_of_pos hpoolPos]
  apply (div_le_iff₀ hpoolPos).2
  exact hpost.trans <| hnumerator.trans <|
    mul_le_mul_of_nonneg_left hpoolLower
      (div_nonneg hbetaAct.le hL.le)

/-! ## The eventual paper beta/sigma nonsmooth bounds -/













end BankPaperRealization

end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankPaperCanonicalGuardedPostchargeCorrectionRateClosure -/
section


/-!
# Paper-rate closure for the guarded postcharge correction

The raw nonsmooth correction already has the strict
`secondOrderScale / (p * L)` bound.  The implemented selector uses the same
row discrepancies after removing at most three guarded coordinates and
adding the fixed postcharge numerator shift.

The existing finite postcharge-density theorem is stronger than its usual
endpoint-slack specialization: its reserve parameter is only the requested
upper bound.  Taking that parameter to be a fixed constant divided by `L`
and using `L^2 = o(n^deltaStar)` gives a uniform guarded density
`O(1 / L^2)`.  The guarded pools are subsets of the raw pools, so the
existing global `4n/p` valuation census then gives the strict paper rate.

Finally, the guarded-minus-raw defect is bounded by the sum of the two
aggregate corrections.  This avoids imposing a separate cross-moment
estimate.
-/

open Filter Topology Asymptotics
open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.Scale

noncomputable section

namespace BankPaperRealization



theorem roughCanonicalUniformGuardedPostchargeCorrectionDensityConstant_pos
    (W K0 : Nat) {c beta : Real} (hc : 0 < c) :
    0 <
      roughCanonicalUniformGuardedPostchargeCorrectionDensityConstant
        W K0 c beta := by
  unfold roughCanonicalUniformGuardedPostchargeCorrectionDensityConstant
  have hC :=
    roughCanonicalSharpUnifiedRowScaleConstant_nonneg
      W K0 (beta := beta) hc
  have hG :=
    roughCanonicalBalancedGuardNumeratorConstant_pos
      W K0 (beta := beta) hc
  exact div_pos (mul_pos (by norm_num) (by positivity))
    (roughCanonicalRawBroadPoolDensity_pos W)

private theorem guardedPostchargeRate_L_sq_div_rpow_tendsto_zero
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

private theorem guardedPostchargeRate_rpow_tendsto_atTop
    {deltaStar : Real} (hdelta : 0 < deltaStar) :
    Tendsto (fun n : Nat => (n : Real) ^ deltaStar) atTop atTop := by
  exact (tendsto_rpow_atTop hdelta).comp tendsto_natCast_atTop_atTop

/-- The balanced guarded postcharge density has a uniform
`constant/(4 L^2)` bound on every active attained row. -/
theorem
    eventually_roughCanonicalUniformGuardedPostchargeCorrectionDensityBound
    (W K0 : Nat) {c beta deltaStar : Real}
    (hc : 0 < c) (hdelta : 0 < deltaStar) :
    ∀ᶠ n : Nat in atTop,
      forall (depth : Nat)
        (R : BankPaperRealization n
          (upperEndpoint n (upperTailLength c n)))
        (certificate : GuardedCentralAnchorCertificate c depth n
          R.anchorGuardLeftCore R.anchorGuardRightCore
          (R.centralChangedMarkers depth)),
      centralAnchorCutoffThreshold depth <= n ->
      yNat n < centralAnchorCutoff depth n ->
      ∀ label ∈ roughCanonicalActiveRawCorrectionLabels n
        (upperTailLength c n) (K0 + 1) deltaStar,
        abs
          (R.roughCanonicalGuardedPostchargeCorrectionDensity certificate
            deltaStar W (K0 + 1) label
            (roughHeadBalancedAlpha W n (upperTailLength c n)
              (K0 + 1) beta (L n))
            beta (L n)) <=
          roughCanonicalUniformGuardedPostchargeCorrectionDensityConstant
              W K0 c beta /
            (4 * L n ^ 2) := by
  let d := roughCanonicalRawBroadPoolDensity W
  let C := roughCanonicalSharpUnifiedRowScaleConstant W K0 c beta
  let G := roughCanonicalBalancedGuardNumeratorConstant W K0 c beta
  let D :=
    roughCanonicalUniformGuardedPostchargeCorrectionDensityConstant
      W K0 c beta
  have hd : 0 < d := by
    dsimp only [d]
    exact roughCanonicalRawBroadPoolDensity_pos W
  have hdensity_ne : roughCanonicalRawBroadPoolDensity W ≠ 0 :=
    (roughCanonicalRawBroadPoolDensity_pos W).ne'
  have hC : 0 <= C := by
    dsimp only [C]
    exact
      roughCanonicalSharpUnifiedRowScaleConstant_nonneg
        W K0 (beta := beta) hc
  have hG : 0 < G := by
    dsimp only [G]
    exact
      roughCanonicalBalancedGuardNumeratorConstant_pos
        W K0 (beta := beta) hc
  have hA : 0 < 3 * C + G := by positivity
  have hD : 0 < D := by
    dsimp only [D]
    exact
      roughCanonicalUniformGuardedPostchargeCorrectionDensityConstant_pos
        W K0 (beta := beta) hc
  have hraw :=
    Erdos390.WholePaper.eventually_roughCanonicalBalancedRawRowQuotaError_abs_le_unified_active
      W K0 (beta := beta) hc hdelta
  have hlinear :=
    eventually_roughCanonical_activeRawBroadPool_linear_lower
      W (K0 + 1) hc hdelta
  have hLOne : ∀ᶠ n : Nat in atTop, 1 <= L n := by
    have hLTop : Tendsto L atTop atTop := by
      simpa only [L] using
        Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
    exact hLTop.eventually (eventually_ge_atTop 1)
  have hratio : ∀ᶠ n : Nat in atTop,
      L n ^ 2 / (n : Real) ^ deltaStar < 1 / 4 :=
    (guardedPostchargeRate_L_sq_div_rpow_tendsto_zero hdelta).eventually
      (eventually_lt_nhds (by norm_num : (0 : Real) < 1 / 4))
  have hpower : ∀ᶠ n : Nat in atTop,
      max 4 (24 / d) <= (n : Real) ^ deltaStar :=
    (guardedPostchargeRate_rpow_tendsto_atTop hdelta).eventually
      (eventually_ge_atTop (max 4 (24 / d)))
  filter_upwards [eventually_ge_atTop 2, hraw, hlinear, hLOne,
      hratio, hpower]
      with n hn hrawN hlinearN hLone hratioN hpowerN
  intro depth R certificate hnCutoff hyCutoff label hlabel
  have hlabelParts :=
    mem_roughCanonicalActiveRawCorrectionLabels.mp hlabel
  let row : CanonicalCompleteRoughRow (yNat n)
      (roughRawCandidateSet n (upperTailLength c n) (K0 + 1)) :=
    ⟨label, hlabelParts.1⟩
  have hlabelData : IsCompleteRoughLabel (yNat n) label := by
    simpa only [row] using
      (isCompleteRoughLabel_of_canonicalCompleteRoughRow row)
  have hlabelPos : 0 < label := hlabelData.1
  have hnPos : 0 < n := by omega
  have hnReal : (0 : Real) < (n : Real) := by exact_mod_cast hnPos
  have hlabelReal : (0 : Real) < (label : Real) := by
    exact_mod_cast hlabelPos
  have hpowPos : (0 : Real) < (n : Real) ^ deltaStar :=
    Real.rpow_pos_of_pos hnReal deltaStar
  have hL : 0 < L n := zero_lt_one.trans_le hLone
  let X : Real := ((n / label : Nat) : Real)
  have hnatUpper :
      (n : Real) / (label : Real) < X + 1 := by
    apply (div_lt_iff₀ hlabelReal).2
    have hnat := (Nat.div_lt_iff_lt_mul hlabelPos).mp
      (Nat.lt_succ_self (n / label))
    dsimp only [X]
    exact_mod_cast hnat
  have hactiveHalf :
      (n : Real) ^ deltaStar / 2 <=
        (n : Real) / (label : Real) := by
    calc
      (n : Real) ^ deltaStar / 2 <=
          (2 * (n : Real) / (label : Real)) / 2 :=
        div_le_div_of_nonneg_right hlabelParts.2.2 (by norm_num)
      _ = (n : Real) / (label : Real) := by ring
  have hpowerFour : (4 : Real) <= (n : Real) ^ deltaStar :=
    (le_max_left 4 (24 / d)).trans hpowerN
  have hXlower :
      (n : Real) ^ deltaStar / 4 <= X := by
    have hhalfFour :
        (n : Real) ^ deltaStar / 4 <=
          (n : Real) ^ deltaStar / 2 - 1 := by
      linarith
    linarith
  have hLsq :
      L n ^ 2 <= X := by
    have hlogSmall :
        L n ^ 2 < (n : Real) ^ deltaStar / 4 := by
      have hcross := (div_lt_iff₀ hpowPos).mp hratioN
      nlinarith
    exact (hlogSmall.trans_le hXlower).le
  have hpowerDensity :
      24 / d <= (n : Real) ^ deltaStar :=
    (le_max_right 4 (24 / d)).trans hpowerN
  have hsix : 6 <= d * X := by
    have hcross := (div_le_iff₀ hd).mp hpowerDensity
    have hmul := mul_le_mul_of_nonneg_left hXlower hd.le
    nlinarith
  have hrawPool :
      d * X <=
        ((roughCanonicalBroadCorrectionPool W n
          (upperTailLength c n) (K0 + 1) (yNat n) label).card : Real) := by
    dsimp only [d, X]
    exact hlinearN label hlabelData hlabelParts.2
  have hrawQuota := hrawN row (by simpa only [row] using hlabelParts.2)
  let targetReserve : Real := D / (4 * L n)
  have htargetReserve : 0 < targetReserve := by
    dsimp only [targetReserve]
    exact div_pos hD (mul_pos (by norm_num) hL)
  have hfirst :
      12 * C <= d * targetReserve * L n := by
    have hbase : 12 * C <= 4 * (3 * C + G) := by
      nlinarith [hG.le]
    calc
      12 * C <= 4 * (3 * C + G) := hbase
      _ = d * targetReserve * L n := by
        dsimp only [targetReserve, D]
        unfold
          roughCanonicalUniformGuardedPostchargeCorrectionDensityConstant
        dsimp only [d, C, G]
        field_simp [hdensity_ne, hL.ne']
        ring
  have hsecond :
      4 * (3 * C + G) * L n <=
        d * targetReserve * X := by
    have hcoef : 0 <= 4 * (3 * C + G) / L n := by positivity
    calc
      4 * (3 * C + G) * L n =
          (4 * (3 * C + G) / L n) * L n ^ 2 := by
        field_simp [hL.ne']
      _ <= (4 * (3 * C + G) / L n) * X :=
        mul_le_mul_of_nonneg_left hLsq hcoef
      _ = d * targetReserve * X := by
        dsimp only [targetReserve, D]
        unfold
          roughCanonicalUniformGuardedPostchargeCorrectionDensityConstant
        dsimp only [d, C, G]
        field_simp [hdensity_ne, hL.ne']
        ring
  have hdensity :=
    R.roughCanonicalBalancedGuardedPostchargeCorrectionDensity_abs_le_reserve
      certificate row hc hn hLone hnCutoff hyCutoff hlabelParts.2
      hd htargetReserve hC (by rfl) hrawQuota
      (by simpa only [X] using hrawPool)
      (by simpa only [X] using hsix)
      hfirst hsecond
  have htarget :
      targetReserve / L n = D / (4 * L n ^ 2) := by
    dsimp only [targetReserve]
    field_simp [hL.ne']
  simpa only [row, D, htarget] using hdensity









end BankPaperRealization

end

end Erdos390.WholePaper

end

theorem solution : Erdos390.RemainingAnalyticGoal004_017 := by
  exact @Erdos390.WholePaper.BankPaperRealization.eventually_roughCanonicalUniformGuardedPostchargeCorrectionDensityBound
