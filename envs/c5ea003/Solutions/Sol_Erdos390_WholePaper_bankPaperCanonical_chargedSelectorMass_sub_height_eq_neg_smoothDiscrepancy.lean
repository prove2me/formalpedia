-- Prove2me | solution 1 for Erdos390.WholePaper.bankPaperCanonical_chargedSelectorMass_sub_height_eq_neg_smoothDiscrepancy
-- status  : ACCEPTED   (prove)
-- author  : @doctosil
-- created : 2026-09-17T16:02:51.429679+00:00
-- url     : https://prove2.me/submissions/b4d8e5b5-a23d-4668-bb0b-6399568e0122

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

/- Source module: Erdos390.WholePaper.CompleteRoughRowPartition -/
section


/-!
# The finite partition into complete rough rows

For a finite set `A`, its complete rough labels are precisely the labels
actually attained on `A`.  Filtering `A` at one such label gives the
corresponding row.  These rows form a literal finite partition of `A`:
they are nonempty, lie in `A`, have constant complete signature, are
pairwise disjoint, and have union exactly `A`.

The final results transport arbitrary additive weights across this
partition, including the factorization-coordinate weights used later in
the paper.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

noncomputable section

/-! ## Labels and row fibers -/











/-! ## Row support and constancy -/

/-- Every complete rough row is a subset of the original finite set. -/
theorem completeRoughRowFiber_subset
    (y : ℕ) (A : Finset ℕ) (label : ℕ) :
    completeRoughRowFiber y A label ⊆ A := by
  intro a ha
  exact (mem_completeRoughRowFiber.mp ha).1

/-- The integer rough label is constant throughout its row fiber. -/
theorem completeRoughLabel_eq_of_mem_rowFiber
    {y label a : ℕ} {A : Finset ℕ}
    (ha : a ∈ completeRoughRowFiber y A label) :
    completeRoughLabel y a = label :=
  (mem_completeRoughRowFiber.mp ha).2





/-! ## Exact finite partition -/

/-- Distinct attained labels have disjoint row fibers. -/
theorem completeRoughRowFibers_pairwiseDisjoint
    (y : ℕ) (A : Finset ℕ) :
    ((completeRoughLabelSet y A : Finset ℕ) : Set ℕ).PairwiseDisjoint
      (completeRoughRowFiber y A) := by
  intro label _hlabel other _hother hne
  change Disjoint (completeRoughRowFiber y A label)
    (completeRoughRowFiber y A other)
  rw [Finset.disjoint_left]
  intro a haLabel haOther
  have hlabelEq : completeRoughLabel y a = label :=
    completeRoughLabel_eq_of_mem_rowFiber haLabel
  have hotherEq : completeRoughLabel y a = other :=
    completeRoughLabel_eq_of_mem_rowFiber haOther
  exact hne (hlabelEq.symm.trans hotherEq)

/-- The union of all attained-label row fibers is exactly `A`. -/
theorem completeRoughLabelSet_biUnion_rowFibers
    (y : ℕ) (A : Finset ℕ) :
    (completeRoughLabelSet y A).biUnion
        (completeRoughRowFiber y A) = A := by
  ext a
  constructor
  · intro ha
    rw [Finset.mem_biUnion] at ha
    obtain ⟨label, _hlabel, haRow⟩ := ha
    exact (completeRoughRowFiber_subset y A label) haRow
  · intro ha
    rw [Finset.mem_biUnion]
    refine ⟨completeRoughLabel y a, ?_, ?_⟩
    · exact mem_completeRoughLabelSet.mpr ⟨a, ha, rfl⟩
    · exact mem_completeRoughRowFiber.mpr ⟨ha, rfl⟩

/-! ## Additive partition identities -/

/-- Every additive weight on `A` is the sum of its weights row by row. -/
theorem sum_eq_sum_completeRoughRowFibers
    {M : Type*} [AddCommMonoid M]
    (y : ℕ) (A : Finset ℕ) (weight : ℕ → M) :
    ∑ a ∈ A, weight a =
      ∑ label ∈ completeRoughLabelSet y A,
        ∑ a ∈ completeRoughRowFiber y A label, weight a := by
  classical
  calc
    ∑ a ∈ A, weight a =
        ∑ a ∈ (completeRoughLabelSet y A).biUnion
          (completeRoughRowFiber y A), weight a := by
      rw [completeRoughLabelSet_biUnion_rowFibers]
    _ = ∑ label ∈ completeRoughLabelSet y A,
          ∑ a ∈ completeRoughRowFiber y A label, weight a := by
      exact Finset.sum_biUnion
        (completeRoughRowFibers_pairwiseDisjoint y A)







end

end Erdos390.WholePaper

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















/-- The upper interval contains exactly `h` integer tokens. -/
theorem roughUpperBlock_card (n h : ℕ) :
    (roughUpperBlock n h).card = h := by
  simp only [roughUpperBlock, Nat.card_Ioc]
  omega





/-! ## The finite head and raw weights -/

















































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

/-- Every fixed exceptional factor is a literal upper-tail occurrence. -/
theorem paperFixedExceptionalFactors_subset_tail
    {n h : ℕ}
    (R : BankPaperRealization n (upperEndpoint n h))
    (deltaStar : ℝ) :
    R.paperFixedExceptionalFactors deltaStar ⊆
      Finset.Ioc (2 * n) (upperEndpoint n h) := by
  simpa only [roughUpperBlock, upperEndpoint] using
    R.paperFixedExceptionalFactors_subset_upperBlock deltaStar

/-- The set difference in the definition makes the fixed factors and all
designated donors literally disjoint. -/
theorem paperFixedExceptionalFactors_disjoint_prechargeDonorSet
    {n h : ℕ}
    (R : BankPaperRealization n (upperEndpoint n h))
    (deltaStar : ℝ) :
    Disjoint (R.paperFixedExceptionalFactors deltaStar)
      R.prechargeDonorSet := by
  rw [Finset.disjoint_left]
  intro a haFixed haDonor
  rw [paperFixedExceptionalFactors, Finset.mem_sdiff] at haFixed
  exact haFixed.2 haDonor

/-- Fixed exceptional factors together with their complementary donor
occurrences remain a subset of the literal upper tail. -/
theorem paperFixedExceptionalBacking_subset_tail
    {n h : ℕ}
    (R : BankPaperRealization n (upperEndpoint n h))
    (deltaStar : ℝ) :
    R.paperFixedExceptionalFactors deltaStar ∪ R.prechargeDonorSet ⊆
      Finset.Ioc (2 * n) (upperEndpoint n h) := by
  intro a ha
  rcases Finset.mem_union.mp ha with haFixed | haDonor
  · exact R.paperFixedExceptionalFactors_subset_tail deltaStar haFixed
  · exact R.prechargeDonorSet_subset_tail haDonor















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



























/-! ## The donor/base row-preserving bijection -/





/-- Re-express a literal finite-state row count as the cardinality of the
corresponding subtype. -/
private theorem completeLabelMultiplicity_eq_subtype_card
    (y : ℕ) (state : Finset ℕ) (label : ℕ) :
    completeLabelMultiplicity y state label =
      Fintype.card {a : ↑state // completeRoughLabel y a.1 = label} := by
  classical
  rw [completeLabelMultiplicity, ← Fintype.card_coe]
  apply Fintype.card_congr
  exact
    { toFun := fun a ↦
        ⟨⟨a.1, (Finset.mem_filter.mp a.2).1⟩,
          (Finset.mem_filter.mp a.2).2⟩
      invFun := fun a ↦
        ⟨a.1.1, Finset.mem_filter.mpr ⟨a.1.2, a.2⟩⟩
      left_inv := by
        intro a
        apply Subtype.ext
        rfl
      right_inv := by
        intro a
        apply Subtype.ext
        rfl }

/-- Donor and base multiplicities agree in every complete rough row.  The
proof is the cardinality equality induced by the literal restricted
`prechargeDonorBaseEquiv`. -/
theorem prechargeBaseState_completeLabelMultiplicity_eq_donorSet
    {n M : ℕ} (R : BankPaperRealization n M) (label : ℕ) :
    completeLabelMultiplicity (yNat n) R.prechargeBaseState label =
      completeLabelMultiplicity (yNat n) R.prechargeDonorSet label := by
  rw [completeLabelMultiplicity_eq_subtype_card,
    completeLabelMultiplicity_eq_subtype_card]
  exact (Fintype.card_congr
    (R.prechargeDonorBaseRowEquiv label)).symm

/-! ## Upper-tail ownership and the postcharge target -/





/-- Every non-smooth row is either active nonexceptional or exceptional.
No asymptotic hypothesis is needed for this literal order dichotomy. -/
theorem roughCanonical_activeNonexceptional_or_exceptional
    {n label : ℕ} {deltaStar : ℝ} (hlabel : label ≠ 1) :
    RoughCanonicalActiveNonexceptionalLabel n deltaStar label ∨
      RoughCanonicalExceptionalLabel n deltaStar label := by
  by_cases hactive :
      (n : ℝ) ^ deltaStar ≤ 2 * (n : ℝ) / (label : ℝ)
  · exact Or.inl ⟨hlabel, hactive⟩
  · exact Or.inr (lt_of_not_ge hactive)

/-- Complete-label multiplicity is monotone under finite-set containment. -/
theorem completeLabelMultiplicity_mono
    {y label : ℕ} {A B : Finset ℕ} (hAB : A ⊆ B) :
    completeLabelMultiplicity y A label ≤
      completeLabelMultiplicity y B label := by
  unfold completeLabelMultiplicity
  apply Finset.card_le_card
  intro a ha
  have haData := Finset.mem_filter.mp ha
  exact Finset.mem_filter.mpr ⟨hAB haData.1, haData.2⟩

/-- Multiplicity is additive on a disjoint union. -/
theorem completeLabelMultiplicity_union_of_disjoint
    {y label : ℕ} {A B : Finset ℕ} (hAB : Disjoint A B) :
    completeLabelMultiplicity y (A ∪ B) label =
      completeLabelMultiplicity y A label +
        completeLabelMultiplicity y B label := by
  have hfilter : Disjoint
      (A.filter fun a ↦ completeRoughLabel y a = label)
      (B.filter fun a ↦ completeRoughLabel y a = label) :=
    hAB.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _)
  unfold completeLabelMultiplicity
  rw [Finset.filter_union,
    Finset.card_union_of_disjoint hfilter]

/-- On an exceptional complete rough row, every upper-tail occurrence is
either an actual donor or belongs to the complementary fixed exceptional
set.  Thus their union exhausts that row, not merely a subset of it. -/
theorem paperFixedExceptional_union_prechargeDonor_multiplicity_eq_upperTarget_of_exceptional
    {n h : ℕ}
    (R : BankPaperRealization n (upperEndpoint n h))
    (deltaStar : ℝ) (label : ℕ)
    (hexceptional : RoughCanonicalExceptionalLabel n deltaStar label) :
    completeLabelMultiplicity (yNat n)
        (R.paperFixedExceptionalFactors deltaStar ∪ R.prechargeDonorSet)
        label =
      roughUpperCompleteRoughRowTarget n h (yNat n) label := by
  unfold completeLabelMultiplicity roughUpperCompleteRoughRowTarget
    completeRoughRowFiber
  apply congrArg Finset.card
  ext a
  simp only [Finset.mem_filter, Finset.mem_union]
  constructor
  · rintro ⟨haFixed | haDonor, haLabel⟩
    · exact ⟨R.paperFixedExceptionalFactors_subset_upperBlock deltaStar
        haFixed, haLabel⟩
    · have haUpper : a ∈ roughUpperBlock n h := by
        simpa only [roughUpperBlock, upperEndpoint] using
          R.prechargeDonorSet_subset_tail haDonor
      exact ⟨haUpper, haLabel⟩
  · rintro ⟨haUpper, haLabel⟩
    by_cases haDonor : a ∈ R.prechargeDonorSet
    · exact ⟨Or.inr haDonor, haLabel⟩
    · refine ⟨Or.inl ?_, haLabel⟩
      apply (R.mem_paperFixedExceptionalFactors (a := a)).2
      refine ⟨haUpper, ?_, haDonor⟩
      simpa only [RoughCanonicalExceptionalLabel, haLabel] using
        hexceptional

/-- Replacing donors by their row-preserving bank bases preserves the
exact exhaustion of an exceptional upper row. -/
theorem paperFixedExceptional_add_prechargeBase_multiplicity_eq_upperTarget_of_exceptional
    {n h : ℕ}
    (R : BankPaperRealization n (upperEndpoint n h))
    (deltaStar : ℝ) (label : ℕ)
    (hexceptional : RoughCanonicalExceptionalLabel n deltaStar label) :
    completeLabelMultiplicity (yNat n)
        (R.paperFixedExceptionalFactors deltaStar) label +
      completeLabelMultiplicity (yNat n) R.prechargeBaseState label =
        roughUpperCompleteRoughRowTarget n h (yNat n) label := by
  calc
    completeLabelMultiplicity (yNat n)
          (R.paperFixedExceptionalFactors deltaStar) label +
        completeLabelMultiplicity (yNat n) R.prechargeBaseState label =
        completeLabelMultiplicity (yNat n)
          (R.paperFixedExceptionalFactors deltaStar) label +
        completeLabelMultiplicity (yNat n) R.prechargeDonorSet label := by
      rw [R.prechargeBaseState_completeLabelMultiplicity_eq_donorSet label]
    _ = completeLabelMultiplicity (yNat n)
          (R.paperFixedExceptionalFactors deltaStar ∪
            R.prechargeDonorSet) label :=
      (completeLabelMultiplicity_union_of_disjoint
        (R.paperFixedExceptionalFactors_disjoint_prechargeDonorSet
          deltaStar)).symm
    _ = roughUpperCompleteRoughRowTarget n h (yNat n) label :=
      R.paperFixedExceptional_union_prechargeDonor_multiplicity_eq_upperTarget_of_exceptional
        deltaStar label hexceptional

/-- Fixed exceptional factors and bank bases consume no more tokens in a
row than the literal upper row contains.  Donors are used for this finite
comparison and then replaced by bases through the row equivalence above. -/
theorem paperFixedExceptional_add_prechargeBase_multiplicity_le_upperTarget
    {n h : ℕ}
    (R : BankPaperRealization n (upperEndpoint n h))
    (deltaStar : ℝ) (label : ℕ) :
    completeLabelMultiplicity (yNat n)
        (R.paperFixedExceptionalFactors deltaStar) label +
      completeLabelMultiplicity (yNat n) R.prechargeBaseState label ≤
        roughUpperCompleteRoughRowTarget n h (yNat n) label := by
  have hbacking :
      R.paperFixedExceptionalFactors deltaStar ∪ R.prechargeDonorSet ⊆
        roughUpperBlock n h := by
    simpa only [roughUpperBlock, upperEndpoint] using
      R.paperFixedExceptionalBacking_subset_tail deltaStar
  calc
    completeLabelMultiplicity (yNat n)
          (R.paperFixedExceptionalFactors deltaStar) label +
        completeLabelMultiplicity (yNat n) R.prechargeBaseState label =
        completeLabelMultiplicity (yNat n)
          (R.paperFixedExceptionalFactors deltaStar) label +
        completeLabelMultiplicity (yNat n) R.prechargeDonorSet label := by
      rw [R.prechargeBaseState_completeLabelMultiplicity_eq_donorSet label]
    _ = completeLabelMultiplicity (yNat n)
          (R.paperFixedExceptionalFactors deltaStar ∪
            R.prechargeDonorSet) label :=
      (completeLabelMultiplicity_union_of_disjoint
        (R.paperFixedExceptionalFactors_disjoint_prechargeDonorSet
          deltaStar)).symm
    _ ≤ completeLabelMultiplicity (yNat n) (roughUpperBlock n h) label :=
      completeLabelMultiplicity_mono hbacking
    _ = roughUpperCompleteRoughRowTarget n h (yNat n) label := rfl





theorem roughCanonicalPostchargeRowTarget_eq_intCast
    {n h : ℕ}
    (R : BankPaperRealization n (upperEndpoint n h))
    (deltaStar : ℝ) (label : ℕ) :
    R.roughCanonicalPostchargeRowTarget deltaStar label =
      (R.roughCanonicalPostchargeRowTargetInt deltaStar label : ℝ) := by
  simp [roughCanonicalPostchargeRowTarget,
    roughCanonicalPostchargeRowTargetInt]

/-- The integer postcharge quota is exactly zero on every exceptional
complete rough row: all upper tokens there are already fixed or banked. -/
theorem roughCanonicalPostchargeRowTargetInt_eq_zero_of_exceptional
    {n h : ℕ}
    (R : BankPaperRealization n (upperEndpoint n h))
    (deltaStar : ℝ) (label : ℕ)
    (hexceptional : RoughCanonicalExceptionalLabel n deltaStar label) :
    R.roughCanonicalPostchargeRowTargetInt deltaStar label = 0 := by
  have hrow :=
    R.paperFixedExceptional_add_prechargeBase_multiplicity_eq_upperTarget_of_exceptional
      deltaStar label hexceptional
  have hrowInt :
      (completeLabelMultiplicity (yNat n)
          (R.paperFixedExceptionalFactors deltaStar) label : ℤ) +
        (completeLabelMultiplicity (yNat n)
          R.prechargeBaseState label : ℤ) =
      (roughUpperCompleteRoughRowTarget n h (yNat n) label : ℤ) := by
    exact_mod_cast hrow
  unfold roughCanonicalPostchargeRowTargetInt
  linarith

/-- Real form of the same paper fact: exceptional rows have `q_R = 0`. -/
theorem roughCanonicalPostchargeRowTarget_eq_zero_of_exceptional
    {n h : ℕ}
    (R : BankPaperRealization n (upperEndpoint n h))
    (deltaStar : ℝ) (label : ℕ)
    (hexceptional : RoughCanonicalExceptionalLabel n deltaStar label) :
    R.roughCanonicalPostchargeRowTarget deltaStar label = 0 := by
  rw [R.roughCanonicalPostchargeRowTarget_eq_intCast deltaStar label,
    R.roughCanonicalPostchargeRowTargetInt_eq_zero_of_exceptional
      deltaStar label hexceptional]
  norm_num

/-- Nonnegativity needs no analytic row census: it follows from the actual
upper-tail ownership injection. -/
theorem roughCanonicalPostchargeRowTarget_nonneg
    {n h : ℕ}
    (R : BankPaperRealization n (upperEndpoint n h))
    (deltaStar : ℝ) (label : ℕ) :
    0 ≤ R.roughCanonicalPostchargeRowTarget deltaStar label := by
  have hfinite :=
    R.paperFixedExceptional_add_prechargeBase_multiplicity_le_upperTarget
      deltaStar label
  have hreal :
      (completeLabelMultiplicity (yNat n)
          (R.paperFixedExceptionalFactors deltaStar) label : ℝ) +
        (completeLabelMultiplicity (yNat n)
          R.prechargeBaseState label : ℝ) ≤
      (roughUpperCompleteRoughRowTarget n h (yNat n) label : ℝ) := by
    exact_mod_cast hfinite
  unfold roughCanonicalPostchargeRowTarget
  linarith

/-! ## Exact local discrepancy ledger -/







/-! ## Exact support reduction for the local deletion set -/







/-! ## Explicit remaining finite/analytic obligations -/







end BankPaperRealization

end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankPaperCanonicalSectionEightActualDataConnector -/
section


/-!
# Actual-data connector for the Section 8 analytic ledger

The reduced Section 8 ledger still names the actual post-guard active mass
and the exact frozen mass/logarithmic ledgers.  The Proposition 8.7 actual-
data connector already supplies the finite decomposition needed to make
those objects literal: every guarded candidate is split into its active
seed and its frozen remainder.

This file adjoins the frozen integral factors, defines the resulting exact
total frozen mass and logarithmic contribution, and proves

`m0 + qTilde = #fixed + sum candidates preSelector`

whenever the actual active-measure constructor holds.  Consequently the
first frozen-baseline estimate reduces to the rough selector's literal
total-mass estimate.  For the canonical scaled seed, its active mass is
exactly the guarded smooth base.  Exact interval support then centers the
frozen logarithmic contribution, while the complete central-tail product
satisfies `logY = h * L + O(secondOrderScale)` by elementary factor bounds.
The generic interval-geometry theorem exposes the selector total-mass
estimate, and the final constructed-quota theorem proves that estimate from
the rough-stage frozen baseline ledger, nearest-integer construction, and
the existing `d = O(secondOrderScale / L)` theorem.

No abstract `qTilde`, `m0`, or `Lambda0` remains in the final theorem.
-/

open Filter Topology Asymptotics
open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.PaperBridgeFit
open Erdos390.Full.PaperGuardCensus
open Erdos390.Full.Scale
open BankPaperRealization

noncomputable section

/-! ## Literal frozen mass and logarithmic contribution -/









/-! ## Families of literal actual data -/





/-! ## Elementary logarithmic geometry of the literal upper tail -/















/-! ## Centering the literal frozen logarithmic ledger -/















/-! ## Exact charged-selector row ledger -/

/-- Extend the complete-rough-row partition of `A` by zero across any
finite superset of its attained labels. -/
theorem sum_eq_sum_completeRoughRowFibers_of_labelSet_subset
    {M : Type*} [AddCommMonoid M]
    (y : Nat) (A labels : Finset Nat) (weight : Nat -> M)
    (hlabels : completeRoughLabelSet y A ⊆ labels) :
    (∑ a ∈ A, weight a) =
      ∑ label ∈ labels,
        ∑ a ∈ completeRoughRowFiber y A label, weight a := by
  classical
  rw [sum_eq_sum_completeRoughRowFibers]
  refine Finset.sum_subset hlabels ?_
  intro label _hlabel hlabelNotAttained
  have hempty : completeRoughRowFiber y A label = ∅ := by
    ext a
    simp only [Finset.notMem_empty, iff_false]
    intro ha
    exact hlabelNotAttained (mem_completeRoughLabelSet.mpr
      ⟨a, (mem_completeRoughRowFiber.mp ha).1,
        (mem_completeRoughRowFiber.mp ha).2⟩)
  rw [hempty]
  simp

/-- The cardinality of a finite set is the sum of its complete-label
multiplicities over any finite label set containing all attained labels. -/
theorem card_cast_eq_sum_completeLabelMultiplicity_of_labelSet_subset
    (y : Nat) (A labels : Finset Nat)
    (hlabels : completeRoughLabelSet y A ⊆ labels) :
    (A.card : Real) =
      ∑ label ∈ labels,
        (completeLabelMultiplicity y A label : Real) := by
  simpa [completeLabelMultiplicity, completeRoughRowFiber] using
    (sum_eq_sum_completeRoughRowFibers_of_labelSet_subset
      (M := Real) y A labels (fun _a => (1 : Real)) hlabels)



/-- Exact finite charged-product identity.  Once every nonsmooth attained
row has its postcharge mass, global active-row capacity rules out a missing
positive row.  Consequently the full mass error is exactly the negative of
the one remaining smooth-row postcharge discrepancy.

This identity includes both charged integral layers: the fixed exceptional
factors and `prechargeBaseState`.  It has no asymptotic premise. -/
theorem bankPaperCanonical_chargedSelectorMass_sub_height_eq_neg_smoothDiscrepancy
    {c : Real} {depth n h K : Nat} {left right : Nat -> Nat}
    {changed : Finset Nat}
    (R : BankPaperRealization n (upperEndpoint n h))
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (deltaStar : Real) (selector : Nat -> Real)
    (hactiveRows : ∀ label ∈ completeRoughLabelSet (yNat n)
        (R.roughCanonicalGuardedCandidateSet certificate deltaStar K),
      RoughCanonicalActiveNonexceptionalLabel n deltaStar label ->
        (∑ a ∈ R.roughCanonicalGuardedRow certificate deltaStar K label,
            selector a) =
          R.roughCanonicalPostchargeRowTarget deltaStar label)
    (hexceptionalRows : ∀ label ∈ completeRoughLabelSet (yNat n)
        (R.roughCanonicalGuardedCandidateSet certificate deltaStar K),
      label ≠ 1 -> RoughCanonicalExceptionalLabel n deltaStar label ->
        (∑ a ∈ R.roughCanonicalGuardedRow certificate deltaStar K label,
            selector a) = 0)
    (hcapacity : forall label, IsCompleteRoughLabel (yNat n) label ->
      RoughCanonicalActiveNonexceptionalLabel n deltaStar label ->
        RoughCanonicalPostchargeRowCapacity R certificate deltaStar K label) :
    ((R.paperFixedExceptionalFactors deltaStar).card : Real) +
        (R.prechargeBaseState.card : Real) +
        (∑ a ∈ R.roughCanonicalGuardedCandidateSet
          certificate deltaStar K, selector a) - (h : Real) =
      -R.roughCanonicalPostchargeRowDiscrepancy certificate deltaStar K
        1 selector := by
  classical
  let candidates :=
    R.roughCanonicalGuardedCandidateSet certificate deltaStar K
  let labels := bankPaperCanonicalChargedLabelSet
    (K := K) R certificate deltaStar
  have hupperLabels :
      completeRoughLabelSet (yNat n) (roughUpperBlock n h) ⊆ labels := by
    intro label hlabel
    simp [labels, bankPaperCanonicalChargedLabelSet, hlabel]
  have hfixedLabels :
      completeRoughLabelSet (yNat n)
        (R.paperFixedExceptionalFactors deltaStar) ⊆ labels := by
    intro label hlabel
    simp [labels, bankPaperCanonicalChargedLabelSet, hlabel]
  have hbaseLabels :
      completeRoughLabelSet (yNat n) R.prechargeBaseState ⊆ labels := by
    intro label hlabel
    simp [labels, bankPaperCanonicalChargedLabelSet, hlabel]
  have hcandidateLabels :
      completeRoughLabelSet (yNat n) candidates ⊆ labels := by
    intro label hlabel
    simp [labels, candidates, bankPaperCanonicalChargedLabelSet, hlabel]
  have hone : 1 ∈ labels := by
    simp [labels, bankPaperCanonicalChargedLabelSet]
  have hcandidatesPartition :
      (∑ a ∈ candidates, selector a) =
        ∑ label ∈ labels,
          ∑ a ∈ completeRoughRowFiber (yNat n) candidates label,
            selector a :=
    sum_eq_sum_completeRoughRowFibers_of_labelSet_subset
      (yNat n) candidates labels selector hcandidateLabels
  have hupperPartition :
      ((roughUpperBlock n h).card : Real) =
        ∑ label ∈ labels,
          (roughUpperCompleteRoughRowTarget n h (yNat n) label : Real) := by
    simpa only [roughUpperCompleteRoughRowTarget] using
      card_cast_eq_sum_completeLabelMultiplicity_of_labelSet_subset
        (yNat n) (roughUpperBlock n h) labels hupperLabels
  have hfixedPartition :
      ((R.paperFixedExceptionalFactors deltaStar).card : Real) =
        ∑ label ∈ labels,
          (completeLabelMultiplicity (yNat n)
            (R.paperFixedExceptionalFactors deltaStar) label : Real) :=
    card_cast_eq_sum_completeLabelMultiplicity_of_labelSet_subset
      (yNat n) (R.paperFixedExceptionalFactors deltaStar) labels hfixedLabels
  have hbasePartition :
      (R.prechargeBaseState.card : Real) =
        ∑ label ∈ labels,
          (completeLabelMultiplicity (yNat n) R.prechargeBaseState
            label : Real) :=
    card_cast_eq_sum_completeLabelMultiplicity_of_labelSet_subset
      (yNat n) R.prechargeBaseState labels hbaseLabels
  have hrow : ∀ label ∈ labels, label ≠ 1 ->
      (∑ a ∈ completeRoughRowFiber (yNat n) candidates label,
          selector a) =
        R.roughCanonicalPostchargeRowTarget deltaStar label := by
    intro label hlabel hlabelNeOne
    by_cases hlabelCandidate :
        label ∈ completeRoughLabelSet (yNat n) candidates
    · rcases roughCanonical_activeNonexceptional_or_exceptional
          (n := n) (deltaStar := deltaStar) hlabelNeOne with
        hactive | hexceptional
      · simpa only [candidates, BankPaperRealization.roughCanonicalGuardedRow]
          using hactiveRows label (by simpa only [candidates] using
            hlabelCandidate) hactive
      · have hzero := hexceptionalRows label
          (by simpa only [candidates] using hlabelCandidate)
          hlabelNeOne hexceptional
        have htargetZero :=
          R.roughCanonicalPostchargeRowTarget_eq_zero_of_exceptional
            deltaStar label hexceptional
        simpa only [candidates, BankPaperRealization.roughCanonicalGuardedRow,
          htargetZero] using hzero
    · have hempty :
          completeRoughRowFiber (yNat n) candidates label = ∅ := by
        ext a
        simp only [Finset.notMem_empty, iff_false]
        intro ha
        exact hlabelCandidate (mem_completeRoughLabelSet.mpr
          ⟨a, (mem_completeRoughRowFiber.mp ha).1,
            (mem_completeRoughRowFiber.mp ha).2⟩)
      have hcomplete : IsCompleteRoughLabel (yNat n) label := by
        simp only [labels, bankPaperCanonicalChargedLabelSet,
          Finset.mem_insert, Finset.mem_union] at hlabel
        rcases hlabel with hlabelOne |
          (((hlabelUpper | hlabelFixed) | hlabelBase) | hlabelCandidates)
        · exact (hlabelNeOne hlabelOne).elim
        · exact isCompleteRoughLabel_of_canonicalCompleteRoughRow
            (⟨label, hlabelUpper⟩ : CanonicalCompleteRoughRow (yNat n)
              (roughUpperBlock n h))
        · exact isCompleteRoughLabel_of_canonicalCompleteRoughRow
            (⟨label, hlabelFixed⟩ : CanonicalCompleteRoughRow (yNat n)
              (R.paperFixedExceptionalFactors deltaStar))
        · exact isCompleteRoughLabel_of_canonicalCompleteRoughRow
            (⟨label, hlabelBase⟩ : CanonicalCompleteRoughRow (yNat n)
              R.prechargeBaseState)
        · exact isCompleteRoughLabel_of_canonicalCompleteRoughRow
            (⟨label, hlabelCandidates⟩ : CanonicalCompleteRoughRow (yNat n)
              candidates)
      rcases roughCanonical_activeNonexceptional_or_exceptional
          (n := n) (deltaStar := deltaStar) hlabelNeOne with
        hactive | hexceptional
      · have hcap := hcapacity label hcomplete hactive
        unfold RoughCanonicalPostchargeRowCapacity at hcap
        have htargetZero :
            R.roughCanonicalPostchargeRowTarget deltaStar label = 0 := by
          rw [show R.roughCanonicalGuardedRow certificate deltaStar K label = ∅ by
            simpa only [candidates,
              BankPaperRealization.roughCanonicalGuardedRow] using hempty]
            at hcap
          apply le_antisymm
          · simpa only [Finset.card_empty, Nat.cast_zero] using hcap
          · exact
              R.roughCanonicalPostchargeRowTarget_nonneg deltaStar label
        simp only [hempty, Finset.sum_empty, htargetZero]
      · have htargetZero :=
          R.roughCanonicalPostchargeRowTarget_eq_zero_of_exceptional
            deltaStar label hexceptional
        simp only [hempty, Finset.sum_empty, htargetZero]
  have hrowDifference :
      (∑ label ∈ labels,
          ∑ a ∈ completeRoughRowFiber (yNat n) candidates label,
            selector a) -
          ∑ label ∈ labels,
            R.roughCanonicalPostchargeRowTarget deltaStar label =
        (∑ a ∈ completeRoughRowFiber (yNat n) candidates 1,
            selector a) -
          R.roughCanonicalPostchargeRowTarget deltaStar 1 := by
    rw [← Finset.sum_sub_distrib]
    calc
      (∑ label ∈ labels,
          ((∑ a ∈ completeRoughRowFiber (yNat n) candidates label,
              selector a) -
            R.roughCanonicalPostchargeRowTarget deltaStar label)) =
          ∑ label ∈ labels,
            if label = 1 then
              ((∑ a ∈ completeRoughRowFiber (yNat n) candidates 1,
                  selector a) -
                R.roughCanonicalPostchargeRowTarget deltaStar 1)
            else 0 := by
        apply Finset.sum_congr rfl
        intro label hlabel
        by_cases hlabelOne : label = 1
        · subst label
          simp
        · rw [if_neg hlabelOne, hrow label hlabel hlabelOne, sub_self]
      _ = (∑ a ∈ completeRoughRowFiber (yNat n) candidates 1,
              selector a) -
            R.roughCanonicalPostchargeRowTarget deltaStar 1 := by
        simp [hone]
  have htargetPartition :
      (∑ label ∈ labels,
          R.roughCanonicalPostchargeRowTarget deltaStar label) =
        ((roughUpperBlock n h).card : Real) -
          ((R.paperFixedExceptionalFactors deltaStar).card : Real) -
          (R.prechargeBaseState.card : Real) := by
    unfold BankPaperRealization.roughCanonicalPostchargeRowTarget
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib,
      ← hupperPartition, ← hfixedPartition, ← hbasePartition]
  have htargetPartition' :
      (∑ label ∈ labels,
          R.roughCanonicalPostchargeRowTarget deltaStar label) =
        (h : Real) -
          ((R.paperFixedExceptionalFactors deltaStar).card : Real) -
          (R.prechargeBaseState.card : Real) := by
    simpa only [roughUpperBlock_card] using htargetPartition
  rw [hcandidatesPartition,
    BankPaperRealization.roughCanonicalPostchargeRowDiscrepancy]
  change ((R.paperFixedExceptionalFactors deltaStar).card : Real) +
      (R.prechargeBaseState.card : Real) +
      (∑ label ∈ labels,
        ∑ a ∈ completeRoughRowFiber (yNat n) candidates label,
          selector a) - (h : Real) =
    -(R.roughCanonicalPostchargeRowTarget deltaStar 1 -
      ∑ a ∈ completeRoughRowFiber (yNat n) candidates 1, selector a)
  calc
    ((R.paperFixedExceptionalFactors deltaStar).card : Real) +
          (R.prechargeBaseState.card : Real) +
          (∑ label ∈ labels,
            ∑ a ∈ completeRoughRowFiber (yNat n) candidates label,
              selector a) - (h : Real) =
        (∑ label ∈ labels,
            ∑ a ∈ completeRoughRowFiber (yNat n) candidates label,
              selector a) -
          ((h : Real) -
            ((R.paperFixedExceptionalFactors deltaStar).card : Real) -
            (R.prechargeBaseState.card : Real)) := by ring
    _ = (∑ label ∈ labels,
            ∑ a ∈ completeRoughRowFiber (yNat n) candidates label,
              selector a) -
          ∑ label ∈ labels,
            R.roughCanonicalPostchargeRowTarget deltaStar label := by
      rw [htargetPartition']
    _ = (∑ a ∈ completeRoughRowFiber (yNat n) candidates 1,
            selector a) -
          R.roughCanonicalPostchargeRowTarget deltaStar 1 := hrowDifference
    _ = -(R.roughCanonicalPostchargeRowTarget deltaStar 1 -
          ∑ a ∈ completeRoughRowFiber (yNat n) candidates 1,
            selector a) := by ring



























/-! ## The remaining actual analytic sources -/

















/-! ## Construction of the old Section 8 ledger -/













end

end Erdos390.WholePaper

end

theorem solution :
∀ {c : Real} {depth n h K : Nat} {left right : Nat → Nat} {changed : Finset.{0} Nat}
  (R : Erdos390.WholePaper.BankPaperRealization n (Erdos390.WholePaper.upperEndpoint n h))
  (certificate : Erdos390.WholePaper.GuardedCentralAnchorCertificate c depth n left right changed) (deltaStar : Real)
  (selector : Nat → Real),
  (∀ (label : Nat),
      Membership.mem.{0, 0}
          (Erdos390.WholePaper.completeRoughLabelSet (Erdos390.Full.ArithmeticModel.yNat n)
            (Erdos390.WholePaper.BankPaperRealization.roughCanonicalGuardedCandidateSet R certificate deltaStar K))
          label →
        Erdos390.WholePaper.BankPaperRealization.RoughCanonicalActiveNonexceptionalLabel n deltaStar label →
          Eq.{1}
            (∑ a ∈ Erdos390.WholePaper.BankPaperRealization.roughCanonicalGuardedRow R certificate deltaStar K label,
              selector a)
            (Erdos390.WholePaper.BankPaperRealization.roughCanonicalPostchargeRowTarget R deltaStar label)) →
    (∀ (label : Nat),
        Membership.mem.{0, 0}
            (Erdos390.WholePaper.completeRoughLabelSet (Erdos390.Full.ArithmeticModel.yNat n)
              (Erdos390.WholePaper.BankPaperRealization.roughCanonicalGuardedCandidateSet R certificate deltaStar K))
            label →
          Ne.{1} label (1 : Nat) →
            Erdos390.WholePaper.BankPaperRealization.RoughCanonicalExceptionalLabel n deltaStar label →
              Eq.{1}
                (∑
                  a ∈ Erdos390.WholePaper.BankPaperRealization.roughCanonicalGuardedRow R certificate deltaStar K label,
                  selector a)
                (0 : Real)) →
      (∀ (label : Nat),
          Erdos390.WholePaper.IsCompleteRoughLabel (Erdos390.Full.ArithmeticModel.yNat n) label →
            Erdos390.WholePaper.BankPaperRealization.RoughCanonicalActiveNonexceptionalLabel n deltaStar label →
              Erdos390.WholePaper.BankPaperRealization.RoughCanonicalPostchargeRowCapacity R certificate deltaStar K
                label) →
        Eq.{1}
          (HSub.hSub.{0, 0, 0}
            (HAdd.hAdd.{0, 0, 0}
              (HAdd.hAdd.{0, 0, 0}
                ↑(Finset.card.{0} (Erdos390.WholePaper.BankPaperRealization.paperFixedExceptionalFactors R deltaStar))
                ↑(Finset.card.{0} (Erdos390.WholePaper.BankPaperRealization.prechargeBaseState R)))
              (∑
                a ∈
                  Erdos390.WholePaper.BankPaperRealization.roughCanonicalGuardedCandidateSet R certificate deltaStar K,
                selector a))
            ↑h)
          (Neg.neg.{0}
            (Erdos390.WholePaper.BankPaperRealization.roughCanonicalPostchargeRowDiscrepancy R certificate deltaStar K
              (1 : Nat) selector)) := by
  exact @Erdos390.WholePaper.bankPaperCanonical_chargedSelectorMass_sub_height_eq_neg_smoothDiscrepancy
