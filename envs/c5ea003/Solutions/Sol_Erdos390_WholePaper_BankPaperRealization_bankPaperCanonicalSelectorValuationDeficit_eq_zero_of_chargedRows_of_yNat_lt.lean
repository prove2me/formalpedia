-- Prove2me | solution 1 for Erdos390.WholePaper.BankPaperRealization.bankPaperCanonicalSelectorValuationDeficit_eq_zero_of_chargedRows_of_yNat_lt
-- status  : ACCEPTED   (prove)
-- author  : @doctosil
-- created : 2026-09-17T15:54:20.014372+00:00
-- url     : https://prove2.me/submissions/37217ed9-eb42-4219-af7a-3f0f2f079d3f

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

/-- The full vector signature throughout a row is the factorization of
that row's integer label. -/
theorem completeRoughSignature_eq_label_factorization_of_mem_rowFiber
    {y label a : ℕ} {A : Finset ℕ}
    (ha : a ∈ completeRoughRowFiber y A label) :
    completeRoughSignature y a = label.factorization := by
  calc
    completeRoughSignature y a =
        (completeRoughLabel y a).factorization :=
      (completeRoughLabel_factorization y a).symm
    _ = label.factorization :=
      congrArg Nat.factorization
        (completeRoughLabel_eq_of_mem_rowFiber ha)



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



/-- Above the cutoff, a factorization coordinate is visibly constant on
each complete rough row. -/
theorem factorization_eq_label_factorization_of_mem_rowFiber
    {y p label a : ℕ} {A : Finset ℕ}
    (hp : y < p)
    (ha : a ∈ completeRoughRowFiber y A label) :
    a.factorization p = label.factorization p := by
  simpa only [completeRoughSignature_apply, if_pos hp] using
    congrArg (fun signature : ℕ →₀ ℕ ↦ signature p)
      (completeRoughSignature_eq_label_factorization_of_mem_rowFiber ha)



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

































/-! ## The remaining actual analytic sources -/

















/-! ## Construction of the old Section 8 ledger -/













end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankPaperCanonicalSignedResidualSelectorIdentification -/
section


/-!
# Exact selector identification for the four-term signed rough residual

The quantitative signed-residual file defines the four scalar terms and
proves their bounds, while the selector handoff defines the literal
target-minus-selector valuation deficit.  This file isolates the finite
identity still needed to connect them.

There are two independent finite ledgers:

* the target ledger expands the charged selector target as the raw upper
  valuation, less fixed exceptional factors and the bank base, with
  exceptional donors restored;
* the selector ledger expands the concrete guarded source as the raw lower
  valuation, less exceptional and nonexceptional deleted coordinates, plus
  the aggregate row correction.

The target ledger is proved below in the medium-prime range from the existing
charge divisibility.  The selector ledger remains a named source-level input:
the current implementation uses guarded postcharge corrections, whereas the
available aggregate correction scalar is defined using raw rows and raw
broad pools, and no global valuation reindexing theorem identifies them.

Once the two ledgers are available, the exact four signs follow by ring
algebra.  A final transport theorem records the additional, already-defined
valuation moment introduced by structured smooth placement.  Thus the
remaining gap is localized without assuming the desired final equality.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.PaperBridgeFit

noncomputable section

namespace BankPaperRealization

/-! ## Concrete raw and source ledgers -/







/-! ## Exact reduction of the source ledger -/















/-! ## What the guarded postcharge correction actually contributes -/













/-! ## The charged target ledger is already derivable -/

/-- The literal exceptional upper set is the disjoint union of the retained
fixed exceptional factors and the exceptional designated donors. -/
theorem paperExceptionalUpperFactors_eq_fixed_union_exceptionalDonors
    {n h : Nat}
    (R : BankPaperRealization n (upperEndpoint n h))
    (deltaStar : Real) :
    paperExceptionalUpperFactors n h deltaStar =
      R.paperFixedExceptionalFactors deltaStar ∪
        R.roughCanonicalExceptionalDonorSet deltaStar := by
  ext a
  constructor
  · intro ha
    by_cases hdonor : a ∈ R.prechargeDonorSet
    · apply Finset.mem_union_right
      exact (R.mem_roughCanonicalExceptionalDonorSet).2
        ⟨hdonor, (mem_paperExceptionalUpperFactors.mp ha).2⟩
    · apply Finset.mem_union_left
      exact Finset.mem_sdiff.mpr ⟨ha, hdonor⟩
  · intro ha
    rcases Finset.mem_union.mp ha with hfixed | hdonor
    · exact (Finset.mem_sdiff.mp hfixed).1
    · have hdonorData :=
        (R.mem_roughCanonicalExceptionalDonorSet).1 hdonor
      have htail := R.prechargeDonorSet_subset_tail hdonorData.1
      apply mem_paperExceptionalUpperFactors.mpr
      constructor
      · simpa only [roughUpperBlock, upperEndpoint] using htail
      · exact hdonorData.2



/-! ## Four-term identification and structured transport -/













/-! ## The literal Post-Hfit pre-selector -/



























end BankPaperRealization

end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankPaperCanonicalTopFrozenSelectorTailSupportReductionConnector -/
section


/-!
# Selector-tail support reduction for the frozen-top sources

Outside the medium-prime band there are two disjoint finite mechanisms.

* At a head prime `q ≤ W`, every raw or constant-pool correction term has
  zero `q`-valuation.  The source moment is therefore exactly the moment of
  the scaled structured seed, hence `Rhead.target`.
* At a high prime `yNat n < q`, factorization is constant on each complete
  rough row.  Charged nonsmooth-row totals, together with postcharge row
  capacity for unattained active rows, identify the source moment with the
  selector-tail target ledger.

Thus the only extra low-prime datum is the literal compatibility

`Rhead.target p =
  (certificate.selectorTailTarget R fixed).factorization p`.

The finite theorems below first expose the low/high reductions separately,
then package selector-tail support for both the literal `qTilde` source and
its nearest-integer rounded counterpart.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.PaperBridgeFit
open Erdos390.Full.PaperGuardCensus

noncomputable section

namespace BankPaperRealization

/-! ## Head-prime vanishing -/













/-! ## High-prime row reindexing -/

/-- A weighted high-prime moment can be reindexed over any finite superset
of the attained complete rough labels. -/
theorem
    sum_mul_factorization_eq_sum_rowSum_mul_labelFactorization_of_labelSet_subset
    (y p : Nat) (A labels : Finset Nat) (weight : Nat -> Real)
    (hyp : y < p) (hlabels : completeRoughLabelSet y A ⊆ labels) :
    (∑ a ∈ A, weight a * (a.factorization p : Real)) =
      ∑ label ∈ labels,
        (∑ a ∈ completeRoughRowFiber y A label, weight a) *
          (label.factorization p : Real) := by
  rw [sum_eq_sum_completeRoughRowFibers_of_labelSet_subset
    y A labels (fun a => weight a * (a.factorization p : Real)) hlabels]
  apply Finset.sum_congr rfl
  intro label _hlabel
  calc
    (∑ a ∈ completeRoughRowFiber y A label,
        weight a * (a.factorization p : Real)) =
      ∑ a ∈ completeRoughRowFiber y A label,
        weight a * (label.factorization p : Real) := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [factorization_eq_label_factorization_of_mem_rowFiber hyp ha]
    _ = (∑ a ∈ completeRoughRowFiber y A label, weight a) *
          (label.factorization p : Real) := by
      rw [Finset.sum_mul]

/-- Cast-valued specialization of the preceding weighted partition. -/
theorem
    sum_factorization_cast_eq_sum_completeLabelMultiplicity_mul_of_labelSet_subset
    (y p : Nat) (A labels : Finset Nat)
    (hyp : y < p) (hlabels : completeRoughLabelSet y A ⊆ labels) :
    (∑ a ∈ A, (a.factorization p : Real)) =
      ∑ label ∈ labels,
        (completeLabelMultiplicity y A label : Real) *
          (label.factorization p : Real) := by
  simpa [completeLabelMultiplicity, completeRoughRowFiber] using
    (sum_mul_factorization_eq_sum_rowSum_mul_labelFactorization_of_labelSet_subset
      y p A labels (fun _a => (1 : Real)) hyp hlabels)

/-- Charged nonsmooth rows and global postcharge capacity determine the
target total on every non-smooth label in the finite charged universe,
including labels not attained by guarded candidates. -/
theorem
    sum_chargedSelector_eq_postchargeRowTarget_of_mem_labelSet_of_ne_one
    {c : Real} {depth n h K : Nat} {left right : Nat -> Nat}
    {changed : Finset Nat}
    (R : BankPaperRealization n (upperEndpoint n h))
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (deltaStar : Real) (selector : Nat -> Real)
    (hrows : BankPaperCanonicalChargedNonsmoothRowRealization
      (K := K) R certificate deltaStar selector)
    (hcapacity : forall label, IsCompleteRoughLabel (yNat n) label ->
      RoughCanonicalActiveNonexceptionalLabel n deltaStar label ->
        RoughCanonicalPostchargeRowCapacity R certificate deltaStar K label)
    {label : Nat}
    (hlabel : label ∈
      bankPaperCanonicalChargedLabelSet (K := K)
        R certificate deltaStar)
    (hlabelNeOne : label ≠ 1) :
    (∑ a ∈ R.roughCanonicalGuardedRow certificate deltaStar K label,
        selector a) =
      R.roughCanonicalPostchargeRowTarget deltaStar label := by
  by_cases hlabelCandidate :
      label ∈ completeRoughLabelSet (yNat n)
        (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
  · rcases roughCanonical_activeNonexceptional_or_exceptional
        (n := n) (deltaStar := deltaStar) hlabelNeOne with
      hactive | hexceptional
    · exact hrows.1 label hlabelCandidate hactive
    · have hzero :=
        hrows.2 label hlabelCandidate hlabelNeOne hexceptional
      have htargetZero :=
        R.roughCanonicalPostchargeRowTarget_eq_zero_of_exceptional
          deltaStar label hexceptional
      simpa only [htargetZero] using hzero
  · have hempty :
        R.roughCanonicalGuardedRow certificate deltaStar K label = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro a ha
      exact hlabelCandidate
        (mem_completeRoughLabelSet.mpr
          ⟨a, (mem_completeRoughRowFiber.mp ha).1,
            (mem_completeRoughRowFiber.mp ha).2⟩)
    have hcomplete : IsCompleteRoughLabel (yNat n) label := by
      simp only [bankPaperCanonicalChargedLabelSet,
        Finset.mem_insert, Finset.mem_union] at hlabel
      rcases hlabel with hlabelOne |
        (((hlabelUpper | hlabelFixed) | hlabelBase) | hlabelCandidates)
      · exact (hlabelNeOne hlabelOne).elim
      · exact isCompleteRoughLabel_of_canonicalCompleteRoughRow
          (⟨label, hlabelUpper⟩ :
            CanonicalCompleteRoughRow (yNat n) (roughUpperBlock n h))
      · exact isCompleteRoughLabel_of_canonicalCompleteRoughRow
          (⟨label, hlabelFixed⟩ :
            CanonicalCompleteRoughRow (yNat n)
              (R.paperFixedExceptionalFactors deltaStar))
      · exact isCompleteRoughLabel_of_canonicalCompleteRoughRow
          (⟨label, hlabelBase⟩ :
            CanonicalCompleteRoughRow (yNat n) R.prechargeBaseState)
      · exact isCompleteRoughLabel_of_canonicalCompleteRoughRow
          (⟨label, hlabelCandidates⟩ :
            CanonicalCompleteRoughRow (yNat n)
              (R.roughCanonicalGuardedCandidateSet certificate
                deltaStar K))
    rcases roughCanonical_activeNonexceptional_or_exceptional
        (n := n) (deltaStar := deltaStar) hlabelNeOne with
      hactive | hexceptional
    · have hcap := hcapacity label hcomplete hactive
      unfold RoughCanonicalPostchargeRowCapacity at hcap
      rw [hempty] at hcap
      have htargetZero :
          R.roughCanonicalPostchargeRowTarget deltaStar label = 0 := by
        apply le_antisymm
        · simpa only [Finset.card_empty, Nat.cast_zero] using hcap
        · exact
            R.roughCanonicalPostchargeRowTarget_nonneg deltaStar label
      simp only [hempty, Finset.sum_empty, htargetZero]
    · have htargetZero :=
        R.roughCanonicalPostchargeRowTarget_eq_zero_of_exceptional
          deltaStar label hexceptional
      simp only [hempty, Finset.sum_empty, htargetZero]

/-- The signed target ledger is equivalent, after cancelling designated
exceptional donors, to the three charged row families used by the
postcharge target. -/
theorem
    selectorTailTarget_factorization_eq_upper_sub_fixed_sub_base_of_signedTargetLedger
    {c : Real} {depth n : Nat}
    (R : BankPaperRealization n
      (upperEndpoint n (upperTailLength c n)))
    (certificate : GuardedCentralAnchorCertificate c depth n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (deltaStar : Real) (p : Nat)
    (htarget : BankPaperCanonicalSignedResidualTargetLedger
      R certificate deltaStar p) :
    ((certificate.selectorTailTarget R
        (R.paperFixedExceptionalFactors deltaStar)).factorization p :
      Real) =
      (∑ a ∈ roughUpperBlock n (upperTailLength c n),
        (a.factorization p : Real)) -
      (∑ a ∈ R.paperFixedExceptionalFactors deltaStar,
        (a.factorization p : Real)) -
      ∑ a ∈ R.prechargeBaseState, (a.factorization p : Real) := by
  have hdisjoint :
      Disjoint (R.paperFixedExceptionalFactors deltaStar)
        (R.roughCanonicalExceptionalDonorSet deltaStar) := by
    rw [Finset.disjoint_left]
    intro a hfixed hdonor
    have hdonor' :=
      ((R.mem_roughCanonicalExceptionalDonorSet).1 hdonor).1
    exact (Finset.disjoint_left.mp
      (R.paperFixedExceptionalFactors_disjoint_prechargeDonorSet
        deltaStar)) hfixed hdonor'
  have hexceptionalSum :
      (∑ a ∈ paperExceptionalUpperFactors n
          (upperTailLength c n) deltaStar,
        (a.factorization p : Real)) =
      (∑ a ∈ R.paperFixedExceptionalFactors deltaStar,
        (a.factorization p : Real)) +
      ∑ a ∈ R.roughCanonicalExceptionalDonorSet deltaStar,
        (a.factorization p : Real) := by
    rw [paperExceptionalUpperFactors_eq_fixed_union_exceptionalDonors
      R deltaStar, Finset.sum_union hdisjoint]
  unfold BankPaperCanonicalSignedResidualTargetLedger at htarget
  rw [hexceptionalSum] at htarget
  linarith only [htarget]

/-- High-prime selector-tail closure from charged row totals. -/
theorem
    bankPaperCanonicalSelectorValuationDeficit_eq_zero_of_chargedRows_of_yNat_lt
    {c : Real} {depth n K : Nat}
    (R : BankPaperRealization n
      (upperEndpoint n (upperTailLength c n)))
    (certificate : GuardedCentralAnchorCertificate c depth n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (deltaStar : Real) (selector : Nat -> Real)
    (p : Nat) (hyp : yNat n < p)
    (hrows : BankPaperCanonicalChargedNonsmoothRowRealization
      (K := K) R certificate deltaStar selector)
    (hcapacity : forall label, IsCompleteRoughLabel (yNat n) label ->
      RoughCanonicalActiveNonexceptionalLabel n deltaStar label ->
        RoughCanonicalPostchargeRowCapacity R certificate deltaStar K label)
    (htarget : BankPaperCanonicalSignedResidualTargetLedger
      R certificate deltaStar p) :
    bankPaperCanonicalSelectorValuationDeficit R certificate
        (R.paperFixedExceptionalFactors deltaStar)
        (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
        selector p = 0 := by
  classical
  let candidates :=
    R.roughCanonicalGuardedCandidateSet certificate deltaStar K
  let labels :=
    bankPaperCanonicalChargedLabelSet (K := K) R certificate deltaStar
  have hupperLabels :
      completeRoughLabelSet (yNat n)
          (roughUpperBlock n (upperTailLength c n)) ⊆ labels := by
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
  have hcandidatesPartition :
      (∑ a ∈ candidates, selector a * (a.factorization p : Real)) =
        ∑ label ∈ labels,
          (∑ a ∈ completeRoughRowFiber (yNat n) candidates label,
              selector a) *
            (label.factorization p : Real) :=
    sum_mul_factorization_eq_sum_rowSum_mul_labelFactorization_of_labelSet_subset
      (yNat n) p candidates labels selector hyp hcandidateLabels
  have hupperPartition :
      (∑ a ∈ roughUpperBlock n (upperTailLength c n),
          (a.factorization p : Real)) =
        ∑ label ∈ labels,
          (roughUpperCompleteRoughRowTarget n
              (upperTailLength c n) (yNat n) label : Real) *
            (label.factorization p : Real) := by
    simpa [roughUpperCompleteRoughRowTarget, completeLabelMultiplicity,
      completeRoughRowFiber] using
      (sum_factorization_cast_eq_sum_completeLabelMultiplicity_mul_of_labelSet_subset
        (yNat n) p (roughUpperBlock n (upperTailLength c n))
          labels hyp hupperLabels)
  have hfixedPartition :
      (∑ a ∈ R.paperFixedExceptionalFactors deltaStar,
          (a.factorization p : Real)) =
        ∑ label ∈ labels,
          (completeLabelMultiplicity (yNat n)
              (R.paperFixedExceptionalFactors deltaStar) label : Real) *
            (label.factorization p : Real) :=
    sum_factorization_cast_eq_sum_completeLabelMultiplicity_mul_of_labelSet_subset
      (yNat n) p (R.paperFixedExceptionalFactors deltaStar)
        labels hyp hfixedLabels
  have hbasePartition :
      (∑ a ∈ R.prechargeBaseState, (a.factorization p : Real)) =
        ∑ label ∈ labels,
          (completeLabelMultiplicity (yNat n)
              R.prechargeBaseState label : Real) *
            (label.factorization p : Real) :=
    sum_factorization_cast_eq_sum_completeLabelMultiplicity_mul_of_labelSet_subset
      (yNat n) p R.prechargeBaseState labels hyp hbaseLabels
  have hrowMoment :
      (∑ label ∈ labels,
          (∑ a ∈ completeRoughRowFiber (yNat n) candidates label,
              selector a) *
            (label.factorization p : Real)) =
        ∑ label ∈ labels,
          R.roughCanonicalPostchargeRowTarget deltaStar label *
            (label.factorization p : Real) := by
    apply Finset.sum_congr rfl
    intro label hlabel
    by_cases hlabelOne : label = 1
    · subst label
      simp
    · have hrow :=
        sum_chargedSelector_eq_postchargeRowTarget_of_mem_labelSet_of_ne_one
          R certificate deltaStar selector hrows hcapacity
            (by simpa only [labels] using hlabel) hlabelOne
      exact
        (by
          simpa only [BankPaperRealization.roughCanonicalGuardedRow] using
            congrArg
              (fun x : Real => x * (label.factorization p : Real)) hrow)
  have htargetPartition :
      (∑ label ∈ labels,
          R.roughCanonicalPostchargeRowTarget deltaStar label *
            (label.factorization p : Real)) =
        (∑ a ∈ roughUpperBlock n (upperTailLength c n),
            (a.factorization p : Real)) -
          (∑ a ∈ R.paperFixedExceptionalFactors deltaStar,
            (a.factorization p : Real)) -
          ∑ a ∈ R.prechargeBaseState,
            (a.factorization p : Real) := by
    calc
      (∑ label ∈ labels,
          R.roughCanonicalPostchargeRowTarget deltaStar label *
            (label.factorization p : Real)) =
        (∑ label ∈ labels,
            (roughUpperCompleteRoughRowTarget n
                (upperTailLength c n) (yNat n) label : Real) *
              (label.factorization p : Real)) -
          (∑ label ∈ labels,
            (completeLabelMultiplicity (yNat n)
                (R.paperFixedExceptionalFactors deltaStar) label : Real) *
              (label.factorization p : Real)) -
          ∑ label ∈ labels,
            (completeLabelMultiplicity (yNat n)
                R.prechargeBaseState label : Real) *
              (label.factorization p : Real) := by
          simp only [roughCanonicalPostchargeRowTarget, sub_mul,
            Finset.sum_sub_distrib]
      _ = (∑ a ∈ roughUpperBlock n (upperTailLength c n),
              (a.factorization p : Real)) -
            (∑ a ∈ R.paperFixedExceptionalFactors deltaStar,
              (a.factorization p : Real)) -
            ∑ a ∈ R.prechargeBaseState,
              (a.factorization p : Real) := by
          rw [← hupperPartition, ← hfixedPartition, ← hbasePartition]
  have hselectorMoment :
      (∑ a ∈ candidates, selector a * (a.factorization p : Real)) =
        (∑ a ∈ roughUpperBlock n (upperTailLength c n),
            (a.factorization p : Real)) -
          (∑ a ∈ R.paperFixedExceptionalFactors deltaStar,
            (a.factorization p : Real)) -
          ∑ a ∈ R.prechargeBaseState,
            (a.factorization p : Real) := by
    rw [hcandidatesPartition, hrowMoment, htargetPartition]
  have htargetSimple :=
    selectorTailTarget_factorization_eq_upper_sub_fixed_sub_base_of_signedTargetLedger
      R certificate deltaStar p htarget
  unfold bankPaperCanonicalSelectorValuationDeficit
  simpa only [candidates] using
    sub_eq_zero.mpr (htargetSimple.trans hselectorMoment.symm)

/-! ## WithTop and rounded support wrappers -/





end BankPaperRealization

end

end Erdos390.WholePaper

end

theorem solution :
∀ {c : Real} {depth n K : Nat}
  (R :
    Erdos390.WholePaper.BankPaperRealization n
      (Erdos390.WholePaper.upperEndpoint n (Erdos390.WholePaper.upperTailLength c n)))
  (certificate :
    Erdos390.WholePaper.GuardedCentralAnchorCertificate c depth n
      (@Erdos390.WholePaper.BankPaperRealization.anchorGuardLeftCore n
        (Erdos390.WholePaper.upperEndpoint n (Erdos390.WholePaper.upperTailLength c n)) R)
      (@Erdos390.WholePaper.BankPaperRealization.anchorGuardRightCore n
        (Erdos390.WholePaper.upperEndpoint n (Erdos390.WholePaper.upperTailLength c n)) R)
      (@Erdos390.WholePaper.BankPaperRealization.centralChangedMarkers n
        (Erdos390.WholePaper.upperEndpoint n (Erdos390.WholePaper.upperTailLength c n)) R depth))
  (deltaStar : Real) (selector : Nat → Real) (p : Nat),
  @LT.lt.{0} Nat instLTNat (Erdos390.Full.ArithmeticModel.yNat n) p →
    @Erdos390.WholePaper.BankPaperCanonicalChargedNonsmoothRowRealization c depth n
        (Erdos390.WholePaper.upperTailLength c n) K
        (@Erdos390.WholePaper.BankPaperRealization.anchorGuardLeftCore n
          (Erdos390.WholePaper.upperEndpoint n (Erdos390.WholePaper.upperTailLength c n)) R)
        (@Erdos390.WholePaper.BankPaperRealization.anchorGuardRightCore n
          (Erdos390.WholePaper.upperEndpoint n (Erdos390.WholePaper.upperTailLength c n)) R)
        (@Erdos390.WholePaper.BankPaperRealization.centralChangedMarkers n
          (Erdos390.WholePaper.upperEndpoint n (Erdos390.WholePaper.upperTailLength c n)) R depth)
        R certificate deltaStar selector →
      (∀ (label : Nat),
          Erdos390.WholePaper.IsCompleteRoughLabel (Erdos390.Full.ArithmeticModel.yNat n) label →
            Erdos390.WholePaper.BankPaperRealization.RoughCanonicalActiveNonexceptionalLabel n deltaStar label →
              @Erdos390.WholePaper.BankPaperRealization.RoughCanonicalPostchargeRowCapacity c depth n
                (Erdos390.WholePaper.upperTailLength c n)
                (@Erdos390.WholePaper.BankPaperRealization.anchorGuardLeftCore n
                  (Erdos390.WholePaper.upperEndpoint n (Erdos390.WholePaper.upperTailLength c n)) R)
                (@Erdos390.WholePaper.BankPaperRealization.anchorGuardRightCore n
                  (Erdos390.WholePaper.upperEndpoint n (Erdos390.WholePaper.upperTailLength c n)) R)
                (@Erdos390.WholePaper.BankPaperRealization.centralChangedMarkers n
                  (Erdos390.WholePaper.upperEndpoint n (Erdos390.WholePaper.upperTailLength c n)) R depth)
                R certificate deltaStar K label) →
        @Erdos390.WholePaper.BankPaperRealization.BankPaperCanonicalSignedResidualTargetLedger c depth n R certificate
            deltaStar p →
          @Eq.{1} Real
            (@Erdos390.WholePaper.bankPaperCanonicalSelectorValuationDeficit c depth n
              (@Erdos390.WholePaper.BankPaperRealization.anchorGuardLeftCore n
                (Erdos390.WholePaper.upperEndpoint n (Erdos390.WholePaper.upperTailLength c n)) R)
              (@Erdos390.WholePaper.BankPaperRealization.anchorGuardRightCore n
                (Erdos390.WholePaper.upperEndpoint n (Erdos390.WholePaper.upperTailLength c n)) R)
              (@Erdos390.WholePaper.BankPaperRealization.centralChangedMarkers n
                (Erdos390.WholePaper.upperEndpoint n (Erdos390.WholePaper.upperTailLength c n)) R depth)
              R certificate
              (@Erdos390.WholePaper.BankPaperRealization.paperFixedExceptionalFactors n
                (Erdos390.WholePaper.upperTailLength c n) R deltaStar)
              (@Erdos390.WholePaper.BankPaperRealization.roughCanonicalGuardedCandidateSet c depth n
                (Erdos390.WholePaper.upperTailLength c n)
                (@Erdos390.WholePaper.BankPaperRealization.anchorGuardLeftCore n
                  (Erdos390.WholePaper.upperEndpoint n (Erdos390.WholePaper.upperTailLength c n)) R)
                (@Erdos390.WholePaper.BankPaperRealization.anchorGuardRightCore n
                  (Erdos390.WholePaper.upperEndpoint n (Erdos390.WholePaper.upperTailLength c n)) R)
                (@Erdos390.WholePaper.BankPaperRealization.centralChangedMarkers n
                  (Erdos390.WholePaper.upperEndpoint n (Erdos390.WholePaper.upperTailLength c n)) R depth)
                R certificate deltaStar K)
              selector p)
            (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) := by
  exact @Erdos390.WholePaper.BankPaperRealization.bankPaperCanonicalSelectorValuationDeficit_eq_zero_of_chargedRows_of_yNat_lt
