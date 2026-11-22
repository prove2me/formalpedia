-- Prove2me | solution 1 for Erdos390.WholePaper.BankPaperRealization.bankPaperCanonicalSignedResidualTargetLedger_of_chargeDvd
-- status  : ACCEPTED   (prove)
-- author  : @doctosil
-- created : 2026-09-17T15:54:22.078813+00:00
-- url     : https://prove2.me/submissions/ff6ed339-53a5-4103-b9fb-86b7943f151a

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
import Definitions.Def_erdos390_analytic_foundations_009

/- Source module: Erdos390.WholePaper.CentralAnchorDivisorSupport -/
section


/-!
# Prime support and valuations of the central-anchor divisor

The exact anchor product introduces only the promotion power of two and the
chosen carry cofactors.  This file makes that assertion literal at every
prime, so later allocation estimates can be applied directly to the actual
integer divisor.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

noncomputable section

theorem routedCentralCofactor_pos
    {n p q : ℕ} (hq : IsRoutedCentralCofactor n p q) : 0 < q := by
  rcases hq with hzero | ⟨r, _hrPos, _hr, _hpRow, hqLower, _hqUpper⟩
  · omega
  · omega

theorem largeCentralCofactor_pos
    {n X : ℕ} {q : ℕ → ℕ}
    (hq : IsLargeCentralCofactorChoice n X q)
    {p : ℕ} (hp : p ∈ largeCentralPrimes n X) :
    0 < q p :=
  routedCentralCofactor_pos (hq p hp)

theorem largeCentralCofactorProduct_pos
    {n X : ℕ} {q : ℕ → ℕ}
    (hq : IsLargeCentralCofactorChoice n X q) :
    0 < largeCentralCofactorProduct n X q := by
  exact Finset.prod_pos fun p hp ↦ largeCentralCofactor_pos hq hp

theorem centralAnchorDivisor_pos
    {n X : ℕ} {q : ℕ → ℕ}
    (hq : IsLargeCentralCofactorChoice n X q) :
    0 < centralAnchorDivisor n X q := by
  exact mul_pos (pow_pos (by norm_num : 0 < (2 : ℕ)) _)
    (largeCentralCofactorProduct_pos hq)







end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.CentralAnchorTailDivisibility -/
section


/-!
# From central-anchor valuation reserve to literal tail divisibility

The analytic part of the central-anchor argument produces inequalities at a
fixed finite set of primes.  This file supplies the exact arithmetic bridge:
the factorial-tail valuation is the valuation of the literal tail product,
and bounds on the finite support of the anchor divisor imply actual natural-
number divisibility.
-/

namespace Erdos390.WholePaper

noncomputable section

/-- The literal tail product is positive, including when the tail is empty. -/
theorem centralTailProduct_pos (n h : ℕ) : 0 < centralTailProduct n h := by
  exact Finset.prod_pos fun a ha ↦ by
    have haMem : a ∈ Finset.Ioc (2 * n) (2 * n + h) := ha
    exact Nat.zero_lt_of_lt (Finset.mem_Ioc.mp haMem).1















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





























theorem componentOccurrence_mem_factorInterval
    (hTwoN : 2 * n ≤ M)
    (request : ↑(bankBottomPaperRequests n))
    {occurrence : ℕ}
    (hoccurrence : occurrence ∈ realization.componentOccurrences request) :
    occurrence ∈ factorInterval n M := by
  rw [realization.componentOccurrences_eq_states_insert_donor request]
    at hoccurrence
  simp only [Finset.mem_insert, Finset.mem_singleton] at hoccurrence
  have hinterval := realization.states_donor_mem_factorInterval hTwoN request
  rcases hoccurrence with hoccurrence | hoccurrence | hoccurrence
  · simpa only [hoccurrence] using hinterval.1
  · simpa only [hoccurrence] using hinterval.2.1
  · simpa only [hoccurrence] using hinterval.2.2

























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



































private theorem stateValues_mem_factorInterval
    {n M : ℕ} (R : BankOrdinaryPaperRealization n M)
    (request : ↑(bankOrdinaryPaperRequests n)) :
    R.sourceStateValue request ∈ factorInterval n M ∧
      R.targetStateValue request ∈ factorInterval n M := by
  have heligible := mem_bankOrdinaryEligibleRelation.mp
    (R.markerDonorPair_mem request)
  have hspec := bankOrdinaryPaperRequest_component_spec request.1
  let P := R.marker request
  let q := bankOrdinaryPaperRequestSource request.1
  let b := bankOrdinaryPaperRequestTarget request.1
  let Q := bankOrdinaryScale
    (bankOrdinaryPaperRequestPool n request.1).1
  have hPpos : (0 : ℚ) < P := by
    exact_mod_cast (R.marker_prime request).pos
  have hPnonneg : (0 : ℚ) ≤ P := hPpos.le
  have hmarker := heligible.2.2.2.1
  have hcell := hspec.2.2.2.2.2.2
  change 4 * (n : ℚ) < 3 * Q * P ∧
    2 * Q * P ≤ 3 * (n : ℚ) at hmarker
  change (Q < (q : ℚ) ∧ (q : ℚ) ≤ 4 * Q / 3) ∧
    3 * Q / 4 < (b : ℚ) at hcell
  have hQq := mul_lt_mul_of_pos_left hcell.1.1
    hPpos
  have hqUpper := mul_le_mul_of_nonneg_left hcell.1.2 hPnonneg
  have hbLower := mul_lt_mul_of_pos_left hcell.2
    hPpos
  have hmarkerLower := hmarker.1
  have hmarkerUpper := hmarker.2
  have hsourceLowerQ : (n : ℚ) < P * q := by
    nlinarith [hmarkerLower, hQq]
  have htargetLowerQ : (n : ℚ) < P * b := by
    nlinarith [hmarkerLower, hbLower]
  have hcellSourceUpper : P * (4 * Q / 3) ≤ 2 * (n : ℚ) := by
    have hscaled := mul_le_mul_of_nonneg_left hmarkerUpper
      (by norm_num : (0 : ℚ) ≤ 2 / 3)
    convert hscaled using 1 <;> ring
  have hsourceUpperQ : P * q ≤ 2 * (n : ℚ) := by
    exact hqUpper.trans hcellSourceUpper
  have hsourceLower : n < P * q := by exact_mod_cast hsourceLowerQ
  have htargetLower : n < P * b := by exact_mod_cast htargetLowerQ
  have hsourceUpper : P * q ≤ M := by
    have : P * q ≤ 2 * n := by exact_mod_cast hsourceUpperQ
    exact this.trans R.two_mul_n_le_M
  have htargetUpper : P * b ≤ M := by
    have hbq : b ≤ q := hspec.2.2.2.2.1.le
    exact (Nat.mul_le_mul_left P hbq).trans hsourceUpper
  simp only [sourceStateValue, targetStateValue, factorInterval,
    Finset.mem_Ioc]
  exact ⟨⟨hsourceLower, hsourceUpper⟩,
    ⟨htargetLower, htargetUpper⟩⟩

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



























theorem componentOccurrence_mem_factorInterval
    {n M : ℕ} (R : BankOrdinaryPaperRealization n M)
    (request : ↑(bankOrdinaryPaperRequests n))
    {occurrence : ℕ}
    (hoccurrence : occurrence ∈ R.componentOccurrences request) :
    occurrence ∈ factorInterval n M := by
  rw [componentOccurrences, Finset.mem_image] at hoccurrence
  obtain ⟨kind, _hkind, hvalue⟩ := hoccurrence
  cases kind
  · simpa only [← hvalue, occurrenceValue_sourceState] using
      (R.stateValues_mem_factorInterval request).1
  · simpa only [← hvalue, occurrenceValue_targetState] using
      (R.stateValues_mem_factorInterval request).2
  · simpa only [← hvalue, occurrenceValue_donor] using
      R.donorValue_mem_factorInterval request





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

















/-- Every named occurrence of every component lies in the factor interval. -/
theorem prechargeComponentOccurrence_mem_factorInterval
    {n M : ℕ} (R : BankPaperRealization n M)
    (request : BankPaperMarkerRequest n) {occurrence : ℕ}
    (hoccurrence : occurrence ∈
      R.prechargeComponentOccurrences request) :
    occurrence ∈ factorInterval n M := by
  cases request with
  | inl request =>
      exact R.bottom.componentOccurrence_mem_factorInterval
        R.ordinary.two_mul_n_le_M
        (bankBottomRelevantRequestToPaperRequest request) hoccurrence
  | inr request =>
      exact R.ordinary.componentOccurrence_mem_factorInterval
        request hoccurrence

theorem prechargeBaseStateValue_mem_factorInterval
    {n M : ℕ} (R : BankPaperRealization n M)
    (request : BankPaperMarkerRequest n) :
    R.prechargeBaseStateValue request ∈ factorInterval n M :=
  R.prechargeComponentOccurrence_mem_factorInterval request
    (R.prechargeBaseStateValue_mem_componentOccurrences request)





/-! ## Complete rough signatures -/







/-! ## Endpoint and donor injectivity -/





















/-! ## Literal finite states, donor tail, and replacement map -/





















theorem prechargeBaseState_subset_factorInterval
    {n M : ℕ} (R : BankPaperRealization n M) :
    R.prechargeBaseState ⊆ factorInterval n M := by
  intro value hvalue
  rw [prechargeBaseState, indexedPathState, Finset.mem_image] at hvalue
  obtain ⟨request, _hrequest, rfl⟩ := hvalue
  exact R.prechargeBaseStateValue_mem_factorInterval request



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

/- Source module: Erdos390.WholePaper.BankPaperExactificationState -/
section


/-!
# The actual paper bank as a two-state exactification bank

`BankPaperPaths` orients a downward slot from state zero to state one, so its
change is `-e_p`; the generic exactification interface instead calls the
left-hand signed family `+e_p`.  We therefore pair each generic slot with the
actual slot of the opposite orientation.  Boolean state `false` remains the
paper's precharged path state zero and state `true` remains path state one.
This simultaneously aligns signs and keeps the base product equal to the
one reserved in the tail.  The file proves the required product change,
complete-row invariance, positivity, and pairwise cross-slot disjointness.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel

noncomputable section



@[simp] theorem bankPaperOppositeSlot_fst
    {P : Type*} {beta : P → ℕ} (slot : SignedBankSlot beta) :
    (bankPaperOppositeSlot slot).1 = slot.1 := by
  rcases slot with ⟨p, copy | copy⟩ <;> rfl

@[simp] theorem bankPaperOppositeSlot_involutive
    {P : Type*} {beta : P → ℕ} (slot : SignedBankSlot beta) :
    bankPaperOppositeSlot (bankPaperOppositeSlot slot) = slot := by
  rcases slot with ⟨p, copy | copy⟩ <;> rfl







@[simp] theorem BankPaperRealization.exactificationState_false
    {n M : ℕ} (R : BankPaperRealization n M)
    (slot : SignedBankSlot (bankRoundingBetaOnSupport n)) :
    R.exactificationState slot false =
      R.pathStateZero (bankPaperOppositeSlot slot) := by
  simp [BankPaperRealization.exactificationState]

@[simp] theorem BankPaperRealization.exactificationState_true
    {n M : ℕ} (R : BankPaperRealization n M)
    (slot : SignedBankSlot (bankRoundingBetaOnSupport n)) :
    R.exactificationState slot true =
      R.pathStateOne (bankPaperOppositeSlot slot) := by
  simp [BankPaperRealization.exactificationState]



namespace BankPaperRealization



















end BankPaperRealization

end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankPaperPrechargeExactificationBridge -/
section


/-!
# Identification of the precharged state with the exactification base bank

The concrete precharge layer indexes components by the global request type,
whereas guarded exactification takes the union of state zero over signed bank
slots.  These are two presentations of the same finite set.  The opposite-slot
reindexing used to align signed valuation changes is an involution, so it does
not alter the global state-zero union.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel

noncomputable section



/-- Every relevant bottom request and every ordinary request occurs in its
unique signed-slot path. -/
theorem bankPaperIndexedPathComponentRequest_surjective {n : ℕ} :
    Function.Surjective
      (bankPaperIndexedPathComponentRequest (n := n)) := by
  intro request
  cases request with
  | inl request =>
      have hmove : request.1.2 ∈
          bankBottomRelevantMoves request.1.1.1 := by
        apply (bankBottomPaperRequestRelevant_iff_mem_moves request.1).mp
        exact (Finset.mem_filter.mp request.property).2
      let move : ↑(bankBottomRelevantMoves request.1.1.1) :=
        ⟨request.1.2, hmove⟩
      refine ⟨⟨request.1.1, Sum.inr move⟩, ?_⟩
      apply congrArg Sum.inl
      apply Subtype.ext
      rfl
  | inr request =>
      refine ⟨⟨request.1.1, Sum.inl request.1.2⟩, ?_⟩
      apply congrArg Sum.inr
      apply Subtype.ext
      rfl

namespace BankPaperRealization

/-- State zero of one actual path component is exactly the orientation-aware
precharge value of its global request. -/
@[simp] theorem pathStateZeroValue_eq_prechargeBaseStateValue
    {n M : ℕ} (R : BankPaperRealization n M)
    (slot : SignedBankSlot (bankRoundingBetaOnSupport n))
    (component : BankPaperPathComponent slot) :
    R.pathStateZeroValue slot component =
      R.prechargeBaseStateValue
        (bankPaperPathComponentRequest slot component) := by
  cases component <;> rfl

/-- The generic exactification base bank is literally the paper's precharged
base state.  The orientation swap only permutes the signed slots. -/
theorem baseExactificationBank_eq_prechargeBaseState
    {n M : ℕ} (R : BankPaperRealization n M) :
    baseBankFactors R.exactificationState = R.prechargeBaseState := by
  classical
  ext factor
  constructor
  · intro hfactor
    rw [baseBankFactors, chosenBankFactors, Finset.mem_biUnion] at hfactor
    obtain ⟨slot, _hslot, hstate⟩ := hfactor
    rw [R.exactificationState_false, pathStateZero, indexedPathState,
      Finset.mem_image] at hstate
    obtain ⟨component, _hcomponent, hvalue⟩ := hstate
    rw [prechargeBaseState, indexedPathState, Finset.mem_image]
    refine ⟨bankPaperPathComponentRequest
      (bankPaperOppositeSlot slot) component, Finset.mem_univ _, ?_⟩
    exact (R.pathStateZeroValue_eq_prechargeBaseStateValue
      (bankPaperOppositeSlot slot) component).symm.trans hvalue
  · intro hfactor
    rw [prechargeBaseState, indexedPathState, Finset.mem_image] at hfactor
    obtain ⟨request, _hrequest, hvalue⟩ := hfactor
    obtain ⟨⟨slot, component⟩, hrequestIndex⟩ :=
      bankPaperIndexedPathComponentRequest_surjective request
    rw [← hrequestIndex] at hvalue
    have hcomponentValue :
        R.pathStateZeroValue slot component = factor := by
      exact (R.pathStateZeroValue_eq_prechargeBaseStateValue
        slot component).trans hvalue
    have hstate : factor ∈ R.pathStateZero slot := by
      rw [pathStateZero, indexedPathState, Finset.mem_image]
      exact ⟨component, Finset.mem_univ _, hcomponentValue⟩
    have hstateOpposite : factor ∈
        R.exactificationState (bankPaperOppositeSlot slot) false := by
      simpa only [R.exactificationState_false,
        bankPaperOppositeSlot_involutive] using hstate
    rw [baseBankFactors, chosenBankFactors, Finset.mem_biUnion]
    exact ⟨bankPaperOppositeSlot slot, Finset.mem_univ _, hstateOpposite⟩

/-- Product form of the literal base-state identification. -/
theorem baseExactificationBank_prod_eq_prechargeBaseStateProduct
    {n M : ℕ} (R : BankPaperRealization n M) :
    (baseBankFactors R.exactificationState).prod id =
      R.prechargeBaseStateProduct := by
  rw [R.baseExactificationBank_eq_prechargeBaseState]
  rfl





end BankPaperRealization

end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankPaperPrechargedTailTarget -/
section


/-!
# The residual target after the guarded anchor charge

This file names the exact natural-number target passed to fractional
selection and guarded exactification.  Combined divisibility of the guarded
anchor divisor and the precharged bank immediately shows that the generic
exactification base product divides this target.  The final multiplication
identity is division-free.
-/

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel

noncomputable section

namespace GuardedCentralAnchorCertificate



/-- The quotient target is positive. -/
theorem prechargedTailTarget_pos
    {c : ℝ} {depth n : ℕ} {left right : ℕ → ℕ}
    {changed : Finset ℕ}
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed) :
    0 < certificate.prechargedTailTarget := by
  apply Nat.div_pos
  · exact Nat.le_of_dvd
      (centralTailProduct_pos n (upperTailLength c n))
      certificate.divisor_dvd_tail
  · exact centralAnchorDivisor_pos certificate.isCofactorChoice

/-- Division-free target identity used by final product assembly. -/
theorem prechargedTailTarget_mul_centralAnchorDivisor
    {c : ℝ} {depth n : ℕ} {left right : ℕ → ℕ}
    {changed : Finset ℕ}
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed) :
    certificate.prechargedTailTarget *
        centralAnchorDivisor n (centralAnchorCutoff depth n) certificate.q =
      centralTailProduct n (upperTailLength c n) := by
  exact Nat.div_mul_cancel certificate.divisor_dvd_tail





end GuardedCentralAnchorCertificate

end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankPaperSelectorTailTarget -/
section


/-!
# The residual selector target after all base charges

The guarded central anchors are charged before `prechargedTailTarget` is
formed.  Fractional selection starts only after an independently fixed
factor set and the literal state-zero exactification bank have also been
charged.  This file names that second quotient and records the exact
division-free and valuation interfaces used by the post-tangent
certificate.
-/

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel

noncomputable section

namespace BankPaperRealization



/-- The generic exactification notation for the selector charge is exactly
the concrete precharged bank product. -/
theorem selectorTailCharge_eq_fixed_mul_prechargeBaseStateProduct
    {n M : ℕ} (R : BankPaperRealization n M)
    (fixed : Finset ℕ) :
    R.selectorTailCharge fixed =
      fixed.prod id * R.prechargeBaseStateProduct := by
  rw [selectorTailCharge,
    R.baseExactificationBank_prod_eq_prechargeBaseStateProduct]

/-- Positivity of the selector charge follows from positivity of the
caller's fixed factors and interval positivity of every actual precharged
bank factor. -/
theorem selectorTailCharge_pos
    {n M : ℕ} (R : BankPaperRealization n M)
    (fixed : Finset ℕ)
    (hfixedPositive : ∀ a ∈ fixed, 0 < a) :
    0 < R.selectorTailCharge fixed := by
  rw [R.selectorTailCharge_eq_fixed_mul_prechargeBaseStateProduct]
  apply Nat.mul_pos
  · exact Finset.prod_pos fun a ha ↦ by
      simpa only [id_eq] using hfixedPositive a ha
  · rw [prechargeBaseStateProduct]
    apply Finset.prod_pos
    intro factor hfactor
    have hinterval := R.prechargeBaseState_subset_factorInterval hfactor
    exact Nat.zero_lt_of_lt (Finset.mem_Ioc.mp hinterval).1

end BankPaperRealization

namespace GuardedCentralAnchorCertificate



/-- A positive divisor of the positive precharged tail leaves a positive
selector target. -/
theorem selectorTailTarget_pos
    {c : ℝ} {depth n : ℕ} {left right : ℕ → ℕ}
    {changed : Finset ℕ}
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (R : BankPaperRealization n
      (upperEndpoint n (upperTailLength c n)))
    (fixed : Finset ℕ)
    (hfixedPositive : ∀ a ∈ fixed, 0 < a)
    (hchargeDvd : R.selectorTailCharge fixed ∣
      certificate.prechargedTailTarget) :
    0 < certificate.selectorTailTarget R fixed := by
  apply Nat.div_pos
  · exact Nat.le_of_dvd certificate.prechargedTailTarget_pos hchargeDvd
  · exact R.selectorTailCharge_pos fixed hfixedPositive

/-- Division-free recovery of the precharged tail from the residual
selector target and its complete base charge. -/
theorem selectorTailTarget_mul_selectorTailCharge
    {c : ℝ} {depth n : ℕ} {left right : ℕ → ℕ}
    {changed : Finset ℕ}
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (R : BankPaperRealization n
      (upperEndpoint n (upperTailLength c n)))
    (fixed : Finset ℕ)
    (hchargeDvd : R.selectorTailCharge fixed ∣
      certificate.prechargedTailTarget) :
    certificate.selectorTailTarget R fixed *
        R.selectorTailCharge fixed =
      certificate.prechargedTailTarget := by
  rw [selectorTailTarget]
  exact Nat.div_mul_cancel hchargeDvd





end GuardedCentralAnchorCertificate

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

















end BankPaperRealization

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

/-- At a medium prime the central anchor divisor has zero valuation, and
the two quotient charges expand to the exact target ledger. -/
theorem bankPaperCanonicalSignedResidualTargetLedger_of_chargeDvd
    {c : Real} {depth n W p : Nat}
    (R : BankPaperRealization n
      (upperEndpoint n (upperTailLength c n)))
    (certificate : GuardedCentralAnchorCertificate c depth n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (deltaStar : Real)
    (hprefix : 2 * depth + 1 <= W)
    (hp : p.Prime) (hWp : W < p)
    (hchargeDvd :
      R.selectorTailCharge (R.paperFixedExceptionalFactors deltaStar) ∣
        certificate.prechargedTailTarget) :
    BankPaperCanonicalSignedResidualTargetLedger
      R certificate deltaStar p := by
  let h := upperTailLength c n
  let fixed := R.paperFixedExceptionalFactors deltaStar
  let exceptional := paperExceptionalUpperFactors n h deltaStar
  let exceptionalDonors :=
    R.roughCanonicalExceptionalDonorSet deltaStar
  let divisor :=
    centralAnchorDivisor n (centralAnchorCutoff depth n) certificate.q
  let charge := R.selectorTailCharge fixed
  let target := certificate.selectorTailTarget R fixed
  have hchargeDvd' :
      charge ∣ certificate.prechargedTailTarget := by
    simpa only [charge, fixed] using hchargeDvd
  have hfixedPositive : ∀ a ∈ fixed, 0 < a := by
    intro a ha
    have htail := R.paperFixedExceptionalFactors_subset_tail deltaStar ha
    exact Nat.zero_lt_of_lt (Finset.mem_Ioc.mp htail).1
  have hbasePositive : 0 < R.prechargeBaseStateProduct := by
    unfold prechargeBaseStateProduct
    apply Finset.prod_pos
    intro a ha
    have hinterval := R.prechargeBaseState_subset_factorInterval ha
    exact Nat.zero_lt_of_lt (Finset.mem_Ioc.mp hinterval).1
  have hfixedProdPositive : 0 < fixed.prod id := by
    apply Finset.prod_pos
    intro a ha
    simpa only [id_eq] using hfixedPositive a ha
  have hchargePositive : 0 < charge := by
    dsimp only [charge]
    exact R.selectorTailCharge_pos fixed hfixedPositive
  have htargetPositive : 0 < target := by
    dsimp only [target]
    exact certificate.selectorTailTarget_pos
      R fixed hfixedPositive hchargeDvd'
  have hdivisorPositive : 0 < divisor := by
    dsimp only [divisor]
    exact centralAnchorDivisor_pos certificate.isCofactorChoice
  have hprechargedPositive : 0 < certificate.prechargedTailTarget :=
    certificate.prechargedTailTarget_pos
  have hdivisorZero : divisor.factorization p = 0 := by
    apply Nat.factorization_eq_zero_of_not_dvd
    intro hpDvd
    have hpSupport := certificate.divisor_prime_support p hp
      (by simpa only [divisor] using hpDvd)
    have hpLe : p <= 2 * depth + 1 :=
      (mem_primesUpTo.mp hpSupport).2
    omega
  have hprechargedFactorization :
      certificate.prechargedTailTarget.factorization p =
        (centralTailProduct n h).factorization p := by
    have hproduct := congrArg (fun z : Nat => z.factorization p)
      certificate.prechargedTailTarget_mul_centralAnchorDivisor
    change
      (certificate.prechargedTailTarget * divisor).factorization p =
        (centralTailProduct n h).factorization p at hproduct
    rw [Nat.factorization_mul hprechargedPositive.ne'
      hdivisorPositive.ne', Finsupp.add_apply, hdivisorZero,
      add_zero] at hproduct
    exact hproduct
  have htargetFactorization :
      target.factorization p + charge.factorization p =
        certificate.prechargedTailTarget.factorization p := by
    have hproduct := congrArg (fun z : Nat => z.factorization p)
      (certificate.selectorTailTarget_mul_selectorTailCharge
        R fixed hchargeDvd')
    change
      (target * charge).factorization p =
        certificate.prechargedTailTarget.factorization p at hproduct
    simpa only [Nat.factorization_mul htargetPositive.ne'
      hchargePositive.ne', Finsupp.add_apply] using hproduct
  have hchargeFactorization :
      charge.factorization p =
        (fixed.prod id).factorization p +
          R.prechargeBaseStateProduct.factorization p := by
    dsimp only [charge]
    rw [R.selectorTailCharge_eq_fixed_mul_prechargeBaseStateProduct,
      Nat.factorization_mul hfixedProdPositive.ne'
        hbasePositive.ne', Finsupp.add_apply]
  have htailFactorization :
      ((centralTailProduct n h).factorization p : Real) =
        ∑ a ∈ roughUpperBlock n h, (a.factorization p : Real) := by
    have hnat :
        (centralTailProduct n h).factorization p =
          ∑ a ∈ roughUpperBlock n h, a.factorization p := by
      unfold centralTailProduct roughUpperBlock factorInterval
      rw [Nat.factorization_prod_apply]
      · simp only [id_eq]
      · intro a ha
        exact (Nat.zero_lt_of_lt (Finset.mem_Ioc.mp ha).1).ne'
    exact_mod_cast hnat
  have hfixedFactorization :
      ((fixed.prod id).factorization p : Real) =
        ∑ a ∈ fixed, (a.factorization p : Real) := by
    have hnat :
        (fixed.prod id).factorization p =
          ∑ a ∈ fixed, a.factorization p :=
      Nat.factorization_prod_apply
        (fun a ha => (hfixedPositive a ha).ne')
    exact_mod_cast hnat
  have hbaseFactorization :
      (R.prechargeBaseStateProduct.factorization p : Real) =
        ∑ a ∈ R.prechargeBaseState, (a.factorization p : Real) := by
    have hnat :
        R.prechargeBaseStateProduct.factorization p =
          ∑ a ∈ R.prechargeBaseState, a.factorization p := by
      unfold prechargeBaseStateProduct
      rw [Nat.factorization_prod_apply]
      · simp only [id_eq]
      · intro a ha
        have hinterval := R.prechargeBaseState_subset_factorInterval ha
        exact (Nat.zero_lt_of_lt (Finset.mem_Ioc.mp hinterval).1).ne'
    exact_mod_cast hnat
  have hfixedExceptionalDisjoint :
      Disjoint fixed exceptionalDonors := by
    rw [Finset.disjoint_left]
    intro a hfixedA hexceptionalDonor
    have hdonorA :=
      ((R.mem_roughCanonicalExceptionalDonorSet).1
        hexceptionalDonor).1
    exact (Finset.disjoint_left.mp
      (R.paperFixedExceptionalFactors_disjoint_prechargeDonorSet
        deltaStar)) hfixedA hdonorA
  have hexceptionalPartition :
      exceptional = fixed ∪ exceptionalDonors := by
    dsimp only [exceptional, fixed, exceptionalDonors]
    exact
      paperExceptionalUpperFactors_eq_fixed_union_exceptionalDonors
        R deltaStar
  have hexceptionalSum :
      (∑ a ∈ exceptional, (a.factorization p : Real)) =
        (∑ a ∈ fixed, (a.factorization p : Real)) +
          ∑ a ∈ exceptionalDonors, (a.factorization p : Real) := by
    rw [hexceptionalPartition,
      Finset.sum_union hfixedExceptionalDisjoint]
  unfold BankPaperCanonicalSignedResidualTargetLedger
  change
    (target.factorization p : Real) =
      (∑ a ∈ roughUpperBlock n h, (a.factorization p : Real)) -
      (∑ a ∈ exceptional, (a.factorization p : Real)) +
      (∑ a ∈ exceptionalDonors, (a.factorization p : Real)) -
      ∑ a ∈ R.prechargeBaseState, (a.factorization p : Real)
  have htargetFactorizationReal :
      (target.factorization p : Real) +
          (charge.factorization p : Real) =
        (certificate.prechargedTailTarget.factorization p : Real) := by
    exact_mod_cast htargetFactorization
  have hchargeFactorizationReal :
      (charge.factorization p : Real) =
        ((fixed.prod id).factorization p : Real) +
          (R.prechargeBaseStateProduct.factorization p : Real) := by
    exact_mod_cast hchargeFactorization
  rw [hprechargedFactorization] at htargetFactorizationReal
  rw [htailFactorization, hchargeFactorizationReal,
    hfixedFactorization, hbaseFactorization] at htargetFactorizationReal
  rw [hexceptionalSum]
  linarith only [htargetFactorizationReal]

/-! ## Four-term identification and structured transport -/













/-! ## The literal Post-Hfit pre-selector -/



























end BankPaperRealization

end

end Erdos390.WholePaper

end

theorem solution :
∀ {c : Real} {depth n W p : Nat}
  (R :
    Erdos390.WholePaper.BankPaperRealization n
      (Erdos390.WholePaper.upperEndpoint n (Erdos390.WholePaper.upperTailLength c n)))
  (certificate :
    Erdos390.WholePaper.GuardedCentralAnchorCertificate c depth n
      (Erdos390.WholePaper.BankPaperRealization.anchorGuardLeftCore R)
      (Erdos390.WholePaper.BankPaperRealization.anchorGuardRightCore R)
      (Erdos390.WholePaper.BankPaperRealization.centralChangedMarkers R depth))
  (deltaStar : Real),
  LE.le.{0} (HAdd.hAdd.{0, 0, 0} (HMul.hMul.{0, 0, 0} (2 : Nat) depth) (1 : Nat)) W →
    Nat.Prime p →
      LT.lt.{0} W p →
        Dvd.dvd.{0}
            (Erdos390.WholePaper.BankPaperRealization.selectorTailCharge R
              (Erdos390.WholePaper.BankPaperRealization.paperFixedExceptionalFactors R deltaStar))
            (Erdos390.WholePaper.GuardedCentralAnchorCertificate.prechargedTailTarget certificate) →
          Erdos390.WholePaper.BankPaperRealization.BankPaperCanonicalSignedResidualTargetLedger R certificate deltaStar
            p := by
  exact @Erdos390.WholePaper.BankPaperRealization.bankPaperCanonicalSignedResidualTargetLedger_of_chargeDvd
