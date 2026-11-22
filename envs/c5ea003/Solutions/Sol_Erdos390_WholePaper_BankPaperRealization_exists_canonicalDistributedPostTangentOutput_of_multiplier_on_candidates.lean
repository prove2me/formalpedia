-- Prove2me | solution 1 for Erdos390.WholePaper.BankPaperRealization.exists_canonicalDistributedPostTangentOutput_of_multiplier_on_candidates
-- status  : ACCEPTED   (prove)
-- author  : @doctosil
-- created : 2026-09-17T15:54:08.511231+00:00
-- url     : https://prove2.me/submissions/00762258-af24-473d-9d16-40e2f04228d4

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







/-- Exact coordinatewise valuation subtraction for the residual selector
target.  The subtraction is natural truncated subtraction, with
divisibility supplying the required coordinatewise inequality. -/
theorem selectorTailTarget_factorization_eq_sub
    {c : ℝ} {depth n : ℕ} {left right : ℕ → ℕ}
    {changed : Finset ℕ}
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (R : BankPaperRealization n
      (upperEndpoint n (upperTailLength c n)))
    (fixed : Finset ℕ)
    (hchargeDvd : R.selectorTailCharge fixed ∣
      certificate.prechargedTailTarget)
    (q : ℕ) :
    (certificate.selectorTailTarget R fixed).factorization q =
      certificate.prechargedTailTarget.factorization q -
        (R.selectorTailCharge fixed).factorization q := by
  rw [selectorTailTarget]
  simpa only [Finsupp.sub_apply] using
    congrArg (fun factorization : ℕ →₀ ℕ ↦ factorization q)
      (Nat.factorization_div hchargeDvd)

/-- The post-tangent valuation certificate can equivalently be stated with
all fixed and base-bank valuations removed from its target.  This is an
exact equivalence for an arbitrary real-valued selector ledger. -/
theorem valuationCertificate_iff_selectorTailTarget
    {c : ℝ} {depth n : ℕ} {left right : ℕ → ℕ}
    {changed : Finset ℕ}
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (R : BankPaperRealization n
      (upperEndpoint n (upperTailLength c n)))
    (fixed : Finset ℕ) (weighted : ℕ → ℝ)
    (hfixedPositive : ∀ a ∈ fixed, 0 < a)
    (hchargeDvd : R.selectorTailCharge fixed ∣
      certificate.prechargedTailTarget) :
    (∀ q,
      ((fixed.prod id *
          (baseBankFactors R.exactificationState).prod id).factorization q :
            ℝ) + weighted q =
        (certificate.prechargedTailTarget.factorization q : ℝ)) ↔
      (∀ q, weighted q =
        ((certificate.selectorTailTarget R fixed).factorization q : ℝ)) := by
  have hchargePos : 0 < R.selectorTailCharge fixed :=
    R.selectorTailCharge_pos fixed hfixedPositive
  have hchargeLe : ∀ q,
      (R.selectorTailCharge fixed).factorization q ≤
        certificate.prechargedTailTarget.factorization q :=
    (Nat.factorization_le_iff_dvd hchargePos.ne'
      certificate.prechargedTailTarget_pos.ne').mpr hchargeDvd
  constructor
  · intro hcharged q
    have hchargedQ :
        ((R.selectorTailCharge fixed).factorization q : ℝ) + weighted q =
          (certificate.prechargedTailTarget.factorization q : ℝ) := by
      simpa only [BankPaperRealization.selectorTailCharge] using hcharged q
    rw [certificate.selectorTailTarget_factorization_eq_sub
      R fixed hchargeDvd q, Nat.cast_sub (hchargeLe q)]
    linarith
  · intro hresidual q
    have hresidualQ := hresidual q
    rw [certificate.selectorTailTarget_factorization_eq_sub
      R fixed hchargeDvd q, Nat.cast_sub (hchargeLe q)] at hresidualQ
    change ((R.selectorTailCharge fixed).factorization q : ℝ) +
      weighted q =
        (certificate.prechargedTailTarget.factorization q : ℝ)
    linarith

end GuardedCentralAnchorCertificate

end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.TangentCommonMultiplierLists -/
section


/-!
# Finite common-multiplier lists for the tangent absorber

This file begins the literal common-list construction of Section 9.  It
defines the integer interval

`(n / v, (2 * n - K * h) / u]`

and applies exactly the five tests appearing in the paper: head
coprimality, the exceptional-row cutoff, exclusion of dedicated rows, and
the two numerical endpoint guards.  The resulting list is finite by
construction.

The uniform positive-density lower bound still needs the paper's reduced
residue-class count and exceptional-row Selberg-sieve estimate.  Everything
around those two analytic inputs is proved here: endpoint location, the
complete-rough-row identity, the exact finite deletion ledger, and the
paper's combinatorial fact that an exhaustive guard set deletes at most two
multipliers per guard.
-/

namespace Erdos390.WholePaper

noncomputable section

/-! ## Literal interval and cleanliness predicates -/



























/-! ## Endpoint location and complete rough rows -/



/-- Multiplying by a positive integer at most the cutoff changes no
prime-power coordinate above the cutoff. -/
theorem completeRoughSignature_small_left_mul
    {y label a : ℕ} (hlabel : 0 < label) (hlabelLe : label ≤ y)
    (ha : 0 < a) :
    completeRoughSignature y (label * a) =
      completeRoughSignature y a := by
  ext p
  rw [completeRoughSignature_apply, completeRoughSignature_apply]
  by_cases hp : y < p
  · rw [if_pos hp, if_pos hp,
      Nat.factorization_mul hlabel.ne' ha.ne']
    simp only [Finsupp.add_apply,
      Nat.factorization_eq_zero_of_lt (hlabelLe.trans_lt hp), zero_add]
  · simp only [if_neg hp]

/-- Integer-label version of the complete-rough-row identity. -/
theorem completeRoughLabel_small_left_mul
    {y label a : ℕ} (hlabel : 0 < label) (hlabelLe : label ≤ y)
    (ha : 0 < a) :
    completeRoughLabel y (label * a) = completeRoughLabel y a :=
  completeRoughSignature_eq_iff_label_eq.mp
    (completeRoughSignature_small_left_mul hlabel hlabelLe ha)



/-! ## Exact finite deletion counts -/















end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.TangentFlowAlgebra -/
section


/-!
# Exact algebra of the tangent flow

A tangent request replaces weight at `t * a` by the same weight at `s * a`.
This file defines the simultaneous finite update on actual natural-number
coordinates and proves its exact linear invariants.  In particular, the full
valuation of the common multiplier cancels; no squarefreeness or coprimality
assumption on that multiplier is needed.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

noncomputable section







theorem sum_tangentPointMass_mul
    {A : Finset ℕ} {b : ℕ} (hb : b ∈ A) (value : ℕ → ℝ) :
    ∑ a ∈ A, tangentPointMass b a * value a = value b := by
  rw [Finset.sum_eq_single b]
  · simp [tangentPointMass]
  · intro a ha hab
    simp [tangentPointMass, hab]
  · exact fun hnot ↦ (hnot hb).elim

/-- Master finite-sum identity: testing the coordinate update against any
function gives the directed endpoint difference for every request. -/
theorem tangentDelta_weightedSum
    {ι : Type*} (requests : Finset ι)
    (source target multiplier : ι → ℕ) (weight : ι → ℝ)
    (A : Finset ℕ) (value : ℕ → ℝ)
    (hsource : ∀ e ∈ requests, source e * multiplier e ∈ A)
    (htarget : ∀ e ∈ requests, target e * multiplier e ∈ A) :
    ∑ a ∈ A,
        tangentDelta requests source target multiplier weight a * value a =
      ∑ e ∈ requests, weight e *
        (value (source e * multiplier e) -
          value (target e * multiplier e)) := by
  simp only [tangentDelta, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e he
  calc
    (∑ a ∈ A,
        weight e *
            (tangentPointMass (source e * multiplier e) a -
              tangentPointMass (target e * multiplier e) a) * value a) =
        weight e *
            (∑ a ∈ A,
              tangentPointMass (source e * multiplier e) a * value a) -
          weight e *
            (∑ a ∈ A,
              tangentPointMass (target e * multiplier e) a * value a) := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro a _ha
      ring
    _ = weight e *
        (value (source e * multiplier e) -
          value (target e * multiplier e)) := by
      rw [sum_tangentPointMass_mul (hsource e he) value,
        sum_tangentPointMass_mul (htarget e he) value]
      ring

/-- Weighted sums after the update equal the old sums plus the request
boundary tested against the same function. -/
theorem tangentUpdate_weightedSum
    {ι : Type*} (requests : Finset ι)
    (source target multiplier : ι → ℕ) (weight : ι → ℝ)
    (x : ℕ → ℝ) (A : Finset ℕ) (value : ℕ → ℝ)
    (hsource : ∀ e ∈ requests, source e * multiplier e ∈ A)
    (htarget : ∀ e ∈ requests, target e * multiplier e ∈ A) :
    ∑ a ∈ A,
        tangentUpdate requests source target multiplier weight x a * value a =
      (∑ a ∈ A, x a * value a) +
        ∑ e ∈ requests, weight e *
          (value (source e * multiplier e) -
            value (target e * multiplier e)) := by
  simp only [tangentUpdate, add_mul, Finset.sum_add_distrib]
  rw [tangentDelta_weightedSum requests source target multiplier weight A
    value hsource htarget]

/-- The complete factorization vector of the common multiplier cancels. -/
theorem tangent_endpoint_factorization_sub
    {source target multiplier p : ℕ}
    (hsource : source ≠ 0) (htarget : target ≠ 0)
    (hmultiplier : multiplier ≠ 0) :
    (((source * multiplier).factorization p : ℕ) : ℝ) -
        (((target * multiplier).factorization p : ℕ) : ℝ) =
      (source.factorization p : ℝ) - (target.factorization p : ℝ) := by
  rw [Nat.factorization_mul hsource hmultiplier,
    Nat.factorization_mul htarget hmultiplier]
  simp only [Finsupp.add_apply, Nat.cast_add]
  ring

/-- Exact valuation update, expressed only through source and target labels. -/
theorem tangentUpdate_valuation
    {ι : Type*} (requests : Finset ι)
    (source target multiplier : ι → ℕ) (weight : ι → ℝ)
    (x : ℕ → ℝ) (A : Finset ℕ) (p : ℕ)
    (hsourceMem : ∀ e ∈ requests, source e * multiplier e ∈ A)
    (htargetMem : ∀ e ∈ requests, target e * multiplier e ∈ A)
    (hsourcePos : ∀ e ∈ requests, source e ≠ 0)
    (htargetPos : ∀ e ∈ requests, target e ≠ 0)
    (hmultiplierPos : ∀ e ∈ requests, multiplier e ≠ 0) :
    ∑ a ∈ A,
        tangentUpdate requests source target multiplier weight x a *
          (a.factorization p : ℝ) =
      (∑ a ∈ A, x a * (a.factorization p : ℝ)) +
        ∑ e ∈ requests, weight e *
          ((source e).factorization p - (target e).factorization p : ℝ) := by
  rw [tangentUpdate_weightedSum requests source target multiplier weight x A
    (fun a ↦ (a.factorization p : ℝ)) hsourceMem htargetMem]
  apply congrArg (fun z : ℝ ↦ (∑ a ∈ A, x a * (a.factorization p : ℝ)) + z)
  apply Finset.sum_congr rfl
  intro e he
  rw [tangent_endpoint_factorization_sub
    (hsourcePos e he) (htargetPos e he) (hmultiplierPos e he)]

/-- If the directed label boundary is the residual valuation vector, the
updated selector has the exact target valuation. -/
theorem tangentUpdate_valuation_eq_target
    {ι : Type*} (requests : Finset ι)
    (source target multiplier : ι → ℕ) (weight : ι → ℝ)
    (x : ℕ → ℝ) (A : Finset ℕ) (targetValuation : ℕ → ℝ)
    (hsourceMem : ∀ e ∈ requests, source e * multiplier e ∈ A)
    (htargetMem : ∀ e ∈ requests, target e * multiplier e ∈ A)
    (hsourcePos : ∀ e ∈ requests, source e ≠ 0)
    (htargetPos : ∀ e ∈ requests, target e ≠ 0)
    (hmultiplierPos : ∀ e ∈ requests, multiplier e ≠ 0)
    (hboundary : ∀ p : ℕ,
      ∑ e ∈ requests, weight e *
          ((source e).factorization p - (target e).factorization p : ℝ) =
        targetValuation p -
          ∑ a ∈ A, x a * (a.factorization p : ℝ)) :
    ∀ p : ℕ,
      ∑ a ∈ A,
          tangentUpdate requests source target multiplier weight x a *
            (a.factorization p : ℝ) = targetValuation p := by
  intro p
  rw [tangentUpdate_valuation requests source target multiplier weight x A p
    hsourceMem htargetMem hsourcePos htargetPos hmultiplierPos,
    hboundary p]
  ring



/-- Staying in the same complete-signature row preserves its exact row sum. -/
theorem tangentUpdate_signatureRow
    {ι σ : Type*} [DecidableEq σ]
    (requests : Finset ι)
    (source target multiplier : ι → ℕ) (weight : ι → ℝ)
    (x : ℕ → ℝ) (A : Finset ℕ) (signature : ℕ → σ) (row : σ)
    (hsource : ∀ e ∈ requests, source e * multiplier e ∈ A)
    (htarget : ∀ e ∈ requests, target e * multiplier e ∈ A)
    (hsame : ∀ e ∈ requests,
      signature (source e * multiplier e) =
        signature (target e * multiplier e)) :
    ∑ a ∈ A.filter (fun a ↦ signature a = row),
        tangentUpdate requests source target multiplier weight x a =
      ∑ a ∈ A.filter (fun a ↦ signature a = row), x a := by
  let indicator : ℕ → ℝ := fun a ↦
    if signature a = row then 1 else 0
  have hweighted := tangentUpdate_weightedSum requests source target multiplier
    weight x A indicator hsource htarget
  have hboundary :
      ∑ e ∈ requests, weight e *
        (indicator (source e * multiplier e) -
          indicator (target e * multiplier e)) = 0 := by
    apply Finset.sum_eq_zero
    intro e he
    simp only [indicator, hsame e he, sub_self, mul_zero]
  rw [hboundary, add_zero] at hweighted
  simpa only [indicator, Finset.sum_filter, ite_mul, mul_ite, one_mul,
    mul_one, zero_mul, mul_zero]
    using hweighted





end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.TangentStarTransport -/
section


/-!
# Exact finite star transport for tangent residuals

A zero-sum residual on a finite vertex type is transported through one
chosen pivot.  Positive residual leaves its vertex for the pivot; negative
residual is supplied from the pivot.  The construction is literal,
nonnegative, supported on the star, and has exactly the requested
divergence.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

noncomputable section







variable {V : Type*} [DecidableEq V]

/-! ## Pointwise support and sign -/











/-! ## Exact outgoing and incoming sums -/

variable [Fintype V]















/-! ## Traffic -/





/-! ## Boundary identities consumed by `TangentFlowAlgebra` -/

/-- Finite integration by parts for any directed flow. -/
theorem tangentFlow_weightedBoundary_eq_divergence
    {W : Type*} [Fintype W]
    (flow : W → W → ℝ) (value : W → ℝ) :
    (∑ source : W, ∑ target : W,
        flow source target * (value source - value target)) =
      ∑ v : W, tangentFlowDivergence flow v * value v := by
  classical
  have hout :
      (∑ source : W, ∑ target : W,
          flow source target * value source) =
        ∑ source : W,
          (∑ target : W, flow source target) * value source := by
    apply Finset.sum_congr rfl
    intro source _hsource
    rw [Finset.sum_mul]
  have hin :
      (∑ source : W, ∑ target : W,
          flow source target * value target) =
        ∑ target : W,
          (∑ source : W, flow source target) * value target := by
    calc
      (∑ source : W, ∑ target : W,
          flow source target * value target) =
          ∑ target : W, ∑ source : W,
            flow source target * value target := by
        rw [Finset.sum_comm]
      _ = ∑ target : W,
          (∑ source : W, flow source target) * value target := by
        apply Finset.sum_congr rfl
        intro target _htarget
        rw [Finset.sum_mul]
  calc
    (∑ source : W, ∑ target : W,
        flow source target * (value source - value target)) =
        (∑ source : W, ∑ target : W,
          flow source target * value source) -
        ∑ source : W, ∑ target : W,
          flow source target * value target := by
      simp_rw [mul_sub, Finset.sum_sub_distrib]
    _ = (∑ source : W,
          (∑ target : W, flow source target) * value source) -
        ∑ target : W,
          (∑ source : W, flow source target) * value target := by
      rw [hout, hin]
    _ = ∑ v : W, tangentFlowDivergence flow v * value v := by
      simp only [tangentFlowDivergence, sub_mul,
        Finset.sum_sub_distrib]









end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.TangentRequestSplitting -/
section


/-!
# Literal finite splitting of tangent-flow requests

This file formalizes only the algebra in the paper's request splitting.
It assumes concrete nonnegative edge masses and forms explicit `Fin k`
families of equal pieces.  It contains no flow-existence, list-capacity,
or collision-avoidance assertion.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

noncomputable section







theorem one_le_tangentRequestCount (L sigma f : ℝ) :
    1 ≤ tangentRequestCount L sigma f := by
  exact le_max_left 1 (Nat.ceil (4 * L * f / sigma))

theorem tangentRequestCount_pos (L sigma f : ℝ) :
    0 < tangentRequestCount L sigma f := by
  exact lt_of_lt_of_le Nat.zero_lt_one (one_le_tangentRequestCount L sigma f)

/-- The ceiling definition dominates the normalized edge mass. -/
theorem normalizedMass_le_tangentRequestCount
    (L sigma f : ℝ) :
    4 * L * f / sigma ≤ (tangentRequestCount L sigma f : ℝ) := by
  have hceil : 4 * L * f / sigma ≤
      (Nat.ceil (4 * L * f / sigma) : ℝ) :=
    Nat.le_ceil (4 * L * f / sigma)
  have hceilMax : Nat.ceil (4 * L * f / sigma) ≤
      tangentRequestCount L sigma f := by
    exact le_max_right 1 (Nat.ceil (4 * L * f / sigma))
  exact hceil.trans (by exact_mod_cast hceilMax)

/-- Every equal request piece has the paper's size bound. -/
theorem tangentRequestPieceMass_le
    {L sigma f : ℝ} (_hf : 0 ≤ f) (hL : 0 < L) (hsigma : 0 < sigma) :
    tangentRequestPieceMass L sigma f ≤ sigma / (4 * L) := by
  have hk : 0 < (tangentRequestCount L sigma f : ℝ) := by
    exact_mod_cast tangentRequestCount_pos L sigma f
  have hfourL : 0 < 4 * L := by positivity
  have hnormalized := normalizedMass_le_tangentRequestCount L sigma f
  have hmul : 4 * L * f ≤
      (tangentRequestCount L sigma f : ℝ) * sigma :=
    (div_le_iff₀ hsigma).1 hnormalized
  unfold tangentRequestPieceMass
  apply (div_le_div_iff₀ hk hfourL).2
  simpa only [mul_assoc, mul_comm, mul_left_comm] using hmul







/-- The `Fin k` equal pieces of one edge sum exactly to its original mass. -/
theorem sum_tangentRequestPieceMass
    (L sigma f : ℝ) :
    (∑ _i : Fin (tangentRequestCount L sigma f),
        tangentRequestPieceMass L sigma f) = f := by
  have hk : (tangentRequestCount L sigma f : ℝ) ≠ 0 := by
    exact_mod_cast (tangentRequestCount_pos L sigma f).ne'
  simp only [tangentRequestPieceMass, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  field_simp













theorem tangentSplitRequestWeight_nonneg
    {E : Type*} {edges : Finset E} {L sigma : ℝ} {flow : E → ℝ}
    (hflow : ∀ e ∈ edges, 0 ≤ flow e)
    (request : TangentSplitRequest edges L sigma flow) :
    0 ≤ tangentSplitRequestWeight request := by
  unfold tangentSplitRequestWeight tangentRequestPieceMass
  exact div_nonneg (hflow request.1.1 request.1.2) (by positivity)



theorem tangentSplitRequestWeight_le
    {E : Type*} {edges : Finset E} {L sigma : ℝ} {flow : E → ℝ}
    (hflow : ∀ e ∈ edges, 0 ≤ flow e)
    (hL : 0 < L) (hsigma : 0 < sigma)
    (request : TangentSplitRequest edges L sigma flow) :
    tangentSplitRequestWeight request ≤ sigma / (4 * L) := by
  exact tangentRequestPieceMass_le
    (hflow request.1.1 request.1.2) hL hsigma

/-- Paper normalization of the preceding bound: with endpoint slack
`sigma / L`, every split request uses at most one quarter of that slack. -/
theorem tangentSplitRequestWeight_mem_slackQuarter
    {E : Type*} {edges : Finset E} {L sigma : ℝ} {flow : E → ℝ}
    (hflow : ∀ e ∈ edges, 0 ≤ flow e)
    (hL : 0 < L) (hsigma : 0 < sigma)
    (request : TangentSplitRequest edges L sigma flow) :
    0 ≤ tangentSplitRequestWeight request ∧
      tangentSplitRequestWeight request ≤ (sigma / L) / 4 := by
  refine ⟨tangentSplitRequestWeight_nonneg hflow request, ?_⟩
  calc
    tangentSplitRequestWeight request ≤ sigma / (4 * L) :=
      tangentSplitRequestWeight_le hflow hL hsigma request
    _ = (sigma / L) / 4 := by
      field_simp [hL.ne']









/-- Request splitting preserves the complete directed edge boundary when
tested against any label function.  This is the exact bridge from the
paper's edge flow to the request family consumed by `tangentUpdate`. -/
theorem sum_tangentSplitRequestWeight_mul_sub
    {E P : Type*} (edges : Finset E) (source target : E → P)
    (L sigma : ℝ) (flow : E → ℝ) (value : P → ℝ) :
    (∑ request : TangentSplitRequest edges L sigma flow,
        tangentSplitRequestWeight request *
          (value (tangentSplitRequestSource source request) -
            value (tangentSplitRequestTarget target request))) =
      ∑ e ∈ edges, flow e * (value (source e) - value (target e)) := by
  classical
  simp only [TangentSplitRequest, tangentSplitRequestWeight,
    tangentSplitRequestSource, tangentSplitRequestTarget,
    tangentSplitRequestEdge, Fintype.sum_sigma]
  calc
    (∑ e : ↑edges,
        ∑ _i : Fin (tangentRequestCount L sigma (flow e.1)),
          tangentRequestPieceMass L sigma (flow e.1) *
            (value (source e.1) - value (target e.1))) =
      ∑ e : ↑edges,
        flow e.1 * (value (source e.1) - value (target e.1)) := by
      apply Finset.sum_congr rfl
      intro e _he
      rw [← Finset.sum_mul, sum_tangentRequestPieceMass]
    _ = ∑ e ∈ edges,
        flow e * (value (source e) - value (target e)) := by
      simpa using Finset.sum_attach edges
        (fun e ↦ flow e * (value (source e) - value (target e)))















end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.TangentCollisionFreeFeasibility -/
section


/-!
# Collision-free tangent updates and coordinate feasibility

The probabilistic part of the tangent construction is used only to produce
requests whose numerical endpoints are all distinct.  This file records the
deterministic consequence for the literal finite update: a used coordinate
receives exactly one signed request, and the paper's endpoint slack gives the
claimed post-move margin.

Importantly, `TangentEndpointsDistinct` below is an explicit input, not a
formalization of the paper's common-list estimate or local-lemma argument.
The final theorem connects that visible input to the actual split requests;
it does not claim to construct collision-free multipliers.
-/

namespace Erdos390.WholePaper

noncomputable section



theorem tangentDelta_eq_weight_of_source
    {ι : Type*} {requests : Finset ι}
    {source target multiplier : ι → ℕ} {weight : ι → ℝ}
    (hdistinct : TangentEndpointsDistinct requests source target multiplier)
    {e : ι} (he : e ∈ requests) :
    tangentDelta requests source target multiplier weight
        (source e * multiplier e) = weight e := by
  classical
  rw [tangentDelta, Finset.sum_eq_single e]
  · have hcross := hdistinct.source_ne_target e he e he
    have hsourceTarget : source e ≠ target e := by
      intro heq
      apply hcross
      rw [heq]
    have hmultiplier : multiplier e ≠ 0 := by
      intro hm
      apply hcross
      simp [hm]
    simp [tangentPointMass, hsourceTarget, hmultiplier]
  · intro f hf hfe
    have hsourceNe :
        source e * multiplier e ≠ source f * multiplier f := by
      intro hEq
      have hef : e = f := hdistinct.source_injective he hf hEq
      exact hfe hef.symm
    have htargetNe :
        source e * multiplier e ≠ target f * multiplier f :=
      hdistinct.source_ne_target e he f hf
    simp [tangentPointMass, hsourceNe, htargetNe]
  · exact fun hnot ↦ (hnot he).elim

theorem tangentDelta_eq_neg_weight_of_target
    {ι : Type*} {requests : Finset ι}
    {source target multiplier : ι → ℕ} {weight : ι → ℝ}
    (hdistinct : TangentEndpointsDistinct requests source target multiplier)
    {e : ι} (he : e ∈ requests) :
    tangentDelta requests source target multiplier weight
        (target e * multiplier e) = -weight e := by
  classical
  rw [tangentDelta, Finset.sum_eq_single e]
  · have hcross := hdistinct.source_ne_target e he e he
    have htargetSource : target e ≠ source e := by
      intro heq
      apply hcross
      rw [heq]
    have hmultiplier : multiplier e ≠ 0 := by
      intro hm
      apply hcross
      simp [hm]
    simp [tangentPointMass, htargetSource, hmultiplier]
  · intro f hf hfe
    have hsourceNe :
        target e * multiplier e ≠ source f * multiplier f :=
      (hdistinct.source_ne_target f hf e he).symm
    have htargetNe :
        target e * multiplier e ≠ target f * multiplier f := by
      intro hEq
      have hef : e = f := hdistinct.target_injective he hf hEq
      exact hfe hef.symm
    simp [tangentPointMass, hsourceNe, htargetNe]
  · exact fun hnot ↦ (hnot he).elim

theorem tangentDelta_eq_zero_of_unused
    {ι : Type*} {requests : Finset ι}
    {source target multiplier : ι → ℕ} {weight : ι → ℝ}
    {a : ℕ}
    (hsource : ∀ e ∈ requests, a ≠ source e * multiplier e)
    (htarget : ∀ e ∈ requests, a ≠ target e * multiplier e) :
    tangentDelta requests source target multiplier weight a = 0 := by
  apply Finset.sum_eq_zero
  intro e he
  simp [tangentPointMass, hsource e he, htarget e he]

theorem tangentUpdate_eq_add_weight_of_source
    {ι : Type*} {requests : Finset ι}
    {source target multiplier : ι → ℕ} {weight : ι → ℝ}
    {x : ℕ → ℝ}
    (hdistinct : TangentEndpointsDistinct requests source target multiplier)
    {e : ι} (he : e ∈ requests) :
    tangentUpdate requests source target multiplier weight x
        (source e * multiplier e) =
      x (source e * multiplier e) + weight e := by
  rw [tangentUpdate, tangentDelta_eq_weight_of_source hdistinct he]

theorem tangentUpdate_eq_sub_weight_of_target
    {ι : Type*} {requests : Finset ι}
    {source target multiplier : ι → ℕ} {weight : ι → ℝ}
    {x : ℕ → ℝ}
    (hdistinct : TangentEndpointsDistinct requests source target multiplier)
    {e : ι} (he : e ∈ requests) :
    tangentUpdate requests source target multiplier weight x
        (target e * multiplier e) =
      x (target e * multiplier e) - weight e := by
  rw [tangentUpdate, tangentDelta_eq_neg_weight_of_target hdistinct he]
  ring

/-- Collision-free requests of size at most `δ` preserve the global box
whenever every used endpoint starts with `δ` two-sided slack. -/
theorem tangentUpdate_mem_unitInterval
    {ι : Type*} {requests : Finset ι}
    {source target multiplier : ι → ℕ} {weight : ι → ℝ}
    {x : ℕ → ℝ} {A : Finset ℕ} {δ : ℝ}
    (hdistinct : TangentEndpointsDistinct requests source target multiplier)
    (hδ : 0 ≤ δ)
    (hweight : ∀ e ∈ requests, 0 ≤ weight e ∧ weight e ≤ δ)
    (hsourceSlack : ∀ e ∈ requests,
      δ ≤ x (source e * multiplier e) ∧
        x (source e * multiplier e) ≤ 1 - δ)
    (htargetSlack : ∀ e ∈ requests,
      δ ≤ x (target e * multiplier e) ∧
        x (target e * multiplier e) ≤ 1 - δ)
    (hglobal : ∀ a ∈ A, x a ∈ Set.Icc (0 : ℝ) 1) :
    ∀ a ∈ A,
      tangentUpdate requests source target multiplier weight x a ∈
        Set.Icc (0 : ℝ) 1 := by
  intro a ha
  by_cases hs : ∃ e ∈ requests, a = source e * multiplier e
  · obtain ⟨e, he, rfl⟩ := hs
    rw [tangentUpdate_eq_add_weight_of_source hdistinct he]
    have hw := hweight e he
    have hx := hsourceSlack e he
    constructor <;> linarith
  · have hsAll : ∀ e ∈ requests, a ≠ source e * multiplier e := by
      intro e he hEq
      exact hs ⟨e, he, hEq⟩
    by_cases ht : ∃ e ∈ requests, a = target e * multiplier e
    · obtain ⟨e, he, rfl⟩ := ht
      rw [tangentUpdate_eq_sub_weight_of_target hdistinct he]
      have hw := hweight e he
      have hx := htargetSlack e he
      constructor <;> linarith
    · have htAll : ∀ e ∈ requests, a ≠ target e * multiplier e := by
        intro e he hEq
        exact ht ⟨e, he, hEq⟩
      rw [tangentUpdate, tangentDelta_eq_zero_of_unused hsAll htAll, add_zero]
      exact hglobal a ha

/-- Paper (9.38): if every request has size at most one quarter of the
available slack, every used endpoint retains three quarters of that slack. -/
theorem tangentUpdate_source_margin
    {ι : Type*} {requests : Finset ι}
    {source target multiplier : ι → ℕ} {weight : ι → ℝ}
    {x : ℕ → ℝ} {δ : ℝ}
    (hdistinct : TangentEndpointsDistinct requests source target multiplier)
    (hδ : 0 ≤ δ)
    (hweight : ∀ e ∈ requests, 0 ≤ weight e ∧ weight e ≤ δ / 4)
    (hsourceSlack : ∀ e ∈ requests,
      δ ≤ x (source e * multiplier e) ∧
        x (source e * multiplier e) ≤ 1 - δ)
    {e : ι} (he : e ∈ requests) :
    3 * δ / 4 ≤
        tangentUpdate requests source target multiplier weight x
          (source e * multiplier e) ∧
      tangentUpdate requests source target multiplier weight x
          (source e * multiplier e) ≤ 1 - 3 * δ / 4 := by
  rw [tangentUpdate_eq_add_weight_of_source hdistinct he]
  have hw := hweight e he
  have hx := hsourceSlack e he
  constructor <;> linarith

theorem tangentUpdate_target_margin
    {ι : Type*} {requests : Finset ι}
    {source target multiplier : ι → ℕ} {weight : ι → ℝ}
    {x : ℕ → ℝ} {δ : ℝ}
    (hdistinct : TangentEndpointsDistinct requests source target multiplier)
    (hδ : 0 ≤ δ)
    (hweight : ∀ e ∈ requests, 0 ≤ weight e ∧ weight e ≤ δ / 4)
    (htargetSlack : ∀ e ∈ requests,
      δ ≤ x (target e * multiplier e) ∧
        x (target e * multiplier e) ≤ 1 - δ)
    {e : ι} (he : e ∈ requests) :
    3 * δ / 4 ≤
        tangentUpdate requests source target multiplier weight x
          (target e * multiplier e) ∧
      tangentUpdate requests source target multiplier weight x
          (target e * multiplier e) ≤ 1 - 3 * δ / 4 := by
  rw [tangentUpdate_eq_sub_weight_of_target hdistinct he]
  have hw := hweight e he
  have hx := htargetSlack e he
  constructor <;> linarith

/-- Deterministic terminal for the two formalized tangent layers.  The
literal requests are the `Fin` pieces of the strictly positive support flow,
their
quarter-slack bound is derived from the splitting formula, and endpoint
distinctness remains the explicit output required from the still-separate
common-list/LLL construction. -/
theorem tangentSplitUpdate_feasible_and_margin
    {E : Type*} [DecidableEq E] (edges : Finset E)
    (source target : E → ℕ) {L sigma : ℝ} (flow : E → ℝ)
    (hflow : ∀ e ∈ edges, 0 < flow e)
    (hL : 0 < L) (hsigma : 0 < sigma)
    (multiplier : TangentSplitRequest edges L sigma flow → ℕ)
    (x : ℕ → ℝ) (A : Finset ℕ)
    (hdistinct : TangentEndpointsDistinct
      (tangentSplitRequests edges L sigma flow)
      (tangentSplitRequestSource source)
      (tangentSplitRequestTarget target) multiplier)
    (hsourceSlack : ∀ request : TangentSplitRequest edges L sigma flow,
      sigma / L ≤ x (tangentSplitRequestSource source request *
          multiplier request) ∧
        x (tangentSplitRequestSource source request * multiplier request) ≤
          1 - sigma / L)
    (htargetSlack : ∀ request : TangentSplitRequest edges L sigma flow,
      sigma / L ≤ x (tangentSplitRequestTarget target request *
          multiplier request) ∧
        x (tangentSplitRequestTarget target request * multiplier request) ≤
          1 - sigma / L)
    (hglobal : ∀ a ∈ A, x a ∈ Set.Icc (0 : ℝ) 1) :
    (∀ a ∈ A,
      tangentUpdate (tangentSplitRequests edges L sigma flow)
          (tangentSplitRequestSource source)
          (tangentSplitRequestTarget target) multiplier
          tangentSplitRequestWeight x a ∈ Set.Icc (0 : ℝ) 1) ∧
      (∀ request : TangentSplitRequest edges L sigma flow,
        3 * (sigma / L) / 4 ≤
            tangentUpdate (tangentSplitRequests edges L sigma flow)
              (tangentSplitRequestSource source)
              (tangentSplitRequestTarget target) multiplier
              tangentSplitRequestWeight x
              (tangentSplitRequestSource source request * multiplier request) ∧
          tangentUpdate (tangentSplitRequests edges L sigma flow)
              (tangentSplitRequestSource source)
              (tangentSplitRequestTarget target) multiplier
              tangentSplitRequestWeight x
              (tangentSplitRequestSource source request * multiplier request) ≤
            1 - 3 * (sigma / L) / 4) ∧
      ∀ request : TangentSplitRequest edges L sigma flow,
        3 * (sigma / L) / 4 ≤
            tangentUpdate (tangentSplitRequests edges L sigma flow)
              (tangentSplitRequestSource source)
              (tangentSplitRequestTarget target) multiplier
              tangentSplitRequestWeight x
              (tangentSplitRequestTarget target request * multiplier request) ∧
          tangentUpdate (tangentSplitRequests edges L sigma flow)
              (tangentSplitRequestSource source)
              (tangentSplitRequestTarget target) multiplier
              tangentSplitRequestWeight x
              (tangentSplitRequestTarget target request * multiplier request) ≤
            1 - 3 * (sigma / L) / 4 := by
  have hflowNonneg : ∀ e ∈ edges, 0 ≤ flow e :=
    fun e he ↦ (hflow e he).le
  have hdelta : 0 ≤ sigma / L := div_nonneg hsigma.le hL.le
  have hweightQuarter : ∀ request : TangentSplitRequest edges L sigma flow,
      0 ≤ tangentSplitRequestWeight request ∧
        tangentSplitRequestWeight request ≤ (sigma / L) / 4 :=
    fun request ↦
      tangentSplitRequestWeight_mem_slackQuarter hflowNonneg hL hsigma request
  have hweightFull : ∀ request : TangentSplitRequest edges L sigma flow,
      0 ≤ tangentSplitRequestWeight request ∧
        tangentSplitRequestWeight request ≤ sigma / L := by
    intro request
    have hw := hweightQuarter request
    exact ⟨hw.1, by linarith⟩
  refine ⟨tangentUpdate_mem_unitInterval hdistinct hdelta
      (fun request _hrequest ↦ hweightFull request)
      (fun request _hrequest ↦ hsourceSlack request)
      (fun request _hrequest ↦ htargetSlack request) hglobal, ?_, ?_⟩
  · intro request
    exact tangentUpdate_source_margin hdistinct hdelta
      (fun request _hrequest ↦ hweightQuarter request)
      (fun request _hrequest ↦ hsourceSlack request)
      (by simp only [tangentSplitRequests, Finset.mem_univ])
  · intro request
    exact tangentUpdate_target_margin hdistinct hdelta
      (fun request _hrequest ↦ hweightQuarter request)
      (fun request _hrequest ↦ htargetSlack request)
      (by simp only [tangentSplitRequests, Finset.mem_univ])

end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankPaperCanonicalTangentResidualBridge -/
section


/-!
# Literal canonical residual for the selector-to-tangent handoff

The canonical Saias reduction currently stops at a selector continuation: it
does not yet construct the pre-tangent rounded selector.  This file removes
the *generic residual* ambiguity without asserting that missing construction.

For a supplied selector `x`, the residual coordinate at a medium prime is
defined literally as

`valuation(selectorTailTarget) - valuation(x)`.

The two remaining selector inputs are named explicitly.  The post-rounding
prime-band balance says that these coordinates sum to zero, while prime-band
support says that the selector already has the target valuation at every
prime outside the band.  Neither fact follows merely from
`roughCanonicalRawRowQuotaError`: that quantity is a complete-rough row quota
error, not a prime-coordinate valuation identity.

From those inputs, the finite prime residual has zero total mass and its
positive star split requests have exactly the valuation deficit required by
`tangentUpdate_valuation_eq_target`.  The final theorem also retains the
all-row integrality input verbatim.  It does not claim that clean common
multipliers, feasibility of the tangent update, or the selector itself have
already been constructed.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel

noncomputable section

/-! ## Literal selector deficit and its finite prime domain -/















/-! ## Prime-label geometry and exact residual algebra -/



/-- Every canonical tangent label is prime. -/
theorem bankPaperCanonicalTangentPrimeLabel_prime
    {n W : ℕ} (p : BankPaperCanonicalTangentPrime n W) :
    (bankPaperCanonicalTangentPrimeLabel p).Prime := by
  exact prime_of_mem_primeBand p.2

/-- Every canonical tangent label lies below the paper smooth cutoff. -/
theorem bankPaperCanonicalTangentPrimeLabel_le_yNat
    {n W : ℕ} (p : BankPaperCanonicalTangentPrime n W) :
    bankPaperCanonicalTangentPrimeLabel p ≤ yNat n := by
  exact le_yNat_of_mem_primeBand p.2

/-- At a non-prime coordinate, both the target and every candidate
factorization vanish. -/
theorem bankPaperCanonicalSelectorValuationDeficit_eq_zero_of_not_prime
    {c : ℝ} {depth n : ℕ} {left right : ℕ → ℕ}
    {changed : Finset ℕ}
    (R : BankPaperRealization n
      (upperEndpoint n (upperTailLength c n)))
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (fixed candidates : Finset ℕ) (x : ℕ → ℝ) {q : ℕ}
    (hq : ¬q.Prime) :
    bankPaperCanonicalSelectorValuationDeficit
      R certificate fixed candidates x q = 0 := by
  simp [bankPaperCanonicalSelectorValuationDeficit,
    Nat.factorization_eq_zero_of_not_prime _ hq]



/-- Prime labels form the standard factorization basis on the finite band.
This statement is independent of the selector and is useful for exposing
the exact support requirement. -/
theorem sum_bankPaperCanonicalTangentPrime_factorization
    {n W : ℕ} (coefficient : ℕ → ℝ) (q : ℕ) :
    (∑ p : BankPaperCanonicalTangentPrime n W,
        coefficient p.1 *
          ((bankPaperCanonicalTangentPrimeLabel p).factorization q : ℝ)) =
      if q ∈ primeBand n W then coefficient q else 0 := by
  calc
    (∑ p : BankPaperCanonicalTangentPrime n W,
        coefficient p.1 *
          ((bankPaperCanonicalTangentPrimeLabel p).factorization q : ℝ)) =
        ∑ p ∈ primeBand n W,
          coefficient p * (p.factorization q : ℝ) := by
      simpa only [bankPaperCanonicalTangentPrimeLabel] using
        (Finset.sum_subtype (primeBand n W) (fun _p ↦ Iff.rfl)
          (fun p ↦ coefficient p * (p.factorization q : ℝ))).symm
    _ = if q ∈ primeBand n W then coefficient q else 0 := by
      by_cases hq : q ∈ primeBand n W
      · rw [if_pos hq, Finset.sum_eq_single q]
        · simp only [(prime_of_mem_primeBand hq).factorization_self,
            Nat.cast_one, mul_one]
        · intro p hp hpq
          have hpPrime : p.Prime := prime_of_mem_primeBand hp
          have hfactorization : p.factorization q = 0 := by
            by_contra hnonzero
            exact hpq (hpPrime.eq_of_factorization_pos hnonzero)
          simp only [hfactorization, Nat.cast_zero, mul_zero]
        · exact fun hqNotMem ↦ (hqNotMem hq).elim
      · rw [if_neg hq]
        apply Finset.sum_eq_zero
        intro p hp
        have hpPrime : p.Prime := prime_of_mem_primeBand hp
        have hpq : p ≠ q := by
          intro hpq
          apply hq
          simpa only [hpq] using hp
        have hfactorization : p.factorization q = 0 := by
          by_contra hnonzero
          exact hpq (hpPrime.eq_of_factorization_pos hnonzero)
        simp only [hfactorization, Nat.cast_zero, mul_zero]

/-- The finite prime residual expands to the full selector valuation deficit.
The only non-definitional input is exact agreement outside the prime band. -/
theorem sum_bankPaperCanonicalTangentResidual_mul_factorization_eq_deficit
    {c : ℝ} {depth n W : ℕ} {left right : ℕ → ℕ}
    {changed : Finset ℕ}
    (R : BankPaperRealization n
      (upperEndpoint n (upperTailLength c n)))
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (fixed candidates : Finset ℕ) (x : ℕ → ℝ)
    (hsupport : BankPaperCanonicalSelectorDeficitSupportedOnPrimeBand (W := W)
      R certificate fixed candidates x) (q : ℕ) :
    (∑ p : BankPaperCanonicalTangentPrime n W,
        bankPaperCanonicalTangentResidual
            R certificate fixed candidates x p *
          ((bankPaperCanonicalTangentPrimeLabel p).factorization q : ℝ)) =
      bankPaperCanonicalSelectorValuationDeficit
        R certificate fixed candidates x q := by
  calc
    (∑ p : BankPaperCanonicalTangentPrime n W,
        bankPaperCanonicalTangentResidual
            R certificate fixed candidates x p *
          ((bankPaperCanonicalTangentPrimeLabel p).factorization q : ℝ)) =
        if q ∈ primeBand n W then
          bankPaperCanonicalSelectorValuationDeficit
            R certificate fixed candidates x q
        else 0 := by
      simpa only [bankPaperCanonicalTangentResidual] using
        sum_bankPaperCanonicalTangentPrime_factorization
          (n := n) (W := W)
          (fun p ↦ bankPaperCanonicalSelectorValuationDeficit
            R certificate fixed candidates x p) q
    _ = bankPaperCanonicalSelectorValuationDeficit
          R certificate fixed candidates x q := by
      by_cases hqBand : q ∈ primeBand n W
      · rw [if_pos hqBand]
      · rw [if_neg hqBand]
        by_cases hqPrime : q.Prime
        · exact (hsupport q hqPrime hqBand).symm
        · exact (bankPaperCanonicalSelectorValuationDeficit_eq_zero_of_not_prime
            R certificate fixed candidates x hqPrime).symm

/-! ## Instantiation of the star split-request boundary -/





end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.TangentDistributedFlowCensus -/
section


/-!
# Distributed finite-band flow census

This file isolates the quantitative interface needed between a genuine
finite-band earthmover and the already formalized split-request collision
terminal.  Unlike the one-pivot star, a distributed earthmover records a
separate port load at every vertex.  Its two analytic ledgers are

* `traffic <= (1/2) * ||residual||_1 + 2 * cutTraffic`;
* `incident(label v) <= |residual v| + 2 * portLoad v`.

These are the literal estimates produced by the cell-boundary construction
in the paper.  They are strictly stronger than the final collision target
and do not mention a density or the constant `1 / 24`.

The module proves all consequences after those construction ledgers:

* positive support has at most `|V|^2` edges;
* the total split-request count and every endpoint-label request load have
  explicit upper bounds;
* fixed main/error/ceiling parameter budgets imply the exact existing guard
  `4*T + I_source + I_target <= density^2/24` for every request;
* hence the already proved `1/8` collision-census conclusion follows.

Existence of the cell earthmover is deliberately not postulated here.  It
must be constructed from band balance, prefix-load bounds, cell cardinality,
and adjacent-cell ratio geometry.  The downstream theorems keep every
construction estimate as a visible
hypothesis, so the unfinished construction cannot be confused with a
selector theorem or with the final collision target.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel

noncomputable section

/-! ## Residual, cut, and port ledgers -/









/-! ## Literal ratio-cell cuts and uniform adjacent-cell ports -/











































/-! ## Visible hypotheses for a distributed construction -/

/- The construction estimates are deliberately *not* bundled into a
structure.  The repository audit discipline forbids hiding a claimed
traffic or incident estimate in a conclusion-bearing certificate.  Every
generic theorem below therefore displays the exact flow property that it
uses. -/

/-! ## Support, locality, and literal traffic consequences -/









/-! ## Boundary preservation for an arbitrary distributed flow -/

/-- Restricting a nonnegative flow to its strictly positive support does not
change any weighted edge sum. -/
theorem sum_tangentPositiveFlowEdges_mul_eq_full_of_nonneg
    {V : Type*} [Fintype V] [DecidableEq V]
    (flow : V -> V -> Real)
    (hflow : forall source target, 0 <= flow source target)
    (value : V × V -> Real) :
    (∑ edge ∈ tangentPositiveFlowEdges flow,
        flow edge.1 edge.2 * value edge) =
      ∑ edge : V × V, flow edge.1 edge.2 * value edge := by
  classical
  apply Finset.sum_subset
    (Finset.subset_univ (tangentPositiveFlowEdges flow))
  intro edge _hedge hedge
  have hnotPos : ¬0 < flow edge.1 edge.2 := by
    simpa only [mem_tangentPositiveFlowEdges] using hedge
  have hzero : flow edge.1 edge.2 = 0 :=
    le_antisymm (le_of_not_gt hnotPos) (hflow edge.1 edge.2)
  simp only [hzero, zero_mul]

/-- The positive support of a distributed earthmover has exactly the
prescribed residual boundary against every vertex test function. -/
theorem tangentDistributedPositiveEdges_boundary_eq_residual
    {V : Type*} [Fintype V] [DecidableEq V]
    (flow : V -> V -> Real) (residual : V -> Real)
    (hflow : forall source target, 0 <= flow source target)
    (hdivergence : forall v,
      tangentFlowDivergence flow v = residual v)
    (value : V -> Real) :
    (∑ edge ∈ tangentPositiveFlowEdges flow,
        flow edge.1 edge.2 * (value edge.1 - value edge.2)) =
      ∑ v : V, residual v * value v := by
  calc
    (∑ edge ∈ tangentPositiveFlowEdges flow,
        flow edge.1 edge.2 * (value edge.1 - value edge.2)) =
      ∑ edge : V × V,
        flow edge.1 edge.2 * (value edge.1 - value edge.2) :=
      sum_tangentPositiveFlowEdges_mul_eq_full_of_nonneg
        flow hflow
          (fun edge => value edge.1 - value edge.2)
    _ = ∑ source : V, ∑ target : V,
        flow source target * (value source - value target) := by
      rw [Fintype.sum_prod_type]
    _ = ∑ v : V,
        tangentFlowDivergence flow v * value v :=
      tangentFlow_weightedBoundary_eq_divergence flow value
    _ = ∑ v : V, residual v * value v := by
      apply Finset.sum_congr rfl
      intro v _hv
      rw [hdivergence v]

/-- Factorization-coordinate form of the distributed boundary. -/
theorem tangentDistributedPositiveEdges_factorizationBoundary_eq_residual
    {V : Type*} [Fintype V] [DecidableEq V]
    (flow : V -> V -> Real) (label : V -> Nat) (residual : V -> Real)
    (hflow : forall source target, 0 <= flow source target)
    (hdivergence : forall v,
      tangentFlowDivergence flow v = residual v)
    (p : Nat) :
    (∑ edge ∈ tangentPositiveFlowEdges flow,
        flow edge.1 edge.2 *
          (((tangentStarEdgeSource label edge).factorization p : Real) -
            ((tangentStarEdgeTarget label edge).factorization p : Real))) =
      ∑ v : V, residual v * (label v).factorization p := by
  simpa only [tangentStarEdgeSource, tangentStarEdgeTarget] using
    tangentDistributedPositiveEdges_boundary_eq_residual
      flow residual hflow hdivergence
      (fun v => ((label v).factorization p : Real))

/-- Equal request splitting preserves the distributed residual boundary. -/
theorem tangentDistributedSplitRequest_factorizationBoundary_eq_residual
    {V : Type*} [Fintype V] [DecidableEq V]
    (flow : V -> V -> Real) (label : V -> Nat) (residual : V -> Real)
    (hflow : forall source target, 0 <= flow source target)
    (hdivergence : forall v,
      tangentFlowDivergence flow v = residual v)
    (L sigma : Real) (p : Nat) :
    (∑ request : TangentSplitRequest
          (tangentPositiveFlowEdges flow) L sigma
            (fun edge : V × V => flow edge.1 edge.2),
        tangentSplitRequestWeight request *
          (((tangentSplitRequestSource (tangentStarEdgeSource label)
                request).factorization p : Real) -
            ((tangentSplitRequestTarget (tangentStarEdgeTarget label)
                request).factorization p : Real))) =
      ∑ v : V, residual v * (label v).factorization p := by
  calc
    (∑ request : TangentSplitRequest
          (tangentPositiveFlowEdges flow) L sigma
            (fun edge : V × V => flow edge.1 edge.2),
        tangentSplitRequestWeight request *
          (((tangentSplitRequestSource (tangentStarEdgeSource label)
                request).factorization p : Real) -
            ((tangentSplitRequestTarget (tangentStarEdgeTarget label)
                request).factorization p : Real))) =
      ∑ edge ∈ tangentPositiveFlowEdges flow,
        flow edge.1 edge.2 *
          (((tangentStarEdgeSource label edge).factorization p : Real) -
            ((tangentStarEdgeTarget label edge).factorization p : Real)) := by
      simpa only using
        sum_tangentSplitRequestWeight_mul_sub
          (tangentPositiveFlowEdges flow)
          (tangentStarEdgeSource label) (tangentStarEdgeTarget label)
          L sigma (fun edge : V × V => flow edge.1 edge.2)
          (fun q => (q.factorization p : Real))
    _ = ∑ v : V, residual v * (label v).factorization p :=
      tangentDistributedPositiveEdges_factorizationBoundary_eq_residual
        flow label residual hflow hdivergence p

/-! ## Weighted per-label port control -/









/-! ## Total and endpoint request counts -/









/-! ## Paper-parameter closure of the collision guard

The three budgets below mirror the actual parameter order in Section 9.
The main term is made small by the fixed band width `w`; the error and
ceiling terms are absorbed only after the mesh is fixed and `n` tends to
infinity.  None of them is a traffic or request-count hypothesis. -/















/-! ## Connector to the actual paper collision terminal -/

namespace BankPaperRealization



end BankPaperRealization

end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankPaperCanonicalPreTangentSelector -/
section


/-!
# Honest selector-rounding interface for the finite-band tangent

The canonical Saias theorem controls complete-rough row quota errors, while
the tangent consumes prime-valuation residuals of an actual rounded
selector.  Those are different index sets, so a row error cannot simply be
renamed as traffic.

This file records the minimal missing selector-rounding output as a
predicate on an explicit selector.  It contains no flow, request count,
density, or collision target.  The residual estimates are exactly the two
inputs used upstream of the paper earthmover:

* the pointwise prime estimate;
* signed prefix estimates on literal ratio-cell cuts.

Unlike a conclusion-bearing structure, the selector and every requested
property remain visible in the existential handoff proposition.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel

noncomputable section





/-! ## Direct projections used by downstream assembly -/

theorem bankPaperCanonicalRoundedSelectorTangentInput_selectorState
    {c : Real} {depth n W : Nat} {left right : Nat -> Nat}
    {changed : Finset Nat}
    {R : BankPaperRealization n
      (upperEndpoint n (upperTailLength c n))}
    {certificate : GuardedCentralAnchorCertificate c depth n
      left right changed}
    {fixed candidates : Finset Nat}
    {Band : Type*} [DecidableEq Band]
    {bandOf : BankPaperCanonicalTangentPrime n W -> Band}
    {cellIndex : BankPaperCanonicalTangentPrime n W -> Nat}
    {pointwiseUpper : BankPaperCanonicalTangentPrime n W -> Real}
    {prefixUpper : Band -> Nat -> Real}
    {selector : Nat -> Real}
    (S : BankPaperCanonicalRoundedSelectorTangentInput
      R certificate fixed candidates bandOf cellIndex
        pointwiseUpper prefixUpper selector) :
    (∀ a ∈ candidates,
        0 <= selector a ∧ selector a <= 1) ∧
      BankPaperCanonicalSelectorRowIntegral n candidates selector ∧
      BankPaperCanonicalPostRoundingPrimeBandBalance (W := W)
        R certificate fixed candidates selector ∧
      BankPaperCanonicalSelectorDeficitSupportedOnPrimeBand (W := W)
        R certificate fixed candidates selector := by
  exact ⟨S.1, S.2.1, S.2.2.1, S.2.2.2.1⟩



end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankPaperCanonicalDistributedTangentBridge -/
section


/-!
# Canonical selector boundary through a distributed tangent flow

This is the star-free replacement for the boundary portion of
`BankPaperCanonicalTangentResidualBridge`.  A distributed earthmover with
the literal canonical residual has the exact factorization boundary needed
by `tangentUpdate_valuation_eq_target`; equal request splitting preserves it.

No clean-list estimate or final collision conclusion occurs in this module.
The only collision-facing asymptotic recorded here is the unconditional
dense-support ceiling `yNat^3 / n -> 0`.
-/

open scoped BigOperators
open Filter Topology

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel

noncomputable section













/-! ## Canonical notation for an arbitrary distributed flow -/











/-- Exact canonical request boundary for an arbitrary nonnegative
distributed flow with the literal selector-residual divergence.  This
replaces the star-specific theorem
`bankPaperCanonicalTangentStarSplitRequest_boundary_eq_selectorDeficit` in a
distributed Section 9 assembly. -/
theorem bankPaperCanonicalDistributedSplitRequest_boundary_eq_selectorDeficit
    {c : Real} {depth n W : Nat} {left right : Nat -> Nat}
    {changed : Finset Nat}
    (R : BankPaperRealization n
      (upperEndpoint n (upperTailLength c n)))
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (fixed candidates : Finset Nat) (x : Nat -> Real)
    (flow : BankPaperCanonicalTangentPrime n W ->
      BankPaperCanonicalTangentPrime n W -> Real)
    (hflow : forall source target, 0 <= flow source target)
    (hdivergence : forall p,
      tangentFlowDivergence flow p =
        bankPaperCanonicalTangentResidual
          R certificate fixed candidates x p)
    (hsupport : BankPaperCanonicalSelectorDeficitSupportedOnPrimeBand
      (W := W) R certificate fixed candidates x)
    (L sigma : Real) :
    (forall p : BankPaperCanonicalTangentPrime n W,
      tangentFlowDivergence flow p =
        bankPaperCanonicalTangentResidual
          R certificate fixed candidates x p) ∧
      forall q : Nat,
        (∑ request : TangentSplitRequest
              (tangentPositiveFlowEdges flow) L sigma
                (fun edge :
                    BankPaperCanonicalTangentPrime n W ×
                      BankPaperCanonicalTangentPrime n W =>
                  flow edge.1 edge.2),
            tangentSplitRequestWeight request *
              (((tangentSplitRequestSource
                    (tangentStarEdgeSource
                      bankPaperCanonicalTangentPrimeLabel)
                    request).factorization q : Real) -
                ((tangentSplitRequestTarget
                    (tangentStarEdgeTarget
                      bankPaperCanonicalTangentPrimeLabel)
                    request).factorization q : Real))) =
          bankPaperCanonicalSelectorValuationDeficit
            R certificate fixed candidates x q := by
  refine ⟨hdivergence, ?_⟩
  intro q
  calc
    (∑ request : TangentSplitRequest
          (tangentPositiveFlowEdges flow) L sigma
            (fun edge :
                BankPaperCanonicalTangentPrime n W ×
                  BankPaperCanonicalTangentPrime n W =>
              flow edge.1 edge.2),
        tangentSplitRequestWeight request *
          (((tangentSplitRequestSource
                (tangentStarEdgeSource
                  bankPaperCanonicalTangentPrimeLabel)
                request).factorization q : Real) -
            ((tangentSplitRequestTarget
                (tangentStarEdgeTarget
                  bankPaperCanonicalTangentPrimeLabel)
                request).factorization q : Real))) =
      ∑ p : BankPaperCanonicalTangentPrime n W,
        bankPaperCanonicalTangentResidual
            R certificate fixed candidates x p *
          ((bankPaperCanonicalTangentPrimeLabel p).factorization q : Real) :=
      tangentDistributedSplitRequest_factorizationBoundary_eq_residual
        flow bankPaperCanonicalTangentPrimeLabel
        (bankPaperCanonicalTangentResidual
          R certificate fixed candidates x)
        hflow hdivergence L sigma q
    _ = bankPaperCanonicalSelectorValuationDeficit
          R certificate fixed candidates x q :=
      sum_bankPaperCanonicalTangentResidual_mul_factorization_eq_deficit
        R certificate fixed candidates x hsupport q

/-- Selector-facing version of the distributed boundary theorem.  Its
selector input is exactly the upstream rounding predicate; no target traffic
or collision condition is accepted here. -/
theorem bankPaperCanonicalRoundedSelector_distributedBoundary
    {c : Real} {depth n W : Nat} {left right : Nat -> Nat}
    {changed : Finset Nat}
    (R : BankPaperRealization n
      (upperEndpoint n (upperTailLength c n)))
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (fixed candidates : Finset Nat)
    {Band : Type*} [DecidableEq Band]
    (bandOf : BankPaperCanonicalTangentPrime n W -> Band)
    (cellIndex : BankPaperCanonicalTangentPrime n W -> Nat)
    (pointwiseUpper : BankPaperCanonicalTangentPrime n W -> Real)
    (prefixUpper : Band -> Nat -> Real)
    (selector : Nat -> Real)
    (S : BankPaperCanonicalRoundedSelectorTangentInput
      R certificate fixed candidates bandOf cellIndex
        pointwiseUpper prefixUpper selector)
    (flow : BankPaperCanonicalTangentPrime n W ->
      BankPaperCanonicalTangentPrime n W -> Real)
    (hflow : forall source target, 0 <= flow source target)
    (hdivergence : forall p,
      tangentFlowDivergence flow p =
        bankPaperCanonicalTangentResidual
          R certificate fixed candidates selector p)
    (L sigma : Real) :
    (forall p : BankPaperCanonicalTangentPrime n W,
      tangentFlowDivergence flow p =
        bankPaperCanonicalTangentResidual
          R certificate fixed candidates selector p) ∧
      forall q : Nat,
        (∑ request : TangentSplitRequest
              (tangentPositiveFlowEdges flow) L sigma
                (fun edge :
                    BankPaperCanonicalTangentPrime n W ×
                      BankPaperCanonicalTangentPrime n W =>
                  flow edge.1 edge.2),
            tangentSplitRequestWeight request *
              (((tangentSplitRequestSource
                    (tangentStarEdgeSource
                      bankPaperCanonicalTangentPrimeLabel)
                    request).factorization q : Real) -
                ((tangentSplitRequestTarget
                    (tangentStarEdgeTarget
                      bankPaperCanonicalTangentPrimeLabel)
                    request).factorization q : Real))) =
          bankPaperCanonicalSelectorValuationDeficit
            R certificate fixed candidates selector q := by
  apply bankPaperCanonicalDistributedSplitRequest_boundary_eq_selectorDeficit
    R certificate fixed candidates selector flow hflow hdivergence
  exact
    (bankPaperCanonicalRoundedSelectorTangentInput_selectorState S).2.2.2



/-! ## Selector bounds converted to the literal cell ledgers -/









/-! ## The explicit ratio-cell flow, rather than a supplied flow -/







end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankPaperCanonicalSectionNineAssembly -/
section


/-!
# Canonical Section 9 assembly reduction

This file assembles the already-proved finite pieces of the tangent stage.
Starting from an explicitly supplied pre-tangent selector, it uses the
literal prime-band residual, star transport, request splitting, canonical
clean-list lower bounds, pair arithmetic, the `1/8` census budget, and the
collision-free endpoint theorem.  The selected common multipliers are then
fed to the actual `tangentUpdate`; feasibility, complete-rough row sums, and
the selector-tail valuation are proved for that update.

The construction does not hide the remaining selector theorem.  Its finite
inputs still include selector feasibility and row integrality, prime-band
balance and support, uniform endpoint slack on every clean list, and the
displayed request-wise list-loss and traffic smallness comparisons.  The
final continuation wrapper also retains the genuinely geometric disjointness
conditions.
-/

open Filter
open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel

noncomputable section

/-! ## Canonical request notation -/















/-! ## Deterministic endpoint facts for clean multipliers -/

/-- Every member of a split clean list is positive. -/
theorem tangentSplitCleanMultiplier_pos
    {E : Type*} {edges : Finset E} {source target : E → ℕ}
    {L sigma : ℝ} {flow : E → ℝ}
    {n K h Phead X0 y : ℕ}
    {dedicatedRows numericalGuards : Finset ℕ}
    (request : TangentSplitRequest edges L sigma flow) {multiplier : ℕ}
    (hmultiplier : multiplier ∈
      tangentSplitCleanMultiplierLists edges source target L sigma flow
        n K h Phead X0 y dedicatedRows numericalGuards request) :
    0 < multiplier := by
  have hclean : multiplier ∈ tangentCleanCommonMultiplierList
      n K h Phead X0 y
        (max (tangentSplitRequestSource source request)
          (tangentSplitRequestTarget target request))
        (min (tangentSplitRequestSource source request)
          (tangentSplitRequestTarget target request))
        dedicatedRows numericalGuards := by
    simpa only [tangentSplitCleanMultiplierLists,
      tangentCleanMultiplierLists] using hmultiplier
  have hlower := (mem_tangentCleanCommonMultiplierList.mp hclean).1.1
  exact (Nat.zero_le _).trans_lt hlower



/-- Multiplying two permitted prime labels by the same positive common
multiplier keeps the two endpoints in the same complete-rough row. -/
theorem tangentSplitEndpoints_completeRoughLabel_eq
    {y source target multiplier : ℕ}
    (hsourcePos : 0 < source) (htargetPos : 0 < target)
    (hsourceLe : source ≤ y) (htargetLe : target ≤ y)
    (hmultiplierPos : 0 < multiplier) :
    completeRoughLabel y (source * multiplier) =
      completeRoughLabel y (target * multiplier) := by
  calc
    completeRoughLabel y (source * multiplier) =
        completeRoughLabel y multiplier :=
      completeRoughLabel_small_left_mul
        hsourcePos hsourceLe hmultiplierPos
    _ = completeRoughLabel y (target * multiplier) :=
      (completeRoughLabel_small_left_mul
        htargetPos htargetLe hmultiplierPos).symm

/-! ## Finite Section 9 assembly once clean-list lower bounds are available -/

namespace BankPaperRealization



end BankPaperRealization

namespace BankPaperRealization



end BankPaperRealization

namespace BankPaperRealization



end BankPaperRealization

namespace BankPaperRealization



end BankPaperRealization

end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankPaperCanonicalDistributedCandidateSet -/
section


/-!
# Distributed Section 9 on a guarded candidate subset

The original distributed Section 9 API is intentionally retained verbatim:
it works on `roughRawCandidateSet n h K`.  This module adds a parallel,
backward-compatible interface for an arbitrary finite candidate set contained
in that raw universe.

Containment alone does not put the endpoints selected from a clean multiplier
list back into the smaller set.  The generic post-choice theorem therefore
takes selected-endpoint membership, while pre-choice assembly takes clean-list
endpoint closure.  A concrete guarded set obtained by subtracting the
numerical guards is supplied below; its endpoint closure is derived from the
defining set difference and the existing clean-list membership theorem.  No
disjointness conclusion is inferred merely from containment in the raw
candidate set.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel

noncomputable section

/-! ## A concrete guarded candidate subset -/









namespace BankPaperRealization

/-! ## Generic deterministic post-choice socket -/

/-- Apply a chosen collision-free distributed multiplier family on an
arbitrary guarded candidate set.

The candidate set may be arbitrary.  The explicit `hselectedEndpoints` premise
is the exact closure fact needed to keep the update supported on `candidates`;
no redundant inclusion in the paper's raw candidate universe is required.

The result is otherwise identical to the raw-candidate post-choice socket.
In particular it returns the literal update, row integrality, feasibility,
and the charged valuation certificate on the supplied candidate set. -/
theorem exists_canonicalDistributedPostTangentOutput_of_multiplier_on_candidates
    {c : Real} {depth n W K h Phead X0 : Nat}
    (R : BankPaperRealization n
      (upperEndpoint n (upperTailLength c n)))
    (certificate : GuardedCentralAnchorCertificate c depth n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (fixedExceptional fixed candidates : Finset Nat)
    (selector : Nat → Real)
    {Band : Type*} [DecidableEq Band]
    (bandOf : BankPaperCanonicalTangentPrime n W → Band)
    (cellIndex : BankPaperCanonicalTangentPrime n W → Nat)
    (pointwiseUpper : BankPaperCanonicalTangentPrime n W → Real)
    (prefixUpper : Band → Nat → Real)
    (S : BankPaperCanonicalRoundedSelectorTangentInput
      R certificate fixed candidates
        bandOf cellIndex pointwiseUpper prefixUpper selector)
    (flow : BankPaperCanonicalTangentPrime n W →
      BankPaperCanonicalTangentPrime n W → Real)
    (hflowNonneg : ∀ source target, 0 ≤ flow source target)
    (hdivergence : ∀ p,
      tangentFlowDivergence flow p =
        bankPaperCanonicalTangentResidual
          R certificate fixed candidates selector p)
    (L sigma : Real)
    (hL : 0 < L) (hsigma : 0 < sigma)
    (hfixedPositive : ∀ a ∈ fixed, 0 < a)
    (hchargeDvd : R.selectorTailCharge fixed ∣
      certificate.prechargedTailTarget)
    (multiplier : BankPaperCanonicalDistributedTangentSplitRequest
      flow L sigma → Nat)
    (hmultiplierMem : ∀ request,
      multiplier request ∈
        tangentSplitCleanMultiplierLists
          (tangentPositiveFlowEdges flow)
          (tangentStarEdgeSource bankPaperCanonicalTangentPrimeLabel)
          (tangentStarEdgeTarget bankPaperCanonicalTangentPrimeLabel)
          L sigma
          (fun edge : BankPaperCanonicalTangentPrime n W ×
              BankPaperCanonicalTangentPrime n W =>
            flow edge.1 edge.2)
          n K h Phead X0 (yNat n) R.tangentPaperDedicatedRows
          (R.tangentPaperNumericalGuardSet
            certificate fixedExceptional) request)
    (hselectedEndpoints : ∀ request,
      bankPaperCanonicalDistributedTangentRequestSource request *
            multiplier request ∈ candidates ∧
        bankPaperCanonicalDistributedTangentRequestTarget request *
            multiplier request ∈ candidates)
    (hdistinct : TangentEndpointsDistinct
      (tangentSplitRequests
        (tangentPositiveFlowEdges flow) L sigma
        (fun edge : BankPaperCanonicalTangentPrime n W ×
            BankPaperCanonicalTangentPrime n W =>
          flow edge.1 edge.2))
      (bankPaperCanonicalDistributedTangentRequestSource
        (flow := flow) (L := L) (sigma := sigma))
      (bankPaperCanonicalDistributedTangentRequestTarget
        (flow := flow) (L := L) (sigma := sigma))
      multiplier)
    (hsourceSlack : ∀ request,
      sigma / L ≤ selector
          (bankPaperCanonicalDistributedTangentRequestSource request *
            multiplier request) ∧
        selector
          (bankPaperCanonicalDistributedTangentRequestSource request *
            multiplier request) ≤ 1 - sigma / L)
    (htargetSlack : ∀ request,
      sigma / L ≤ selector
          (bankPaperCanonicalDistributedTangentRequestTarget request *
            multiplier request) ∧
        selector
          (bankPaperCanonicalDistributedTangentRequestTarget request *
            multiplier request) ≤ 1 - sigma / L) :
    ∃ output : BankPaperCanonicalPostTangentOutput R certificate
        candidates fixed,
      output.selector =
        bankPaperCanonicalDistributedTangentUpdatedSelector
          flow L sigma multiplier selector := by
  let edges := tangentPositiveFlowEdges flow
  let source := tangentStarEdgeSource
    (bankPaperCanonicalTangentPrimeLabel (n := n) (W := W))
  let target := tangentStarEdgeTarget
    (bankPaperCanonicalTangentPrimeLabel (n := n) (W := W))
  let edgeFlow : BankPaperCanonicalTangentPrime n W ×
      BankPaperCanonicalTangentPrime n W → Real :=
    fun edge => flow edge.1 edge.2
  let requests := tangentSplitRequests edges L sigma edgeFlow
  let requestSource : TangentSplitRequest edges L sigma edgeFlow → ℕ :=
    tangentSplitRequestSource source
  let requestTarget : TangentSplitRequest edges L sigma edgeFlow → ℕ :=
    tangentSplitRequestTarget target
  have hstate :=
    bankPaperCanonicalRoundedSelectorTangentInput_selectorState S
  have hfeasible : ∀ a ∈ candidates,
      0 ≤ selector a ∧ selector a ≤ 1 := hstate.1
  have hrowIntegral : BankPaperCanonicalSelectorRowIntegral
      n candidates selector := hstate.2.1
  have hmultiplierMem' : ∀ request :
      TangentSplitRequest edges L sigma edgeFlow,
      multiplier request ∈
        tangentSplitCleanMultiplierLists edges source target L sigma edgeFlow
          n K h Phead X0 (yNat n) R.tangentPaperDedicatedRows
          (R.tangentPaperNumericalGuardSet
            certificate fixedExceptional) request := by
    intro request
    simpa only [edges, source, target, edgeFlow] using
      hmultiplierMem request
  have hdistinct' : TangentEndpointsDistinct requests requestSource
      requestTarget multiplier := by
    simpa only [requests, requestSource, requestTarget, edges, source, target,
      edgeFlow, bankPaperCanonicalDistributedTangentRequestSource,
      bankPaperCanonicalDistributedTangentRequestTarget] using hdistinct
  have hsourceSlack' : ∀ request :
      TangentSplitRequest edges L sigma edgeFlow,
      sigma / L ≤ selector
          (requestSource request * multiplier request) ∧
        selector (requestSource request * multiplier request) ≤
          1 - sigma / L := by
    intro request
    simpa only [requestSource, edges, source, edgeFlow,
      bankPaperCanonicalDistributedTangentRequestSource] using
        hsourceSlack request
  have htargetSlack' : ∀ request :
      TangentSplitRequest edges L sigma edgeFlow,
      sigma / L ≤ selector
          (requestTarget request * multiplier request) ∧
        selector (requestTarget request * multiplier request) ≤
          1 - sigma / L := by
    intro request
    simpa only [requestTarget, edges, target, edgeFlow,
      bankPaperCanonicalDistributedTangentRequestTarget] using
        htargetSlack request
  have hrequestPrime : ∀ request :
      TangentSplitRequest edges L sigma edgeFlow,
      (requestSource request).Prime ∧
        (requestTarget request).Prime := by
    intro request
    constructor
    · simpa only [requestSource, source, tangentSplitRequestSource,
        tangentSplitRequestEdge, tangentStarEdgeSource] using
        bankPaperCanonicalTangentPrimeLabel_prime request.1.1.1
    · simpa only [requestTarget, target, tangentSplitRequestTarget,
        tangentSplitRequestEdge, tangentStarEdgeTarget] using
        bankPaperCanonicalTangentPrimeLabel_prime request.1.1.2
  have hrequestUpper : ∀ request :
      TangentSplitRequest edges L sigma edgeFlow,
      requestSource request ≤ yNat n ∧
        requestTarget request ≤ yNat n := by
    intro request
    constructor
    · simpa only [requestSource, source, tangentSplitRequestSource,
        tangentSplitRequestEdge, tangentStarEdgeSource] using
        bankPaperCanonicalTangentPrimeLabel_le_yNat request.1.1.1
    · simpa only [requestTarget, target, tangentSplitRequestTarget,
        tangentSplitRequestEdge, tangentStarEdgeTarget] using
        bankPaperCanonicalTangentPrimeLabel_le_yNat request.1.1.2
  have hmultiplierPos : ∀ request :
      TangentSplitRequest edges L sigma edgeFlow,
      0 < multiplier request := by
    intro request
    exact tangentSplitCleanMultiplier_pos request
      (hmultiplierMem' request)
  have hendpointMem : ∀ request :
      TangentSplitRequest edges L sigma edgeFlow,
      requestSource request * multiplier request ∈ candidates ∧
        requestTarget request * multiplier request ∈ candidates := by
    intro request
    simpa only [requestSource, requestTarget, edges, source, target, edgeFlow,
      bankPaperCanonicalDistributedTangentRequestSource,
      bankPaperCanonicalDistributedTangentRequestTarget] using
        hselectedEndpoints request
  have hsameRow : ∀ request :
      TangentSplitRequest edges L sigma edgeFlow,
      completeRoughLabel (yNat n)
          (requestSource request * multiplier request) =
        completeRoughLabel (yNat n)
          (requestTarget request * multiplier request) := by
    intro request
    exact tangentSplitEndpoints_completeRoughLabel_eq
      (hrequestPrime request).1.pos (hrequestPrime request).2.pos
      (hrequestUpper request).1 (hrequestUpper request).2
      (hmultiplierPos request)
  have hflowPos : ∀ edge ∈ edges, 0 < edgeFlow edge := by
    intro edge hedge
    simpa only [edgeFlow] using
      (mem_tangentPositiveFlowEdges.mp hedge)
  have hfeasibleUpdate := tangentSplitUpdate_feasible_and_margin
    edges source target edgeFlow hflowPos hL hsigma multiplier selector
      candidates hdistinct' hsourceSlack' htargetSlack' hfeasible
  have hrowPreserve : ∀ label,
      ∑ a ∈ completeRoughRowFiber (yNat n) candidates label,
          tangentUpdate requests requestSource requestTarget multiplier
            tangentSplitRequestWeight selector a =
        ∑ a ∈ completeRoughRowFiber (yNat n) candidates label,
          selector a := by
    intro label
    simpa only [completeRoughRowFiber] using
      tangentUpdate_signatureRow requests requestSource requestTarget
        multiplier tangentSplitRequestWeight selector candidates
        (completeRoughLabel (yNat n)) label
        (fun request _hrequest => (hendpointMem request).1)
        (fun request _hrequest => (hendpointMem request).2)
        (fun request _hrequest => hsameRow request)
  have hrowIntegralUpdate :
      BankPaperCanonicalSelectorRowIntegral n candidates
        (tangentUpdate requests requestSource requestTarget multiplier
          tangentSplitRequestWeight selector) := by
    intro label hlabel
    obtain ⟨k, hk⟩ := hrowIntegral label hlabel
    exact ⟨k, (hrowPreserve label).trans hk⟩
  have hcanonical :=
    bankPaperCanonicalRoundedSelector_distributedBoundary
      R certificate fixed candidates bandOf cellIndex pointwiseUpper
      prefixUpper selector S flow hflowNonneg hdivergence L sigma
  have hboundary : ∀ q,
      ∑ request ∈ requests,
          tangentSplitRequestWeight request *
            ((requestSource request).factorization q -
              (requestTarget request).factorization q : Real) =
        ((certificate.selectorTailTarget R fixed).factorization q : Real) -
          ∑ a ∈ candidates,
            selector a * (a.factorization q : Real) := by
    intro q
    simpa only [requests, tangentSplitRequests, requestSource, requestTarget,
      source, target, edges, edgeFlow,
      bankPaperCanonicalSelectorValuationDeficit] using hcanonical.2 q
  have hresidualValuation : ∀ q,
      ∑ a ∈ candidates,
          tangentUpdate requests requestSource requestTarget multiplier
              tangentSplitRequestWeight selector a *
            (a.factorization q : Real) =
        ((certificate.selectorTailTarget R fixed).factorization q : Real) :=
    tangentUpdate_valuation_eq_target requests requestSource requestTarget
      multiplier tangentSplitRequestWeight selector candidates
      (fun q => ((certificate.selectorTailTarget R fixed).factorization q :
        Real))
      (fun request _hrequest => (hendpointMem request).1)
      (fun request _hrequest => (hendpointMem request).2)
      (fun request _hrequest => (hrequestPrime request).1.ne_zero)
      (fun request _hrequest => (hrequestPrime request).2.ne_zero)
      (fun request _hrequest => (hmultiplierPos request).ne') hboundary
  have hchargedValuation : ∀ q,
      ((fixed.prod id *
          (baseBankFactors R.exactificationState).prod id).factorization q :
            Real) +
          ∑ a ∈ candidates,
            tangentUpdate requests requestSource requestTarget multiplier
                tangentSplitRequestWeight selector a *
              (a.factorization q : Real) =
        (certificate.prechargedTailTarget.factorization q : Real) := by
    apply (certificate.valuationCertificate_iff_selectorTailTarget
      R fixed
        (fun q => ∑ a ∈ candidates,
          tangentUpdate requests requestSource requestTarget multiplier
              tangentSplitRequestWeight selector a *
            (a.factorization q : Real))
        hfixedPositive hchargeDvd).2
    exact hresidualValuation
  let output : BankPaperCanonicalPostTangentOutput R certificate
      candidates fixed := {
    selector := tangentUpdate requests requestSource requestTarget multiplier
      tangentSplitRequestWeight selector
    feasible := fun a ha => hfeasibleUpdate.1 a ha
    rowIntegral := hrowIntegralUpdate
    valuationCertificate := hchargedValuation }
  refine ⟨output, ?_⟩
  rfl

/-! ## Generic finite distributed assembly -/



end BankPaperRealization

end

end Erdos390.WholePaper

end

universe u_1
theorem solution :
∀ {c : Real} {depth n W K h Phead X0 : Nat}
  (R :
    Erdos390.WholePaper.BankPaperRealization n
      (Erdos390.WholePaper.upperEndpoint n (Erdos390.WholePaper.upperTailLength c n)))
  (certificate :
    Erdos390.WholePaper.GuardedCentralAnchorCertificate c depth n
      (Erdos390.WholePaper.BankPaperRealization.anchorGuardLeftCore R)
      (Erdos390.WholePaper.BankPaperRealization.anchorGuardRightCore R)
      (Erdos390.WholePaper.BankPaperRealization.centralChangedMarkers R depth))
  (fixedExceptional fixed candidates : Finset.{0} Nat) (selector : Nat → Real) {Band : Type u_1}
  [inst : DecidableEq.{u_1 + 1} Band] (bandOf : Erdos390.WholePaper.BankPaperCanonicalTangentPrime n W → Band)
  (cellIndex : Erdos390.WholePaper.BankPaperCanonicalTangentPrime n W → Nat)
  (pointwiseUpper : Erdos390.WholePaper.BankPaperCanonicalTangentPrime n W → Real) (prefixUpper : Band → Nat → Real),
  Erdos390.WholePaper.BankPaperCanonicalRoundedSelectorTangentInput.{u_1} R certificate fixed candidates bandOf
      cellIndex pointwiseUpper prefixUpper selector →
    ∀
      (flow :
        Erdos390.WholePaper.BankPaperCanonicalTangentPrime n W →
          Erdos390.WholePaper.BankPaperCanonicalTangentPrime n W → Real),
      (∀ (source target : Erdos390.WholePaper.BankPaperCanonicalTangentPrime n W),
          LE.le.{0} (0 : Real) (flow source target)) →
        (∀ (p : Erdos390.WholePaper.BankPaperCanonicalTangentPrime n W),
            Eq.{1} (Erdos390.WholePaper.tangentFlowDivergence.{0} flow p)
              (Erdos390.WholePaper.bankPaperCanonicalTangentResidual R certificate fixed candidates selector p)) →
          ∀ (L sigma : Real),
            LT.lt.{0} (0 : Real) L →
              LT.lt.{0} (0 : Real) sigma →
                (∀ (a : Nat), Membership.mem.{0, 0} fixed a → LT.lt.{0} (0 : Nat) a) →
                  Dvd.dvd.{0} (Erdos390.WholePaper.BankPaperRealization.selectorTailCharge R fixed)
                      (Erdos390.WholePaper.GuardedCentralAnchorCertificate.prechargedTailTarget certificate) →
                    ∀
                      (multiplier :
                        Erdos390.WholePaper.BankPaperCanonicalDistributedTangentSplitRequest flow L sigma → Nat),
                      (∀
                          (request :
                            Erdos390.WholePaper.TangentSplitRequest.{0}
                              (Erdos390.WholePaper.tangentPositiveFlowEdges.{0} flow) L sigma
                              fun
                                (edge :
                                  Prod.{0, 0} (Erdos390.WholePaper.BankPaperCanonicalTangentPrime n W)
                                    (Erdos390.WholePaper.BankPaperCanonicalTangentPrime n W)) =>
                              flow edge.1 edge.2),
                          Membership.mem.{0, 0}
                            (Erdos390.WholePaper.tangentSplitCleanMultiplierLists.{0}
                              (Erdos390.WholePaper.tangentPositiveFlowEdges.{0} flow)
                              (Erdos390.WholePaper.tangentStarEdgeSource.{0}
                                Erdos390.WholePaper.bankPaperCanonicalTangentPrimeLabel)
                              (Erdos390.WholePaper.tangentStarEdgeTarget.{0}
                                Erdos390.WholePaper.bankPaperCanonicalTangentPrimeLabel)
                              L sigma
                              (fun
                                  (edge :
                                    Prod.{0, 0} (Erdos390.WholePaper.BankPaperCanonicalTangentPrime n W)
                                      (Erdos390.WholePaper.BankPaperCanonicalTangentPrime n W)) =>
                                flow edge.1 edge.2)
                              n K h Phead X0 (Erdos390.Full.ArithmeticModel.yNat n)
                              (Erdos390.WholePaper.BankPaperRealization.tangentPaperDedicatedRows R)
                              (Erdos390.WholePaper.BankPaperRealization.tangentPaperNumericalGuardSet R certificate
                                fixedExceptional)
                              request)
                            (multiplier request)) →
                        (∀
                            (request :
                              Erdos390.WholePaper.BankPaperCanonicalDistributedTangentSplitRequest flow L sigma),
                            And
                              (Membership.mem.{0, 0} candidates
                                (HMul.hMul.{0, 0, 0}
                                  (Erdos390.WholePaper.bankPaperCanonicalDistributedTangentRequestSource request)
                                  (multiplier request)))
                              (Membership.mem.{0, 0} candidates
                                (HMul.hMul.{0, 0, 0}
                                  (Erdos390.WholePaper.bankPaperCanonicalDistributedTangentRequestTarget request)
                                  (multiplier request)))) →
                          Erdos390.WholePaper.TangentEndpointsDistinct.{0}
                              (Erdos390.WholePaper.tangentSplitRequests.{0}
                                (Erdos390.WholePaper.tangentPositiveFlowEdges.{0} flow) L sigma
                                fun
                                  (edge :
                                    Prod.{0, 0} (Erdos390.WholePaper.BankPaperCanonicalTangentPrime n W)
                                      (Erdos390.WholePaper.BankPaperCanonicalTangentPrime n W)) =>
                                flow edge.1 edge.2)
                              Erdos390.WholePaper.bankPaperCanonicalDistributedTangentRequestSource
                              Erdos390.WholePaper.bankPaperCanonicalDistributedTangentRequestTarget multiplier →
                            (∀
                                (request :
                                  Erdos390.WholePaper.BankPaperCanonicalDistributedTangentSplitRequest flow L sigma),
                                And
                                  (LE.le.{0} (HDiv.hDiv.{0, 0, 0} sigma L)
                                    (selector
                                      (HMul.hMul.{0, 0, 0}
                                        (Erdos390.WholePaper.bankPaperCanonicalDistributedTangentRequestSource request)
                                        (multiplier request))))
                                  (LE.le.{0}
                                    (selector
                                      (HMul.hMul.{0, 0, 0}
                                        (Erdos390.WholePaper.bankPaperCanonicalDistributedTangentRequestSource request)
                                        (multiplier request)))
                                    (HSub.hSub.{0, 0, 0} (1 : Real) (HDiv.hDiv.{0, 0, 0} sigma L)))) →
                              (∀
                                  (request :
                                    Erdos390.WholePaper.BankPaperCanonicalDistributedTangentSplitRequest flow L sigma),
                                  And
                                    (LE.le.{0} (HDiv.hDiv.{0, 0, 0} sigma L)
                                      (selector
                                        (HMul.hMul.{0, 0, 0}
                                          (Erdos390.WholePaper.bankPaperCanonicalDistributedTangentRequestTarget
                                            request)
                                          (multiplier request))))
                                    (LE.le.{0}
                                      (selector
                                        (HMul.hMul.{0, 0, 0}
                                          (Erdos390.WholePaper.bankPaperCanonicalDistributedTangentRequestTarget
                                            request)
                                          (multiplier request)))
                                      (HSub.hSub.{0, 0, 0} (1 : Real) (HDiv.hDiv.{0, 0, 0} sigma L)))) →
                                ∃ (output :
                                  Erdos390.WholePaper.BankPaperCanonicalPostTangentOutput R certificate candidates
                                    fixed),
                                  Eq.{1} (Erdos390.WholePaper.BankPaperCanonicalPostTangentOutput.selector output)
                                    (Erdos390.WholePaper.bankPaperCanonicalDistributedTangentUpdatedSelector flow L
                                      sigma multiplier selector) := by
  exact @Erdos390.WholePaper.BankPaperRealization.exists_canonicalDistributedPostTangentOutput_of_multiplier_on_candidates
