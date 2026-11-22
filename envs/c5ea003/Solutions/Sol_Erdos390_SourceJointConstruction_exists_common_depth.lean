-- Prove2me | solution 1 for Erdos390.SourceJointConstruction.exists_common_depth
-- status  : ACCEPTED   (prove)
-- author  : @doctosil
-- created : 2026-09-17T17:25:57.972584+00:00
-- url     : https://prove2.me/submissions/81cb4b10-5fa2-4736-a045-cb9b0a888001

import Mathlib
import Definitions.Def_erdos390_source_bank_interface
import Definitions.Def_erdos390_dickman_step_function
import Theorems.Thm_MediumPNT
import Definitions.Def_erdos390_analytic_foundations_001
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_product_bound
import Theorems.Thm_Erdos390_Full_DickmanBasic_rho_pos_on_zero_five
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_secondDerivative_first_bound
import Definitions.Def_erdos390_analytic_foundations_002
import Definitions.Def_erdos390_analytic_foundations_003
import Definitions.Def_erdos390_analytic_foundations_005
import Definitions.Def_erdos390_analytic_foundations_006
import Definitions.Def_erdos390_analytic_foundations_007
import Definitions.Def_erdos390_analytic_foundations_008
import Definitions.Def_erdos390_analytic_foundations_010
import Theorems.Thm_Erdos390_WholePaper_BankPaperRealization_exists_bankPaperCanonicalSectionNinePostHeight_sourceFirstCutoffAwareDistributedTerminal_compact


section
theorem Erdos390.WholePaper.BankPaperRealization.exists_bankPaperCanonicalSectionNinePostHeight_sourceFirstCutoffAwareDistributedTerminal : Erdos390.RemainingAnalyticGoal004_020 := @Erdos390.WholePaper.BankPaperRealization.exists_bankPaperCanonicalSectionNinePostHeight_sourceFirstCutoffAwareDistributedTerminal_compact
end
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







/-! ## Finite Section 9 assembly once clean-list lower bounds are available -/

namespace BankPaperRealization



end BankPaperRealization

namespace BankPaperRealization



end BankPaperRealization

namespace BankPaperRealization



end BankPaperRealization

namespace BankPaperRealization

/-- Convert the finite post-tangent output into exactly the existential data
requested by `BankPaperCanonicalPostTangentContinuationAtDepth`.  The only
extra premises are the interval, divisibility, and disjointness geometry
which that continuation itself records. -/
theorem canonicalPostTangentContinuationData_of_output
    {c : ℝ} {depth n : ℕ}
    (R : BankPaperRealization n
      (upperEndpoint n (upperTailLength c n)))
    (certificate : GuardedCentralAnchorCertificate c depth n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (candidates fixed : Finset ℕ)
    (output : BankPaperCanonicalPostTangentOutput
      R certificate candidates fixed)
    (hcandidates : candidates ⊆
      factorInterval n (upperEndpoint n (upperTailLength c n)))
    (hfixed : fixed ⊆
      factorInterval n (upperEndpoint n (upperTailLength c n)))
    (hchargeDvd : R.selectorTailCharge fixed ∣
      certificate.prechargedTailTarget)
    (hfixedCandidate : Disjoint fixed candidates)
    (hfixedBank : ∀ slot selected,
      Disjoint fixed (R.exactificationState slot selected))
    (hcandidateBank : ∀ slot selected,
      Disjoint candidates (R.exactificationState slot selected))
    (hanchorsFixed : Disjoint certificate.anchors fixed)
    (hanchorsCandidate : Disjoint certificate.anchors candidates) :
    ∃ candidates' : Finset ℕ, ∃ selector : ℕ → ℝ,
      ∃ fixed' : Finset ℕ,
        candidates' ⊆
            factorInterval n (upperEndpoint n (upperTailLength c n)) ∧
        fixed' ⊆
            factorInterval n (upperEndpoint n (upperTailLength c n)) ∧
        (∀ a ∈ candidates', 0 ≤ selector a ∧ selector a ≤ 1) ∧
        (∀ label ∈ completeRoughLabelSet (yNat n) candidates',
          ∃ k : ℤ,
            ∑ a ∈ completeRoughRowFiber
                (yNat n) candidates' label, selector a = (k : ℝ)) ∧
        R.selectorTailCharge fixed' ∣
          certificate.prechargedTailTarget ∧
        (∀ q,
          ∑ a ∈ candidates',
              selector a * (a.factorization q : ℝ) =
            ((certificate.selectorTailTarget R fixed').factorization q :
              ℝ)) ∧
        Disjoint fixed' candidates' ∧
        (∀ slot selected,
          Disjoint fixed' (R.exactificationState slot selected)) ∧
        (∀ slot selected,
          Disjoint candidates'
            (R.exactificationState slot selected)) ∧
        Disjoint certificate.anchors fixed' ∧
        Disjoint certificate.anchors candidates' := by
  have hfixedPositive : ∀ a ∈ fixed, 0 < a := by
    intro a ha
    have haInterval : a ∈
        Finset.Ioc n (upperEndpoint n (upperTailLength c n)) := by
      simpa only [factorInterval] using hfixed ha
    exact Nat.zero_lt_of_lt (Finset.mem_Ioc.mp haInterval).1
  have hresidualValuation : ∀ q,
      ∑ a ∈ candidates,
          output.selector a * (a.factorization q : ℝ) =
        ((certificate.selectorTailTarget R fixed).factorization q : ℝ) := by
    apply (certificate.valuationCertificate_iff_selectorTailTarget
      R fixed
        (fun q ↦ ∑ a ∈ candidates,
          output.selector a * (a.factorization q : ℝ))
        hfixedPositive hchargeDvd).1
    exact output.valuationCertificate
  exact ⟨candidates, output.selector, fixed, hcandidates, hfixed,
    output.feasible, output.rowIntegral, hchargeDvd, hresidualValuation,
    hfixedCandidate, hfixedBank, hcandidateBank, hanchorsFixed,
    hanchorsCandidate⟩

end BankPaperRealization

end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankPaperCanonicalDistributedSectionNineTerminal -/
section


/-!
# Distributed Section 9 terminal at the capacity depth

`BankPaperCanonicalSectionNineFinalPayload` is a genuinely finite object.  It
contains the selected clean multipliers, endpoint collision-freedom, exact
flow and valuation boundaries, the actual post-tangent output, tail-charge
divisibility, and all seven final interval/collision facts.  The capacity
stage, on the other hand, supplies its bank and guarded anchor certificate
existentially.

This file keeps those witnesses synchronized.  The fixed-depth terminal below
asks, eventually, for one capacity-stage bank/certificate together with one
finite final payload for that same bank, certificate, and depth.  It is
strictly more concrete than a post-tangent continuation: its premise exposes
the complete distributed payload rather than assuming the continuation it is
meant to prove.

The existing `BankPaperCanonicalSectionNineOutputAtDepth` is intentionally not
used as an intermediate proposition.  That interface asks for a Section 9
output for every bank/certificate satisfying the three capacity facts,
whereas both the capacity theorem and the finite construction choose one
synchronized existential pair.  Instead we apply
`canonicalPostTangentContinuationData_of_output` directly to the output and
geometry carried by the finite payload.
-/

open scoped BigOperators
open Filter

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel

noncomputable section

namespace BankPaperRealization

/-! ## Finite payload projection -/

/-- Forget the transport witnesses retained by the final payload and expose
exactly the finite output, divisibility, interval, and collision data consumed
by `canonicalPostTangentContinuationData_of_output`.

No clean-list or analytic hypothesis is discarded before the payload is
constructed: the clean multipliers are fields of the payload, while the
Post-Hfit, actual-P87, and scalar budget hypotheses are the explicit inputs of
`bankPaperCanonicalSectionNineFinalPayload_of_roundedSelector_guardedSlack`. -/
theorem bankPaperCanonicalSectionNineFinalPayload_to_outputData
    {c : ℝ} {depth n W K : ℕ}
    (R : BankPaperRealization n
      (upperEndpoint n (upperTailLength c n)))
    (certificate : GuardedCentralAnchorCertificate c depth n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (deltaStar : ℝ) (selector : ℕ → ℝ)
    (flow : BankPaperCanonicalTangentPrime n W →
      BankPaperCanonicalTangentPrime n W → ℝ)
    (L sigma : ℝ)
    (hpayload :
      R.BankPaperCanonicalSectionNineFinalPayload (K := K)
        certificate deltaStar selector flow L sigma) :
    ∃ _output : BankPaperCanonicalPostTangentOutput R certificate
        (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
        (R.paperFixedExceptionalFactors deltaStar),
      R.roughCanonicalGuardedCandidateSet certificate deltaStar K ⊆
          factorInterval n
            (upperEndpoint n (upperTailLength c n)) ∧
        R.paperFixedExceptionalFactors deltaStar ⊆
          factorInterval n
            (upperEndpoint n (upperTailLength c n)) ∧
        R.selectorTailCharge
              (R.paperFixedExceptionalFactors deltaStar) ∣
            certificate.prechargedTailTarget ∧
        Disjoint (R.paperFixedExceptionalFactors deltaStar)
          (R.roughCanonicalGuardedCandidateSet
            certificate deltaStar K) ∧
        (∀ slot selected,
          Disjoint (R.paperFixedExceptionalFactors deltaStar)
            (R.exactificationState slot selected)) ∧
        (∀ slot selected,
          Disjoint
            (R.roughCanonicalGuardedCandidateSet
              certificate deltaStar K)
            (R.exactificationState slot selected)) ∧
        Disjoint certificate.anchors
          (R.paperFixedExceptionalFactors deltaStar) ∧
        Disjoint certificate.anchors
          (R.roughCanonicalGuardedCandidateSet
            certificate deltaStar K) := by
  unfold BankPaperCanonicalSectionNineFinalPayload at hpayload
  obtain ⟨_multiplier, _hmultiplier, _hdistinct, _hdivergence,
    _hboundary, output, _hselector, hchargeDvd, hgeometry⟩ := hpayload
  unfold BankPaperCanonicalSectionNineFinalGeometry at hgeometry
  obtain ⟨hcandidates, hfixed, hfixedCandidate, hfixedBank,
    hcandidateBank, hanchorsFixed, hanchorsCandidate⟩ := hgeometry
  exact ⟨output, hcandidates, hfixed, hchargeDvd, hfixedCandidate,
    hfixedBank, hcandidateBank, hanchorsFixed, hanchorsCandidate⟩

end BankPaperRealization

/-! ## Synchronized fixed-depth terminal -/



/-- The synchronized terminal retains the complete fixed-depth capacity
premise needed by the fixed-depth upper-endpoint bridge. -/
theorem
    BankPaperCanonicalDistributedSectionNineTerminalAtDepth.to_canonicalCapacityAtDepth
    {c deltaStar : ℝ} {depth : ℕ}
    (H :
      BankPaperCanonicalDistributedSectionNineTerminalAtDepth
        c deltaStar depth) :
    BankPaperCanonicalCapacityAtDepth c depth := by
  simp only [BankPaperCanonicalDistributedSectionNineTerminalAtDepth] at H
  simp only [BankPaperCanonicalCapacityAtDepth]
  filter_upwards [H] with n Hn
  obtain ⟨R, certificate, hcombined, hbaseDvd, htargetTail,
    _W, _K, _selector, _flow, _L, _sigma, _hpayload⟩ := Hn
  exact ⟨R, certificate, hcombined, hbaseDvd, htargetTail⟩

/-- A synchronized finite distributed terminal gives the exact canonical
post-tangent continuation at that same depth.

The capacity argument of the continuation is not used to replace the
terminal witnesses: the terminal already contains its own synchronized
capacity witnesses and finite payload. -/
theorem
    BankPaperCanonicalDistributedSectionNineTerminalAtDepth.to_postTangentContinuationAtDepth
    {c deltaStar : ℝ} {depth : ℕ}
    (H :
      BankPaperCanonicalDistributedSectionNineTerminalAtDepth
        c deltaStar depth) :
    BankPaperCanonicalPostTangentContinuationAtDepth c depth := by
  simp only [BankPaperCanonicalPostTangentContinuationAtDepth]
  intro _hcapacity
  simp only [BankPaperCanonicalDistributedSectionNineTerminalAtDepth] at H
  filter_upwards [H] with n Hn
  obtain ⟨R, certificate, hcombined, hbaseDvd, htargetTail,
    W, K, selector, flow, L, sigma, hpayload⟩ := Hn
  obtain ⟨output, hcandidates, hfixed, hchargeDvd, hfixedCandidate,
    hfixedBank, hcandidateBank, hanchorsFixed, hanchorsCandidate⟩ :=
    R.bankPaperCanonicalSectionNineFinalPayload_to_outputData
      certificate deltaStar selector flow L sigma hpayload
  refine ⟨R, certificate, hcombined, hbaseDvd, htargetTail, ?_⟩
  exact R.canonicalPostTangentContinuationData_of_output certificate
    (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
    (R.paperFixedExceptionalFactors deltaStar) output
    hcandidates hfixed hchargeDvd hfixedCandidate hfixedBank
    hcandidateBank hanchorsFixed hanchorsCandidate

/-! ## Same-depth upper endpoint -/



/-! ## Depth-first main terminal -/







end

end Erdos390.WholePaper

end

/- Source module: SourceWitness -/
section


open Filter
open Erdos390.WholePaper

/-- The closed source construction chooses a common capacity depth for both
capacity and post-tangent continuation. This interface discards the analytic
cutoffs that the final witness extraction does not use. -/
theorem Erdos390.SourceJointConstruction.exists_common_depth
    {c : ℝ} (hc : Erdos390.WholePaper.C0 < c) :
    ∃ depth : ℕ, 201 ≤ depth ∧
      BankPaperCanonicalCapacityAtDepth c depth ∧
      BankPaperCanonicalPostTangentContinuationAtDepth c depth := by
  obtain ⟨depth, W, r0, deltaStar, hdepth, _, _, _, _, _, _, _, _, Hterminal⟩ :=
    BankPaperRealization.exists_bankPaperCanonicalSectionNinePostHeight_sourceFirstCutoffAwareDistributedTerminal
      hc
  exact ⟨depth, hdepth, Hterminal.to_canonicalCapacityAtDepth,
    Hterminal.to_postTangentContinuationAtDepth⟩

end

theorem solution :
∀ {c : Real},
  LT.lt.{0} Erdos390.WholePaper.C0 c →
    ∃ depth,
      And (LE.le.{0} (201 : Nat) depth)
        (And (Erdos390.WholePaper.BankPaperCanonicalCapacityAtDepth c depth)
          (Erdos390.WholePaper.BankPaperCanonicalPostTangentContinuationAtDepth c depth)) := by
  exact @Erdos390.SourceJointConstruction.exists_common_depth
