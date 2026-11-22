-- Prove2me | solution 1 for Erdos390.WholePaper.BankPaperRealization.exists_bankPaperCanonicalSectionNinePostHeight_sourceInputsAndPrimitiveGapsAt_of_canonical
-- status  : ACCEPTED   (prove)
-- author  : @doctosil
-- created : 2026-09-17T15:55:46.924797+00:00
-- url     : https://prove2.me/submissions/905741b3-c5bd-4237-b26e-3ff88093780a

import Mathlib
import Definitions.Def_erdos390_source_bank_interface
import Definitions.Def_erdos390_dickman_step_function
import Theorems.Thm_MediumPNT
import Definitions.Def_erdos390_analytic_foundations_001
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_product_bound
import Theorems.Thm_Erdos390_Full_DickmanBasic_rho_pos_on_zero_five
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_secondDerivative_first_bound
import Definitions.Def_erdos390_analytic_foundations_002
import Definitions.Def_erdos390_analytic_foundations_006
import Definitions.Def_erdos390_analytic_foundations_007
import Definitions.Def_erdos390_analytic_foundations_008
import Definitions.Def_erdos390_analytic_foundations_009
import Definitions.Def_erdos390_analytic_foundations_010

/- Source module: Erdos390.Full.PaperBridgeFit -/
section


/-!
# The finite arithmetic data in the bridge fit

This file instantiates the nonlinear finite-family layer with the actual
objects appearing in Lemmas 8.5--8.6 and Proposition 8.7: guarded smooth
structured cells, arithmetic prime bands, valuation statistics, the physical
logarithm, centered head indicators, and the compensated slow score.

The sample is the tagged disjoint union of the paper's cells.  Tagging is the
formal counterpart of the disjointification performed before normalization;
the underlying integer remains available as `Sample.value`.

All statements in this file are finite identities.  Asymptotic marked-smooth
estimates are not silently inserted as hypotheses equivalent to the desired
fit.  Where a later analytic estimate is still needed, the exact finite
quantity it must bound is exposed explicitly.
-/

open scoped BigOperators
open Metric Set

namespace Erdos390.Full

noncomputable section

open ArithmeticModel StructuredCells HeadPattern

namespace PaperBridgeFit







namespace StructuredSampleData

variable {Head : Type*} [Fintype Head]





























/-- Every integer in the guarded sample is smooth at the paper's integral
cutoff.  Guard deletion changes neither smoothness nor the head pattern. -/
theorem value_mem_smoothNumbers (D : StructuredSampleData Head) (m : D.Sample) :
    D.value m ∈ Nat.smoothNumbers (yNat D.n + 1) := by
  have hm : D.value m ∈ structuredCell
      (D.pattern (D.cellOf m).1) (D.lo (D.cellOf m).2)
      (D.hi (D.cellOf m).2) (yNat D.n) :=
    (Finset.mem_sdiff.mp (D.value_mem_cell m)).1
  exact (mem_smoothInterval.mp (mem_structuredCell.mp hm).1).2.2

theorem value_not_guard (D : StructuredSampleData Head) (m : D.Sample) :
    D.value m ∉ D.guards :=
  (Finset.mem_sdiff.mp (D.value_mem_cell m)).2



end StructuredSampleData



namespace BaselineAllocation

variable {Head : Type*} [Fintype Head]
  {D : StructuredSampleData Head}



















end BaselineAllocation









namespace BridgeData

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]
  (B : BridgeData Head Band)

















































































/-! ### Exact main/nuisance coordinate splitting -/

































































































































/-! ## Exact target and moment correspondence -/















































































/-! ## Actual baseline mixture and coarse cells -/





























































































/-! ## Explicit finite diameter -/





















/-! ## A finite `ell^1` tilt bound -/













































/-! ## Target envelopes imply the ODE radius margin -/















/-! ## Concrete Proposition 8.7 endpoint -/











end BridgeData

/-! ## Non-circular order of asymptotic choices -/



end PaperBridgeFit

end


end Erdos390.Full

end

/- Source module: Erdos390.Full.PaperHeadSimplex -/
section


/-!
# The literal finite head-pattern simplex used in Section 8

For a fixed finite head-prime set `P` and a positive exponent `E`, the paper
uses the vertices `0` and `E e_p`.  This module constructs those exact
valuation patterns and proves that two different vertices cannot contain the
same positive integer.  The result discharges the cell-disjointness premise
used when tagged structured cells are returned to literal integer
coordinates.
-/

namespace Erdos390.Full.PaperHeadSimplex

noncomputable section













/-- Distinct simplex vertices disagree at a common head prime. -/
theorem patternsSeparated (P : Finset Nat)
    (hprime : ∀ p ∈ P, p.Prime) (E : Nat) (hE : 0 < E) :
    forall h k : Tag P, h ≠ k -> exists p,
      p ∈ (pattern P hprime E h).primes ∧
      p ∈ (pattern P hprime E k).primes ∧
      (pattern P hprime E h).exponent p ≠
        (pattern P hprime E k).exponent p := by
  intro h k hne
  cases h with
  | none =>
      cases k with
      | none => exact (hne rfl).elim
      | some q =>
          refine ⟨q.1, q.2, q.2, ?_⟩
          simp only [pattern, exponent_none, exponent_some_self]
          exact Nat.ne_of_lt hE
  | some p =>
      cases k with
      | none =>
          refine ⟨p.1, p.2, p.2, ?_⟩
          simp only [pattern, exponent_some_self, exponent_none]
          exact Nat.ne_of_gt hE
      | some q =>
          have hpq : p.1 ≠ q.1 := by
            intro hpq
            have hpqSubtype : p = q := Subtype.ext hpq
            exact hne (congrArg some hpqSubtype)
          refine ⟨p.1, p.2, p.2, ?_⟩
          simp only [pattern, exponent_some_self]
          rw [exponent_some_ne P E q p.1 hpq]
          exact Nat.ne_of_gt hE

end

end Erdos390.Full.PaperHeadSimplex

end

/- Source module: Erdos390.Full.PaperBridgeFitFeasibility -/
section


/-!
# Feasibility and frozen-ledger consequences of the actual bridge tilt

The nonlinear bridge changes only the active structured-cell coordinates.
This file records, for the literal finite exponential family used in
`PaperBridgeFit`, the conclusions which are independent of the analytic
covariance estimates: positivity, preservation of the active mass, an
explicit coordinate ceiling on a preselected parameter ball, and literal
preservation of every frozen top/protected coordinate and integer quota.

The coordinate ceiling is not postulated as a property of the output.  It is
deduced from the exact finite density-ratio estimate and an explicit baseline
slack inequality.  In the final Proposition 8.7 specialization that baseline
slack is discharged by the structured-cell count and the paper's `O(1/L)`
baseline-coordinate bound.
-/

open scoped BigOperators

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

open FiniteExponentialFamily

namespace StructuredSampleData

variable {Head : Type*} [Fintype Head]





/-- The literal `0, E e_p` head simplex used in the paper automatically
satisfies `HeadPatternsSeparated`; this is not an extra final hypothesis. -/
theorem headPatternsSeparated_of_paperHeadSimplex
    (P : Finset Nat) (hprime : ∀ p ∈ P, p.Prime)
    (E : Nat) (hE : 0 < E)
    (D : StructuredSampleData (PaperHeadSimplex.Tag P))
    (hpattern : D.pattern = PaperHeadSimplex.pattern P hprime E) :
    D.HeadPatternsSeparated := by
  rw [HeadPatternsSeparated, hpattern]
  exact PaperHeadSimplex.patternsSeparated P hprime E hE

end StructuredSampleData

namespace BridgeData

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]
  (B : BridgeData Head Band)











/-! The paper uses a compact *effective-score* box, not the crude sum of
all score norms.  The next estimates therefore take the correct pointwise
score bound and have constants independent of the number of active cells. -/













/-! ## Actual natural-number coordinates -/

















/-! ## Frozen top/protected coordinates and the integer ledger -/

















end BridgeData

end

end Erdos390.Full.PaperBridgeFit

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

/-- A simultaneous `divisor * bank` charge makes the actual precharge
product divide the residual target. -/
theorem prechargeBaseStateProduct_dvd_prechargedTailTarget
    {c : ℝ} {depth n : ℕ} {left right : ℕ → ℕ}
    {changed : Finset ℕ}
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (R : BankPaperRealization n
      (upperEndpoint n (upperTailLength c n)))
    (hcombined :
      centralAnchorDivisor n (centralAnchorCutoff depth n) certificate.q *
          R.prechargeBaseStateProduct ∣
        centralTailProduct n (upperTailLength c n)) :
    R.prechargeBaseStateProduct ∣ certificate.prechargedTailTarget := by
  exact (Nat.dvd_div_iff_mul_dvd certificate.divisor_dvd_tail).2 hcombined

/-- The exact same divisibility in the generic exactification notation. -/
theorem baseExactificationBank_prod_dvd_prechargedTailTarget
    {c : ℝ} {depth n : ℕ} {left right : ℕ → ℕ}
    {changed : Finset ℕ}
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (R : BankPaperRealization n
      (upperEndpoint n (upperTailLength c n)))
    (hcombined :
      centralAnchorDivisor n (centralAnchorCutoff depth n) certificate.q *
          R.prechargeBaseStateProduct ∣
        centralTailProduct n (upperTailLength c n)) :
    (baseBankFactors R.exactificationState).prod id ∣
      certificate.prechargedTailTarget := by
  rw [R.baseExactificationBank_prod_eq_prechargeBaseStateProduct]
  exact certificate.prechargeBaseStateProduct_dvd_prechargedTailTarget
    R hcombined

end GuardedCentralAnchorCertificate

end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankPaperCanonicalActualActiveMeasureAdditiveRefinement -/
section


/-!
# Actual active measure carried by the protected additive refinement

The canonical scaled active seed has exact literal mass `q`.  The protected
additive refinement places its ambient push-forward below the pre-selector
by construction: on every active coordinate it is the active weight plus
the nonnegative protected constant `betaProt / L`.

This file joins those two independent facts.  It proves the minimized
coordinate-fit predicate, candidate nonnegativity, and hence the full
actual-active-measure constructor on the literal guarded candidate set.
The first connector below records the older, stronger hypothesis that all
structured active values lie in the guarded *broad* correction pool.  That
hypothesis is false for the nonzero paper head vertices: the correction pool
is head-free.  The second half of the file therefore gives the literal
paper-faithful placement.  It extends the protected refinement only on the
finite structured active image, which already lies in the guarded smooth
row, and leaves the old refinement unchanged on its whole correction pool.
Its exact capacity predicate is discharged either pointwise or from the
existing cell-density/base-weight bound.

No rounded-selector transport is asserted here.  Replacing a smooth row
can change its integer row sum and prime moments; those equalities are the
separate additive-ledger boundary recorded by the refinement module.
-/

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.PaperBridgeFit
open Erdos390.Full.PaperGuardCensus

noncomputable section

namespace BankPaperRealization

/-! ## Pointwise fit and feasibility -/





/-! ## Full guarded actual-measure constructor -/



/-! ## Structured placement on the whole guarded smooth row

The broad correction pool is the head-free part of the smooth row, whereas
the structured sample contains the nonzero paper head vertices as well.  The
following selector therefore keeps the protected refinement on its original
pool and, at every remaining structured active value, installs precisely the
active seed (the protected layer is zero there). -/

/-- Fixed physical endpoints in `[1,2]` put every structured value in the
literal interval `(n,2n]`. -/
theorem bankPaperCanonicalStructuredValue_bounds_of_physicalIntervals
    {Head Band : Type*} [Fintype Head] [DecidableEq Head]
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData Head Band)
    (I : PhysicalIntervals)
    (hlowerOne : forall sigma, 1 <= I.lower sigma)
    (hupperTwo : forall sigma, I.upper sigma <= 2)
    (hlo : forall sigma, B.sampleData.lo sigma =
      physicalBound (I.lower sigma) B.sampleData.n)
    (hhi : forall sigma, B.sampleData.hi sigma =
      physicalBound (I.upper sigma) B.sampleData.n) :
    (forall m : B.sampleData.Sample,
      B.sampleData.n < B.sampleData.value m) ∧
      forall m : B.sampleData.Sample,
        B.sampleData.value m <= 2 * B.sampleData.n := by
  constructor
  · intro m
    have hnlo : B.sampleData.n <=
        B.sampleData.lo (B.sampleData.cellOf m).2 := by
      rw [hlo]
      unfold physicalBound
      apply Nat.le_floor
      exact_mod_cast (show (B.sampleData.n : Real) <=
        I.lower (B.sampleData.cellOf m).2 *
          (B.sampleData.n : Real) by
        nlinarith [show (0 : Real) <= (B.sampleData.n : Real) by
          positivity,
          hlowerOne (B.sampleData.cellOf m).2])
    exact hnlo.trans_lt (B.sampleData.lo_lt_value m)
  · intro m
    let sigma := (B.sampleData.cellOf m).2
    have hvalue : B.sampleData.value m <=
        physicalBound (I.upper sigma) B.sampleData.n := by
      simpa only [sigma, hhi] using B.sampleData.value_le_hi m
    have hupperPos : 0 < I.upper sigma :=
      (I.lower_pos sigma).trans (I.lower_lt_upper sigma)
    have hfloor :
        (physicalBound (I.upper sigma) B.sampleData.n : Real) <=
          I.upper sigma * (B.sampleData.n : Real) := by
      unfold physicalBound
      exact Nat.floor_le
        (mul_nonneg hupperPos.le (by positivity))
    have htwo : I.upper sigma * (B.sampleData.n : Real) <=
        2 * (B.sampleData.n : Real) :=
      mul_le_mul_of_nonneg_right (hupperTwo sigma) (by positivity)
    have hbound : physicalBound (I.upper sigma) B.sampleData.n <=
        2 * B.sampleData.n := by
      have hcast := hfloor.trans htwo
      exact_mod_cast hcast
    exact hvalue.trans hbound





















/-! ## Exact frozen remainder of the corrected placement -/











/-! ## Exact coordinate capacity and selector feasibility -/









/-! ## Full guarded constructor with the corrected placement -/









end BankPaperRealization

end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankPaperCanonicalBridgeRelevantGuardLedger -/
section


/-!
# The bridge-relevant numerical-guard ledger

The literal rough construction uses the global five-family guard

`anchors ∪ fixedExceptional ∪ donors ∪ baseState ∪ alternateState`.

That global set is not the guard census used by the smooth bridge.  Fixed
exceptional factors and donors lie above `2n`, while the two bank endpoint
states have a prime complete-rough label above `yNat n`.  Hence, on the
positive `yNat n`-smooth values at most `2n` which occur in every bridge
cell, the global guard agrees exactly with the promoted residual anchors
whose base prime is at most `yNat n`.

This file makes that relevant guard literal.  Its cardinality is at most
`yNat n`, so it fits in the promoted part of `GuardSlot`.  We adjoin the
harmless sentinel value `0` before enumerating it.  This avoids a false
nonemptiness requirement on an image of a nonempty slot type; the sentinel
cannot occur in a structured cell.  Two promoted slots per smooth integer
therefore suffice uniformly, and no bank slot is required.

Thus the correct replacement for a global
`ledger.guards = roughCanonicalGuardSet` hypothesis is the eventual local
predicate `BankPaperCanonicalBridgeGuardAgreement`.  A total fixed ledger
family, chosen before any realization or certificate, uses a harmless
zero-valued fallback on the finite prefix where the relevant guard does not
fit.  Once a realization exists the paper census forces the canonical branch,
so this fixed family agrees with the global rough guard on the bridge
universe.  The concrete elimination interfaces below give equality after
deleting guards from a raw cell, equality after restricting deletion to
structured active values, and pointwise avoidance of the full guard.
-/

open Filter Topology

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.PaperBridgeFit
open Erdos390.Full.PaperGuardCensus
open Erdos390.Full.Scale
open Erdos390.Full.StructuredCells

noncomputable section

/-! ## Enumerating an arbitrary finite guard together with a zero sentinel -/







/-! ## The literal bridge-relevant subfamily -/











namespace BankPaperRealization



/-! ## The canonical two-promoted-slot ledger -/



















/-! ## Equality on raw cells and structured active values -/









/-- Any locally agreeing ledger turns the structured sample's built-in guard
avoidance into avoidance of the full global rough guard.  This is the generic
`hnotGuard` migration interface; it does not require a global equality of
finite guard sets. -/
theorem structuredSample_value_not_fullGuard_of_agreement
    {Head : Type*} [Fintype Head]
    (D : StructuredSampleData Head)
    {c : Real} {depth h Cprom Cbank : Nat}
    {left right : Nat -> Nat} {changed : Finset Nat}
    (G : Ledger D.n Cprom Cbank)
    (R : BankPaperRealization D.n (upperEndpoint D.n h))
    (certificate : GuardedCentralAnchorCertificate c depth D.n
      left right changed)
    (deltaStar : Real)
    (hagreement : BankPaperCanonicalBridgeGuardAgreement
      G R certificate deltaStar)
    (hupper : forall m : D.Sample, D.value m <= 2 * D.n)
    (hguards : D.guards = G.guards)
    (m : D.Sample) :
    D.value m ∉ R.roughCanonicalGuardSet certificate deltaStar := by
  intro haFull
  apply D.value_not_guard m
  rw [hguards]
  exact
    (hagreement (D.value m) (D.value_pos m) (hupper m)
      (D.value_mem_smoothNumbers m)).mpr haFull



end BankPaperRealization

end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankPaperCanonicalSectionNinePostHeightSourceInputAssemblyConnector -/
section


/-!
# Mechanical source-input assembly for the fresh post-height bridge

This file is downstream from the honest reduction boundary in
`BankPaperCanonicalSectionNinePostHeightEventualSupplierConnector`.  It does
not alter that boundary and does not assert a final supplier.

There are two results.

* A finite constructor takes one already-chosen fresh bridge `J`, its
  genuinely target-dependent synchronization facts, and one already-produced
  rounded source state.  Canonical sample geometry and the two literal
  capacity divisibilities then construct
  `BankPaperCanonicalSectionNinePostHeightSourceInputsAt` and the existing
  `BankPaperCanonicalSectionNinePostHeightPrimitiveGapsAt`.
* A mesh-uniform eventual wrapper supplies all of the mechanical hypotheses
  of that finite constructor from the existing Section 8 ledger, canonical
  guarded-cell estimates, bridge-guard agreement, and the rounded-source
  theorem.  The realization and certificate are the literal fiber of the
  same `BankPaperCanonicalGuardedTailFamily`.

The wrapper still quantifies over `J` and assumes the four target-margin
bounds, the exact frozen/final-mass synchronization, and
`BankPaperCanonicalTopFrozenRoundedSourceResidualInputsAt`.  Thus it is an
assembly theorem, not a renamed solution of the target/source producer gap.
-/

open Filter Topology Set Asymptotics
open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.ArithmeticBandGeometry
open Erdos390.Full.FiniteProbability
open Erdos390.Full.GuardSquarefreeErrorRate
open Erdos390.Full.HeadPattern
open Erdos390.Full.PaperBridgeFit
open Erdos390.Full.PaperGuardCensus
open Erdos390.Full.PaperHeadSimplex
open Erdos390.Full.PaperScaleMarkedCell
open Erdos390.Full.RegularMeshPrimeCutoffs
open Erdos390.Full.RegularRelativeMesh
open Erdos390.Full.Scale

noncomputable section

namespace BankPaperRealization

set_option maxHeartbeats 2400000

/-! ## Finite assembly -/

/-- Construct the literal post-height source package and the existing
primitive-gap record from one coherent finite bridge.

The hypotheses named `hsourceState`, `hmFrozen`, `hfinalActiveMass`, and
`hsourceResidual` are exact outputs or inputs of existing narrow
connectors.  Everything else stored in the resulting source package is
derived here from canonical sample geometry or from the two displayed
capacity divisibilities. -/
theorem
    exists_bankPaperCanonicalSectionNinePostHeight_sourceInputsAndPrimitiveGapsAt_of_canonical
    {delta eta : Real} (M : RegularRelativeMesh.Mesh delta eta)
    {P : Finset Nat}
    (hprime : ∀ p ∈ P, p.Prime) (E : Nat) (hE : 0 < E)
    (Bsource : BridgeData (PaperHeadSimplex.Tag P)
      (BankPaperCanonicalExponentBand M))
    {c : Real} {depth K0 : Nat}
    (R : BankPaperRealization Bsource.sampleData.n
      (upperEndpoint Bsource.sampleData.n
        (upperTailLength c Bsource.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth
      Bsource.sampleData.n R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (I : PhysicalIntervals)
    (hlowerOne : ∀ sign, 1 ≤ I.lower sign)
    (hupperTwo : ∀ sign, I.upper sign ≤ 2)
    (Cprom Cbank : Nat) (G : ∀ n, Ledger n Cprom Cbank)
    (deltaStar mu sourceMarginFloor headMarginFloor
      physicalEtaFloor postMarginFloor : Real)
    (logY Lambda0 mFrozen qTilde : Nat → Real)
    (hsourceMarginFloor : 0 < sourceMarginFloor)
    (hheadMarginFloor : 0 < headMarginFloor)
    (hphysicalEtaFloor : 0 < physicalEtaFloor)
    (hpostMarginFloor : 0 < postMarginFloor)
    (hdelta : 0 < delta)
    (J : BankPaperCanonicalSectionNinePostHeightBridgeInputsAt
      (K0 := K0) M Bsource R certificate I deltaStar hdelta)
    (hexponentSync : J.exponent = E)
    (hhead : primesUpTo J.postHeightBridge.sampleData.W ⊆ P)
    (hsep :
      physicalBound (I.upper .minus) J.postHeightBridge.sampleData.n <
        physicalBound (I.lower .plus) J.postHeightBridge.sampleData.n)
    (hremaining : ∀ cell : Cell (PaperHeadSimplex.Tag P),
      (rawCell (PaperHeadSimplex.pattern P hprime E) I
          J.postHeightBridge.sampleData.n cell \
        (G J.postHeightBridge.sampleData.n).guards).Nonempty)
    (hcanonical :
      J.postHeightBridge.sampleData =
        canonicalSampleData
          (W := J.postHeightBridge.sampleData.W)
          (PaperHeadSimplex.pattern P hprime E) I
          (G J.postHeightBridge.sampleData.n) hsep hremaining)
    (hguardAgreement :
      BankPaperCanonicalBridgeGuardAgreement
        (G J.postHeightBridge.sampleData.n) R certificate deltaStar)
    (hupperBroad : ∀ sign,
      physicalBound (I.upper sign) J.postHeightBridge.sampleData.n ≤
        2 * J.postHeightBridge.sampleData.n -
          (K0 + 1) *
            upperTailLength c J.postHeightBridge.sampleData.n)
    (hroughDepth :
      (K0 + 1) * upperTailLength c J.postHeightBridge.sampleData.n ≤
        J.postHeightBridge.sampleData.n)
    (hqnOne : 1 ≤ J.qn)
    (hbetaProt : 0 ≤ J.betaProt)
    (hsourceState :
      BankPaperCanonicalSelectorSourceState
        (W := J.postHeightBridge.sampleData.W) R certificate
        (R.paperFixedExceptionalFactors deltaStar)
        (R.roughCanonicalGuardedCandidateSet certificate
          deltaStar (K0 + 1))
        J.roundedSourceSelector)
    (Cmass density : Real)
    (hCmass : 0 ≤ Cmass) (hdensity : 0 < density)
    (hmassUpper :
      J.qn ≤
        Cmass * (J.postHeightBridge.sampleData.n : Real) /
          J.postHeightBridge.L)
    (hcellDensity : ∀ cell : Cell (PaperHeadSimplex.Tag P),
      density * (J.postHeightBridge.sampleData.n : Real) ≤
        (Fintype.card
          (J.postHeightBridge.sampleData.SampleAt cell) : Real))
    (hcombined :
      centralAnchorDivisor J.postHeightBridge.sampleData.n
            (centralAnchorCutoff depth J.postHeightBridge.sampleData.n)
            certificate.q * R.prechargeBaseStateProduct ∣
        centralTailProduct J.postHeightBridge.sampleData.n
          (upperTailLength c J.postHeightBridge.sampleData.n))
    (hcharge :
      R.selectorTailCharge (R.paperFixedExceptionalFactors deltaStar) ∣
        certificate.prechargedTailTarget)
    (hsourceMargin :
      sourceMarginFloor ≤ J.Tsource.cellMassMargin)
    (hheadMargin :
      headMarginFloor ≤ J.targetInputs.headMargin)
    (hphysicalEta :
      physicalEtaFloor ≤ J.targetInputs.physicalEta)
    (hpostMargin :
      postMarginFloor ≤ J.postHeightTarget.cellMassMargin)
    (hqTildeFamily :
      J.qTilde = qTilde Bsource.sampleData.n)
    (hmFrozen :
      mFrozen Bsource.sampleData.n =
        bankPaperCanonicalTopFrozenSmoothFrozenMass (K := K0 + 1)
          J.postHeightBridge R certificate deltaStar J.betaProt J.alpha)
    (hfinalActiveMass :
      J.qn =
        bankPaperCanonicalSmoothFinalActiveMassFamily
          mu logY Lambda0 mFrozen qTilde Bsource.sampleData.n)
    (hsourceResidual :
      BankPaperCanonicalTopFrozenRoundedSourceResidualInputsAt
        (K := K0 + 1) J.postHeightBridge R certificate
          (R.paperFixedExceptionalFactors deltaStar)
          J.Tsource deltaStar J.betaProt J.alpha J.beta J.qTilde) :
    ∃ S : BankPaperCanonicalSectionNinePostHeightSourceInputsAt
        M Bsource R certificate I deltaStar hdelta J,
      ∃ _Hgap :
          BankPaperCanonicalSectionNinePostHeightPrimitiveGapsAt
            M Bsource R certificate I E deltaStar mu
              sourceMarginFloor headMarginFloor physicalEtaFloor
              postMarginFloor logY Lambda0 mFrozen qTilde hdelta J S,
        S.Cmass = Cmass ∧ S.density = density := by
  have hpatternE :
      J.postHeightBridge.sampleData.pattern =
        PaperHeadSimplex.pattern P hprime E := by
    calc
      J.postHeightBridge.sampleData.pattern =
          (canonicalSampleData
            (W := J.postHeightBridge.sampleData.W)
            (PaperHeadSimplex.pattern P hprime E) I
            (G J.postHeightBridge.sampleData.n)
            hsep hremaining).pattern :=
        congrArg
          (fun D : StructuredSampleData (PaperHeadSimplex.Tag P) =>
            D.pattern)
          hcanonical
      _ = PaperHeadSimplex.pattern P hprime E :=
        canonicalSampleData_pattern
          (PaperHeadSimplex.pattern P hprime E) I
          (G J.postHeightBridge.sampleData.n) hsep hremaining
  have hpattern :
      J.postHeightBridge.sampleData.pattern =
        PaperHeadSimplex.pattern P hprime J.exponent := by
    simpa only [hexponentSync] using hpatternE
  have hsampleGuards :
      J.postHeightBridge.sampleData.guards =
        (G J.postHeightBridge.sampleData.n).guards := by
    calc
      J.postHeightBridge.sampleData.guards =
          (canonicalSampleData
            (W := J.postHeightBridge.sampleData.W)
            (PaperHeadSimplex.pattern P hprime E) I
            (G J.postHeightBridge.sampleData.n)
            hsep hremaining).guards :=
        congrArg
          (fun D : StructuredSampleData (PaperHeadSimplex.Tag P) =>
            D.guards)
          hcanonical
      _ = (G J.postHeightBridge.sampleData.n).guards :=
        canonicalSampleData_guards
          (PaperHeadSimplex.pattern P hprime E) I
          (G J.postHeightBridge.sampleData.n) hsep hremaining
  have hbounds :=
    bankPaperCanonicalStructuredValue_bounds_of_physicalIntervals
      J.postHeightBridge I hlowerOne hupperTwo
        J.postHeightHlo J.postHeightHhi
  have houtsideGuard :
      ∀ m : J.postHeightBridge.sampleData.Sample,
        J.postHeightBridge.sampleData.value m ∉
          R.roughCanonicalGuardSet certificate deltaStar := by
    intro m
    exact
      structuredSample_value_not_fullGuard_of_agreement
        J.postHeightBridge.sampleData
        (G J.postHeightBridge.sampleData.n)
        R certificate deltaStar hguardAgreement
        hbounds.2 hsampleGuards m
  have hheadSeparated :
      J.postHeightBridge.sampleData.HeadPatternsSeparated :=
    Erdos390.Full.PaperBridgeFit.StructuredSampleData.headPatternsSeparated_of_paperHeadSimplex
      P hprime E hE J.postHeightBridge.sampleData hpatternE
  have hbase :
      (baseBankFactors R.exactificationState).prod id ∣
        certificate.prechargedTailTarget :=
    certificate.baseExactificationBank_prod_dvd_prechargedTailTarget
      R hcombined
  have htarget :
      certificate.prechargedTailTarget *
            centralAnchorDivisor J.postHeightBridge.sampleData.n
              (centralAnchorCutoff depth J.postHeightBridge.sampleData.n)
              certificate.q =
        centralTailProduct J.postHeightBridge.sampleData.n
          (upperTailLength c J.postHeightBridge.sampleData.n) :=
    certificate.prechargedTailTarget_mul_centralAnchorDivisor
  let S :
      BankPaperCanonicalSectionNinePostHeightSourceInputsAt
        M Bsource R certificate I deltaStar hdelta J := {
    lowerOne := hlowerOne
    upperTwo := hupperTwo
    upperBroad := hupperBroad
    qn_one_le := hqnOne
    hprime := hprime
    hpattern := hpattern
    headPrimes := hhead
    headSeparated := hheadSeparated
    roughDepth := hroughDepth
    outsideGuard := houtsideGuard
    betaProt_nonneg := hbetaProt
    sourceState := hsourceState
    Cmass := Cmass
    density := density
    Cmass_nonneg := hCmass
    density_pos := hdensity
    massUpper := hmassUpper
    cellDensity := hcellDensity
    combined_dvd := hcombined
    base_dvd := hbase
    charge_dvd := hcharge
    target_tail := htarget
  }
  let Hgap :
      BankPaperCanonicalSectionNinePostHeightPrimitiveGapsAt
        M Bsource R certificate I E deltaStar mu
          sourceMarginFloor headMarginFloor physicalEtaFloor postMarginFloor
          logY Lambda0 mFrozen qTilde hdelta J S := {
    exponent_pos := hE
    exponent_sync := hexponentSync
    sourceMarginFloor_pos := hsourceMarginFloor
    headMarginFloor_pos := hheadMarginFloor
    physicalEtaFloor_pos := hphysicalEtaFloor
    postMarginFloor_pos := hpostMarginFloor
    sourceTarget_margin := hsourceMargin
    headMargin_uniform := hheadMargin
    physicalEta_uniform := hphysicalEta
    postHeightTarget_margin := hpostMargin
    qTilde_family := hqTildeFamily
    mFrozen_family := hmFrozen
    finalActiveMass_family := hfinalActiveMass
    sourceResidual := hsourceResidual
  }
  exact ⟨S, Hgap, rfl, rfl⟩

/-! ## Eventual mechanical wrapper -/



end BankPaperRealization

end

end Erdos390.WholePaper

end

theorem solution :
∀ {delta eta : Real} (M : Erdos390.Full.RegularRelativeMesh.Mesh delta eta) {P : Finset.{0} Nat}
  (hprime :
    ∀ (p : Nat),
      @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
          (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p →
        Nat.Prime p)
  (E : Nat) (hE : @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) E)
  (Bsource :
    @Erdos390.Full.PaperBridgeFit.BridgeData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P)
      (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M)
      (@instFintypeOption.{0}
        (@Subtype.{1} Nat fun (p : Nat) =>
          @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
            (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
        (@Finset.Subtype.fintype.{0} Nat P))
      (fun (a b : Erdos390.Full.PaperHeadSimplex.Tag P) =>
        @Option.instDecidableEq.{0}
          (@Subtype.{1} Nat fun (p : Nat) =>
            @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
              (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
          (fun
              (a b :
                @Subtype.{1} Nat fun (p : Nat) =>
                  @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                    (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p) =>
            @Subtype.instDecidableEq.{1} Nat
              (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P)
              instDecidableEqNat a b)
          a b)
      (Fin.fintype
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (instDecidableEqFin
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
  {c : Real} {depth K0 : Nat}
  (R :
    Erdos390.WholePaper.BankPaperRealization
      (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P)
        (@instFintypeOption.{0}
          (@Subtype.{1} Nat fun (p : Nat) =>
            @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
              (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
          (@Finset.Subtype.fintype.{0} Nat P))
        (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P)
          (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M)
          (@instFintypeOption.{0}
            (@Subtype.{1} Nat fun (p : Nat) =>
              @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
            (@Finset.Subtype.fintype.{0} Nat P))
          (fun (a b : Erdos390.Full.PaperHeadSimplex.Tag P) =>
            @Option.instDecidableEq.{0}
              (@Subtype.{1} Nat fun (p : Nat) =>
                @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                  (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
              (fun
                  (a b :
                    @Subtype.{1} Nat fun (p : Nat) =>
                      @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                        (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p) =>
                @Subtype.instDecidableEq.{1} Nat
                  (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                    (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P)
                  instDecidableEqNat a b)
              a b)
          (Fin.fintype
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
          (instDecidableEqFin
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
          Bsource))
      (Erdos390.WholePaper.upperEndpoint
        (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P)
          (@instFintypeOption.{0}
            (@Subtype.{1} Nat fun (p : Nat) =>
              @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
            (@Finset.Subtype.fintype.{0} Nat P))
          (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P)
            (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M)
            (@instFintypeOption.{0}
              (@Subtype.{1} Nat fun (p : Nat) =>
                @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                  (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
              (@Finset.Subtype.fintype.{0} Nat P))
            (fun (a b : Erdos390.Full.PaperHeadSimplex.Tag P) =>
              @Option.instDecidableEq.{0}
                (@Subtype.{1} Nat fun (p : Nat) =>
                  @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                    (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                (fun
                    (a b :
                      @Subtype.{1} Nat fun (p : Nat) =>
                        @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                          (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p) =>
                  @Subtype.instDecidableEq.{1} Nat
                    (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P)
                    instDecidableEqNat a b)
                a b)
            (Fin.fintype
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
            (instDecidableEqFin
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
            Bsource))
        (Erdos390.WholePaper.upperTailLength c
          (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P)
            (@instFintypeOption.{0}
              (@Subtype.{1} Nat fun (p : Nat) =>
                @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                  (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
              (@Finset.Subtype.fintype.{0} Nat P))
            (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P)
              (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M)
              (@instFintypeOption.{0}
                (@Subtype.{1} Nat fun (p : Nat) =>
                  @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                    (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                (@Finset.Subtype.fintype.{0} Nat P))
              (fun (a b : Erdos390.Full.PaperHeadSimplex.Tag P) =>
                @Option.instDecidableEq.{0}
                  (@Subtype.{1} Nat fun (p : Nat) =>
                    @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                  (fun
                      (a b :
                        @Subtype.{1} Nat fun (p : Nat) =>
                          @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                            (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p) =>
                    @Subtype.instDecidableEq.{1} Nat
                      (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                        (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P)
                      instDecidableEqNat a b)
                  a b)
              (Fin.fintype
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                  (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
              (instDecidableEqFin
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                  (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
              Bsource)))))
  (certificate :
    Erdos390.WholePaper.GuardedCentralAnchorCertificate c depth
      (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P)
        (@instFintypeOption.{0}
          (@Subtype.{1} Nat fun (p : Nat) =>
            @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
              (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
          (@Finset.Subtype.fintype.{0} Nat P))
        (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P)
          (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M)
          (@instFintypeOption.{0}
            (@Subtype.{1} Nat fun (p : Nat) =>
              @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
            (@Finset.Subtype.fintype.{0} Nat P))
          (fun (a b : Erdos390.Full.PaperHeadSimplex.Tag P) =>
            @Option.instDecidableEq.{0}
              (@Subtype.{1} Nat fun (p : Nat) =>
                @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                  (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
              (fun
                  (a b :
                    @Subtype.{1} Nat fun (p : Nat) =>
                      @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                        (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p) =>
                @Subtype.instDecidableEq.{1} Nat
                  (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                    (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P)
                  instDecidableEqNat a b)
              a b)
          (Fin.fintype
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
          (instDecidableEqFin
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
          Bsource))
      (@Erdos390.WholePaper.BankPaperRealization.anchorGuardLeftCore
        (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P)
          (@instFintypeOption.{0}
            (@Subtype.{1} Nat fun (p : Nat) =>
              @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
            (@Finset.Subtype.fintype.{0} Nat P))
          (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P)
            (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M)
            (@instFintypeOption.{0}
              (@Subtype.{1} Nat fun (p : Nat) =>
                @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                  (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
              (@Finset.Subtype.fintype.{0} Nat P))
            (fun (a b : Erdos390.Full.PaperHeadSimplex.Tag P) =>
              @Option.instDecidableEq.{0}
                (@Subtype.{1} Nat fun (p : Nat) =>
                  @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                    (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                (fun
                    (a b :
                      @Subtype.{1} Nat fun (p : Nat) =>
                        @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                          (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p) =>
                  @Subtype.instDecidableEq.{1} Nat
                    (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P)
                    instDecidableEqNat a b)
                a b)
            (Fin.fintype
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
            (instDecidableEqFin
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
            Bsource))
        (Erdos390.WholePaper.upperEndpoint
          (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P)
            (@instFintypeOption.{0}
              (@Subtype.{1} Nat fun (p : Nat) =>
                @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                  (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
              (@Finset.Subtype.fintype.{0} Nat P))
            (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P)
              (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M)
              (@instFintypeOption.{0}
                (@Subtype.{1} Nat fun (p : Nat) =>
                  @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                    (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                (@Finset.Subtype.fintype.{0} Nat P))
              (fun (a b : Erdos390.Full.PaperHeadSimplex.Tag P) =>
                @Option.instDecidableEq.{0}
                  (@Subtype.{1} Nat fun (p : Nat) =>
                    @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                  (fun
                      (a b :
                        @Subtype.{1} Nat fun (p : Nat) =>
                          @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                            (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p) =>
                    @Subtype.instDecidableEq.{1} Nat
                      (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                        (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P)
                      instDecidableEqNat a b)
                  a b)
              (Fin.fintype
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                  (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
              (instDecidableEqFin
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                  (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
              Bsource))
          (Erdos390.WholePaper.upperTailLength c
            (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P)
              (@instFintypeOption.{0}
                (@Subtype.{1} Nat fun (p : Nat) =>
                  @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                    (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                (@Finset.Subtype.fintype.{0} Nat P))
              (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P)
                (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M)
                (@instFintypeOption.{0}
                  (@Subtype.{1} Nat fun (p : Nat) =>
                    @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                  (@Finset.Subtype.fintype.{0} Nat P))
                (fun (a b : Erdos390.Full.PaperHeadSimplex.Tag P) =>
                  @Option.instDecidableEq.{0}
                    (@Subtype.{1} Nat fun (p : Nat) =>
                      @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                        (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                    (fun
                        (a b :
                          @Subtype.{1} Nat fun (p : Nat) =>
                            @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                              (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P
                              p) =>
                      @Subtype.instDecidableEq.{1} Nat
                        (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                          (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P)
                        instDecidableEqNat a b)
                    a b)
                (Fin.fintype
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                    (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                (instDecidableEqFin
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                    (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                Bsource))))
        R)
      (@Erdos390.WholePaper.BankPaperRealization.anchorGuardRightCore
        (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P)
          (@instFintypeOption.{0}
            (@Subtype.{1} Nat fun (p : Nat) =>
              @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
            (@Finset.Subtype.fintype.{0} Nat P))
          (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P)
            (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M)
            (@instFintypeOption.{0}
              (@Subtype.{1} Nat fun (p : Nat) =>
                @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                  (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
              (@Finset.Subtype.fintype.{0} Nat P))
            (fun (a b : Erdos390.Full.PaperHeadSimplex.Tag P) =>
              @Option.instDecidableEq.{0}
                (@Subtype.{1} Nat fun (p : Nat) =>
                  @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                    (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                (fun
                    (a b :
                      @Subtype.{1} Nat fun (p : Nat) =>
                        @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                          (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p) =>
                  @Subtype.instDecidableEq.{1} Nat
                    (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P)
                    instDecidableEqNat a b)
                a b)
            (Fin.fintype
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
            (instDecidableEqFin
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
            Bsource))
        (Erdos390.WholePaper.upperEndpoint
          (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P)
            (@instFintypeOption.{0}
              (@Subtype.{1} Nat fun (p : Nat) =>
                @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                  (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
              (@Finset.Subtype.fintype.{0} Nat P))
            (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P)
              (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M)
              (@instFintypeOption.{0}
                (@Subtype.{1} Nat fun (p : Nat) =>
                  @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                    (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                (@Finset.Subtype.fintype.{0} Nat P))
              (fun (a b : Erdos390.Full.PaperHeadSimplex.Tag P) =>
                @Option.instDecidableEq.{0}
                  (@Subtype.{1} Nat fun (p : Nat) =>
                    @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                  (fun
                      (a b :
                        @Subtype.{1} Nat fun (p : Nat) =>
                          @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                            (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p) =>
                    @Subtype.instDecidableEq.{1} Nat
                      (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                        (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P)
                      instDecidableEqNat a b)
                  a b)
              (Fin.fintype
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                  (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
              (instDecidableEqFin
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                  (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
              Bsource))
          (Erdos390.WholePaper.upperTailLength c
            (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P)
              (@instFintypeOption.{0}
                (@Subtype.{1} Nat fun (p : Nat) =>
                  @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                    (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                (@Finset.Subtype.fintype.{0} Nat P))
              (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P)
                (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M)
                (@instFintypeOption.{0}
                  (@Subtype.{1} Nat fun (p : Nat) =>
                    @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                  (@Finset.Subtype.fintype.{0} Nat P))
                (fun (a b : Erdos390.Full.PaperHeadSimplex.Tag P) =>
                  @Option.instDecidableEq.{0}
                    (@Subtype.{1} Nat fun (p : Nat) =>
                      @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                        (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                    (fun
                        (a b :
                          @Subtype.{1} Nat fun (p : Nat) =>
                            @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                              (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P
                              p) =>
                      @Subtype.instDecidableEq.{1} Nat
                        (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                          (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P)
                        instDecidableEqNat a b)
                    a b)
                (Fin.fintype
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                    (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                (instDecidableEqFin
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                    (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                Bsource))))
        R)
      (@Erdos390.WholePaper.BankPaperRealization.centralChangedMarkers
        (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P)
          (@instFintypeOption.{0}
            (@Subtype.{1} Nat fun (p : Nat) =>
              @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
            (@Finset.Subtype.fintype.{0} Nat P))
          (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P)
            (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M)
            (@instFintypeOption.{0}
              (@Subtype.{1} Nat fun (p : Nat) =>
                @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                  (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
              (@Finset.Subtype.fintype.{0} Nat P))
            (fun (a b : Erdos390.Full.PaperHeadSimplex.Tag P) =>
              @Option.instDecidableEq.{0}
                (@Subtype.{1} Nat fun (p : Nat) =>
                  @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                    (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                (fun
                    (a b :
                      @Subtype.{1} Nat fun (p : Nat) =>
                        @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                          (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p) =>
                  @Subtype.instDecidableEq.{1} Nat
                    (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P)
                    instDecidableEqNat a b)
                a b)
            (Fin.fintype
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
            (instDecidableEqFin
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
            Bsource))
        (Erdos390.WholePaper.upperEndpoint
          (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P)
            (@instFintypeOption.{0}
              (@Subtype.{1} Nat fun (p : Nat) =>
                @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                  (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
              (@Finset.Subtype.fintype.{0} Nat P))
            (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P)
              (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M)
              (@instFintypeOption.{0}
                (@Subtype.{1} Nat fun (p : Nat) =>
                  @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                    (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                (@Finset.Subtype.fintype.{0} Nat P))
              (fun (a b : Erdos390.Full.PaperHeadSimplex.Tag P) =>
                @Option.instDecidableEq.{0}
                  (@Subtype.{1} Nat fun (p : Nat) =>
                    @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                  (fun
                      (a b :
                        @Subtype.{1} Nat fun (p : Nat) =>
                          @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                            (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p) =>
                    @Subtype.instDecidableEq.{1} Nat
                      (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                        (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P)
                      instDecidableEqNat a b)
                  a b)
              (Fin.fintype
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                  (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
              (instDecidableEqFin
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                  (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
              Bsource))
          (Erdos390.WholePaper.upperTailLength c
            (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P)
              (@instFintypeOption.{0}
                (@Subtype.{1} Nat fun (p : Nat) =>
                  @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                    (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                (@Finset.Subtype.fintype.{0} Nat P))
              (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P)
                (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M)
                (@instFintypeOption.{0}
                  (@Subtype.{1} Nat fun (p : Nat) =>
                    @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                  (@Finset.Subtype.fintype.{0} Nat P))
                (fun (a b : Erdos390.Full.PaperHeadSimplex.Tag P) =>
                  @Option.instDecidableEq.{0}
                    (@Subtype.{1} Nat fun (p : Nat) =>
                      @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                        (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                    (fun
                        (a b :
                          @Subtype.{1} Nat fun (p : Nat) =>
                            @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                              (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P
                              p) =>
                      @Subtype.instDecidableEq.{1} Nat
                        (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                          (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P)
                        instDecidableEqNat a b)
                    a b)
                (Fin.fintype
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                    (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                (instDecidableEqFin
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                    (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                Bsource))))
        R depth))
  (I : Erdos390.Full.PaperGuardCensus.PhysicalIntervals)
  (hlowerOne :
    ∀ (sign : Erdos390.Full.PaperBridgeFit.PhysicalSign),
      @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
        (I.lower sign))
  (hupperTwo :
    ∀ (sign : Erdos390.Full.PaperBridgeFit.PhysicalSign),
      @LE.le.{0} Real Real.instLE (I.upper sign)
        (@OfNat.ofNat.{0} Real (nat_lit 2)
          (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
            (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
              (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))))
  (Cprom Cbank : Nat) (G : (n : Nat) → Erdos390.Full.PaperGuardCensus.Ledger n Cprom Cbank)
  (deltaStar mu sourceMarginFloor headMarginFloor physicalEtaFloor postMarginFloor : Real)
  (logY Lambda0 mFrozen qTilde : Nat → Real)
  (hsourceMarginFloor :
    @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
      sourceMarginFloor)
  (hheadMarginFloor :
    @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
      headMarginFloor)
  (hphysicalEtaFloor :
    @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
      physicalEtaFloor)
  (hpostMarginFloor :
    @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
      postMarginFloor)
  (hdelta :
    @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) delta)
  (J :
    @Erdos390.WholePaper.BankPaperRealization.BankPaperCanonicalSectionNinePostHeightBridgeInputsAt delta eta M P
      Bsource c depth K0 R certificate I deltaStar hdelta)
  (hexponentSync :
    @Eq.{1} Nat
      (@Erdos390.WholePaper.BankPaperRealization.BankPaperCanonicalSectionNinePostHeightBridgeInputsAt.exponent delta
        eta M P Bsource c depth K0 R certificate I deltaStar hdelta J)
      E)
  (hhead :
    @HasSubset.Subset.{0} (Finset.{0} Nat) (@Finset.instHasSubset.{0} Nat)
      (Erdos390.WholePaper.primesUpTo
        (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{0} (Erdos390.Full.PaperHeadSimplex.Tag P)
          (@instFintypeOption.{0}
            (@Subtype.{1} Nat fun (p : Nat) =>
              @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
            (@Finset.Subtype.fintype.{0} Nat P))
          (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P)
            (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M)
            (@instFintypeOption.{0}
              (@Subtype.{1} Nat fun (p : Nat) =>
                @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                  (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
              (@Finset.Subtype.fintype.{0} Nat P))
            (fun (a b : Erdos390.Full.PaperHeadSimplex.Tag P) =>
              @Option.instDecidableEq.{0}
                (@Subtype.{1} Nat fun (p : Nat) =>
                  @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                    (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                (fun
                    (a b :
                      @Subtype.{1} Nat fun (p : Nat) =>
                        @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                          (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p) =>
                  @Subtype.instDecidableEq.{1} Nat
                    (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P)
                    instDecidableEqNat a b)
                a b)
            (Fin.fintype
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
            (instDecidableEqFin
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
            (@Erdos390.WholePaper.BankPaperRealization.BankPaperCanonicalSectionNinePostHeightBridgeInputsAt.postHeightBridge
              delta eta M P Bsource c depth K0 R certificate I deltaStar hdelta J))))
      P)
  (hsep :
    @LT.lt.{0} Nat instLTNat
      (Erdos390.Full.ArithmeticModel.physicalBound (I.upper Erdos390.Full.PaperBridgeFit.PhysicalSign.minus)
        (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P)
          (@instFintypeOption.{0}
            (@Subtype.{1} Nat fun (p : Nat) =>
              @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
            (@Finset.Subtype.fintype.{0} Nat P))
          (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P)
            (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M)
            (@instFintypeOption.{0}
              (@Subtype.{1} Nat fun (p : Nat) =>
                @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                  (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
              (@Finset.Subtype.fintype.{0} Nat P))
            (fun (a b : Erdos390.Full.PaperHeadSimplex.Tag P) =>
              @Option.instDecidableEq.{0}
                (@Subtype.{1} Nat fun (p : Nat) =>
                  @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                    (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                (fun
                    (a b :
                      @Subtype.{1} Nat fun (p : Nat) =>
                        @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                          (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p) =>
                  @Subtype.instDecidableEq.{1} Nat
                    (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P)
                    instDecidableEqNat a b)
                a b)
            (Fin.fintype
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
            (instDecidableEqFin
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
            (@Erdos390.WholePaper.BankPaperRealization.BankPaperCanonicalSectionNinePostHeightBridgeInputsAt.postHeightBridge
              delta eta M P Bsource c depth K0 R certificate I deltaStar hdelta J))))
      (Erdos390.Full.ArithmeticModel.physicalBound (I.lower Erdos390.Full.PaperBridgeFit.PhysicalSign.plus)
        (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P)
          (@instFintypeOption.{0}
            (@Subtype.{1} Nat fun (p : Nat) =>
              @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
            (@Finset.Subtype.fintype.{0} Nat P))
          (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P)
            (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M)
            (@instFintypeOption.{0}
              (@Subtype.{1} Nat fun (p : Nat) =>
                @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                  (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
              (@Finset.Subtype.fintype.{0} Nat P))
            (fun (a b : Erdos390.Full.PaperHeadSimplex.Tag P) =>
              @Option.instDecidableEq.{0}
                (@Subtype.{1} Nat fun (p : Nat) =>
                  @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                    (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                (fun
                    (a b :
                      @Subtype.{1} Nat fun (p : Nat) =>
                        @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                          (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p) =>
                  @Subtype.instDecidableEq.{1} Nat
                    (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P)
                    instDecidableEqNat a b)
                a b)
            (Fin.fintype
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
            (instDecidableEqFin
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
            (@Erdos390.WholePaper.BankPaperRealization.BankPaperCanonicalSectionNinePostHeightBridgeInputsAt.postHeightBridge
              delta eta M P Bsource c depth K0 R certificate I deltaStar hdelta J)))))
  (hremaining :
    ∀ (cell : Erdos390.Full.PaperBridgeFit.Cell.{0} (Erdos390.Full.PaperHeadSimplex.Tag P)),
      @Finset.Nonempty.{0} Nat
        (@SDiff.sdiff.{0} (Finset.{0} Nat) (@Finset.instSDiff.{0} Nat instDecidableEqNat)
          (@Erdos390.Full.PaperGuardCensus.rawCell.{0} (Erdos390.Full.PaperHeadSimplex.Tag P)
            (Erdos390.Full.PaperHeadSimplex.pattern P hprime E) I
            (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P)
              (@instFintypeOption.{0}
                (@Subtype.{1} Nat fun (p : Nat) =>
                  @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                    (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                (@Finset.Subtype.fintype.{0} Nat P))
              (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P)
                (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M)
                (@instFintypeOption.{0}
                  (@Subtype.{1} Nat fun (p : Nat) =>
                    @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                  (@Finset.Subtype.fintype.{0} Nat P))
                (fun (a b : Erdos390.Full.PaperHeadSimplex.Tag P) =>
                  @Option.instDecidableEq.{0}
                    (@Subtype.{1} Nat fun (p : Nat) =>
                      @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                        (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                    (fun
                        (a b :
                          @Subtype.{1} Nat fun (p : Nat) =>
                            @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                              (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P
                              p) =>
                      @Subtype.instDecidableEq.{1} Nat
                        (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                          (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P)
                        instDecidableEqNat a b)
                    a b)
                (Fin.fintype
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                    (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                (instDecidableEqFin
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                    (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                (@Erdos390.WholePaper.BankPaperRealization.BankPaperCanonicalSectionNinePostHeightBridgeInputsAt.postHeightBridge
                  delta eta M P Bsource c depth K0 R certificate I deltaStar hdelta J)))
            cell)
          (@Erdos390.Full.PaperGuardCensus.Ledger.guards
            (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P)
              (@instFintypeOption.{0}
                (@Subtype.{1} Nat fun (p : Nat) =>
                  @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                    (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                (@Finset.Subtype.fintype.{0} Nat P))
              (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P)
                (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M)
                (@instFintypeOption.{0}
                  (@Subtype.{1} Nat fun (p : Nat) =>
                    @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                  (@Finset.Subtype.fintype.{0} Nat P))
                (fun (a b : Erdos390.Full.PaperHeadSimplex.Tag P) =>
                  @Option.instDecidableEq.{0}
                    (@Subtype.{1} Nat fun (p : Nat) =>
                      @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                        (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                    (fun
                        (a b :
                          @Subtype.{1} Nat fun (p : Nat) =>
                            @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                              (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P
                              p) =>
                      @Subtype.instDecidableEq.{1} Nat
                        (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                          (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P)
                        instDecidableEqNat a b)
                    a b)
                (Fin.fintype
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                    (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                (instDecidableEqFin
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                    (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                (@Erdos390.WholePaper.BankPaperRealization.BankPaperCanonicalSectionNinePostHeightBridgeInputsAt.postHeightBridge
                  delta eta M P Bsource c depth K0 R certificate I deltaStar hdelta J)))
            Cprom Cbank
            (G
              (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P)
                (@instFintypeOption.{0}
                  (@Subtype.{1} Nat fun (p : Nat) =>
                    @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                  (@Finset.Subtype.fintype.{0} Nat P))
                (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P)
                  (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M)
                  (@instFintypeOption.{0}
                    (@Subtype.{1} Nat fun (p : Nat) =>
                      @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                        (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                    (@Finset.Subtype.fintype.{0} Nat P))
                  (fun (a b : Erdos390.Full.PaperHeadSimplex.Tag P) =>
                    @Option.instDecidableEq.{0}
                      (@Subtype.{1} Nat fun (p : Nat) =>
                        @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                          (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                      (fun
                          (a b :
                            @Subtype.{1} Nat fun (p : Nat) =>
                              @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P
                                p) =>
                        @Subtype.instDecidableEq.{1} Nat
                          (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                            (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P)
                          instDecidableEqNat a b)
                      a b)
                  (Fin.fintype
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                      (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                  (instDecidableEqFin
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                      (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                  (@Erdos390.WholePaper.BankPaperRealization.BankPaperCanonicalSectionNinePostHeightBridgeInputsAt.postHeightBridge
                    delta eta M P Bsource c depth K0 R certificate I deltaStar hdelta J)))))))
  (hcanonical :
    @Eq.{1}
      (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.{0} (Erdos390.Full.PaperHeadSimplex.Tag P)
        (@instFintypeOption.{0}
          (@Subtype.{1} Nat fun (p : Nat) =>
            @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
              (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
          (@Finset.Subtype.fintype.{0} Nat P)))
      (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P)
        (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M)
        (@instFintypeOption.{0}
          (@Subtype.{1} Nat fun (p : Nat) =>
            @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
              (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
          (@Finset.Subtype.fintype.{0} Nat P))
        (fun (a b : Erdos390.Full.PaperHeadSimplex.Tag P) =>
          @Option.instDecidableEq.{0}
            (@Subtype.{1} Nat fun (p : Nat) =>
              @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
            (fun
                (a b :
                  @Subtype.{1} Nat fun (p : Nat) =>
                    @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p) =>
              @Subtype.instDecidableEq.{1} Nat
                (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                  (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P)
                instDecidableEqNat a b)
            a b)
        (Fin.fintype
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
        (instDecidableEqFin
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
        (@Erdos390.WholePaper.BankPaperRealization.BankPaperCanonicalSectionNinePostHeightBridgeInputsAt.postHeightBridge
          delta eta M P Bsource c depth K0 R certificate I deltaStar hdelta J))
      (@Erdos390.Full.PaperGuardCensus.canonicalSampleData.{0} (Erdos390.Full.PaperHeadSimplex.Tag P)
        (@instFintypeOption.{0}
          (@Subtype.{1} Nat fun (p : Nat) =>
            @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
              (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
          (@Finset.Subtype.fintype.{0} Nat P))
        (Erdos390.Full.PaperHeadSimplex.pattern P hprime E) I
        (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P)
          (@instFintypeOption.{0}
            (@Subtype.{1} Nat fun (p : Nat) =>
              @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
            (@Finset.Subtype.fintype.{0} Nat P))
          (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P)
            (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M)
            (@instFintypeOption.{0}
              (@Subtype.{1} Nat fun (p : Nat) =>
                @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                  (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
              (@Finset.Subtype.fintype.{0} Nat P))
            (fun (a b : Erdos390.Full.PaperHeadSimplex.Tag P) =>
              @Option.instDecidableEq.{0}
                (@Subtype.{1} Nat fun (p : Nat) =>
                  @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                    (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                (fun
                    (a b :
                      @Subtype.{1} Nat fun (p : Nat) =>
                        @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                          (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p) =>
                  @Subtype.instDecidableEq.{1} Nat
                    (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P)
                    instDecidableEqNat a b)
                a b)
            (Fin.fintype
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
            (instDecidableEqFin
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
            (@Erdos390.WholePaper.BankPaperRealization.BankPaperCanonicalSectionNinePostHeightBridgeInputsAt.postHeightBridge
              delta eta M P Bsource c depth K0 R certificate I deltaStar hdelta J)))
        (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{0} (Erdos390.Full.PaperHeadSimplex.Tag P)
          (@instFintypeOption.{0}
            (@Subtype.{1} Nat fun (p : Nat) =>
              @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
            (@Finset.Subtype.fintype.{0} Nat P))
          (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P)
            (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M)
            (@instFintypeOption.{0}
              (@Subtype.{1} Nat fun (p : Nat) =>
                @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                  (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
              (@Finset.Subtype.fintype.{0} Nat P))
            (fun (a b : Erdos390.Full.PaperHeadSimplex.Tag P) =>
              @Option.instDecidableEq.{0}
                (@Subtype.{1} Nat fun (p : Nat) =>
                  @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                    (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                (fun
                    (a b :
                      @Subtype.{1} Nat fun (p : Nat) =>
                        @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                          (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p) =>
                  @Subtype.instDecidableEq.{1} Nat
                    (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P)
                    instDecidableEqNat a b)
                a b)
            (Fin.fintype
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
            (instDecidableEqFin
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
            (@Erdos390.WholePaper.BankPaperRealization.BankPaperCanonicalSectionNinePostHeightBridgeInputsAt.postHeightBridge
              delta eta M P Bsource c depth K0 R certificate I deltaStar hdelta J)))
        Cprom Cbank
        (G
          (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P)
            (@instFintypeOption.{0}
              (@Subtype.{1} Nat fun (p : Nat) =>
                @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                  (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
              (@Finset.Subtype.fintype.{0} Nat P))
            (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P)
              (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M)
              (@instFintypeOption.{0}
                (@Subtype.{1} Nat fun (p : Nat) =>
                  @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                    (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                (@Finset.Subtype.fintype.{0} Nat P))
              (fun (a b : Erdos390.Full.PaperHeadSimplex.Tag P) =>
                @Option.instDecidableEq.{0}
                  (@Subtype.{1} Nat fun (p : Nat) =>
                    @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                  (fun
                      (a b :
                        @Subtype.{1} Nat fun (p : Nat) =>
                          @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                            (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p) =>
                    @Subtype.instDecidableEq.{1} Nat
                      (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                        (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P)
                      instDecidableEqNat a b)
                  a b)
              (Fin.fintype
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                  (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
              (instDecidableEqFin
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                  (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
              (@Erdos390.WholePaper.BankPaperRealization.BankPaperCanonicalSectionNinePostHeightBridgeInputsAt.postHeightBridge
                delta eta M P Bsource c depth K0 R certificate I deltaStar hdelta J))))
        hsep hremaining))
  (hguardAgreement :
    @Erdos390.WholePaper.BankPaperRealization.BankPaperCanonicalBridgeGuardAgreement c depth
      (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P)
        (@instFintypeOption.{0}
          (@Subtype.{1} Nat fun (p : Nat) =>
            @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
              (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
          (@Finset.Subtype.fintype.{0} Nat P))
        (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P)
          (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M)
          (@instFintypeOption.{0}
            (@Subtype.{1} Nat fun (p : Nat) =>
              @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
            (@Finset.Subtype.fintype.{0} Nat P))
          (fun (a b : Erdos390.Full.PaperHeadSimplex.Tag P) =>
            @Option.instDecidableEq.{0}
              (@Subtype.{1} Nat fun (p : Nat) =>
                @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                  (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
              (fun
                  (a b :
                    @Subtype.{1} Nat fun (p : Nat) =>
                      @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                        (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p) =>
                @Subtype.instDecidableEq.{1} Nat
                  (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                    (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P)
                  instDecidableEqNat a b)
              a b)
          (Fin.fintype
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
          (instDecidableEqFin
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
          (@Erdos390.WholePaper.BankPaperRealization.BankPaperCanonicalSectionNinePostHeightBridgeInputsAt.postHeightBridge
            delta eta M P Bsource c depth K0 R certificate I deltaStar hdelta J)))
      (Erdos390.WholePaper.upperTailLength c
        (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P)
          (@instFintypeOption.{0}
            (@Subtype.{1} Nat fun (p : Nat) =>
              @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
            (@Finset.Subtype.fintype.{0} Nat P))
          (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P)
            (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M)
            (@instFintypeOption.{0}
              (@Subtype.{1} Nat fun (p : Nat) =>
                @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                  (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
              (@Finset.Subtype.fintype.{0} Nat P))
            (fun (a b : Erdos390.Full.PaperHeadSimplex.Tag P) =>
              @Option.instDecidableEq.{0}
                (@Subtype.{1} Nat fun (p : Nat) =>
                  @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                    (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                (fun
                    (a b :
                      @Subtype.{1} Nat fun (p : Nat) =>
                        @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                          (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p) =>
                  @Subtype.instDecidableEq.{1} Nat
                    (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P)
                    instDecidableEqNat a b)
                a b)
            (Fin.fintype
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
            (instDecidableEqFin
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
            Bsource)))
      Cprom Cbank
      (@Erdos390.WholePaper.BankPaperRealization.anchorGuardLeftCore
        (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P)
          (@instFintypeOption.{0}
            (@Subtype.{1} Nat fun (p : Nat) =>
              @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
            (@Finset.Subtype.fintype.{0} Nat P))
          (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P)
            (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M)
            (@instFintypeOption.{0}
              (@Subtype.{1} Nat fun (p : Nat) =>
                @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                  (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
              (@Finset.Subtype.fintype.{0} Nat P))
            (fun (a b : Erdos390.Full.PaperHeadSimplex.Tag P) =>
              @Option.instDecidableEq.{0}
                (@Subtype.{1} Nat fun (p : Nat) =>
                  @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                    (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                (fun
                    (a b :
                      @Subtype.{1} Nat fun (p : Nat) =>
                        @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                          (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p) =>
                  @Subtype.instDecidableEq.{1} Nat
                    (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P)
                    instDecidableEqNat a b)
                a b)
            (Fin.fintype
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
            (instDecidableEqFin
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
            Bsource))
        (Erdos390.WholePaper.upperEndpoint
          (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P)
            (@instFintypeOption.{0}
              (@Subtype.{1} Nat fun (p : Nat) =>
                @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                  (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
              (@Finset.Subtype.fintype.{0} Nat P))
            (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P)
              (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M)
              (@instFintypeOption.{0}
                (@Subtype.{1} Nat fun (p : Nat) =>
                  @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                    (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                (@Finset.Subtype.fintype.{0} Nat P))
              (fun (a b : Erdos390.Full.PaperHeadSimplex.Tag P) =>
                @Option.instDecidableEq.{0}
                  (@Subtype.{1} Nat fun (p : Nat) =>
                    @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                  (fun
                      (a b :
                        @Subtype.{1} Nat fun (p : Nat) =>
                          @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                            (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p) =>
                    @Subtype.instDecidableEq.{1} Nat
                      (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                        (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P)
                      instDecidableEqNat a b)
                  a b)
              (Fin.fintype
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                  (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
              (instDecidableEqFin
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                  (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
              Bsource))
          (Erdos390.WholePaper.upperTailLength c
            (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P)
              (@instFintypeOption.{0}
                (@Subtype.{1} Nat fun (p : Nat) =>
                  @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                    (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                (@Finset.Subtype.fintype.{0} Nat P))
              (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P)
                (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M)
                (@instFintypeOption.{0}
                  (@Subtype.{1} Nat fun (p : Nat) =>
                    @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                  (@Finset.Subtype.fintype.{0} Nat P))
                (fun (a b : Erdos390.Full.PaperHeadSimplex.Tag P) =>
                  @Option.instDecidableEq.{0}
                    (@Subtype.{1} Nat fun (p : Nat) =>
                      @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                        (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                    (fun
                        (a b :
                          @Subtype.{1} Nat fun (p : Nat) =>
                            @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                              (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P
                              p) =>
                      @Subtype.instDecidableEq.{1} Nat
                        (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                          (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P)
                        instDecidableEqNat a b)
                    a b)
                (Fin.fintype
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                    (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                (instDecidableEqFin
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                    (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                Bsource))))
        R)
      (@Erdos390.WholePaper.BankPaperRealization.anchorGuardRightCore
        (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P)
          (@instFintypeOption.{0}
            (@Subtype.{1} Nat fun (p : Nat) =>
              @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
            (@Finset.Subtype.fintype.{0} Nat P))
          (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P)
            (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M)
            (@instFintypeOption.{0}
              (@Subtype.{1} Nat fun (p : Nat) =>
                @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                  (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
              (@Finset.Subtype.fintype.{0} Nat P))
            (fun (a b : Erdos390.Full.PaperHeadSimplex.Tag P) =>
              @Option.instDecidableEq.{0}
                (@Subtype.{1} Nat fun (p : Nat) =>
                  @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                    (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                (fun
                    (a b :
                      @Subtype.{1} Nat fun (p : Nat) =>
                        @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                          (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p) =>
                  @Subtype.instDecidableEq.{1} Nat
                    (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P)
                    instDecidableEqNat a b)
                a b)
            (Fin.fintype
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
            (instDecidableEqFin
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
            Bsource))
        (Erdos390.WholePaper.upperEndpoint
          (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P)
            (@instFintypeOption.{0}
              (@Subtype.{1} Nat fun (p : Nat) =>
                @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                  (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
              (@Finset.Subtype.fintype.{0} Nat P))
            (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P)
              (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M)
              (@instFintypeOption.{0}
                (@Subtype.{1} Nat fun (p : Nat) =>
                  @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                    (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                (@Finset.Subtype.fintype.{0} Nat P))
              (fun (a b : Erdos390.Full.PaperHeadSimplex.Tag P) =>
                @Option.instDecidableEq.{0}
                  (@Subtype.{1} Nat fun (p : Nat) =>
                    @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                  (fun
                      (a b :
                        @Subtype.{1} Nat fun (p : Nat) =>
                          @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                            (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p) =>
                    @Subtype.instDecidableEq.{1} Nat
                      (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                        (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P)
                      instDecidableEqNat a b)
                  a b)
              (Fin.fintype
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                  (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
              (instDecidableEqFin
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                  (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
              Bsource))
          (Erdos390.WholePaper.upperTailLength c
            (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P)
              (@instFintypeOption.{0}
                (@Subtype.{1} Nat fun (p : Nat) =>
                  @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                    (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                (@Finset.Subtype.fintype.{0} Nat P))
              (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P)
                (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M)
                (@instFintypeOption.{0}
                  (@Subtype.{1} Nat fun (p : Nat) =>
                    @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                  (@Finset.Subtype.fintype.{0} Nat P))
                (fun (a b : Erdos390.Full.PaperHeadSimplex.Tag P) =>
                  @Option.instDecidableEq.{0}
                    (@Subtype.{1} Nat fun (p : Nat) =>
                      @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                        (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                    (fun
                        (a b :
                          @Subtype.{1} Nat fun (p : Nat) =>
                            @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                              (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P
                              p) =>
                      @Subtype.instDecidableEq.{1} Nat
                        (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                          (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P)
                        instDecidableEqNat a b)
                    a b)
                (Fin.fintype
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                    (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                (instDecidableEqFin
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                    (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                Bsource))))
        R)
      (@Erdos390.WholePaper.BankPaperRealization.centralChangedMarkers
        (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P)
          (@instFintypeOption.{0}
            (@Subtype.{1} Nat fun (p : Nat) =>
              @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
            (@Finset.Subtype.fintype.{0} Nat P))
          (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P)
            (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M)
            (@instFintypeOption.{0}
              (@Subtype.{1} Nat fun (p : Nat) =>
                @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                  (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
              (@Finset.Subtype.fintype.{0} Nat P))
            (fun (a b : Erdos390.Full.PaperHeadSimplex.Tag P) =>
              @Option.instDecidableEq.{0}
                (@Subtype.{1} Nat fun (p : Nat) =>
                  @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                    (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                (fun
                    (a b :
                      @Subtype.{1} Nat fun (p : Nat) =>
                        @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                          (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p) =>
                  @Subtype.instDecidableEq.{1} Nat
                    (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P)
                    instDecidableEqNat a b)
                a b)
            (Fin.fintype
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
            (instDecidableEqFin
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
            Bsource))
        (Erdos390.WholePaper.upperEndpoint
          (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P)
            (@instFintypeOption.{0}
              (@Subtype.{1} Nat fun (p : Nat) =>
                @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                  (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
              (@Finset.Subtype.fintype.{0} Nat P))
            (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P)
              (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M)
              (@instFintypeOption.{0}
                (@Subtype.{1} Nat fun (p : Nat) =>
                  @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                    (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                (@Finset.Subtype.fintype.{0} Nat P))
              (fun (a b : Erdos390.Full.PaperHeadSimplex.Tag P) =>
                @Option.instDecidableEq.{0}
                  (@Subtype.{1} Nat fun (p : Nat) =>
                    @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                  (fun
                      (a b :
                        @Subtype.{1} Nat fun (p : Nat) =>
                          @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                            (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p) =>
                    @Subtype.instDecidableEq.{1} Nat
                      (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                        (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P)
                      instDecidableEqNat a b)
                  a b)
              (Fin.fintype
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                  (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
              (instDecidableEqFin
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                  (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
              Bsource))
          (Erdos390.WholePaper.upperTailLength c
            (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P)
              (@instFintypeOption.{0}
                (@Subtype.{1} Nat fun (p : Nat) =>
                  @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                    (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                (@Finset.Subtype.fintype.{0} Nat P))
              (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P)
                (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M)
                (@instFintypeOption.{0}
                  (@Subtype.{1} Nat fun (p : Nat) =>
                    @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                  (@Finset.Subtype.fintype.{0} Nat P))
                (fun (a b : Erdos390.Full.PaperHeadSimplex.Tag P) =>
                  @Option.instDecidableEq.{0}
                    (@Subtype.{1} Nat fun (p : Nat) =>
                      @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                        (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                    (fun
                        (a b :
                          @Subtype.{1} Nat fun (p : Nat) =>
                            @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                              (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P
                              p) =>
                      @Subtype.instDecidableEq.{1} Nat
                        (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                          (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P)
                        instDecidableEqNat a b)
                    a b)
                (Fin.fintype
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                    (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                (instDecidableEqFin
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                    (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                Bsource))))
        R depth)
      (G
        (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P)
          (@instFintypeOption.{0}
            (@Subtype.{1} Nat fun (p : Nat) =>
              @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
            (@Finset.Subtype.fintype.{0} Nat P))
          (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P)
            (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M)
            (@instFintypeOption.{0}
              (@Subtype.{1} Nat fun (p : Nat) =>
                @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                  (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
              (@Finset.Subtype.fintype.{0} Nat P))
            (fun (a b : Erdos390.Full.PaperHeadSimplex.Tag P) =>
              @Option.instDecidableEq.{0}
                (@Subtype.{1} Nat fun (p : Nat) =>
                  @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                    (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                (fun
                    (a b :
                      @Subtype.{1} Nat fun (p : Nat) =>
                        @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                          (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p) =>
                  @Subtype.instDecidableEq.{1} Nat
                    (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P)
                    instDecidableEqNat a b)
                a b)
            (Fin.fintype
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
            (instDecidableEqFin
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
            (@Erdos390.WholePaper.BankPaperRealization.BankPaperCanonicalSectionNinePostHeightBridgeInputsAt.postHeightBridge
              delta eta M P Bsource c depth K0 R certificate I deltaStar hdelta J))))
      R certificate deltaStar)
  (hupperBroad :
    ∀ (sign : Erdos390.Full.PaperBridgeFit.PhysicalSign),
      @LE.le.{0} Nat instLENat
        (Erdos390.Full.ArithmeticModel.physicalBound (I.upper sign)
          (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P)
            (@instFintypeOption.{0}
              (@Subtype.{1} Nat fun (p : Nat) =>
                @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                  (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
              (@Finset.Subtype.fintype.{0} Nat P))
            (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P)
              (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M)
              (@instFintypeOption.{0}
                (@Subtype.{1} Nat fun (p : Nat) =>
                  @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                    (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                (@Finset.Subtype.fintype.{0} Nat P))
              (fun (a b : Erdos390.Full.PaperHeadSimplex.Tag P) =>
                @Option.instDecidableEq.{0}
                  (@Subtype.{1} Nat fun (p : Nat) =>
                    @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                  (fun
                      (a b :
                        @Subtype.{1} Nat fun (p : Nat) =>
                          @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                            (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p) =>
                    @Subtype.instDecidableEq.{1} Nat
                      (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                        (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P)
                      instDecidableEqNat a b)
                  a b)
              (Fin.fintype
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                  (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
              (instDecidableEqFin
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                  (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
              (@Erdos390.WholePaper.BankPaperRealization.BankPaperCanonicalSectionNinePostHeightBridgeInputsAt.postHeightBridge
                delta eta M P Bsource c depth K0 R certificate I deltaStar hdelta J))))
        (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
            (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P)
              (@instFintypeOption.{0}
                (@Subtype.{1} Nat fun (p : Nat) =>
                  @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                    (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                (@Finset.Subtype.fintype.{0} Nat P))
              (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P)
                (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M)
                (@instFintypeOption.{0}
                  (@Subtype.{1} Nat fun (p : Nat) =>
                    @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                  (@Finset.Subtype.fintype.{0} Nat P))
                (fun (a b : Erdos390.Full.PaperHeadSimplex.Tag P) =>
                  @Option.instDecidableEq.{0}
                    (@Subtype.{1} Nat fun (p : Nat) =>
                      @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                        (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                    (fun
                        (a b :
                          @Subtype.{1} Nat fun (p : Nat) =>
                            @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                              (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P
                              p) =>
                      @Subtype.instDecidableEq.{1} Nat
                        (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                          (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P)
                        instDecidableEqNat a b)
                    a b)
                (Fin.fintype
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                    (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                (instDecidableEqFin
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                    (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                (@Erdos390.WholePaper.BankPaperRealization.BankPaperCanonicalSectionNinePostHeightBridgeInputsAt.postHeightBridge
                  delta eta M P Bsource c depth K0 R certificate I deltaStar hdelta J))))
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) K0
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
            (Erdos390.WholePaper.upperTailLength c
              (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P)
                (@instFintypeOption.{0}
                  (@Subtype.{1} Nat fun (p : Nat) =>
                    @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                  (@Finset.Subtype.fintype.{0} Nat P))
                (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P)
                  (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M)
                  (@instFintypeOption.{0}
                    (@Subtype.{1} Nat fun (p : Nat) =>
                      @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                        (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                    (@Finset.Subtype.fintype.{0} Nat P))
                  (fun (a b : Erdos390.Full.PaperHeadSimplex.Tag P) =>
                    @Option.instDecidableEq.{0}
                      (@Subtype.{1} Nat fun (p : Nat) =>
                        @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                          (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                      (fun
                          (a b :
                            @Subtype.{1} Nat fun (p : Nat) =>
                              @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P
                                p) =>
                        @Subtype.instDecidableEq.{1} Nat
                          (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                            (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P)
                          instDecidableEqNat a b)
                      a b)
                  (Fin.fintype
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                      (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                  (instDecidableEqFin
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                      (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                  (@Erdos390.WholePaper.BankPaperRealization.BankPaperCanonicalSectionNinePostHeightBridgeInputsAt.postHeightBridge
                    delta eta M P Bsource c depth K0 R certificate I deltaStar hdelta J)))))))
  (hroughDepth :
    @LE.le.{0} Nat instLENat
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) K0
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (Erdos390.WholePaper.upperTailLength c
          (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P)
            (@instFintypeOption.{0}
              (@Subtype.{1} Nat fun (p : Nat) =>
                @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                  (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
              (@Finset.Subtype.fintype.{0} Nat P))
            (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P)
              (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M)
              (@instFintypeOption.{0}
                (@Subtype.{1} Nat fun (p : Nat) =>
                  @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                    (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                (@Finset.Subtype.fintype.{0} Nat P))
              (fun (a b : Erdos390.Full.PaperHeadSimplex.Tag P) =>
                @Option.instDecidableEq.{0}
                  (@Subtype.{1} Nat fun (p : Nat) =>
                    @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                  (fun
                      (a b :
                        @Subtype.{1} Nat fun (p : Nat) =>
                          @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                            (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p) =>
                    @Subtype.instDecidableEq.{1} Nat
                      (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                        (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P)
                      instDecidableEqNat a b)
                  a b)
              (Fin.fintype
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                  (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
              (instDecidableEqFin
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                  (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
              (@Erdos390.WholePaper.BankPaperRealization.BankPaperCanonicalSectionNinePostHeightBridgeInputsAt.postHeightBridge
                delta eta M P Bsource c depth K0 R certificate I deltaStar hdelta J)))))
      (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P)
        (@instFintypeOption.{0}
          (@Subtype.{1} Nat fun (p : Nat) =>
            @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
              (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
          (@Finset.Subtype.fintype.{0} Nat P))
        (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P)
          (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M)
          (@instFintypeOption.{0}
            (@Subtype.{1} Nat fun (p : Nat) =>
              @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
            (@Finset.Subtype.fintype.{0} Nat P))
          (fun (a b : Erdos390.Full.PaperHeadSimplex.Tag P) =>
            @Option.instDecidableEq.{0}
              (@Subtype.{1} Nat fun (p : Nat) =>
                @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                  (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
              (fun
                  (a b :
                    @Subtype.{1} Nat fun (p : Nat) =>
                      @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                        (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p) =>
                @Subtype.instDecidableEq.{1} Nat
                  (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                    (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P)
                  instDecidableEqNat a b)
              a b)
          (Fin.fintype
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
          (instDecidableEqFin
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
          (@Erdos390.WholePaper.BankPaperRealization.BankPaperCanonicalSectionNinePostHeightBridgeInputsAt.postHeightBridge
            delta eta M P Bsource c depth K0 R certificate I deltaStar hdelta J))))
  (hqnOne :
    @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
      (@Erdos390.WholePaper.BankPaperRealization.BankPaperCanonicalSectionNinePostHeightBridgeInputsAt.qn delta eta M P
        Bsource c depth K0 R certificate I deltaStar hdelta J))
  (hbetaProt :
    @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
      (@Erdos390.WholePaper.BankPaperRealization.BankPaperCanonicalSectionNinePostHeightBridgeInputsAt.betaProt delta
        eta M P Bsource c depth K0 R certificate I deltaStar hdelta J))
  (hsourceState :
    @Erdos390.WholePaper.BankPaperRealization.BankPaperCanonicalSelectorSourceState c depth
      (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P)
        (@instFintypeOption.{0}
          (@Subtype.{1} Nat fun (p : Nat) =>
            @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
              (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
          (@Finset.Subtype.fintype.{0} Nat P))
        (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P)
          (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M)
          (@instFintypeOption.{0}
            (@Subtype.{1} Nat fun (p : Nat) =>
              @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
            (@Finset.Subtype.fintype.{0} Nat P))
          (fun (a b : Erdos390.Full.PaperHeadSimplex.Tag P) =>
            @Option.instDecidableEq.{0}
              (@Subtype.{1} Nat fun (p : Nat) =>
                @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                  (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
              (fun
                  (a b :
                    @Subtype.{1} Nat fun (p : Nat) =>
                      @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                        (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p) =>
                @Subtype.instDecidableEq.{1} Nat
                  (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                    (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P)
                  instDecidableEqNat a b)
              a b)
          (Fin.fintype
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
          (instDecidableEqFin
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
          Bsource))
      (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{0} (Erdos390.Full.PaperHeadSimplex.Tag P)
        (@instFintypeOption.{0}
          (@Subtype.{1} Nat fun (p : Nat) =>
            @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
              (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
          (@Finset.Subtype.fintype.{0} Nat P))
        (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P)
          (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M)
          (@instFintypeOption.{0}
            (@Subtype.{1} Nat fun (p : Nat) =>
              @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
            (@Finset.Subtype.fintype.{0} Nat P))
          (fun (a b : Erdos390.Full.PaperHeadSimplex.Tag P) =>
            @Option.instDecidableEq.{0}
              (@Subtype.{1} Nat fun (p : Nat) =>
                @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                  (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
              (fun
                  (a b :
                    @Subtype.{1} Nat fun (p : Nat) =>
                      @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                        (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p) =>
                @Subtype.instDecidableEq.{1} Nat
                  (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                    (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P)
                  instDecidableEqNat a b)
              a b)
          (Fin.fintype
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
          (instDecidableEqFin
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
          (@Erdos390.WholePaper.BankPaperRealization.BankPaperCanonicalSectionNinePostHeightBridgeInputsAt.postHeightBridge
            delta eta M P Bsource c depth K0 R certificate I deltaStar hdelta J)))
      (@Erdos390.WholePaper.BankPaperRealization.anchorGuardLeftCore
        (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P)
          (@instFintypeOption.{0}
            (@Subtype.{1} Nat fun (p : Nat) =>
              @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
            (@Finset.Subtype.fintype.{0} Nat P))
          (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P)
            (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M)
            (@instFintypeOption.{0}
              (@Subtype.{1} Nat fun (p : Nat) =>
                @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                  (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
              (@Finset.Subtype.fintype.{0} Nat P))
            (fun (a b : Erdos390.Full.PaperHeadSimplex.Tag P) =>
              @Option.instDecidableEq.{0}
                (@Subtype.{1} Nat fun (p : Nat) =>
                  @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                    (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                (fun
                    (a b :
                      @Subtype.{1} Nat fun (p : Nat) =>
                        @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                          (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p) =>
                  @Subtype.instDecidableEq.{1} Nat
                    (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P)
                    instDecidableEqNat a b)
                a b)
            (Fin.fintype
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
            (instDecidableEqFin
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
            Bsource))
        (Erdos390.WholePaper.upperEndpoint
          (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P)
            (@instFintypeOption.{0}
              (@Subtype.{1} Nat fun (p : Nat) =>
                @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                  (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
              (@Finset.Subtype.fintype.{0} Nat P))
            (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P)
              (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M)
              (@instFintypeOption.{0}
                (@Subtype.{1} Nat fun (p : Nat) =>
                  @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                    (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                (@Finset.Subtype.fintype.{0} Nat P))
              (fun (a b : Erdos390.Full.PaperHeadSimplex.Tag P) =>
                @Option.instDecidableEq.{0}
                  (@Subtype.{1} Nat fun (p : Nat) =>
                    @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                  (fun
                      (a b :
                        @Subtype.{1} Nat fun (p : Nat) =>
                          @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                            (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p) =>
                    @Subtype.instDecidableEq.{1} Nat
                      (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                        (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P)
                      instDecidableEqNat a b)
                  a b)
              (Fin.fintype
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                  (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
              (instDecidableEqFin
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                  (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
              Bsource))
          (Erdos390.WholePaper.upperTailLength c
            (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P)
              (@instFintypeOption.{0}
                (@Subtype.{1} Nat fun (p : Nat) =>
                  @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                    (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                (@Finset.Subtype.fintype.{0} Nat P))
              (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P)
                (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M)
                (@instFintypeOption.{0}
                  (@Subtype.{1} Nat fun (p : Nat) =>
                    @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                  (@Finset.Subtype.fintype.{0} Nat P))
                (fun (a b : Erdos390.Full.PaperHeadSimplex.Tag P) =>
                  @Option.instDecidableEq.{0}
                    (@Subtype.{1} Nat fun (p : Nat) =>
                      @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                        (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                    (fun
                        (a b :
                          @Subtype.{1} Nat fun (p : Nat) =>
                            @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                              (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P
                              p) =>
                      @Subtype.instDecidableEq.{1} Nat
                        (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                          (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P)
                        instDecidableEqNat a b)
                    a b)
                (Fin.fintype
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                    (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                (instDecidableEqFin
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                    (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                Bsource))))
        R)
      (@Erdos390.WholePaper.BankPaperRealization.anchorGuardRightCore
        (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P)
          (@instFintypeOption.{0}
            (@Subtype.{1} Nat fun (p : Nat) =>
              @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
            (@Finset.Subtype.fintype.{0} Nat P))
          (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P)
            (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M)
            (@instFintypeOption.{0}
              (@Subtype.{1} Nat fun (p : Nat) =>
                @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                  (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
              (@Finset.Subtype.fintype.{0} Nat P))
            (fun (a b : Erdos390.Full.PaperHeadSimplex.Tag P) =>
              @Option.instDecidableEq.{0}
                (@Subtype.{1} Nat fun (p : Nat) =>
                  @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                    (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                (fun
                    (a b :
                      @Subtype.{1} Nat fun (p : Nat) =>
                        @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                          (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p) =>
                  @Subtype.instDecidableEq.{1} Nat
                    (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P)
                    instDecidableEqNat a b)
                a b)
            (Fin.fintype
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
            (instDecidableEqFin
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
            Bsource))
        (Erdos390.WholePaper.upperEndpoint
          (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P)
            (@instFintypeOption.{0}
              (@Subtype.{1} Nat fun (p : Nat) =>
                @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                  (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
              (@Finset.Subtype.fintype.{0} Nat P))
            (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P)
              (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M)
              (@instFintypeOption.{0}
                (@Subtype.{1} Nat fun (p : Nat) =>
                  @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                    (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                (@Finset.Subtype.fintype.{0} Nat P))
              (fun (a b : Erdos390.Full.PaperHeadSimplex.Tag P) =>
                @Option.instDecidableEq.{0}
                  (@Subtype.{1} Nat fun (p : Nat) =>
                    @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                  (fun
                      (a b :
                        @Subtype.{1} Nat fun (p : Nat) =>
                          @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                            (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p) =>
                    @Subtype.instDecidableEq.{1} Nat
                      (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                        (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P)
                      instDecidableEqNat a b)
                  a b)
              (Fin.fintype
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                  (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
              (instDecidableEqFin
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                  (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
              Bsource))
          (Erdos390.WholePaper.upperTailLength c
            (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P)
              (@instFintypeOption.{0}
                (@Subtype.{1} Nat fun (p : Nat) =>
                  @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                    (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                (@Finset.Subtype.fintype.{0} Nat P))
              (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P)
                (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M)
                (@instFintypeOption.{0}
                  (@Subtype.{1} Nat fun (p : Nat) =>
                    @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                  (@Finset.Subtype.fintype.{0} Nat P))
                (fun (a b : Erdos390.Full.PaperHeadSimplex.Tag P) =>
                  @Option.instDecidableEq.{0}
                    (@Subtype.{1} Nat fun (p : Nat) =>
                      @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                        (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                    (fun
                        (a b :
                          @Subtype.{1} Nat fun (p : Nat) =>
                            @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                              (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P
                              p) =>
                      @Subtype.instDecidableEq.{1} Nat
                        (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                          (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P)
                        instDecidableEqNat a b)
                    a b)
                (Fin.fintype
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                    (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                (instDecidableEqFin
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                    (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                Bsource))))
        R)
      (@Erdos390.WholePaper.BankPaperRealization.centralChangedMarkers
        (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P)
          (@instFintypeOption.{0}
            (@Subtype.{1} Nat fun (p : Nat) =>
              @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
            (@Finset.Subtype.fintype.{0} Nat P))
          (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P)
            (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M)
            (@instFintypeOption.{0}
              (@Subtype.{1} Nat fun (p : Nat) =>
                @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                  (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
              (@Finset.Subtype.fintype.{0} Nat P))
            (fun (a b : Erdos390.Full.PaperHeadSimplex.Tag P) =>
              @Option.instDecidableEq.{0}
                (@Subtype.{1} Nat fun (p : Nat) =>
                  @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                    (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                (fun
                    (a b :
                      @Subtype.{1} Nat fun (p : Nat) =>
                        @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                          (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p) =>
                  @Subtype.instDecidableEq.{1} Nat
                    (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P)
                    instDecidableEqNat a b)
                a b)
            (Fin.fintype
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
            (instDecidableEqFin
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
            Bsource))
        (Erdos390.WholePaper.upperEndpoint
          (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P)
            (@instFintypeOption.{0}
              (@Subtype.{1} Nat fun (p : Nat) =>
                @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                  (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
              (@Finset.Subtype.fintype.{0} Nat P))
            (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P)
              (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M)
              (@instFintypeOption.{0}
                (@Subtype.{1} Nat fun (p : Nat) =>
                  @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                    (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                (@Finset.Subtype.fintype.{0} Nat P))
              (fun (a b : Erdos390.Full.PaperHeadSimplex.Tag P) =>
                @Option.instDecidableEq.{0}
                  (@Subtype.{1} Nat fun (p : Nat) =>
                    @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                  (fun
                      (a b :
                        @Subtype.{1} Nat fun (p : Nat) =>
                          @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                            (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p) =>
                    @Subtype.instDecidableEq.{1} Nat
                      (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                        (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P)
                      instDecidableEqNat a b)
                  a b)
              (Fin.fintype
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                  (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
              (instDecidableEqFin
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                  (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
              Bsource))
          (Erdos390.WholePaper.upperTailLength c
            (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P)
              (@instFintypeOption.{0}
                (@Subtype.{1} Nat fun (p : Nat) =>
                  @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                    (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                (@Finset.Subtype.fintype.{0} Nat P))
              (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P)
                (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M)
                (@instFintypeOption.{0}
                  (@Subtype.{1} Nat fun (p : Nat) =>
                    @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                  (@Finset.Subtype.fintype.{0} Nat P))
                (fun (a b : Erdos390.Full.PaperHeadSimplex.Tag P) =>
                  @Option.instDecidableEq.{0}
                    (@Subtype.{1} Nat fun (p : Nat) =>
                      @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                        (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                    (fun
                        (a b :
                          @Subtype.{1} Nat fun (p : Nat) =>
                            @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                              (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P
                              p) =>
                      @Subtype.instDecidableEq.{1} Nat
                        (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                          (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P)
                        instDecidableEqNat a b)
                    a b)
                (Fin.fintype
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                    (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                (instDecidableEqFin
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                    (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                Bsource))))
        R depth)
      R certificate
      (@Erdos390.WholePaper.BankPaperRealization.paperFixedExceptionalFactors
        (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P)
          (@instFintypeOption.{0}
            (@Subtype.{1} Nat fun (p : Nat) =>
              @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
            (@Finset.Subtype.fintype.{0} Nat P))
          (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P)
            (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M)
            (@instFintypeOption.{0}
              (@Subtype.{1} Nat fun (p : Nat) =>
                @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                  (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
              (@Finset.Subtype.fintype.{0} Nat P))
            (fun (a b : Erdos390.Full.PaperHeadSimplex.Tag P) =>
              @Option.instDecidableEq.{0}
                (@Subtype.{1} Nat fun (p : Nat) =>
                  @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                    (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                (fun
                    (a b :
                      @Subtype.{1} Nat fun (p : Nat) =>
                        @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                          (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p) =>
                  @Subtype.instDecidableEq.{1} Nat
                    (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P)
                    instDecidableEqNat a b)
                a b)
            (Fin.fintype
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
            (instDecidableEqFin
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
            Bsource))
        (Erdos390.WholePaper.upperTailLength c
          (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P)
            (@instFintypeOption.{0}
              (@Subtype.{1} Nat fun (p : Nat) =>
                @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                  (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
              (@Finset.Subtype.fintype.{0} Nat P))
            (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P)
              (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M)
              (@instFintypeOption.{0}
                (@Subtype.{1} Nat fun (p : Nat) =>
                  @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                    (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                (@Finset.Subtype.fintype.{0} Nat P))
              (fun (a b : Erdos390.Full.PaperHeadSimplex.Tag P) =>
                @Option.instDecidableEq.{0}
                  (@Subtype.{1} Nat fun (p : Nat) =>
                    @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                  (fun
                      (a b :
                        @Subtype.{1} Nat fun (p : Nat) =>
                          @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                            (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p) =>
                    @Subtype.instDecidableEq.{1} Nat
                      (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                        (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P)
                      instDecidableEqNat a b)
                  a b)
              (Fin.fintype
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                  (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
              (instDecidableEqFin
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                  (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
              Bsource)))
        R deltaStar)
      (@Erdos390.WholePaper.BankPaperRealization.roughCanonicalGuardedCandidateSet c depth
        (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P)
          (@instFintypeOption.{0}
            (@Subtype.{1} Nat fun (p : Nat) =>
              @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
            (@Finset.Subtype.fintype.{0} Nat P))
          (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P)
            (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M)
            (@instFintypeOption.{0}
              (@Subtype.{1} Nat fun (p : Nat) =>
                @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                  (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
              (@Finset.Subtype.fintype.{0} Nat P))
            (fun (a b : Erdos390.Full.PaperHeadSimplex.Tag P) =>
              @Option.instDecidableEq.{0}
                (@Subtype.{1} Nat fun (p : Nat) =>
                  @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                    (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                (fun
                    (a b :
                      @Subtype.{1} Nat fun (p : Nat) =>
                        @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                          (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p) =>
                  @Subtype.instDecidableEq.{1} Nat
                    (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P)
                    instDecidableEqNat a b)
                a b)
            (Fin.fintype
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
            (instDecidableEqFin
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
            Bsource))
        (Erdos390.WholePaper.upperTailLength c
          (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P)
            (@instFintypeOption.{0}
              (@Subtype.{1} Nat fun (p : Nat) =>
                @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                  (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
              (@Finset.Subtype.fintype.{0} Nat P))
            (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P)
              (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M)
              (@instFintypeOption.{0}
                (@Subtype.{1} Nat fun (p : Nat) =>
                  @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                    (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                (@Finset.Subtype.fintype.{0} Nat P))
              (fun (a b : Erdos390.Full.PaperHeadSimplex.Tag P) =>
                @Option.instDecidableEq.{0}
                  (@Subtype.{1} Nat fun (p : Nat) =>
                    @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                  (fun
                      (a b :
                        @Subtype.{1} Nat fun (p : Nat) =>
                          @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                            (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p) =>
                    @Subtype.instDecidableEq.{1} Nat
                      (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                        (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P)
                      instDecidableEqNat a b)
                  a b)
              (Fin.fintype
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                  (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
              (instDecidableEqFin
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                  (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
              Bsource)))
        (@Erdos390.WholePaper.BankPaperRealization.anchorGuardLeftCore
          (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P)
            (@instFintypeOption.{0}
              (@Subtype.{1} Nat fun (p : Nat) =>
                @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                  (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
              (@Finset.Subtype.fintype.{0} Nat P))
            (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P)
              (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M)
              (@instFintypeOption.{0}
                (@Subtype.{1} Nat fun (p : Nat) =>
                  @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                    (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                (@Finset.Subtype.fintype.{0} Nat P))
              (fun (a b : Erdos390.Full.PaperHeadSimplex.Tag P) =>
                @Option.instDecidableEq.{0}
                  (@Subtype.{1} Nat fun (p : Nat) =>
                    @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                  (fun
                      (a b :
                        @Subtype.{1} Nat fun (p : Nat) =>
                          @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                            (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p) =>
                    @Subtype.instDecidableEq.{1} Nat
                      (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                        (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P)
                      instDecidableEqNat a b)
                  a b)
              (Fin.fintype
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                  (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
              (instDecidableEqFin
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                  (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
              Bsource))
          (Erdos390.WholePaper.upperEndpoint
            (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P)
              (@instFintypeOption.{0}
                (@Subtype.{1} Nat fun (p : Nat) =>
                  @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                    (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                (@Finset.Subtype.fintype.{0} Nat P))
              (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P)
                (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M)
                (@instFintypeOption.{0}
                  (@Subtype.{1} Nat fun (p : Nat) =>
                    @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                  (@Finset.Subtype.fintype.{0} Nat P))
                (fun (a b : Erdos390.Full.PaperHeadSimplex.Tag P) =>
                  @Option.instDecidableEq.{0}
                    (@Subtype.{1} Nat fun (p : Nat) =>
                      @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                        (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                    (fun
                        (a b :
                          @Subtype.{1} Nat fun (p : Nat) =>
                            @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                              (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P
                              p) =>
                      @Subtype.instDecidableEq.{1} Nat
                        (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                          (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P)
                        instDecidableEqNat a b)
                    a b)
                (Fin.fintype
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                    (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                (instDecidableEqFin
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                    (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                Bsource))
            (Erdos390.WholePaper.upperTailLength c
              (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P)
                (@instFintypeOption.{0}
                  (@Subtype.{1} Nat fun (p : Nat) =>
                    @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                  (@Finset.Subtype.fintype.{0} Nat P))
                (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P)
                  (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M)
                  (@instFintypeOption.{0}
                    (@Subtype.{1} Nat fun (p : Nat) =>
                      @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                        (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                    (@Finset.Subtype.fintype.{0} Nat P))
                  (fun (a b : Erdos390.Full.PaperHeadSimplex.Tag P) =>
                    @Option.instDecidableEq.{0}
                      (@Subtype.{1} Nat fun (p : Nat) =>
                        @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                          (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                      (fun
                          (a b :
                            @Subtype.{1} Nat fun (p : Nat) =>
                              @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P
                                p) =>
                        @Subtype.instDecidableEq.{1} Nat
                          (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                            (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P)
                          instDecidableEqNat a b)
                      a b)
                  (Fin.fintype
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                      (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                  (instDecidableEqFin
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                      (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                  Bsource))))
          R)
        (@Erdos390.WholePaper.BankPaperRealization.anchorGuardRightCore
          (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P)
            (@instFintypeOption.{0}
              (@Subtype.{1} Nat fun (p : Nat) =>
                @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                  (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
              (@Finset.Subtype.fintype.{0} Nat P))
            (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P)
              (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M)
              (@instFintypeOption.{0}
                (@Subtype.{1} Nat fun (p : Nat) =>
                  @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                    (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                (@Finset.Subtype.fintype.{0} Nat P))
              (fun (a b : Erdos390.Full.PaperHeadSimplex.Tag P) =>
                @Option.instDecidableEq.{0}
                  (@Subtype.{1} Nat fun (p : Nat) =>
                    @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                  (fun
                      (a b :
                        @Subtype.{1} Nat fun (p : Nat) =>
                          @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                            (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p) =>
                    @Subtype.instDecidableEq.{1} Nat
                      (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                        (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P)
                      instDecidableEqNat a b)
                  a b)
              (Fin.fintype
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                  (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
              (instDecidableEqFin
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                  (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
              Bsource))
          (Erdos390.WholePaper.upperEndpoint
            (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P)
              (@instFintypeOption.{0}
                (@Subtype.{1} Nat fun (p : Nat) =>
                  @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                    (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                (@Finset.Subtype.fintype.{0} Nat P))
              (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P)
                (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M)
                (@instFintypeOption.{0}
                  (@Subtype.{1} Nat fun (p : Nat) =>
                    @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                  (@Finset.Subtype.fintype.{0} Nat P))
                (fun (a b : Erdos390.Full.PaperHeadSimplex.Tag P) =>
                  @Option.instDecidableEq.{0}
                    (@Subtype.{1} Nat fun (p : Nat) =>
                      @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                        (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                    (fun
                        (a b :
                          @Subtype.{1} Nat fun (p : Nat) =>
                            @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                              (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P
                              p) =>
                      @Subtype.instDecidableEq.{1} Nat
                        (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                          (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P)
                        instDecidableEqNat a b)
                    a b)
                (Fin.fintype
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                    (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                (instDecidableEqFin
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                    (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                Bsource))
            (Erdos390.WholePaper.upperTailLength c
              (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P)
                (@instFintypeOption.{0}
                  (@Subtype.{1} Nat fun (p : Nat) =>
                    @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                  (@Finset.Subtype.fintype.{0} Nat P))
                (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P)
                  (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M)
                  (@instFintypeOption.{0}
                    (@Subtype.{1} Nat fun (p : Nat) =>
                      @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                        (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                    (@Finset.Subtype.fintype.{0} Nat P))
                  (fun (a b : Erdos390.Full.PaperHeadSimplex.Tag P) =>
                    @Option.instDecidableEq.{0}
                      (@Subtype.{1} Nat fun (p : Nat) =>
                        @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                          (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                      (fun
                          (a b :
                            @Subtype.{1} Nat fun (p : Nat) =>
                              @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P
                                p) =>
                        @Subtype.instDecidableEq.{1} Nat
                          (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                            (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P)
                          instDecidableEqNat a b)
                      a b)
                  (Fin.fintype
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                      (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                  (instDecidableEqFin
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                      (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                  Bsource))))
          R)
        (@Erdos390.WholePaper.BankPaperRealization.centralChangedMarkers
          (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P)
            (@instFintypeOption.{0}
              (@Subtype.{1} Nat fun (p : Nat) =>
                @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                  (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
              (@Finset.Subtype.fintype.{0} Nat P))
            (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P)
              (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M)
              (@instFintypeOption.{0}
                (@Subtype.{1} Nat fun (p : Nat) =>
                  @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                    (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                (@Finset.Subtype.fintype.{0} Nat P))
              (fun (a b : Erdos390.Full.PaperHeadSimplex.Tag P) =>
                @Option.instDecidableEq.{0}
                  (@Subtype.{1} Nat fun (p : Nat) =>
                    @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                  (fun
                      (a b :
                        @Subtype.{1} Nat fun (p : Nat) =>
                          @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                            (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p) =>
                    @Subtype.instDecidableEq.{1} Nat
                      (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                        (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P)
                      instDecidableEqNat a b)
                  a b)
              (Fin.fintype
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                  (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
              (instDecidableEqFin
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                  (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
              Bsource))
          (Erdos390.WholePaper.upperEndpoint
            (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P)
              (@instFintypeOption.{0}
                (@Subtype.{1} Nat fun (p : Nat) =>
                  @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                    (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                (@Finset.Subtype.fintype.{0} Nat P))
              (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P)
                (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M)
                (@instFintypeOption.{0}
                  (@Subtype.{1} Nat fun (p : Nat) =>
                    @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                  (@Finset.Subtype.fintype.{0} Nat P))
                (fun (a b : Erdos390.Full.PaperHeadSimplex.Tag P) =>
                  @Option.instDecidableEq.{0}
                    (@Subtype.{1} Nat fun (p : Nat) =>
                      @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                        (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                    (fun
                        (a b :
                          @Subtype.{1} Nat fun (p : Nat) =>
                            @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                              (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P
                              p) =>
                      @Subtype.instDecidableEq.{1} Nat
                        (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                          (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P)
                        instDecidableEqNat a b)
                    a b)
                (Fin.fintype
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                    (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                (instDecidableEqFin
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                    (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                Bsource))
            (Erdos390.WholePaper.upperTailLength c
              (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P)
                (@instFintypeOption.{0}
                  (@Subtype.{1} Nat fun (p : Nat) =>
                    @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                  (@Finset.Subtype.fintype.{0} Nat P))
                (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P)
                  (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M)
                  (@instFintypeOption.{0}
                    (@Subtype.{1} Nat fun (p : Nat) =>
                      @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                        (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                    (@Finset.Subtype.fintype.{0} Nat P))
                  (fun (a b : Erdos390.Full.PaperHeadSimplex.Tag P) =>
                    @Option.instDecidableEq.{0}
                      (@Subtype.{1} Nat fun (p : Nat) =>
                        @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                          (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                      (fun
                          (a b :
                            @Subtype.{1} Nat fun (p : Nat) =>
                              @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P
                                p) =>
                        @Subtype.instDecidableEq.{1} Nat
                          (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                            (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P)
                          instDecidableEqNat a b)
                      a b)
                  (Fin.fintype
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                      (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                  (instDecidableEqFin
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                      (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                  Bsource))))
          R depth)
        R certificate deltaStar
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) K0
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@Erdos390.WholePaper.BankPaperRealization.BankPaperCanonicalSectionNinePostHeightBridgeInputsAt.roundedSourceSelector
        delta eta M P Bsource c depth K0 R certificate I deltaStar hdelta J))
  (Cmass density : Real)
  (hCmass :
    @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) Cmass)
  (hdensity :
    @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) density)
  (hmassUpper :
    @LE.le.{0} Real Real.instLE
      (@Erdos390.WholePaper.BankPaperRealization.BankPaperCanonicalSectionNinePostHeightBridgeInputsAt.qn delta eta M P
        Bsource c depth K0 R certificate I deltaStar hdelta J)
      (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) Cmass
          (@Nat.cast.{0} Real Real.instNatCast
            (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P)
              (@instFintypeOption.{0}
                (@Subtype.{1} Nat fun (p : Nat) =>
                  @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                    (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                (@Finset.Subtype.fintype.{0} Nat P))
              (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P)
                (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M)
                (@instFintypeOption.{0}
                  (@Subtype.{1} Nat fun (p : Nat) =>
                    @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                  (@Finset.Subtype.fintype.{0} Nat P))
                (fun (a b : Erdos390.Full.PaperHeadSimplex.Tag P) =>
                  @Option.instDecidableEq.{0}
                    (@Subtype.{1} Nat fun (p : Nat) =>
                      @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                        (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                    (fun
                        (a b :
                          @Subtype.{1} Nat fun (p : Nat) =>
                            @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                              (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P
                              p) =>
                      @Subtype.instDecidableEq.{1} Nat
                        (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                          (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P)
                        instDecidableEqNat a b)
                    a b)
                (Fin.fintype
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                    (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                (instDecidableEqFin
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                    (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                (@Erdos390.WholePaper.BankPaperRealization.BankPaperCanonicalSectionNinePostHeightBridgeInputsAt.postHeightBridge
                  delta eta M P Bsource c depth K0 R certificate I deltaStar hdelta J)))))
        (@Erdos390.Full.PaperBridgeFit.BridgeData.L.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P)
          (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M)
          (@instFintypeOption.{0}
            (@Subtype.{1} Nat fun (p : Nat) =>
              @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
            (@Finset.Subtype.fintype.{0} Nat P))
          (fun (a b : Erdos390.Full.PaperHeadSimplex.Tag P) =>
            @Option.instDecidableEq.{0}
              (@Subtype.{1} Nat fun (p : Nat) =>
                @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                  (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
              (fun
                  (a b :
                    @Subtype.{1} Nat fun (p : Nat) =>
                      @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                        (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p) =>
                @Subtype.instDecidableEq.{1} Nat
                  (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                    (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P)
                  instDecidableEqNat a b)
              a b)
          (Fin.fintype
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
          (instDecidableEqFin
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
          (@Erdos390.WholePaper.BankPaperRealization.BankPaperCanonicalSectionNinePostHeightBridgeInputsAt.postHeightBridge
            delta eta M P Bsource c depth K0 R certificate I deltaStar hdelta J))))
  (hcellDensity :
    ∀ (cell : Erdos390.Full.PaperBridgeFit.Cell.{0} (Erdos390.Full.PaperHeadSimplex.Tag P)),
      @LE.le.{0} Real Real.instLE
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) density
          (@Nat.cast.{0} Real Real.instNatCast
            (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P)
              (@instFintypeOption.{0}
                (@Subtype.{1} Nat fun (p : Nat) =>
                  @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                    (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                (@Finset.Subtype.fintype.{0} Nat P))
              (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P)
                (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M)
                (@instFintypeOption.{0}
                  (@Subtype.{1} Nat fun (p : Nat) =>
                    @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                  (@Finset.Subtype.fintype.{0} Nat P))
                (fun (a b : Erdos390.Full.PaperHeadSimplex.Tag P) =>
                  @Option.instDecidableEq.{0}
                    (@Subtype.{1} Nat fun (p : Nat) =>
                      @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                        (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                    (fun
                        (a b :
                          @Subtype.{1} Nat fun (p : Nat) =>
                            @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                              (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P
                              p) =>
                      @Subtype.instDecidableEq.{1} Nat
                        (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                          (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P)
                        instDecidableEqNat a b)
                    a b)
                (Fin.fintype
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                    (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                (instDecidableEqFin
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                    (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                (@Erdos390.WholePaper.BankPaperRealization.BankPaperCanonicalSectionNinePostHeightBridgeInputsAt.postHeightBridge
                  delta eta M P Bsource c depth K0 R certificate I deltaStar hdelta J)))))
        (@Nat.cast.{0} Real Real.instNatCast
          (@Fintype.card.{0}
            (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.SampleAt.{0} (Erdos390.Full.PaperHeadSimplex.Tag P)
              (@instFintypeOption.{0}
                (@Subtype.{1} Nat fun (p : Nat) =>
                  @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                    (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                (@Finset.Subtype.fintype.{0} Nat P))
              (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P)
                (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M)
                (@instFintypeOption.{0}
                  (@Subtype.{1} Nat fun (p : Nat) =>
                    @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                  (@Finset.Subtype.fintype.{0} Nat P))
                (fun (a b : Erdos390.Full.PaperHeadSimplex.Tag P) =>
                  @Option.instDecidableEq.{0}
                    (@Subtype.{1} Nat fun (p : Nat) =>
                      @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                        (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                    (fun
                        (a b :
                          @Subtype.{1} Nat fun (p : Nat) =>
                            @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                              (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P
                              p) =>
                      @Subtype.instDecidableEq.{1} Nat
                        (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                          (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P)
                        instDecidableEqNat a b)
                    a b)
                (Fin.fintype
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                    (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                (instDecidableEqFin
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                    (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                (@Erdos390.WholePaper.BankPaperRealization.BankPaperCanonicalSectionNinePostHeightBridgeInputsAt.postHeightBridge
                  delta eta M P Bsource c depth K0 R certificate I deltaStar hdelta J))
              cell)
            (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.sampleAtFintype.{0}
              (Erdos390.Full.PaperHeadSimplex.Tag P)
              (@instFintypeOption.{0}
                (@Subtype.{1} Nat fun (p : Nat) =>
                  @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                    (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                (@Finset.Subtype.fintype.{0} Nat P))
              (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P)
                (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M)
                (@instFintypeOption.{0}
                  (@Subtype.{1} Nat fun (p : Nat) =>
                    @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                  (@Finset.Subtype.fintype.{0} Nat P))
                (fun (a b : Erdos390.Full.PaperHeadSimplex.Tag P) =>
                  @Option.instDecidableEq.{0}
                    (@Subtype.{1} Nat fun (p : Nat) =>
                      @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                        (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                    (fun
                        (a b :
                          @Subtype.{1} Nat fun (p : Nat) =>
                            @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                              (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P
                              p) =>
                      @Subtype.instDecidableEq.{1} Nat
                        (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                          (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P)
                        instDecidableEqNat a b)
                    a b)
                (Fin.fintype
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                    (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                (instDecidableEqFin
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                    (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                (@Erdos390.WholePaper.BankPaperRealization.BankPaperCanonicalSectionNinePostHeightBridgeInputsAt.postHeightBridge
                  delta eta M P Bsource c depth K0 R certificate I deltaStar hdelta J))
              cell))))
  (hcombined :
    @Dvd.dvd.{0} Nat Nat.instDvd
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
        (Erdos390.WholePaper.centralAnchorDivisor
          (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P)
            (@instFintypeOption.{0}
              (@Subtype.{1} Nat fun (p : Nat) =>
                @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                  (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
              (@Finset.Subtype.fintype.{0} Nat P))
            (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P)
              (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M)
              (@instFintypeOption.{0}
                (@Subtype.{1} Nat fun (p : Nat) =>
                  @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                    (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                (@Finset.Subtype.fintype.{0} Nat P))
              (fun (a b : Erdos390.Full.PaperHeadSimplex.Tag P) =>
                @Option.instDecidableEq.{0}
                  (@Subtype.{1} Nat fun (p : Nat) =>
                    @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                  (fun
                      (a b :
                        @Subtype.{1} Nat fun (p : Nat) =>
                          @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                            (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p) =>
                    @Subtype.instDecidableEq.{1} Nat
                      (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                        (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P)
                      instDecidableEqNat a b)
                  a b)
              (Fin.fintype
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                  (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
              (instDecidableEqFin
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                  (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
              (@Erdos390.WholePaper.BankPaperRealization.BankPaperCanonicalSectionNinePostHeightBridgeInputsAt.postHeightBridge
                delta eta M P Bsource c depth K0 R certificate I deltaStar hdelta J)))
          (Erdos390.WholePaper.centralAnchorCutoff depth
            (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P)
              (@instFintypeOption.{0}
                (@Subtype.{1} Nat fun (p : Nat) =>
                  @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                    (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                (@Finset.Subtype.fintype.{0} Nat P))
              (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P)
                (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M)
                (@instFintypeOption.{0}
                  (@Subtype.{1} Nat fun (p : Nat) =>
                    @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                  (@Finset.Subtype.fintype.{0} Nat P))
                (fun (a b : Erdos390.Full.PaperHeadSimplex.Tag P) =>
                  @Option.instDecidableEq.{0}
                    (@Subtype.{1} Nat fun (p : Nat) =>
                      @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                        (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                    (fun
                        (a b :
                          @Subtype.{1} Nat fun (p : Nat) =>
                            @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                              (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P
                              p) =>
                      @Subtype.instDecidableEq.{1} Nat
                        (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                          (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P)
                        instDecidableEqNat a b)
                    a b)
                (Fin.fintype
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                    (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                (instDecidableEqFin
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                    (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                (@Erdos390.WholePaper.BankPaperRealization.BankPaperCanonicalSectionNinePostHeightBridgeInputsAt.postHeightBridge
                  delta eta M P Bsource c depth K0 R certificate I deltaStar hdelta J))))
          (@Erdos390.WholePaper.GuardedCentralAnchorCertificate.q c depth
            (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P)
              (@instFintypeOption.{0}
                (@Subtype.{1} Nat fun (p : Nat) =>
                  @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                    (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                (@Finset.Subtype.fintype.{0} Nat P))
              (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P)
                (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M)
                (@instFintypeOption.{0}
                  (@Subtype.{1} Nat fun (p : Nat) =>
                    @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                  (@Finset.Subtype.fintype.{0} Nat P))
                (fun (a b : Erdos390.Full.PaperHeadSimplex.Tag P) =>
                  @Option.instDecidableEq.{0}
                    (@Subtype.{1} Nat fun (p : Nat) =>
                      @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                        (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                    (fun
                        (a b :
                          @Subtype.{1} Nat fun (p : Nat) =>
                            @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                              (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P
                              p) =>
                      @Subtype.instDecidableEq.{1} Nat
                        (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                          (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P)
                        instDecidableEqNat a b)
                    a b)
                (Fin.fintype
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                    (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                (instDecidableEqFin
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                    (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                Bsource))
            (@Erdos390.WholePaper.BankPaperRealization.anchorGuardLeftCore
              (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P)
                (@instFintypeOption.{0}
                  (@Subtype.{1} Nat fun (p : Nat) =>
                    @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                  (@Finset.Subtype.fintype.{0} Nat P))
                (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P)
                  (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M)
                  (@instFintypeOption.{0}
                    (@Subtype.{1} Nat fun (p : Nat) =>
                      @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                        (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                    (@Finset.Subtype.fintype.{0} Nat P))
                  (fun (a b : Erdos390.Full.PaperHeadSimplex.Tag P) =>
                    @Option.instDecidableEq.{0}
                      (@Subtype.{1} Nat fun (p : Nat) =>
                        @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                          (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                      (fun
                          (a b :
                            @Subtype.{1} Nat fun (p : Nat) =>
                              @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P
                                p) =>
                        @Subtype.instDecidableEq.{1} Nat
                          (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                            (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P)
                          instDecidableEqNat a b)
                      a b)
                  (Fin.fintype
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                      (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                  (instDecidableEqFin
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                      (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                  Bsource))
              (Erdos390.WholePaper.upperEndpoint
                (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P)
                  (@instFintypeOption.{0}
                    (@Subtype.{1} Nat fun (p : Nat) =>
                      @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                        (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                    (@Finset.Subtype.fintype.{0} Nat P))
                  (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P)
                    (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M)
                    (@instFintypeOption.{0}
                      (@Subtype.{1} Nat fun (p : Nat) =>
                        @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                          (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                      (@Finset.Subtype.fintype.{0} Nat P))
                    (fun (a b : Erdos390.Full.PaperHeadSimplex.Tag P) =>
                      @Option.instDecidableEq.{0}
                        (@Subtype.{1} Nat fun (p : Nat) =>
                          @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                            (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                        (fun
                            (a b :
                              @Subtype.{1} Nat fun (p : Nat) =>
                                @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                  (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P
                                  p) =>
                          @Subtype.instDecidableEq.{1} Nat
                            (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                              (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P)
                            instDecidableEqNat a b)
                        a b)
                    (Fin.fintype
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                        (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                    (instDecidableEqFin
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                        (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                    Bsource))
                (Erdos390.WholePaper.upperTailLength c
                  (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P)
                    (@instFintypeOption.{0}
                      (@Subtype.{1} Nat fun (p : Nat) =>
                        @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                          (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                      (@Finset.Subtype.fintype.{0} Nat P))
                    (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P)
                      (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M)
                      (@instFintypeOption.{0}
                        (@Subtype.{1} Nat fun (p : Nat) =>
                          @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                            (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                        (@Finset.Subtype.fintype.{0} Nat P))
                      (fun (a b : Erdos390.Full.PaperHeadSimplex.Tag P) =>
                        @Option.instDecidableEq.{0}
                          (@Subtype.{1} Nat fun (p : Nat) =>
                            @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                              (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                          (fun
                              (a b :
                                @Subtype.{1} Nat fun (p : Nat) =>
                                  @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                    (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat))
                                    P p) =>
                            @Subtype.instDecidableEq.{1} Nat
                              (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P)
                              instDecidableEqNat a b)
                          a b)
                      (Fin.fintype
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                          (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                      (instDecidableEqFin
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                          (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                      Bsource))))
              R)
            (@Erdos390.WholePaper.BankPaperRealization.anchorGuardRightCore
              (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P)
                (@instFintypeOption.{0}
                  (@Subtype.{1} Nat fun (p : Nat) =>
                    @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                  (@Finset.Subtype.fintype.{0} Nat P))
                (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P)
                  (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M)
                  (@instFintypeOption.{0}
                    (@Subtype.{1} Nat fun (p : Nat) =>
                      @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                        (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                    (@Finset.Subtype.fintype.{0} Nat P))
                  (fun (a b : Erdos390.Full.PaperHeadSimplex.Tag P) =>
                    @Option.instDecidableEq.{0}
                      (@Subtype.{1} Nat fun (p : Nat) =>
                        @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                          (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                      (fun
                          (a b :
                            @Subtype.{1} Nat fun (p : Nat) =>
                              @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P
                                p) =>
                        @Subtype.instDecidableEq.{1} Nat
                          (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                            (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P)
                          instDecidableEqNat a b)
                      a b)
                  (Fin.fintype
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                      (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                  (instDecidableEqFin
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                      (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                  Bsource))
              (Erdos390.WholePaper.upperEndpoint
                (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P)
                  (@instFintypeOption.{0}
                    (@Subtype.{1} Nat fun (p : Nat) =>
                      @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                        (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                    (@Finset.Subtype.fintype.{0} Nat P))
                  (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P)
                    (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M)
                    (@instFintypeOption.{0}
                      (@Subtype.{1} Nat fun (p : Nat) =>
                        @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                          (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                      (@Finset.Subtype.fintype.{0} Nat P))
                    (fun (a b : Erdos390.Full.PaperHeadSimplex.Tag P) =>
                      @Option.instDecidableEq.{0}
                        (@Subtype.{1} Nat fun (p : Nat) =>
                          @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                            (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                        (fun
                            (a b :
                              @Subtype.{1} Nat fun (p : Nat) =>
                                @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                  (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P
                                  p) =>
                          @Subtype.instDecidableEq.{1} Nat
                            (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                              (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P)
                            instDecidableEqNat a b)
                        a b)
                    (Fin.fintype
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                        (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                    (instDecidableEqFin
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                        (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                    Bsource))
                (Erdos390.WholePaper.upperTailLength c
                  (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P)
                    (@instFintypeOption.{0}
                      (@Subtype.{1} Nat fun (p : Nat) =>
                        @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                          (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                      (@Finset.Subtype.fintype.{0} Nat P))
                    (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P)
                      (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M)
                      (@instFintypeOption.{0}
                        (@Subtype.{1} Nat fun (p : Nat) =>
                          @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                            (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                        (@Finset.Subtype.fintype.{0} Nat P))
                      (fun (a b : Erdos390.Full.PaperHeadSimplex.Tag P) =>
                        @Option.instDecidableEq.{0}
                          (@Subtype.{1} Nat fun (p : Nat) =>
                            @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                              (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                          (fun
                              (a b :
                                @Subtype.{1} Nat fun (p : Nat) =>
                                  @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                    (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat))
                                    P p) =>
                            @Subtype.instDecidableEq.{1} Nat
                              (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P)
                              instDecidableEqNat a b)
                          a b)
                      (Fin.fintype
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                          (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                      (instDecidableEqFin
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                          (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                      Bsource))))
              R)
            (@Erdos390.WholePaper.BankPaperRealization.centralChangedMarkers
              (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P)
                (@instFintypeOption.{0}
                  (@Subtype.{1} Nat fun (p : Nat) =>
                    @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                  (@Finset.Subtype.fintype.{0} Nat P))
                (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P)
                  (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M)
                  (@instFintypeOption.{0}
                    (@Subtype.{1} Nat fun (p : Nat) =>
                      @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                        (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                    (@Finset.Subtype.fintype.{0} Nat P))
                  (fun (a b : Erdos390.Full.PaperHeadSimplex.Tag P) =>
                    @Option.instDecidableEq.{0}
                      (@Subtype.{1} Nat fun (p : Nat) =>
                        @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                          (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                      (fun
                          (a b :
                            @Subtype.{1} Nat fun (p : Nat) =>
                              @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P
                                p) =>
                        @Subtype.instDecidableEq.{1} Nat
                          (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                            (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P)
                          instDecidableEqNat a b)
                      a b)
                  (Fin.fintype
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                      (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                  (instDecidableEqFin
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                      (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                  Bsource))
              (Erdos390.WholePaper.upperEndpoint
                (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P)
                  (@instFintypeOption.{0}
                    (@Subtype.{1} Nat fun (p : Nat) =>
                      @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                        (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                    (@Finset.Subtype.fintype.{0} Nat P))
                  (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P)
                    (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M)
                    (@instFintypeOption.{0}
                      (@Subtype.{1} Nat fun (p : Nat) =>
                        @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                          (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                      (@Finset.Subtype.fintype.{0} Nat P))
                    (fun (a b : Erdos390.Full.PaperHeadSimplex.Tag P) =>
                      @Option.instDecidableEq.{0}
                        (@Subtype.{1} Nat fun (p : Nat) =>
                          @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                            (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                        (fun
                            (a b :
                              @Subtype.{1} Nat fun (p : Nat) =>
                                @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                  (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P
                                  p) =>
                          @Subtype.instDecidableEq.{1} Nat
                            (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                              (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P)
                            instDecidableEqNat a b)
                        a b)
                    (Fin.fintype
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                        (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                    (instDecidableEqFin
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                        (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                    Bsource))
                (Erdos390.WholePaper.upperTailLength c
                  (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P)
                    (@instFintypeOption.{0}
                      (@Subtype.{1} Nat fun (p : Nat) =>
                        @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                          (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                      (@Finset.Subtype.fintype.{0} Nat P))
                    (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P)
                      (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M)
                      (@instFintypeOption.{0}
                        (@Subtype.{1} Nat fun (p : Nat) =>
                          @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                            (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                        (@Finset.Subtype.fintype.{0} Nat P))
                      (fun (a b : Erdos390.Full.PaperHeadSimplex.Tag P) =>
                        @Option.instDecidableEq.{0}
                          (@Subtype.{1} Nat fun (p : Nat) =>
                            @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                              (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                          (fun
                              (a b :
                                @Subtype.{1} Nat fun (p : Nat) =>
                                  @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                    (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat))
                                    P p) =>
                            @Subtype.instDecidableEq.{1} Nat
                              (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P)
                              instDecidableEqNat a b)
                          a b)
                      (Fin.fintype
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                          (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                      (instDecidableEqFin
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                          (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                      Bsource))))
              R depth)
            certificate))
        (@Erdos390.WholePaper.BankPaperRealization.prechargeBaseStateProduct
          (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P)
            (@instFintypeOption.{0}
              (@Subtype.{1} Nat fun (p : Nat) =>
                @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                  (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
              (@Finset.Subtype.fintype.{0} Nat P))
            (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P)
              (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M)
              (@instFintypeOption.{0}
                (@Subtype.{1} Nat fun (p : Nat) =>
                  @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                    (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                (@Finset.Subtype.fintype.{0} Nat P))
              (fun (a b : Erdos390.Full.PaperHeadSimplex.Tag P) =>
                @Option.instDecidableEq.{0}
                  (@Subtype.{1} Nat fun (p : Nat) =>
                    @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                  (fun
                      (a b :
                        @Subtype.{1} Nat fun (p : Nat) =>
                          @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                            (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p) =>
                    @Subtype.instDecidableEq.{1} Nat
                      (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                        (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P)
                      instDecidableEqNat a b)
                  a b)
              (Fin.fintype
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                  (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
              (instDecidableEqFin
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                  (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
              Bsource))
          (Erdos390.WholePaper.upperEndpoint
            (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P)
              (@instFintypeOption.{0}
                (@Subtype.{1} Nat fun (p : Nat) =>
                  @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                    (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                (@Finset.Subtype.fintype.{0} Nat P))
              (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P)
                (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M)
                (@instFintypeOption.{0}
                  (@Subtype.{1} Nat fun (p : Nat) =>
                    @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                  (@Finset.Subtype.fintype.{0} Nat P))
                (fun (a b : Erdos390.Full.PaperHeadSimplex.Tag P) =>
                  @Option.instDecidableEq.{0}
                    (@Subtype.{1} Nat fun (p : Nat) =>
                      @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                        (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                    (fun
                        (a b :
                          @Subtype.{1} Nat fun (p : Nat) =>
                            @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                              (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P
                              p) =>
                      @Subtype.instDecidableEq.{1} Nat
                        (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                          (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P)
                        instDecidableEqNat a b)
                    a b)
                (Fin.fintype
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                    (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                (instDecidableEqFin
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                    (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                Bsource))
            (Erdos390.WholePaper.upperTailLength c
              (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P)
                (@instFintypeOption.{0}
                  (@Subtype.{1} Nat fun (p : Nat) =>
                    @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                  (@Finset.Subtype.fintype.{0} Nat P))
                (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P)
                  (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M)
                  (@instFintypeOption.{0}
                    (@Subtype.{1} Nat fun (p : Nat) =>
                      @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                        (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                    (@Finset.Subtype.fintype.{0} Nat P))
                  (fun (a b : Erdos390.Full.PaperHeadSimplex.Tag P) =>
                    @Option.instDecidableEq.{0}
                      (@Subtype.{1} Nat fun (p : Nat) =>
                        @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                          (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                      (fun
                          (a b :
                            @Subtype.{1} Nat fun (p : Nat) =>
                              @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P
                                p) =>
                        @Subtype.instDecidableEq.{1} Nat
                          (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                            (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P)
                          instDecidableEqNat a b)
                      a b)
                  (Fin.fintype
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                      (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                  (instDecidableEqFin
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                      (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                  Bsource))))
          R))
      (Erdos390.WholePaper.centralTailProduct
        (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P)
          (@instFintypeOption.{0}
            (@Subtype.{1} Nat fun (p : Nat) =>
              @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
            (@Finset.Subtype.fintype.{0} Nat P))
          (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P)
            (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M)
            (@instFintypeOption.{0}
              (@Subtype.{1} Nat fun (p : Nat) =>
                @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                  (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
              (@Finset.Subtype.fintype.{0} Nat P))
            (fun (a b : Erdos390.Full.PaperHeadSimplex.Tag P) =>
              @Option.instDecidableEq.{0}
                (@Subtype.{1} Nat fun (p : Nat) =>
                  @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                    (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                (fun
                    (a b :
                      @Subtype.{1} Nat fun (p : Nat) =>
                        @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                          (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p) =>
                  @Subtype.instDecidableEq.{1} Nat
                    (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P)
                    instDecidableEqNat a b)
                a b)
            (Fin.fintype
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
            (instDecidableEqFin
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
            (@Erdos390.WholePaper.BankPaperRealization.BankPaperCanonicalSectionNinePostHeightBridgeInputsAt.postHeightBridge
              delta eta M P Bsource c depth K0 R certificate I deltaStar hdelta J)))
        (Erdos390.WholePaper.upperTailLength c
          (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P)
            (@instFintypeOption.{0}
              (@Subtype.{1} Nat fun (p : Nat) =>
                @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                  (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
              (@Finset.Subtype.fintype.{0} Nat P))
            (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P)
              (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M)
              (@instFintypeOption.{0}
                (@Subtype.{1} Nat fun (p : Nat) =>
                  @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                    (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                (@Finset.Subtype.fintype.{0} Nat P))
              (fun (a b : Erdos390.Full.PaperHeadSimplex.Tag P) =>
                @Option.instDecidableEq.{0}
                  (@Subtype.{1} Nat fun (p : Nat) =>
                    @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                  (fun
                      (a b :
                        @Subtype.{1} Nat fun (p : Nat) =>
                          @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                            (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p) =>
                    @Subtype.instDecidableEq.{1} Nat
                      (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                        (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P)
                      instDecidableEqNat a b)
                  a b)
              (Fin.fintype
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                  (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
              (instDecidableEqFin
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                  (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
              (@Erdos390.WholePaper.BankPaperRealization.BankPaperCanonicalSectionNinePostHeightBridgeInputsAt.postHeightBridge
                delta eta M P Bsource c depth K0 R certificate I deltaStar hdelta J))))))
  (hcharge :
    @Dvd.dvd.{0} Nat Nat.instDvd
      (@Erdos390.WholePaper.BankPaperRealization.selectorTailCharge
        (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P)
          (@instFintypeOption.{0}
            (@Subtype.{1} Nat fun (p : Nat) =>
              @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
            (@Finset.Subtype.fintype.{0} Nat P))
          (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P)
            (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M)
            (@instFintypeOption.{0}
              (@Subtype.{1} Nat fun (p : Nat) =>
                @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                  (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
              (@Finset.Subtype.fintype.{0} Nat P))
            (fun (a b : Erdos390.Full.PaperHeadSimplex.Tag P) =>
              @Option.instDecidableEq.{0}
                (@Subtype.{1} Nat fun (p : Nat) =>
                  @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                    (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                (fun
                    (a b :
                      @Subtype.{1} Nat fun (p : Nat) =>
                        @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                          (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p) =>
                  @Subtype.instDecidableEq.{1} Nat
                    (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P)
                    instDecidableEqNat a b)
                a b)
            (Fin.fintype
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
            (instDecidableEqFin
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
            Bsource))
        (Erdos390.WholePaper.upperEndpoint
          (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P)
            (@instFintypeOption.{0}
              (@Subtype.{1} Nat fun (p : Nat) =>
                @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                  (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
              (@Finset.Subtype.fintype.{0} Nat P))
            (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P)
              (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M)
              (@instFintypeOption.{0}
                (@Subtype.{1} Nat fun (p : Nat) =>
                  @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                    (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                (@Finset.Subtype.fintype.{0} Nat P))
              (fun (a b : Erdos390.Full.PaperHeadSimplex.Tag P) =>
                @Option.instDecidableEq.{0}
                  (@Subtype.{1} Nat fun (p : Nat) =>
                    @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                  (fun
                      (a b :
                        @Subtype.{1} Nat fun (p : Nat) =>
                          @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                            (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p) =>
                    @Subtype.instDecidableEq.{1} Nat
                      (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                        (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P)
                      instDecidableEqNat a b)
                  a b)
              (Fin.fintype
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                  (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
              (instDecidableEqFin
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                  (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
              Bsource))
          (Erdos390.WholePaper.upperTailLength c
            (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P)
              (@instFintypeOption.{0}
                (@Subtype.{1} Nat fun (p : Nat) =>
                  @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                    (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                (@Finset.Subtype.fintype.{0} Nat P))
              (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P)
                (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M)
                (@instFintypeOption.{0}
                  (@Subtype.{1} Nat fun (p : Nat) =>
                    @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                  (@Finset.Subtype.fintype.{0} Nat P))
                (fun (a b : Erdos390.Full.PaperHeadSimplex.Tag P) =>
                  @Option.instDecidableEq.{0}
                    (@Subtype.{1} Nat fun (p : Nat) =>
                      @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                        (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                    (fun
                        (a b :
                          @Subtype.{1} Nat fun (p : Nat) =>
                            @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                              (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P
                              p) =>
                      @Subtype.instDecidableEq.{1} Nat
                        (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                          (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P)
                        instDecidableEqNat a b)
                    a b)
                (Fin.fintype
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                    (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                (instDecidableEqFin
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                    (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                Bsource))))
        R
        (@Erdos390.WholePaper.BankPaperRealization.paperFixedExceptionalFactors
          (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P)
            (@instFintypeOption.{0}
              (@Subtype.{1} Nat fun (p : Nat) =>
                @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                  (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
              (@Finset.Subtype.fintype.{0} Nat P))
            (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P)
              (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M)
              (@instFintypeOption.{0}
                (@Subtype.{1} Nat fun (p : Nat) =>
                  @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                    (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                (@Finset.Subtype.fintype.{0} Nat P))
              (fun (a b : Erdos390.Full.PaperHeadSimplex.Tag P) =>
                @Option.instDecidableEq.{0}
                  (@Subtype.{1} Nat fun (p : Nat) =>
                    @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                  (fun
                      (a b :
                        @Subtype.{1} Nat fun (p : Nat) =>
                          @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                            (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p) =>
                    @Subtype.instDecidableEq.{1} Nat
                      (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                        (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P)
                      instDecidableEqNat a b)
                  a b)
              (Fin.fintype
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                  (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
              (instDecidableEqFin
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                  (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
              Bsource))
          (Erdos390.WholePaper.upperTailLength c
            (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P)
              (@instFintypeOption.{0}
                (@Subtype.{1} Nat fun (p : Nat) =>
                  @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                    (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                (@Finset.Subtype.fintype.{0} Nat P))
              (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P)
                (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M)
                (@instFintypeOption.{0}
                  (@Subtype.{1} Nat fun (p : Nat) =>
                    @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                  (@Finset.Subtype.fintype.{0} Nat P))
                (fun (a b : Erdos390.Full.PaperHeadSimplex.Tag P) =>
                  @Option.instDecidableEq.{0}
                    (@Subtype.{1} Nat fun (p : Nat) =>
                      @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                        (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                    (fun
                        (a b :
                          @Subtype.{1} Nat fun (p : Nat) =>
                            @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                              (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P
                              p) =>
                      @Subtype.instDecidableEq.{1} Nat
                        (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                          (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P)
                        instDecidableEqNat a b)
                    a b)
                (Fin.fintype
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                    (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                (instDecidableEqFin
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                    (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                Bsource)))
          R deltaStar))
      (@Erdos390.WholePaper.GuardedCentralAnchorCertificate.prechargedTailTarget c depth
        (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P)
          (@instFintypeOption.{0}
            (@Subtype.{1} Nat fun (p : Nat) =>
              @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
            (@Finset.Subtype.fintype.{0} Nat P))
          (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P)
            (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M)
            (@instFintypeOption.{0}
              (@Subtype.{1} Nat fun (p : Nat) =>
                @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                  (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
              (@Finset.Subtype.fintype.{0} Nat P))
            (fun (a b : Erdos390.Full.PaperHeadSimplex.Tag P) =>
              @Option.instDecidableEq.{0}
                (@Subtype.{1} Nat fun (p : Nat) =>
                  @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                    (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                (fun
                    (a b :
                      @Subtype.{1} Nat fun (p : Nat) =>
                        @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                          (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p) =>
                  @Subtype.instDecidableEq.{1} Nat
                    (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P)
                    instDecidableEqNat a b)
                a b)
            (Fin.fintype
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
            (instDecidableEqFin
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
            Bsource))
        (@Erdos390.WholePaper.BankPaperRealization.anchorGuardLeftCore
          (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P)
            (@instFintypeOption.{0}
              (@Subtype.{1} Nat fun (p : Nat) =>
                @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                  (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
              (@Finset.Subtype.fintype.{0} Nat P))
            (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P)
              (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M)
              (@instFintypeOption.{0}
                (@Subtype.{1} Nat fun (p : Nat) =>
                  @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                    (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                (@Finset.Subtype.fintype.{0} Nat P))
              (fun (a b : Erdos390.Full.PaperHeadSimplex.Tag P) =>
                @Option.instDecidableEq.{0}
                  (@Subtype.{1} Nat fun (p : Nat) =>
                    @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                  (fun
                      (a b :
                        @Subtype.{1} Nat fun (p : Nat) =>
                          @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                            (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p) =>
                    @Subtype.instDecidableEq.{1} Nat
                      (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                        (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P)
                      instDecidableEqNat a b)
                  a b)
              (Fin.fintype
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                  (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
              (instDecidableEqFin
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                  (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
              Bsource))
          (Erdos390.WholePaper.upperEndpoint
            (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P)
              (@instFintypeOption.{0}
                (@Subtype.{1} Nat fun (p : Nat) =>
                  @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                    (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                (@Finset.Subtype.fintype.{0} Nat P))
              (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P)
                (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M)
                (@instFintypeOption.{0}
                  (@Subtype.{1} Nat fun (p : Nat) =>
                    @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                  (@Finset.Subtype.fintype.{0} Nat P))
                (fun (a b : Erdos390.Full.PaperHeadSimplex.Tag P) =>
                  @Option.instDecidableEq.{0}
                    (@Subtype.{1} Nat fun (p : Nat) =>
                      @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                        (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                    (fun
                        (a b :
                          @Subtype.{1} Nat fun (p : Nat) =>
                            @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                              (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P
                              p) =>
                      @Subtype.instDecidableEq.{1} Nat
                        (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                          (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P)
                        instDecidableEqNat a b)
                    a b)
                (Fin.fintype
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                    (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                (instDecidableEqFin
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                    (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                Bsource))
            (Erdos390.WholePaper.upperTailLength c
              (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P)
                (@instFintypeOption.{0}
                  (@Subtype.{1} Nat fun (p : Nat) =>
                    @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                  (@Finset.Subtype.fintype.{0} Nat P))
                (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P)
                  (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M)
                  (@instFintypeOption.{0}
                    (@Subtype.{1} Nat fun (p : Nat) =>
                      @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                        (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                    (@Finset.Subtype.fintype.{0} Nat P))
                  (fun (a b : Erdos390.Full.PaperHeadSimplex.Tag P) =>
                    @Option.instDecidableEq.{0}
                      (@Subtype.{1} Nat fun (p : Nat) =>
                        @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                          (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                      (fun
                          (a b :
                            @Subtype.{1} Nat fun (p : Nat) =>
                              @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P
                                p) =>
                        @Subtype.instDecidableEq.{1} Nat
                          (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                            (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P)
                          instDecidableEqNat a b)
                      a b)
                  (Fin.fintype
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                      (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                  (instDecidableEqFin
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                      (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                  Bsource))))
          R)
        (@Erdos390.WholePaper.BankPaperRealization.anchorGuardRightCore
          (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P)
            (@instFintypeOption.{0}
              (@Subtype.{1} Nat fun (p : Nat) =>
                @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                  (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
              (@Finset.Subtype.fintype.{0} Nat P))
            (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P)
              (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M)
              (@instFintypeOption.{0}
                (@Subtype.{1} Nat fun (p : Nat) =>
                  @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                    (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                (@Finset.Subtype.fintype.{0} Nat P))
              (fun (a b : Erdos390.Full.PaperHeadSimplex.Tag P) =>
                @Option.instDecidableEq.{0}
                  (@Subtype.{1} Nat fun (p : Nat) =>
                    @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                  (fun
                      (a b :
                        @Subtype.{1} Nat fun (p : Nat) =>
                          @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                            (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p) =>
                    @Subtype.instDecidableEq.{1} Nat
                      (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                        (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P)
                      instDecidableEqNat a b)
                  a b)
              (Fin.fintype
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                  (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
              (instDecidableEqFin
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                  (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
              Bsource))
          (Erdos390.WholePaper.upperEndpoint
            (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P)
              (@instFintypeOption.{0}
                (@Subtype.{1} Nat fun (p : Nat) =>
                  @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                    (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                (@Finset.Subtype.fintype.{0} Nat P))
              (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P)
                (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M)
                (@instFintypeOption.{0}
                  (@Subtype.{1} Nat fun (p : Nat) =>
                    @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                  (@Finset.Subtype.fintype.{0} Nat P))
                (fun (a b : Erdos390.Full.PaperHeadSimplex.Tag P) =>
                  @Option.instDecidableEq.{0}
                    (@Subtype.{1} Nat fun (p : Nat) =>
                      @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                        (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                    (fun
                        (a b :
                          @Subtype.{1} Nat fun (p : Nat) =>
                            @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                              (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P
                              p) =>
                      @Subtype.instDecidableEq.{1} Nat
                        (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                          (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P)
                        instDecidableEqNat a b)
                    a b)
                (Fin.fintype
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                    (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                (instDecidableEqFin
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                    (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                Bsource))
            (Erdos390.WholePaper.upperTailLength c
              (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P)
                (@instFintypeOption.{0}
                  (@Subtype.{1} Nat fun (p : Nat) =>
                    @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                  (@Finset.Subtype.fintype.{0} Nat P))
                (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P)
                  (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M)
                  (@instFintypeOption.{0}
                    (@Subtype.{1} Nat fun (p : Nat) =>
                      @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                        (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                    (@Finset.Subtype.fintype.{0} Nat P))
                  (fun (a b : Erdos390.Full.PaperHeadSimplex.Tag P) =>
                    @Option.instDecidableEq.{0}
                      (@Subtype.{1} Nat fun (p : Nat) =>
                        @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                          (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                      (fun
                          (a b :
                            @Subtype.{1} Nat fun (p : Nat) =>
                              @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P
                                p) =>
                        @Subtype.instDecidableEq.{1} Nat
                          (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                            (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P)
                          instDecidableEqNat a b)
                      a b)
                  (Fin.fintype
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                      (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                  (instDecidableEqFin
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                      (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                  Bsource))))
          R)
        (@Erdos390.WholePaper.BankPaperRealization.centralChangedMarkers
          (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P)
            (@instFintypeOption.{0}
              (@Subtype.{1} Nat fun (p : Nat) =>
                @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                  (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
              (@Finset.Subtype.fintype.{0} Nat P))
            (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P)
              (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M)
              (@instFintypeOption.{0}
                (@Subtype.{1} Nat fun (p : Nat) =>
                  @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                    (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                (@Finset.Subtype.fintype.{0} Nat P))
              (fun (a b : Erdos390.Full.PaperHeadSimplex.Tag P) =>
                @Option.instDecidableEq.{0}
                  (@Subtype.{1} Nat fun (p : Nat) =>
                    @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                  (fun
                      (a b :
                        @Subtype.{1} Nat fun (p : Nat) =>
                          @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                            (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p) =>
                    @Subtype.instDecidableEq.{1} Nat
                      (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                        (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P)
                      instDecidableEqNat a b)
                  a b)
              (Fin.fintype
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                  (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
              (instDecidableEqFin
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                  (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
              Bsource))
          (Erdos390.WholePaper.upperEndpoint
            (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P)
              (@instFintypeOption.{0}
                (@Subtype.{1} Nat fun (p : Nat) =>
                  @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                    (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                (@Finset.Subtype.fintype.{0} Nat P))
              (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P)
                (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M)
                (@instFintypeOption.{0}
                  (@Subtype.{1} Nat fun (p : Nat) =>
                    @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                  (@Finset.Subtype.fintype.{0} Nat P))
                (fun (a b : Erdos390.Full.PaperHeadSimplex.Tag P) =>
                  @Option.instDecidableEq.{0}
                    (@Subtype.{1} Nat fun (p : Nat) =>
                      @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                        (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                    (fun
                        (a b :
                          @Subtype.{1} Nat fun (p : Nat) =>
                            @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                              (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P
                              p) =>
                      @Subtype.instDecidableEq.{1} Nat
                        (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                          (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P)
                        instDecidableEqNat a b)
                    a b)
                (Fin.fintype
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                    (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                (instDecidableEqFin
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                    (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                Bsource))
            (Erdos390.WholePaper.upperTailLength c
              (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P)
                (@instFintypeOption.{0}
                  (@Subtype.{1} Nat fun (p : Nat) =>
                    @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                  (@Finset.Subtype.fintype.{0} Nat P))
                (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P)
                  (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M)
                  (@instFintypeOption.{0}
                    (@Subtype.{1} Nat fun (p : Nat) =>
                      @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                        (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                    (@Finset.Subtype.fintype.{0} Nat P))
                  (fun (a b : Erdos390.Full.PaperHeadSimplex.Tag P) =>
                    @Option.instDecidableEq.{0}
                      (@Subtype.{1} Nat fun (p : Nat) =>
                        @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                          (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                      (fun
                          (a b :
                            @Subtype.{1} Nat fun (p : Nat) =>
                              @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P
                                p) =>
                        @Subtype.instDecidableEq.{1} Nat
                          (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                            (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P)
                          instDecidableEqNat a b)
                      a b)
                  (Fin.fintype
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                      (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                  (instDecidableEqFin
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                      (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                  Bsource))))
          R depth)
        certificate))
  (hsourceMargin :
    @LE.le.{0} Real Real.instLE sourceMarginFloor
      (@Erdos390.Full.PaperGuardCensus.BarycentricTarget.cellMassMargin.{0} (Erdos390.Full.PaperHeadSimplex.Tag P)
        (@instFintypeOption.{0}
          (@Subtype.{1} Nat fun (p : Nat) =>
            @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
              (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
          (@Finset.Subtype.fintype.{0} Nat P))
        (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P)
          (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M)
          (@instFintypeOption.{0}
            (@Subtype.{1} Nat fun (p : Nat) =>
              @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
            (@Finset.Subtype.fintype.{0} Nat P))
          (fun (a b : Erdos390.Full.PaperHeadSimplex.Tag P) =>
            @Option.instDecidableEq.{0}
              (@Subtype.{1} Nat fun (p : Nat) =>
                @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                  (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
              (fun
                  (a b :
                    @Subtype.{1} Nat fun (p : Nat) =>
                      @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                        (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p) =>
                @Subtype.instDecidableEq.{1} Nat
                  (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                    (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P)
                  instDecidableEqNat a b)
              a b)
          (Fin.fintype
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
          (instDecidableEqFin
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
          Bsource)
        (@Erdos390.WholePaper.BankPaperRealization.BankPaperCanonicalSectionNinePostHeightBridgeInputsAt.Tsource delta
          eta M P Bsource c depth K0 R certificate I deltaStar hdelta J)))
  (hheadMargin :
    @LE.le.{0} Real Real.instLE headMarginFloor
      (@Erdos390.WholePaper.BankPaperCanonicalSectionNinePostHeightBaselineTargetInputs.headMargin.{0} P
        (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M)
        (Fin.fintype
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
        (instDecidableEqFin
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
        Bsource I
        (@Erdos390.WholePaper.BankPaperRealization.bankPaperCanonicalSectionNinePostHeightRoundedQ0.{0} P
          (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M)
          (Fin.fintype
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
          (instDecidableEqFin
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) K0
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          Bsource c depth R certificate deltaStar
          (@Erdos390.WholePaper.BankPaperRealization.BankPaperCanonicalSectionNinePostHeightBridgeInputsAt.betaProt
            delta eta M P Bsource c depth K0 R certificate I deltaStar hdelta J)
          (@Erdos390.WholePaper.BankPaperRealization.bankPaperCanonicalPostHfitBalancedAlpha.{0, 0}
            (Erdos390.Full.PaperHeadSimplex.Tag P) (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M)
            (@instFintypeOption.{0}
              (@Subtype.{1} Nat fun (p : Nat) =>
                @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                  (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
              (@Finset.Subtype.fintype.{0} Nat P))
            (fun (a b : Erdos390.Full.PaperHeadSimplex.Tag P) =>
              @Option.instDecidableEq.{0}
                (@Subtype.{1} Nat fun (p : Nat) =>
                  @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                    (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                (fun
                    (a b :
                      @Subtype.{1} Nat fun (p : Nat) =>
                        @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                          (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p) =>
                  @Subtype.instDecidableEq.{1} Nat
                    (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P)
                    instDecidableEqNat a b)
                a b)
            (Fin.fintype
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
            (instDecidableEqFin
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
            Bsource c K0
            (@Erdos390.WholePaper.BankPaperRealization.BankPaperCanonicalSectionNinePostHeightBridgeInputsAt.betaProt
              delta eta M P Bsource c depth K0 R certificate I deltaStar hdelta J)
            (@Erdos390.WholePaper.BankPaperRealization.BankPaperCanonicalSectionNinePostHeightBridgeInputsAt.betaAct
              delta eta M P Bsource c depth K0 R certificate I deltaStar hdelta J))
          (@Erdos390.WholePaper.BankPaperRealization.BankPaperCanonicalSectionNinePostHeightBridgeInputsAt.qTilde delta
            eta M P Bsource c depth K0 R certificate I deltaStar hdelta J))
        (@Erdos390.WholePaper.BankPaperRealization.bankPaperCanonicalSectionNinePostHeightA0.{0} P
          (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M)
          (Fin.fintype
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
          (instDecidableEqFin
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) K0
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          Bsource c depth R certificate
          (@Erdos390.WholePaper.BankPaperRealization.BankPaperCanonicalSectionNinePostHeightBridgeInputsAt.Tsource delta
            eta M P Bsource c depth K0 R certificate I deltaStar hdelta J)
          deltaStar
          (@Erdos390.WholePaper.BankPaperRealization.BankPaperCanonicalSectionNinePostHeightBridgeInputsAt.betaProt
            delta eta M P Bsource c depth K0 R certificate I deltaStar hdelta J)
          (@Erdos390.WholePaper.BankPaperRealization.bankPaperCanonicalPostHfitBalancedAlpha.{0, 0}
            (Erdos390.Full.PaperHeadSimplex.Tag P) (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M)
            (@instFintypeOption.{0}
              (@Subtype.{1} Nat fun (p : Nat) =>
                @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                  (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
              (@Finset.Subtype.fintype.{0} Nat P))
            (fun (a b : Erdos390.Full.PaperHeadSimplex.Tag P) =>
              @Option.instDecidableEq.{0}
                (@Subtype.{1} Nat fun (p : Nat) =>
                  @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                    (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                (fun
                    (a b :
                      @Subtype.{1} Nat fun (p : Nat) =>
                        @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                          (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p) =>
                  @Subtype.instDecidableEq.{1} Nat
                    (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P)
                    instDecidableEqNat a b)
                a b)
            (Fin.fintype
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
            (instDecidableEqFin
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
            Bsource c K0
            (@Erdos390.WholePaper.BankPaperRealization.BankPaperCanonicalSectionNinePostHeightBridgeInputsAt.betaProt
              delta eta M P Bsource c depth K0 R certificate I deltaStar hdelta J)
            (@Erdos390.WholePaper.BankPaperRealization.BankPaperCanonicalSectionNinePostHeightBridgeInputsAt.betaAct
              delta eta M P Bsource c depth K0 R certificate I deltaStar hdelta J))
          (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
            (@Erdos390.WholePaper.BankPaperRealization.BankPaperCanonicalSectionNinePostHeightBridgeInputsAt.betaProt
              delta eta M P Bsource c depth K0 R certificate I deltaStar hdelta J)
            (@Erdos390.WholePaper.BankPaperRealization.BankPaperCanonicalSectionNinePostHeightBridgeInputsAt.betaAct
              delta eta M P Bsource c depth K0 R certificate I deltaStar hdelta J))
          (@Erdos390.WholePaper.BankPaperRealization.BankPaperCanonicalSectionNinePostHeightBridgeInputsAt.qTilde delta
            eta M P Bsource c depth K0 R certificate I deltaStar hdelta J))
        (@Erdos390.WholePaper.BankPaperRealization.BankPaperCanonicalSectionNinePostHeightBridgeInputsAt.d delta eta M P
          Bsource c depth K0 R certificate I deltaStar hdelta J)
        (@Erdos390.WholePaper.BankPaperRealization.BankPaperCanonicalSectionNinePostHeightBridgeInputsAt.exponent delta
          eta M P Bsource c depth K0 R certificate I deltaStar hdelta J)
        (@Erdos390.WholePaper.BankPaperRealization.bankPaperCanonicalSectionNinePostHeightActiveHeadTarget.{0} P
          (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M)
          (Fin.fintype
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
          (instDecidableEqFin
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
          Bsource c depth R certificate deltaStar)
        (@Erdos390.WholePaper.BankPaperRealization.BankPaperCanonicalSectionNinePostHeightBridgeInputsAt.targetInputs
          delta eta M P Bsource c depth K0 R certificate I deltaStar hdelta J)))
  (hphysicalEta :
    @LE.le.{0} Real Real.instLE physicalEtaFloor
      (@Erdos390.WholePaper.BankPaperCanonicalSectionNinePostHeightBaselineTargetInputs.physicalEta.{0} P
        (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M)
        (Fin.fintype
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
        (instDecidableEqFin
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
        Bsource I
        (@Erdos390.WholePaper.BankPaperRealization.bankPaperCanonicalSectionNinePostHeightRoundedQ0.{0} P
          (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M)
          (Fin.fintype
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
          (instDecidableEqFin
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) K0
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          Bsource c depth R certificate deltaStar
          (@Erdos390.WholePaper.BankPaperRealization.BankPaperCanonicalSectionNinePostHeightBridgeInputsAt.betaProt
            delta eta M P Bsource c depth K0 R certificate I deltaStar hdelta J)
          (@Erdos390.WholePaper.BankPaperRealization.bankPaperCanonicalPostHfitBalancedAlpha.{0, 0}
            (Erdos390.Full.PaperHeadSimplex.Tag P) (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M)
            (@instFintypeOption.{0}
              (@Subtype.{1} Nat fun (p : Nat) =>
                @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                  (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
              (@Finset.Subtype.fintype.{0} Nat P))
            (fun (a b : Erdos390.Full.PaperHeadSimplex.Tag P) =>
              @Option.instDecidableEq.{0}
                (@Subtype.{1} Nat fun (p : Nat) =>
                  @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                    (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                (fun
                    (a b :
                      @Subtype.{1} Nat fun (p : Nat) =>
                        @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                          (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p) =>
                  @Subtype.instDecidableEq.{1} Nat
                    (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P)
                    instDecidableEqNat a b)
                a b)
            (Fin.fintype
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
            (instDecidableEqFin
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
            Bsource c K0
            (@Erdos390.WholePaper.BankPaperRealization.BankPaperCanonicalSectionNinePostHeightBridgeInputsAt.betaProt
              delta eta M P Bsource c depth K0 R certificate I deltaStar hdelta J)
            (@Erdos390.WholePaper.BankPaperRealization.BankPaperCanonicalSectionNinePostHeightBridgeInputsAt.betaAct
              delta eta M P Bsource c depth K0 R certificate I deltaStar hdelta J))
          (@Erdos390.WholePaper.BankPaperRealization.BankPaperCanonicalSectionNinePostHeightBridgeInputsAt.qTilde delta
            eta M P Bsource c depth K0 R certificate I deltaStar hdelta J))
        (@Erdos390.WholePaper.BankPaperRealization.bankPaperCanonicalSectionNinePostHeightA0.{0} P
          (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M)
          (Fin.fintype
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
          (instDecidableEqFin
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) K0
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          Bsource c depth R certificate
          (@Erdos390.WholePaper.BankPaperRealization.BankPaperCanonicalSectionNinePostHeightBridgeInputsAt.Tsource delta
            eta M P Bsource c depth K0 R certificate I deltaStar hdelta J)
          deltaStar
          (@Erdos390.WholePaper.BankPaperRealization.BankPaperCanonicalSectionNinePostHeightBridgeInputsAt.betaProt
            delta eta M P Bsource c depth K0 R certificate I deltaStar hdelta J)
          (@Erdos390.WholePaper.BankPaperRealization.bankPaperCanonicalPostHfitBalancedAlpha.{0, 0}
            (Erdos390.Full.PaperHeadSimplex.Tag P) (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M)
            (@instFintypeOption.{0}
              (@Subtype.{1} Nat fun (p : Nat) =>
                @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                  (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
              (@Finset.Subtype.fintype.{0} Nat P))
            (fun (a b : Erdos390.Full.PaperHeadSimplex.Tag P) =>
              @Option.instDecidableEq.{0}
                (@Subtype.{1} Nat fun (p : Nat) =>
                  @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                    (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                (fun
                    (a b :
                      @Subtype.{1} Nat fun (p : Nat) =>
                        @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                          (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p) =>
                  @Subtype.instDecidableEq.{1} Nat
                    (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P)
                    instDecidableEqNat a b)
                a b)
            (Fin.fintype
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
            (instDecidableEqFin
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
            Bsource c K0
            (@Erdos390.WholePaper.BankPaperRealization.BankPaperCanonicalSectionNinePostHeightBridgeInputsAt.betaProt
              delta eta M P Bsource c depth K0 R certificate I deltaStar hdelta J)
            (@Erdos390.WholePaper.BankPaperRealization.BankPaperCanonicalSectionNinePostHeightBridgeInputsAt.betaAct
              delta eta M P Bsource c depth K0 R certificate I deltaStar hdelta J))
          (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
            (@Erdos390.WholePaper.BankPaperRealization.BankPaperCanonicalSectionNinePostHeightBridgeInputsAt.betaProt
              delta eta M P Bsource c depth K0 R certificate I deltaStar hdelta J)
            (@Erdos390.WholePaper.BankPaperRealization.BankPaperCanonicalSectionNinePostHeightBridgeInputsAt.betaAct
              delta eta M P Bsource c depth K0 R certificate I deltaStar hdelta J))
          (@Erdos390.WholePaper.BankPaperRealization.BankPaperCanonicalSectionNinePostHeightBridgeInputsAt.qTilde delta
            eta M P Bsource c depth K0 R certificate I deltaStar hdelta J))
        (@Erdos390.WholePaper.BankPaperRealization.BankPaperCanonicalSectionNinePostHeightBridgeInputsAt.d delta eta M P
          Bsource c depth K0 R certificate I deltaStar hdelta J)
        (@Erdos390.WholePaper.BankPaperRealization.BankPaperCanonicalSectionNinePostHeightBridgeInputsAt.exponent delta
          eta M P Bsource c depth K0 R certificate I deltaStar hdelta J)
        (@Erdos390.WholePaper.BankPaperRealization.bankPaperCanonicalSectionNinePostHeightActiveHeadTarget.{0} P
          (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M)
          (Fin.fintype
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
          (instDecidableEqFin
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
          Bsource c depth R certificate deltaStar)
        (@Erdos390.WholePaper.BankPaperRealization.BankPaperCanonicalSectionNinePostHeightBridgeInputsAt.targetInputs
          delta eta M P Bsource c depth K0 R certificate I deltaStar hdelta J)))
  (hpostMargin :
    @LE.le.{0} Real Real.instLE postMarginFloor
      (@Erdos390.Full.PaperGuardCensus.BarycentricTarget.cellMassMargin.{0} (Erdos390.Full.PaperHeadSimplex.Tag P)
        (@instFintypeOption.{0}
          (@Subtype.{1} Nat fun (p : Nat) =>
            @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
              (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
          (@Finset.Subtype.fintype.{0} Nat P))
        (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P)
          (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M)
          (@instFintypeOption.{0}
            (@Subtype.{1} Nat fun (p : Nat) =>
              @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
            (@Finset.Subtype.fintype.{0} Nat P))
          (fun (a b : Erdos390.Full.PaperHeadSimplex.Tag P) =>
            @Option.instDecidableEq.{0}
              (@Subtype.{1} Nat fun (p : Nat) =>
                @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                  (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
              (fun
                  (a b :
                    @Subtype.{1} Nat fun (p : Nat) =>
                      @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                        (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p) =>
                @Subtype.instDecidableEq.{1} Nat
                  (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                    (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P)
                  instDecidableEqNat a b)
              a b)
          (Fin.fintype
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
          (instDecidableEqFin
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
          (@Erdos390.WholePaper.BankPaperRealization.BankPaperCanonicalSectionNinePostHeightBridgeInputsAt.postHeightBridge
            delta eta M P Bsource c depth K0 R certificate I deltaStar hdelta J))
        (@Erdos390.WholePaper.BankPaperRealization.BankPaperCanonicalSectionNinePostHeightBridgeInputsAt.postHeightTarget
          delta eta M P Bsource c depth K0 R certificate I deltaStar hdelta J)))
  (hqTildeFamily :
    @Eq.{1} Real
      (@Erdos390.WholePaper.BankPaperRealization.BankPaperCanonicalSectionNinePostHeightBridgeInputsAt.qTilde delta eta
        M P Bsource c depth K0 R certificate I deltaStar hdelta J)
      (qTilde
        (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P)
          (@instFintypeOption.{0}
            (@Subtype.{1} Nat fun (p : Nat) =>
              @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
            (@Finset.Subtype.fintype.{0} Nat P))
          (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P)
            (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M)
            (@instFintypeOption.{0}
              (@Subtype.{1} Nat fun (p : Nat) =>
                @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                  (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
              (@Finset.Subtype.fintype.{0} Nat P))
            (fun (a b : Erdos390.Full.PaperHeadSimplex.Tag P) =>
              @Option.instDecidableEq.{0}
                (@Subtype.{1} Nat fun (p : Nat) =>
                  @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                    (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                (fun
                    (a b :
                      @Subtype.{1} Nat fun (p : Nat) =>
                        @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                          (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p) =>
                  @Subtype.instDecidableEq.{1} Nat
                    (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P)
                    instDecidableEqNat a b)
                a b)
            (Fin.fintype
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
            (instDecidableEqFin
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
            Bsource))))
  (hmFrozen :
    @Eq.{1} Real
      (mFrozen
        (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P)
          (@instFintypeOption.{0}
            (@Subtype.{1} Nat fun (p : Nat) =>
              @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
            (@Finset.Subtype.fintype.{0} Nat P))
          (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P)
            (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M)
            (@instFintypeOption.{0}
              (@Subtype.{1} Nat fun (p : Nat) =>
                @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                  (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
              (@Finset.Subtype.fintype.{0} Nat P))
            (fun (a b : Erdos390.Full.PaperHeadSimplex.Tag P) =>
              @Option.instDecidableEq.{0}
                (@Subtype.{1} Nat fun (p : Nat) =>
                  @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                    (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                (fun
                    (a b :
                      @Subtype.{1} Nat fun (p : Nat) =>
                        @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                          (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p) =>
                  @Subtype.instDecidableEq.{1} Nat
                    (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P)
                    instDecidableEqNat a b)
                a b)
            (Fin.fintype
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
            (instDecidableEqFin
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
            Bsource)))
      (@Erdos390.WholePaper.BankPaperRealization.bankPaperCanonicalTopFrozenSmoothFrozenMass.{0} P
        (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M)
        (Fin.fintype
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
        (instDecidableEqFin
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
        (@Erdos390.WholePaper.BankPaperRealization.BankPaperCanonicalSectionNinePostHeightBridgeInputsAt.postHeightBridge
          delta eta M P Bsource c depth K0 R certificate I deltaStar hdelta J)
        c depth
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) K0
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        R certificate deltaStar
        (@Erdos390.WholePaper.BankPaperRealization.BankPaperCanonicalSectionNinePostHeightBridgeInputsAt.betaProt delta
          eta M P Bsource c depth K0 R certificate I deltaStar hdelta J)
        (@Erdos390.WholePaper.BankPaperRealization.BankPaperCanonicalSectionNinePostHeightBridgeInputsAt.alpha delta eta
          M P Bsource c depth K0 R certificate I deltaStar hdelta J)))
  (hfinalActiveMass :
    @Eq.{1} Real
      (@Erdos390.WholePaper.BankPaperRealization.BankPaperCanonicalSectionNinePostHeightBridgeInputsAt.qn delta eta M P
        Bsource c depth K0 R certificate I deltaStar hdelta J)
      (Erdos390.WholePaper.bankPaperCanonicalSmoothFinalActiveMassFamily mu logY Lambda0 mFrozen qTilde
        (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P)
          (@instFintypeOption.{0}
            (@Subtype.{1} Nat fun (p : Nat) =>
              @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
            (@Finset.Subtype.fintype.{0} Nat P))
          (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P)
            (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M)
            (@instFintypeOption.{0}
              (@Subtype.{1} Nat fun (p : Nat) =>
                @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                  (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
              (@Finset.Subtype.fintype.{0} Nat P))
            (fun (a b : Erdos390.Full.PaperHeadSimplex.Tag P) =>
              @Option.instDecidableEq.{0}
                (@Subtype.{1} Nat fun (p : Nat) =>
                  @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                    (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                (fun
                    (a b :
                      @Subtype.{1} Nat fun (p : Nat) =>
                        @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                          (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p) =>
                  @Subtype.instDecidableEq.{1} Nat
                    (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P)
                    instDecidableEqNat a b)
                a b)
            (Fin.fintype
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
            (instDecidableEqFin
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
            Bsource))))
  (hsourceResidual :
    @Erdos390.WholePaper.BankPaperRealization.BankPaperCanonicalTopFrozenRoundedSourceResidualInputsAt.{0} P
      (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M)
      (Fin.fintype
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (instDecidableEqFin
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@Erdos390.WholePaper.BankPaperRealization.BankPaperCanonicalSectionNinePostHeightBridgeInputsAt.postHeightBridge
        delta eta M P Bsource c depth K0 R certificate I deltaStar hdelta J)
      c depth
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) K0
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      R certificate
      (@Erdos390.WholePaper.BankPaperRealization.paperFixedExceptionalFactors
        (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P)
          (@instFintypeOption.{0}
            (@Subtype.{1} Nat fun (p : Nat) =>
              @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
            (@Finset.Subtype.fintype.{0} Nat P))
          (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P)
            (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M)
            (@instFintypeOption.{0}
              (@Subtype.{1} Nat fun (p : Nat) =>
                @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                  (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
              (@Finset.Subtype.fintype.{0} Nat P))
            (fun (a b : Erdos390.Full.PaperHeadSimplex.Tag P) =>
              @Option.instDecidableEq.{0}
                (@Subtype.{1} Nat fun (p : Nat) =>
                  @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                    (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                (fun
                    (a b :
                      @Subtype.{1} Nat fun (p : Nat) =>
                        @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                          (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p) =>
                  @Subtype.instDecidableEq.{1} Nat
                    (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P)
                    instDecidableEqNat a b)
                a b)
            (Fin.fintype
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
            (instDecidableEqFin
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
            Bsource))
        (Erdos390.WholePaper.upperTailLength c
          (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P)
            (@instFintypeOption.{0}
              (@Subtype.{1} Nat fun (p : Nat) =>
                @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                  (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
              (@Finset.Subtype.fintype.{0} Nat P))
            (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P)
              (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M)
              (@instFintypeOption.{0}
                (@Subtype.{1} Nat fun (p : Nat) =>
                  @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                    (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                (@Finset.Subtype.fintype.{0} Nat P))
              (fun (a b : Erdos390.Full.PaperHeadSimplex.Tag P) =>
                @Option.instDecidableEq.{0}
                  (@Subtype.{1} Nat fun (p : Nat) =>
                    @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                  (fun
                      (a b :
                        @Subtype.{1} Nat fun (p : Nat) =>
                          @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                            (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p) =>
                    @Subtype.instDecidableEq.{1} Nat
                      (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                        (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P)
                      instDecidableEqNat a b)
                  a b)
              (Fin.fintype
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                  (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
              (instDecidableEqFin
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                  (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
              Bsource)))
        R deltaStar)
      (@Erdos390.WholePaper.BankPaperRealization.BankPaperCanonicalSectionNinePostHeightBridgeInputsAt.Tsource delta eta
        M P Bsource c depth K0 R certificate I deltaStar hdelta J)
      deltaStar
      (@Erdos390.WholePaper.BankPaperRealization.BankPaperCanonicalSectionNinePostHeightBridgeInputsAt.betaProt delta
        eta M P Bsource c depth K0 R certificate I deltaStar hdelta J)
      (@Erdos390.WholePaper.BankPaperRealization.BankPaperCanonicalSectionNinePostHeightBridgeInputsAt.alpha delta eta M
        P Bsource c depth K0 R certificate I deltaStar hdelta J)
      (@Erdos390.WholePaper.BankPaperRealization.BankPaperCanonicalSectionNinePostHeightBridgeInputsAt.beta delta eta M
        P Bsource c depth K0 R certificate I deltaStar hdelta J)
      (@Erdos390.WholePaper.BankPaperRealization.BankPaperCanonicalSectionNinePostHeightBridgeInputsAt.qTilde delta eta
        M P Bsource c depth K0 R certificate I deltaStar hdelta J)),
  @Exists.{1}
    (@Erdos390.WholePaper.BankPaperRealization.BankPaperCanonicalSectionNinePostHeightSourceInputsAt delta eta M P
      Bsource c depth K0 R certificate I deltaStar hdelta J)
    fun
      (S :
        @Erdos390.WholePaper.BankPaperRealization.BankPaperCanonicalSectionNinePostHeightSourceInputsAt delta eta M P
          Bsource c depth K0 R certificate I deltaStar hdelta J) =>
    @Exists.{0}
      (@Erdos390.WholePaper.BankPaperRealization.BankPaperCanonicalSectionNinePostHeightPrimitiveGapsAt delta eta M P
        Bsource c depth K0 R certificate I E deltaStar mu sourceMarginFloor headMarginFloor physicalEtaFloor
        postMarginFloor logY Lambda0 mFrozen qTilde hdelta J S)
      fun
        (_Hgap :
          @Erdos390.WholePaper.BankPaperRealization.BankPaperCanonicalSectionNinePostHeightPrimitiveGapsAt delta eta M P
            Bsource c depth K0 R certificate I E deltaStar mu sourceMarginFloor headMarginFloor physicalEtaFloor
            postMarginFloor logY Lambda0 mFrozen qTilde hdelta J S) =>
      And
        (@Eq.{1} Real
          (@Erdos390.WholePaper.BankPaperRealization.BankPaperCanonicalSectionNinePostHeightSourceInputsAt.Cmass delta
            eta M P Bsource c depth K0 R certificate I deltaStar hdelta J S)
          Cmass)
        (@Eq.{1} Real
          (@Erdos390.WholePaper.BankPaperRealization.BankPaperCanonicalSectionNinePostHeightSourceInputsAt.density delta
            eta M P Bsource c depth K0 R certificate I deltaStar hdelta J S)
          density) := by
  exact @Erdos390.WholePaper.BankPaperRealization.exists_bankPaperCanonicalSectionNinePostHeight_sourceInputsAndPrimitiveGapsAt_of_canonical
