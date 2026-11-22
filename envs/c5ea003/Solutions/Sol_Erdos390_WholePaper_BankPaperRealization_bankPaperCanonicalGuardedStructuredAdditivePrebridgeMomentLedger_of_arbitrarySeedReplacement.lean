-- Prove2me | solution 1 for Erdos390.WholePaper.BankPaperRealization.bankPaperCanonicalGuardedStructuredAdditivePrebridgeMomentLedger_of_arbitrarySeedReplacement
-- status  : ACCEPTED   (prove)
-- author  : @doctosil
-- created : 2026-09-17T16:14:27.474279+00:00
-- url     : https://prove2.me/submissions/28dedf2b-b9f4-43c7-8e18-75a22e25eeb9

import Mathlib
import Definitions.Def_erdos390_source_bank_interface
import Definitions.Def_erdos390_dickman_step_function
import Theorems.Thm_MediumPNT
import Definitions.Def_erdos390_analytic_foundations_001
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_product_bound
import Theorems.Thm_Erdos390_Full_DickmanBasic_rho_pos_on_zero_five
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_secondDerivative_first_bound
import Definitions.Def_erdos390_analytic_foundations_002
import Definitions.Def_erdos390_analytic_foundations_007
import Definitions.Def_erdos390_analytic_foundations_008

/- Source module: Erdos390.WholePaper.BankPaperProposition87ActualDataConnector -/
section


/-!
# Actual paper data at the Proposition 8.7 / guarded-selector interface

The paper does not use the mass-one normalization of the bridge.  Its
literal active weights are the numbers `z_m^0`, and

`q_n = sum_m z_m^0`.

At a clean numerical coordinate the protected frozen layer may overlap the
active layer.  Consequently `q_n` is not, in general, the sum of the whole
guarded selector on the active support.  This module keeps the two layers
separate.  Every guarded candidate is represented by a frozen tag of weight

`preSelector a - activeSeedAmbient a`,

while Proposition 8.7 evolves the active seed.  Thus the protected overlap
is retained exactly and the combined selector at time zero is the supplied
guarded pre-selector.

The single construction still missing from the finite guarded ledger is
named `BankPaperCanonicalActualActiveMeasureConstructor`.  It asks only for
the paper's active-measure realization: the seed has the canonical
barycentric shape, has eventual paper-scale mass at least one, is supported
on the guarded candidates, and is dominated by the already feasible
pre-selector.  Row integrality, target agreement, band balance, support,
pointwise estimates, and prefix estimates are not repeated in this
constructor; they are derived below from the existing guarded selector and
the Proposition 8.7 path.
-/

open Filter Topology Set
set_option backward.isDefEq.respectTransparency false

open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.PaperBridgeFit
open Erdos390.Full.PaperGuardCensus
open Erdos390.Full.RegularMeshPrimeCutoffs
open Erdos390.Full.RegularRelativeMesh

noncomputable section

/-! ## The literal active mass and its sole construction socket -/

























/-! ## The actual scaled bridge data -/









/-! ## Tagged frozen remainder and exact push-forward -/





















/-! ## The initial combined selector -/









/-! ## The literal active marked target and endpoint -/













/-! ## Smooth active support and unchanged complete-rough rows -/







/-- Push-forward mass over any finite set containing every active sample
value is the total tagged seed mass. -/
theorem sum_bankPaperCanonicalActiveSeedAmbientWeight_eq_activeMass_of_subset
    {Head : Type*} [Fintype Head]
    (D : StructuredSampleData Head) (activeSeed : D.Sample -> Real)
    (support : Finset Nat)
    (hvalues : ∀ m : D.Sample, D.value m ∈ support) :
    (∑ a ∈ support,
      bankPaperCanonicalActiveSeedAmbientWeight D activeSeed a) =
        bankPaperCanonicalLiteralActiveMass D activeSeed := by
  classical
  unfold bankPaperCanonicalActiveSeedAmbientWeight
    bankPaperCanonicalLiteralActiveMass
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro m _hm
  rw [Finset.sum_eq_single (D.value m)]
  · simp
  · intro a _ha hne
    simp [hne.symm]
  · intro hnot
    exact (hnot (hvalues m)).elim

/-- The active seed push-forward vanishes at a coordinate which is not the
value of any active sample tag. -/
theorem bankPaperCanonicalActiveSeedAmbientWeight_eq_zero_of_not_value
    {Head : Type*} [Fintype Head]
    (D : StructuredSampleData Head) (activeSeed : D.Sample -> Real)
    (a : Nat) (ha : forall m : D.Sample, D.value m ≠ a) :
    bankPaperCanonicalActiveSeedAmbientWeight D activeSeed a = 0 := by
  unfold bankPaperCanonicalActiveSeedAmbientWeight
  apply Finset.sum_eq_zero
  intro m _hm
  rw [if_neg (ha m)]













/-! ## Prime support, exact bands, and the derived prefix ledger -/











/-! ## Complete endpoint handoff -/



/-! ## Direct coupling to the guarded continuation -/



end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankPaperCanonicalSmoothAdditivePlacement -/
section


/-!
# Paper-faithful placement boundary for the guarded smooth refinement

The smooth bridge in the paper does not preserve the medium-prime moments
of an earlier provisional selector.  It freezes the protected layer,
redistributes the active mass while preserving the smooth-row ledger and
the moments outside the tangent band, and then fits the medium-prime band
moments.  Proposition 8.7 supplies that latter fit.

Accordingly, the pre-selector part of the actual endpoint theorem needs
only complete-row integrality and deficit support outside the medium-prime
band.  Its older statement accepted a full rounded-selector tangent input,
although the proof used only those two fields.  This file records the
weaker exact theorem, constructs the minimized ledger from the paper's two
literal zero-head cells, and proves the exact scaled structured head-cell
moments.  It then resolves the support boundary--the nonzero head cells lie
in the smooth row, not in its head-free correction subpool--by transporting
a signed ledger over the whole smooth row for the corrected selector.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.PaperBridgeFit
open Erdos390.Full.PaperGuardCensus
open Erdos390.Full.PrimeSums
open Erdos390.Full.RegularMeshPrimeCutoffs
open Erdos390.Full.RegularRelativeMesh

noncomputable section

namespace BankPaperRealization



/-! ## Exact finite algebra for the two zero-head pools -/





















/-! ## The head-free correction-pool ledger -/











/-! ## Structured head-cell realization -/





/-- Weighted ambient push-forward over a support containing all structured
values is exactly the corresponding tagged weighted sum. -/
theorem sum_bankPaperCanonicalActiveSeedAmbientWeight_mul_valuation_eq_tagged
    {Head : Type*} [Fintype Head]
    (D : StructuredSampleData Head) (seed : D.Sample -> Real)
    (support : Finset Nat)
    (hvalues : forall m : D.Sample, D.value m ∈ support)
    (p : Nat) :
    (∑ a ∈ support,
        bankPaperCanonicalActiveSeedAmbientWeight D seed a *
          valuation p a) =
      ∑ m : D.Sample, seed m * valuation p (D.value m) := by
  classical
  unfold bankPaperCanonicalActiveSeedAmbientWeight
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro m _hm
  rw [Finset.sum_eq_single (D.value m)]
  · simp
  · intro a _ha hne
    simp [hne.symm]
  · intro hnot
    exact (hnot (hvalues m)).elim













/-! ## Exact support boundary -/



/-! ## Signed whole-smooth-row placement ledger -/



































end BankPaperRealization

/-! ## Weaker actual-endpoint preselector interface -/



namespace BankPaperRealization







end BankPaperRealization

end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankPaperCanonicalSectionNinePostHeightSourcePrebridgeConnector -/
section


/-!
# The literal frozen-top source-to-post-height prebridge

The frozen-top rounded source contains its own nearest-integer active seed,
whereas the final baseline uses the fresh post-height barycentric seed of
mass `q0-d`.  These seeds are not equal.  What the structured prebridge
needs is instead their exact *signed difference* on the complete smooth
row:

* its total mass is the integer `-d`;
* its valuation moment at every head prime is zero.

This file proves that ledger.  The old head moment is recovered from the
literal source state's zero deficit outside the medium-prime band and the
paper's selector-tail target.  The new head moment is the exact
`activeHeadTarget` realized by the post-height target.  Thus no equality of
the old and new seeds is assumed.

The final theorem combines this ledger with the geometric feasibility
theorem from the post-height placed-measure connector, yielding the actual
measure and the full row-integral structured placement.
-/

open Set
open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.PaperBridgeFit
open Erdos390.Full.PaperGuardCensus
open Erdos390.Full.PaperHeadSimplex

noncomputable section

namespace BankPaperRealization

/-! ## The geometric outside compatibility -/



/-! ## Arbitrary replacement of a two-zero-cell source seed -/

/-- Pointwise signed identity for replacing the active seed of an arbitrary
two-zero-cell source by a fresh structured seed.

The outside selector may retain any frozen data.  It is constrained only
at occupied active coordinates outside the protected broad pool, exactly
as in the existing two-zero-cell placement theorem. -/
theorem
    bankPaperCanonicalGuardedStructuredAdditivePlacementSelector_arbitrarySeed_sub_twoZeroSource_of_active
    {P : Finset Nat} {Band : Type*}
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData (PaperHeadSimplex.Tag P) Band)
    {c : Real} {depth K : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (deltaStar betaProt : Real)
    (oldSeed newSeed : B.sampleData.Sample → Real)
    (outsideSelector : Nat → Real)
    (houtsideActive : ∀ a,
      a ∈ bankPaperCanonicalStructuredActiveValues B.sampleData →
      a ∉ R.roughCanonicalGuardedBroadCorrectionPool certificate
        deltaStar B.sampleData.W K 1 →
      outsideSelector a =
        bankPaperCanonicalActiveSeedAmbientWeight
          B.sampleData oldSeed a)
    (a : Nat) :
    bankPaperCanonicalGuardedStructuredAdditivePlacementSelector (K := K)
          B R certificate deltaStar betaProt
          (bankPaperCanonicalTwoZeroHeadCellSourceSelector (K := K)
            B R certificate deltaStar betaProt oldSeed outsideSelector)
          newSeed a -
        bankPaperCanonicalTwoZeroHeadCellSourceSelector (K := K)
          B R certificate deltaStar betaProt oldSeed outsideSelector a =
      bankPaperCanonicalActiveSeedAmbientWeight B.sampleData newSeed a -
        bankPaperCanonicalActiveSeedAmbientWeight
          B.sampleData oldSeed a := by
  by_cases hactive :
      a ∈ bankPaperCanonicalStructuredActiveValues B.sampleData
  · rw [bankPaperCanonicalGuardedStructuredAdditivePlacementSelector_apply_of_mem
      (K := K) B R certificate
        (bankPaperCanonicalTwoZeroHeadCellSourceSelector (K := K)
          B R certificate deltaStar betaProt oldSeed outsideSelector)
        newSeed hactive]
    by_cases hpool : a ∈
        R.roughCanonicalGuardedBroadCorrectionPool certificate
          deltaStar B.sampleData.W K 1
    · rw [bankPaperCanonicalGuardedSmoothProtectedLayer_apply_of_mem
          B R certificate hpool]
      unfold bankPaperCanonicalTwoZeroHeadCellSourceSelector
      rw [if_pos hpool]
      ring
    · rw [bankPaperCanonicalGuardedSmoothProtectedLayer_apply_of_not_mem
          B R certificate hpool]
      unfold bankPaperCanonicalTwoZeroHeadCellSourceSelector
      rw [if_neg hpool, houtsideActive a hactive hpool]
      ring
  · rw [bankPaperCanonicalGuardedStructuredAdditivePlacementSelector_apply_of_not_mem
      (K := K) B R certificate
        (bankPaperCanonicalTwoZeroHeadCellSourceSelector (K := K)
          B R certificate deltaStar betaProt oldSeed outsideSelector)
        newSeed hactive]
    have hnew :
        bankPaperCanonicalActiveSeedAmbientWeight
            B.sampleData newSeed a = 0 := by
      apply bankPaperCanonicalActiveSeedAmbientWeight_eq_zero_of_not_value
      intro m hma
      exact hactive
        (mem_bankPaperCanonicalStructuredActiveValues.mpr ⟨m, hma⟩)
    have hold :
        bankPaperCanonicalActiveSeedAmbientWeight
            B.sampleData oldSeed a = 0 := by
      apply bankPaperCanonicalActiveSeedAmbientWeight_eq_zero_of_not_value
      intro m hma
      exact hactive
        (mem_bankPaperCanonicalStructuredActiveValues.mpr ⟨m, hma⟩)
    by_cases hpool : a ∈
        R.roughCanonicalGuardedBroadCorrectionPool certificate
          deltaStar B.sampleData.W K 1
    · rw [bankPaperCanonicalGuardedSmoothAdditiveRefinement_apply_of_mem
          B R certificate
            (bankPaperCanonicalTwoZeroHeadCellSourceSelector (K := K)
              B R certificate deltaStar betaProt oldSeed outsideSelector)
            newSeed hpool]
      unfold bankPaperCanonicalTwoZeroHeadCellSourceSelector
      rw [if_pos hpool, hnew, hold]
      ring
    · rw [bankPaperCanonicalGuardedSmoothAdditiveRefinement_apply_of_not_mem
          B R certificate
            (bankPaperCanonicalTwoZeroHeadCellSourceSelector (K := K)
              B R certificate deltaStar betaProt oldSeed outsideSelector)
            newSeed hpool,
        hnew, hold]
      ring

/-- Exact prebridge ledger for an arbitrary fresh replacement seed.

This theorem distills the mathematical content of a seed replacement:
support on the complete smooth row, an integral signed mass change, and
equality of all head-prime moments. -/
theorem
    bankPaperCanonicalGuardedStructuredAdditivePrebridgeMomentLedger_of_arbitrarySeedReplacement
    {P : Finset Nat} {Band : Type*}
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData (PaperHeadSimplex.Tag P) Band)
    {c : Real} {depth K : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (deltaStar betaProt : Real)
    (oldSeed newSeed : B.sampleData.Sample → Real)
    (outsideSelector : Nat → Real)
    (houtsideActive : ∀ a,
      a ∈ bankPaperCanonicalStructuredActiveValues B.sampleData →
      a ∉ R.roughCanonicalGuardedBroadCorrectionPool certificate
        deltaStar B.sampleData.W K 1 →
      outsideSelector a =
        bankPaperCanonicalActiveSeedAmbientWeight
          B.sampleData oldSeed a)
    (hactiveSmooth :
      bankPaperCanonicalStructuredActiveValues B.sampleData ⊆
        R.roughCanonicalGuardedRow certificate deltaStar K 1)
    (rowChange : Int)
    (hmass :
      bankPaperCanonicalLiteralActiveMass B.sampleData newSeed -
          bankPaperCanonicalLiteralActiveMass B.sampleData oldSeed =
        (rowChange : Real))
    (hhead : ∀ q : Nat, q.Prime → q ≤ B.sampleData.W →
      (∑ m : B.sampleData.Sample,
          newSeed m * valuation q (B.sampleData.value m)) =
        ∑ m : B.sampleData.Sample,
          oldSeed m * valuation q (B.sampleData.value m)) :
    BankPaperCanonicalGuardedStructuredAdditivePrebridgeMomentLedger
      (K := K) B R certificate deltaStar betaProt
        (bankPaperCanonicalTwoZeroHeadCellSourceSelector (K := K)
          B R certificate deltaStar betaProt oldSeed outsideSelector)
        newSeed := by
  have hvalues : ∀ m : B.sampleData.Sample,
      B.sampleData.value m ∈
        R.roughCanonicalGuardedRow certificate deltaStar K 1 := by
    intro m
    exact hactiveSmooth
      (mem_bankPaperCanonicalStructuredActiveValues.mpr ⟨m, rfl⟩)
  refine ⟨hactiveSmooth, ⟨rowChange, ?_⟩, ?_⟩
  · calc
      (∑ a ∈ R.roughCanonicalGuardedRow certificate deltaStar K 1,
        (bankPaperCanonicalGuardedStructuredAdditivePlacementSelector
              (K := K) B R certificate deltaStar betaProt
              (bankPaperCanonicalTwoZeroHeadCellSourceSelector (K := K)
                B R certificate deltaStar betaProt oldSeed outsideSelector)
              newSeed a -
          bankPaperCanonicalTwoZeroHeadCellSourceSelector (K := K)
            B R certificate deltaStar betaProt oldSeed outsideSelector a)) =
        ∑ a ∈ R.roughCanonicalGuardedRow certificate deltaStar K 1,
          (bankPaperCanonicalActiveSeedAmbientWeight
                B.sampleData newSeed a -
            bankPaperCanonicalActiveSeedAmbientWeight
              B.sampleData oldSeed a) := by
          apply Finset.sum_congr rfl
          intro a _ha
          exact
            bankPaperCanonicalGuardedStructuredAdditivePlacementSelector_arbitrarySeed_sub_twoZeroSource_of_active
              (K := K) B R certificate deltaStar betaProt
                oldSeed newSeed outsideSelector houtsideActive a
      _ =
          (∑ a ∈ R.roughCanonicalGuardedRow certificate deltaStar K 1,
            bankPaperCanonicalActiveSeedAmbientWeight
              B.sampleData newSeed a) -
          ∑ a ∈ R.roughCanonicalGuardedRow certificate deltaStar K 1,
            bankPaperCanonicalActiveSeedAmbientWeight
              B.sampleData oldSeed a := by
        rw [Finset.sum_sub_distrib]
      _ =
          bankPaperCanonicalLiteralActiveMass B.sampleData newSeed -
            bankPaperCanonicalLiteralActiveMass B.sampleData oldSeed := by
        rw [
          sum_bankPaperCanonicalActiveSeedAmbientWeight_eq_activeMass_of_subset
            B.sampleData newSeed
              (R.roughCanonicalGuardedRow certificate deltaStar K 1)
              hvalues,
          sum_bankPaperCanonicalActiveSeedAmbientWeight_eq_activeMass_of_subset
            B.sampleData oldSeed
              (R.roughCanonicalGuardedRow certificate deltaStar K 1)
              hvalues]
      _ = (rowChange : Real) := hmass
  · intro q hqPrime hqW
    unfold
      bankPaperCanonicalGuardedStructuredAdditivePlacementValuationMoment
    calc
      (∑ a ∈ R.roughCanonicalGuardedRow certificate deltaStar K 1,
        (bankPaperCanonicalGuardedStructuredAdditivePlacementSelector
              (K := K) B R certificate deltaStar betaProt
              (bankPaperCanonicalTwoZeroHeadCellSourceSelector (K := K)
                B R certificate deltaStar betaProt oldSeed outsideSelector)
              newSeed a -
          bankPaperCanonicalTwoZeroHeadCellSourceSelector (K := K)
            B R certificate deltaStar betaProt oldSeed outsideSelector a) *
          (a.factorization q : Real)) =
        ∑ a ∈ R.roughCanonicalGuardedRow certificate deltaStar K 1,
          (bankPaperCanonicalActiveSeedAmbientWeight
                B.sampleData newSeed a -
            bankPaperCanonicalActiveSeedAmbientWeight
              B.sampleData oldSeed a) * valuation q a := by
          apply Finset.sum_congr rfl
          intro a _ha
          rw [
            bankPaperCanonicalGuardedStructuredAdditivePlacementSelector_arbitrarySeed_sub_twoZeroSource_of_active
              (K := K) B R certificate deltaStar betaProt
                oldSeed newSeed outsideSelector houtsideActive a]
          rfl
      _ =
          (∑ a ∈ R.roughCanonicalGuardedRow certificate deltaStar K 1,
            bankPaperCanonicalActiveSeedAmbientWeight
                B.sampleData newSeed a * valuation q a) -
          ∑ a ∈ R.roughCanonicalGuardedRow certificate deltaStar K 1,
            bankPaperCanonicalActiveSeedAmbientWeight
                B.sampleData oldSeed a * valuation q a := by
        rw [← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro a _ha
        ring
      _ =
          (∑ m : B.sampleData.Sample,
            newSeed m * valuation q (B.sampleData.value m)) -
          ∑ m : B.sampleData.Sample,
            oldSeed m * valuation q (B.sampleData.value m) := by
        rw [
          sum_bankPaperCanonicalActiveSeedAmbientWeight_mul_valuation_eq_tagged
            B.sampleData newSeed
              (R.roughCanonicalGuardedRow certificate deltaStar K 1)
              hvalues q,
          sum_bankPaperCanonicalActiveSeedAmbientWeight_mul_valuation_eq_tagged
            B.sampleData oldSeed
              (R.roughCanonicalGuardedRow certificate deltaStar K 1)
              hvalues q]
      _ = 0 := sub_eq_zero.mpr (hhead q hqPrime hqW)

/-! ## Recovering the old head moment from the literal source state -/



/-! ## The paper's `q0-d` prebridge ledger -/



/-! ## Row quota and full placement -/





/-! ## One-shot geometric source-to-post-height construction -/



end BankPaperRealization

end

end Erdos390.WholePaper

end

universe u_1
theorem solution :
∀ {P : Finset.{0} Nat} {Band : Type u_1} [inst : Fintype.{u_1} Band] [inst_1 : DecidableEq.{u_1 + 1} Band]
  (B :
    @Erdos390.Full.PaperBridgeFit.BridgeData.{0, u_1} (Erdos390.Full.PaperHeadSimplex.Tag P) Band
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
      inst inst_1)
  {c : Real} {depth K : Nat}
  (R :
    Erdos390.WholePaper.BankPaperRealization
      (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P)
        (@instFintypeOption.{0}
          (@Subtype.{1} Nat fun (p : Nat) =>
            @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
              (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
          (@Finset.Subtype.fintype.{0} Nat P))
        (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1} (Erdos390.Full.PaperHeadSimplex.Tag P) Band
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
          inst inst_1 B))
      (Erdos390.WholePaper.upperEndpoint
        (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P)
          (@instFintypeOption.{0}
            (@Subtype.{1} Nat fun (p : Nat) =>
              @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
            (@Finset.Subtype.fintype.{0} Nat P))
          (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1} (Erdos390.Full.PaperHeadSimplex.Tag P) Band
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
            inst inst_1 B))
        (Erdos390.WholePaper.upperTailLength c
          (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P)
            (@instFintypeOption.{0}
              (@Subtype.{1} Nat fun (p : Nat) =>
                @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                  (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
              (@Finset.Subtype.fintype.{0} Nat P))
            (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1} (Erdos390.Full.PaperHeadSimplex.Tag P) Band
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
              inst inst_1 B)))))
  (certificate :
    Erdos390.WholePaper.GuardedCentralAnchorCertificate c depth
      (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P)
        (@instFintypeOption.{0}
          (@Subtype.{1} Nat fun (p : Nat) =>
            @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
              (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
          (@Finset.Subtype.fintype.{0} Nat P))
        (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1} (Erdos390.Full.PaperHeadSimplex.Tag P) Band
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
          inst inst_1 B))
      (@Erdos390.WholePaper.BankPaperRealization.anchorGuardLeftCore
        (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P)
          (@instFintypeOption.{0}
            (@Subtype.{1} Nat fun (p : Nat) =>
              @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
            (@Finset.Subtype.fintype.{0} Nat P))
          (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1} (Erdos390.Full.PaperHeadSimplex.Tag P) Band
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
            inst inst_1 B))
        (Erdos390.WholePaper.upperEndpoint
          (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P)
            (@instFintypeOption.{0}
              (@Subtype.{1} Nat fun (p : Nat) =>
                @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                  (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
              (@Finset.Subtype.fintype.{0} Nat P))
            (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1} (Erdos390.Full.PaperHeadSimplex.Tag P) Band
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
              inst inst_1 B))
          (Erdos390.WholePaper.upperTailLength c
            (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P)
              (@instFintypeOption.{0}
                (@Subtype.{1} Nat fun (p : Nat) =>
                  @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                    (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                (@Finset.Subtype.fintype.{0} Nat P))
              (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1} (Erdos390.Full.PaperHeadSimplex.Tag P) Band
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
                inst inst_1 B))))
        R)
      (@Erdos390.WholePaper.BankPaperRealization.anchorGuardRightCore
        (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P)
          (@instFintypeOption.{0}
            (@Subtype.{1} Nat fun (p : Nat) =>
              @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
            (@Finset.Subtype.fintype.{0} Nat P))
          (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1} (Erdos390.Full.PaperHeadSimplex.Tag P) Band
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
            inst inst_1 B))
        (Erdos390.WholePaper.upperEndpoint
          (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P)
            (@instFintypeOption.{0}
              (@Subtype.{1} Nat fun (p : Nat) =>
                @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                  (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
              (@Finset.Subtype.fintype.{0} Nat P))
            (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1} (Erdos390.Full.PaperHeadSimplex.Tag P) Band
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
              inst inst_1 B))
          (Erdos390.WholePaper.upperTailLength c
            (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P)
              (@instFintypeOption.{0}
                (@Subtype.{1} Nat fun (p : Nat) =>
                  @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                    (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                (@Finset.Subtype.fintype.{0} Nat P))
              (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1} (Erdos390.Full.PaperHeadSimplex.Tag P) Band
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
                inst inst_1 B))))
        R)
      (@Erdos390.WholePaper.BankPaperRealization.centralChangedMarkers
        (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P)
          (@instFintypeOption.{0}
            (@Subtype.{1} Nat fun (p : Nat) =>
              @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
            (@Finset.Subtype.fintype.{0} Nat P))
          (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1} (Erdos390.Full.PaperHeadSimplex.Tag P) Band
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
            inst inst_1 B))
        (Erdos390.WholePaper.upperEndpoint
          (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P)
            (@instFintypeOption.{0}
              (@Subtype.{1} Nat fun (p : Nat) =>
                @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                  (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
              (@Finset.Subtype.fintype.{0} Nat P))
            (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1} (Erdos390.Full.PaperHeadSimplex.Tag P) Band
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
              inst inst_1 B))
          (Erdos390.WholePaper.upperTailLength c
            (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P)
              (@instFintypeOption.{0}
                (@Subtype.{1} Nat fun (p : Nat) =>
                  @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                    (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                (@Finset.Subtype.fintype.{0} Nat P))
              (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1} (Erdos390.Full.PaperHeadSimplex.Tag P) Band
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
                inst inst_1 B))))
        R depth))
  (deltaStar betaProt : Real)
  (oldSeed newSeed :
    @Erdos390.Full.PaperBridgeFit.StructuredSampleData.Sample.{0} (Erdos390.Full.PaperHeadSimplex.Tag P)
        (@instFintypeOption.{0}
          (@Subtype.{1} Nat fun (p : Nat) =>
            @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
              (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
          (@Finset.Subtype.fintype.{0} Nat P))
        (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1} (Erdos390.Full.PaperHeadSimplex.Tag P) Band
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
          inst inst_1 B) →
      Real)
  (outsideSelector : Nat → Real),
  (∀ (a : Nat),
      @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
          (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat))
          (@Erdos390.WholePaper.bankPaperCanonicalStructuredActiveValues.{0} (Erdos390.Full.PaperHeadSimplex.Tag P)
            (@instFintypeOption.{0}
              (@Subtype.{1} Nat fun (p : Nat) =>
                @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                  (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
              (@Finset.Subtype.fintype.{0} Nat P))
            (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1} (Erdos390.Full.PaperHeadSimplex.Tag P) Band
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
              inst inst_1 B))
          a →
        Not
            (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
              (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat))
              (@Erdos390.WholePaper.BankPaperRealization.roughCanonicalGuardedBroadCorrectionPool c depth
                (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P)
                  (@instFintypeOption.{0}
                    (@Subtype.{1} Nat fun (p : Nat) =>
                      @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                        (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                    (@Finset.Subtype.fintype.{0} Nat P))
                  (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1} (Erdos390.Full.PaperHeadSimplex.Tag P)
                    Band
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
                    inst inst_1 B))
                (Erdos390.WholePaper.upperTailLength c
                  (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P)
                    (@instFintypeOption.{0}
                      (@Subtype.{1} Nat fun (p : Nat) =>
                        @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                          (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                      (@Finset.Subtype.fintype.{0} Nat P))
                    (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1} (Erdos390.Full.PaperHeadSimplex.Tag P)
                      Band
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
                      inst inst_1 B)))
                (@Erdos390.WholePaper.BankPaperRealization.anchorGuardLeftCore
                  (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P)
                    (@instFintypeOption.{0}
                      (@Subtype.{1} Nat fun (p : Nat) =>
                        @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                          (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                      (@Finset.Subtype.fintype.{0} Nat P))
                    (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1} (Erdos390.Full.PaperHeadSimplex.Tag P)
                      Band
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
                      inst inst_1 B))
                  (Erdos390.WholePaper.upperEndpoint
                    (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P)
                      (@instFintypeOption.{0}
                        (@Subtype.{1} Nat fun (p : Nat) =>
                          @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                            (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                        (@Finset.Subtype.fintype.{0} Nat P))
                      (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1}
                        (Erdos390.Full.PaperHeadSimplex.Tag P) Band
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
                                      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                        (@Finset.instSetLike.{0} Nat))
                                      P p) =>
                              @Subtype.instDecidableEq.{1} Nat
                                (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                  (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P)
                                instDecidableEqNat a b)
                            a b)
                        inst inst_1 B))
                    (Erdos390.WholePaper.upperTailLength c
                      (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P)
                        (@instFintypeOption.{0}
                          (@Subtype.{1} Nat fun (p : Nat) =>
                            @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                              (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                          (@Finset.Subtype.fintype.{0} Nat P))
                        (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1}
                          (Erdos390.Full.PaperHeadSimplex.Tag P) Band
                          (@instFintypeOption.{0}
                            (@Subtype.{1} Nat fun (p : Nat) =>
                              @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                            (@Finset.Subtype.fintype.{0} Nat P))
                          (fun (a b : Erdos390.Full.PaperHeadSimplex.Tag P) =>
                            @Option.instDecidableEq.{0}
                              (@Subtype.{1} Nat fun (p : Nat) =>
                                @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                  (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P
                                  p)
                              (fun
                                  (a b :
                                    @Subtype.{1} Nat fun (p : Nat) =>
                                      @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                        (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                          (@Finset.instSetLike.{0} Nat))
                                        P p) =>
                                @Subtype.instDecidableEq.{1} Nat
                                  (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                    (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat))
                                    P)
                                  instDecidableEqNat a b)
                              a b)
                          inst inst_1 B))))
                  R)
                (@Erdos390.WholePaper.BankPaperRealization.anchorGuardRightCore
                  (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P)
                    (@instFintypeOption.{0}
                      (@Subtype.{1} Nat fun (p : Nat) =>
                        @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                          (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                      (@Finset.Subtype.fintype.{0} Nat P))
                    (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1} (Erdos390.Full.PaperHeadSimplex.Tag P)
                      Band
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
                      inst inst_1 B))
                  (Erdos390.WholePaper.upperEndpoint
                    (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P)
                      (@instFintypeOption.{0}
                        (@Subtype.{1} Nat fun (p : Nat) =>
                          @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                            (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                        (@Finset.Subtype.fintype.{0} Nat P))
                      (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1}
                        (Erdos390.Full.PaperHeadSimplex.Tag P) Band
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
                                      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                        (@Finset.instSetLike.{0} Nat))
                                      P p) =>
                              @Subtype.instDecidableEq.{1} Nat
                                (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                  (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P)
                                instDecidableEqNat a b)
                            a b)
                        inst inst_1 B))
                    (Erdos390.WholePaper.upperTailLength c
                      (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P)
                        (@instFintypeOption.{0}
                          (@Subtype.{1} Nat fun (p : Nat) =>
                            @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                              (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                          (@Finset.Subtype.fintype.{0} Nat P))
                        (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1}
                          (Erdos390.Full.PaperHeadSimplex.Tag P) Band
                          (@instFintypeOption.{0}
                            (@Subtype.{1} Nat fun (p : Nat) =>
                              @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                            (@Finset.Subtype.fintype.{0} Nat P))
                          (fun (a b : Erdos390.Full.PaperHeadSimplex.Tag P) =>
                            @Option.instDecidableEq.{0}
                              (@Subtype.{1} Nat fun (p : Nat) =>
                                @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                  (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P
                                  p)
                              (fun
                                  (a b :
                                    @Subtype.{1} Nat fun (p : Nat) =>
                                      @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                        (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                          (@Finset.instSetLike.{0} Nat))
                                        P p) =>
                                @Subtype.instDecidableEq.{1} Nat
                                  (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                    (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat))
                                    P)
                                  instDecidableEqNat a b)
                              a b)
                          inst inst_1 B))))
                  R)
                (@Erdos390.WholePaper.BankPaperRealization.centralChangedMarkers
                  (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P)
                    (@instFintypeOption.{0}
                      (@Subtype.{1} Nat fun (p : Nat) =>
                        @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                          (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                      (@Finset.Subtype.fintype.{0} Nat P))
                    (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1} (Erdos390.Full.PaperHeadSimplex.Tag P)
                      Band
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
                      inst inst_1 B))
                  (Erdos390.WholePaper.upperEndpoint
                    (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P)
                      (@instFintypeOption.{0}
                        (@Subtype.{1} Nat fun (p : Nat) =>
                          @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                            (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                        (@Finset.Subtype.fintype.{0} Nat P))
                      (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1}
                        (Erdos390.Full.PaperHeadSimplex.Tag P) Band
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
                                      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                        (@Finset.instSetLike.{0} Nat))
                                      P p) =>
                              @Subtype.instDecidableEq.{1} Nat
                                (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                  (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P)
                                instDecidableEqNat a b)
                            a b)
                        inst inst_1 B))
                    (Erdos390.WholePaper.upperTailLength c
                      (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P)
                        (@instFintypeOption.{0}
                          (@Subtype.{1} Nat fun (p : Nat) =>
                            @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                              (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                          (@Finset.Subtype.fintype.{0} Nat P))
                        (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1}
                          (Erdos390.Full.PaperHeadSimplex.Tag P) Band
                          (@instFintypeOption.{0}
                            (@Subtype.{1} Nat fun (p : Nat) =>
                              @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                            (@Finset.Subtype.fintype.{0} Nat P))
                          (fun (a b : Erdos390.Full.PaperHeadSimplex.Tag P) =>
                            @Option.instDecidableEq.{0}
                              (@Subtype.{1} Nat fun (p : Nat) =>
                                @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                  (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P
                                  p)
                              (fun
                                  (a b :
                                    @Subtype.{1} Nat fun (p : Nat) =>
                                      @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                        (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                          (@Finset.instSetLike.{0} Nat))
                                        P p) =>
                                @Subtype.instDecidableEq.{1} Nat
                                  (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                    (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat))
                                    P)
                                  instDecidableEqNat a b)
                              a b)
                          inst inst_1 B))))
                  R depth)
                R certificate deltaStar
                (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{0} (Erdos390.Full.PaperHeadSimplex.Tag P)
                  (@instFintypeOption.{0}
                    (@Subtype.{1} Nat fun (p : Nat) =>
                      @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                        (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                    (@Finset.Subtype.fintype.{0} Nat P))
                  (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1} (Erdos390.Full.PaperHeadSimplex.Tag P)
                    Band
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
                    inst inst_1 B))
                K (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
              a) →
          @Eq.{1} Real (outsideSelector a)
            (@Erdos390.WholePaper.bankPaperCanonicalActiveSeedAmbientWeight.{0} (Erdos390.Full.PaperHeadSimplex.Tag P)
              (@instFintypeOption.{0}
                (@Subtype.{1} Nat fun (p : Nat) =>
                  @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                    (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                (@Finset.Subtype.fintype.{0} Nat P))
              (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1} (Erdos390.Full.PaperHeadSimplex.Tag P) Band
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
                inst inst_1 B)
              oldSeed a)) →
    @HasSubset.Subset.{0} (Finset.{0} Nat) (@Finset.instHasSubset.{0} Nat)
        (@Erdos390.WholePaper.bankPaperCanonicalStructuredActiveValues.{0} (Erdos390.Full.PaperHeadSimplex.Tag P)
          (@instFintypeOption.{0}
            (@Subtype.{1} Nat fun (p : Nat) =>
              @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
            (@Finset.Subtype.fintype.{0} Nat P))
          (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1} (Erdos390.Full.PaperHeadSimplex.Tag P) Band
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
            inst inst_1 B))
        (@Erdos390.WholePaper.BankPaperRealization.roughCanonicalGuardedRow c depth
          (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P)
            (@instFintypeOption.{0}
              (@Subtype.{1} Nat fun (p : Nat) =>
                @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                  (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
              (@Finset.Subtype.fintype.{0} Nat P))
            (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1} (Erdos390.Full.PaperHeadSimplex.Tag P) Band
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
              inst inst_1 B))
          (Erdos390.WholePaper.upperTailLength c
            (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P)
              (@instFintypeOption.{0}
                (@Subtype.{1} Nat fun (p : Nat) =>
                  @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                    (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                (@Finset.Subtype.fintype.{0} Nat P))
              (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1} (Erdos390.Full.PaperHeadSimplex.Tag P) Band
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
                inst inst_1 B)))
          (@Erdos390.WholePaper.BankPaperRealization.anchorGuardLeftCore
            (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P)
              (@instFintypeOption.{0}
                (@Subtype.{1} Nat fun (p : Nat) =>
                  @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                    (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                (@Finset.Subtype.fintype.{0} Nat P))
              (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1} (Erdos390.Full.PaperHeadSimplex.Tag P) Band
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
                inst inst_1 B))
            (Erdos390.WholePaper.upperEndpoint
              (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P)
                (@instFintypeOption.{0}
                  (@Subtype.{1} Nat fun (p : Nat) =>
                    @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                  (@Finset.Subtype.fintype.{0} Nat P))
                (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1} (Erdos390.Full.PaperHeadSimplex.Tag P)
                  Band
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
                  inst inst_1 B))
              (Erdos390.WholePaper.upperTailLength c
                (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P)
                  (@instFintypeOption.{0}
                    (@Subtype.{1} Nat fun (p : Nat) =>
                      @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                        (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                    (@Finset.Subtype.fintype.{0} Nat P))
                  (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1} (Erdos390.Full.PaperHeadSimplex.Tag P)
                    Band
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
                    inst inst_1 B))))
            R)
          (@Erdos390.WholePaper.BankPaperRealization.anchorGuardRightCore
            (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P)
              (@instFintypeOption.{0}
                (@Subtype.{1} Nat fun (p : Nat) =>
                  @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                    (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                (@Finset.Subtype.fintype.{0} Nat P))
              (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1} (Erdos390.Full.PaperHeadSimplex.Tag P) Band
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
                inst inst_1 B))
            (Erdos390.WholePaper.upperEndpoint
              (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P)
                (@instFintypeOption.{0}
                  (@Subtype.{1} Nat fun (p : Nat) =>
                    @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                  (@Finset.Subtype.fintype.{0} Nat P))
                (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1} (Erdos390.Full.PaperHeadSimplex.Tag P)
                  Band
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
                  inst inst_1 B))
              (Erdos390.WholePaper.upperTailLength c
                (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P)
                  (@instFintypeOption.{0}
                    (@Subtype.{1} Nat fun (p : Nat) =>
                      @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                        (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                    (@Finset.Subtype.fintype.{0} Nat P))
                  (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1} (Erdos390.Full.PaperHeadSimplex.Tag P)
                    Band
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
                    inst inst_1 B))))
            R)
          (@Erdos390.WholePaper.BankPaperRealization.centralChangedMarkers
            (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P)
              (@instFintypeOption.{0}
                (@Subtype.{1} Nat fun (p : Nat) =>
                  @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                    (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                (@Finset.Subtype.fintype.{0} Nat P))
              (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1} (Erdos390.Full.PaperHeadSimplex.Tag P) Band
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
                inst inst_1 B))
            (Erdos390.WholePaper.upperEndpoint
              (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P)
                (@instFintypeOption.{0}
                  (@Subtype.{1} Nat fun (p : Nat) =>
                    @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                  (@Finset.Subtype.fintype.{0} Nat P))
                (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1} (Erdos390.Full.PaperHeadSimplex.Tag P)
                  Band
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
                  inst inst_1 B))
              (Erdos390.WholePaper.upperTailLength c
                (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P)
                  (@instFintypeOption.{0}
                    (@Subtype.{1} Nat fun (p : Nat) =>
                      @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                        (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                    (@Finset.Subtype.fintype.{0} Nat P))
                  (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1} (Erdos390.Full.PaperHeadSimplex.Tag P)
                    Band
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
                    inst inst_1 B))))
            R depth)
          R certificate deltaStar K (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
      ∀ (rowChange : Int),
        @Eq.{1} Real
            (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
              (@Erdos390.WholePaper.bankPaperCanonicalLiteralActiveMass.{0} (Erdos390.Full.PaperHeadSimplex.Tag P)
                (@instFintypeOption.{0}
                  (@Subtype.{1} Nat fun (p : Nat) =>
                    @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                  (@Finset.Subtype.fintype.{0} Nat P))
                (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1} (Erdos390.Full.PaperHeadSimplex.Tag P)
                  Band
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
                  inst inst_1 B)
                newSeed)
              (@Erdos390.WholePaper.bankPaperCanonicalLiteralActiveMass.{0} (Erdos390.Full.PaperHeadSimplex.Tag P)
                (@instFintypeOption.{0}
                  (@Subtype.{1} Nat fun (p : Nat) =>
                    @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                  (@Finset.Subtype.fintype.{0} Nat P))
                (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1} (Erdos390.Full.PaperHeadSimplex.Tag P)
                  Band
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
                  inst inst_1 B)
                oldSeed))
            (@Int.cast.{0} Real Real.instIntCast rowChange) →
          (∀ (q : Nat),
              Nat.Prime q →
                @LE.le.{0} Nat instLENat q
                    (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{0} (Erdos390.Full.PaperHeadSimplex.Tag P)
                      (@instFintypeOption.{0}
                        (@Subtype.{1} Nat fun (p : Nat) =>
                          @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                            (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                        (@Finset.Subtype.fintype.{0} Nat P))
                      (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1}
                        (Erdos390.Full.PaperHeadSimplex.Tag P) Band
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
                                      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                        (@Finset.instSetLike.{0} Nat))
                                      P p) =>
                              @Subtype.instDecidableEq.{1} Nat
                                (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                  (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P)
                                instDecidableEqNat a b)
                            a b)
                        inst inst_1 B)) →
                  @Eq.{1} Real
                    (@Finset.sum.{0, 0}
                      (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.Sample.{0}
                        (Erdos390.Full.PaperHeadSimplex.Tag P)
                        (@instFintypeOption.{0}
                          (@Subtype.{1} Nat fun (p : Nat) =>
                            @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                              (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                          (@Finset.Subtype.fintype.{0} Nat P))
                        (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1}
                          (Erdos390.Full.PaperHeadSimplex.Tag P) Band
                          (@instFintypeOption.{0}
                            (@Subtype.{1} Nat fun (p : Nat) =>
                              @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                            (@Finset.Subtype.fintype.{0} Nat P))
                          (fun (a b : Erdos390.Full.PaperHeadSimplex.Tag P) =>
                            @Option.instDecidableEq.{0}
                              (@Subtype.{1} Nat fun (p : Nat) =>
                                @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                  (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P
                                  p)
                              (fun
                                  (a b :
                                    @Subtype.{1} Nat fun (p : Nat) =>
                                      @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                        (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                          (@Finset.instSetLike.{0} Nat))
                                        P p) =>
                                @Subtype.instDecidableEq.{1} Nat
                                  (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                    (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat))
                                    P)
                                  instDecidableEqNat a b)
                              a b)
                          inst inst_1 B))
                      Real Real.instAddCommMonoid
                      (@Finset.univ.{0}
                        (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.Sample.{0}
                          (Erdos390.Full.PaperHeadSimplex.Tag P)
                          (@instFintypeOption.{0}
                            (@Subtype.{1} Nat fun (p : Nat) =>
                              @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                            (@Finset.Subtype.fintype.{0} Nat P))
                          (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1}
                            (Erdos390.Full.PaperHeadSimplex.Tag P) Band
                            (@instFintypeOption.{0}
                              (@Subtype.{1} Nat fun (p : Nat) =>
                                @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                  (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P
                                  p)
                              (@Finset.Subtype.fintype.{0} Nat P))
                            (fun (a b : Erdos390.Full.PaperHeadSimplex.Tag P) =>
                              @Option.instDecidableEq.{0}
                                (@Subtype.{1} Nat fun (p : Nat) =>
                                  @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                    (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat))
                                    P p)
                                (fun
                                    (a b :
                                      @Subtype.{1} Nat fun (p : Nat) =>
                                        @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                          (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                            (@Finset.instSetLike.{0} Nat))
                                          P p) =>
                                  @Subtype.instDecidableEq.{1} Nat
                                    (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                        (@Finset.instSetLike.{0} Nat))
                                      P)
                                    instDecidableEqNat a b)
                                a b)
                            inst inst_1 B))
                        (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.sampleFintype.{0}
                          (Erdos390.Full.PaperHeadSimplex.Tag P)
                          (@instFintypeOption.{0}
                            (@Subtype.{1} Nat fun (p : Nat) =>
                              @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                            (@Finset.Subtype.fintype.{0} Nat P))
                          (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1}
                            (Erdos390.Full.PaperHeadSimplex.Tag P) Band
                            (@instFintypeOption.{0}
                              (@Subtype.{1} Nat fun (p : Nat) =>
                                @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                  (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P
                                  p)
                              (@Finset.Subtype.fintype.{0} Nat P))
                            (fun (a b : Erdos390.Full.PaperHeadSimplex.Tag P) =>
                              @Option.instDecidableEq.{0}
                                (@Subtype.{1} Nat fun (p : Nat) =>
                                  @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                    (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat))
                                    P p)
                                (fun
                                    (a b :
                                      @Subtype.{1} Nat fun (p : Nat) =>
                                        @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                          (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                            (@Finset.instSetLike.{0} Nat))
                                          P p) =>
                                  @Subtype.instDecidableEq.{1} Nat
                                    (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                        (@Finset.instSetLike.{0} Nat))
                                      P)
                                    instDecidableEqNat a b)
                                a b)
                            inst inst_1 B)))
                      fun
                        (m :
                          @Erdos390.Full.PaperBridgeFit.StructuredSampleData.Sample.{0}
                            (Erdos390.Full.PaperHeadSimplex.Tag P)
                            (@instFintypeOption.{0}
                              (@Subtype.{1} Nat fun (p : Nat) =>
                                @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                  (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P
                                  p)
                              (@Finset.Subtype.fintype.{0} Nat P))
                            (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1}
                              (Erdos390.Full.PaperHeadSimplex.Tag P) Band
                              (@instFintypeOption.{0}
                                (@Subtype.{1} Nat fun (p : Nat) =>
                                  @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                    (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat))
                                    P p)
                                (@Finset.Subtype.fintype.{0} Nat P))
                              (fun (a b : Erdos390.Full.PaperHeadSimplex.Tag P) =>
                                @Option.instDecidableEq.{0}
                                  (@Subtype.{1} Nat fun (p : Nat) =>
                                    @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                        (@Finset.instSetLike.{0} Nat))
                                      P p)
                                  (fun
                                      (a b :
                                        @Subtype.{1} Nat fun (p : Nat) =>
                                          @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                            (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                              (@Finset.instSetLike.{0} Nat))
                                            P p) =>
                                    @Subtype.instDecidableEq.{1} Nat
                                      (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                        (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                          (@Finset.instSetLike.{0} Nat))
                                        P)
                                      instDecidableEqNat a b)
                                  a b)
                              inst inst_1 B)) =>
                      @HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) (newSeed m)
                        (Erdos390.Full.ArithmeticModel.valuation q
                          (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.value.{0}
                            (Erdos390.Full.PaperHeadSimplex.Tag P)
                            (@instFintypeOption.{0}
                              (@Subtype.{1} Nat fun (p : Nat) =>
                                @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                  (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P
                                  p)
                              (@Finset.Subtype.fintype.{0} Nat P))
                            (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1}
                              (Erdos390.Full.PaperHeadSimplex.Tag P) Band
                              (@instFintypeOption.{0}
                                (@Subtype.{1} Nat fun (p : Nat) =>
                                  @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                    (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat))
                                    P p)
                                (@Finset.Subtype.fintype.{0} Nat P))
                              (fun (a b : Erdos390.Full.PaperHeadSimplex.Tag P) =>
                                @Option.instDecidableEq.{0}
                                  (@Subtype.{1} Nat fun (p : Nat) =>
                                    @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                        (@Finset.instSetLike.{0} Nat))
                                      P p)
                                  (fun
                                      (a b :
                                        @Subtype.{1} Nat fun (p : Nat) =>
                                          @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                            (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                              (@Finset.instSetLike.{0} Nat))
                                            P p) =>
                                    @Subtype.instDecidableEq.{1} Nat
                                      (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                        (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                          (@Finset.instSetLike.{0} Nat))
                                        P)
                                      instDecidableEqNat a b)
                                  a b)
                              inst inst_1 B)
                            m)))
                    (@Finset.sum.{0, 0}
                      (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.Sample.{0}
                        (Erdos390.Full.PaperHeadSimplex.Tag P)
                        (@instFintypeOption.{0}
                          (@Subtype.{1} Nat fun (p : Nat) =>
                            @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                              (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                          (@Finset.Subtype.fintype.{0} Nat P))
                        (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1}
                          (Erdos390.Full.PaperHeadSimplex.Tag P) Band
                          (@instFintypeOption.{0}
                            (@Subtype.{1} Nat fun (p : Nat) =>
                              @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                            (@Finset.Subtype.fintype.{0} Nat P))
                          (fun (a b : Erdos390.Full.PaperHeadSimplex.Tag P) =>
                            @Option.instDecidableEq.{0}
                              (@Subtype.{1} Nat fun (p : Nat) =>
                                @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                  (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P
                                  p)
                              (fun
                                  (a b :
                                    @Subtype.{1} Nat fun (p : Nat) =>
                                      @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                        (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                          (@Finset.instSetLike.{0} Nat))
                                        P p) =>
                                @Subtype.instDecidableEq.{1} Nat
                                  (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                    (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat))
                                    P)
                                  instDecidableEqNat a b)
                              a b)
                          inst inst_1 B))
                      Real Real.instAddCommMonoid
                      (@Finset.univ.{0}
                        (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.Sample.{0}
                          (Erdos390.Full.PaperHeadSimplex.Tag P)
                          (@instFintypeOption.{0}
                            (@Subtype.{1} Nat fun (p : Nat) =>
                              @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                            (@Finset.Subtype.fintype.{0} Nat P))
                          (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1}
                            (Erdos390.Full.PaperHeadSimplex.Tag P) Band
                            (@instFintypeOption.{0}
                              (@Subtype.{1} Nat fun (p : Nat) =>
                                @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                  (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P
                                  p)
                              (@Finset.Subtype.fintype.{0} Nat P))
                            (fun (a b : Erdos390.Full.PaperHeadSimplex.Tag P) =>
                              @Option.instDecidableEq.{0}
                                (@Subtype.{1} Nat fun (p : Nat) =>
                                  @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                    (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat))
                                    P p)
                                (fun
                                    (a b :
                                      @Subtype.{1} Nat fun (p : Nat) =>
                                        @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                          (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                            (@Finset.instSetLike.{0} Nat))
                                          P p) =>
                                  @Subtype.instDecidableEq.{1} Nat
                                    (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                        (@Finset.instSetLike.{0} Nat))
                                      P)
                                    instDecidableEqNat a b)
                                a b)
                            inst inst_1 B))
                        (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.sampleFintype.{0}
                          (Erdos390.Full.PaperHeadSimplex.Tag P)
                          (@instFintypeOption.{0}
                            (@Subtype.{1} Nat fun (p : Nat) =>
                              @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                            (@Finset.Subtype.fintype.{0} Nat P))
                          (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1}
                            (Erdos390.Full.PaperHeadSimplex.Tag P) Band
                            (@instFintypeOption.{0}
                              (@Subtype.{1} Nat fun (p : Nat) =>
                                @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                  (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P
                                  p)
                              (@Finset.Subtype.fintype.{0} Nat P))
                            (fun (a b : Erdos390.Full.PaperHeadSimplex.Tag P) =>
                              @Option.instDecidableEq.{0}
                                (@Subtype.{1} Nat fun (p : Nat) =>
                                  @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                    (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat))
                                    P p)
                                (fun
                                    (a b :
                                      @Subtype.{1} Nat fun (p : Nat) =>
                                        @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                          (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                            (@Finset.instSetLike.{0} Nat))
                                          P p) =>
                                  @Subtype.instDecidableEq.{1} Nat
                                    (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                        (@Finset.instSetLike.{0} Nat))
                                      P)
                                    instDecidableEqNat a b)
                                a b)
                            inst inst_1 B)))
                      fun
                        (m :
                          @Erdos390.Full.PaperBridgeFit.StructuredSampleData.Sample.{0}
                            (Erdos390.Full.PaperHeadSimplex.Tag P)
                            (@instFintypeOption.{0}
                              (@Subtype.{1} Nat fun (p : Nat) =>
                                @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                  (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P
                                  p)
                              (@Finset.Subtype.fintype.{0} Nat P))
                            (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1}
                              (Erdos390.Full.PaperHeadSimplex.Tag P) Band
                              (@instFintypeOption.{0}
                                (@Subtype.{1} Nat fun (p : Nat) =>
                                  @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                    (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat))
                                    P p)
                                (@Finset.Subtype.fintype.{0} Nat P))
                              (fun (a b : Erdos390.Full.PaperHeadSimplex.Tag P) =>
                                @Option.instDecidableEq.{0}
                                  (@Subtype.{1} Nat fun (p : Nat) =>
                                    @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                        (@Finset.instSetLike.{0} Nat))
                                      P p)
                                  (fun
                                      (a b :
                                        @Subtype.{1} Nat fun (p : Nat) =>
                                          @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                            (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                              (@Finset.instSetLike.{0} Nat))
                                            P p) =>
                                    @Subtype.instDecidableEq.{1} Nat
                                      (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                        (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                          (@Finset.instSetLike.{0} Nat))
                                        P)
                                      instDecidableEqNat a b)
                                  a b)
                              inst inst_1 B)) =>
                      @HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) (oldSeed m)
                        (Erdos390.Full.ArithmeticModel.valuation q
                          (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.value.{0}
                            (Erdos390.Full.PaperHeadSimplex.Tag P)
                            (@instFintypeOption.{0}
                              (@Subtype.{1} Nat fun (p : Nat) =>
                                @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                  (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P
                                  p)
                              (@Finset.Subtype.fintype.{0} Nat P))
                            (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1}
                              (Erdos390.Full.PaperHeadSimplex.Tag P) Band
                              (@instFintypeOption.{0}
                                (@Subtype.{1} Nat fun (p : Nat) =>
                                  @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                    (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat))
                                    P p)
                                (@Finset.Subtype.fintype.{0} Nat P))
                              (fun (a b : Erdos390.Full.PaperHeadSimplex.Tag P) =>
                                @Option.instDecidableEq.{0}
                                  (@Subtype.{1} Nat fun (p : Nat) =>
                                    @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                        (@Finset.instSetLike.{0} Nat))
                                      P p)
                                  (fun
                                      (a b :
                                        @Subtype.{1} Nat fun (p : Nat) =>
                                          @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                            (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                              (@Finset.instSetLike.{0} Nat))
                                            P p) =>
                                    @Subtype.instDecidableEq.{1} Nat
                                      (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                        (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                          (@Finset.instSetLike.{0} Nat))
                                        P)
                                      instDecidableEqNat a b)
                                  a b)
                              inst inst_1 B)
                            m)))) →
            @Erdos390.WholePaper.BankPaperRealization.BankPaperCanonicalGuardedStructuredAdditivePrebridgeMomentLedger.{0,
                  u_1}
              (Erdos390.Full.PaperHeadSimplex.Tag P) Band
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
              inst inst_1 B c depth K R certificate deltaStar betaProt
              (@Erdos390.WholePaper.BankPaperRealization.bankPaperCanonicalTwoZeroHeadCellSourceSelector.{u_1} P Band
                inst inst_1 B c depth K R certificate deltaStar betaProt oldSeed outsideSelector)
              newSeed := by
  exact @Erdos390.WholePaper.BankPaperRealization.bankPaperCanonicalGuardedStructuredAdditivePrebridgeMomentLedger_of_arbitrarySeedReplacement
