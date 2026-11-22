-- Prove2me | solution 1 for Erdos390.WholePaper.BankPaperRealization.bankPaperCanonicalTopFrozenRoundedSourceSelector_feasible_of_qTildeSource
-- status  : ACCEPTED   (prove)
-- author  : @doctosil
-- created : 2026-09-17T15:54:58.467572+00:00
-- url     : https://prove2.me/submissions/3e13dc75-1763-40a4-9a60-caef32010f0b

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

/- Source module: Erdos390.WholePaper.BankPaperCanonicalGlobalCorrectedSourceSelector -/
section


/-!
# Global corrected source selector

The original two-zero-cell source selector uses the protected-plus-active
weight on the smooth guarded broad pool and the old active ambient weight
everywhere else.  That is the right source for the Section 8 moment ledger,
but it is not the selector required by the Section 9 endpoint theorem on a
nonsmooth active row.

This file makes a rowwise compatible global replacement.  Off the smooth
broad pool it keeps the old ambient weight on complete-rough label `1`, and
uses the already constructed postcharge corrected row weight on active
nonexceptional labels, while exceptional labels are zero.  Consequently:

* once structured active values are known to lie in the complete smooth
  row, the source still agrees with the old ambient weight at every such
  coordinate outside the smooth broad pool, so the existing two-zero-cell
  prebridge ledger applies unchanged;
* every active nonsmooth guarded broad coordinate is exactly the explicit
  postcharge corrected row weight; and
* after structured placement, the two exact `hpreNonsmooth` and
  `hpreUpper` interfaces consumed by the endpoint-slack theorem are exposed.

The exact corrected-weight identity uses the literal active-nonexceptional
classification; preservation by structured placement additionally uses
smooth-row support of the structured active values.  The smooth upper theorem
honestly retains the pointwise `O(1 / L)` upper bound for the placement seed.
Existing two-zero-cell capacity only bounds the resulting selector by `1`;
it does not imply this sharper estimate.

On an active nonexceptional complete label, the outside selector intentionally
uses the full corrected-row weight, including its raw-weight branch outside
the guarded broad correction pool.  This is the rowwise selector whose total
is controlled by the postcharge construction, rather than a pointwise-only
patch of the old ambient source.  A rounded-selector input for this global
source remains explicit below; it is not manufactured from local slack.
-/

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.PaperBridgeFit
open Erdos390.Full.PaperGuardCensus

noncomputable section

namespace BankPaperRealization

/-! ## Arbitrary-seed push-forward -/

/-- Numerical head-pattern separation makes the structured value map
injective, so the ambient push-forward of an arbitrary seed at an occupied
coordinate is exactly the corresponding tagged weight.  This elementary
form is kept below the Section 8 one-shot layer so that the latter can reuse
the global source connector without an import cycle. -/
theorem bankPaperCanonicalActiveSeedAmbientWeight_eq_of_value_of_headPatternsSeparated
    {Head : Type*} [Fintype Head]
    (D : StructuredSampleData Head) (seed : D.Sample -> Real)
    (hsep : D.HeadPatternsSeparated) (m : D.Sample) :
    bankPaperCanonicalActiveSeedAmbientWeight D seed (D.value m) =
      seed m := by
  classical
  unfold bankPaperCanonicalActiveSeedAmbientWeight
  rw [Finset.sum_eq_single m]
  · simp
  · intro k _hk hkm
    rw [if_neg]
    intro hvalue
    exact hkm (D.value_injective_of_headPatternsSeparated hsep hvalue)
  · simp

/-! ## The global outside selector -/









/-! ## The global source and its exact rowwise values -/







/-! ## Compatibility with the Section 8 prebridge ledger -/



/-! ## Full Section 8 placement with the global source -/







/-! ## Exact endpoint-slack inputs after structured placement -/









end BankPaperRealization

end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankPaperCanonicalTopFrozenRoundedSourceStateConnector -/
section


/-!
# Nearest-integer source state for the frozen-top selector

The finite frozen-top source at mass `qTilde` has the paper's literal
smooth-row mass, but that mass need not be an integer.  The initialization
step replaces `qTilde` by

`q0 = nearestInteger(mFrozen + qTilde) - mFrozen`.

This connector proves the exact part of that handoff:

* changing the scaled seed from `qTilde` to `q0` changes no nonsmooth row;
* the new smooth-row total is the declared nearest integer;
* the charged nonsmooth-row equations therefore imply integrality of every
  complete rough row; and
* feasibility and exact target agreement outside the tangent prime band
  then package the result as `BankPaperCanonicalSelectorSourceState`.

The last two properties are retained as explicit premises.  They are not
consequences of row-mass rounding: feasibility is pointwise, while target
agreement is a prime-valuation identity.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.PaperBridgeFit
open Erdos390.Full.PaperGuardCensus

noncomputable section

namespace BankPaperRealization

/-! ## The exact frozen mass and nearest-integer source -/













/-! ## Nonsmooth rows are independent of the active seed -/









/-! ## Exact smooth and nonsmooth row ledgers -/











/-! ## Exact feasibility transport through the two zero cells -/

/-- Feasibility of the literal `qTilde` frozen-top source transports to the
nearest-integer source once the two changed zero-head cells satisfy their
literal capacities.  All other structured coordinates are unchanged, and
coordinates outside the structured image have zero old and new ambient
seed weight. -/
theorem bankPaperCanonicalTopFrozenRoundedSourceSelector_feasible_of_qTildeSource
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
    (T : BarycentricTarget B.sampleData)
    (deltaStar betaProt alpha betaTotal qTilde : Real)
    (hbetaProt : 0 <= betaProt)
    (hsep : B.sampleData.HeadPatternsSeparated)
    (hactiveSmooth :
      bankPaperCanonicalStructuredActiveValues B.sampleData ⊆
        R.roughCanonicalGuardedRow certificate deltaStar K 1)
    (hsource : ∀ a ∈
      R.roughCanonicalGuardedCandidateSet certificate deltaStar K,
      0 <= bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop (K := K)
          B R certificate deltaStar betaProt alpha betaTotal
            (bankPaperCanonicalScaledActiveSeed T qTilde) a ∧
        bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop (K := K)
          B R certificate deltaStar betaProt alpha betaTotal
            (bankPaperCanonicalScaledActiveSeed T qTilde) a <= 1)
    (hminus : ∀ m : B.sampleData.Sample,
      B.sampleData.cellOf m = (none, .minus) ->
        B.sampleData.value m ∈
          R.roughCanonicalGuardedBroadCorrectionPool certificate
            deltaStar B.sampleData.W K 1)
    (hplus : ∀ m : B.sampleData.Sample,
      B.sampleData.cellOf m = (none, .plus) ->
        B.sampleData.value m ∈
          R.roughCanonicalGuardedBroadCorrectionPool certificate
            deltaStar B.sampleData.W K 1)
    (hminusCapacity : ∀ m : B.sampleData.Sample,
      B.sampleData.cellOf m = (none, .minus) ->
        0 <= bankPaperCanonicalTopFrozenRoundedActiveSeed (K := K)
            B R certificate T deltaStar betaProt alpha qTilde m ∧
          betaProt / B.L +
              bankPaperCanonicalTopFrozenRoundedActiveSeed (K := K)
                B R certificate T deltaStar betaProt alpha qTilde m <= 1)
    (hplusCapacity : ∀ m : B.sampleData.Sample,
      B.sampleData.cellOf m = (none, .plus) ->
        0 <= bankPaperCanonicalTopFrozenRoundedActiveSeed (K := K)
            B R certificate T deltaStar betaProt alpha qTilde m ∧
          betaProt / B.L +
              bankPaperCanonicalTopFrozenRoundedActiveSeed (K := K)
                B R certificate T deltaStar betaProt alpha qTilde m <= 1) :
    ∀ a ∈ R.roughCanonicalGuardedCandidateSet certificate deltaStar K,
      0 <= bankPaperCanonicalTopFrozenRoundedSourceSelector (K := K)
          B R certificate T deltaStar betaProt alpha betaTotal qTilde a ∧
        bankPaperCanonicalTopFrozenRoundedSourceSelector (K := K)
          B R certificate T deltaStar betaProt alpha betaTotal qTilde a <= 1 := by
  intro a haCandidate
  by_cases hactive :
      a ∈ bankPaperCanonicalStructuredActiveValues B.sampleData
  · obtain ⟨m, rfl⟩ :=
      mem_bankPaperCanonicalStructuredActiveValues.mp hactive
    have hnewAmbient :
        bankPaperCanonicalActiveSeedAmbientWeight B.sampleData
            (bankPaperCanonicalTopFrozenRoundedActiveSeed (K := K)
              B R certificate T deltaStar betaProt alpha qTilde)
            (B.sampleData.value m) =
          bankPaperCanonicalTopFrozenRoundedActiveSeed (K := K)
            B R certificate T deltaStar betaProt alpha qTilde m :=
      bankPaperCanonicalActiveSeedAmbientWeight_eq_of_value_of_headPatternsSeparated
        B.sampleData
          (bankPaperCanonicalTopFrozenRoundedActiveSeed (K := K)
            B R certificate T deltaStar betaProt alpha qTilde)
          hsep m
    have holdAmbient :
        bankPaperCanonicalActiveSeedAmbientWeight B.sampleData
            (bankPaperCanonicalScaledActiveSeed T qTilde)
            (B.sampleData.value m) =
          bankPaperCanonicalScaledActiveSeed T qTilde m :=
      bankPaperCanonicalActiveSeedAmbientWeight_eq_of_value_of_headPatternsSeparated
        B.sampleData (bankPaperCanonicalScaledActiveSeed T qTilde) hsep m
    by_cases hmMinus :
        B.sampleData.cellOf m = (none, .minus)
    · have hmPool := hminus m hmMinus
      rw [bankPaperCanonicalTopFrozenRoundedSourceSelector,
        bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop,
        bankPaperCanonicalTwoZeroHeadCellSourceSelector, if_pos hmPool,
        hnewAmbient]
      have hcap := hminusCapacity m hmMinus
      exact
        ⟨add_nonneg (div_nonneg hbetaProt B.L_pos.le) hcap.1,
          hcap.2⟩
    · by_cases hmPlus :
          B.sampleData.cellOf m = (none, .plus)
      · have hmPool := hplus m hmPlus
        rw [bankPaperCanonicalTopFrozenRoundedSourceSelector,
          bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop,
          bankPaperCanonicalTwoZeroHeadCellSourceSelector, if_pos hmPool,
          hnewAmbient]
        have hcap := hplusCapacity m hmPlus
        exact
          ⟨add_nonneg (div_nonneg hbetaProt B.L_pos.le) hcap.1,
            hcap.2⟩
      · have hsame :
          bankPaperCanonicalTopFrozenRoundedActiveSeed (K := K)
              B R certificate T deltaStar betaProt alpha qTilde m =
            bankPaperCanonicalScaledActiveSeed T qTilde m := by
          simp [bankPaperCanonicalTopFrozenRoundedActiveSeed,
            bankPaperCanonicalTwoZeroHeadCellRebalance,
            bankPaperCanonicalUniformCellIncrement, hmMinus, hmPlus]
        have hsourceEq :
            bankPaperCanonicalTopFrozenRoundedSourceSelector (K := K)
                B R certificate T deltaStar betaProt alpha betaTotal
                  qTilde (B.sampleData.value m) =
              bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop (K := K)
                B R certificate deltaStar betaProt alpha betaTotal
                  (bankPaperCanonicalScaledActiveSeed T qTilde)
                    (B.sampleData.value m) := by
          have hmSmooth :=
            hactiveSmooth
              (mem_bankPaperCanonicalStructuredActiveValues.mpr ⟨m, rfl⟩)
          have hmLabel :
              completeRoughLabel (yNat B.sampleData.n)
                  (B.sampleData.value m) = 1 :=
            (mem_completeRoughRowFiber.mp hmSmooth).2
          by_cases hmPool :
              B.sampleData.value m ∈
                R.roughCanonicalGuardedBroadCorrectionPool certificate
                  deltaStar B.sampleData.W K 1
          · simp only [bankPaperCanonicalTopFrozenRoundedSourceSelector,
              bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop,
              bankPaperCanonicalTwoZeroHeadCellSourceSelector, hmPool,
              if_true, hnewAmbient, holdAmbient, hsame]
          · simp only [bankPaperCanonicalTopFrozenRoundedSourceSelector,
              bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop,
              bankPaperCanonicalTwoZeroHeadCellSourceSelector, hmPool,
              if_false,
              bankPaperCanonicalGlobalCorrectedOutsideSelectorWithTop,
              hmLabel, if_true, hnewAmbient, holdAmbient, hsame]
        rw [hsourceEq]
        exact hsource (B.sampleData.value m) haCandidate
  · have hnewZero :
        bankPaperCanonicalActiveSeedAmbientWeight B.sampleData
            (bankPaperCanonicalTopFrozenRoundedActiveSeed (K := K)
              B R certificate T deltaStar betaProt alpha qTilde) a = 0 := by
      apply bankPaperCanonicalActiveSeedAmbientWeight_eq_zero_of_not_value
      intro m hma
      exact hactive
        (mem_bankPaperCanonicalStructuredActiveValues.mpr ⟨m, hma⟩)
    have holdZero :
        bankPaperCanonicalActiveSeedAmbientWeight B.sampleData
            (bankPaperCanonicalScaledActiveSeed T qTilde) a = 0 := by
      apply bankPaperCanonicalActiveSeedAmbientWeight_eq_zero_of_not_value
      intro m hma
      exact hactive
        (mem_bankPaperCanonicalStructuredActiveValues.mpr ⟨m, hma⟩)
    have hsourceEq :
        bankPaperCanonicalTopFrozenRoundedSourceSelector (K := K)
            B R certificate T deltaStar betaProt alpha betaTotal qTilde a =
          bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop (K := K)
            B R certificate deltaStar betaProt alpha betaTotal
              (bankPaperCanonicalScaledActiveSeed T qTilde) a := by
      by_cases haPool :
          a ∈ R.roughCanonicalGuardedBroadCorrectionPool certificate
            deltaStar B.sampleData.W K 1
      · simp only [bankPaperCanonicalTopFrozenRoundedSourceSelector,
          bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop,
          bankPaperCanonicalTwoZeroHeadCellSourceSelector, haPool, if_true,
          hnewZero, holdZero]
      · by_cases haLabel :
          completeRoughLabel (yNat B.sampleData.n) a = 1
        · simp only [bankPaperCanonicalTopFrozenRoundedSourceSelector,
            bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop,
            bankPaperCanonicalTwoZeroHeadCellSourceSelector, haPool, if_false,
            bankPaperCanonicalGlobalCorrectedOutsideSelectorWithTop,
            haLabel, if_true, hnewZero, holdZero]
        · simp only [bankPaperCanonicalTopFrozenRoundedSourceSelector,
            bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop,
            bankPaperCanonicalTwoZeroHeadCellSourceSelector, haPool, if_false,
            bankPaperCanonicalGlobalCorrectedOutsideSelectorWithTop,
            haLabel, if_false]
    rw [hsourceEq]
    exact hsource a haCandidate

/-! ## Complete-row integrality and the source-state handoff -/







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
  (T :
    @Erdos390.Full.PaperGuardCensus.BarycentricTarget.{0} (Erdos390.Full.PaperHeadSimplex.Tag P)
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
  (deltaStar betaProt alpha betaTotal qTilde : Real),
  @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) betaProt →
    @Erdos390.Full.PaperBridgeFit.StructuredSampleData.HeadPatternsSeparated.{0} (Erdos390.Full.PaperHeadSimplex.Tag P)
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
                                    (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat))
                                    P p) =>
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
                                    (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat))
                                    P p) =>
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
                                    (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat))
                                    P p) =>
                            @Subtype.instDecidableEq.{1} Nat
                              (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P)
                              instDecidableEqNat a b)
                          a b)
                      inst inst_1 B))))
              R depth)
            R certificate deltaStar K (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
        (∀ (a : Nat),
            @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat))
                (@Erdos390.WholePaper.BankPaperRealization.roughCanonicalGuardedCandidateSet c depth
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
                        inst inst_1 B)))
                  (@Erdos390.WholePaper.BankPaperRealization.anchorGuardLeftCore
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
                            inst inst_1 B))))
                    R)
                  (@Erdos390.WholePaper.BankPaperRealization.anchorGuardRightCore
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
                            inst inst_1 B))))
                    R)
                  (@Erdos390.WholePaper.BankPaperRealization.centralChangedMarkers
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
                            inst inst_1 B))))
                    R depth)
                  R certificate deltaStar K)
                a →
              And
                (@LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
                  (@Erdos390.WholePaper.BankPaperRealization.bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop.{u_1}
                    P Band inst inst_1 B c depth K R certificate deltaStar betaProt alpha betaTotal
                    (@Erdos390.WholePaper.bankPaperCanonicalScaledActiveSeed.{0} (Erdos390.Full.PaperHeadSimplex.Tag P)
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
                        inst inst_1 B)
                      T qTilde)
                    a))
                (@LE.le.{0} Real Real.instLE
                  (@Erdos390.WholePaper.BankPaperRealization.bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop.{u_1}
                    P Band inst inst_1 B c depth K R certificate deltaStar betaProt alpha betaTotal
                    (@Erdos390.WholePaper.bankPaperCanonicalScaledActiveSeed.{0} (Erdos390.Full.PaperHeadSimplex.Tag P)
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
                        inst inst_1 B)
                      T qTilde)
                    a)
                  (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))) →
          (∀
              (m :
                @Erdos390.Full.PaperBridgeFit.StructuredSampleData.Sample.{0} (Erdos390.Full.PaperHeadSimplex.Tag P)
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
                    inst inst_1 B)),
              @Eq.{1} (Erdos390.Full.PaperBridgeFit.Cell.{0} (Erdos390.Full.PaperHeadSimplex.Tag P))
                  (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.cellOf.{0} (Erdos390.Full.PaperHeadSimplex.Tag P)
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
                      inst inst_1 B)
                    m)
                  (@Prod.mk.{0, 0}
                    (Option.{0}
                      (@Subtype.{1} Nat fun (p : Nat) =>
                        @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                          (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p))
                    Erdos390.Full.PaperBridgeFit.PhysicalSign
                    (@Option.none.{0}
                      (@Subtype.{1} Nat fun (p : Nat) =>
                        @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                          (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p))
                    Erdos390.Full.PaperBridgeFit.PhysicalSign.minus) →
                @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                  (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat))
                  (@Erdos390.WholePaper.BankPaperRealization.roughCanonicalGuardedBroadCorrectionPool c depth
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
                          inst inst_1 B)))
                    (@Erdos390.WholePaper.BankPaperRealization.anchorGuardLeftCore
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
                        (Erdos390.WholePaper.upperTailLength c
                          (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0}
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
                              inst inst_1 B))))
                      R)
                    (@Erdos390.WholePaper.BankPaperRealization.anchorGuardRightCore
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
                        (Erdos390.WholePaper.upperTailLength c
                          (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0}
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
                              inst inst_1 B))))
                      R)
                    (@Erdos390.WholePaper.BankPaperRealization.centralChangedMarkers
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
                        (Erdos390.WholePaper.upperTailLength c
                          (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0}
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
                              inst inst_1 B))))
                      R depth)
                    R certificate deltaStar
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
                        inst inst_1 B))
                    K (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                  (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.value.{0} (Erdos390.Full.PaperHeadSimplex.Tag P)
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
                      inst inst_1 B)
                    m)) →
            (∀
                (m :
                  @Erdos390.Full.PaperBridgeFit.StructuredSampleData.Sample.{0} (Erdos390.Full.PaperHeadSimplex.Tag P)
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
                      inst inst_1 B)),
                @Eq.{1} (Erdos390.Full.PaperBridgeFit.Cell.{0} (Erdos390.Full.PaperHeadSimplex.Tag P))
                    (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.cellOf.{0}
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
                        inst inst_1 B)
                      m)
                    (@Prod.mk.{0, 0}
                      (Option.{0}
                        (@Subtype.{1} Nat fun (p : Nat) =>
                          @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                            (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p))
                      Erdos390.Full.PaperBridgeFit.PhysicalSign
                      (@Option.none.{0}
                        (@Subtype.{1} Nat fun (p : Nat) =>
                          @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                            (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p))
                      Erdos390.Full.PaperBridgeFit.PhysicalSign.plus) →
                  @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                    (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat))
                    (@Erdos390.WholePaper.BankPaperRealization.roughCanonicalGuardedBroadCorrectionPool c depth
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
                      (@Erdos390.WholePaper.BankPaperRealization.anchorGuardLeftCore
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
                        (Erdos390.WholePaper.upperEndpoint
                          (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0}
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
                              inst inst_1 B))
                          (Erdos390.WholePaper.upperTailLength c
                            (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0}
                              (Erdos390.Full.PaperHeadSimplex.Tag P)
                              (@instFintypeOption.{0}
                                (@Subtype.{1} Nat fun (p : Nat) =>
                                  @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                    (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat))
                                    P p)
                                (@Finset.Subtype.fintype.{0} Nat P))
                              (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1}
                                (Erdos390.Full.PaperHeadSimplex.Tag P) Band
                                (@instFintypeOption.{0}
                                  (@Subtype.{1} Nat fun (p : Nat) =>
                                    @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                        (@Finset.instSetLike.{0} Nat))
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
                                inst inst_1 B))))
                        R)
                      (@Erdos390.WholePaper.BankPaperRealization.anchorGuardRightCore
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
                        (Erdos390.WholePaper.upperEndpoint
                          (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0}
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
                              inst inst_1 B))
                          (Erdos390.WholePaper.upperTailLength c
                            (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0}
                              (Erdos390.Full.PaperHeadSimplex.Tag P)
                              (@instFintypeOption.{0}
                                (@Subtype.{1} Nat fun (p : Nat) =>
                                  @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                    (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat))
                                    P p)
                                (@Finset.Subtype.fintype.{0} Nat P))
                              (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1}
                                (Erdos390.Full.PaperHeadSimplex.Tag P) Band
                                (@instFintypeOption.{0}
                                  (@Subtype.{1} Nat fun (p : Nat) =>
                                    @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                        (@Finset.instSetLike.{0} Nat))
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
                                inst inst_1 B))))
                        R)
                      (@Erdos390.WholePaper.BankPaperRealization.centralChangedMarkers
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
                        (Erdos390.WholePaper.upperEndpoint
                          (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0}
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
                              inst inst_1 B))
                          (Erdos390.WholePaper.upperTailLength c
                            (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0}
                              (Erdos390.Full.PaperHeadSimplex.Tag P)
                              (@instFintypeOption.{0}
                                (@Subtype.{1} Nat fun (p : Nat) =>
                                  @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                    (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat))
                                    P p)
                                (@Finset.Subtype.fintype.{0} Nat P))
                              (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1}
                                (Erdos390.Full.PaperHeadSimplex.Tag P) Band
                                (@instFintypeOption.{0}
                                  (@Subtype.{1} Nat fun (p : Nat) =>
                                    @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                        (@Finset.instSetLike.{0} Nat))
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
                                inst inst_1 B))))
                        R depth)
                      R certificate deltaStar
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
                      K (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                    (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.value.{0} (Erdos390.Full.PaperHeadSimplex.Tag P)
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
                        inst inst_1 B)
                      m)) →
              (∀
                  (m :
                    @Erdos390.Full.PaperBridgeFit.StructuredSampleData.Sample.{0} (Erdos390.Full.PaperHeadSimplex.Tag P)
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
                        inst inst_1 B)),
                  @Eq.{1} (Erdos390.Full.PaperBridgeFit.Cell.{0} (Erdos390.Full.PaperHeadSimplex.Tag P))
                      (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.cellOf.{0}
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
                          inst inst_1 B)
                        m)
                      (@Prod.mk.{0, 0}
                        (Option.{0}
                          (@Subtype.{1} Nat fun (p : Nat) =>
                            @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                              (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p))
                        Erdos390.Full.PaperBridgeFit.PhysicalSign
                        (@Option.none.{0}
                          (@Subtype.{1} Nat fun (p : Nat) =>
                            @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                              (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p))
                        Erdos390.Full.PaperBridgeFit.PhysicalSign.minus) →
                    And
                      (@LE.le.{0} Real Real.instLE
                        (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
                        (@Erdos390.WholePaper.BankPaperRealization.bankPaperCanonicalTopFrozenRoundedActiveSeed.{u_1} P
                          Band inst inst_1 B c depth K R certificate T deltaStar betaProt alpha qTilde m))
                      (@LE.le.{0} Real Real.instLE
                        (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                          (@HDiv.hDiv.{0, 0, 0} Real Real Real
                            (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid)) betaProt
                            (@Erdos390.Full.PaperBridgeFit.BridgeData.L.{0, u_1} (Erdos390.Full.PaperHeadSimplex.Tag P)
                              Band
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
                              inst inst_1 B))
                          (@Erdos390.WholePaper.BankPaperRealization.bankPaperCanonicalTopFrozenRoundedActiveSeed.{u_1}
                            P Band inst inst_1 B c depth K R certificate T deltaStar betaProt alpha qTilde m))
                        (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))) →
                (∀
                    (m :
                      @Erdos390.Full.PaperBridgeFit.StructuredSampleData.Sample.{0}
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
                          inst inst_1 B)),
                    @Eq.{1} (Erdos390.Full.PaperBridgeFit.Cell.{0} (Erdos390.Full.PaperHeadSimplex.Tag P))
                        (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.cellOf.{0}
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
                            inst inst_1 B)
                          m)
                        (@Prod.mk.{0, 0}
                          (Option.{0}
                            (@Subtype.{1} Nat fun (p : Nat) =>
                              @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P
                                p))
                          Erdos390.Full.PaperBridgeFit.PhysicalSign
                          (@Option.none.{0}
                            (@Subtype.{1} Nat fun (p : Nat) =>
                              @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P
                                p))
                          Erdos390.Full.PaperBridgeFit.PhysicalSign.plus) →
                      And
                        (@LE.le.{0} Real Real.instLE
                          (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
                          (@Erdos390.WholePaper.BankPaperRealization.bankPaperCanonicalTopFrozenRoundedActiveSeed.{u_1}
                            P Band inst inst_1 B c depth K R certificate T deltaStar betaProt alpha qTilde m))
                        (@LE.le.{0} Real Real.instLE
                          (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                            (@HDiv.hDiv.{0, 0, 0} Real Real Real
                              (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid)) betaProt
                              (@Erdos390.Full.PaperBridgeFit.BridgeData.L.{0, u_1}
                                (Erdos390.Full.PaperHeadSimplex.Tag P) Band
                                (@instFintypeOption.{0}
                                  (@Subtype.{1} Nat fun (p : Nat) =>
                                    @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                        (@Finset.instSetLike.{0} Nat))
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
                                inst inst_1 B))
                            (@Erdos390.WholePaper.BankPaperRealization.bankPaperCanonicalTopFrozenRoundedActiveSeed.{u_1}
                              P Band inst inst_1 B c depth K R certificate T deltaStar betaProt alpha qTilde m))
                          (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))) →
                  ∀ (a : Nat),
                    @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                        (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat))
                        (@Erdos390.WholePaper.BankPaperRealization.roughCanonicalGuardedCandidateSet c depth
                          (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0}
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
                              inst inst_1 B))
                          (Erdos390.WholePaper.upperTailLength c
                            (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0}
                              (Erdos390.Full.PaperHeadSimplex.Tag P)
                              (@instFintypeOption.{0}
                                (@Subtype.{1} Nat fun (p : Nat) =>
                                  @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                    (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat))
                                    P p)
                                (@Finset.Subtype.fintype.{0} Nat P))
                              (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1}
                                (Erdos390.Full.PaperHeadSimplex.Tag P) Band
                                (@instFintypeOption.{0}
                                  (@Subtype.{1} Nat fun (p : Nat) =>
                                    @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                        (@Finset.instSetLike.{0} Nat))
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
                                inst inst_1 B)))
                          (@Erdos390.WholePaper.BankPaperRealization.anchorGuardLeftCore
                            (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0}
                              (Erdos390.Full.PaperHeadSimplex.Tag P)
                              (@instFintypeOption.{0}
                                (@Subtype.{1} Nat fun (p : Nat) =>
                                  @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                    (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat))
                                    P p)
                                (@Finset.Subtype.fintype.{0} Nat P))
                              (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1}
                                (Erdos390.Full.PaperHeadSimplex.Tag P) Band
                                (@instFintypeOption.{0}
                                  (@Subtype.{1} Nat fun (p : Nat) =>
                                    @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                        (@Finset.instSetLike.{0} Nat))
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
                                inst inst_1 B))
                            (Erdos390.WholePaper.upperEndpoint
                              (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0}
                                (Erdos390.Full.PaperHeadSimplex.Tag P)
                                (@instFintypeOption.{0}
                                  (@Subtype.{1} Nat fun (p : Nat) =>
                                    @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                        (@Finset.instSetLike.{0} Nat))
                                      P p)
                                  (@Finset.Subtype.fintype.{0} Nat P))
                                (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1}
                                  (Erdos390.Full.PaperHeadSimplex.Tag P) Band
                                  (@instFintypeOption.{0}
                                    (@Subtype.{1} Nat fun (p : Nat) =>
                                      @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                        (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                          (@Finset.instSetLike.{0} Nat))
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
                                  inst inst_1 B))
                              (Erdos390.WholePaper.upperTailLength c
                                (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0}
                                  (Erdos390.Full.PaperHeadSimplex.Tag P)
                                  (@instFintypeOption.{0}
                                    (@Subtype.{1} Nat fun (p : Nat) =>
                                      @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                        (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                          (@Finset.instSetLike.{0} Nat))
                                        P p)
                                    (@Finset.Subtype.fintype.{0} Nat P))
                                  (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1}
                                    (Erdos390.Full.PaperHeadSimplex.Tag P) Band
                                    (@instFintypeOption.{0}
                                      (@Subtype.{1} Nat fun (p : Nat) =>
                                        @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                          (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                            (@Finset.instSetLike.{0} Nat))
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
                                    inst inst_1 B))))
                            R)
                          (@Erdos390.WholePaper.BankPaperRealization.anchorGuardRightCore
                            (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0}
                              (Erdos390.Full.PaperHeadSimplex.Tag P)
                              (@instFintypeOption.{0}
                                (@Subtype.{1} Nat fun (p : Nat) =>
                                  @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                    (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat))
                                    P p)
                                (@Finset.Subtype.fintype.{0} Nat P))
                              (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1}
                                (Erdos390.Full.PaperHeadSimplex.Tag P) Band
                                (@instFintypeOption.{0}
                                  (@Subtype.{1} Nat fun (p : Nat) =>
                                    @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                        (@Finset.instSetLike.{0} Nat))
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
                                inst inst_1 B))
                            (Erdos390.WholePaper.upperEndpoint
                              (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0}
                                (Erdos390.Full.PaperHeadSimplex.Tag P)
                                (@instFintypeOption.{0}
                                  (@Subtype.{1} Nat fun (p : Nat) =>
                                    @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                        (@Finset.instSetLike.{0} Nat))
                                      P p)
                                  (@Finset.Subtype.fintype.{0} Nat P))
                                (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1}
                                  (Erdos390.Full.PaperHeadSimplex.Tag P) Band
                                  (@instFintypeOption.{0}
                                    (@Subtype.{1} Nat fun (p : Nat) =>
                                      @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                        (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                          (@Finset.instSetLike.{0} Nat))
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
                                  inst inst_1 B))
                              (Erdos390.WholePaper.upperTailLength c
                                (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0}
                                  (Erdos390.Full.PaperHeadSimplex.Tag P)
                                  (@instFintypeOption.{0}
                                    (@Subtype.{1} Nat fun (p : Nat) =>
                                      @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                        (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                          (@Finset.instSetLike.{0} Nat))
                                        P p)
                                    (@Finset.Subtype.fintype.{0} Nat P))
                                  (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1}
                                    (Erdos390.Full.PaperHeadSimplex.Tag P) Band
                                    (@instFintypeOption.{0}
                                      (@Subtype.{1} Nat fun (p : Nat) =>
                                        @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                          (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                            (@Finset.instSetLike.{0} Nat))
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
                                    inst inst_1 B))))
                            R)
                          (@Erdos390.WholePaper.BankPaperRealization.centralChangedMarkers
                            (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0}
                              (Erdos390.Full.PaperHeadSimplex.Tag P)
                              (@instFintypeOption.{0}
                                (@Subtype.{1} Nat fun (p : Nat) =>
                                  @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                    (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat))
                                    P p)
                                (@Finset.Subtype.fintype.{0} Nat P))
                              (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1}
                                (Erdos390.Full.PaperHeadSimplex.Tag P) Band
                                (@instFintypeOption.{0}
                                  (@Subtype.{1} Nat fun (p : Nat) =>
                                    @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                        (@Finset.instSetLike.{0} Nat))
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
                                inst inst_1 B))
                            (Erdos390.WholePaper.upperEndpoint
                              (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0}
                                (Erdos390.Full.PaperHeadSimplex.Tag P)
                                (@instFintypeOption.{0}
                                  (@Subtype.{1} Nat fun (p : Nat) =>
                                    @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                        (@Finset.instSetLike.{0} Nat))
                                      P p)
                                  (@Finset.Subtype.fintype.{0} Nat P))
                                (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1}
                                  (Erdos390.Full.PaperHeadSimplex.Tag P) Band
                                  (@instFintypeOption.{0}
                                    (@Subtype.{1} Nat fun (p : Nat) =>
                                      @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                        (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                          (@Finset.instSetLike.{0} Nat))
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
                                  inst inst_1 B))
                              (Erdos390.WholePaper.upperTailLength c
                                (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0}
                                  (Erdos390.Full.PaperHeadSimplex.Tag P)
                                  (@instFintypeOption.{0}
                                    (@Subtype.{1} Nat fun (p : Nat) =>
                                      @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                        (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                          (@Finset.instSetLike.{0} Nat))
                                        P p)
                                    (@Finset.Subtype.fintype.{0} Nat P))
                                  (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1}
                                    (Erdos390.Full.PaperHeadSimplex.Tag P) Band
                                    (@instFintypeOption.{0}
                                      (@Subtype.{1} Nat fun (p : Nat) =>
                                        @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                          (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                            (@Finset.instSetLike.{0} Nat))
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
                                    inst inst_1 B))))
                            R depth)
                          R certificate deltaStar K)
                        a →
                      And
                        (@LE.le.{0} Real Real.instLE
                          (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
                          (@Erdos390.WholePaper.BankPaperRealization.bankPaperCanonicalTopFrozenRoundedSourceSelector.{u_1}
                            P Band inst inst_1 B c depth K R certificate T deltaStar betaProt alpha betaTotal qTilde a))
                        (@LE.le.{0} Real Real.instLE
                          (@Erdos390.WholePaper.BankPaperRealization.bankPaperCanonicalTopFrozenRoundedSourceSelector.{u_1}
                            P Band inst inst_1 B c depth K R certificate T deltaStar betaProt alpha betaTotal qTilde a)
                          (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))) := by
  exact @Erdos390.WholePaper.BankPaperRealization.bankPaperCanonicalTopFrozenRoundedSourceSelector_feasible_of_qTildeSource
