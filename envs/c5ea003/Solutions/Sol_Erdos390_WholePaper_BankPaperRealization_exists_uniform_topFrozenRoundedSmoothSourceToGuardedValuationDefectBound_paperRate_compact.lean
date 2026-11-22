-- Prove2me | solution 1 for Erdos390.WholePaper.BankPaperRealization.exists_uniform_topFrozenRoundedSmoothSourceToGuardedValuationDefectBound_paperRate_compact
-- status  : ACCEPTED   (prove)
-- author  : @doctosil
-- created : 2026-09-17T17:30:02.43684+00:00
-- url     : https://prove2.me/submissions/1c4caa08-4e35-4a8f-8e7a-6e99d0e6204b

import Definitions.Def_erdos390_remaining_analytic_propositions_007
import Mathlib
import Definitions.Def_erdos390_source_bank_interface
import Definitions.Def_erdos390_dickman_step_function
import Theorems.Thm_MediumPNT
import Definitions.Def_erdos390_analytic_foundations_001
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_product_bound
import Theorems.Thm_Erdos390_Full_DickmanBasic_rho_pos_on_zero_five
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_secondDerivative_first_bound
import Definitions.Def_erdos390_analytic_foundations_002
import Definitions.Def_erdos390_analytic_foundations_004
import Definitions.Def_erdos390_analytic_foundations_006
import Definitions.Def_erdos390_analytic_foundations_007
import Definitions.Def_erdos390_analytic_foundations_008
import Definitions.Def_erdos390_analytic_foundations_009
import Definitions.Def_erdos390_analytic_foundations_010
import Theorems.Thm_Erdos390_WholePaper_BankPaperRealization_exists_uniform_guardedRawCell_valuation_mean_profiles_paperRate_compact
import Theorems.Thm_Erdos390_WholePaper_BankPaperRealization_exists_uniform_guardedSmoothBasePool_valuation_mean_profile_paperRate_compact
import Theorems.Thm_Erdos390_WholePaper_BankPaperRealization_roughCanonicalTopFrozenRoundedSmoothSourceToGuardedValuationDefect_eq_roundedActive_sub_guardedBase



section
theorem Erdos390.WholePaper.BankPaperRealization.exists_uniform_guardedSmoothBasePool_valuation_mean_profile_paperRate : Erdos390.RemainingAnalyticGoal007_006 := @Erdos390.WholePaper.BankPaperRealization.exists_uniform_guardedSmoothBasePool_valuation_mean_profile_paperRate_compact
end
section
universe u_1
theorem Erdos390.WholePaper.BankPaperRealization.exists_uniform_guardedRawCell_valuation_mean_profiles_paperRate : Erdos390.RemainingAnalyticGoal007_005.{u_1} := @Erdos390.WholePaper.BankPaperRealization.exists_uniform_guardedRawCell_valuation_mean_profiles_paperRate_compact
end
/- Source module: Erdos390.Full.UniformFiniteProbability -/
section


/-!
# Uniform probability on an actual finite cell

This is the exact bridge between counting averages on a finite arithmetic
cell and the `FiniteProbability` objects used by the tilt and covariance
modules.  Nonemptiness is explicit, so normalization never divides by a
silently vanishing cell cardinality.
-/

open scoped BigOperators

namespace Erdos390.Full

noncomputable section

namespace FiniteProbability

variable {Alpha : Type*}





/-- Expectation under the uniform law is the literal subtype sum divided by
the actual cell cardinality. -/
theorem uniformOnFinset_expect_eq (S : Finset Alpha) (hS : S.Nonempty)
    (F : S → ℝ) :
    (uniformOnFinset S hS).expect F =
      (∑ x : S, F x) / (S.card : ℝ) := by
  unfold expect
  calc
    (∑ x : S, (1 / (S.card : ℝ)) * F x) =
        (1 / (S.card : ℝ)) * ∑ x : S, F x := by
      rw [Finset.mul_sum]
    _ = (∑ x : S, F x) / (S.card : ℝ) := by ring

/-- Subtype summation is exactly the usual filtered finset summation. -/
theorem sum_subtype_eq_sum_filter (S : Finset Alpha) (F : Alpha → ℝ) :
    (∑ x : S, F x) = ∑ x ∈ S, F x := by
  exact Finset.sum_coe_sort S F

/-- Expectation written with the ambient function and the literal cell
cardinality. -/
theorem uniformOnFinset_expect_ambient_eq
    (S : Finset Alpha) (hS : S.Nonempty) (F : Alpha → ℝ) :
    (uniformOnFinset S hS).expect (fun x : S ↦ F x) =
      (∑ x ∈ S, F x) / (S.card : ℝ) := by
  rw [uniformOnFinset_expect_eq, sum_subtype_eq_sum_filter]

end FiniteProbability

end

end Erdos390.Full

end

/- Source module: Erdos390.Full.PaperCanonicalMediumNuisanceRows -/
section


/-!
# Canonical raw-cell attachment for the medium nuisance rows

This file contains the dependent-type bookkeeping which identifies the
guard-deleted exponential tilt on a literal raw structured cell with the
`cellMediumLaw` carried by canonical `BridgeData`.  In particular, later
moving-prefix and prime-power estimates can be proved on the raw cell and
transported to the exact laws used by the nuisance Schur complement without
an unrecorded change of sample space.
-/

open scoped BigOperators

namespace Erdos390.Full

noncomputable section

open ArithmeticModel ArithmeticBandGeometry FiniteProbability
open PaperGuardCensus GuardedUniformCell ValuationScoreDomination

namespace FiniteProbability

variable {Alpha : Type*}

/-- Equality of the underlying finite sets, together with pointwise equality
of the scores and statistics, gives literal equality of tilted expectations.
The formulation is useful when the equality changes a subtype. -/
theorem uniformOnFinset_exponentialTilt_expect_eq_of_finset_eq
    (S T : Finset Alpha) (hST : S = T)
    (hS : S.Nonempty) (hT : T.Nonempty)
    (scoreS : S → ℝ) (scoreT : T → ℝ)
    (hscore : ∀ (x : S) (y : T), (x : Alpha) = (y : Alpha) →
      scoreS x = scoreT y)
    (F : Alpha → ℝ) :
    ((uniformOnFinset S hS).exponentialTilt scoreS).expect
        (fun x ↦ F (x : Alpha)) =
      ((uniformOnFinset T hT).exponentialTilt scoreT).expect
        (fun x ↦ F (x : Alpha)) := by
  subst T
  have hscoreEq : scoreS = scoreT := by
    funext x
    exact hscore x x rfl
  subst scoreT
  have hproof : hS = hT := Subsingleton.elim _ _
  subst hT
  rfl



end FiniteProbability

namespace PaperBridgeFit

open HeadPattern

namespace BridgeData

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]
  (B : BridgeData Head Band)











end BridgeData

end PaperBridgeFit

end

end Erdos390.Full

end

/- Source module: Erdos390.WholePaper.UpperScale -/
section


/-!
# Elementary scale facts for the upper bound

This module isolates the exact ceiling and endpoint used on the upper-bound
side of the paper.  Every asymptotic statement is proved directly from
elementary real-logarithm limits.  No prime-counting input is used.
-/

open Filter Topology

namespace Erdos390.WholePaper

noncomputable section









/-- A pointwise positivity criterion for the second-order scale. -/
theorem secondOrderScale_pos {n : ℕ} (hn : 2 ≤ n) :
    0 < secondOrderScale n := by
  rw [secondOrderScale]
  exact div_pos (by positivity)
    (Real.log_pos (by exact_mod_cast hn))

































end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankPaperCanonicalSmoothQuotaHeightLedger -/
section


/-!
# The exact smooth-row quota and height ledger from Section 8

This file records the algebraic part of the paper's smooth-row initialization
without replacing any actual finite mass by an asymptotic main term.

The literal active base component is the constant weight `betaAct / L n` on
the head-free, `yNat n`-smooth part of the broad interval.  Its exact support
is the complete-rough row with label one.  The later definitions follow the
paper verbatim:

* `Q_sm(0)` is the nearest integer to `m_sm,fr + qTilde`, with a half-integer
  tie sent to the smaller integer;
* `q0 = Q_sm(0) - m_sm,fr`;
* `Q_sm(d) = Q_sm(0) - d` and `qAct(d) = q0 - d`;
* `A0 = logY - Lambda0 - q0 * L` and `A(d) = A0 + d * L`;
* `d` is the tie-lower nearest integer to
  `(mu * q0 - A0) / (L + mu)`.

All displayed identities and the two nearest-integer errors are unconditional.
The analytic comparison between the raw base mass and the actual post-guard
mass is deliberately left to the companion asymptotic module.
-/

open Filter Topology
open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.Scale

noncomputable section

/-! ## The literal rough smooth base component -/

















/-! ## Tie-lower nearest integers -/









/-- The universal half-unit rounding error. -/
theorem bankPaperNearestIntegerTieLower_abs_sub_le (x : Real) :
    |(bankPaperNearestIntegerTieLower x : Real) - x| ≤ 1 / 2 := by
  have hcell :=
    (bankPaperNearestIntegerTieLower_eq_iff x
      (bankPaperNearestIntegerTieLower x)).1 rfl
  apply abs_le.mpr
  constructor <;> linarith

/-! ## Exact smooth-row quota initialization -/







/-- Exact expression for the initialization error. -/
theorem bankPaperCanonicalSmoothInitialActiveMass_sub_actual
    (mFrozen qTilde : Real) :
    bankPaperCanonicalSmoothInitialActiveMass mFrozen qTilde - qTilde =
      (bankPaperCanonicalSmoothInitialQuota mFrozen qTilde : Real) -
        (mFrozen + qTilde) := by
  unfold bankPaperCanonicalSmoothInitialActiveMass
  ring

/-- The paper's literal bound `|q0 - qTilde| <= 1/2`. -/
theorem bankPaperCanonicalSmoothInitialActiveMass_abs_sub_actual_le
    (mFrozen qTilde : Real) :
    |bankPaperCanonicalSmoothInitialActiveMass mFrozen qTilde - qTilde| ≤
      1 / 2 := by
  rw [bankPaperCanonicalSmoothInitialActiveMass_sub_actual]
  exact bankPaperNearestIntegerTieLower_abs_sub_le (mFrozen + qTilde)

















/-! ## Exact frozen-height ledger and centered adjustment -/



























/-! ## Literal Section 8 families -/

























end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankPaperCanonicalSmoothQuotaHeightAsymptotic -/
section


/-!
# The analytic Section 8 smooth-row quota and height bridge

The raw active smooth component from the exact companion file has a positive
`n / log n` lower bound by the repository's uniform de Bruijn--Saias and
fixed-head estimates.  This file proves that bound directly for complete-
rough label one, then propagates it through the exact nearest-integer and
height-center constructions.

Only one repository-level analytic ledger remains absent.  It is named
`BankPaperCanonicalSectionEightAnalyticLedger` below and contains exactly:

* the actual post-guard smooth mass differs from the explicit raw base mass
  by `o(n / log n)`;
* the literal frozen height defect `A0` is `O(n / log n)`.

These are precisely the two estimates asserted together in the paper's
Section 8 frozen ledger.  No selector, active-measure, or positivity premise
is hidden in that predicate.  Every consequence after it, including
`d = O(n / log^2 n)` and the positive lower bound for `q0 - d`, is proved
here.
-/

open Filter Topology Asymptotics

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.DickmanBasic
open Erdos390.Full.PaperGuardCensus
open Erdos390.Full.Scale
open Erdos390.Full.StructuredCells

noncomputable section

/-! ## The label-one raw base pool is macroscopically large -/











/-! ## The exact missing analytic ledger -/



/-! ## Nearest-integer initialization preserves the paper scale -/











/-! ## The logarithmically smaller height adjustment -/

/-- The paper's scale `n / log^2 n` tends to infinity. -/
theorem secondOrderScale_div_L_tendsto_atTop :
    Tendsto (fun n : Nat => secondOrderScale n / L n) atTop atTop := by
  have hzero : Tendsto
      (fun n : Nat => L n ^ 2 / (n : Real)) atTop (nhds 0) := by
    simpa only [L, Function.comp_apply, id_eq] using
      ((Real.isLittleO_pow_log_id_atTop (n := 2)).comp_tendsto
        (tendsto_natCast_atTop_atTop (R := Real))).tendsto_div_nhds_zero
  have hpos : ∀ᶠ n : Nat in atTop,
      0 < L n ^ 2 / (n : Real) := by
    filter_upwards [eventually_gt_atTop 1] with n hn
    exact div_pos (pow_pos (L_pos hn) 2) (by positivity)
  have hright : Tendsto
      (fun n : Nat => L n ^ 2 / (n : Real)) atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨hzero, hpos⟩
  apply hright.inv_tendsto_nhdsGT_zero.congr'
  filter_upwards [eventually_gt_atTop 1] with n hn
  have hL : 0 < L n := L_pos hn
  have hnReal : (n : Real) ≠ 0 := by positivity
  apply (eq_div_iff hL.ne').2
  change (L n ^ 2 / (n : Real))⁻¹ * L n = (n : Real) / L n
  rw [inv_div]
  field_simp [hL.ne', hnReal]





/-! ## Full propagation from the minimal missing ledger -/















end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankPaperCanonicalMediumPrimeStructuredPlacementMomentRateConnector -/
section


/-!
# Medium-prime rate for the structured two-zero-cell placement moment

The literal two-zero-cell rebalance spreads each requested mass uniformly
inside one guarded structured cell.  Consequently its medium-prime moment is
controlled by the valuation mean of the *uniform guarded-cell law*.  It is not
unconditionally controlled for arbitrary `minusMass` and `plusMass`, and the
uniform law must not be silently replaced by the generally tilted
`cellMediumLaw`.

This connector first proves the exact finite expectation identity.  It then
combines:

* a reciprocal valuation-mean bound in each of the two zero-head cells; and
* an `O(secondOrderScale / L)` bound for the sum of the absolute mass changes.

The resulting estimate is exactly on the
`secondOrderScale / (p * L)` scale required by the third conjunct of
`BankPaperCanonicalPostHfitMediumPrimeImplementationRateInputs`.
-/

set_option backward.isDefEq.respectTransparency false

open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.PaperBridgeFit
open Erdos390.Full.Scale

noncomputable section

namespace BankPaperRealization

/-! ## Exact uniform-cell expectation algebra -/

/-- A uniform mass increment in one structured cell has valuation moment
equal to the requested mass times the valuation expectation under the
literal uniform guarded-cell probability. -/
theorem
    sum_bankPaperCanonicalUniformCellIncrement_mul_valuation_eq_mass_mul_guardedCellProbability_expect
    {Head Band : Type*} [Fintype Head] [DecidableEq Head]
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData Head Band) (cell : Cell Head)
    (mass : Real) (p : Nat) :
    (∑ m : B.sampleData.Sample,
        bankPaperCanonicalUniformCellIncrement
            B.sampleData cell mass m *
          valuation p (B.sampleData.value m)) =
      mass * (B.guardedCellProbability cell).expect
        (fun m ↦ valuation p (m : Nat)) := by
  classical
  rw [Fintype.sum_sigma, Finset.sum_eq_single cell]
  · simp only [bankPaperCanonicalUniformCellIncrement,
      StructuredSampleData.cellOf, if_true, StructuredSampleData.value,
      Fintype.card_coe]
    unfold BridgeData.guardedCellProbability
    rw [Erdos390.Full.FiniteProbability.uniformOnFinset_expect_eq]
    rw [← Finset.mul_sum]
    ring
  · intro other _hother hne
    apply Finset.sum_eq_zero
    intro m _hm
    simp [bankPaperCanonicalUniformCellIncrement,
      StructuredSampleData.cellOf, hne]
  · intro hnot
    exact (hnot (Finset.mem_univ cell)).elim



/-! ## Quantitative paper-rate closure -/







end BankPaperRealization

end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankPaperCanonicalSmoothSourceGuardedRateClosure -/
section


/-!
# Exact reduction of the smooth source-to-guarded rate

The literal frozen-top implementation defect has already been reduced to
complete rough label `1`.  This file exposes the finite algebra inside that
last row.

There are two points which are easy to conflate.

* The paper's `qTilde` is the mass of the guarded active broad layer.  When
  the canonical scaled seed is instantiated at that mass, its literal mass
  is *exactly* the guarded smooth base mass.  No asymptotic comparison is
  needed.
* The valuation moment is not determined by total mass.  After the exact
  mass synchronization, the remaining analytic term is the difference
  between the scaled barycentric valuation moment and the uniform guarded
  broad-pool valuation moment.  The nearest-integer normalization contributes
  only the two explicit zero-head-cell moments.

The declarations below prove only these exact reductions.  In particular,
no `O(1 / (p L))` valuation comparison is introduced as an assumption.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.HeadPattern
open Erdos390.Full.PaperBridgeFit
open Erdos390.Full.PaperGuardCensus
open Erdos390.Full.StructuredCells

noncomputable section

namespace BankPaperRealization

/-! ## Exact moving structured-cell identification -/





/-! ## Exact guarded-mass synchronization -/



/-! ## The three literal valuation moments -/







/-- The rounded active valuation moment is exactly the scaled moment plus
the two displayed zero-cell moments. -/
theorem
    sum_bankPaperCanonicalTopFrozenRoundedActiveSeed_mul_valuation_eq_scaled_add_nearestInteger
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
    (deltaStar betaProt alpha qTilde : Real) (p : Nat) :
    (∑ m : B.sampleData.Sample,
        bankPaperCanonicalTopFrozenRoundedActiveSeed (K := K)
            B R certificate T deltaStar betaProt alpha qTilde m *
          valuation p (B.sampleData.value m)) =
      bankPaperCanonicalScaledActiveValuationMoment T qTilde p +
        bankPaperCanonicalTopFrozenNearestIntegerValuationMoment (K := K)
          B R certificate deltaStar betaProt alpha qTilde p := by
  unfold bankPaperCanonicalScaledActiveValuationMoment
  unfold bankPaperCanonicalTopFrozenNearestIntegerValuationMoment
  unfold bankPaperCanonicalTopFrozenRoundedActiveSeed
  calc
    (∑ m : B.sampleData.Sample,
        bankPaperCanonicalTwoZeroHeadCellRebalance B.sampleData
            (bankPaperCanonicalScaledActiveSeed T qTilde)
            (bankPaperCanonicalTopFrozenNearestIntegerCellMass (K := K)
              B R certificate deltaStar betaProt alpha qTilde)
            (bankPaperCanonicalTopFrozenNearestIntegerCellMass (K := K)
              B R certificate deltaStar betaProt alpha qTilde) m *
          valuation p (B.sampleData.value m)) =
      (∑ m : B.sampleData.Sample,
          bankPaperCanonicalScaledActiveSeed T qTilde m *
            valuation p (B.sampleData.value m)) +
        (∑ m : B.sampleData.Sample,
          bankPaperCanonicalUniformCellIncrement B.sampleData
              (none, .minus)
              (bankPaperCanonicalTopFrozenNearestIntegerCellMass (K := K)
                B R certificate deltaStar betaProt alpha qTilde) m *
            valuation p (B.sampleData.value m)) +
        ∑ m : B.sampleData.Sample,
          bankPaperCanonicalUniformCellIncrement B.sampleData
              (none, .plus)
              (bankPaperCanonicalTopFrozenNearestIntegerCellMass (K := K)
                B R certificate deltaStar betaProt alpha qTilde) m *
            valuation p (B.sampleData.value m) := by
      rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro m _hm
      unfold bankPaperCanonicalTwoZeroHeadCellRebalance
      ring
    _ =
      (∑ m : B.sampleData.Sample,
          bankPaperCanonicalScaledActiveSeed T qTilde m *
            valuation p (B.sampleData.value m)) +
        (bankPaperCanonicalTopFrozenNearestIntegerCellMass (K := K)
              B R certificate deltaStar betaProt alpha qTilde *
            (B.guardedCellProbability (none, .minus)).expect
              (fun m ↦ valuation p (m : Nat)) +
          bankPaperCanonicalTopFrozenNearestIntegerCellMass (K := K)
              B R certificate deltaStar betaProt alpha qTilde *
            (B.guardedCellProbability (none, .plus)).expect
              (fun m ↦ valuation p (m : Nat))) := by
      rw [
        sum_bankPaperCanonicalUniformCellIncrement_mul_valuation_eq_mass_mul_guardedCellProbability_expect
          B (none, .minus)
            (bankPaperCanonicalTopFrozenNearestIntegerCellMass (K := K)
              B R certificate deltaStar betaProt alpha qTilde) p,
        sum_bankPaperCanonicalUniformCellIncrement_mul_valuation_eq_mass_mul_guardedCellProbability_expect
          B (none, .plus)
            (bankPaperCanonicalTopFrozenNearestIntegerCellMass (K := K)
              B R certificate deltaStar betaProt alpha qTilde) p]
      ring

/-! ## Exact label-one source decomposition -/





/-- Final exact decomposition.  Once the total mass has been synchronized,
the only large analytic comparison is the displayed scaled-active versus
guarded-broad moment; the nearest-integer contribution is already an
explicit two-cell term. -/
theorem
    roughCanonicalTopFrozenRoundedSmoothSourceToGuardedValuationDefect_eq_scaled_sub_guardedBase_add_nearestInteger
    {P : Finset Nat} {Band : Type*}
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData (PaperHeadSimplex.Tag P) Band)
    {c : Real} {depth : Nat} (K0 : Nat)
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (T : BarycentricTarget B.sampleData)
    (deltaStar betaProt betaAct qTilde : Real)
    (p : Nat)
    (hn : 1 <= B.sampleData.n) (hdeltaUpper : deltaStar <= 1)
    (hvalues : ∀ m : B.sampleData.Sample,
      B.sampleData.value m ∈
        R.roughCanonicalGuardedRow certificate deltaStar (K0 + 1) 1) :
    roughCanonicalTopFrozenRoundedSmoothSourceToGuardedValuationDefect
        B K0 R certificate T deltaStar betaProt betaAct qTilde p =
      bankPaperCanonicalScaledActiveValuationMoment T qTilde p -
        bankPaperCanonicalGuardedSmoothBaseValuationMoment (K := K0 + 1)
          B R certificate deltaStar betaAct p +
        bankPaperCanonicalTopFrozenNearestIntegerValuationMoment
          (K := K0 + 1) B R certificate deltaStar betaProt
            (bankPaperCanonicalPostHfitBalancedAlpha
              B c K0 betaProt betaAct)
            qTilde p := by
  rw [
    roughCanonicalTopFrozenRoundedSmoothSourceToGuardedValuationDefect_eq_roundedActive_sub_guardedBase
      B K0 R certificate T deltaStar betaProt betaAct qTilde p
        hn hdeltaUpper hvalues,
    sum_bankPaperCanonicalTopFrozenRoundedActiveSeed_mul_valuation_eq_scaled_add_nearestInteger]
  ring

end BankPaperRealization

end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankPaperCanonicalSmoothSourceGuardedSharpValuationRateClosure -/
section


/-!
# Sharp valuation-rate ingredients for the smooth source

This file begins the analytic lift left explicit by
`BankPaperCanonicalSmoothSourceGuardedRateClosure`.

The first theorem below is the sharp un-tilted full-valuation profile for one
fixed raw structured cell.  It is obtained only from already proved inputs:

* the common `paperDivisibilityMain` law through `yNat n ^ 4`;
* the arbitrary-divisor reciprocal fallback;
* the finite prime-power tail identity; and
* the sharp conversion of the `yNat n ^ 4` tail to `1 / (p * L n)`.

No full-valuation comparison is assumed.
-/

open Filter Topology
set_option backward.isDefEq.respectTransparency false

open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.ArithmeticBandGeometry
open Erdos390.Full.Scale
open Erdos390.Full.HeadPattern
open Erdos390.Full.StructuredCells
open Erdos390.Full.FiniteProbability
open Erdos390.Full.PrimePowerCovariance
open Erdos390.Full.PrimePowerCutoffCovariance
open Erdos390.Full.PaperScaleMarkedCell
open Erdos390.Full.PaperMovingPrefixMarkedCell
open Erdos390.Full.PaperPrimePowerTailRate
open Erdos390.Full.PaperRawPrefixThirdCumulantFallback
open Erdos390.Full.PaperRawTiltedValuationMeanRows
open Erdos390.Full.LocalFugacityBounds
open Erdos390.Full.ValuationScoreDomination
open Erdos390.Full.PaperGuardCensus
open Erdos390.Full.PaperBridgeFit
open Erdos390.Full.GuardedUniformCell
open Erdos390.Full.GuardDeletionSquarefreeProfiles
open Erdos390.Full.GuardSquarefreeErrorRate
open Erdos390.Full.PaperCanonicalTiltedPrefixRows

noncomputable section

namespace BankPaperRealization

set_option maxHeartbeats 2400000

/-! ## Fixed raw structured cells -/





/-! ## Literal guard deletion -/

/-- Tilting by the identically-zero score does not change an expectation.
This small identity lets the general conditional-deletion theorem be used
without replacing the literal uniform laws by unnamed equivalent laws. -/
theorem finiteProbability_exponentialTilt_zero_expect
    {Omega : Type*} [Fintype Omega]
    (mu : FiniteProbability Omega) (F : Omega → Real) :
    (mu.exponentialTilt (fun _ ↦ 0)).expect F = mu.expect F := by
  have hpartition :
      mu.expPartition (fun _ ↦ 0) = 1 := by
    unfold FiniteProbability.expPartition FiniteProbability.expect
    simp only [Real.exp_zero, mul_one]
    exact mu.mass_sum
  rw [mu.exponentialTilt_expect_eq, hpartition, div_one]
  apply congrArg mu.expect
  funext omega
  simp



/-! ## The concrete guard ledger at the stronger `1 / L` rate -/













/-- Bridge-data specialization of the preceding guarded raw-cell theorem.
The only additional input is the repository's literal identification of the
sample data with `canonicalSampleData`; no tilted law is introduced. -/
theorem
    exists_uniform_bridge_guardedCell_valuation_mean_profiles_paperRate
    {Head : Type*} [Fintype Head] [DecidableEq Head] [Nonempty Head]
    (P : Head → Pattern) (I : PhysicalIntervals)
    (Cprom Cbank : Nat) (G : ∀ n, Ledger n Cprom Cbank)
    (W : Nat) (hW : 1 < W)
    (hHeadLe : ∀ h, ∀ q ∈ (P h).primes, q ≤ W) :
    ∃ Cval : Real, 0 < Cval ∧ ∃ N₀ : Nat,
      ∀ {Band : Type*} [Fintype Band] [DecidableEq Band]
        (B : BridgeData Head Band),
        N₀ ≤ B.sampleData.n → B.sampleData.W = W →
        (hsep : physicalBound (I.upper .minus) B.sampleData.n <
          physicalBound (I.lower .plus) B.sampleData.n) →
        (hremaining : ∀ c : Cell Head,
          (rawCell P I B.sampleData.n c \
            (G B.sampleData.n).guards).Nonempty) →
        B.sampleData = canonicalSampleData
          (W := B.sampleData.W) P I (G B.sampleData.n)
            hsep hremaining →
        ∀ p : BandPrime B.sampleData.n B.sampleData.W,
          let Kcut := Nat.log p.1 (yNat B.sampleData.n ^ 4)
          ∀ c : Cell Head,
            |(B.guardedCellProbability c).expect
                  (fun m ↦ valuation p.1 (m : Nat)) -
              ∑ k ∈ positiveExponents Kcut,
                paperDivisibilityMain B.sampleData.n (p.1 ^ k)| ≤
              Cval / ((p.1 : Real) * B.L) := by
  obtain ⟨Cval, hCval, N₀, hrate⟩ :=
    exists_uniform_guardedRawCell_valuation_mean_profiles_paperRate
      P I Cprom Cbank G W hW hHeadLe
  refine ⟨Cval, hCval, N₀, ?_⟩
  intro Band _instBand _instBandDec B hN hBW hsep hremaining hcanonical p
  have hrateP :=
    hrate (n := B.sampleData.n) (p := p.1) hN
      (by simpa only [hBW] using p.2)
  dsimp only at hrateP ⊢
  intro c
  have hraw := hrateP c (hremaining c)
  have hcell :
      B.sampleData.cellFinset c =
        rawCell P I B.sampleData.n c \
          (G B.sampleData.n).guards := by
    calc
      B.sampleData.cellFinset c =
          (canonicalSampleData (W := B.sampleData.W)
            P I (G B.sampleData.n) hsep hremaining).cellFinset c :=
        congrArg (fun D : StructuredSampleData Head ↦ D.cellFinset c)
          hcanonical
      _ = rawCell P I B.sampleData.n c \
          (G B.sampleData.n).guards := by
        exact canonicalSampleData_cellFinset
          P I (G B.sampleData.n) hsep hremaining c
  have hreindex :
      (uniformOnFinset
          (rawCell P I B.sampleData.n c \
            (G B.sampleData.n).guards)
          (hremaining c)).expect
            (fun m ↦ valuation p.1 (m : Nat)) =
        (uniformOnFinset
          (B.sampleData.cellFinset c)
          (B.sampleData.cell_nonempty c)).expect
            (fun m ↦ valuation p.1 (m : Nat)) := by
    have htilt :=
      uniformOnFinset_exponentialTilt_expect_eq_of_finset_eq
        (rawCell P I B.sampleData.n c \
          (G B.sampleData.n).guards)
        (B.sampleData.cellFinset c) hcell.symm
        (hremaining c) (B.sampleData.cell_nonempty c)
        (fun _ ↦ (0 : Real)) (fun _ ↦ (0 : Real))
        (by
          intro x y hxy
          rfl)
        (fun m : Nat ↦ valuation p.1 m)
    simpa only [finiteProbability_exponentialTilt_zero_expect] using htilt
  unfold BridgeData.guardedCellProbability
  rw [← hreindex]
  simpa only [BridgeData.L, Erdos390.Full.Scale.L, hBW] using hraw

end BankPaperRealization

end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankPaperCanonicalSmoothSourceGuardedSharpValuationRateClosureMixture -/
section


/-!
# Barycentric mixture algebra for the sharp smooth-source rate

The analytic marked-cell estimates compare every cell and the moving broad
pool to one common truncated prime-power profile.  This file performs the
remaining finite convex-mixture algebra exactly.

No cell-versus-broad rate is assumed.  The quantitative transfer theorem
takes two separate common-profile bounds, which are the outputs supplied by
the fixed-cell and moving-prefix analyses.
-/

set_option backward.isDefEq.respectTransparency false

open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.PaperBridgeFit
open Erdos390.Full.PaperGuardCensus
open Erdos390.Full.FiniteProbability

noncomputable section

namespace BankPaperRealization

/-! ## Exact convex-mixture identities -/

/-- The scaled active valuation moment is the active mass times the
barycentric convex combination of the literal guarded-cell valuation
means. -/
theorem
    bankPaperCanonicalScaledActiveValuationMoment_eq_q_mul_cellMeans
    {Head : Type*} [Fintype Head] [Nonempty Head]
    {D : StructuredSampleData Head}
    (T : BarycentricTarget D) (q : Real) (p : Nat) :
    bankPaperCanonicalScaledActiveValuationMoment T q p =
      q * ∑ c : Cell Head,
        T.cellProbability c *
          (uniformOnFinset (D.cellFinset c) (D.cell_nonempty c)).expect
            (fun m ↦ valuation p (m : Nat)) := by
  classical
  unfold bankPaperCanonicalScaledActiveValuationMoment
  unfold bankPaperCanonicalScaledActiveSeed
  rw [Fintype.sum_sigma]
  calc
    (∑ c : Cell Head, ∑ m : D.SampleAt c,
        q * T.baseline.baseWeight ⟨c, m⟩ *
          valuation p (D.value ⟨c, m⟩)) =
      ∑ c : Cell Head,
        q * T.cellProbability c *
          (uniformOnFinset (D.cellFinset c) (D.cell_nonempty c)).expect
            (fun m ↦ valuation p (m : Nat)) := by
      apply Finset.sum_congr rfl
      intro c _hc
      rw [FiniteProbability.uniformOnFinset_expect_eq]
      simp only [BaselineAllocation.baseWeight,
        StructuredSampleData.cellOf, StructuredSampleData.value,
        Fintype.card_coe]
      unfold BarycentricTarget.baseline
      rw [← Finset.mul_sum]
      ring
    _ = q * ∑ c : Cell Head,
        T.cellProbability c *
          (uniformOnFinset (D.cellFinset c) (D.cell_nonempty c)).expect
            (fun m ↦ valuation p (m : Nat)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro c _hc
      ring

/-- The constant guarded smooth-base moment is its literal mass times the
uniform valuation mean of the guarded broad pool. -/
theorem
    bankPaperCanonicalGuardedSmoothBaseValuationMoment_eq_mass_mul_poolMean
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
    (deltaStar betaAct : Real) (p : Nat)
    (hpool :
      (R.roughCanonicalGuardedBroadCorrectionPool certificate
        deltaStar B.sampleData.W K 1).Nonempty) :
    bankPaperCanonicalGuardedSmoothBaseValuationMoment (K := K)
        B R certificate deltaStar betaAct p =
      bankPaperCanonicalGuardedSmoothBaseMass R certificate
          deltaStar B.sampleData.W K betaAct *
        (uniformOnFinset
          (R.roughCanonicalGuardedBroadCorrectionPool certificate
            deltaStar B.sampleData.W K 1) hpool).expect
          (fun a ↦ valuation p (a : Nat)) := by
  unfold bankPaperCanonicalGuardedSmoothBaseValuationMoment
  unfold bankPaperCanonicalGuardedSmoothBaseMass
  rw [FiniteProbability.uniformOnFinset_expect_ambient_eq]
  unfold BridgeData.L Erdos390.Full.Scale.L
  have hcard :
      ((R.roughCanonicalGuardedBroadCorrectionPool certificate
        deltaStar B.sampleData.W K 1).card : Real) ≠ 0 := by
    exact_mod_cast Finset.card_ne_zero.mpr hpool
  field_simp [hcard]

/-- After synchronizing `q` with the literal guarded smooth mass, the
unrounded active-versus-base moment is exactly mass times a difference of
probability means. -/
theorem
    bankPaperCanonicalScaledActiveValuationMoment_sub_guardedSmoothBase_eq_mass_mul_meanDefect
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
    (deltaStar betaAct q : Real) (p : Nat)
    (hq : q =
      bankPaperCanonicalGuardedSmoothBaseMass R certificate
        deltaStar B.sampleData.W K betaAct)
    (hpool :
      (R.roughCanonicalGuardedBroadCorrectionPool certificate
        deltaStar B.sampleData.W K 1).Nonempty) :
    bankPaperCanonicalScaledActiveValuationMoment T q p -
        bankPaperCanonicalGuardedSmoothBaseValuationMoment (K := K)
          B R certificate deltaStar betaAct p =
      q *
        ((∑ cell : Cell (PaperHeadSimplex.Tag P),
            T.cellProbability cell *
              (B.guardedCellProbability cell).expect
                (fun m ↦ valuation p (m : Nat))) -
          (uniformOnFinset
            (R.roughCanonicalGuardedBroadCorrectionPool certificate
              deltaStar B.sampleData.W K 1) hpool).expect
                (fun a ↦ valuation p (a : Nat))) := by
  rw [
    bankPaperCanonicalScaledActiveValuationMoment_eq_q_mul_cellMeans,
    bankPaperCanonicalGuardedSmoothBaseValuationMoment_eq_mass_mul_poolMean
      B R certificate deltaStar betaAct p hpool,
    ← hq]
  unfold BridgeData.guardedCellProbability
  ring

/-! ## Common-profile quantitative transfer -/

/-- A convex combination and one broad-pool law inherit their difference
bound from separate estimates against the same common profile. -/
theorem
    abs_bankPaperCanonicalScaledActiveValuationMoment_sub_guardedSmoothBase_le_of_commonProfile
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
    (deltaStar betaAct q main Ccell Cpool : Real) (p : Nat)
    (hq : q =
      bankPaperCanonicalGuardedSmoothBaseMass R certificate
        deltaStar B.sampleData.W K betaAct)
    (hpool :
      (R.roughCanonicalGuardedBroadCorrectionPool certificate
        deltaStar B.sampleData.W K 1).Nonempty)
    (_hp : 0 < p) (_hL : 0 < B.L)
    (_hCcell : 0 ≤ Ccell) (_hCpool : 0 ≤ Cpool)
    (hcell : ∀ cell : Cell (PaperHeadSimplex.Tag P),
      |(B.guardedCellProbability cell).expect
          (fun m ↦ valuation p (m : Nat)) - main| ≤
        Ccell / ((p : Real) * B.L))
    (hpoolProfile :
      |(uniformOnFinset
          (R.roughCanonicalGuardedBroadCorrectionPool certificate
            deltaStar B.sampleData.W K 1) hpool).expect
          (fun a ↦ valuation p (a : Nat)) - main| ≤
        Cpool / ((p : Real) * B.L)) :
    |bankPaperCanonicalScaledActiveValuationMoment T q p -
        bankPaperCanonicalGuardedSmoothBaseValuationMoment (K := K)
          B R certificate deltaStar betaAct p| ≤
      |q| * ((Ccell + Cpool) / ((p : Real) * B.L)) := by
  let cellMean : Cell (PaperHeadSimplex.Tag P) → Real := fun cell ↦
    (B.guardedCellProbability cell).expect
      (fun m ↦ valuation p (m : Nat))
  let poolMean : Real :=
    (uniformOnFinset
      (R.roughCanonicalGuardedBroadCorrectionPool certificate
        deltaStar B.sampleData.W K 1) hpool).expect
      (fun a ↦ valuation p (a : Nat))
  have hmixIdentity :
      (∑ cell : Cell (PaperHeadSimplex.Tag P),
          T.cellProbability cell * cellMean cell) - main =
        ∑ cell : Cell (PaperHeadSimplex.Tag P),
          T.cellProbability cell * (cellMean cell - main) := by
    calc
      (∑ cell : Cell (PaperHeadSimplex.Tag P),
          T.cellProbability cell * cellMean cell) - main =
        (∑ cell : Cell (PaperHeadSimplex.Tag P),
          T.cellProbability cell * cellMean cell) -
          (∑ cell : Cell (PaperHeadSimplex.Tag P),
            T.cellProbability cell) * main := by
          rw [T.sum_cellProbability, one_mul]
      _ = _ := by
        rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro cell _hcell
        ring
  have hmix :
      |(∑ cell : Cell (PaperHeadSimplex.Tag P),
          T.cellProbability cell * cellMean cell) - main| ≤
        Ccell / ((p : Real) * B.L) := by
    rw [hmixIdentity]
    calc
      |∑ cell : Cell (PaperHeadSimplex.Tag P),
          T.cellProbability cell * (cellMean cell - main)| ≤
        ∑ cell : Cell (PaperHeadSimplex.Tag P),
          |T.cellProbability cell * (cellMean cell - main)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ = ∑ cell : Cell (PaperHeadSimplex.Tag P),
          T.cellProbability cell * |cellMean cell - main| := by
        apply Finset.sum_congr rfl
        intro cell _hcell
        rw [abs_mul, abs_of_nonneg (T.cellProbability_pos cell).le]
      _ ≤ ∑ cell : Cell (PaperHeadSimplex.Tag P),
          T.cellProbability cell *
            (Ccell / ((p : Real) * B.L)) := by
        apply Finset.sum_le_sum
        intro cell _hcell
        exact mul_le_mul_of_nonneg_left
          (by simpa only [cellMean] using hcell cell)
          (T.cellProbability_pos cell).le
      _ = Ccell / ((p : Real) * B.L) := by
        rw [← Finset.sum_mul, T.sum_cellProbability, one_mul]
  have hmeanPair :
      |(∑ cell : Cell (PaperHeadSimplex.Tag P),
          T.cellProbability cell * cellMean cell) - poolMean| ≤
        (Ccell + Cpool) / ((p : Real) * B.L) := by
    calc
      |(∑ cell : Cell (PaperHeadSimplex.Tag P),
          T.cellProbability cell * cellMean cell) - poolMean| ≤
        |(∑ cell : Cell (PaperHeadSimplex.Tag P),
          T.cellProbability cell * cellMean cell) - main| +
          |poolMean - main| := by
            have htri := abs_add_le
              ((∑ cell : Cell (PaperHeadSimplex.Tag P),
                T.cellProbability cell * cellMean cell) - main)
              (main - poolMean)
            simpa only [sub_add_sub_cancel, abs_sub_comm] using htri
      _ ≤ Ccell / ((p : Real) * B.L) +
          Cpool / ((p : Real) * B.L) :=
        add_le_add hmix
          (by simpa only [poolMean] using hpoolProfile)
      _ = (Ccell + Cpool) / ((p : Real) * B.L) := by ring
  rw [
    bankPaperCanonicalScaledActiveValuationMoment_sub_guardedSmoothBase_eq_mass_mul_meanDefect
      B R certificate T deltaStar betaAct q p hq hpool,
    abs_mul]
  exact mul_le_mul_of_nonneg_left hmeanPair (abs_nonneg q)

end BankPaperRealization

end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankPaperCanonicalSmoothSourceGuardedSharpValuationRateClosureFinal -/
section


/-!
# Full sharp smooth-source valuation lift

This file combines the two separately proved common-profile estimates:

* every canonical guarded active cell; and
* the canonical guarded label-one broad pool.

The only remaining step is the exact barycentric algebra.  In particular,
the theorem below does not assume a cell-versus-pool valuation comparison.
-/

open Filter Topology
open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.ArithmeticBandGeometry
open Erdos390.Full.Scale
open Erdos390.Full.HeadPattern
open Erdos390.Full.PaperBridgeFit
open Erdos390.Full.PaperGuardCensus
open Erdos390.Full.PaperScaleMarkedCell
open Erdos390.Full.PrimePowerCovariance
open Erdos390.Full.FiniteProbability

noncomputable section

namespace BankPaperRealization

set_option maxHeartbeats 2400000

/-- The unrounded scaled active valuation moment and the constant guarded
smooth-base valuation moment differ by the sharp paper rate.  All analytic
inputs are discharged by the fixed-cell, moving-prefix, prime-power-tail,
guard-census, and barycentric theorems proved earlier in this closure chain.
-/
theorem
    exists_uniform_scaledActive_sub_guardedSmoothBase_valuationMoment_paperRate
    (Phead : Finset Nat)
    (Patterns : PaperHeadSimplex.Tag Phead → Pattern)
    (I : PhysicalIntervals)
    (Cprom Cbank : Nat) (G : ∀ n, Ledger n Cprom Cbank)
    (W K depth : Nat) (hW : 1 < W)
    (hHeadLe : ∀ h, ∀ q ∈ (Patterns h).primes, q ≤ W)
    {c : Real} (hc : 0 < c) :
    ∃ Cval : Real, 0 < Cval ∧ ∃ N₀ : Nat,
      ∀ {Band : Type*} [Fintype Band] [DecidableEq Band]
        (B : BridgeData (PaperHeadSimplex.Tag Phead) Band)
        (R : BankPaperRealization B.sampleData.n
          (upperEndpoint B.sampleData.n
            (upperTailLength c B.sampleData.n)))
        (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
          R.anchorGuardLeftCore R.anchorGuardRightCore
          (R.centralChangedMarkers depth))
        (T : BarycentricTarget B.sampleData)
        (deltaStar betaAct q : Real),
        N₀ ≤ B.sampleData.n → B.sampleData.W = W →
        ∀ (hsep : physicalBound (I.upper .minus) B.sampleData.n <
            physicalBound (I.lower .plus) B.sampleData.n)
          (hremaining : ∀ cell : Cell (PaperHeadSimplex.Tag Phead),
            (rawCell Patterns I B.sampleData.n cell \
              (G B.sampleData.n).guards).Nonempty),
          B.sampleData = canonicalSampleData
              (W := B.sampleData.W) Patterns I (G B.sampleData.n)
                hsep hremaining →
          q = bankPaperCanonicalGuardedSmoothBaseMass R certificate
              deltaStar B.sampleData.W K betaAct →
          ∀ _hpool :
            (R.roughCanonicalGuardedBroadCorrectionPool certificate
              deltaStar B.sampleData.W K 1).Nonempty,
          ∀ p : BandPrime B.sampleData.n B.sampleData.W,
            |bankPaperCanonicalScaledActiveValuationMoment T q p.1 -
                bankPaperCanonicalGuardedSmoothBaseValuationMoment (K := K)
                  B R certificate deltaStar betaAct p.1| ≤
              |q| * (Cval / ((p.1 : Real) * B.L)) := by
  obtain ⟨Ccell, hCcell, Ncell, hcellRate⟩ :=
    exists_uniform_bridge_guardedCell_valuation_mean_profiles_paperRate
      Patterns I Cprom Cbank G W hW hHeadLe
  obtain ⟨Cpool, hCpool, Npool, hpoolRate⟩ :=
    exists_uniform_guardedSmoothBasePool_valuation_mean_profile_paperRate
      W K depth hW hc
  let Cval : Real := Ccell + Cpool
  have hCval : 0 < Cval := by
    dsimp only [Cval]
    positivity
  refine ⟨Cval, hCval, max 2 (max Ncell Npool), ?_⟩
  intro Band _instBand _instBandDec B R certificate T
    deltaStar betaAct q hN hBW hsep hremaining hcanonical hq hpool p
  subst W
  have hn : 1 < B.sampleData.n := by omega
  have hNcell : Ncell ≤ B.sampleData.n := by omega
  have hNpool : Npool ≤ B.sampleData.n := by omega
  have hpBandW : p.1 ∈
      primeBand B.sampleData.n B.sampleData.W := p.2
  have hcell :=
    hcellRate B hNcell rfl hsep hremaining hcanonical p
  have hpoolProfile :=
    hpoolRate R certificate deltaStar hNpool hpBandW
      hpool
  let Kcut := Nat.log p.1 (yNat B.sampleData.n ^ 4)
  let mainSum := ∑ j ∈ positiveExponents Kcut,
    paperDivisibilityMain B.sampleData.n (p.1 ^ j)
  have hcell' :
      ∀ cell : Cell (PaperHeadSimplex.Tag Phead),
        |(B.guardedCellProbability cell).expect
              (fun m ↦ valuation p.1 (m : Nat)) - mainSum| ≤
          Ccell / ((p.1 : Real) * B.L) := by
    intro cell
    simpa only [Kcut, mainSum] using hcell cell
  have hpool' :
      |(uniformOnFinset
          (R.roughCanonicalGuardedBroadCorrectionPool certificate
            deltaStar B.sampleData.W K 1) hpool).expect
          (fun a ↦ valuation p.1 (a : Nat)) - mainSum| ≤
        Cpool / ((p.1 : Real) * B.L) := by
    simpa only [Kcut, mainSum, BridgeData.L,
      Erdos390.Full.Scale.L] using hpoolProfile
  have hpPrime := prime_of_mem_primeBand p.2
  have hpPos : 0 < p.1 := hpPrime.pos
  have hL : 0 < B.L := by
    simpa only [BridgeData.L] using L_pos hn
  have hfinal :=
    abs_bankPaperCanonicalScaledActiveValuationMoment_sub_guardedSmoothBase_le_of_commonProfile
      B R certificate T deltaStar betaAct q mainSum Ccell Cpool p.1
      hq hpool hpPos hL hCcell.le hCpool.le hcell' hpool'
  simpa only [Cval] using hfinal

end BankPaperRealization

end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankPaperCanonicalSmoothSourceGuardedSharpRoundedValuationRateConnector -/
section


/-!
# Rounded smooth-source to guarded valuation rate

The sharp common-profile closure controls the unrounded barycentric active
moment against the constant guarded label-one broad layer.  The exact
frozen-top decomposition has one additional term: the same nearest-integer
mass is inserted in each physical copy of the zero head cell.

This file bounds that literal correction directly.  Its cell mass is at most
`1 / 4`, by the universal half-unit nearest-integer error, and reciprocal
zero-cell valuation means then put it on the same
`secondOrderScale / (p * L)` scale.
-/

open Filter Topology
open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.ArithmeticBandGeometry
open Erdos390.Full.Scale
open Erdos390.Full.HeadPattern
open Erdos390.Full.PaperBridgeFit
open Erdos390.Full.PaperGuardCensus
open Erdos390.Full.FiniteProbability

noncomputable section

namespace BankPaperRealization

set_option maxHeartbeats 2400000

/-! ## The synchronized guarded active mass -/

/-- The guarded label-one active mass has its pointwise paper-scale upper
bound without an additional analytic hypothesis.  Indeed, its support is
contained in the raw label-one smooth pool, which in turn lies in an
interval of cardinality at most `n`. -/
theorem
    abs_bankPaperCanonicalGuardedSmoothBaseMass_le_abs_mul_secondOrderScale
    {c : Real} {depth n h : Nat} {left right : Nat -> Nat}
    {changed : Finset Nat}
    (R : BankPaperRealization n (upperEndpoint n h))
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (deltaStar : Real) (W K : Nat) (betaAct : Real)
    (hn : 1 < n) :
    |bankPaperCanonicalGuardedSmoothBaseMass R certificate
        deltaStar W K betaAct| ≤
      |betaAct| * secondOrderScale n := by
  have hL : 0 < L n := L_pos hn
  have hguardedSubset :
      R.roughCanonicalGuardedBroadCorrectionPool certificate
          deltaStar W K 1 ⊆
        bankPaperCanonicalRawSmoothBasePool W n h K := by
    simpa only [bankPaperCanonicalRawSmoothBasePool] using
      R.roughCanonicalGuardedBroadCorrectionPool_subset_broadPool
        certificate deltaStar W K 1
  have hrawSubset :
      bankPaperCanonicalRawSmoothBasePool W n h K ⊆
        roughBroadLowerBlock n h K := by
    intro a ha
    change a ∈ roughCanonicalBroadCorrectionPool W n h K (yNat n) 1 at ha
    have haRow := mem_completeRoughRowFiber.mp ha
    exact (mem_roughHeadFree.mp haRow.1).1
  have hcardNat :
      (R.roughCanonicalGuardedBroadCorrectionPool certificate
        deltaStar W K 1).card ≤ n := by
    calc
      (R.roughCanonicalGuardedBroadCorrectionPool certificate
          deltaStar W K 1).card ≤
          (bankPaperCanonicalRawSmoothBasePool W n h K).card :=
        Finset.card_le_card hguardedSubset
      _ ≤ (roughBroadLowerBlock n h K).card :=
        Finset.card_le_card hrawSubset
      _ ≤ n := by
        simp only [roughBroadLowerBlock, Nat.card_Ioc]
        omega
  have hcard :
      ((R.roughCanonicalGuardedBroadCorrectionPool certificate
        deltaStar W K 1).card : Real) ≤ (n : Real) := by
    exact_mod_cast hcardNat
  have hcardNonneg :
      (0 : Real) ≤
        ((R.roughCanonicalGuardedBroadCorrectionPool certificate
          deltaStar W K 1).card : Real) :=
    Nat.cast_nonneg _
  unfold bankPaperCanonicalGuardedSmoothBaseMass
  rw [abs_mul, abs_div, abs_of_pos hL, abs_of_nonneg hcardNonneg]
  rw [secondOrderScale]
  calc
    |betaAct| / L n *
        ((R.roughCanonicalGuardedBroadCorrectionPool certificate
          deltaStar W K 1).card : Real) ≤
        |betaAct| / L n * (n : Real) :=
      mul_le_mul_of_nonneg_left hcard
        (div_nonneg (abs_nonneg _) hL.le)
    _ = |betaAct| * ((n : Real) / L n) := by ring

/-! ## The literal nearest-integer correction -/

/-- Each of the two zero-head cells receives half of a row-mass rounding
error of absolute size at most `1 / 2`. -/
theorem
    abs_bankPaperCanonicalTopFrozenNearestIntegerCellMass_le_quarter
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
    (deltaStar betaProt alpha qTilde : Real) :
    |bankPaperCanonicalTopFrozenNearestIntegerCellMass (K := K)
        B R certificate deltaStar betaProt alpha qTilde| ≤
      (1 : Real) / 4 := by
  let mFrozen :=
    bankPaperCanonicalTopFrozenSmoothFrozenMass (K := K)
      B R certificate deltaStar betaProt alpha
  have hround :=
    bankPaperCanonicalSmoothInitialActiveMass_abs_sub_actual_le
      mFrozen qTilde
  unfold bankPaperCanonicalTopFrozenNearestIntegerCellMass
  unfold bankPaperCanonicalTopFrozenRoundedActiveMass
  change
    |(bankPaperCanonicalSmoothInitialActiveMass mFrozen qTilde -
        qTilde) / 2| ≤ (1 : Real) / 4
  rw [abs_div, abs_of_pos (by norm_num : (0 : Real) < 2)]
  linarith

/-- Reciprocal valuation means in the two physical zero-head cells give a
literal reciprocal-prime bound for the nearest-integer valuation moment. -/
theorem
    abs_bankPaperCanonicalTopFrozenNearestIntegerValuationMoment_le
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
    (deltaStar betaProt alpha qTilde Azero : Real) (p : Nat)
    (hp : p.Prime) (hAzero : 0 ≤ Azero)
    (hmean : ∀ sigma : PhysicalSign,
      (B.guardedCellProbability (none, sigma)).expect
          (fun m ↦ valuation p (m : Nat)) ≤ Azero / (p : Real)) :
    |bankPaperCanonicalTopFrozenNearestIntegerValuationMoment (K := K)
        B R certificate deltaStar betaProt alpha qTilde p| ≤
      Azero / (2 * (p : Real)) := by
  let cellMass :=
    bankPaperCanonicalTopFrozenNearestIntegerCellMass (K := K)
      B R certificate deltaStar betaProt alpha qTilde
  let meanMinus :=
    (B.guardedCellProbability (none, .minus)).expect
      (fun m ↦ valuation p (m : Nat))
  let meanPlus :=
    (B.guardedCellProbability (none, .plus)).expect
      (fun m ↦ valuation p (m : Nat))
  have hmass : |cellMass| ≤ (1 : Real) / 4 := by
    simpa only [cellMass] using
      abs_bankPaperCanonicalTopFrozenNearestIntegerCellMass_le_quarter
        (K := K) B R certificate deltaStar betaProt alpha qTilde
  have hminus0 : 0 ≤ meanMinus :=
    (B.guardedCellProbability (none, .minus)).expect_nonneg _
      (fun m ↦ valuation_nonneg p (m : Nat))
  have hplus0 : 0 ≤ meanPlus :=
    (B.guardedCellProbability (none, .plus)).expect_nonneg _
      (fun m ↦ valuation_nonneg p (m : Nat))
  have hminus : meanMinus ≤ Azero / (p : Real) := by
    simpa only [meanMinus] using hmean .minus
  have hplus : meanPlus ≤ Azero / (p : Real) := by
    simpa only [meanPlus] using hmean .plus
  have hpR : (0 : Real) < p := by exact_mod_cast hp.pos
  have hrate0 : 0 ≤ Azero / (p : Real) :=
    div_nonneg hAzero hpR.le
  unfold bankPaperCanonicalTopFrozenNearestIntegerValuationMoment
  change |cellMass * meanMinus + cellMass * meanPlus| ≤ _
  calc
    |cellMass * meanMinus + cellMass * meanPlus| ≤
        |cellMass * meanMinus| + |cellMass * meanPlus| :=
      abs_add_le _ _
    _ = |cellMass| * meanMinus + |cellMass| * meanPlus := by
      rw [abs_mul, abs_mul, abs_of_nonneg hminus0,
        abs_of_nonneg hplus0]
    _ ≤ ((1 : Real) / 4) * (Azero / (p : Real)) +
        ((1 : Real) / 4) * (Azero / (p : Real)) := by
      exact add_le_add
        (mul_le_mul hmass hminus hminus0 (by norm_num))
        (mul_le_mul hmass hplus hplus0 (by norm_num))
    _ = Azero / (2 * (p : Real)) := by
      field_simp [hpR.ne']
      ring

/-! ## Sharp rounded finite-rate connector -/

/-- The complete rounded label-one source-to-guarded defect has the paper
rate.  The hypotheses retained at the call site are the honest construction
interfaces not determined by the valuation analysis itself:

* literal identification with the canonical guarded sample;
* synchronization of `qTilde` with the guarded smooth-base mass;
* membership of the structured active values in the guarded smooth row; and
* reciprocal valuation means in the two zero-head cells.

The active coefficient `betaAct` is fixed outside the uniform quantifiers,
so the resulting constant may honestly depend on its absolute value.
-/
theorem
    exists_uniform_topFrozenRoundedSmoothSourceToGuardedValuationDefectBound_paperRate
    (Phead : Finset Nat)
    (Patterns : PaperHeadSimplex.Tag Phead → Pattern)
    (I : PhysicalIntervals)
    (Cprom Cbank : Nat) (G : ∀ n, Ledger n Cprom Cbank)
    (W K0 depth : Nat) (hW : 1 < W)
    (hHeadLe : ∀ h, ∀ q ∈ (Patterns h).primes, q ≤ W)
    {c : Real} (hc : 0 < c)
    (betaAct Azero : Real) (hAzero : 0 ≤ Azero) :
    ∃ Csource : Real, 0 < Csource ∧ ∃ N₀ : Nat,
      ∀ {Band : Type*} [Fintype Band] [DecidableEq Band]
        (B : BridgeData (PaperHeadSimplex.Tag Phead) Band)
        (R : BankPaperRealization B.sampleData.n
          (upperEndpoint B.sampleData.n
            (upperTailLength c B.sampleData.n)))
          (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
          R.anchorGuardLeftCore R.anchorGuardRightCore
          (R.centralChangedMarkers depth))
        (T : BarycentricTarget B.sampleData)
        (deltaStar betaProt qTilde : Real),
        N₀ ≤ B.sampleData.n → B.sampleData.W = W →
        ∀ (hsep : physicalBound (I.upper .minus) B.sampleData.n <
            physicalBound (I.lower .plus) B.sampleData.n)
          (hremaining : ∀ cell : Cell (PaperHeadSimplex.Tag Phead),
            (rawCell Patterns I B.sampleData.n cell \
              (G B.sampleData.n).guards).Nonempty),
          B.sampleData = canonicalSampleData
              (W := B.sampleData.W) Patterns I (G B.sampleData.n)
                hsep hremaining →
          qTilde = bankPaperCanonicalGuardedSmoothBaseMass R certificate
              deltaStar B.sampleData.W (K0 + 1) betaAct →
          deltaStar ≤ 1 →
          (∀ m : B.sampleData.Sample,
            B.sampleData.value m ∈
              R.roughCanonicalGuardedRow certificate deltaStar
                (K0 + 1) 1) →
          ∀ _hpool :
            (R.roughCanonicalGuardedBroadCorrectionPool certificate
              deltaStar B.sampleData.W (K0 + 1) 1).Nonempty,
          ∀ p : BandPrime B.sampleData.n B.sampleData.W,
            (∀ sigma : PhysicalSign,
              (B.guardedCellProbability (none, sigma)).expect
                  (fun m ↦ valuation p.1 (m : Nat)) ≤
                Azero / (p.1 : Real)) →
            RoughCanonicalTopFrozenRoundedSmoothSourceToGuardedValuationDefectBound
              B K0 R certificate T deltaStar betaProt betaAct qTilde p.1
              (Csource *
                (secondOrderScale B.sampleData.n /
                  ((p.1 : Real) * B.L))) := by
  obtain ⟨Csharp, hCsharp, Nsharp, hsharp⟩ :=
    exists_uniform_scaledActive_sub_guardedSmoothBase_valuationMoment_paperRate
      Phead Patterns I Cprom Cbank G W (K0 + 1) depth hW hHeadLe hc
  have hscaleEvent : ∀ᶠ n : Nat in atTop,
      1 ≤ secondOrderScale n / L n :=
    secondOrderScale_div_L_tendsto_atTop.eventually
      (eventually_ge_atTop 1)
  obtain ⟨Nscale, hNscale⟩ := Filter.eventually_atTop.mp hscaleEvent
  let Csource : Real := |betaAct| * Csharp + Azero / 2 + 1
  have hCsource : 0 < Csource := by
    dsimp only [Csource]
    positivity
  refine ⟨Csource, hCsource, max 2 (max Nsharp Nscale), ?_⟩
  intro Band _instBand _instBandDec B R certificate T
    deltaStar betaProt qTilde hN hBW hsep hremaining
    hcanonical hmassSync hdeltaUpper hvalues _hpool p hmean
  have hn : 1 < B.sampleData.n := by omega
  have hNsharp : Nsharp ≤ B.sampleData.n := by omega
  have hNscaleBound : Nscale ≤ B.sampleData.n := by omega
  have hp := prime_of_mem_primeBand p.2
  have hpR : (0 : Real) < p.1 := by exact_mod_cast hp.pos
  have hL : 0 < B.L := B.L_pos
  let scale : Real :=
    secondOrderScale B.sampleData.n / ((p.1 : Real) * B.L)
  have hscale0 : 0 ≤ scale := by
    dsimp only [scale]
    exact
      div_nonneg (secondOrderScale_pos (by omega)).le
        (mul_nonneg hpR.le hL.le)
  have hscaleOne :
      1 ≤ secondOrderScale B.sampleData.n / B.L := by
    simpa only [BridgeData.L] using
      hNscale B.sampleData.n hNscaleBound
  have hqBound :
      |qTilde| ≤ |betaAct| * secondOrderScale B.sampleData.n := by
    rw [hmassSync]
    exact
      abs_bankPaperCanonicalGuardedSmoothBaseMass_le_abs_mul_secondOrderScale
        R certificate deltaStar B.sampleData.W (K0 + 1) betaAct hn
  have hsharpBound :=
    hsharp B R certificate T deltaStar betaAct qTilde
      hNsharp hBW hsep hremaining hcanonical hmassSync _hpool p
  have hprincipal :
      |bankPaperCanonicalScaledActiveValuationMoment T qTilde p.1 -
          bankPaperCanonicalGuardedSmoothBaseValuationMoment (K := K0 + 1)
            B R certificate deltaStar betaAct p.1| ≤
        (|betaAct| * Csharp) * scale := by
    calc
      |bankPaperCanonicalScaledActiveValuationMoment T qTilde p.1 -
          bankPaperCanonicalGuardedSmoothBaseValuationMoment (K := K0 + 1)
            B R certificate deltaStar betaAct p.1| ≤
        |qTilde| * (Csharp / ((p.1 : Real) * B.L)) :=
          hsharpBound
      _ ≤ (|betaAct| * secondOrderScale B.sampleData.n) *
          (Csharp / ((p.1 : Real) * B.L)) := by
        exact mul_le_mul_of_nonneg_right hqBound
          (div_nonneg hCsharp.le (mul_nonneg hpR.le hL.le))
      _ = (|betaAct| * Csharp) * scale := by
        dsimp only [scale]
        ring
  have hnearestRaw :=
    abs_bankPaperCanonicalTopFrozenNearestIntegerValuationMoment_le
      (K := K0 + 1) B R certificate deltaStar betaProt
      (bankPaperCanonicalPostHfitBalancedAlpha
        B c K0 betaProt betaAct)
      qTilde Azero p.1 hp hAzero hmean
  have hnearest :
      |bankPaperCanonicalTopFrozenNearestIntegerValuationMoment
          (K := K0 + 1) B R certificate deltaStar betaProt
            (bankPaperCanonicalPostHfitBalancedAlpha
              B c K0 betaProt betaAct)
            qTilde p.1| ≤
        (Azero / 2) * scale := by
    calc
      |bankPaperCanonicalTopFrozenNearestIntegerValuationMoment
          (K := K0 + 1) B R certificate deltaStar betaProt
            (bankPaperCanonicalPostHfitBalancedAlpha
              B c K0 betaProt betaAct)
            qTilde p.1| ≤
        Azero / (2 * (p.1 : Real)) := hnearestRaw
      _ = (Azero / (2 * (p.1 : Real))) * 1 := by ring
      _ ≤ (Azero / (2 * (p.1 : Real))) *
          (secondOrderScale B.sampleData.n / B.L) := by
        exact mul_le_mul_of_nonneg_left hscaleOne
          (div_nonneg hAzero
            (mul_nonneg (by norm_num) hpR.le))
      _ = (Azero / 2) * scale := by
        dsimp only [scale]
        field_simp [hpR.ne', hL.ne']
  have hdecomp :=
    roughCanonicalTopFrozenRoundedSmoothSourceToGuardedValuationDefect_eq_scaled_sub_guardedBase_add_nearestInteger
      B K0 R certificate T deltaStar betaProt betaAct qTilde p.1
      (by omega : 1 ≤ B.sampleData.n) hdeltaUpper hvalues
  unfold RoughCanonicalTopFrozenRoundedSmoothSourceToGuardedValuationDefectBound
  rw [hdecomp]
  calc
    |bankPaperCanonicalScaledActiveValuationMoment T qTilde p.1 -
          bankPaperCanonicalGuardedSmoothBaseValuationMoment (K := K0 + 1)
            B R certificate deltaStar betaAct p.1 +
        bankPaperCanonicalTopFrozenNearestIntegerValuationMoment
          (K := K0 + 1) B R certificate deltaStar betaProt
            (bankPaperCanonicalPostHfitBalancedAlpha
              B c K0 betaProt betaAct)
            qTilde p.1| ≤
      |bankPaperCanonicalScaledActiveValuationMoment T qTilde p.1 -
          bankPaperCanonicalGuardedSmoothBaseValuationMoment (K := K0 + 1)
            B R certificate deltaStar betaAct p.1| +
        |bankPaperCanonicalTopFrozenNearestIntegerValuationMoment
          (K := K0 + 1) B R certificate deltaStar betaProt
            (bankPaperCanonicalPostHfitBalancedAlpha
              B c K0 betaProt betaAct)
            qTilde p.1| :=
      abs_add_le _ _
    _ ≤ (|betaAct| * Csharp) * scale + (Azero / 2) * scale :=
      add_le_add hprincipal hnearest
    _ = (|betaAct| * Csharp + Azero / 2) * scale := by ring
    _ ≤ Csource * scale := by
      exact mul_le_mul_of_nonneg_right
        (by dsimp only [Csource]; linarith) hscale0
    _ = Csource *
        (secondOrderScale B.sampleData.n /
          ((p.1 : Real) * B.L)) := by
      rfl

end BankPaperRealization

end

end Erdos390.WholePaper

end

universe u_1
theorem solution : Erdos390.RemainingAnalyticGoal007_013.{u_1} := by
  exact @Erdos390.WholePaper.BankPaperRealization.exists_uniform_topFrozenRoundedSmoothSourceToGuardedValuationDefectBound_paperRate
