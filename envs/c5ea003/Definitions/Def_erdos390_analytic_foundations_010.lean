-- Prove2me | Definitions.Def_erdos390_analytic_foundations_010
-- name    : erdos390_analytic_foundations_010
-- status  : Definition
-- author  : @doctosil
-- created : 2026-09-17T15:06:24.551459+00:00
-- url     : https://prove2.me/theorems/e62cfa14-9a6e-4880-b076-be0c66ff05a6
-- title:
--   Source-dependent correction rates and synchronized Section 9 inputs
-- statement:
--   This final bundle defines source-to-guarded valuation defects, implementation-rate predicates, exponent-band and multiplicative ratio-cell geometry, traffic and port majorants, Section 9 final-payload and terminal predicates, and coherent post-height bridge/source input structures.
--
--   Writing $d$ for clean-list density, $\sigma$ for slack, $\rho$ for the ratio parameter, $C_H$ for the tangent constant and $M(\rho)$ for the canonical ratio-cell main coefficient, the explicit paper choices are
--   $$w_* =\frac{d^2\sigma}{96M(\rho)C_H},\qquad e_* =\frac{d^2\sigma}{2304}.$$
--   The physical post-height target uses $\mu=\log(3/2)$ and the separated intervals $[1,4/3]$ and $[5/3,7/4]$. Associated constructors retain the common source, rounded seed, placed selector, head reserve and ordinary logarithmic target.
--
--   The synchronized analytic-completion predicate asks for one mesh, head set, bridge family and compatible constants satisfying the stated eventual size, active-mass and post-fitting conditions. The depth-indexed terminal predicates similarly record the exact payload required downstream. These are definitions of obligations and interfaces; they do not assert that the terminal or completion exists.
-- source:
--   https://github.com/ShouqiaoW/erdos/blob/61325b10bbdc29f4fb5e0618b414b9f2189333ad/390/lean/Erdos390/WholePaper/BankPaperCanonicalSectionNineTopFrozenSynchronizedAnalyticCompletionConnector.lean; grouped definitions extracted from multiple source modules at this commit, including Erdos390.WholePaper.BankPaperCanonicalArbitrarySourceSelectorDeficitPaperRateClosureConnector, Erdos390.WholePaper.BankPaperCanonicalImplementationDefectRateReductionConnector, Erdos390.WholePaper.BankPaperCanonicalTopFrozenImplementationRateReductionConnector, with the remaining originating modules identified by source-module comments in the definition body.

import Mathlib
import Definitions.Def_erdos390_source_bank_interface
import Definitions.Def_erdos390_dickman_step_function
import Theorems.Thm_MediumPNT
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_product_bound
import Theorems.Thm_Erdos390_Full_DickmanBasic_rho_pos_on_zero_five
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_secondDerivative_first_bound
import Definitions.Def_erdos390_analytic_foundations_009


/- Source module: Erdos390.WholePaper.BankPaperCanonicalArbitrarySourceSelectorDeficitPaperRateClosureConnector -/
section


/-!
# Selector-deficit paper-rate closure for an arbitrary verified source

The original selector-deficit closure is specialized to the legacy
no-top Post-Hfit source.  The actual Section 8 producer can instead start
from an arbitrary verified source, and in particular from the rounded
frozen-top source.  This file transports the exact residual bookkeeping to
that interface without identifying either source with the legacy selector.

For a supplied `sourceSelector`, its raw-correction defect splits
unconditionally into

* the source moment minus the implemented guarded postcharge correction;
* the guarded postcharge correction minus the older raw-pool correction.

After structured placement this gives the same seven visible terms as in
the legacy closure: the four complete-residual terms, the two implementation
defects, and the placement moment.  The quantitative theorem deliberately
retains all three implementation bounds as inputs.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.PaperBridgeFit
open Erdos390.Full.PaperGuardCensus
open Erdos390.Full.Scale

noncomputable section

namespace BankPaperRealization

/-! ## Source-parametric correction defects -/

/-- The correction moment of an arbitrary source minus the correction
actually installed on the guarded postcharge pools. -/
def roughCanonicalSourceToGuardedCorrectionValuationDefect
    {c : Real} {depth n W K : Nat}
    (R : BankPaperRealization n
      (upperEndpoint n (upperTailLength c n)))
    (certificate : GuardedCentralAnchorCertificate c depth n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (deltaStar alpha beta ell : Real)
    (sourceSelector : Nat -> Real) (p : Nat) : Real :=
  roughCanonicalSourceValuationCorrectionMoment
      (W := W) (K := K)
      R certificate deltaStar alpha beta ell sourceSelector p -
    R.roughCanonicalAggregateGuardedPostchargeRowCorrection certificate
      deltaStar W K alpha beta ell p



/-! ## A named source-parametric complete residual -/

/-- The four-term complete signed residual at arbitrary raw-weight
parameters.  Naming it keeps the source-parametric closure readable. -/
def roughCanonicalParameterizedCompleteSignedResidual
    {c : Real} {depth n : Nat}
    (R : BankPaperRealization n
      (upperEndpoint n (upperTailLength c n)))
    (W K : Nat)
    (certificate : GuardedCentralAnchorCertificate c depth n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (deltaStar alpha beta ell : Real) (p : Nat) : Real :=
  roughCanonicalCompleteSignedResidual
    (roughCanonicalRawSignedValuationResidual n
      (upperTailLength c n) K
      (roughHeadCompatibleRawWeight W n (upperTailLength c n) K
        alpha beta ell) p)
    (roughCanonicalSignedExceptionalResidual n
      (upperTailLength c n) K deltaStar
      (roughHeadCompatibleRawWeight W n (upperTailLength c n) K
        alpha beta ell) p)
    (roughCanonicalAggregateRawRowCorrection W n
      (upperTailLength c n) K deltaStar alpha beta ell p)
    (R.roughCanonicalAggregateGuardResidual certificate deltaStar K
      (roughHeadCompatibleRawWeight W n (upperTailLength c n) K
        alpha beta ell) p)



/-! ## Exact seven-term identity for an arbitrary source -/





/-! ## Quantitative arbitrary-source interface -/

/-- The three implementation estimates needed after the generic four-term
complete residual has been bounded. -/
def BankPaperCanonicalMediumPrimeImplementationRateInputsOfSource
    {Head Band : Type*} [Fintype Head] [DecidableEq Head]
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData Head Band)
    {c : Real} {depth K : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (deltaStar betaProt alpha beta ell : Real)
    (sourceSelector : Nat -> Real)
    (placementSeed : B.sampleData.Sample -> Real)
    (p : Nat)
    (scale Csource CguardedRaw Cplacement : Real) : Prop :=
  abs
      (roughCanonicalSourceToGuardedCorrectionValuationDefect
        (W := B.sampleData.W) (K := K)
        R certificate deltaStar alpha beta ell sourceSelector p) <=
        Csource * scale ∧
    abs
      (R.roughCanonicalAggregateGuardedRawCorrectionValuationDefect
        certificate deltaStar B.sampleData.W K
          alpha beta ell p) <=
        CguardedRaw * scale ∧
    abs
      (bankPaperCanonicalGuardedStructuredAdditivePlacementValuationMoment
        (K := K) B R certificate deltaStar betaProt
          sourceSelector placementSeed p) <=
        Cplacement * scale



/-! ## Frozen-top balanced specialization -/



/-- The implementation-rate package specialized to the balanced rounded
frozen-top source. -/
def BankPaperCanonicalTopFrozenRoundedMediumPrimeImplementationRateInputs
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
    (placementSeed : B.sampleData.Sample -> Real)
    (p : Nat)
    (scale Csource CguardedRaw Cplacement : Real) : Prop :=
  BankPaperCanonicalMediumPrimeImplementationRateInputsOfSource
    (K := K0 + 1) B R certificate deltaStar betaProt
      (bankPaperCanonicalPostHfitBalancedAlpha
        B c K0 betaProt betaAct)
      (betaProt + betaAct) B.L
      (bankPaperCanonicalTopFrozenRoundedSourceSelector
        (K := K0 + 1) B R certificate T deltaStar betaProt
          (bankPaperCanonicalPostHfitBalancedAlpha
            B c K0 betaProt betaAct)
          (betaProt + betaAct) qTilde)
      placementSeed p scale Csource CguardedRaw Cplacement



end BankPaperRealization

end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankPaperCanonicalImplementationDefectRateReductionConnector -/
section


/-!
# Quantitative reduction of the two selector implementation defects

The selector-deficit closure leaves two implementation terms:

* the actual Post-Hfit source moment minus the correction installed on the
  guarded nonsmooth pools;
* that guarded correction minus the older correction on raw pools.

This file reduces both terms without identifying either pair of moments by
fiat.  The first defect is partitioned by complete rough rows.  The already
proved pointwise formula for the global source kills every nonsmooth row,
so only the literal smooth-row defect remains.  The second defect is bounded
by the exact two rowwise quantities from the guarded/raw defect formula:
the normalized pool-moment shift and the postcharge numerator shift.

The finite guard census is used once more to bound the latter numerator
shift by `1 + 3 M` whenever the raw row coordinates have absolute value at
most `M`.  Thus any later analytic estimate sees the precise pool-moment
input that is still required rather than an unjustified reindex.
-/

open Filter Topology
open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.PaperBridgeFit

noncomputable section

namespace BankPaperRealization

/-! ## Row partition of the source-to-guarded defect -/

/-- The contribution of one raw complete-rough label to the difference
between an actual source correction moment and a supplied family of guarded
row-correction moments.  The second sum uses the literal nonexceptional
guarded set, so the definition remains valid without deciding whether the
smooth label itself is exceptional. -/
def roughCanonicalSourceGuardedRowValuationDefectAtLabel
    {c : Real} {depth n : Nat}
    (R : BankPaperRealization n
      (upperEndpoint n (upperTailLength c n)))
    (certificate : GuardedCentralAnchorCertificate c depth n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (deltaStar : Real) (K : Nat)
    (selector rawWeight : Nat -> Real)
    (guardedCorrection : Nat -> Real) (p label : Nat) : Real :=
  by
    classical
    exact
      (∑ a ∈ R.roughCanonicalGuardedRow certificate deltaStar K label,
          selector a * (a.factorization p : Real)) -
        (∑ a ∈ completeRoughRowFiber (yNat n)
            (R.roughCanonicalNonexceptionalGuardedCandidateSet certificate
              deltaStar K) label,
          rawWeight a * (a.factorization p : Real)) -
        if RoughCanonicalActiveNonexceptionalLabel n deltaStar label then
          guardedCorrection label
        else
          0







/-! ## Post-Hfit specialization and nonsmooth cancellation -/

















/-! ## Rowwise guarded/raw rate majorant -/































/-! ## The finite numerator-shift estimate already available from guards -/



/-! ## Direct connector to the existing implementation-rate package -/







end BankPaperRealization

end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankPaperCanonicalTopFrozenImplementationRateReductionConnector -/
section


/-!
# Literal implementation-rate reductions for the rounded frozen-top source

The balanced selector-deficit identity for the rounded frozen-top source
contains three implementation terms.  This file connects each of them to
the strongest already justified finite reduction, without identifying the
frozen-top source with the older no-top source.

* The source-to-guarded defect is partitioned into complete rough rows.
  Every nonsmooth row cancels for the literal frozen-top selector, leaving
  exactly one guarded smooth-row defect.
* The guarded/raw defect is source-independent, so its existing rowwise
  pool-moment and numerator-shift majorant applies literally.
* A second two-zero-cell rebalance has the existing uniform-cell valuation
  moment whenever the retained outside part of the frozen-top source agrees
  with its old tagged seed on occupied active coordinates.  That compatibility
  is stated explicitly; it is not inferred by confusing the top source with
  the legacy source.

The only quantitative inputs left by the final constructor are therefore
the smooth-row mismatch, the guarded/raw rowwise majorant, the two uniform
cell valuation means, and the absolute two-cell mass budget.
-/

open Filter
open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.PaperBridgeFit
open Erdos390.Full.PaperGuardCensus
open Erdos390.Full.Scale

noncomputable section

namespace BankPaperRealization

/-! ## Source-parametric nonsmooth cancellation -/

/-- The row contribution to the source-to-guarded defect for an arbitrary
source, with the literal raw weight and guarded postcharge correction. -/
def roughCanonicalPostchargeSourceGuardedRowValuationDefectAtLabel
    {c : Real} {depth n : Nat}
    (R : BankPaperRealization n
      (upperEndpoint n (upperTailLength c n)))
    (certificate : GuardedCentralAnchorCertificate c depth n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (deltaStar : Real) (W K : Nat) (alpha beta ell : Real)
    (sourceSelector : Nat -> Real) (p label : Nat) : Real :=
  R.roughCanonicalSourceGuardedRowValuationDefectAtLabel certificate
    deltaStar K sourceSelector
    (roughHeadCompatibleRawWeight W n (upperTailLength c n) K
      alpha beta ell)
    (fun rowLabel =>
      R.roughCanonicalGuardedPostchargeRowCorrectionValuationMomentAtLabel
        certificate deltaStar W K rowLabel alpha beta ell p)
    p label







/-- The one possible surviving row in an arbitrary source-to-guarded
defect.  The membership test handles an empty raw smooth row. -/
def roughCanonicalSmoothSourceToGuardedValuationDefect
    {c : Real} {depth n : Nat}
    (R : BankPaperRealization n
      (upperEndpoint n (upperTailLength c n)))
    (certificate : GuardedCentralAnchorCertificate c depth n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (deltaStar : Real) (W K : Nat) (alpha beta ell : Real)
    (sourceSelector : Nat -> Real) (p : Nat) : Real :=
  if 1 ∈ completeRoughLabelSet (yNat n)
      (roughRawCandidateSet n (upperTailLength c n) K) then
    R.roughCanonicalPostchargeSourceGuardedRowValuationDefectAtLabel
      certificate deltaStar W K alpha beta ell sourceSelector p 1
  else
    0



/-! ## Literal rounded frozen-top source reduction -/

/-- The surviving smooth-row mismatch for the literal rounded frozen-top
source at balanced depth `K0 + 1`. -/
def roughCanonicalTopFrozenRoundedSmoothSourceToGuardedValuationDefect
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
    (p : Nat) : Real :=
  R.roughCanonicalSmoothSourceToGuardedValuationDefect certificate
    deltaStar B.sampleData.W (K0 + 1)
    (bankPaperCanonicalPostHfitBalancedAlpha
      B c K0 betaProt betaAct)
    (betaProt + betaAct) B.L
    (bankPaperCanonicalTopFrozenRoundedSourceSelector
      (K := K0 + 1) B R certificate T deltaStar betaProt
        (bankPaperCanonicalPostHfitBalancedAlpha
          B c K0 betaProt betaAct)
        (betaProt + betaAct) qTilde)
    p



/-- The smallest quantitative source input left after nonsmooth
cancellation: a bound for the literal rounded frozen-top smooth row. -/
def RoughCanonicalTopFrozenRoundedSmoothSourceToGuardedValuationDefectBound
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
    (p : Nat) (bound : Real) : Prop :=
  abs
      (roughCanonicalTopFrozenRoundedSmoothSourceToGuardedValuationDefect
        B K0 R certificate T deltaStar betaProt betaAct qTilde p) <=
    bound



/-! ## The two literal non-placement defect inputs -/







/-! ## Source-parametric two-zero placement moment -/





/-! ## Literal frozen-top placement specialization -/

/-- The exact compatibility needed to reuse the two-zero-cell placement
formula for the rounded frozen-top source.  It only concerns occupied
structured active coordinates outside the protected broad pool. -/
def BankPaperCanonicalTopFrozenRoundedPlacementOutsideCompatibility
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
    (deltaStar betaProt alpha beta qTilde : Real) : Prop :=
  ∀ a,
    a ∈ bankPaperCanonicalStructuredActiveValues B.sampleData ->
    a ∉ R.roughCanonicalGuardedBroadCorrectionPool certificate
      deltaStar B.sampleData.W K 1 ->
    bankPaperCanonicalGlobalCorrectedOutsideSelectorWithTop (K := K)
        B R certificate deltaStar alpha beta
          (bankPaperCanonicalTopFrozenRoundedActiveSeed (K := K)
            B R certificate T deltaStar betaProt alpha qTilde) a =
      bankPaperCanonicalActiveSeedAmbientWeight B.sampleData
        (bankPaperCanonicalTopFrozenRoundedActiveSeed (K := K)
          B R certificate T deltaStar betaProt alpha qTilde) a

/-- A concrete sufficient form of outside compatibility: the restored
top weight vanishes on the relevant structured active coordinates. -/
def BankPaperCanonicalTopFrozenSmoothTopInvisibleOnStructuredActive
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
    (deltaStar alpha : Real) : Prop :=
  ∀ a,
    a ∈ bankPaperCanonicalStructuredActiveValues B.sampleData ->
    a ∉ R.roughCanonicalGuardedBroadCorrectionPool certificate
      deltaStar B.sampleData.W K 1 ->
    bankPaperCanonicalSmoothTopWeight B.sampleData.W B.sampleData.n
      (upperTailLength c B.sampleData.n) K alpha B.L a = 0







/-! ## Complete three-input constructor -/



end BankPaperRealization

end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankPaperCanonicalTopFrozenRoundedSourceStateEventualConnector -/
section


/-!
# Eventual construction of the frozen-top rounded source state

The finite nearest-integer connector reduces the frozen-top source state to
three kinds of input:

* canonical sample geometry and the capacities of the two zero-head cells;
* feasibility of the literal `qTilde` source and its charged nonsmooth rows;
* exact selector-tail agreement outside the medium-prime band.

The first group is already asymptotic.  Canonical sample geometry is
provided by
`bankPaperCanonicalSectionEight_twoZeroHeadCell_geometryInputs`.  The
generic two-cell scalar-capacity theorem also supplies the initialization
capacity once it is applied to the uniformly bounded change
`(q0 - qTilde) / 2`.

This file packages that reuse.  The remaining residual input records only
the three facts for which the repository has no source-specific producer:
literal `qTilde` feasibility, charged nonsmooth rows, and literal `qTilde`
selector-tail support.  The zero-head correction is proved below to preserve
that support.  The equality identifying the analytic family `mFrozen` with
the concrete frozen-top row mass is also kept explicit at the eventual
synchronization boundary.
-/

open Filter Topology Asymptotics
open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.PaperBridgeFit
open Erdos390.Full.PaperGuardCensus
open Erdos390.Full.Scale

noncomputable section

namespace BankPaperRealization

/-! ## The initial-only cell change and its capacity -/

/-- The nearest-integer change placed in one zero-head cell, as an
asymptotic family. -/
def bankPaperCanonicalSymmetricInitialCellMassFamily
    (mFrozen qTilde : Nat -> Real) (n : Nat) : Real :=
  bankPaperCanonicalSymmetricInitialAndHeightCellMass
    (mFrozen n) (qTilde n) 0





/-! ## Selector-tail support transport -/









/-! ## Exact residual input -/

/-- The source-specific facts not supplied by canonical geometry or the
Section 8 analytic capacity argument.

The first conjunct is feasibility before nearest-integer rounding.  The
second is the charged nonsmooth-row realization already used by the
frozen-top initial-mass theorem.  The third is the exact selector-tail
support identity for that same literal source; it transports to the rounded
source by the preceding theorem. -/
def BankPaperCanonicalTopFrozenRoundedSourceResidualInputsAt
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
    (fixed : Finset Nat)
    (T : BarycentricTarget B.sampleData)
    (deltaStar betaProt alpha betaTotal qTilde : Real) : Prop :=
  (∀ a ∈ R.roughCanonicalGuardedCandidateSet certificate deltaStar K,
      0 <= bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop (K := K)
          B R certificate deltaStar betaProt alpha betaTotal
            (bankPaperCanonicalScaledActiveSeed T qTilde) a ∧
        bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop (K := K)
          B R certificate deltaStar betaProt alpha betaTotal
            (bankPaperCanonicalScaledActiveSeed T qTilde) a <= 1) ∧
    BankPaperCanonicalChargedNonsmoothRowRealization
      (K := K) R certificate deltaStar
        (bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop (K := K)
          B R certificate deltaStar betaProt alpha betaTotal
            (bankPaperCanonicalScaledActiveSeed T qTilde)) ∧
    BankPaperCanonicalSelectorDeficitSupportedOnPrimeBand
      (W := B.sampleData.W) R certificate fixed
      (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
      (bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop (K := K)
        B R certificate deltaStar betaProt alpha betaTotal
          (bankPaperCanonicalScaledActiveSeed T qTilde))

/-! ## Finite assembly -/



/-! ## Eventual canonical supplier -/



end BankPaperRealization

end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankPaperCanonicalP87TargetEnvelopeConnector -/
section


/-!
# Finite target envelopes from the canonical selector residual

The paper obtains the slow target estimate from two genuinely different
inputs:

* the pointwise medium-prime residual rate; and
* exact ordinary-log compatibility
  `sum_p t_p r_p = 0`.

The latter is not implied by the current guarded-selector state.  This file
therefore names it explicitly and proves only the finite algebra which
follows from it.  In particular, no selector construction or logarithmic
compatibility theorem is hidden in a structure field.

For a residual `r_p`, exact compatibility rewrites

`sum_j alpha_j Delta_j = sum_p (alpha_{j(p)} - t_p) r_p`.

The pointwise rate and the literal prime-deviation `L¹` bound then give the
two target envelopes, with the uniform constant enlarged from `Cinitial` to
`7 * Cinitial`.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.ArithmeticBandGeometry
open Erdos390.Full.PaperBridgeFit
open Erdos390.Full.PaperGuardCensus

noncomputable section

/-! ## The explicit ordinary-log input -/

/-- Exact normalized ordinary-log compatibility of the prebridge selector.

This is the finite identity used in the paper after the head, physical, and
frozen logarithmic ledgers have been fitted.  It is deliberately a visible
input: the currently constructed guarded-selector state does not yet prove
it. -/
def BankPaperCanonicalSelectorOrdinaryLogCompatible
    {c : Real} {depth n W : Nat} {left right : Nat -> Nat}
    {changed : Finset Nat}
    (R : BankPaperRealization n
      (upperEndpoint n (upperTailLength c n)))
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (fixed candidates : Finset Nat) (selector : Nat -> Real) : Prop :=
  ∑ p : BankPaperCanonicalTangentPrime n W,
      tPrime n p.1 *
        bankPaperCanonicalTangentResidual
          R certificate fixed candidates selector p = 0

/-! ## General finite residual algebra -/





/-! ## Specialization to the literal initial P87 residual -/



end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankPaperCanonicalSectionNinePostHeightOrdinaryLogLedgerConnector -/
section


/-!
# Exact post-height ordinary-log ledger

The post-height baseline realizes the paper's ordinary logarithm exactly.
This file connects that finite moment to the residual selector target.

There are two logically separate ingredients.

* The target/frozen charge ledger identifies the logarithm left for the
  fractional selector after the fixed factors and the state-zero bank.
* Primewise source support says that every valuation deficit outside
  `W < p <= y` is already zero.

Together with the exact post-height moment these imply that the
`tPrime`-weighted initial residual is zero.  No ordinary-log compatibility,
weighted-residual identity, or target envelope is assumed as an input.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.PaperBridgeFit
open Erdos390.Full.PaperGuardCensus
open Erdos390.Full.PaperHeadSimplex

noncomputable section

/-! ## A finite factorization support for a selector -/

/-- The finite set containing every prime occurring in either the residual
target or one of the numerical selector coordinates. -/
def bankPaperCanonicalSelectorLogSupport
    (target : Nat) (candidates : Finset Nat) : Finset Nat :=
  target.factorization.support ∪
    candidates.biUnion fun a => a.factorization.support





/-! ## Ordinary logarithm equals the logarithmically weighted deficit -/







/-! ## Exact active/frozen logarithmic decomposition -/





/-! ## The exact selector-tail charge -/





/-! ## The fresh post-height seed realizes `logY - Lambda0` -/



/-! ## Complete post-height selector ledger -/









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

/-- If the canonical active seed is scaled by the literal guarded smooth
base mass, then its finite total mass is exactly that base mass.  This is
the canonical specialization of the paper's definition of `qTilde`; the
error is identically zero. -/
@[simp] theorem
    bankPaperCanonicalLiteralActiveMass_scaledGuardedSmoothBase_eq
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
    (deltaStar betaAct : Real) :
    bankPaperCanonicalLiteralActiveMass B.sampleData
        (bankPaperCanonicalScaledActiveSeed T
          (bankPaperCanonicalGuardedSmoothBaseMass R certificate
            deltaStar B.sampleData.W K betaAct)) =
      bankPaperCanonicalGuardedSmoothBaseMass R certificate
        deltaStar B.sampleData.W K betaAct := by
  exact bankPaperCanonicalLiteralActiveMass_scaledActiveSeed T _

/-! ## The three literal valuation moments -/

/-- The valuation moment of the scaled barycentric active seed. -/
def bankPaperCanonicalScaledActiveValuationMoment
    {Head : Type*} [Fintype Head]
    {D : StructuredSampleData Head}
    (T : BarycentricTarget D) (q : Real) (p : Nat) : Real :=
  ∑ m : D.Sample,
    bankPaperCanonicalScaledActiveSeed T q m *
      valuation p (D.value m)

/-- The valuation moment of the constant guarded active broad layer. -/
def bankPaperCanonicalGuardedSmoothBaseValuationMoment
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
    (deltaStar betaAct : Real) (p : Nat) : Real :=
  betaAct / B.L *
    ∑ a ∈ R.roughCanonicalGuardedBroadCorrectionPool certificate
        deltaStar B.sampleData.W K 1,
      valuation p a

/-- The valuation moment added by the two equal nearest-integer
increments in the physical copies of the zero head cell. -/
def bankPaperCanonicalTopFrozenNearestIntegerValuationMoment
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
    (deltaStar betaProt alpha qTilde : Real) (p : Nat) : Real :=
  let cellMass :=
    bankPaperCanonicalTopFrozenNearestIntegerCellMass (K := K)
      B R certificate deltaStar betaProt alpha qTilde
  cellMass *
      (B.guardedCellProbability (none, .minus)).expect
        (fun m ↦ valuation p (m : Nat)) +
    cellMass *
      (B.guardedCellProbability (none, .plus)).expect
        (fun m ↦ valuation p (m : Nat))



/-! ## Exact label-one source decomposition -/







end BankPaperRealization

end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankPaperCanonicalBalancedRawSignedValuationResidualBoundConnector -/
section


/-!
# The balanced raw signed valuation residual

The raw signed residual is the one generic term left as a premise in the
four-term paper-rate closure.  This file proves it directly from the
elementary fixed-modulus interval count.

For a fixed prime `p`, every valuation is expanded into the indicators of
`p ^ k` divisibility.  At one exponent, the upper interval has endpoint
error less than one, while each of the two head-free lower intervals has
error at most `roughHeadModulus W + 1`.  The three real-length main terms
cancel exactly by `roughHeadBalancedAlpha_length_normalization`.

The resulting finite bound is logarithmic in the physical endpoint.  The
last section absorbs that logarithm uniformly for `p <= yNat n` into the
paper scale `secondOrderScale n / (p * L n)`.
-/

open Filter Topology
open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.Scale

noncomputable section

namespace BankPaperRealization

/-! ## Valuations as finite prime-power column sums -/









/-! ## The literal one-column residual -/



/-- The upper-minus-high-minus-broad discrepancy at one prime-power
divisibility column. -/
def roughCanonicalRawPrimePowerColumnResidual
    (W n h K : Nat) (alpha beta ell : Real) (p k : Nat) : Real :=
  (((roughUpperBlock n h).filter (fun a => p ^ k ∣ a)).card : Real) -
    alpha *
      ((coprimeMultipleIoc (roughHeadModulus W) (p ^ k)
        (2 * n - K * h) (2 * n)).card : Real) -
    (beta / ell) *
      ((coprimeMultipleIoc (roughHeadModulus W) (p ^ k)
        n (2 * n - K * h)).card : Real)









/-! ## Fixed constants for the balanced point -/

/-- Fixed upper bound for one prime-power column after inserting the
balanced coefficient and requiring `L n >= 1`. -/
noncomputable def roughCanonicalBalancedRawPrimePowerColumnConstant
    (W K0 : Nat) (c beta : Real) : Real :=
  1 +
    (roughBalancedAlphaConstant W K0 c beta + abs beta) *
      ((roughHeadModulus W : Real) + 1)



/-- The explicit constant in the eventual paper-rate bound.  The factor
`5 / log 2` converts the exponent count to the existing
`5 * log (yNat n)` endpoint chamber. -/
noncomputable def roughCanonicalBalancedRawSignedValuationConstant
    (W K0 : Nat) (c beta : Real) : Real :=
  (5 / Real.log 2) *
    roughCanonicalBalancedRawPrimePowerColumnConstant W K0 c beta







/-! ## Eventual paper-rate absorption -/





end BankPaperRealization

end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankPaperCanonicalRatioCellGeometry -/
section


/-!
# Canonical exponent bands and merged multiplicative ratio cells

This file supplies the elementary geometry missing between the canonical
regular exponent mesh and the explicit ratio-cell earthmover.

For a natural lower endpoint `A` and a fixed real `rho > 1`, the raw
multiplicative cutoffs are

`floor (A * rho ^ k)`.

The raw cell of a label is the first interval

`(floor (A * rho ^ k), floor (A * rho ^ (k+1))]`

which contains it.  In each canonical exponent band the final raw fragment
is merged into its predecessor.  Thus a merged cell contains at most two raw
cells, and adjacent merged cells span at most three powers of `rho`.  This is
the exact reason that the paper chooses `rho ^ 3 < r0`.

Everything in this module is finite and elementary.  The final section
isolates the one genuinely analytic input still needed for the earthmover:
prime occupancy of every full fixed-ratio interval.  No prime-distribution
statement is stored in the geometry construction.
-/

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.ArithmeticBandGeometry
open Erdos390.Full.PositiveCellTransfer
open Erdos390.Full.RegularRelativeMesh
open Erdos390.Full.RegularMeshPrimeCutoffs

noncomputable section

/-! ## Raw multiplicative cells -/

/-- The natural cutoff `floor (A * rho^k)` used by a multiplicative cell. -/
def tangentMultiplicativeRatioCutoff
    (lower : Nat) (rho : Real) (k : Nat) : Nat :=
  ⌊(lower : Real) * rho ^ k⌋₊

@[simp]
theorem tangentMultiplicativeRatioCutoff_zero
    (lower : Nat) (rho : Real) :
    tangentMultiplicativeRatioCutoff lower rho 0 = lower := by
  simp [tangentMultiplicativeRatioCutoff]



/-- Powers of a fixed `rho > 1` eventually cover every natural label. -/
theorem exists_label_le_tangentMultiplicativeRatioCutoff_succ
    {lower : Nat} {rho : Real}
    (hlower : 0 < lower) (hrho : 1 < rho) (label : Nat) :
    ∃ k : Nat,
      label <= tangentMultiplicativeRatioCutoff lower rho (k + 1) := by
  have hlowerReal : 0 < (lower : Real) := by exact_mod_cast hlower
  obtain ⟨k, hk⟩ :=
    pow_unbounded_of_one_lt ((label : Real) / (lower : Real)) hrho
  exact ⟨k, by
    apply Nat.le_floor
    have hk' : (label : Real) < (lower : Real) * rho ^ k := by
      have := (div_lt_iff₀ hlowerReal).mp hk
      simpa only [mul_comm] using this
    have hpow : rho ^ k <= rho ^ (k + 1) :=
      pow_le_pow_right₀ (by linarith) (by omega)
    exact hk'.le.trans
      (mul_le_mul_of_nonneg_left hpow hlowerReal.le)⟩

/-- The first raw multiplicative cell whose upper cutoff contains `label`.
The totalized branches are irrelevant in the paper range, where `lower > 0`
and `rho > 1`; keeping the definition total avoids proof arguments in the
cell-index function consumed by the earthmover. -/
def tangentMultiplicativeRawCellIndex
    (lower label : Nat) (rho : Real) : Nat :=
  if h : 0 < lower ∧ 1 < rho then
    Nat.find
      (exists_label_le_tangentMultiplicativeRatioCutoff_succ
        h.1 h.2 label)
  else 0













/-! ## Merging the terminal fragment -/

/-- The paper merges the final raw fragment into its predecessor. -/
def tangentMergedRatioCellIndex (lastRaw raw : Nat) : Nat :=
  min raw (lastRaw - 1)

/-- Last index after merging the terminal raw fragment. -/
def tangentMergedRatioLastCell (lastRaw : Nat) : Nat :=
  lastRaw - 1

















/-! ## The canonical paper exponent bands -/

/-- The finite exponent-band type: one moving low band followed by the
positive regular relative mesh. -/
abbrev BankPaperCanonicalExponentBand
    {delta eta : Real} (M : RegularRelativeMesh.Mesh delta eta) :=
  Fin (M.cellCount + 1)

/-- Exact canonical band assignment already used by the Section 8
arithmetic partition. -/
def bankPaperCanonicalExponentBandOf
    {delta eta : Real} (M : RegularRelativeMesh.Mesh delta eta)
    {n W : Nat} (hdelta : 0 < delta) (hn : 1 < n)
    (hW : W ≠ 0) (S : ScaleSeparation M n W)
    (p : BankPaperCanonicalTangentPrime n W) :
    BankPaperCanonicalExponentBand M :=
  (RegularMeshPrimeCutoffs.Mesh.canonicalPartition
    M hdelta hn hW S).band p

/-- Natural lower endpoint of one canonical exponent band. -/
def bankPaperCanonicalExponentBandLower
    {delta eta : Real} (M : RegularRelativeMesh.Mesh delta eta)
    (n W : Nat) (band : BankPaperCanonicalExponentBand M) : Nat :=
  fullCutoff M n W band.1

/-- Natural upper endpoint of one canonical exponent band. -/
def bankPaperCanonicalExponentBandUpper
    {delta eta : Real} (M : RegularRelativeMesh.Mesh delta eta)
    (n W : Nat) (band : BankPaperCanonicalExponentBand M) : Nat :=
  fullCutoff M n W (band.1 + 1)





/-- Raw `rho`-cell index of a canonical tangent prime inside its exact
Section 8 exponent band. -/
def bankPaperCanonicalRawRatioCellIndex
    {delta eta : Real} (M : RegularRelativeMesh.Mesh delta eta)
    {n W : Nat} (hdelta : 0 < delta) (hn : 1 < n)
    (hW : W ≠ 0) (S : ScaleSeparation M n W)
    (rho : Real) (p : BankPaperCanonicalTangentPrime n W) : Nat :=
  tangentMultiplicativeRawCellIndex
    (bankPaperCanonicalExponentBandLower M n W
      (bankPaperCanonicalExponentBandOf M hdelta hn hW S p))
    p.1 rho

/-- Index of the terminal raw fragment in one canonical exponent band. -/
def bankPaperCanonicalLastRawRatioCell
    {delta eta : Real} (M : RegularRelativeMesh.Mesh delta eta)
    {n W : Nat} (rho : Real)
    (band : BankPaperCanonicalExponentBand M) : Nat :=
  tangentMultiplicativeRawCellIndex
    (bankPaperCanonicalExponentBandLower M n W band)
    (bankPaperCanonicalExponentBandUpper M n W band) rho

/-- Last occupied index expected by the earthmover after the possible
terminal raw fragment is merged. -/
def bankPaperCanonicalLastRatioCell
    {delta eta : Real} (M : RegularRelativeMesh.Mesh delta eta)
    {n W : Nat} (rho : Real)
    (band : BankPaperCanonicalExponentBand M) : Nat :=
  tangentMergedRatioLastCell
    (bankPaperCanonicalLastRawRatioCell M (n := n) (W := W) rho band)

/-- Merged canonical ratio-cell index. -/
def bankPaperCanonicalRatioCellIndex
    {delta eta : Real} (M : RegularRelativeMesh.Mesh delta eta)
    {n W : Nat} (hdelta : 0 < delta) (hn : 1 < n)
    (hW : W ≠ 0) (S : ScaleSeparation M n W)
    (rho : Real) (p : BankPaperCanonicalTangentPrime n W) : Nat :=
  tangentMergedRatioCellIndex
    (bankPaperCanonicalLastRawRatioCell M (n := n) (W := W) rho
      (bankPaperCanonicalExponentBandOf M hdelta hn hW S p))
    (bankPaperCanonicalRawRatioCellIndex M hdelta hn hW S rho p)











/-! ## Exact analytic occupancy boundary -/

/-- Uniform fixed-ratio prime occupancy above one fixed cutoff.  This is the
precise PNT consequence needed to populate all *full* raw cells. -/
def TangentFixedRatioPrimeIntervalOccupied
    (W : Nat) (rho : Real) : Prop :=
  forall A : Nat, W <= A ->
    ∃ p : Nat, p.Prime ∧ A < p ∧ p <= ⌊rho * (A : Real)⌋₊





end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankPaperCanonicalRatioCellTraffic -/
section


/-!
# Analytic envelopes for the canonical ratio cells

This file is the first analytic layer after the concrete ratio-cell
geometry.  It makes three facts explicit.

* A strict tail after cell `cut` lies between the next multiplicative
  cutoff and the upper endpoint of its canonical exponent band.  Capping
  the lower endpoint by the band upper endpoint makes the statement valid
  for every natural `cut`, including vacuous cuts beyond the last cell.
* Every full raw interval contained in a merged cell injects into the
  actual finite cell.  The fixed-ratio PNT therefore gives a quantitative
  lower bound for the literal denominator used by the distributed port.
* Uniform Mertens and the PNT denominator combine into finite cut-traffic
  and pointwise-port envelopes.  No mesh sum is estimated here: the final
  Riemann-sum collapse is deliberately left as a separate analytic step.

There are no new distribution hypotheses.  The only asymptotic inputs are
the audited safe PNT and uniform reciprocal-prime estimate already present
in the repository.
-/

open Filter Topology
open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.PrimeSums
open Erdos390.Full.PrimeBandQuadrature
open Erdos390.Full.RegularRelativeMesh
open Erdos390.Full.RegularMeshPrimeCutoffs

noncomputable section

/-! ## Concrete endpoints for strict cell tails -/

/-- The next raw multiplicative cutoff, capped by the exponent-band upper
endpoint.  The cap makes this a valid endpoint even for a vacuous cut past
the last canonical cell. -/
def bankPaperCanonicalRatioCellTailLower
    {delta eta : Real} (M : RegularRelativeMesh.Mesh delta eta)
    (n W : Nat) (rho : Real)
    (band : BankPaperCanonicalExponentBand M) (cut : Nat) : Nat :=
  min
    (tangentMultiplicativeRatioCutoff
      (bankPaperCanonicalExponentBandLower M n W band) rho (cut + 1))
    (bankPaperCanonicalExponentBandUpper M n W band)

/-- The upper endpoint of a canonical ratio-cell strict tail. -/
def bankPaperCanonicalRatioCellTailUpper
    {delta eta : Real} (M : RegularRelativeMesh.Mesh delta eta)
    (n W : Nat) (band : BankPaperCanonicalExponentBand M) : Nat :=
  bankPaperCanonicalExponentBandUpper M n W band









/-! ## Uniform Mertens envelope on the concrete tails -/

/-- The explicit Mertens majorant attached to one canonical strict tail. -/
def bankPaperCanonicalRatioCellTailMajorant
    {delta eta : Real} (M : RegularRelativeMesh.Mesh delta eta)
    (n W : Nat) (rho scale : Real)
    (band : BankPaperCanonicalExponentBand M) (cut : Nat) : Real :=
  bankPaperCanonicalHarmonicTailMajorant scale
    (bankPaperCanonicalRatioCellTailLower M n W rho band cut)
    (bankPaperCanonicalRatioCellTailUpper M n W band)





/-! ## Quantitative PNT denominator inside an actual cell -/

/-- Uniform quantitative fixed-ratio prime counting above one cutoff. -/
def TangentFixedRatioPrimeCountLower
    (W : Nat) (rho : Real) : Prop :=
  forall A : Nat, W <= A ->
    ((rho - 1) / 2) * ((A : Real) / Real.log (A : Real)) <=
      (Nat.primeCounting ⌊rho * (A : Real)⌋₊ -
        Nat.primeCounting A : Nat)











/-! ## Finite traffic envelopes before the final mesh sum -/



/-- Literal harmonic envelope for the residual `ell^1` mass. -/
def bankPaperCanonicalHarmonicResidualL1Envelope
    (n W : Nat) (scale : Real) : Real :=
  ∑ p : BankPaperCanonicalTangentPrime n W,
    bankPaperCanonicalHarmonicPointwiseUpper scale p

/-- Uniform Mertens endpoint majorant for the complete harmonic residual
mass on `W < p <= yNat n`. -/
def bankPaperCanonicalHarmonicResidualL1Majorant
    (n W : Nat) (scale : Real) : Real :=
  bankPaperCanonicalHarmonicTailMajorant scale W (yNat n)















/-- The two Mertens tails incident to a vertex's cell. -/
def bankPaperCanonicalRatioCellPortNumeratorEnvelope
    {delta eta : Real} (M : RegularRelativeMesh.Mesh delta eta)
    {n W : Nat} (hdelta : 0 < delta) (hn : 1 < n)
    (hW : W ≠ 0) (S : ScaleSeparation M n W)
    (rho scale : Real) (p : BankPaperCanonicalTangentPrime n W) : Real :=
  (if bankPaperCanonicalRatioCellIndex M hdelta hn hW S rho p = 0 then 0
    else bankPaperCanonicalRatioCellTailMajorant M n W rho scale
      (bankPaperCanonicalExponentBandOf M hdelta hn hW S p)
      (bankPaperCanonicalRatioCellIndex M hdelta hn hW S rho p - 1)) +
    bankPaperCanonicalRatioCellTailMajorant M n W rho scale
      (bankPaperCanonicalExponentBandOf M hdelta hn hW S p)
      (bankPaperCanonicalRatioCellIndex M hdelta hn hW S rho p)







/-- PNT main term used as the analytic lower denominator at a vertex. -/
def bankPaperCanonicalRatioCellPNTDenominator
    {delta eta : Real} (M : RegularRelativeMesh.Mesh delta eta)
    {n W : Nat} (hdelta : 0 < delta) (hn : 1 < n)
    (hW : W ≠ 0) (S : ScaleSeparation M n W)
    (rho : Real) (p : BankPaperCanonicalTangentPrime n W) : Real :=
  let A := tangentMultiplicativeRatioCutoff
    (bankPaperCanonicalExponentBandLower M n W
      (bankPaperCanonicalExponentBandOf M hdelta hn hW S p)) rho
    (bankPaperCanonicalRatioCellIndex M hdelta hn hW S rho p)
  ((rho - 1) / 2) * ((A : Real) / Real.log (A : Real))







end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankPaperCanonicalRatioCellMomentTraffic -/
section


/-!
# Moment collapse of the canonical ratio-cell traffic

The endpoint-by-endpoint Mertens envelope is useful for pointwise ports,
but it is deliberately too wasteful for the sum over all cell cuts: its
uniform error is repeated once at every cut.  For total traffic one first
interchanges the two finite sums.  A vertex in cell `i` occurs in exactly
`i` strict tails, so the complete tail census is the first moment of the
literal cell index.

For the canonical multiplicative cells that index is at most

`(log y / log rho) * (t_p - t_lower)`.

The arithmetic moment bounds already proved for the canonical regular
mesh then give the paper-sized factor `delta + ratio`.  The only loss from
the natural floors is the explicit quantity `log 2 / log y`.

No new asymptotic or distribution hypothesis occurs in this file.
-/

open Filter Topology
open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.ArithmeticBandGeometry
open Erdos390.Full.PrimeBandQuadrature
open Erdos390.Full.RegularRelativeMesh
open Erdos390.Full.RegularMeshPrimeCutoffs

noncomputable section

/-! ## The finite cut/tail interchange -/



/-! ## Logarithmic control of the concrete cell index -/





/-! ## The exact shifted-coordinate moment -/

/-- The canonical arithmetic first moment measured from the actual natural
lower endpoint in each exponent band. -/
def bankPaperCanonicalRatioCellCoordinateMoment
    {delta eta : Real} (M : RegularRelativeMesh.Mesh delta eta)
    {n W : Nat} (hdelta : 0 < delta) (hn : 1 < n)
    (hW : W ≠ 0) (S : ScaleSeparation M n W) : Real :=
  let P := RegularMeshPrimeCutoffs.Mesh.canonicalPartition
    M hdelta hn hW S
  ∑ band : BankPaperCanonicalExponentBand M,
    P.mass band *
      (P.center band -
        RegularMeshPrimeCutoffs.Mesh.cutoffCoordinate M n W band.1)





/-! ## Canonical-mesh bound for the shifted moment -/

/-- The only coordinate loss caused by flooring a positive mesh endpoint. -/
def bankPaperCanonicalRatioCellFloorLoss (n : Nat) : Real :=
  Real.log 2 / Real.log (y n)







/-! ## Moment majorants for the complete traffic ledger -/

/-- Exact arithmetic-moment majorant for the sum of the canonical cut
loads. -/
def bankPaperCanonicalRatioCellMomentCutMajorant
    {delta eta : Real} (M : RegularRelativeMesh.Mesh delta eta)
    (n : Nat) (rho scale : Real) : Real :=
  scale * Real.log (y n) / Real.log rho *
    (2 * delta + 3 * M.ratio *
      (1 + (M.cellCount : Real) *
        bankPaperCanonicalRatioCellFloorLoss n))

/-- Total-traffic majorant obtained by using the global Mertens estimate
only once and the exact arithmetic moment for all cell cuts. -/
def bankPaperCanonicalRatioCellMomentTotalTrafficMajorant
    {delta eta : Real} (M : RegularRelativeMesh.Mesh delta eta)
    (n W : Nat) (rho scale : Real) : Real :=
  bankPaperCanonicalHarmonicResidualL1Majorant n W scale / 2 +
    2 * bankPaperCanonicalRatioCellMomentCutMajorant M n rho scale







/-! ## Paper-scale scalar reduction -/

/-- Fixed main-term traffic constant supplied by the moment collapse. -/
def bankPaperCanonicalRatioCellTrafficConstant (rho : Real) : Real :=
  6 / Real.log rho

/-- Every non-main contribution after the paper specialization
`scale = tangentConstant * N / log y`.  For fixed parameters this is an
explicit scalar tending to zero; no traffic quantity remains in it. -/
def bankPaperCanonicalRatioCellTrafficErrorCoefficient
    {delta eta : Real} (M : RegularRelativeMesh.Mesh delta eta)
    (n W : Nat) (rho tangentConstant : Real) : Real :=
  tangentConstant /
      (2 * Real.log (y n)) *
    (Real.log (Real.log (yNat n : Real)) -
        Real.log (Real.log (W : Real)) +
      5 * fullReciprocalSumUniformConstant /
        Real.log (W : Real) ^ 3) +
    6 * tangentConstant * M.ratio * (M.cellCount : Real) * Real.log 2 /
      (Real.log rho * Real.log (y n))



/-! ## Concrete geometry for the normalized pointwise port -/

/-- The natural start of the merged ratio cell containing `p`. -/
def bankPaperCanonicalRatioCellCurrentLower
    {delta eta : Real} (M : RegularRelativeMesh.Mesh delta eta)
    {n W : Nat} (hdelta : 0 < delta) (hn : 1 < n)
    (hW : W ≠ 0) (S : ScaleSeparation M n W)
    (rho : Real) (p : BankPaperCanonicalTangentPrime n W) : Nat :=
  tangentMultiplicativeRatioCutoff
    (bankPaperCanonicalExponentBandLower M n W
      (bankPaperCanonicalExponentBandOf M hdelta hn hW S p)) rho
    (bankPaperCanonicalRatioCellIndex M hdelta hn hW S rho p)







/-! ## Scalar Mertens cancellation in one PNT-normalized port -/









/-! ## Collapse of the remaining band endpoint gap -/





/-! ## Uniform paper-scale port envelope -/

/-- Scalar port majorant, uniform in the vertex. -/
def bankPaperCanonicalRatioCellUniformPortMajorant
    {delta eta : Real} (M : RegularRelativeMesh.Mesh delta eta)
    (n W : Nat) (rho scale : Real) : Real :=
  (8 * rho ^ 2 / (rho - 1)) * scale *
    ((delta + M.ratio) * Real.log (y n) + Real.log 2 +
      5 * fullReciprocalSumUniformConstant /
        Real.log (W : Real) ^ 2)





/-! ## Paper-scale scalar reduction for the incident ledger -/

/-- Fixed coefficient of one weighted uniform port. -/
def bankPaperCanonicalRatioCellPortConstant (rho : Real) : Real :=
  8 * rho ^ 2 / (rho - 1)

/-- Fixed coefficient after the two ports in the incident ledger. -/
def bankPaperCanonicalRatioCellIncidentConstant (rho : Real) : Real :=
  16 * rho ^ 2 / (rho - 1)

/-- Explicit vanishing coefficient left by the weighted residual and the
two pointwise-port errors at the paper scale. -/
def bankPaperCanonicalRatioCellIncidentErrorCoefficient
    (W n : Nat) (rho tangentConstant : Real) : Real :=
  tangentConstant / Real.log (y n) *
    (1 + 2 * bankPaperCanonicalRatioCellPortConstant rho *
      (Real.log 2 +
        5 * fullReciprocalSumUniformConstant /
          Real.log (W : Real) ^ 2))





/-! ## A manifestly vanishing upper coefficient for total traffic -/

/-- A nonnegative asymptotic upper form for the total-traffic error
coefficient.  It separates `log(log y)/log y` from fixed multiples of
`1/log y`. -/
def bankPaperCanonicalRatioCellTrafficErrorUpperCoefficient
    {delta eta : Real} (M : RegularRelativeMesh.Mesh delta eta)
    (W n : Nat) (rho tangentConstant : Real) : Real :=
  (tangentConstant / 2) *
      (Real.log (Real.log (y n)) / Real.log (y n)) +
    (tangentConstant / 2 *
      (|Real.log (Real.log (W : Real))| +
        5 * fullReciprocalSumUniformConstant /
          Real.log (W : Real) ^ 3)) *
      (1 / Real.log (y n)) +
    (6 * tangentConstant * M.ratio * (M.cellCount : Real) * Real.log 2 /
      Real.log rho) * (1 / Real.log (y n))









/-! ## Explicit fixed choices for the paper budgets -/

/-- The coefficient multiplying the fixed band width in the distributed
paper main budget after inserting the concrete traffic and incident
constants. -/
def bankPaperCanonicalRatioCellMainCoefficient (rho : Real) : Real :=
  16 * bankPaperCanonicalRatioCellTrafficConstant rho +
    8 * bankPaperCanonicalRatioCellIncidentConstant rho



/-- A fixed positive width leaving a factor-two reserve in `hmain`.
It depends only on the already-fixed density, split parameter, cell ratio,
and tangent constant, never on the final asymptotic variable `n`. -/
def bankPaperCanonicalRatioCellPaperWidthChoice
    (density sigma rho tangentConstant : Real) : Real :=
  density ^ 2 * sigma /
    (96 * bankPaperCanonicalRatioCellMainCoefficient rho * tangentConstant)







/-- A symmetric positive allocation for the two error coefficients.  The
weights `16` and `8` then sum to exactly the available `density^2 / 96`
paper error budget. -/
def bankPaperCanonicalRatioCellPaperErrorChoice
    (density sigma : Real) : Real :=
  density ^ 2 * sigma / 2304







end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankPaperCanonicalSectionNineFinalGeometry -/
section


/-!
# Literal Section 9 final geometry

This file joins the last three finite interfaces before the existing
post-tangent continuation:

* the actual Proposition 8.7 endpoint and its guarded slack package;
* the canonical occupied ratio-cell geometry and actual-`q` traffic ledger;
* the finite distributed clean-multiplier supplier on guarded candidates.

The conclusion deliberately stops at a post-tangent output, its exact
distributed update, and the interval/collision geometry required downstream.
It does not repeat the exactification or upper-endpoint terminal.

One collision input remains explicit.  The existing realization API does not
prove that the fixed exceptional factors avoid the full actual component
census.  `BankPaperCanonicalSectionNineFixedComponentCollisionFree` names
exactly that missing finite statement.  It is used only to deduce that the
fixed factors avoid every Boolean exactification state.  Candidate--bank
disjointness, in contrast, follows from the literal five-family numerical
guard and is proved here.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.PaperBridgeFit
open Erdos390.Full.PaperGuardCensus
open Erdos390.Full.PrimeBandQuadrature
open Erdos390.Full.RegularMeshPrimeCutoffs
open Erdos390.Full.RegularRelativeMesh

noncomputable section

namespace BankPaperRealization

/-! ## Exactification states belong to the literal numerical guard -/

/-- State one of an actual path component is the orientation-aware alternate
precharge value of the corresponding global request. -/
@[simp] theorem pathStateOneValue_eq_prechargeAlternateStateValue
    {n M : Nat} (R : BankPaperRealization n M)
    (slot : SignedBankSlot (bankRoundingBetaOnSupport n))
    (component : BankPaperPathComponent slot) :
    R.pathStateOneValue slot component =
      R.prechargeAlternateStateValue
        (bankPaperPathComponentRequest slot component) := by
  cases component <;> rfl



/-! ## The exact final finite geometry -/

/-- The one collision statement not supplied by the guarded-candidate
construction: fixed exceptional factors avoid every actual bank-component
occurrence.  Keeping the global census here permits direct reuse of
`disjoint_exactificationState_of_disjoint_allComponentOccurrences`. -/
def BankPaperCanonicalSectionNineFixedComponentCollisionFree
    {c : Real} {n : Nat}
    (R : BankPaperRealization n
      (upperEndpoint n (upperTailLength c n)))
    (deltaStar : Real) : Prop :=
  Disjoint (R.paperFixedExceptionalFactors deltaStar)
    R.allComponentOccurrences

/-- The seven geometric facts outside
`BankPaperCanonicalPostTangentOutput` for the literal guarded candidates and
fixed exceptional factors.  Tail-charge divisibility is intentionally not a
geometry field and remains an input of the finite assembly theorem below. -/
def BankPaperCanonicalSectionNineFinalGeometry
    {c : Real} {depth n : Nat}
    (R : BankPaperRealization n
      (upperEndpoint n (upperTailLength c n)))
    (certificate : GuardedCentralAnchorCertificate c depth n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (deltaStar : Real) (K : Nat) : Prop :=
  let candidates :=
    R.roughCanonicalGuardedCandidateSet certificate deltaStar K
  let fixed := R.paperFixedExceptionalFactors deltaStar
  candidates ⊆
      factorInterval n (upperEndpoint n (upperTailLength c n)) ∧
    fixed ⊆
      factorInterval n (upperEndpoint n (upperTailLength c n)) ∧
    Disjoint fixed candidates ∧
    (∀ slot selected,
      Disjoint fixed (R.exactificationState slot selected)) ∧
    (∀ slot selected,
      Disjoint candidates (R.exactificationState slot selected)) ∧
    Disjoint certificate.anchors fixed ∧
    Disjoint certificate.anchors candidates



/-! ## Reusable finite flow and output package -/

/-- The literal canonical ratio-cell earthmover used by the final connector.
Naming it once keeps the clean-list premise and the final payload
definitionally synchronized. -/
def bankPaperCanonicalSectionNineRatioCellFlow
    {delta eta : Real} (M : RegularRelativeMesh.Mesh delta eta)
    {c : Real} {depth n W : Nat}
    (R : BankPaperRealization n
      (upperEndpoint n (upperTailLength c n)))
    (certificate : GuardedCentralAnchorCertificate c depth n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (deltaStar : Real) (K : Nat)
    (hdelta : 0 < delta) (hn : 1 < n) (hW : W ≠ 0)
    (S : ScaleSeparation M n W) (rho : Real)
    (selector : Nat → Real) :
    BankPaperCanonicalTangentPrime n W →
      BankPaperCanonicalTangentPrime n W → Real :=
  tangentRatioCellEarthmoverFlow
    (bankPaperCanonicalLastRatioCell M (n := n) (W := W) rho)
    (bankPaperCanonicalTangentResidual (W := W) R certificate
      (R.paperFixedExceptionalFactors deltaStar)
      (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
      selector)
    (bankPaperCanonicalExponentBandOf M hdelta hn hW S)
    (bankPaperCanonicalRatioCellIndex M hdelta hn hW S rho)

/-- Strong finite output of the connector: a clean multiplier family,
endpoint collision-freedom, exact flow and factorization boundaries, the
literal updated selector, tail-charge divisibility, and all final geometry. -/
def BankPaperCanonicalSectionNineFinalPayload
    {c : Real} {depth n W K : Nat}
    (R : BankPaperRealization n
      (upperEndpoint n (upperTailLength c n)))
    (certificate : GuardedCentralAnchorCertificate c depth n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (deltaStar : Real) (selector : Nat → Real)
    (flow : BankPaperCanonicalTangentPrime n W →
      BankPaperCanonicalTangentPrime n W → Real)
    (L sigma : Real) : Prop :=
  ∃ multiplier :
      BankPaperCanonicalDistributedTangentSplitRequest flow L sigma → Nat,
    (∀ request,
      multiplier request ∈
        tangentSplitCleanMultiplierLists
          (tangentPositiveFlowEdges flow)
          (tangentStarEdgeSource bankPaperCanonicalTangentPrimeLabel)
          (tangentStarEdgeTarget bankPaperCanonicalTangentPrimeLabel)
          L sigma
          (fun edge : BankPaperCanonicalTangentPrime n W ×
              BankPaperCanonicalTangentPrime n W =>
            flow edge.1 edge.2)
          n K (upperTailLength c n) (roughHeadModulus W)
          (tangentPaperExceptionalCutoff deltaStar n) (yNat n)
          R.tangentPaperDedicatedRows
          (R.tangentPaperNumericalGuardSet certificate
            (R.paperFixedExceptionalFactors deltaStar)) request) ∧
    TangentEndpointsDistinct
        (tangentSplitRequests
          (tangentPositiveFlowEdges flow) L sigma
          (fun edge : BankPaperCanonicalTangentPrime n W ×
              BankPaperCanonicalTangentPrime n W =>
            flow edge.1 edge.2))
        bankPaperCanonicalDistributedTangentRequestSource
        bankPaperCanonicalDistributedTangentRequestTarget multiplier ∧
    (∀ p : BankPaperCanonicalTangentPrime n W,
      tangentFlowDivergence flow p =
        bankPaperCanonicalTangentResidual R certificate
          (R.paperFixedExceptionalFactors deltaStar)
          (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
          selector p) ∧
    (∀ q : Nat,
      (∑ request : BankPaperCanonicalDistributedTangentSplitRequest
            flow L sigma,
          tangentSplitRequestWeight request *
            (((bankPaperCanonicalDistributedTangentRequestSource
                  request).factorization q : Real) -
              ((bankPaperCanonicalDistributedTangentRequestTarget
                  request).factorization q : Real))) =
        bankPaperCanonicalSelectorValuationDeficit R certificate
          (R.paperFixedExceptionalFactors deltaStar)
          (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
          selector q) ∧
    ∃ output : BankPaperCanonicalPostTangentOutput R certificate
        (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
        (R.paperFixedExceptionalFactors deltaStar),
      (output.selector =
          bankPaperCanonicalDistributedTangentUpdatedSelector
            flow L sigma multiplier selector) ∧
        (R.selectorTailCharge
              (R.paperFixedExceptionalFactors deltaStar) ∣
            certificate.prechargedTailTarget) ∧
        R.BankPaperCanonicalSectionNineFinalGeometry
          certificate deltaStar K

/-! ## Actual Post-Hfit/P87 finite composition -/



end BankPaperRealization

end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankPaperCombinedChargeDepthFirstTerminal -/
section


/-!
# Depth-first combined charge terminal

The original combined-charge terminal specializes `deltaStar` before it
exposes the capacity depth.  For the Section 9 clean-list application this
creates an artificial cycle: the clean-list width `W` must dominate the
chosen depth, while the tangent-compatible `deltaStar` is defined using
`W`.

The strengthened precharge-capacity theorem actually chooses its depth
using only `c`.  This file preserves that proof order.  It first fixes one
capacity depth and then proves the complete combined-charge conclusion
uniformly for every admissible `deltaStar`.  The tangent-choice corollary
therefore allows `W` and `r0` to be chosen after the depth is known.

The payload also retains the base exactification-bank divisibility fact
needed by `BankPaperCanonicalPostTangentContinuationAtDepth`; the older
combined-charge terminal discarded this already-proved capacity fact.
-/

open Filter Topology

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel
open Erdos390.Full.Scale

noncomputable section

/-! ## Fixed-depth payload -/

/-- The complete combined fixed-factor and precharge output at one already
chosen capacity depth.

Besides the existing combined-charge conclusions, this interface retains
the base exactification-bank divisibility required by the downstream
capacity continuation. -/
def BankPaperCombinedChargeTerminalAtDepth
    (c deltaStar : ℝ) (depth : ℕ) : Prop :=
  ∀ᶠ n : ℕ in atTop,
    ∃ bank : BankPaperRealization n
        (upperEndpoint n (upperTailLength c n)),
      ∃ certificate : GuardedCentralAnchorCertificate c depth n
          bank.anchorGuardLeftCore bank.anchorGuardRightCore
          (bank.centralChangedMarkers depth),
        centralAnchorDivisor n (centralAnchorCutoff depth n)
              certificate.q * bank.prechargeBaseStateProduct ∣
            centralTailProduct n (upperTailLength c n) ∧
          (baseBankFactors bank.exactificationState).prod id ∣
            certificate.prechargedTailTarget ∧
          bank.selectorTailCharge
                (bank.paperFixedExceptionalFactors deltaStar) ∣
            certificate.prechargedTailTarget ∧
          (∀ p ∈ primesUpTo (2 * depth + 1),
            (c - C0) / (24 * (((p - 1 : ℕ) : ℝ))) *
                  secondOrderScale n +
                (bank.selectorTailCharge
                  (bank.paperFixedExceptionalFactors deltaStar)).factorization p ≤
              certificate.prechargedTailTarget.factorization p) ∧
          certificate.selectorTailTarget bank
                (bank.paperFixedExceptionalFactors deltaStar) *
              bank.selectorTailCharge
                (bank.paperFixedExceptionalFactors deltaStar) =
            certificate.prechargedTailTarget ∧
          certificate.prechargedTailTarget *
              centralAnchorDivisor n (centralAnchorCutoff depth n)
                certificate.q =
            centralTailProduct n (upperTailLength c n)

/-! ## Uniform admissible exponent after capacity -/



/-! ## Tangent-compatible exponent after capacity -/



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



end BankPaperRealization

/-! ## Synchronized fixed-depth terminal -/

/-- One eventual capacity witness and one complete finite distributed
Section 9 payload, synchronized at the same `n`, bank, guarded anchor
certificate, and capacity depth.

The existential parameters `W`, `K`, `selector`, `flow`, `L`, and `sigma`
remain visible because they are genuine finite construction data. -/
def BankPaperCanonicalDistributedSectionNineTerminalAtDepth
    (c deltaStar : ℝ) (depth : ℕ) : Prop :=
  ∀ᶠ n : ℕ in atTop,
    ∃ R : BankPaperRealization n
        (upperEndpoint n (upperTailLength c n)),
      ∃ certificate : GuardedCentralAnchorCertificate c depth n
          R.anchorGuardLeftCore R.anchorGuardRightCore
          (R.centralChangedMarkers depth),
        centralAnchorDivisor n (centralAnchorCutoff depth n)
              certificate.q * R.prechargeBaseStateProduct ∣
            centralTailProduct n (upperTailLength c n) ∧
          (baseBankFactors R.exactificationState).prod id ∣
            certificate.prechargedTailTarget ∧
          certificate.prechargedTailTarget *
                centralAnchorDivisor n (centralAnchorCutoff depth n)
                  certificate.q =
              centralTailProduct n (upperTailLength c n) ∧
          ∃ W K : ℕ,
            ∃ selector : ℕ → ℝ,
              ∃ flow : BankPaperCanonicalTangentPrime n W →
                  BankPaperCanonicalTangentPrime n W → ℝ,
                ∃ L sigma : ℝ,
                  R.BankPaperCanonicalSectionNineFinalPayload (K := K)
                    certificate deltaStar selector flow L sigma





/-! ## Same-depth upper endpoint -/



/-! ## Depth-first main terminal -/







end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankPaperCanonicalSectionNineBudgetClosure -/
section


/-!
# Canonical Section 9 budget closure

This connector discharges the three literal clean-list hypotheses and the
three scalar paper budgets left visible by the final Section 9 geometry
theorem.  It also turns one narrow upper estimate for the actual
Proposition 8.7 mass,

`q_n <= Cq * secondOrderScale n`,

into the exact paper-scale domination used by that theorem.

The clean density is the canonical
`tangentPaperCleanListDensity W r0`.  The main budget is finite once the
mesh width is below its explicit choice; the error and ceiling budgets are
eventual consequences of the canonical ratio-cell estimates.  The only new
analytic input is the displayed upper estimate for `q_n`, together with its
fixed scalar coefficient comparison.

The existing parameter-synchronization theorem supplies the fixed
`depth`, `W`, and `r0` facts consumed by the closure; a projection below
records this interface explicitly.  For the clean triplet we use its
distributed clean-list adapter.  That adapter reindexes the same absorbed
clean-list terminal to the literal ratio-cell earthmover, whereas the older
star-flow Section 9 absorbed wrapper has the wrong flow type here.

The Post-Hfit nonsmooth slack package is deliberately not repeated here.
It is an independent finite premise of the final geometry connector, while
the estimates below depend only on clean-list absorption, canonical cell
geometry, and scalar asymptotics.
-/

open Filter
open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.PaperBridgeFit
open Erdos390.Full.RegularMeshPrimeCutoffs
open Erdos390.Full.RegularRelativeMesh

noncomputable section

/-! ## Synchronized core parameters -/



/-! ## Exact logarithmic and actual-mass reductions -/





/-! ## The exact downstream package -/

/-- The literal clean-list, budget, and scale hypotheses consumed by
`bankPaperCanonicalSectionNineFinalPayload_of_roundedSelector_guardedSlack`.

The first two fields record synchronization of the actual bridge sample
with the ambient canonical index and width.  After rewriting by those
equalities, every remaining field has exactly the type of the corresponding
premise in the final geometry theorem: three clean-list fields, three paper
budgets, the actual-scale domination, and the logarithmic scale identity,
with
`N = secondOrderScale n` and
`density = tangentPaperCleanListDensity W r0`. -/
def BankPaperCanonicalSectionNineBudgetClosure
    {delta eta : Real} (M : RegularRelativeMesh.Mesh delta eta)
    {Head : Type*} [Fintype Head] [DecidableEq Head]
    (B : BridgeData Head (BankPaperCanonicalExponentBand M))
    {c : Real} {depth n W K0 : Nat}
    (R : BankPaperRealization n
      (upperEndpoint n (upperTailLength c n)))
    (certificate : GuardedCentralAnchorCertificate c depth n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (deltaStar sigma : Real)
    (hdelta : 0 < delta) (hn : 1 < n) (hW : W ≠ 0)
    (S : ScaleSeparation M n W)
    (r0 rho tangentConstant Cpost : Real)
    (endpoint : Nat -> Real) : Prop :=
  B.sampleData.n = n ∧
  B.sampleData.W = W ∧
  let density := tangentPaperCleanListDensity W r0
  let flow :=
    R.bankPaperCanonicalSectionNineRatioCellFlow
      M certificate deltaStar (K0 + 1) hdelta hn hW S rho endpoint
  (∀ request :
      BankPaperCanonicalDistributedTangentSplitRequest flow B.L sigma,
    0 < bankPaperCanonicalDistributedTangentLowerCard
      (density := density) request) ∧
  (∀ request :
      BankPaperCanonicalDistributedTangentSplitRequest flow B.L sigma,
    bankPaperCanonicalDistributedTangentLowerCard
        (density := density) request <=
      (tangentSplitCleanMultiplierLists
        (tangentPositiveFlowEdges flow)
        (tangentStarEdgeSource bankPaperCanonicalTangentPrimeLabel)
        (tangentStarEdgeTarget bankPaperCanonicalTangentPrimeLabel)
        B.L sigma
        (fun edge : BankPaperCanonicalTangentPrime n W ×
            BankPaperCanonicalTangentPrime n W =>
          flow edge.1 edge.2)
        n (K0 + 1) (upperTailLength c n) (roughHeadModulus W)
        (tangentPaperExceptionalCutoff deltaStar n) (yNat n)
        R.tangentPaperDedicatedRows
        (R.tangentPaperNumericalGuardSet certificate
          (R.paperFixedExceptionalFactors deltaStar)) request).card) ∧
  (∀ request :
      BankPaperCanonicalDistributedTangentSplitRequest flow B.L sigma,
    ∀ side,
      density * n <=
        (bankPaperCanonicalDistributedTangentLowerCard
          (density := density) request : Real) *
          tangentEndpointLabel
            bankPaperCanonicalDistributedTangentRequestSource
            bankPaperCanonicalDistributedTangentRequestTarget
            side request) ∧
  tangentDistributedPaperMainBudget
      (bankPaperCanonicalRatioCellTrafficConstant rho)
      (bankPaperCanonicalRatioCellIncidentConstant rho)
      tangentConstant (delta + M.ratio) sigma <= density ^ 2 / 48 ∧
  tangentDistributedPaperErrorBudget
      (bankPaperCanonicalRatioCellTrafficErrorCoefficient
        M n W rho tangentConstant)
      (bankPaperCanonicalRatioCellIncidentErrorCoefficient
        W n rho tangentConstant)
      sigma <= density ^ 2 / 96 ∧
  tangentDistributedPaperCeilingBudget n (yNat n)
      (tangentDistributedSupportCount
        (BankPaperCanonicalTangentPrime n W)) <= density ^ 2 / 96 ∧
  Cpost * B.q / B.L <=
      tangentConstant * secondOrderScale n / Real.log (y n) ∧
  B.L * secondOrderScale n = (n : Real)

/-! ## Eventual closure -/



end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankPaperCanonicalSectionNineFixedComponentCollision -/
section


/-!
# Fixed exceptional factors avoid the actual component census

The fixed exceptional factors lie in the strict upper tail and are defined
by removing every realized donor.  Thus an intersection with the actual bank
census can only come from a bottom-component state which itself lies above
`2n`.  Ordinary states are always at most `2n`, and every ordinary or bottom
donor belongs to `prechargeDonorSet`.

This file records that exact finite reduction.  It then closes the reduction
under the paper's standard narrow-endpoint inequality

`5 * M ≤ 12 * n`.

For the literal endpoint `M = upperEndpoint n (upperTailLength c n)`, that
inequality holds eventually when `0 < c`.  Consequently the collision premise
left explicit in `BankPaperCanonicalSectionNineFinalGeometry` is an eventual
theorem, uniformly in the realization and in `deltaStar`.
-/

open Filter Topology

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel

noncomputable section

namespace BankPaperRealization

/-- The only state values which can possibly meet the fixed exceptional set.

All bottom lower states are listed.  An upper state is listed only when it is
not already the component's donor, since donors are removed in the literal
definition of `paperFixedExceptionalFactors`. -/
def BankPaperCanonicalSectionNineBottomStateCollisionExclusions
    {c : Real} {n : Nat}
    (R : BankPaperRealization n
      (upperEndpoint n (upperTailLength c n)))
    (deltaStar : Real) : Prop :=
  ∀ request : ↑(bankBottomRelevantPaperRequests n),
    let fullRequest :=
      bankBottomRelevantRequestToPaperRequest request
    R.bottom.lowerStateFactor fullRequest ∉
        R.paperFixedExceptionalFactors deltaStar ∧
      (R.bottom.upperStateFactor fullRequest ≠
          R.bottom.donorFactor fullRequest →
        R.bottom.upperStateFactor fullRequest ∉
          R.paperFixedExceptionalFactors deltaStar)













end BankPaperRealization



end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankPaperCanonicalSectionNineTopFrozenEventStepConnector -/
section


/-!
# Public Section 9 event step for the frozen-top Post-Hfit source

The older synchronized event step was private and its input hard-coded the
legacy no-top Post-Hfit package.  This connector exposes the same finite
terminal event shape for the verified nearest-integer frozen-top source.

At one index the only source-specific input is
`BankPaperCanonicalTopFrozenRoundedPostHfitGuardedSlackPackage`.  The event
step combines it with the already existing budget, moment-readiness,
fixed-component collision, and rough-depth hypotheses, then calls
`bankPaperCanonicalSectionNineFinalPayload_of_topFrozenRoundedPostHfit`.

An eventual wrapper reuses the repository's automatic suppliers for those
four source-independent inputs and packages the result directly as
`BankPaperCanonicalDistributedSectionNineTerminalAtDepth`.  No new
family-level Post-Hfit supplier is postulated here.
-/

open Filter

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.PaperBridgeFit
open Erdos390.Full.PaperGuardCensus
open Erdos390.Full.PrimeBandQuadrature
open Erdos390.Full.RegularMeshPrimeCutoffs
open Erdos390.Full.RegularRelativeMesh

noncomputable section

/-! ## Frozen-top synchronized input -/

/-- One finite capacity witness augmented by a frozen-top rounded Post-Hfit
package for the same bank, certificate, and canonical mesh partition.

This proposition contains no Section 9 budget closure, collision conclusion,
clean multiplier construction, final geometry, or final payload. -/
def BankPaperCanonicalSectionNineTopFrozenSynchronizedPostHfitInputAt
    {delta eta : Real} (M : RegularRelativeMesh.Mesh delta eta)
    {P : Finset Nat}
    (B : BridgeData (PaperHeadSimplex.Tag P)
      (BankPaperCanonicalExponentBand M))
    (c : Real) (depth K0 : Nat)
    (deltaStar rho sigma Cpost : Real)
    (hdelta : 0 < delta) : Prop :=
  ∃ R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)),
    ∃ certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
        R.anchorGuardLeftCore R.anchorGuardRightCore
        (R.centralChangedMarkers depth),
      centralAnchorDivisor B.sampleData.n
            (centralAnchorCutoff depth B.sampleData.n)
            certificate.q * R.prechargeBaseStateProduct ∣
          centralTailProduct B.sampleData.n
            (upperTailLength c B.sampleData.n) ∧
        (baseBankFactors R.exactificationState).prod id ∣
          certificate.prechargedTailTarget ∧
        R.selectorTailCharge
              (R.paperFixedExceptionalFactors deltaStar) ∣
          certificate.prechargedTailTarget ∧
        certificate.prechargedTailTarget *
              centralAnchorDivisor B.sampleData.n
                (centralAnchorCutoff depth B.sampleData.n)
                certificate.q =
            centralTailProduct B.sampleData.n
              (upperTailLength c B.sampleData.n) ∧
        ∃ hW : B.sampleData.W ≠ 0,
          ∃ S : ScaleSeparation M B.sampleData.n B.sampleData.W,
            B.partition =
                RegularMeshPrimeCutoffs.Mesh.canonicalPartition
                  M hdelta B.n_gt_one hW S ∧
              ∃ Tsource : BarycentricTarget B.sampleData,
                ∃ betaProt alpha beta qTilde : Real,
                  ∃ placementSeed activeSeed :
                      B.sampleData.Sample → Real,
                    ∃ radius : NNReal,
                      ∃ quota : Int,
                        ∃ path : Real → B.ParamSpace,
                          ∃ endpoint : Nat → Real,
                            BankPaperRealization.BankPaperCanonicalTopFrozenRoundedPostHfitGuardedSlackPackage
                              (K := K0 + 1) B R certificate
                              (R.paperFixedExceptionalFactors deltaStar)
                              Tsource deltaStar betaProt alpha beta
                              qTilde sigma placementSeed activeSeed
                              radius Cpost
                              (bankPaperCanonicalRatioCellIndex
                                M hdelta B.n_gt_one hW S rho)
                              quota path endpoint

/-- Eventual form of the synchronized frozen-top input.  The bridge family
is fixed before the asymptotic index. -/
def BankPaperCanonicalSectionNineTopFrozenSynchronizedPostHfitInput
    {delta eta : Real} (M : RegularRelativeMesh.Mesh delta eta)
    {P : Finset Nat}
    (B : Nat → BridgeData (PaperHeadSimplex.Tag P)
      (BankPaperCanonicalExponentBand M))
    (c : Real) (depth K0 : Nat)
    (deltaStar rho sigma Cpost : Real)
    (hdelta : 0 < delta) : Prop :=
  ∀ᶠ n : Nat in atTop,
    BankPaperCanonicalSectionNineTopFrozenSynchronizedPostHfitInputAt
      M (B n) c depth K0 deltaStar rho sigma Cpost hdelta

/-! ## Public one-index assembly -/



/-! ## Eventual direct terminal packaging -/



end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankPaperCanonicalSectionNinePostHeightLocalInputConnector -/
section


/-!
# Paper-faithful finite inputs after the Section 8 height choice

The legacy symmetric-height input fixes a bridge whose baseline has mass
`q0`.  After the integer height `d` is chosen, the paper instead installs a
fresh barycentric target of mass

`qn = q0 - d`.

This file keeps those two stages separate.  A scaffold bridge contributes
only the structured sample needed to define the rounded frozen-top source.
The certificate-dependent logarithmic target is the literal
`log certificate.prechargedTailTarget`; its rounded frozen ledger determines
`A0`.  From the resulting post-height target `Tpost` we construct a new
active-mass bridge `Bpost`, whose baseline is definitionally the scaled
post-height seed and whose partition is the canonical mesh partition.

The source and dependent structures below are finite input packages, not
new analytic assertions.  The source package is discharged by the existing
post-height source-prebridge theorem.  The dependent package lists exactly
the remaining hypotheses consumed by the audited arbitrary-source Post-hfit
producer.  The final adapter packages the result as the public top-frozen
synchronized input for this same `Bpost`, realization, and certificate.
-/

open Set
set_option backward.isDefEq.respectTransparency false

open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.PaperBridgeFit
open Erdos390.Full.PaperGuardCensus
open Erdos390.Full.PaperHeadSimplex
open Erdos390.Full.RegularMeshPrimeCutoffs
open Erdos390.Full.RegularRelativeMesh

noncomputable section

namespace BankPaperRealization

/-! ## Certificate-dependent post-height scalars -/

/-- The finite-fiber form of the paper's precharged logarithmic target. -/
def bankPaperCanonicalSectionNinePostHeightLogY
    {P : Finset Nat} {Band : Type*}
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData (PaperHeadSimplex.Tag P) Band)
    {c : Real} {depth : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth)) : Real :=
  Real.log (certificate.prechargedTailTarget : Real)

/-- The nearest-integer active mass before the height displacement. -/
def bankPaperCanonicalSectionNinePostHeightRoundedQ0
    {P : Finset Nat} {Band : Type*}
    [Fintype Band] [DecidableEq Band]
    (K : Nat)
    (B : BridgeData (PaperHeadSimplex.Tag P) Band)
    {c : Real} {depth : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (deltaStar betaProt alpha qTilde : Real) : Real :=
  bankPaperCanonicalTopFrozenRoundedActiveMass (K := K)
    B R certificate deltaStar betaProt alpha qTilde

/-- The complete frozen logarithmic mass of the rounded source, including
the fixed exceptional factors and the state-zero bank. -/
def bankPaperCanonicalSectionNinePostHeightRoundedLambda0
    {P : Finset Nat} {Band : Type*}
    [Fintype Band] [DecidableEq Band]
    (K : Nat)
    (B : BridgeData (PaperHeadSimplex.Tag P) Band)
    {c : Real} {depth : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (Tsource : BarycentricTarget B.sampleData)
    (deltaStar betaProt alpha beta qTilde : Real) : Real :=
  bankPaperCanonicalActualFrozenLogMass B.sampleData
    (R.paperFixedExceptionalFactors deltaStar)
    (baseBankFactors R.exactificationState)
    (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
    (bankPaperCanonicalTopFrozenRoundedSourceSelector (K := K)
      B R certificate Tsource deltaStar betaProt alpha beta qTilde)
    (bankPaperCanonicalTopFrozenRoundedActiveSeed (K := K)
      B R certificate Tsource deltaStar betaProt alpha qTilde)

/-- The paper's initial post-height physical logarithmic mass:
`A0 = logY - Lambda0 - q0 L`. -/
def bankPaperCanonicalSectionNinePostHeightA0
    {P : Finset Nat} {Band : Type*}
    [Fintype Band] [DecidableEq Band]
    (K : Nat)
    (B : BridgeData (PaperHeadSimplex.Tag P) Band)
    {c : Real} {depth : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (Tsource : BarycentricTarget B.sampleData)
    (deltaStar betaProt alpha beta qTilde : Real) : Real :=
  bankPaperCanonicalSectionNinePostHeightLogY B R certificate -
    bankPaperCanonicalSectionNinePostHeightRoundedLambda0
      K B R certificate Tsource deltaStar betaProt alpha beta qTilde -
    bankPaperCanonicalSectionNinePostHeightRoundedQ0
      K B R certificate deltaStar betaProt alpha qTilde * B.L

/-- The active head target left by the same quotient charge. -/
def bankPaperCanonicalSectionNinePostHeightActiveHeadTarget
    {P : Finset Nat} {Band : Type*}
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData (PaperHeadSimplex.Tag P) Band)
    {c : Real} {depth : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (deltaStar : Real) :
    {p : Nat // p ∈ P} → Real :=
  fun p =>
    ((certificate.selectorTailTarget R
      (R.paperFixedExceptionalFactors deltaStar)).factorization p.1 : Real)

/-! ## The fresh post-height bridge -/

/-- Data needed before the fresh bridge can be installed.

`Bsource` is only a scaffold carrying the structured sample.  No equality
between its baseline mass and either `q0` or `qn` is requested.  The target
inputs already use the certificate-derived `A0`, so a single realization
and certificate control the source, charge, target, and final bridge. -/
structure BankPaperCanonicalSectionNinePostHeightBridgeInputsAt
    {delta eta : Real} (M : RegularRelativeMesh.Mesh delta eta)
    {P : Finset Nat}
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
    (deltaStar : Real)
    (hdelta : 0 < delta) where
  Tsource : BarycentricTarget Bsource.sampleData
  betaProt : Real
  betaAct : Real
  qTilde : Real
  d : Int
  exponent : Nat
  hW : Bsource.sampleData.W ≠ 0
  scaleSeparation :
    ScaleSeparation M Bsource.sampleData.n Bsource.sampleData.W
  hlo : ∀ sign, Bsource.sampleData.lo sign =
    physicalBound (I.lower sign) Bsource.sampleData.n
  hhi : ∀ sign, Bsource.sampleData.hi sign =
    physicalBound (I.upper sign) Bsource.sampleData.n
  targetInputs :
    BankPaperCanonicalSectionNinePostHeightBaselineTargetInputs
      Bsource I
      (bankPaperCanonicalSectionNinePostHeightRoundedQ0
        (K0 + 1) Bsource R certificate deltaStar betaProt
          (bankPaperCanonicalPostHfitBalancedAlpha
            Bsource c K0 betaProt betaAct)
          qTilde)
      (bankPaperCanonicalSectionNinePostHeightA0
        (K0 + 1) Bsource R certificate Tsource deltaStar
          betaProt
          (bankPaperCanonicalPostHfitBalancedAlpha
            Bsource c K0 betaProt betaAct)
          (betaProt + betaAct) qTilde)
      d exponent
      (bankPaperCanonicalSectionNinePostHeightActiveHeadTarget
        Bsource R certificate deltaStar)

namespace BankPaperCanonicalSectionNinePostHeightBridgeInputsAt

variable
    {delta eta : Real} {M : RegularRelativeMesh.Mesh delta eta}
    {P : Finset Nat}
    {Bsource : BridgeData (PaperHeadSimplex.Tag P)
      (BankPaperCanonicalExponentBand M)}
    {c : Real} {depth K0 : Nat}
    {R : BankPaperRealization Bsource.sampleData.n
      (upperEndpoint Bsource.sampleData.n
        (upperTailLength c Bsource.sampleData.n))}
    {certificate : GuardedCentralAnchorCertificate c depth
      Bsource.sampleData.n R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth)}
    {I : PhysicalIntervals} {deltaStar : Real} {hdelta : 0 < delta}

/-- The balanced smooth-row center used by the actual Post-hfit source. -/
def alpha
    (J : BankPaperCanonicalSectionNinePostHeightBridgeInputsAt
      (K0 := K0) M Bsource R certificate I deltaStar hdelta) : Real :=
  bankPaperCanonicalPostHfitBalancedAlpha
    Bsource c K0 J.betaProt J.betaAct

/-- The total raw-row correction parameter `betaProt + betaAct`. -/
def beta
    (J : BankPaperCanonicalSectionNinePostHeightBridgeInputsAt
      (K0 := K0) M Bsource R certificate I deltaStar hdelta) : Real :=
  J.betaProt + J.betaAct

/-- The rounded source mass `q0` attached to the bridge inputs. -/
def q0
    (J : BankPaperCanonicalSectionNinePostHeightBridgeInputsAt
      (K0 := K0) M Bsource R certificate I deltaStar hdelta) : Real :=
  bankPaperCanonicalSectionNinePostHeightRoundedQ0
    (K0 + 1) Bsource R certificate deltaStar
      J.betaProt J.alpha J.qTilde

/-- The rounded-source frozen logarithmic mass `Lambda0`. -/
def Lambda0
    (J : BankPaperCanonicalSectionNinePostHeightBridgeInputsAt
      (K0 := K0) M Bsource R certificate I deltaStar hdelta) : Real :=
  bankPaperCanonicalSectionNinePostHeightRoundedLambda0
    (K0 + 1) Bsource R certificate J.Tsource deltaStar
      J.betaProt J.alpha J.beta J.qTilde

/-- The certificate-dependent initial physical height `A0`. -/
def A0
    (J : BankPaperCanonicalSectionNinePostHeightBridgeInputsAt
      (K0 := K0) M Bsource R certificate I deltaStar hdelta) : Real :=
  bankPaperCanonicalSectionNinePostHeightA0
    (K0 + 1) Bsource R certificate J.Tsource deltaStar
      J.betaProt J.alpha J.beta J.qTilde

/-- The active head target attached to the quotient charge. -/
def activeHeadTarget
    (J : BankPaperCanonicalSectionNinePostHeightBridgeInputsAt
      (K0 := K0) M Bsource R certificate I deltaStar hdelta) :
    {p : Nat // p ∈ P} → Real :=
  (fun _ =>
    bankPaperCanonicalSectionNinePostHeightActiveHeadTarget
      Bsource R certificate deltaStar) J

/-- The paper's post-height active mass `qn = q0 - d`. -/
def qn
    (J : BankPaperCanonicalSectionNinePostHeightBridgeInputsAt
      (K0 := K0) M Bsource R certificate I deltaStar hdelta) : Real :=
  bankPaperCanonicalSectionNinePostHeightActiveMass J.q0 J.d

/-- The barycentric target constructed before installing the new bridge. -/
def scaffoldTarget
    (J : BankPaperCanonicalSectionNinePostHeightBridgeInputsAt
      (K0 := K0) M Bsource R certificate I deltaStar hdelta) :
    BarycentricTarget Bsource.sampleData :=
  bankPaperCanonicalSectionNinePostHeightTarget
    Bsource I J.hlo J.hhi J.targetInputs

/-- Positivity of the displayed mesh width follows from the mesh axioms. -/
theorem meshWidth_pos
    (J : BankPaperCanonicalSectionNinePostHeightBridgeInputsAt
      (K0 := K0) M Bsource R certificate I deltaStar hdelta) :
    0 < delta + eta := by
  have _hJ : J = J := rfl
  have heta : 0 < eta := M.ratio_pos.trans_le M.ratio_le_eta
  linarith

/-- The fresh bridge with baseline mass exactly `qn` and the canonical
partition selected by the same mesh witness. -/
def postHeightBridge
    (J : BankPaperCanonicalSectionNinePostHeightBridgeInputsAt
      (K0 := K0) M Bsource R certificate I deltaStar hdelta) :
    BridgeData (PaperHeadSimplex.Tag P)
      (BankPaperCanonicalExponentBand M) :=
  bankPaperCanonicalActiveMassBridgeData
    Bsource.sampleData J.scaffoldTarget J.qn
      J.targetInputs.activeMass_pos M hdelta Bsource.n_gt_one
      J.hW J.scaleSeparation none J.meshWidth_pos

@[simp] theorem postHeightBridge_sampleData
    (J : BankPaperCanonicalSectionNinePostHeightBridgeInputsAt
      (K0 := K0) M Bsource R certificate I deltaStar hdelta) :
    J.postHeightBridge.sampleData = Bsource.sampleData :=
  rfl

@[simp] theorem postHeightBridge_partition
    (J : BankPaperCanonicalSectionNinePostHeightBridgeInputsAt
      (K0 := K0) M Bsource R certificate I deltaStar hdelta) :
    J.postHeightBridge.partition =
      RegularMeshPrimeCutoffs.Mesh.canonicalPartition
        M hdelta J.postHeightBridge.n_gt_one J.hW J.scaleSeparation :=
  rfl

@[simp] theorem postHeightBridge_q
    (J : BankPaperCanonicalSectionNinePostHeightBridgeInputsAt
      (K0 := K0) M Bsource R certificate I deltaStar hdelta) :
    J.postHeightBridge.q = J.qn := by
  exact
    bankPaperCanonicalActiveMassBridgeData_q
      Bsource.sampleData J.scaffoldTarget J.qn
        J.targetInputs.activeMass_pos M hdelta Bsource.n_gt_one
        J.hW J.scaleSeparation none J.meshWidth_pos

/-- The physical interval lower endpoints transported to `Bpost`. -/
def postHeightHlo
    (J : BankPaperCanonicalSectionNinePostHeightBridgeInputsAt
      (K0 := K0) M Bsource R certificate I deltaStar hdelta) :
    ∀ sign, J.postHeightBridge.sampleData.lo sign =
      physicalBound (I.lower sign) J.postHeightBridge.sampleData.n :=
  J.hlo

/-- The physical interval upper endpoints transported to `Bpost`. -/
def postHeightHhi
    (J : BankPaperCanonicalSectionNinePostHeightBridgeInputsAt
      (K0 := K0) M Bsource R certificate I deltaStar hdelta) :
    ∀ sign, J.postHeightBridge.sampleData.hi sign =
      physicalBound (I.upper sign) J.postHeightBridge.sampleData.n :=
  J.hhi

/-- The same numerical post-height target inputs, now indexed by `Bpost`.
Only the bridge's structured sample and logarithmic scale occur in these
fields, and both are unchanged by the active-mass constructor. -/
def postHeightTargetInputs
    (J : BankPaperCanonicalSectionNinePostHeightBridgeInputsAt
      (K0 := K0) M Bsource R certificate I deltaStar hdelta) :
    BankPaperCanonicalSectionNinePostHeightBaselineTargetInputs
      J.postHeightBridge I J.q0 J.A0 J.d J.exponent
        J.activeHeadTarget where
  exponent_pos := J.targetInputs.exponent_pos
  activeMass_pos := J.targetInputs.activeMass_pos
  headMargin := J.targetInputs.headMargin
  headMargin_pos := J.targetInputs.headMargin_pos
  vertex_margin := J.targetInputs.vertex_margin
  zero_margin := J.targetInputs.zero_margin
  physicalEta := J.targetInputs.physicalEta
  physicalEta_pos := J.targetInputs.physicalEta_pos
  minus_below := J.targetInputs.minus_below
  plus_above := J.targetInputs.plus_above

/-- The literal `Tpost` viewed on the fresh bridge. -/
def postHeightTarget
    (J : BankPaperCanonicalSectionNinePostHeightBridgeInputsAt
      (K0 := K0) M Bsource R certificate I deltaStar hdelta) :
    BarycentricTarget J.postHeightBridge.sampleData :=
  bankPaperCanonicalSectionNinePostHeightTarget J.postHeightBridge I
    J.postHeightHlo J.postHeightHhi J.postHeightTargetInputs

/-- The fresh bridge target is the target used to construct that bridge. -/
@[simp] theorem postHeightTarget_eq_scaffoldTarget
    (J : BankPaperCanonicalSectionNinePostHeightBridgeInputsAt
      (K0 := K0) M Bsource R certificate I deltaStar hdelta) :
    J.postHeightTarget = J.scaffoldTarget :=
  rfl

/-- The scaled seed of mass `qn` installed in the fresh bridge. -/
def postHeightActiveSeed
    (J : BankPaperCanonicalSectionNinePostHeightBridgeInputsAt
      (K0 := K0) M Bsource R certificate I deltaStar hdelta) :
    J.postHeightBridge.sampleData.Sample → Real :=
  bankPaperCanonicalSectionNinePostHeightActiveSeed
    J.postHeightBridge I J.postHeightHlo J.postHeightHhi
      J.postHeightTargetInputs

/-- The new bridge baseline is exactly the paper-faithful post-height seed. -/
@[simp] theorem postHeightBridge_baseWeight
    (J : BankPaperCanonicalSectionNinePostHeightBridgeInputsAt
      (K0 := K0) M Bsource R certificate I deltaStar hdelta)
    (m : J.postHeightBridge.sampleData.Sample) :
    J.postHeightBridge.baseline.baseWeight m =
      J.postHeightActiveSeed m := by
  simpa only [
    postHeightBridge, postHeightActiveSeed,
    bankPaperCanonicalSectionNinePostHeightActiveSeed,
    postHeightTarget_eq_scaffoldTarget] using
    (bankPaperCanonicalActiveMassBridgeData_baseWeight_scaledSeed
      Bsource.sampleData J.scaffoldTarget J.qn
        J.targetInputs.activeMass_pos M hdelta Bsource.n_gt_one
        J.hW J.scaleSeparation none J.meshWidth_pos m)

/-- The rounded `q0` is unchanged when the scaffold baseline is replaced. -/
@[simp] theorem roundedQ0_eq_postHeightBridge
    (J : BankPaperCanonicalSectionNinePostHeightBridgeInputsAt
      (K0 := K0) M Bsource R certificate I deltaStar hdelta) :
    J.q0 =
      bankPaperCanonicalTopFrozenRoundedActiveMass (K := K0 + 1)
        J.postHeightBridge R certificate deltaStar J.betaProt
          J.alpha J.qTilde :=
  rfl

/-- The rounded frozen ledger is likewise independent of the scaffold
baseline and partition. -/
@[simp] theorem roundedLambda0_eq_postHeightBridge
    (J : BankPaperCanonicalSectionNinePostHeightBridgeInputsAt
      (K0 := K0) M Bsource R certificate I deltaStar hdelta) :
    J.Lambda0 =
      bankPaperCanonicalActualFrozenLogMass
        J.postHeightBridge.sampleData
        (R.paperFixedExceptionalFactors deltaStar)
        (baseBankFactors R.exactificationState)
        (R.roughCanonicalGuardedCandidateSet certificate
          deltaStar (K0 + 1))
        (bankPaperCanonicalTopFrozenRoundedSourceSelector (K := K0 + 1)
          J.postHeightBridge R certificate J.Tsource deltaStar
            J.betaProt J.alpha J.beta J.qTilde)
        (bankPaperCanonicalTopFrozenRoundedActiveSeed (K := K0 + 1)
          J.postHeightBridge R certificate J.Tsource deltaStar
            J.betaProt J.alpha J.qTilde) :=
  rfl

end BankPaperCanonicalSectionNinePostHeightBridgeInputsAt

namespace BankPaperCanonicalSectionNinePostHeightBridgeInputsAt

variable
    {delta eta : Real} {M : RegularRelativeMesh.Mesh delta eta}
    {P : Finset Nat}
    {Bsource : BridgeData (PaperHeadSimplex.Tag P)
      (BankPaperCanonicalExponentBand M)}
    {c : Real} {depth K0 : Nat}
    {R : BankPaperRealization Bsource.sampleData.n
      (upperEndpoint Bsource.sampleData.n
        (upperTailLength c Bsource.sampleData.n))}
    {certificate : GuardedCentralAnchorCertificate c depth
      Bsource.sampleData.n R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth)}
    {I : PhysicalIntervals} {deltaStar : Real} {hdelta : 0 < delta}

/-- The nearest-integer active seed of the rounded frozen-top source. -/
def roundedActiveSeed
    (J : BankPaperCanonicalSectionNinePostHeightBridgeInputsAt
      (K0 := K0) M Bsource R certificate I deltaStar hdelta) :
    J.postHeightBridge.sampleData.Sample → Real :=
  bankPaperCanonicalTopFrozenRoundedActiveSeed (K := K0 + 1)
    J.postHeightBridge R certificate J.Tsource deltaStar
      J.betaProt J.alpha J.qTilde

/-- The literal rounded frozen-top source on the fresh bridge sample. -/
def roundedSourceSelector
    (J : BankPaperCanonicalSectionNinePostHeightBridgeInputsAt
      (K0 := K0) M Bsource R certificate I deltaStar hdelta) : Nat → Real :=
  bankPaperCanonicalTopFrozenRoundedSourceSelector (K := K0 + 1)
    J.postHeightBridge R certificate J.Tsource deltaStar
      J.betaProt J.alpha J.beta J.qTilde

/-- The source after the complete smooth-row post-height placement. -/
def placedPreSelector
    (J : BankPaperCanonicalSectionNinePostHeightBridgeInputsAt
      (K0 := K0) M Bsource R certificate I deltaStar hdelta) : Nat → Real :=
  bankPaperCanonicalSectionNinePostHeightPlacedPreSelector (K := K0 + 1)
    J.postHeightBridge R certificate J.Tsource I
      J.postHeightHlo J.postHeightHhi J.postHeightTargetInputs
      deltaStar J.betaProt J.alpha J.beta J.qTilde

end BankPaperCanonicalSectionNinePostHeightBridgeInputsAt

/-! ## Literal source and finite geometry -/

/-- The selector, height, and finite geometry inputs needed to pass from the
rounded source to the fresh post-height active measure.

There is no legacy `SymmetricHeightCoreInputsAt` field.  In particular, no
baseline is pinned to `q0`: every bridge-facing assertion below names
`J.postHeightBridge`, whose mass is `qn`. -/
structure BankPaperCanonicalSectionNinePostHeightSourceInputsAt
    {delta eta : Real} (M : RegularRelativeMesh.Mesh delta eta)
    {P : Finset Nat}
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
    (deltaStar : Real)
    (hdelta : 0 < delta)
    (J : BankPaperCanonicalSectionNinePostHeightBridgeInputsAt
      (K0 := K0) M Bsource R certificate I deltaStar hdelta) where
  lowerOne : ∀ sign, 1 ≤ I.lower sign
  upperTwo : ∀ sign, I.upper sign ≤ 2
  upperBroad : ∀ sign,
    physicalBound (I.upper sign) J.postHeightBridge.sampleData.n ≤
      2 * J.postHeightBridge.sampleData.n -
        (K0 + 1) *
          upperTailLength c J.postHeightBridge.sampleData.n
  qn_one_le : 1 ≤ J.qn
  hprime : ∀ p ∈ P, p.Prime
  hpattern :
    J.postHeightBridge.sampleData.pattern =
      PaperHeadSimplex.pattern P hprime J.exponent
  headPrimes : primesUpTo J.postHeightBridge.sampleData.W ⊆ P
  headSeparated : J.postHeightBridge.sampleData.HeadPatternsSeparated
  roughDepth :
    (K0 + 1) *
      upperTailLength c J.postHeightBridge.sampleData.n ≤
        J.postHeightBridge.sampleData.n
  outsideGuard : ∀ m : J.postHeightBridge.sampleData.Sample,
    J.postHeightBridge.sampleData.value m ∉
      R.roughCanonicalGuardSet certificate deltaStar
  betaProt_nonneg : 0 ≤ J.betaProt
  sourceState :
    BankPaperCanonicalSelectorSourceState
      (W := J.postHeightBridge.sampleData.W) R certificate
      (R.paperFixedExceptionalFactors deltaStar)
      (R.roughCanonicalGuardedCandidateSet certificate
        deltaStar (K0 + 1))
      J.roundedSourceSelector
  Cmass : Real
  density : Real
  Cmass_nonneg : 0 ≤ Cmass
  density_pos : 0 < density
  massUpper :
    J.qn ≤
      Cmass * (J.postHeightBridge.sampleData.n : Real) /
        J.postHeightBridge.L
  cellDensity : ∀ cell : Cell (PaperHeadSimplex.Tag P),
    density * (J.postHeightBridge.sampleData.n : Real) ≤
      (Fintype.card
        (J.postHeightBridge.sampleData.SampleAt cell) : Real)
  combined_dvd :
    centralAnchorDivisor J.postHeightBridge.sampleData.n
          (centralAnchorCutoff depth J.postHeightBridge.sampleData.n)
          certificate.q * R.prechargeBaseStateProduct ∣
      centralTailProduct J.postHeightBridge.sampleData.n
        (upperTailLength c J.postHeightBridge.sampleData.n)
  base_dvd :
    (baseBankFactors R.exactificationState).prod id ∣
      certificate.prechargedTailTarget
  charge_dvd :
    R.selectorTailCharge
          (R.paperFixedExceptionalFactors deltaStar) ∣
      certificate.prechargedTailTarget
  target_tail :
    certificate.prechargedTailTarget *
          centralAnchorDivisor J.postHeightBridge.sampleData.n
            (centralAnchorCutoff depth J.postHeightBridge.sampleData.n)
            certificate.q =
      centralTailProduct J.postHeightBridge.sampleData.n
        (upperTailLength c J.postHeightBridge.sampleData.n)

namespace BankPaperCanonicalSectionNinePostHeightSourceInputsAt

variable
    {delta eta : Real} {M : RegularRelativeMesh.Mesh delta eta}
    {P : Finset Nat}
    {Bsource : BridgeData (PaperHeadSimplex.Tag P)
      (BankPaperCanonicalExponentBand M)}
    {c : Real} {depth K0 : Nat}
    {R : BankPaperRealization Bsource.sampleData.n
      (upperEndpoint Bsource.sampleData.n
        (upperTailLength c Bsource.sampleData.n))}
    {certificate : GuardedCentralAnchorCertificate c depth
      Bsource.sampleData.n R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth)}
    {I : PhysicalIntervals} {deltaStar : Real} {hdelta : 0 < delta}
    {J : BankPaperCanonicalSectionNinePostHeightBridgeInputsAt
      (K0 := K0) M Bsource R certificate I deltaStar hdelta}











end BankPaperCanonicalSectionNinePostHeightSourceInputsAt

/-! ## Remaining Proposition 8.7 and slack inputs -/

/-- The genuinely dependent finite tail after the post-height source has
been constructed.

The target envelopes, placed frozen ledger, active ledger, placement-seed
bound, and protected reserve are deliberately not fields: they follow from
the ordinary-log connector, frozen invariance, mass/cell density, and the
protected-refinement theorem.  The sole remaining prime-rate input is the
final placed-selector deficit bound.  Its future uniform derivation is the
composition of the existing source rates with the new post-height placement
rate; no such composite theorem is assumed here. -/
structure BankPaperCanonicalSectionNinePostHeightDependentInputsAt
    {delta eta : Real} (M : RegularRelativeMesh.Mesh delta eta)
    {P : Finset Nat}
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
    (deltaStar sigma Cpost : Real)
    (hdelta : 0 < delta)
    (J : BankPaperCanonicalSectionNinePostHeightBridgeInputsAt
      (K0 := K0) M Bsource R certificate I deltaStar hdelta)
    (S : BankPaperCanonicalSectionNinePostHeightSourceInputsAt
      M Bsource R certificate I deltaStar hdelta J) where
  Cinitial : Real
  Cfixed : Real
  Cinitial_nonneg : 0 ≤ Cinitial
  selectorDeficit :
    ∀ p ∈ primeBand J.postHeightBridge.sampleData.n
        J.postHeightBridge.sampleData.W,
      abs (bankPaperCanonicalSelectorValuationDeficit
        R certificate (R.paperFixedExceptionalFactors deltaStar)
          (R.roughCanonicalGuardedCandidateSet certificate
            deltaStar (K0 + 1))
          J.placedPreSelector p) ≤
        Cinitial * J.postHeightBridge.q /
          ((p : Real) * J.postHeightBridge.L)
  roundedFrozenLedger :
    ∀ m : J.postHeightBridge.sampleData.Sample,
      BridgeData.frozenAmbientWeight
          (bankPaperCanonicalActualFrozenValue
            (candidates :=
              R.roughCanonicalGuardedCandidateSet certificate
                deltaStar (K0 + 1)))
          (bankPaperCanonicalActualFrozenWeight
            J.postHeightBridge.sampleData
            (R.roughCanonicalGuardedCandidateSet certificate
              deltaStar (K0 + 1))
            J.roundedSourceSelector J.roundedActiveSeed)
          (J.postHeightBridge.sampleData.value m) ≤
        Cfixed / J.postHeightBridge.L
  primeDeviation :
    J.postHeightBridge.primeDeviationL1 ≤
      7 * J.postHeightBridge.w
  radius : NNReal
  localP87 :
    ∀ (Delta : BankPaperCanonicalExponentBand M → Real),
      J.postHeightBridge.HasTargetEnvelopes (7 * Cinitial) Delta →
      ∀ (markedTarget : Nat → Real) (N : Real),
        0 ≤ N →
        J.postHeightBridge.q ≤ (1 : Real) * N →
        (∀ p ∈ primeBand J.postHeightBridge.sampleData.n
            J.postHeightBridge.sampleData.W,
          abs (markedTarget p -
            J.postHeightBridge.paperMoment
              (J.postHeightBridge.markedValuation p) 0) ≤
              Cinitial * N /
                ((p : Real) * J.postHeightBridge.L)) →
        (∀ j, Delta j =
          J.postHeightBridge.markedBandResidual markedTarget 0 j) →
        ∀ {Fixed : Type} [Fintype Fixed],
          ∀ (fixedValue : Fixed → Nat) (fixedWeight : Fixed → Real)
            (quota : Int),
            (quota : Real) = (∑ f, fixedWeight f) +
              J.postHeightBridge.q →
            J.postHeightBridge.sampleData.HeadPatternsSeparated →
            (∀ x,
              BridgeData.frozenAmbientWeight fixedValue fixedWeight x ∈
                Icc (0 : Real) 1) →
            (∀ m : J.postHeightBridge.sampleData.Sample,
              BridgeData.frozenAmbientWeight fixedValue fixedWeight
                  (J.postHeightBridge.sampleData.value m) ≤
                Cfixed / J.postHeightBridge.L) →
            (∀ m : J.postHeightBridge.sampleData.Sample,
              J.postHeightBridge.baseline.baseWeight m ≤
                (S.Cmass / S.density) / J.postHeightBridge.L) →
            J.postHeightBridge.HasPaperProposition87Conclusion
              Delta radius markedTarget N Cpost
                fixedValue fixedWeight quota
  cellIndex : BankPaperCanonicalTangentPrime
    J.postHeightBridge.sampleData.n
      J.postHeightBridge.sampleData.W → Nat
  fixedRoom :
    J.betaProt + S.Cmass / S.density ≤ Cfixed
  W_large : 1 < J.postHeightBridge.sampleData.W
  sigma_nonneg : 0 ≤ sigma
  sigma_le_betaProt : sigma ≤ J.betaProt
  largeL :
    Cfixed +
        Real.exp (2 *
          ((Erdos390.Full.PaperStatisticNorm.valuationLogCoefficient
                2 J.postHeightBridge.sampleData.W +
            J.postHeightBridge.nuisanceStatisticCoefficient 2) *
              (3 * (radius : Real)))) *
          (S.Cmass / S.density) + sigma ≤
      J.postHeightBridge.L
  nonsmooth :
    ∀ label,
      RoughCanonicalActiveNonexceptionalLabel
          J.postHeightBridge.sampleData.n deltaStar label →
        sigma / J.postHeightBridge.L +
            |R.roughCanonicalGuardedPostchargeCorrectionDensity certificate
              deltaStar J.postHeightBridge.sampleData.W (K0 + 1) label
                J.alpha J.beta J.postHeightBridge.L| ≤
          J.beta / J.postHeightBridge.L ∧
        J.beta / J.postHeightBridge.L +
            |R.roughCanonicalGuardedPostchargeCorrectionDensity certificate
              deltaStar J.postHeightBridge.sampleData.W (K0 + 1) label
                J.alpha J.beta J.postHeightBridge.L| ≤
          1 - sigma / J.postHeightBridge.L

namespace BankPaperCanonicalSectionNinePostHeightDependentInputsAt

variable
    {delta eta : Real} {M : RegularRelativeMesh.Mesh delta eta}
    {P : Finset Nat}
    {Bsource : BridgeData (PaperHeadSimplex.Tag P)
      (BankPaperCanonicalExponentBand M)}
    {c : Real} {depth K0 : Nat}
    {R : BankPaperRealization Bsource.sampleData.n
      (upperEndpoint Bsource.sampleData.n
        (upperTailLength c Bsource.sampleData.n))}
    {certificate : GuardedCentralAnchorCertificate c depth
      Bsource.sampleData.n R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth)}
    {I : PhysicalIntervals} {deltaStar sigma Cpost : Real}
    {hdelta : 0 < delta}
    {J : BankPaperCanonicalSectionNinePostHeightBridgeInputsAt
      (K0 := K0) M Bsource R certificate I deltaStar hdelta}
    {S : BankPaperCanonicalSectionNinePostHeightSourceInputsAt
      M Bsource R certificate I deltaStar hdelta J}



















end BankPaperCanonicalSectionNinePostHeightDependentInputsAt

/-! ## Exact placement-rate transport -/



/-! ## Finite package producer and synchronized adapter -/





end BankPaperRealization

end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankPaperCanonicalSectionNinePostHeightHeadMarginAlgebra -/
section


/-!
# Finite head-margin algebra for the post-height target

This file isolates the elementary finite-dimensional argument behind the
head-simplex margins.  It contains no realization, certificate, source-state,
or placement hypothesis.

For fixed positive coordinate scales `a p` and nonnegative upper scales
`b p`, suppose a target coordinate lies between `a p * N` and `b p * N`,
while its active mass lies between `cLower * N` and `cUpper * N`.  A finite
minimum of the `a p` gives a common positive vertex reserve.  If the exponent
is large enough that

`2 * sum_p b p <= E * cLower`,

then the zero vertex has reserve at least `1 / 2`.  The minimum of these two
reserves works simultaneously for any two target/mass pairs satisfying the
same envelopes, in particular for the frozen source mass and the fresh
post-height mass.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

noncomputable section

/-! ## Fixed finite coordinate and simplex margins -/

/-- A positive common lower scale for a finite family.  Inserting `1` makes
the definition useful without a nonemptiness assumption on `P`; when `P` is
empty only the zero head vertex remains. -/
noncomputable def
    bankPaperCanonicalSectionNinePostHeightHeadCoordinateFloor
    {P : Finset Nat} (a : {p : Nat // p ∈ P} → Real) : Real :=
  (insert 1
      ((Finset.univ : Finset {p : Nat // p ∈ P}).image a)).min'
    (Finset.insert_nonempty 1 _)





/-- A common head-simplex margin: one half for the zero vertex, intersected
with the lower bound for every nonzero vertex. -/
def bankPaperCanonicalSectionNinePostHeightHeadMargin
    {P : Finset Nat} (E : Nat)
    (a : {p : Nat // p ∈ P} → Real) (cUpper : Real) : Real :=
  min (1 / 2)
    (bankPaperCanonicalSectionNinePostHeightHeadCoordinateFloor a /
      ((E : Real) * cUpper))



/-! ## Choosing a sufficiently large exponent -/



/-! ## One target/mass pair -/



/-! ## Simultaneous source and post-height margins -/



end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankPaperCanonicalSectionNinePostHeightPhysicalMarginAlgebra -/
section


/-!
# The explicit post-height physical margin

This file fixes one completely explicit pair of paper-valid physical
intervals around

`mu = log (3 / 2)`.

The minus pool is `[1, 4 / 3]` and the plus pool is
`[5 / 3, 7 / 4]`.  Thus both pools lie in the paper's physical range
`[1, 2]`, and there is a fixed logarithmic gap on either side of `mu`.

The analytic input is kept transparent.  A generic lemma says that an
error which is `O(scale)` tends to zero whenever `scale` does, and hence
the corresponding centered mean eventually retains half of any fixed
`PhysicalInterpolationTarget` margin.  It is then applied to the literal
post-height physical-mean error and the paper's scale

`L / N`, where `N = secondOrderScale = n / L`.

No target/source wrapper and no conclusion-bearing premise is introduced.
-/

open Filter Topology Set Asymptotics

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.PaperBridgeFit
open Erdos390.Full.PaperGuardCensus
open Erdos390.Full.Scale

noncomputable section

/-! ## Explicit paper-valid physical data -/

/-- The fixed logarithmic center used for the two physical pools. -/
def bankPaperCanonicalSectionNinePostHeightPhysicalMu : Real :=
  Real.log ((3 : Real) / 2)

/-- Two explicit separated physical intervals contained in `[1, 2]`. -/
def bankPaperCanonicalSectionNinePostHeightPhysicalIntervals :
    PhysicalIntervals where
  lower
    | .minus => 1
    | .plus => (5 : Real) / 3
  upper
    | .minus => (4 : Real) / 3
    | .plus => (7 : Real) / 4
  lower_pos := by
    intro sigma
    cases sigma <;> norm_num
  lower_lt_upper := by
    intro sigma
    cases sigma <;> norm_num
  separated := by
    norm_num

@[simp] theorem
    bankPaperCanonicalSectionNinePostHeightPhysicalIntervals_lower_minus :
    bankPaperCanonicalSectionNinePostHeightPhysicalIntervals.lower .minus =
      1 := rfl

@[simp] theorem
    bankPaperCanonicalSectionNinePostHeightPhysicalIntervals_upper_minus :
    bankPaperCanonicalSectionNinePostHeightPhysicalIntervals.upper .minus =
      (4 : Real) / 3 := rfl

@[simp] theorem
    bankPaperCanonicalSectionNinePostHeightPhysicalIntervals_lower_plus :
    bankPaperCanonicalSectionNinePostHeightPhysicalIntervals.lower .plus =
      (5 : Real) / 3 := rfl

@[simp] theorem
    bankPaperCanonicalSectionNinePostHeightPhysicalIntervals_upper_plus :
    bankPaperCanonicalSectionNinePostHeightPhysicalIntervals.upper .plus =
      (7 : Real) / 4 := rfl







/-- The smaller of the two logarithmic gaps around the fixed center. -/
def bankPaperCanonicalSectionNinePostHeightPhysicalGap : Real :=
  min
    (bankPaperCanonicalSectionNinePostHeightPhysicalMu -
      Real.log
        (bankPaperCanonicalSectionNinePostHeightPhysicalIntervals.upper
          .minus))
    (Real.log
        (bankPaperCanonicalSectionNinePostHeightPhysicalIntervals.lower
          .plus) -
      bankPaperCanonicalSectionNinePostHeightPhysicalMu)

theorem bankPaperCanonicalSectionNinePostHeightPhysicalGap_pos :
    0 < bankPaperCanonicalSectionNinePostHeightPhysicalGap := by
  unfold bankPaperCanonicalSectionNinePostHeightPhysicalGap
  apply lt_min
  · apply sub_pos.mpr
    change
      Real.log ((4 : Real) / 3) <
        Real.log ((3 : Real) / 2)
    exact Real.strictMonoOn_log (by norm_num) (by norm_num) (by norm_num)
  · apply sub_pos.mpr
    change
      Real.log ((3 : Real) / 2) <
        Real.log ((5 : Real) / 3)
    exact Real.strictMonoOn_log (by norm_num) (by norm_num) (by norm_num)

/-- A fixed positive margin, chosen as half of the smaller endpoint gap. -/
def bankPaperCanonicalSectionNinePostHeightPhysicalEta : Real :=
  bankPaperCanonicalSectionNinePostHeightPhysicalGap / 2

theorem bankPaperCanonicalSectionNinePostHeightPhysicalEta_pos :
    0 < bankPaperCanonicalSectionNinePostHeightPhysicalEta := by
  exact div_pos
    bankPaperCanonicalSectionNinePostHeightPhysicalGap_pos (by norm_num)

theorem
    bankPaperCanonicalSectionNinePostHeightPhysicalEta_le_minus_gap :
    bankPaperCanonicalSectionNinePostHeightPhysicalEta ≤
      bankPaperCanonicalSectionNinePostHeightPhysicalMu -
        Real.log
          (bankPaperCanonicalSectionNinePostHeightPhysicalIntervals.upper
            .minus) := by
  calc
    bankPaperCanonicalSectionNinePostHeightPhysicalEta =
        bankPaperCanonicalSectionNinePostHeightPhysicalGap / 2 := rfl
    _ ≤ bankPaperCanonicalSectionNinePostHeightPhysicalGap := by
      linarith [bankPaperCanonicalSectionNinePostHeightPhysicalGap_pos]
    _ ≤ bankPaperCanonicalSectionNinePostHeightPhysicalMu -
          Real.log
            (bankPaperCanonicalSectionNinePostHeightPhysicalIntervals.upper
              .minus) := by
      unfold bankPaperCanonicalSectionNinePostHeightPhysicalGap
      exact min_le_left _ _

theorem
    bankPaperCanonicalSectionNinePostHeightPhysicalEta_le_plus_gap :
    bankPaperCanonicalSectionNinePostHeightPhysicalEta ≤
      Real.log
          (bankPaperCanonicalSectionNinePostHeightPhysicalIntervals.lower
            .plus) -
        bankPaperCanonicalSectionNinePostHeightPhysicalMu := by
  calc
    bankPaperCanonicalSectionNinePostHeightPhysicalEta =
        bankPaperCanonicalSectionNinePostHeightPhysicalGap / 2 := rfl
    _ ≤ bankPaperCanonicalSectionNinePostHeightPhysicalGap := by
      linarith [bankPaperCanonicalSectionNinePostHeightPhysicalGap_pos]
    _ ≤ Real.log
          (bankPaperCanonicalSectionNinePostHeightPhysicalIntervals.lower
            .plus) -
          bankPaperCanonicalSectionNinePostHeightPhysicalMu := by
      unfold bankPaperCanonicalSectionNinePostHeightPhysicalGap
      exact min_le_right _ _

/-- The explicit, fixed physical interpolation target. -/
def bankPaperCanonicalSectionNinePostHeightFixedPhysicalTarget :
    PhysicalInterpolationTarget
      bankPaperCanonicalSectionNinePostHeightPhysicalIntervals where
  mu := bankPaperCanonicalSectionNinePostHeightPhysicalMu
  eta := bankPaperCanonicalSectionNinePostHeightPhysicalEta
  eta_pos := bankPaperCanonicalSectionNinePostHeightPhysicalEta_pos
  minus_below := by
    linarith [
      bankPaperCanonicalSectionNinePostHeightPhysicalEta_le_minus_gap]
  plus_above := by
    linarith [
      bankPaperCanonicalSectionNinePostHeightPhysicalEta_le_plus_gap]

@[simp] theorem
    bankPaperCanonicalSectionNinePostHeightFixedPhysicalTarget_mu :
    bankPaperCanonicalSectionNinePostHeightFixedPhysicalTarget.mu =
      bankPaperCanonicalSectionNinePostHeightPhysicalMu := rfl

@[simp] theorem
    bankPaperCanonicalSectionNinePostHeightFixedPhysicalTarget_eta :
    bankPaperCanonicalSectionNinePostHeightFixedPhysicalTarget.eta =
      bankPaperCanonicalSectionNinePostHeightPhysicalEta := rfl

/-! ## The elementary asymptotic margin algebra -/







/-! ## The literal post-height physical mean -/





end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankPaperCanonicalSectionNinePostHeightCoherentTargetConstructor -/
section


/-!
# The coherent finite post-height target constructor

This file closes the finite choice boundary between the depth-first
combined-charge terminal and the fresh Section 9 post-height bridge.

There are two deliberately separate pieces.

* The first theorem turns the eventual existential output of
  `BankPaperCombinedChargeTerminalAtDepth` into one honest tail family.  Its
  conclusion repeats the six literal terminal properties pointwise; no
  conclusion-bearing structure is introduced.
* The bridge definitions below start from an actual
  `StructuredSampleData`, build a harmless scaffold bridge, form the
  paper's literal head/physical barycentric target on that sample, and then
  install that same target in a canonical bridge.  This removes the
  otherwise circular-looking dependence of `barycentricTargetOfPaperData`
  on an already supplied `BridgeData`.

The eventual head and physical interior estimates are proved in the
remaining sections of this module.
-/

open Filter Topology Set
open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.PaperBridgeFit
open Erdos390.Full.PaperGuardCensus
open Erdos390.Full.PaperHeadSimplex
open Erdos390.Full.RegularMeshPrimeCutoffs
open Erdos390.Full.RegularRelativeMesh
open Erdos390.Full.Scale

noncomputable section

/-! ## One coherent family chosen from the eventual terminal -/



/-! ## Uniform finite head bounds from the same fibers -/

/-- A fixed positive coefficient retained for every head prime at most
`W`.  The denominator `48 W` leaves ample room for both pieces of the
combined charge outside the stationary anchor support. -/
def bankPaperCanonicalSectionNinePostHeightHeadLinearFloor
    (c : Real) (W : Nat) : Real :=
  (c - C0) / (48 * (W : Real))



/-- The fixed-prime upper coefficient used for the head-simplex
zero-coordinate estimate. -/
def bankPaperCanonicalSectionNinePostHeightHeadUpperCoefficient
    (c : Real) (p : Nat) : Real :=
  c / (((p - 1 : Nat) : Real)) + 1





/-! ## One pair of source/post-height mass envelopes -/





/-! ## Exact synchronization of the local and family physical means -/



/-! ## A non-circular bridge built from structured sample data -/

/-- A harmless positive baseline used only to give the sample a temporary
`BridgeData` wrapper while the genuine barycentric target is constructed. -/
def bankPaperCanonicalSectionNineTargetScaffoldBaseline
    {Head : Type*} [Fintype Head]
    (D : StructuredSampleData Head) :
    BaselineAllocation D where
  cellMass := fun _ => 1
  cellMass_pos := fun _ => by norm_num

/-- Temporary bridge on an already constructed sample.  Its baseline is
irrelevant: `barycentricTargetOfPaperData` depends on the structured sample
and the displayed head/physical data, not on this baseline. -/
def bankPaperCanonicalSectionNineTargetScaffoldBridge
    {delta eta : Real} (M : RegularRelativeMesh.Mesh delta eta)
    {P : Finset Nat}
    (D : StructuredSampleData (PaperHeadSimplex.Tag P))
    (hdelta : 0 < delta) (hn : 1 < D.n) (hW : D.W ≠ 0)
    (S : ScaleSeparation M D.n D.W) (hw : 0 < delta + eta) :
    BridgeData (PaperHeadSimplex.Tag P)
      (BankPaperCanonicalExponentBand M) where
  sampleData := D
  baseline := bankPaperCanonicalSectionNineTargetScaffoldBaseline D
  partition :=
    RegularMeshPrimeCutoffs.Mesh.canonicalPartition
      M hdelta hn hW S
  lowBand := RegularMeshPrimeCutoffs.Mesh.lowBand M
  referenceHead := none
  w := delta + eta
  w_pos := hw
  n_gt_one := hn

@[simp] theorem
    bankPaperCanonicalSectionNineTargetScaffoldBridge_sampleData
    {delta eta : Real} (M : RegularRelativeMesh.Mesh delta eta)
    {P : Finset Nat}
    (D : StructuredSampleData (PaperHeadSimplex.Tag P))
    (hdelta : 0 < delta) (hn : 1 < D.n) (hW : D.W ≠ 0)
    (S : ScaleSeparation M D.n D.W) (hw : 0 < delta + eta) :
    (bankPaperCanonicalSectionNineTargetScaffoldBridge
      M D hdelta hn hW S hw).sampleData = D :=
  rfl

/-- The source head reserve obtained from the already proved simultaneous
head-margin inequalities. -/
def bankPaperCanonicalSectionNineCoherentSourceHeadReserve
    {P : Finset Nat}
    (E : Nat) (qSource : Real)
    (target : {p : Nat // p ∈ P} → Real)
    (margin : Real)
    (hE : 0 < E) (hqSource : 0 < qSource)
    (hmargin : 0 < margin)
    (hvertex :
      ∀ p, margin ≤ target p / ((E : Real) * qSource))
    (hzero :
      margin ≤
        1 - ∑ p : {p : Nat // p ∈ P},
          target p / ((E : Real) * qSource)) :
    HeadSimplexReserve P where
  exponent := E
  exponent_pos := hE
  activeMass := qSource
  activeMass_pos := hqSource
  target := target
  margin := margin
  margin_pos := hmargin
  vertex_margin := hvertex
  zero_margin := hzero

@[simp] theorem
    bankPaperCanonicalSectionNineCoherentSourceHeadReserve_exponent
    {P : Finset Nat}
    (E : Nat) (qSource : Real)
    (target : {p : Nat // p ∈ P} → Real)
    (margin : Real)
    (hE : 0 < E) (hqSource : 0 < qSource)
    (hmargin : 0 < margin)
    (hvertex :
      ∀ p, margin ≤ target p / ((E : Real) * qSource))
    (hzero :
      margin ≤
        1 - ∑ p : {p : Nat // p ∈ P},
          target p / ((E : Real) * qSource)) :
    (bankPaperCanonicalSectionNineCoherentSourceHeadReserve
      E qSource target margin hE hqSource hmargin hvertex hzero).exponent =
        E :=
  rfl

@[simp] theorem
    bankPaperCanonicalSectionNineCoherentSourceHeadReserve_activeMass
    {P : Finset Nat}
    (E : Nat) (qSource : Real)
    (target : {p : Nat // p ∈ P} → Real)
    (margin : Real)
    (hE : 0 < E) (hqSource : 0 < qSource)
    (hmargin : 0 < margin)
    (hvertex :
      ∀ p, margin ≤ target p / ((E : Real) * qSource))
    (hzero :
      margin ≤
        1 - ∑ p : {p : Nat // p ∈ P},
          target p / ((E : Real) * qSource)) :
    (bankPaperCanonicalSectionNineCoherentSourceHeadReserve
      E qSource target margin hE hqSource hmargin hvertex hzero).activeMass =
        qSource :=
  rfl

@[simp] theorem
    bankPaperCanonicalSectionNineCoherentSourceHeadReserve_target
    {P : Finset Nat}
    (E : Nat) (qSource : Real)
    (target : {p : Nat // p ∈ P} → Real)
    (margin : Real)
    (hE : 0 < E) (hqSource : 0 < qSource)
    (hmargin : 0 < margin)
    (hvertex :
      ∀ p, margin ≤ target p / ((E : Real) * qSource))
    (hzero :
      margin ≤
        1 - ∑ p : {p : Nat // p ∈ P},
          target p / ((E : Real) * qSource))
    (p : {p : Nat // p ∈ P}) :
    (bankPaperCanonicalSectionNineCoherentSourceHeadReserve
      E qSource target margin hE hqSource hmargin hvertex hzero).target p =
        target p :=
  rfl

/-- The genuine source target, formed directly on the supplied structured
sample through the temporary bridge. -/
def bankPaperCanonicalSectionNineCoherentSourceTarget
    {delta eta : Real} (M : RegularRelativeMesh.Mesh delta eta)
    {P : Finset Nat}
    (D : StructuredSampleData (PaperHeadSimplex.Tag P))
    (I : PhysicalIntervals)
    (hlo : ∀ sigma, D.lo sigma =
      physicalBound (I.lower sigma) D.n)
    (hhi : ∀ sigma, D.hi sigma =
      physicalBound (I.upper sigma) D.n)
    (Rhead : HeadSimplexReserve P)
    (Kphysical : PhysicalInterpolationTarget I)
    (hdelta : 0 < delta) (hn : 1 < D.n) (hW : D.W ≠ 0)
    (S : ScaleSeparation M D.n D.W) (hw : 0 < delta + eta) :
    BarycentricTarget D :=
  (bankPaperCanonicalSectionNineTargetScaffoldBridge
    M D hdelta hn hW S hw).barycentricTargetOfPaperData
      I hlo hhi Rhead Kphysical

/-- Install the directly constructed source target into the canonical mesh
bridge on the same structured sample. -/
def bankPaperCanonicalSectionNineCoherentSourceBridge
    {delta eta : Real} (M : RegularRelativeMesh.Mesh delta eta)
    {P : Finset Nat}
    (D : StructuredSampleData (PaperHeadSimplex.Tag P))
    (I : PhysicalIntervals)
    (hlo : ∀ sigma, D.lo sigma =
      physicalBound (I.lower sigma) D.n)
    (hhi : ∀ sigma, D.hi sigma =
      physicalBound (I.upper sigma) D.n)
    (Rhead : HeadSimplexReserve P)
    (Kphysical : PhysicalInterpolationTarget I)
    (hdelta : 0 < delta) (hn : 1 < D.n) (hW : D.W ≠ 0)
    (S : ScaleSeparation M D.n D.W) (hw : 0 < delta + eta) :
    BridgeData (PaperHeadSimplex.Tag P)
      (BankPaperCanonicalExponentBand M) :=
  bankPaperCanonicalBridgeData D
    (bankPaperCanonicalSectionNineCoherentSourceTarget
      M D I hlo hhi Rhead Kphysical hdelta hn hW S hw)
    M hdelta hn hW S none hw

@[simp] theorem bankPaperCanonicalSectionNineCoherentSourceBridge_sampleData
    {delta eta : Real} (M : RegularRelativeMesh.Mesh delta eta)
    {P : Finset Nat}
    (D : StructuredSampleData (PaperHeadSimplex.Tag P))
    (I : PhysicalIntervals)
    (hlo : ∀ sigma, D.lo sigma =
      physicalBound (I.lower sigma) D.n)
    (hhi : ∀ sigma, D.hi sigma =
      physicalBound (I.upper sigma) D.n)
    (Rhead : HeadSimplexReserve P)
    (Kphysical : PhysicalInterpolationTarget I)
    (hdelta : 0 < delta) (hn : 1 < D.n) (hW : D.W ≠ 0)
    (S : ScaleSeparation M D.n D.W) (hw : 0 < delta + eta) :
    (bankPaperCanonicalSectionNineCoherentSourceBridge
      M D I hlo hhi Rhead Kphysical hdelta hn hW S hw).sampleData = D :=
  rfl



/-! ## Finite coherent assembly of the fresh bridge inputs -/

/-- The literal finite head set used by the coherent constructor consists
only of primes. -/
theorem bankPaperCanonicalSectionNinePostHeight_primesUpTo_prime
    (W : Nat) :
    ∀ p ∈ primesUpTo W, p.Prime := by
  intro p hp
  exact (mem_primesUpTo.mp hp).1

namespace BankPaperRealization



/-! ## Eventual coherent target construction on supplied sample geometry -/



end BankPaperRealization

end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankPaperCanonicalSectionNineActiveLedgerConnector -/
section


/-!
# Density packaging for the Section 9 active ledger

The weak Section 9 local input asks for one fixed constant `Cactive` such
that every literal baseline coordinate is at most `Cactive / L`.  For the
canonical scaled seed this is already a consequence of three earlier facts:

* its mass family is `O(secondOrderScale)`;
* every guard-deleted canonical cell has a fixed positive linear density;
* every normalized barycentric cell mass is at most one.

This file packages those facts.  The finite lemma exposes the exact
mass/cardinality calculation.  The eventual theorem uses the proved
guarded raw-cell density and takes a genuine finite minimum over all fixed
head/physical cells.  No coordinate bound is assumed.
-/

open Filter Topology Asymptotics

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.GuardSquarefreeErrorRate
open Erdos390.Full.PaperBridgeFit
open Erdos390.Full.PaperGuardCensus
open Erdos390.Full.PaperScaleMarkedCell
open Erdos390.Full.Scale

noncomputable section

namespace BankPaperRealization

/-! ## A common density for every fixed canonical cell -/

/-- The smallest literal guard-deleted density among the finite family of
head/physical cells. -/
def bankPaperCanonicalGuardedCellDensityFloor
    {Head : Type*} [Fintype Head] [Nonempty Head]
    (Phead : Head → HeadPattern.Pattern)
    (I : PhysicalIntervals) : Real :=
  let densities := (Finset.univ : Finset (Cell Head)).image
    (fun cell =>
      paperCellDensity (Phead cell.1)
        (I.lower cell.2) (I.upper cell.2) / 4)
  densities.min' (by
    exact Finset.image_nonempty.mpr Finset.univ_nonempty)





/-! ## Finite coordinate packaging -/



/-! ## Eventual canonical density wrapper -/



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

/-- Constant in the uniform guarded postcharge density bound. -/
def roughCanonicalUniformGuardedPostchargeCorrectionDensityConstant
    (W K0 : Nat) (c beta : Real) : Real :=
  16 *
      (3 * roughCanonicalSharpUnifiedRowScaleConstant W K0 c beta +
        roughCanonicalBalancedGuardNumeratorConstant W K0 c beta) /
    roughCanonicalRawBroadPoolDensity W

















end BankPaperRealization

end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankPaperCanonicalSectionNinePostHeightEventualSupplierConnector -/
section


/-!
# Honest reduction boundary for the fresh Section 9 post-height bridge

This file deliberately stops before the synchronized analytic completion.
It exports three narrower layers:

* the uniform guarded zero-cell valuation estimate which was previously
  buried inside the placement proof;
* the genuinely missing post-height target/source producer obligation; and
* a finite local-input reduction which packages already-produced analytic
  fields without calling that package a completed eventual supplier.

The selector constant is chosen by
`exists_eventually_bankPaperCanonicalSectionNinePostHeightPlacedSelector_deficit_paperRate`
before Proposition 8.7 chooses its radius and `Cpost`.  In particular, no
supplier is asked to work for every possible later `Cinitial`.

Every family-level definition below uses one
`BankPaperCanonicalGuardedTailFamily`, hence one realization and guarded
certificate at a given index.  The public bridge is always the literal
fresh bridge `J.postHeightBridge`; no legacy symmetric-height equality
`q = q0` occurs.
-/

open Filter Topology Set
open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.ArithmeticBandGeometry
open Erdos390.Full.DickmanBasic
open Erdos390.Full.FiniteProbability
open Erdos390.Full.HeadPattern
open Erdos390.Full.PaperBridgeFit
open Erdos390.Full.PaperGuardCensus
open Erdos390.Full.PaperHeadSimplex
open Erdos390.Full.PaperPrimePowerChamberError
open Erdos390.Full.PaperRawTiltedValuationMeanRows
open Erdos390.Full.PaperScaleMarkedCell
open Erdos390.Full.RegularMeshPrimeCutoffs
open Erdos390.Full.RegularRelativeMesh
open Erdos390.Full.Scale

noncomputable section

namespace BankPaperRealization

set_option maxHeartbeats 2400000

/-! ## Uniform zero-cell valuation means -/



/-! ## The genuine producer obligation -/

/-- Primitive paper inputs still missing after all currently exported
eventual estimates are accounted for.

The first group is the uniform target/source construction:

* fixed positive margins for the pre-height source target and the fresh
  post-height target;
* one fixed positive head-simplex exponent;
* synchronization of the literal frozen mass, `qTilde`, and final active
  mass with the Section 8 analytic families; and
* the three primitive rounded-source residual facts.

The balanced-alpha box is not a field: it is supplied by
`eventually_bankPaperCanonicalPostHfitBalancedAlpha_mem_Icc`.  There is no
dependent-input, Post-Hfit-input, final-event, or implementation-rate field
in this record. -/
structure BankPaperCanonicalSectionNinePostHeightPrimitiveGapsAt
    {delta eta : Real} (M : RegularRelativeMesh.Mesh delta eta)
    {P : Finset Nat}
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
    (E : Nat)
    (deltaStar mu sourceMarginFloor headMarginFloor
      physicalEtaFloor postMarginFloor : Real)
    (logY Lambda0 mFrozen qTilde : Nat → Real)
    (hdelta : 0 < delta)
    (J : BankPaperCanonicalSectionNinePostHeightBridgeInputsAt
      (K0 := K0) M Bsource R certificate I deltaStar hdelta)
    (S : BankPaperCanonicalSectionNinePostHeightSourceInputsAt
      M Bsource R certificate I deltaStar hdelta J) where
  exponent_pos : 0 < E
  exponent_sync : J.exponent = E
  sourceMarginFloor_pos : 0 < sourceMarginFloor
  headMarginFloor_pos : 0 < headMarginFloor
  physicalEtaFloor_pos : 0 < physicalEtaFloor
  postMarginFloor_pos : 0 < postMarginFloor
  sourceTarget_margin :
    sourceMarginFloor ≤ J.Tsource.cellMassMargin
  headMargin_uniform :
    headMarginFloor ≤ J.targetInputs.headMargin
  physicalEta_uniform :
    physicalEtaFloor ≤ J.targetInputs.physicalEta
  postHeightTarget_margin :
    postMarginFloor ≤ J.postHeightTarget.cellMassMargin
  qTilde_family :
    J.qTilde = qTilde Bsource.sampleData.n
  mFrozen_family :
    mFrozen Bsource.sampleData.n =
      bankPaperCanonicalTopFrozenSmoothFrozenMass (K := K0 + 1)
        J.postHeightBridge R certificate deltaStar J.betaProt J.alpha
  finalActiveMass_family :
    J.qn =
      bankPaperCanonicalSmoothFinalActiveMassFamily
        mu logY Lambda0 mFrozen qTilde Bsource.sampleData.n
  sourceResidual :
    BankPaperCanonicalTopFrozenRoundedSourceResidualInputsAt
      (K := K0 + 1) J.postHeightBridge R certificate
        (R.paperFixedExceptionalFactors deltaStar)
        J.Tsource deltaStar J.betaProt J.alpha J.beta J.qTilde

/-- The explicit family-level obligation to construct the fresh bridge and
its source package from one guarded-tail family and the corresponding
capacity witnesses.

This is intentionally named an obligation, not a supplier theorem.  The
existential `J` contains the primitive
`BankPaperCanonicalSectionNinePostHeightBaselineTargetInputs`; the
existential `S` contains the source state obtained after applying the
conditional rounded-source theorem to `Hgap.sourceResidual`.  Their
existence has not yet been proved in the repository.

All already-exported alpha, rate, moment, frozen-ledger, P87, large-`L`,
and nonsmooth conclusions are absent. -/
def BankPaperCanonicalSectionNinePostHeightEventualCoherentBridgeSourceObligation
    (P : Finset Nat)
    (Patterns : PaperHeadSimplex.Tag P → Pattern)
    (I : PhysicalIntervals)
    (Cprom Cbank : Nat) (G : ∀ n, Ledger n Cprom Cbank)
    {c : Real} (depth W K0 E Ntail : Nat)
    (F : BankPaperCanonicalGuardedTailFamily c depth Ntail)
    (deltaStar betaProt betaAct mu sourceMarginFloor headMarginFloor
      physicalEtaFloor postMarginFloor Cmass density : Real)
    (logY Lambda0 mFrozen qTilde : Nat → Real)
    {delta eta : Real} (M : RegularRelativeMesh.Mesh delta eta)
    (hdelta : 0 < delta)
    (B : Nat → BridgeData (PaperHeadSimplex.Tag P)
      (BankPaperCanonicalExponentBand M)) : Prop :=
  ∀ᶠ n : Nat in atTop,
    ∃ Bsource : BridgeData (PaperHeadSimplex.Tag P)
        (BankPaperCanonicalExponentBand M),
      ∃ hnTail : Ntail ≤ Bsource.sampleData.n,
        let R := F.realization Bsource.sampleData.n hnTail
        let certificate := F.certificate Bsource.sampleData.n hnTail
        ∃ J : BankPaperCanonicalSectionNinePostHeightBridgeInputsAt
            (K0 := K0) M Bsource R certificate I deltaStar hdelta,
          ∃ S : BankPaperCanonicalSectionNinePostHeightSourceInputsAt
              M Bsource R certificate I deltaStar hdelta J,
            ∃ _Hgap :
                BankPaperCanonicalSectionNinePostHeightPrimitiveGapsAt
                  M Bsource R certificate I E deltaStar mu
                    sourceMarginFloor headMarginFloor physicalEtaFloor
                    postMarginFloor logY Lambda0 mFrozen qTilde
                    hdelta J S,
              ∃ hsep :
                  physicalBound (I.upper .minus)
                      J.postHeightBridge.sampleData.n <
                    physicalBound (I.lower .plus)
                      J.postHeightBridge.sampleData.n,
                ∃ hremaining :
                    ∀ cell : Cell (PaperHeadSimplex.Tag P),
                      (rawCell Patterns I
                          J.postHeightBridge.sampleData.n cell \
                        (G J.postHeightBridge.sampleData.n).guards).Nonempty,
                  B n = J.postHeightBridge ∧
                    Bsource.sampleData.n = n ∧
                    Bsource.sampleData.W = W ∧
                    J.betaProt = betaProt ∧
                    J.betaAct = betaAct ∧
                    J.postHeightBridge.sampleData =
                      canonicalSampleData
                        (W := J.postHeightBridge.sampleData.W)
                        Patterns I
                          (G J.postHeightBridge.sampleData.n)
                          hsep hremaining ∧
                    J.qTilde =
                      bankPaperCanonicalGuardedSmoothBaseMass
                        R certificate deltaStar
                          J.postHeightBridge.sampleData.W
                          (K0 + 1) J.betaAct ∧
                    S.Cmass = Cmass ∧
                    S.density = density

/-!
## Exact dependent-field census

For `BankPaperCanonicalSectionNinePostHeightDependentInputsAt`, the current
producer map is:

* the physical part of the fresh target interior:
  `bankPaperCanonicalSectionEight_physicalMeanError_isBigO` after the
  Section 8 family identities are synchronized; the unproved part of the
  coherent target constructor is the fixed head-simplex reserve and its
  assembly with that physical interval;
* `Cinitial`, its nonnegativity, and `selectorDeficit`: the uniform placed
  selector theorem, using the zero-cell theorem exported above together
  with the Section 8 `d` and final-mass rates;
* the balanced-alpha box: the standalone eventual balanced-alpha theorem;
* `Cfixed`, `roundedFrozenLedger`, and `fixedRoom`: choose
  `Cfixed = betaProt + Cactive`; additive-placement frozen invariance and
  post-height rounded-source invariance give the pointwise ledger;
* `primeDeviation`: eventual canonical `MomentReady` followed by
  `actual_L1_bound_of_ready`;
* `radius` and `localP87`: varying-active-mass canonical Proposition 8.7,
  with `Ctarget = 7 * Cinitial`, `Cmass = 1`, and
  `Cactive = S.Cmass / S.density`;
* `cellIndex`: the literal `bankPaperCanonicalRatioCellIndex`;
* `W_large`: the fixed choice `2 ≤ W`;
* `sigma_nonneg` and `sigma_le_betaProt`: the fixed parameter choice;
* `largeL`: `eventually_canonical_exponential_slack_le_L`, with `sigma`
  absorbed into the fixed term; and
* `nonsmooth`: `eventually_roughCanonicalBalancedNonsmoothBounds`.

The target envelope, placed frozen ledger, active ledger, active-seed bound,
and protected reserve are not fields of the dependent record: the existing
post-height local connector constructs them after the above data are
installed.

Thus the only producer gap is the uniform coherent target/source
construction recorded in
`BankPaperCanonicalSectionNinePostHeightPrimitiveGapsAt`.
-/

/-! ## Non-final finite local-input reduction -/

/-- What the present file is allowed to conclude at one index: the
balanced-alpha box and a dependent local-input package whose cell index is
the literal ratio-cell index from the same mesh witness.

This is strictly below the public Post-Hfit input and below every eventual
or completion proposition. -/
def BankPaperCanonicalSectionNinePostHeightLocalInputReductionAt
    {delta eta : Real} (M : RegularRelativeMesh.Mesh delta eta)
    {P : Finset Nat}
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
    (deltaStar rho sigma Cpost : Real)
    (hdelta : 0 < delta)
    (J : BankPaperCanonicalSectionNinePostHeightBridgeInputsAt
      (K0 := K0) M Bsource R certificate I deltaStar hdelta)
    (S : BankPaperCanonicalSectionNinePostHeightSourceInputsAt
      M Bsource R certificate I deltaStar hdelta J) : Prop :=
  (0 ≤ J.alpha ∧ J.alpha ≤ 1) ∧
    ∃ A : BankPaperCanonicalSectionNinePostHeightDependentInputsAt
        M Bsource R certificate I deltaStar sigma Cpost hdelta J S,
      A.cellIndex =
        bankPaperCanonicalRatioCellIndex M hdelta
          J.postHeightBridge.n_gt_one J.hW J.scaleSeparation rho



end BankPaperRealization

end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankPaperCanonicalSectionNinePostHeightSourceFirstEventualPostHfitConnector -/
section


/-!
# Source-first eventual Post-Hfit connector

This file performs the fixed-mesh eventual intersection which comes after
the source-first coherent bridge/source construction.

The only Proposition 8.7 input is a specialized eventual callback.  It is
stated below at the exact finite field consumed by
`bankPaperCanonicalSectionNinePostHeightLocalInputReduction_of_exportedFields`;
it does not assume a dependent-input package, a Post-Hfit input, or any
eventual conclusion.  Every other field is constructed here from the
source obligation, the Section 8 analytic ledger, and exported numerical
estimates.
-/

open Filter Topology Set Asymptotics
open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.ArithmeticBandGeometry
open Erdos390.Full.HeadPattern
open Erdos390.Full.PaperBridgeFit
open Erdos390.Full.PaperGuardCensus
open Erdos390.Full.PaperHeadSimplex
open Erdos390.Full.RegularMeshPrimeCutoffs
open Erdos390.Full.RegularRelativeMesh
open Erdos390.Full.Scale

noncomputable section

namespace BankPaperRealization

set_option maxHeartbeats 3600000

/-! ## Exact specialized Proposition 8.7 callback -/

/-- The precise one-index Proposition 8.7 field used by the post-height
finite reduction.

This definition is intentionally only the local P87 callback.  In
particular, it contains neither the selector conclusion nor any local or
eventual Post-Hfit package. -/
def BankPaperCanonicalSectionNinePostHeightSourceFirstSpecializedLocalP87At
    {delta eta : Real} (M : RegularRelativeMesh.Mesh delta eta)
    {P : Finset Nat}
    {Bsource : BridgeData (PaperHeadSimplex.Tag P)
      (BankPaperCanonicalExponentBand M)}
    {c : Real} {depth K0 : Nat}
    {R : BankPaperRealization Bsource.sampleData.n
      (upperEndpoint Bsource.sampleData.n
        (upperTailLength c Bsource.sampleData.n))}
    {certificate : GuardedCentralAnchorCertificate c depth
      Bsource.sampleData.n R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth)}
    {I : PhysicalIntervals} {deltaStar : Real} {hdelta : 0 < delta}
    (Cinitial : Real) (radius : NNReal) (Cpost : Real)
    (J : BankPaperCanonicalSectionNinePostHeightBridgeInputsAt
      (K0 := K0) M Bsource R certificate I deltaStar hdelta)
    (S : BankPaperCanonicalSectionNinePostHeightSourceInputsAt
      M Bsource R certificate I deltaStar hdelta J) : Prop :=
  ∀ (Delta : BankPaperCanonicalExponentBand M → Real),
    J.postHeightBridge.HasTargetEnvelopes (7 * Cinitial) Delta →
    ∀ (markedTarget : Nat → Real) (N : Real),
      0 ≤ N →
      J.postHeightBridge.q ≤ (1 : Real) * N →
      (∀ p ∈ primeBand J.postHeightBridge.sampleData.n
          J.postHeightBridge.sampleData.W,
        abs (markedTarget p -
          J.postHeightBridge.paperMoment
            (J.postHeightBridge.markedValuation p) 0) ≤
          Cinitial * N /
            ((p : Real) * J.postHeightBridge.L)) →
      (∀ j, Delta j =
        J.postHeightBridge.markedBandResidual markedTarget 0 j) →
      ∀ {Fixed : Type} [Fintype Fixed],
        ∀ (fixedValue : Fixed → Nat) (fixedWeight : Fixed → Real)
          (quota : Int),
          (quota : Real) = (∑ f, fixedWeight f) +
            J.postHeightBridge.q →
          J.postHeightBridge.sampleData.HeadPatternsSeparated →
          (∀ x,
            BridgeData.frozenAmbientWeight fixedValue fixedWeight x ∈
              Icc (0 : Real) 1) →
          (∀ m : J.postHeightBridge.sampleData.Sample,
            BridgeData.frozenAmbientWeight fixedValue fixedWeight
                (J.postHeightBridge.sampleData.value m) ≤
              (J.betaProt + S.Cmass / S.density) /
                J.postHeightBridge.L) →
          (∀ m : J.postHeightBridge.sampleData.Sample,
            J.postHeightBridge.baseline.baseWeight m ≤
              (S.Cmass / S.density) / J.postHeightBridge.L) →
          J.postHeightBridge.HasPaperProposition87Conclusion
            Delta radius markedTarget N Cpost
              fixedValue fixedWeight quota

/-- An upstream-only eventual callback for the exact local P87 field.

The premises are the literal source-family synchronizations available from
`BankPaperCanonicalSectionNinePostHeightEventualCoherentBridgeSourceObligation`.
The post-height margin premise is a primitive-gap field.  No conclusion
contract is among the premises. -/
def
    BankPaperCanonicalSectionNinePostHeightSourceFirstSpecializedEventualLocalP87Callback
    {delta eta : Real} (M : RegularRelativeMesh.Mesh delta eta)
    {P : Finset Nat}
    (Patterns : PaperHeadSimplex.Tag P → Pattern)
    (I : PhysicalIntervals)
    (Cprom Cbank : Nat) (G : ∀ n, Ledger n Cprom Cbank)
    {c : Real} (depth W K0 : Nat)
    (deltaStar betaProt betaAct postMarginFloor Cmass density : Real)
    (qMass : Nat → Real)
    (Cinitial : Real) (radius : NNReal) (Cpost : Real)
    (hdelta : 0 < delta) : Prop :=
  ∀ᶠ n : Nat in atTop,
    ∀ (Bsource : BridgeData (PaperHeadSimplex.Tag P)
        (BankPaperCanonicalExponentBand M)),
      Bsource.sampleData.n = n →
      Bsource.sampleData.W = W →
      ∀
        (R : BankPaperRealization Bsource.sampleData.n
          (upperEndpoint Bsource.sampleData.n
            (upperTailLength c Bsource.sampleData.n)))
        (certificate : GuardedCentralAnchorCertificate c depth
          Bsource.sampleData.n R.anchorGuardLeftCore
          R.anchorGuardRightCore (R.centralChangedMarkers depth))
        (J : BankPaperCanonicalSectionNinePostHeightBridgeInputsAt
          (K0 := K0) M Bsource R certificate I deltaStar hdelta)
        (S : BankPaperCanonicalSectionNinePostHeightSourceInputsAt
          M Bsource R certificate I deltaStar hdelta J),
      J.betaProt = betaProt →
      J.betaAct = betaAct →
      ∀
        (hsep :
          physicalBound (I.upper .minus)
              J.postHeightBridge.sampleData.n <
            physicalBound (I.lower .plus)
              J.postHeightBridge.sampleData.n)
        (hremaining :
          ∀ cell : Cell (PaperHeadSimplex.Tag P),
            (rawCell Patterns I J.postHeightBridge.sampleData.n cell \
              (G J.postHeightBridge.sampleData.n).guards).Nonempty),
      J.postHeightBridge.sampleData =
          canonicalSampleData
            (W := J.postHeightBridge.sampleData.W)
            Patterns I (G J.postHeightBridge.sampleData.n)
              hsep hremaining →
      postMarginFloor ≤ J.postHeightTarget.cellMassMargin →
      S.Cmass = Cmass →
      S.density = density →
      J.postHeightBridge.q = qMass n →
      BankPaperCanonicalSectionNinePostHeightSourceFirstSpecializedLocalP87At
        M Cinitial radius Cpost J S



/-! ## Fixed-mesh eventual compositor -/



end BankPaperRealization

end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankPaperCanonicalSectionNinePostHeightSourceFirstPreMeshUniformP87Connector -/
section


/-!
# Pre-mesh uniform Proposition 8.7 callback

The fixed-mesh Proposition 8.7 factory records its choices only after a
particular regular mesh has been introduced.  The underlying uniform theorem
is stronger: after the width, varying active-mass family, source constants,
and selector constant have been fixed, it chooses one radius and one
post-adjustment constant which work for every sufficiently fine permitted
mesh.

This file exposes that dependency order directly.  Its conclusion is the
same specialized eventual callback consumed by the source-first post-height
compositor; it introduces no selector or Post-Hfit conclusion.
-/

open Filter Topology Set
open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.HeadPattern
open Erdos390.Full.PaperBridgeFit
open Erdos390.Full.PaperGuardCensus
open Erdos390.Full.PaperHeadSimplex
open Erdos390.Full.PaperPermittedRegularMesh
open Erdos390.Full.RegularMeshPrimeCutoffs
open Erdos390.Full.RegularRelativeMesh

noncomputable section

namespace BankPaperRealization

/-! ## Pre-mesh uniform adapter -/

/-- Proposition 8.7 in the dependency order required by the final
source-first orchestration.

The tolerance and prime cutoff precede the final width and varying mass
family.  For fixed patterns, source constants, and `Cinitial`, the radius and
`CP87` are then chosen before the eventual callback is specialized to any
particular permitted sufficiently fine mesh. -/
def
    BankPaperCanonicalSectionNinePostHeightSourceFirstPreMeshUniformP87Statement
    (I : PhysicalIntervals)
    (Cprom Cbank : Nat) (G : ∀ n, Ledger n Cprom Cbank) : Prop :=
  (∀ sign, 1 ≤ I.lower sign) →
  (∀ sign, I.upper sign ≤ (2 : Real)) →
  ∃ meshTol : Real, 0 < meshTol ∧
  ∃ W0 : Nat, ∀ W : Nat, W0 ≤ W →
    ∀ (qMass : Nat → Real),
      (∀ᶠ n : Nat in atTop, 1 ≤ qMass n) →
    ∀ {P : Finset Nat}
      (Patterns : PaperHeadSimplex.Tag P → Pattern),
      (∀ h : PaperHeadSimplex.Tag P, ∀ p : Nat,
        p ∈ (Patterns h).primes ↔ p.Prime ∧ p ≤ W) →
    ∀ {c : Real} (depth K0 : Nat)
      (deltaStar betaProt betaAct postMarginFloor Cmass density : Real),
      0 ≤ betaProt →
      0 ≤ Cmass →
      0 < density →
      0 < postMarginFloor →
    ∀ Cinitial : Real, 0 ≤ Cinitial →
      ∃ radius : NNReal, 0 < (radius : Real) ∧
      ∃ CP87 : Real, 0 ≤ CP87 ∧
        ∀ {delta eta : Real} (M : RegularRelativeMesh.Mesh delta eta)
          (hdelta : 0 < delta)
          (_hPermitted : IsPermitted (cMesh := (1 : Real)) M),
          delta + eta ≤ meshTol →
          BankPaperCanonicalSectionNinePostHeightSourceFirstSpecializedEventualLocalP87Callback
            (c := c) M Patterns I Cprom Cbank G depth W K0 deltaStar
              betaProt betaAct postMarginFloor Cmass density qMass
              Cinitial radius CP87 hdelta



end BankPaperRealization

end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankPaperCanonicalSectionNinePostHeightSourceFirstPreMeshSelectorProvider -/
section


/-!
# A placed-selector provider chosen before the final mesh

The placed-selector paper-rate theorem already chooses its uniform constant
before the regular relative mesh.  In the fixed-mesh Post-Hfit compositor,
however, its analytic `d`-bound and final-active-mass lower bound were
specialized only after a mesh had been supplied.

This file packages the same argument in the source-first parameter order.
The Section 8 ledger first selects one nonnegative `Cinitial`.  On one
common tail, and uniformly for every later mesh, the callback consumes only
the literal local source synchronizations, the alpha and beta boxes, the
nonempty correction pool, and exact synchronization of `d` and the fresh
bridge mass with their Section 8 families.  Its conclusion is exactly the
placed-selector deficit estimate; no Post-Hfit or terminal conclusion is
included.
-/

open Filter Topology Set Asymptotics
open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.ArithmeticBandGeometry
open Erdos390.Full.HeadPattern
open Erdos390.Full.PaperBridgeFit
open Erdos390.Full.PaperGuardCensus
open Erdos390.Full.PaperHeadSimplex
open Erdos390.Full.RegularMeshPrimeCutoffs
open Erdos390.Full.RegularRelativeMesh
open Erdos390.Full.Scale

noncomputable section

namespace BankPaperRealization

set_option maxHeartbeats 2400000

/-! ## The literal mesh-uniform callback -/

/-- The exact placed-selector field supplied after `Cinitial` has been
chosen.

The mesh occurs only inside the eventual callback.  The two analytic
premises are equalities with the displayed Section 8 families, rather than
already-proved norm bounds.  The remaining premises are literal local
source, canonical-sample, box, and correction-pool data consumed by the
placed-selector theorem. -/
def
    BankPaperCanonicalSectionNinePostHeightSourceFirstPreMeshPlacedSelectorCallback
    {P : Finset Nat}
    (Patterns : PaperHeadSimplex.Tag P → Pattern)
    (I : PhysicalIntervals)
    (Cprom Cbank : Nat) (G : ∀ n, Ledger n Cprom Cbank)
    {c : Real} (depth W K0 : Nat)
    (deltaStar betaProt betaAct mu : Real)
    (logY Lambda0 mFrozen qTilde : Nat → Real)
    (Cinitial : Real) : Prop :=
  ∀ᶠ n : Nat in atTop,
    ∀ {delta eta : Real}
      (M : RegularRelativeMesh.Mesh delta eta)
      (hdelta : 0 < delta)
      (Bsource : BridgeData (PaperHeadSimplex.Tag P)
        (BankPaperCanonicalExponentBand M)),
      Bsource.sampleData.n = n →
      Bsource.sampleData.W = W →
      ∀
        (R : BankPaperRealization Bsource.sampleData.n
          (upperEndpoint Bsource.sampleData.n
            (upperTailLength c Bsource.sampleData.n)))
        (certificate : GuardedCentralAnchorCertificate c depth
          Bsource.sampleData.n R.anchorGuardLeftCore
          R.anchorGuardRightCore (R.centralChangedMarkers depth))
        (J : BankPaperCanonicalSectionNinePostHeightBridgeInputsAt
          (K0 := K0) M Bsource R certificate I deltaStar hdelta)
        (_S : BankPaperCanonicalSectionNinePostHeightSourceInputsAt
          M Bsource R certificate I deltaStar hdelta J),
      J.betaProt = betaProt →
      J.betaAct = betaAct →
      ∀
        (hsep :
          physicalBound (I.upper .minus)
              J.postHeightBridge.sampleData.n <
            physicalBound (I.lower .plus)
              J.postHeightBridge.sampleData.n)
        (hremaining :
          ∀ cell : Cell (PaperHeadSimplex.Tag P),
            (rawCell Patterns I J.postHeightBridge.sampleData.n cell \
              (G J.postHeightBridge.sampleData.n).guards).Nonempty),
      J.postHeightBridge.sampleData =
          canonicalSampleData
            (W := J.postHeightBridge.sampleData.W)
            Patterns I (G J.postHeightBridge.sampleData.n)
              hsep hremaining →
      J.qTilde =
          bankPaperCanonicalGuardedSmoothBaseMass R certificate
            deltaStar J.postHeightBridge.sampleData.W
              (K0 + 1) J.betaAct →
      (0 ≤ J.alpha ∧ J.alpha ≤ 1) →
      (0 ≤ J.beta / J.postHeightBridge.L ∧
        J.beta / J.postHeightBridge.L ≤ 1) →
      (R.roughCanonicalGuardedBroadCorrectionPool certificate
        deltaStar J.postHeightBridge.sampleData.W
          (K0 + 1) 1).Nonempty →
      (J.d : Real) =
          bankPaperCanonicalSmoothDRealFamily
            mu logY Lambda0 mFrozen qTilde
              Bsource.sampleData.n →
      J.postHeightBridge.q =
          bankPaperCanonicalSmoothFinalActiveMassFamily
            mu logY Lambda0 mFrozen qTilde
              Bsource.sampleData.n →
      ∀ p ∈ primeBand J.postHeightBridge.sampleData.n
          J.postHeightBridge.sampleData.W,
        abs
            (bankPaperCanonicalSelectorValuationDeficit
              R certificate
              (R.paperFixedExceptionalFactors deltaStar)
              (R.roughCanonicalGuardedCandidateSet certificate
                deltaStar (K0 + 1))
              J.placedPreSelector p) ≤
          Cinitial * J.postHeightBridge.q /
            ((p : Real) * J.postHeightBridge.L)

/-! ## Selection from the Section 8 ledger -/



end BankPaperRealization

end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankPaperCanonicalSectionNinePostHeightSourceFirstCrossMeshScalarTransport -/
section


/-!
# Cross-mesh transport of the source-first scalar ledger

The rich source constructor is run after a regular relative mesh has been
chosen, while the Section 8 scalar ledger must be chosen before the final
mesh.  This file records the narrow invariance needed to pass between those
two orders.

Two rich sources made from the same fixed numerical data have, eventually,
the same canonical structured sample.  Their exact rich-to-thin projections
also put both sources on the same realized bank and guarded certificate.
Finally, readiness identifies the barycentric coefficients of both source
targets with the same head target, while the rich projection identifies
their physical mean with the fixed physical target.  Consequently their
scaled active seeds agree.  The frozen mass, precharged logarithm, and
rounded frozen logarithmic mass are therefore independent of which of the
two meshes supplied the bridge partition.

There is no analytic ledger, post-height bridge, downstream contract, or
Section 9 conclusion in this module.
-/

open Filter Topology Set
open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.HeadPattern
open Erdos390.Full.PaperBridgeFit
open Erdos390.Full.PaperGuardCensus
open Erdos390.Full.PaperHeadSimplex
open Erdos390.Full.RegularMeshPrimeCutoffs
open Erdos390.Full.RegularRelativeMesh
open Erdos390.Full.Scale

noncomputable section

namespace BankPaperRealization

/-! ## Reusable rich-source boundary -/

/-- The mesh-dependent geometric fiber returned by the fixed-numerical
rich-source constructor. -/
abbrev
    BankPaperCanonicalSectionNinePostHeightFixedRichFiber
    {delta eta : Real} (M : RegularRelativeMesh.Mesh delta eta)
    (N W : Nat) : Type :=
  let P := primesUpTo W
  let I :=
    bankPaperCanonicalSectionNinePostHeightPhysicalIntervals
  Σ' D : StructuredSampleData (PaperHeadSimplex.Tag P),
  Σ' _hnTail : N ≤ D.n,
  Σ' _hnD : 1 < D.n,
  Σ' _hWD : D.W ≠ 0,
  Σ' _S : ScaleSeparation M D.n D.W,
  Σ' _hlo : (∀ sigma, D.lo sigma =
      physicalBound (I.lower sigma) D.n),
  Σ' _hhi : (∀ sigma, D.hi sigma =
      physicalBound (I.upper sigma) D.n),
    HeadSimplexReserve P

/-- The thin source fiber used by the source-first scalar ledger. -/
abbrev
    BankPaperCanonicalSectionNinePostHeightFixedThinFiber
    {delta eta : Real} (M : RegularRelativeMesh.Mesh delta eta)
    (c : Real) (depth W : Nat) : Type :=
  Σ B : BridgeData
      (PaperHeadSimplex.Tag (primesUpTo W))
      (BankPaperCanonicalExponentBand M),
    BankPaperCanonicalGuardedTailFiber
        c depth B.sampleData.n ×
      BarycentricTarget B.sampleData

/-- The literal rich-to-thin projection used by the fixed-numerical source
constructor, now named so that two mesh instances can be compared. -/
def
    bankPaperCanonicalSectionNinePostHeight_fixedRichThinOfRich
    {delta eta : Real} (M : RegularRelativeMesh.Mesh delta eta)
    {c : Real} {depth N W : Nat}
    (hdelta : 0 < delta)
    (F : BankPaperCanonicalGuardedTailFamily c depth N) :
    BankPaperCanonicalSectionNinePostHeightFixedRichFiber M N W →
      BankPaperCanonicalSectionNinePostHeightFixedThinFiber
        M c depth W := fun Z => by
  let P := primesUpTo W
  let I :=
    bankPaperCanonicalSectionNinePostHeightPhysicalIntervals
  change
    (Σ' D : StructuredSampleData (PaperHeadSimplex.Tag P),
      Σ' _hnTail : N ≤ D.n,
      Σ' _hnD : 1 < D.n,
      Σ' _hWD : D.W ≠ 0,
      Σ' _S : ScaleSeparation M D.n D.W,
      Σ' _hlo : (∀ sigma, D.lo sigma =
          physicalBound (I.lower sigma) D.n),
      Σ' _hhi : (∀ sigma, D.hi sigma =
          physicalBound (I.upper sigma) D.n),
        HeadSimplexReserve P) at Z
  rcases Z with
    ⟨D, hnTail, hnD, hWD, S, hlo, hhi, Rhead⟩
  let Kphysical :=
    bankPaperCanonicalSectionNinePostHeightFixedPhysicalTarget
  have hw : 0 < delta + eta :=
    add_pos hdelta (M.ratio_pos.trans_le M.ratio_le_eta)
  let Tsource :=
    bankPaperCanonicalSectionNineCoherentSourceTarget
      M D I hlo hhi Rhead Kphysical hdelta hnD hWD S hw
  let Bsource :=
    bankPaperCanonicalSectionNineCoherentSourceBridge
      M D I hlo hhi Rhead Kphysical hdelta hnD hWD S hw
  refine ⟨Bsource, ?_⟩
  change
    BankPaperCanonicalGuardedTailFiber c depth D.n ×
      BarycentricTarget D
  exact
    ⟨⟨F.realization D.n hnTail, F.certificate D.n hnTail⟩,
      Tsource⟩

/-- A fixed-numerical rich source together with exactly the four facts
exported by its constructor.  Naming this boundary avoids repeating the
large dependent source type in every cross-mesh statement. -/
structure
    BankPaperCanonicalSectionNinePostHeightFixedRichSourceWitness
    {delta eta : Real} (M : RegularRelativeMesh.Mesh delta eta)
    {c deltaStar betaProt betaAct sourceCellMargin : Real}
    {depth N W K0 E : Nat}
    (hdelta : 0 < delta)
    (F : BankPaperCanonicalGuardedTailFamily c depth N) where
  sourceGeom :
    ∀ n, N ≤ n →
      BankPaperCanonicalSectionNinePostHeightFixedRichFiber M N W
  source :
    ∀ n, N ≤ n →
      BankPaperCanonicalSectionNinePostHeightFixedThinFiber
        M c depth W
  projection :
    ∀ n hn,
      source n hn =
        bankPaperCanonicalSectionNinePostHeight_fixedRichThinOfRich
          M hdelta F (sourceGeom n hn)
  source_event :
    ∀ᶠ n : Nat in atTop,
      ∀ hn : N ≤ n,
        let X := source n hn
        let B := X.1
        let R := X.2.1.1
        let certificate := X.2.1.2
        let T := X.2.2
        let alpha :=
          bankPaperCanonicalPostHfitBalancedAlpha
            B c K0 betaProt betaAct
        let qTilde :=
          F.extendedGuardedSmoothBaseMass
            W (K0 + 1) betaAct deltaStar n
        B.sampleData.n = n ∧
          B.sampleData.W = W ∧
          qTilde =
            bankPaperCanonicalGuardedSmoothBaseMass
              R certificate deltaStar B.sampleData.W
                (K0 + 1) betaAct ∧
          1 ≤ qTilde ∧
          B.sampleData.HeadPatternsSeparated ∧
          bankPaperCanonicalStructuredActiveValues B.sampleData ⊆
            R.roughCanonicalGuardedRow
              certificate deltaStar (K0 + 1) 1 ∧
          (0 ≤ alpha ∧ alpha ≤ 1) ∧
          (0 ≤ betaProt / B.L ∧ betaProt / B.L ≤ 1) ∧
          BankPaperCanonicalTopFrozenRoundedSourceResidualInputsAt
            (K := K0 + 1) B R certificate
            (R.paperFixedExceptionalFactors deltaStar)
            T deltaStar betaProt alpha
              (betaProt + betaAct) qTilde ∧
          certificate.prechargedTailTarget =
            (F.certificate n hn).prechargedTailTarget
  ready_event :
    ∀ᶠ n : Nat in atTop,
      ∀ hn : N ≤ n,
        let X := source n hn
        let B := X.1
        let R := X.2.1.1
        let certificate := X.2.1.2
        let T := X.2.2
        let target :
            {p : Nat // p ∈ primesUpTo W} → Real :=
          fun p =>
            ((certificate.selectorTailTarget R
              (R.paperFixedExceptionalFactors
                deltaStar)).factorization p.1 : Real)
        B.sampleData.n = n ∧
          (∀ p : {p : Nat // p ∈ primesUpTo W},
            bankPaperCanonicalSectionNinePostHeightHeadLinearFloor c W *
                  secondOrderScale n ≤
                target p ∧
              target p ≤
                bankPaperCanonicalSectionNinePostHeightHeadUpperCoefficient
                    c p.1 *
                  secondOrderScale n) ∧
          ∃ _hWB : B.sampleData.W ≠ 0,
          ∃ _S : ScaleSeparation
              M B.sampleData.n B.sampleData.W,
          ∃ hlo : ∀ sigma, B.sampleData.lo sigma =
              physicalBound
                (bankPaperCanonicalSectionNinePostHeightPhysicalIntervals.lower
                  sigma)
                B.sampleData.n,
          ∃ hhi : ∀ sigma, B.sampleData.hi sigma =
              physicalBound
                (bankPaperCanonicalSectionNinePostHeightPhysicalIntervals.upper
                  sigma)
                B.sampleData.n,
          ∃ Rhead : HeadSimplexReserve (primesUpTo W),
          ∃ Kphysical : PhysicalInterpolationTarget
              bankPaperCanonicalSectionNinePostHeightPhysicalIntervals,
            Rhead.exponent = E ∧
              (∀ p, Rhead.target p = target p) ∧
              F.extendedGuardedSmoothBaseMass
                  W (K0 + 1) betaAct deltaStar n =
                Rhead.activeMass ∧
              sourceCellMargin ≤ T.cellMassMargin ∧
              T =
                B.barycentricTargetOfPaperData
                  bankPaperCanonicalSectionNinePostHeightPhysicalIntervals
                  hlo hhi Rhead Kphysical
  canonical_event :
    ∀ᶠ n : Nat in atTop,
      ∀ hn : N ≤ n,
        let X := source n hn
        let B := X.1
        let R := X.2.1.1
        let certificate := X.2.1.2
        ∃ hsep :
            physicalBound
                (bankPaperCanonicalSectionNinePostHeightPhysicalIntervals.upper
                  .minus) n <
              physicalBound
                (bankPaperCanonicalSectionNinePostHeightPhysicalIntervals.lower
                  .plus) n,
        ∃ hremaining :
            ∀ cell :
                Cell (PaperHeadSimplex.Tag (primesUpTo W)),
              (rawCell
                    (PaperHeadSimplex.pattern (primesUpTo W)
                      (bankPaperCanonicalSectionNinePostHeight_primesUpTo_prime
                        W) E)
                    bankPaperCanonicalSectionNinePostHeightPhysicalIntervals
                    n cell \
                  (roughCanonicalBridgeRelevantLedgerFamily depth n).guards
                ).Nonempty,
          B.sampleData =
              canonicalSampleData
                (W := W)
                (PaperHeadSimplex.pattern (primesUpTo W)
                  (bankPaperCanonicalSectionNinePostHeight_primesUpTo_prime W)
                  E)
                bankPaperCanonicalSectionNinePostHeightPhysicalIntervals
                (roughCanonicalBridgeRelevantLedgerFamily depth n)
                hsep hremaining ∧
            BankPaperCanonicalBridgeGuardAgreement
              (roughCanonicalBridgeRelevantLedgerFamily depth
                B.sampleData.n)
              R certificate deltaStar

/-! ## Finite invariance helpers -/







/-! ## Eventual transport between two fixed-rich sources -/



end BankPaperRealization

end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankPaperCanonicalSectionNineTopFrozenSynchronizedAnalyticCompletionConnector -/
section


/-!
# Synchronized analytic completion for the frozen-top Section 9 source

The public frozen-top event step already turns an eventual synchronized
Post-Hfit input into the distributed Section 9 terminal.  This file supplies
the parameter-synchronization layer parallel to
`BankPaperCanonicalSectionNineSynchronizedAnalyticCompletion`.

The completion callback receives the actual combined-charge terminal selected
at the common capacity depth.  It then supplies the mesh, bridge family,
numerical data, actual bridge-mass bound, and frozen-top synchronized input.
No local source package, analytic ledger, or post-height construction is
postulated by this connector.
-/

open Filter

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.PaperBridgeFit
open Erdos390.Full.PaperGuardCensus
open Erdos390.Full.PrimeBandQuadrature
open Erdos390.Full.RegularMeshPrimeCutoffs
open Erdos390.Full.RegularRelativeMesh

noncomputable section

/-! ## Frozen-top residual analytic completion -/

/-- The analytic data which augment one already selected combined-charge
terminal and feed the public frozen-top Section 9 event step.

The depth, width, tangent exponent, and combined tangent parameter are fixed
before this package is requested.  The eventual Post-Hfit input retains the
same bridge family and uses the fixed ratio `21 / 20` required by the
parameter-synchronization theorem below. -/
def BankPaperCanonicalSectionNineTopFrozenSynchronizedAnalyticCompletion
    (c : Real) (depth W : Nat) (r0 deltaStar : Real) : Prop :=
  ∃ delta eta : Real,
    ∃ M : RegularRelativeMesh.Mesh delta eta,
      ∃ P : Finset Nat,
        ∃ B : Nat → BridgeData (PaperHeadSimplex.Tag P)
            (BankPaperCanonicalExponentBand M),
          ∃ K0 : Nat,
            ∃ tangentConstant sigma Cpost Cq : Real,
              ∃ hdelta : 0 < delta,
                0 < tangentConstant ∧
                  0 < sigma ∧
                  delta + M.ratio ≤
                    bankPaperCanonicalRatioCellPaperWidthChoice
                      (tangentPaperCleanListDensity W r0)
                      sigma (21 / 20 : Real) tangentConstant ∧
                  0 ≤ Cpost ∧
                  (2 / 9 : Real) * Cpost * Cq ≤ tangentConstant ∧
                  (∀ᶠ n : Nat in atTop,
                    (B n).sampleData.n = n ∧
                      (B n).sampleData.W = W) ∧
                  (∀ᶠ n : Nat in atTop,
                    (B n).q ≤ Cq * secondOrderScale n) ∧
                  BankPaperCanonicalSectionNineTopFrozenSynchronizedPostHfitInput
                    M B c depth K0 deltaStar (21 / 20 : Real)
                      sigma Cpost hdelta

/-! ## Parameter-synchronized distributed terminal -/



end

end Erdos390.WholePaper

end


