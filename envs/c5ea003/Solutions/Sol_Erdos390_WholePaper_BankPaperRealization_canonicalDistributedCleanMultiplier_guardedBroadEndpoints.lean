-- Prove2me | solution 1 for Erdos390.WholePaper.BankPaperRealization.canonicalDistributedCleanMultiplier_guardedBroadEndpoints
-- status  : ACCEPTED   (prove)
-- author  : @doctosil
-- created : 2026-09-17T15:53:56.232004+00:00
-- url     : https://prove2.me/submissions/c9cab1c2-0d1c-4a44-91fb-fb7d04326290

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

/- Source module: Erdos390.WholePaper.FixedModulusReducedResidueCount -/
section


/-!
# Fixed-modulus reduced-residue counts

This file proves the elementary `O_W(1)` input used in the rough selector
and in the tangent-list census.  A reduced-residue predicate is counted on
literal finite intervals by splitting the interval into complete periods
and one remainder.  Multiples of a number coprime to the fixed modulus are
then reindexed exactly by division.

There is no prime-number theorem, smooth-number estimate, or asymptotic
hypothesis in this module.  The final CRT-style error constant is the
explicit number `M + 1`, independent of the multiplier and the interval.
-/

namespace Erdos390.WholePaper

noncomputable section









/-! ## Exact periodic decomposition -/

















/-! ## Explicit fixed-period error -/







/-! ## Exact CRT reindexing and multiplier-independent error -/







/-! ## Paper-head specializations -/





/-- A prime strictly above the cutoff is coprime to the product of every
head prime at or below the cutoff. -/
theorem prime_coprime_roughHeadModulus_of_cutoff_lt
    {W p : ℕ} (hp : p.Prime) (hWp : W < p) :
    Nat.Coprime p (roughHeadModulus W) := by
  rw [roughHeadModulus, Nat.coprime_prod_right_iff]
  intro q hq
  have hqData := mem_primesUpTo.mp hq
  exact (Nat.coprime_primes hp hqData.1).mpr (by omega)



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

/-- Membership in `I_uv`, together with `0<v≤u`, puts both numerical
endpoints in the broad interval `(n,2n-Kh]`. -/
theorem tangentCommonMultiplierInterval_endpoints
    {n K h u v a : ℕ}
    (hu : 0 < u) (hv : 0 < v) (hvu : v ≤ u)
    (ha : a ∈ tangentCommonMultiplierInterval n K h u v) :
    u * a ∈ Finset.Ioc n (tangentBroadUpper n K h) ∧
      v * a ∈ Finset.Ioc n (tangentBroadUpper n K h) := by
  have haBounds := mem_tangentCommonMultiplierInterval.mp ha
  have hvLower : n < v * a := by
    have h := (Nat.div_lt_iff_lt_mul hv).mp haBounds.1
    simpa only [Nat.mul_comm] using h
  have huLower : n < u * a := by
    exact hvLower.trans_le (Nat.mul_le_mul_right a hvu)
  have huUpper : u * a ≤ tangentBroadUpper n K h := by
    have h := (Nat.le_div_iff_mul_le hu).mp haBounds.2
    simpa only [Nat.mul_comm] using h
  have hvUpper : v * a ≤ tangentBroadUpper n K h :=
    (Nat.mul_le_mul_right a hvu).trans huUpper
  exact ⟨Finset.mem_Ioc.mpr ⟨huLower, huUpper⟩,
    Finset.mem_Ioc.mpr ⟨hvLower, hvUpper⟩⟩

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











/-! ## Instantiation of the star split-request boundary -/





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

/- Source module: Erdos390.WholePaper.TangentPaperCleanListAbsorption -/
section


/-!
# Closing the paper-scale tangent clean-list inequality

This file fixes the moving parameters used in Section 9 of the paper:

* `h = upperTailLength c n = ceil(c n / log n)`;
* `Phead = roughHeadModulus W`;
* `X0 = ceil(n ^ deltaStar)`;
* `y = yNat n = floor(n ^ (2/9))`;
* `W < v <= u <= y` and `u / v <= r0 < 3/2`.

For fixed `W`, `K`, `c`, `r0`, and `deltaStar`, the head-density gap is

`roughHeadDensity W * (2 - r0)`.

We reserve one sixteenth of that gap as the effective list density.  A
slightly conservative explicit version of the paper's one-time cutoff makes
the canonical Selberg main term at most one quarter of the gap.  The
Lambda-squared endpoint remainder and the sharp bank deletion census are
then `o(n/u)`, uniformly for `u <= yNat n`.  The fixed-modulus endpoint loss,
the natural floors and ceilings, and `K*h` are absorbed at the same scale.

Consequently the final candidate-floor-versus-loss inequality is proved
eventually; it is not retained as a premise of the paper-facing wrapper.
-/

open Filter Topology Asymptotics
open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel
open Erdos390.Full.Scale

noncomputable section

/-! ## Literal Section 9 parameters -/











/-- The natural ceiling dominates the literal real exceptional cutoff. -/
theorem tangentPaperExceptionalCutoff_cast_ge
    (deltaStar : ℝ) (n : ℕ) :
    (n : ℝ) ^ deltaStar ≤
      (tangentPaperExceptionalCutoff deltaStar n : ℝ) := by
  unfold tangentPaperExceptionalCutoff
  exact Nat.le_ceil _



/-- Passing the safe integral cutoff test implies the literal real
Section 9 test `2n/R_y(a) >= n^deltaStar`. -/
theorem tangentPaperExceptionalCutoff_le_roughScale_implies_real
    {deltaStar : ℝ} {n y a : ℕ}
    (hscale : tangentPaperExceptionalCutoff deltaStar n ≤
      tangentRoughScale n y a) :
    (n : ℝ) ^ deltaStar ≤
      2 * (n : ℝ) / (completeRoughLabel y a : ℝ) := by
  have hscaleCast :
      (tangentPaperExceptionalCutoff deltaStar n : ℝ) ≤
        (tangentRoughScale n y a : ℝ) := by
    exact_mod_cast hscale
  calc
    (n : ℝ) ^ deltaStar ≤
        (tangentPaperExceptionalCutoff deltaStar n : ℝ) :=
      tangentPaperExceptionalCutoff_cast_ge deltaStar n
    _ ≤ (tangentRoughScale n y a : ℝ) := hscaleCast
    _ ≤ ((2 * n : ℕ) : ℝ) / (completeRoughLabel y a : ℝ) := by
      unfold tangentRoughScale
      exact Nat.cast_div_le
    _ = 2 * (n : ℝ) / (completeRoughLabel y a : ℝ) := by
      push_cast
      ring





/-! ## The harmonic main term -/





/-! ## Moving-scale negligibility -/





/-! ## Eventual exceptional-loss absorption -/





/-! ## The fixed-head candidate at the paper endpoints -/





/-! ## The literal candidate floor absorbs every canonical loss -/



/-! ## Paper-facing clean-list theorem with no arithmetic loss premise -/

namespace BankPaperRealization



end BankPaperRealization

end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankPaperCanonicalTangentSlackIntegration -/
section


/-!
# Canonical parameter and endpoint-slack integration for Section 9

This module closes two finite interfaces which occur immediately before the
distributed tangent.

First, it makes one literal choice of `deltaStar` which simultaneously obeys
the complete fixed-factor/precharge budget and the clean-list head-gap
inequality.  Thus the charge terminal and the clean-list theorem no longer
need independently chosen exceptional exponents.

Second, it proves all of the endpoint classification and slack algebra.  A
clean common multiplier puts both endpoints in the guarded broad pool of one
complete rough row, and a nonsmooth such row is active nonexceptional.  On a
nonsmooth row, the displayed absolute bound for the constant correction
density implies the required two-sided selector margin.  On the smooth row,
the protected floor and active ceiling imply the same margin by elementary
addition.

The only construction fact not present in the preceding development is kept
as the explicit proposition
`BankPaperCanonicalGuardedEndpointSlackConstruction`: the actual guarded
selector must agree with the constant broad-row correction off the smooth row,
and its smooth coordinates must have the protected-plus-active decomposition.
No traffic, collision, clean-list cardinality, or final tangent conclusion is
included in that proposition.  The last theorem packages its consequence in
exactly the endpoint-closure and endpoint-slack shape consumed by the
candidate-parametric distributed assembly.
-/

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel
open Erdos390.Full.Scale
open Filter Topology

noncomputable section

/-! ## One exceptional exponent for the charge and tangent arguments -/













namespace BankPaperRealization

/-! ## The explicit guarded nonsmooth correction -/









/-! ## Clean endpoints lie in the appropriate guarded broad pool -/

/-- Every canonical clean common multiplier puts both numerical endpoints in
the guarded broad correction pool of the multiplier's complete rough row.
If that row is nonsmooth, the integral cutoff test also proves that it is an
active nonexceptional row in the paper's real sense. -/
theorem canonicalDistributedCleanMultiplier_guardedBroadEndpoints
    {c : Real} {depth n W K : Nat}
    (R : BankPaperRealization n
      (upperEndpoint n (upperTailLength c n)))
    (certificate : GuardedCentralAnchorCertificate c depth n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (deltaStar : Real)
    {flow : BankPaperCanonicalTangentPrime n W ->
      BankPaperCanonicalTangentPrime n W -> Real}
    {L sigma : Real}
    (request : BankPaperCanonicalDistributedTangentSplitRequest
      flow L sigma) {common : Nat}
    (hcommon : common ∈
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
          (R.paperFixedExceptionalFactors deltaStar)) request) :
    (bankPaperCanonicalDistributedTangentRequestSource request * common ∈
          R.roughCanonicalGuardedBroadCorrectionPool certificate deltaStar
            W K (completeRoughLabel (yNat n) common) ∧
      bankPaperCanonicalDistributedTangentRequestTarget request * common ∈
          R.roughCanonicalGuardedBroadCorrectionPool certificate deltaStar
            W K (completeRoughLabel (yNat n) common)) ∧
      (completeRoughLabel (yNat n) common ≠ 1 ->
        RoughCanonicalActiveNonexceptionalLabel n deltaStar
          (completeRoughLabel (yNat n) common)) := by
  let s := bankPaperCanonicalDistributedTangentRequestSource request
  let t := bankPaperCanonicalDistributedTangentRequestTarget request
  let label := completeRoughLabel (yNat n) common
  have hsPrime : s.Prime := by
    simpa only [s, bankPaperCanonicalDistributedTangentRequestSource,
      tangentSplitRequestSource, tangentSplitRequestEdge,
      tangentStarEdgeSource] using
      bankPaperCanonicalTangentPrimeLabel_prime request.1.1.1
  have htPrime : t.Prime := by
    simpa only [t, bankPaperCanonicalDistributedTangentRequestTarget,
      tangentSplitRequestTarget, tangentSplitRequestEdge,
      tangentStarEdgeTarget] using
      bankPaperCanonicalTangentPrimeLabel_prime request.1.1.2
  have hWs : W < s := by
    simpa only [s, bankPaperCanonicalDistributedTangentRequestSource,
      tangentSplitRequestSource, tangentSplitRequestEdge,
      tangentStarEdgeSource] using
      cutoff_lt_of_mem_primeBand request.1.1.1.2
  have hWt : W < t := by
    simpa only [t, bankPaperCanonicalDistributedTangentRequestTarget,
      tangentSplitRequestTarget, tangentSplitRequestEdge,
      tangentStarEdgeTarget] using
      cutoff_lt_of_mem_primeBand request.1.1.2.2
  have hsLe : s ≤ yNat n := by
    simpa only [s, bankPaperCanonicalDistributedTangentRequestSource,
      tangentSplitRequestSource, tangentSplitRequestEdge,
      tangentStarEdgeSource] using
      le_yNat_of_mem_primeBand request.1.1.1.2
  have htLe : t ≤ yNat n := by
    simpa only [t, bankPaperCanonicalDistributedTangentRequestTarget,
      tangentSplitRequestTarget, tangentSplitRequestEdge,
      tangentStarEdgeTarget] using
      le_yNat_of_mem_primeBand request.1.1.2.2
  have hclean : common ∈ tangentCleanCommonMultiplierList n K
      (upperTailLength c n) (roughHeadModulus W)
      (tangentPaperExceptionalCutoff deltaStar n) (yNat n)
      (max s t) (min s t) R.tangentPaperDedicatedRows
      (R.tangentPaperNumericalGuardSet certificate
        (R.paperFixedExceptionalFactors deltaStar)) := by
    simpa only [tangentSplitCleanMultiplierLists,
      tangentCleanMultiplierLists, s, t] using hcommon
  have hdata := mem_tangentCleanCommonMultiplierList.mp hclean
  have hcommonPos : 0 < common :=
    tangentSplitCleanMultiplier_pos request hcommon
  have hinterval : common ∈ tangentCommonMultiplierInterval n K
      (upperTailLength c n) (max s t) (min s t) :=
    mem_tangentCommonMultiplierInterval.mpr hdata.1
  have hmaxPos : 0 < max s t := hsPrime.pos.trans_le (le_max_left _ _)
  have hminPos : 0 < min s t := lt_min hsPrime.pos htPrime.pos
  have hendpoints := tangentCommonMultiplierInterval_endpoints
    hmaxPos hminPos min_le_max hinterval
  have hsBroad : s * common ∈
      roughBroadLowerBlock n (upperTailLength c n) K := by
    rcases le_total s t with hst | hts
    · simpa only [roughBroadLowerBlock, tangentBroadUpper,
        min_eq_left hst] using hendpoints.2
    · simpa only [roughBroadLowerBlock, tangentBroadUpper,
        max_eq_left hts] using hendpoints.1
  have htBroad : t * common ∈
      roughBroadLowerBlock n (upperTailLength c n) K := by
    rcases le_total s t with hst | hts
    · simpa only [roughBroadLowerBlock, tangentBroadUpper,
        max_eq_right hst] using hendpoints.1
    · simpa only [roughBroadLowerBlock, tangentBroadUpper,
        min_eq_right hts] using hendpoints.2
  have hmaxNot : max s t * common ∉
      R.tangentPaperNumericalGuardSet certificate
        (R.paperFixedExceptionalFactors deltaStar) :=
    hdata.2.2.2.2.1
  have hminNot : min s t * common ∉
      R.tangentPaperNumericalGuardSet certificate
        (R.paperFixedExceptionalFactors deltaStar) :=
    hdata.2.2.2.2.2
  have hsNot : s * common ∉
      R.tangentPaperNumericalGuardSet certificate
        (R.paperFixedExceptionalFactors deltaStar) := by
    rcases le_total s t with hst | hts
    · simpa only [min_eq_left hst] using hminNot
    · simpa only [max_eq_left hts] using hmaxNot
  have htNot : t * common ∉
      R.tangentPaperNumericalGuardSet certificate
        (R.paperFixedExceptionalFactors deltaStar) := by
    rcases le_total s t with hst | hts
    · simpa only [max_eq_right hst] using hmaxNot
    · simpa only [min_eq_right hts] using hminNot
  have hsHead : Nat.Coprime (s * common) (roughHeadModulus W) :=
    (prime_coprime_roughHeadModulus_of_cutoff_lt hsPrime hWs).mul_left
      hdata.2.1
  have htHead : Nat.Coprime (t * common) (roughHeadModulus W) :=
    (prime_coprime_roughHeadModulus_of_cutoff_lt htPrime hWt).mul_left
      hdata.2.1
  have hsLabel : completeRoughLabel (yNat n) (s * common) = label := by
    exact completeRoughLabel_small_left_mul hsPrime.pos hsLe hcommonPos
  have htLabel : completeRoughLabel (yNat n) (t * common) = label := by
    exact completeRoughLabel_small_left_mul htPrime.pos htLe hcommonPos
  have hsPool : s * common ∈
      R.roughCanonicalGuardedBroadCorrectionPool certificate deltaStar
        W K label := by
    change s * common ∈
      completeRoughRowFiber (yNat n)
          (roughHeadFree W
            (roughBroadLowerBlock n (upperTailLength c n) K)) label \
        R.roughCanonicalGuardSet certificate deltaStar
    apply Finset.mem_sdiff.mpr
    constructor
    · apply mem_completeRoughRowFiber.mpr
      exact ⟨mem_roughHeadFree.mpr ⟨hsBroad, hsHead⟩, hsLabel⟩
    · simpa only [roughCanonicalGuardSet] using hsNot
  have htPool : t * common ∈
      R.roughCanonicalGuardedBroadCorrectionPool certificate deltaStar
        W K label := by
    change t * common ∈
      completeRoughRowFiber (yNat n)
          (roughHeadFree W
            (roughBroadLowerBlock n (upperTailLength c n) K)) label \
        R.roughCanonicalGuardSet certificate deltaStar
    apply Finset.mem_sdiff.mpr
    constructor
    · apply mem_completeRoughRowFiber.mpr
      exact ⟨mem_roughHeadFree.mpr ⟨htBroad, htHead⟩, htLabel⟩
    · simpa only [roughCanonicalGuardSet] using htNot
  have hactive : label ≠ 1 ->
      RoughCanonicalActiveNonexceptionalLabel n deltaStar label := by
    intro hlabel
    exact ⟨hlabel,
      tangentPaperExceptionalCutoff_le_roughScale_implies_real hdata.2.2.1⟩
  simpa only [s, t, label] using ⟨⟨hsPool, htPool⟩, hactive⟩

/-! ## The isolated protected/corrected-selector construction output -/





/-! ## Adapter to the candidate-parametric distributed tangent -/





end BankPaperRealization

end

end Erdos390.WholePaper

end

theorem solution :
∀ {c : Real} {depth n W K : Nat}
  (R :
    Erdos390.WholePaper.BankPaperRealization n
      (Erdos390.WholePaper.upperEndpoint n (Erdos390.WholePaper.upperTailLength c n)))
  (certificate :
    Erdos390.WholePaper.GuardedCentralAnchorCertificate c depth n
      (Erdos390.WholePaper.BankPaperRealization.anchorGuardLeftCore R)
      (Erdos390.WholePaper.BankPaperRealization.anchorGuardRightCore R)
      (Erdos390.WholePaper.BankPaperRealization.centralChangedMarkers R depth))
  (deltaStar : Real)
  {flow :
    Erdos390.WholePaper.BankPaperCanonicalTangentPrime n W →
      Erdos390.WholePaper.BankPaperCanonicalTangentPrime n W → Real}
  {L sigma : Real} (request : Erdos390.WholePaper.BankPaperCanonicalDistributedTangentSplitRequest flow L sigma)
  {common : Nat},
  Membership.mem.{0, 0}
      (Erdos390.WholePaper.tangentSplitCleanMultiplierLists.{0} (Erdos390.WholePaper.tangentPositiveFlowEdges.{0} flow)
        (Erdos390.WholePaper.tangentStarEdgeSource.{0} Erdos390.WholePaper.bankPaperCanonicalTangentPrimeLabel)
        (Erdos390.WholePaper.tangentStarEdgeTarget.{0} Erdos390.WholePaper.bankPaperCanonicalTangentPrimeLabel) L sigma
        (fun edge => flow edge.1 edge.2) n K (Erdos390.WholePaper.upperTailLength c n)
        (Erdos390.WholePaper.roughHeadModulus W) (Erdos390.WholePaper.tangentPaperExceptionalCutoff deltaStar n)
        (Erdos390.Full.ArithmeticModel.yNat n) (Erdos390.WholePaper.BankPaperRealization.tangentPaperDedicatedRows R)
        (Erdos390.WholePaper.BankPaperRealization.tangentPaperNumericalGuardSet R certificate
          (Erdos390.WholePaper.BankPaperRealization.paperFixedExceptionalFactors R deltaStar))
        request)
      common →
    And
      (And
        (Membership.mem.{0, 0}
          (Erdos390.WholePaper.BankPaperRealization.roughCanonicalGuardedBroadCorrectionPool R certificate deltaStar W K
            (Erdos390.WholePaper.completeRoughLabel (Erdos390.Full.ArithmeticModel.yNat n) common))
          (HMul.hMul.{0, 0, 0} (Erdos390.WholePaper.bankPaperCanonicalDistributedTangentRequestSource request) common))
        (Membership.mem.{0, 0}
          (Erdos390.WholePaper.BankPaperRealization.roughCanonicalGuardedBroadCorrectionPool R certificate deltaStar W K
            (Erdos390.WholePaper.completeRoughLabel (Erdos390.Full.ArithmeticModel.yNat n) common))
          (HMul.hMul.{0, 0, 0} (Erdos390.WholePaper.bankPaperCanonicalDistributedTangentRequestTarget request) common)))
      (Ne.{1} (Erdos390.WholePaper.completeRoughLabel (Erdos390.Full.ArithmeticModel.yNat n) common) (1 : Nat) →
        Erdos390.WholePaper.BankPaperRealization.RoughCanonicalActiveNonexceptionalLabel n deltaStar
          (Erdos390.WholePaper.completeRoughLabel (Erdos390.Full.ArithmeticModel.yNat n) common)) := by
  exact @Erdos390.WholePaper.BankPaperRealization.canonicalDistributedCleanMultiplier_guardedBroadEndpoints
