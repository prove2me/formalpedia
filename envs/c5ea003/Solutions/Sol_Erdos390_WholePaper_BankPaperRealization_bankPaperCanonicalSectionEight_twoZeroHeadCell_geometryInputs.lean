-- Prove2me | solution 1 for Erdos390.WholePaper.BankPaperRealization.bankPaperCanonicalSectionEight_twoZeroHeadCell_geometryInputs
-- status  : ACCEPTED   (prove)
-- author  : @doctosil
-- created : 2026-09-17T16:19:17.545491+00:00
-- url     : https://prove2.me/submissions/a3ebc798-dc03-484d-832b-e48b4648caa6

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

/- Source module: Erdos390.WholePaper.RoughHeadCompatibleFinitePoint -/
section


/-!
# The literal head-compatible finite raw point

This file constructs the first finite point in the guarded rough selector.
The upper block `E`, the high lower block `H`, and the broad lower block `J`
are literal natural-number half-open intervals.  Head freedom is imposed by
coprimality with the product of all primes up to `W`, and the raw weight is
defined pointwise from those finite sets.

The second half proves the exact deterministic identities used before any
HT--Saias or prime-number estimate: finite Möbius inclusion--exclusion,
reindexing of smooth multiples by division, and the resulting physical-block
shift through every divisor of the head modulus.
-/

open scoped BigOperators ArithmeticFunction.Moebius

namespace Erdos390.WholePaper

open Erdos390.Full.HeadPattern
open Erdos390.Full.StructuredCells

noncomputable section

/-! ## Literal physical intervals -/











/-- Under the paper's interval-size condition, the two raw blocks exhaust
the whole lower interval `(n,2n]`. -/
theorem roughRawCandidateSet_eq_Ioc
    {n h K : ℕ} (hKh : K * h ≤ n) :
    roughRawCandidateSet n h K = Finset.Ioc n (2 * n) := by
  ext a
  simp only [roughRawCandidateSet, roughHighLowerBlock,
    roughBroadLowerBlock, Finset.mem_union, Finset.mem_Ioc]
  omega









/-! ## The finite head and raw weights -/

















































/-! ## Exact head inclusion--exclusion and smooth physical shifts -/

















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

/-- A complete rough label is always positive, including for `a = 0`, when
the empty factorization gives label `1`. -/
theorem completeRoughLabel_pos (y a : ℕ) :
    0 < completeRoughLabel y a := by
  rw [completeRoughLabel]
  apply Nat.prod_pow_pos_of_zero_notMem_support
  rw [Finsupp.notMem_support_iff, completeRoughSignature_apply]
  simp

theorem completeRoughLabel_ne_zero (y a : ℕ) :
    completeRoughLabel y a ≠ 0 :=
  (completeRoughLabel_pos y a).ne'

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

/-- The retained high-prime product is a literal divisor of the original
number. -/
theorem completeRoughLabel_dvd (y a : ℕ) :
    completeRoughLabel y a ∣ a := by
  by_cases ha : a = 0
  · rw [ha]
    exact dvd_zero _
  · rw [← Nat.factorization_le_iff_dvd
      (completeRoughLabel_ne_zero y a) ha,
      completeRoughLabel_factorization_eq_filter_gt]
    intro p
    rw [Finsupp.filter_apply]
    split_ifs <;> simp

/-- The requested multiplication direction: the original number is the
rough label times its literal complementary quotient. -/
theorem completeRough_decomposition (y a : ℕ) :
    a = completeRoughLabel y a * completeSmoothPart y a := by
  calc
    a = a / completeRoughLabel y a * completeRoughLabel y a :=
      (Nat.div_mul_cancel (completeRoughLabel_dvd y a)).symm
    _ = completeRoughLabel y a * (a / completeRoughLabel y a) :=
      Nat.mul_comm _ _
    _ = completeRoughLabel y a * completeSmoothPart y a := rfl



/-! ## The complementary low-prime factorization -/

/-- The quotient retains exactly the complementary coordinates `p ≤ y`. -/
theorem completeSmoothPart_factorization_eq_filter_le (y a : ℕ) :
    (completeSmoothPart y a).factorization =
      a.factorization.filter (fun p ↦ p ≤ y) := by
  rw [completeSmoothPart,
    Nat.factorization_div (completeRoughLabel_dvd y a),
    completeRoughLabel_factorization_eq_filter_gt]
  ext p
  simp only [Finsupp.filter_apply]
  by_cases hpLow : p ≤ y
  · have hpNotHigh : ¬y < p := Nat.not_lt_of_ge hpLow
    simp [hpLow, hpNotHigh]
  · have hpHigh : y < p := Nat.lt_of_not_ge hpLow
    simp [hpLow, hpHigh]

/-- Coordinate form of the exact low-prime factorization. -/
theorem completeSmoothPart_factorization_apply (y a p : ℕ) :
    (completeSmoothPart y a).factorization p =
      if p ≤ y then a.factorization p else 0 := by
  have h := congrArg (fun f : ℕ →₀ ℕ ↦ f p)
    (completeSmoothPart_factorization_eq_filter_le y a)
  simpa only [Finsupp.filter_apply] using h

/-- Nonzero high-part coordinates lie strictly above the cutoff. -/
theorem completeRoughLabel_factorization_support
    {y a p : ℕ}
    (hp : (completeRoughLabel y a).factorization p ≠ 0) :
    y < p := by
  rw [completeRoughLabel_factorization_apply] at hp
  by_contra hpHigh
  simp [hpHigh] at hp

/-- Nonzero smooth-part coordinates lie weakly below the cutoff. -/
theorem completeSmoothPart_factorization_support
    {y a p : ℕ}
    (hp : (completeSmoothPart y a).factorization p ≠ 0) :
    p ≤ y := by
  rw [completeSmoothPart_factorization_apply] at hp
  by_contra hpLow
  simp [hpLow] at hp

/-- Every prime divisor of the complete rough label is above `y`. -/
theorem prime_dvd_completeRoughLabel_gt
    {y a p : ℕ} (hp : p.Prime)
    (hpDvd : p ∣ completeRoughLabel y a) :
    y < p := by
  have hfactorPos := hp.factorization_pos_of_dvd
    (completeRoughLabel_ne_zero y a) hpDvd
  exact completeRoughLabel_factorization_support hfactorPos.ne'

/-- For a positive original number, the complementary quotient is positive. -/
theorem completeSmoothPart_pos {y a : ℕ} (ha : 0 < a) :
    0 < completeSmoothPart y a := by
  rw [completeSmoothPart]
  apply Nat.div_pos
  · exact Nat.le_of_dvd ha (completeRoughLabel_dvd y a)
  · exact completeRoughLabel_pos y a

/-- For a positive original number, the complementary quotient is literally
`(y+1)`-smooth in Mathlib's positive-number convention. -/
theorem completeSmoothPart_mem_smoothNumbers
    {y a : ℕ} (ha : 0 < a) :
    completeSmoothPart y a ∈ Nat.smoothNumbers (y + 1) := by
  rw [Nat.mem_smoothNumbers']
  intro p hp hpDvd
  have hfactorPos := hp.factorization_pos_of_dvd
    (completeSmoothPart_pos ha).ne' hpDvd
  have hpLow : p ≤ y :=
    completeSmoothPart_factorization_support hfactorPos.ne'
  omega

/-! ## Uniqueness and the smooth-label criterion -/



/-- For positive `a`, the rough label is `1` exactly when `a` is
`(y+1)`-smooth. -/
theorem completeRoughLabel_eq_one_iff_mem_smoothNumbers
    {y a : ℕ} (ha : 0 < a) :
    completeRoughLabel y a = 1 ↔
      a ∈ Nat.smoothNumbers (y + 1) := by
  constructor
  · intro hlabel
    have haPart : a = completeSmoothPart y a := by
      simpa only [hlabel, one_mul] using
        completeRough_decomposition y a
    rw [haPart]
    exact completeSmoothPart_mem_smoothNumbers ha
  · intro haSmooth
    by_contra hlabel
    obtain ⟨p, hp, hpDvdLabel⟩ :=
      Nat.exists_prime_and_dvd hlabel
    have hpHigh : y < p :=
      prime_dvd_completeRoughLabel_gt hp hpDvdLabel
    have hpDvdA : p ∣ a :=
      hpDvdLabel.trans (completeRoughLabel_dvd y a)
    have hpLow :=
      (Nat.mem_smoothNumbers').mp haSmooth p hp hpDvdA
    omega



end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankPaperCanonicalGuardedBridgeConnector -/
section


/-!
# Canonical guarded selector to bridge-fit connector

This module joins the finite objects on the two sides of the Section 8/9
interface without asserting the missing selector theorem.

* `bankPaperCanonicalBridgeData` builds the literal `PaperBridgeFit.BridgeData`
  from an existing guarded structured sample, the canonical barycentric
  baseline, and the canonical regular-mesh partition.
* `BankPaperCanonicalGuardedBridgeSelectorConstructor` is the sole
  existential socket.  Its witness is an actual guarded selector satisfying
  the already defined rounded-selector tangent input and agreeing with the
  bridge baseline on the active structured sample.
* the projection and frozen-layer theorems derive the smooth integer quota,
  feasibility, row integrality, prime-band balance and support, tangent
  balance and pointwise/prefix bounds, the frozen feasibility ledger, and the
  total integer quota.  No one of those conclusions is repeated as a new
  premise.

The active structured sample need only be a subset of the guarded smooth row;
it is not silently identified with the whole row.  All other guarded
coordinates are retained in the frozen layer with their selector weights,
while the fixed exceptional factors have weight one.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.PaperBridgeFit
open Erdos390.Full.PaperGuardCensus
open Erdos390.Full.RegularMeshPrimeCutoffs
open Erdos390.Full.RegularRelativeMesh
open BankPaperRealization

noncomputable section

/-! ## Canonical bridge data -/















/-! ## Active values and integer row quotas -/



theorem mem_bankPaperCanonicalBridgeActiveValues
    {Head Band : Type*} [Fintype Head] [DecidableEq Head]
    [Fintype Band] [DecidableEq Band]
    {B : BridgeData Head Band} {a : Nat} :
    a ∈ bankPaperCanonicalBridgeActiveValues B ↔
      ∃ m : B.sampleData.Sample, B.sampleData.value m = a := by
  simp [bankPaperCanonicalBridgeActiveValues]





/-! ## The sole missing constructor and all tangent projections -/





/-! ## Guarded smooth support -/

/-- A structured sample lying in `(n,2n]` whose values avoid the literal
numerical guards is a subset of the guarded smooth row. -/
theorem bankPaperCanonicalBridgeActiveValues_subset_guardedSmoothRow
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
    (deltaStar : Real)
    (hKh : K * upperTailLength c B.sampleData.n <= B.sampleData.n)
    (hlower : forall m : B.sampleData.Sample,
      B.sampleData.n < B.sampleData.value m)
    (hupper : forall m : B.sampleData.Sample,
      B.sampleData.value m <= 2 * B.sampleData.n)
    (hnotGuard : forall m : B.sampleData.Sample,
      B.sampleData.value m ∉
        R.roughCanonicalGuardSet certificate deltaStar) :
    bankPaperCanonicalBridgeActiveValues B ⊆
      R.roughCanonicalGuardedRow certificate deltaStar K 1 := by
  intro a ha
  obtain ⟨m, hvalue⟩ :=
    mem_bankPaperCanonicalBridgeActiveValues.mp ha
  subst a
  apply mem_completeRoughRowFiber.mpr
  constructor
  · rw [BankPaperRealization.roughCanonicalGuardedCandidateSet,
      Finset.mem_sdiff, roughRawCandidateSet_eq_Ioc hKh]
    exact ⟨Finset.mem_Ioc.mpr ⟨hlower m, hupper m⟩,
      hnotGuard m⟩
  · exact (completeRoughLabel_eq_one_iff_mem_smoothNumbers
      (B.sampleData.value_pos m)).mpr
        (B.sampleData.value_mem_smoothNumbers m)







/-! ## Frozen layer and quota -/























/-! ## Baseline slack and ambient feasibility -/







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

/-- Physical fixed-partition endpoints, pointwise rough-guard avoidance, and the rough tail
inequality place every structured head cell in the guarded smooth row. -/
theorem bankPaperCanonicalStructuredActiveValues_subset_guardedSmoothRow_of_physicalIntervals
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
    (deltaStar : Real) (I : PhysicalIntervals)
    (hlowerOne : forall sigma, 1 <= I.lower sigma)
    (hupperTwo : forall sigma, I.upper sigma <= 2)
    (hlo : forall sigma, B.sampleData.lo sigma =
      physicalBound (I.lower sigma) B.sampleData.n)
    (hhi : forall sigma, B.sampleData.hi sigma =
      physicalBound (I.upper sigma) B.sampleData.n)
    (hKh : K * upperTailLength c B.sampleData.n <= B.sampleData.n)
    (hnotGuard : forall m : B.sampleData.Sample,
      B.sampleData.value m ∉
        R.roughCanonicalGuardSet certificate deltaStar) :
    bankPaperCanonicalStructuredActiveValues B.sampleData ⊆
      R.roughCanonicalGuardedRow certificate deltaStar K 1 := by
  have hbounds := bankPaperCanonicalStructuredValue_bounds_of_physicalIntervals
    B I hlowerOne hupperTwo hlo hhi
  intro a ha
  apply bankPaperCanonicalBridgeActiveValues_subset_guardedSmoothRow
    B R certificate deltaStar hKh hbounds.1 hbounds.2 hnotGuard
  exact mem_bankPaperCanonicalBridgeActiveValues.mpr
    (mem_bankPaperCanonicalStructuredActiveValues.mp ha)



















/-! ## Exact frozen remainder of the corrected placement -/











/-! ## Exact coordinate capacity and selector feasibility -/









/-! ## Full guarded constructor with the corrected placement -/









end BankPaperRealization

end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankPaperCanonicalTwoZeroHeadCellProducerConnector -/
section


/-!
# Concrete producer and mass choice for the two zero-head cells

This file isolates the two finite facts needed by the structured
prebridge producer.

First, a sample in the zero head cell is coprime to the complete head
modulus.  Hence it belongs to the guarded broad correction pool as soon as
its physical interval lies below the literal broad cutoff and every sample
value is known pointwise to avoid the canonical guard set.  In particular, no
cardinality surplus theorem is used to prove membership.

Second, the height adjustment has a canonical symmetric realization: put
`-d / 2` in each of the two physical zero-head cells.  Its total change is
the integer `-d`, and the exact lower and upper coordinate-capacity
conditions reduce to two scalar inequalities involving the old total cell
mass and the guard-deleted cell cardinality.

The nearest-integer normalization from `qTilde` to `q0` is recorded
separately.  That first change is generally real rather than integral; the
integer prebridge ledger applies to the subsequent height change from
`q0` to `q0 - d`.
-/

open Filter Topology
open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.PaperBridgeFit
open Erdos390.Full.PaperGuardCensus
open Erdos390.Full.PrimeSums

noncomputable section

namespace BankPaperRealization

/-! ## The fixed physical intervals eventually lie below the broad cutoff -/





/-! ## The zero head pattern produces head-freeness -/

/-- A structured sample carrying the zero simplex tag is coprime to the
product of every prime at most its head cutoff, provided those primes occur
in the concrete head pattern. -/
theorem bankPaperCanonicalZeroHeadValue_coprime_roughHeadModulus
    {P : Finset Nat}
    (D : StructuredSampleData (PaperHeadSimplex.Tag P))
    (hprime : ∀ p ∈ P, p.Prime) (E : Nat)
    (hpattern : D.pattern = PaperHeadSimplex.pattern P hprime E)
    (hhead : primesUpTo D.W ⊆ P)
    (m : D.Sample) (sigma : PhysicalSign)
    (hcell : D.cellOf m = (none, sigma)) :
    Nat.Coprime (D.value m) (roughHeadModulus D.W) := by
  rw [roughHeadModulus, Nat.coprime_prod_right_iff]
  intro p hp
  have hpP : p ∈ P := hhead hp
  have hpPattern : p ∈ (D.pattern (D.cellOf m).1).primes := by
    rw [hpattern]
    exact hpP
  have hmatch := D.value_matches_head m p hpPattern
  have hzero : (D.value m).factorization p = 0 := by
    simpa [hpattern, hcell, PaperHeadSimplex.pattern] using hmatch
  apply Nat.Coprime.symm
  apply ((mem_primesUpTo.mp hp).1.coprime_iff_not_dvd).mpr
  intro hpDvd
  have hpos := (mem_primesUpTo.mp hp).1.factorization_pos_of_dvd
    (Nat.ne_of_gt (D.value_pos m)) hpDvd
  omega

/-- The exact finite producer for membership in the guarded broad pool.
The two numerical premises are precisely membership in `(n,2n-Kh]`; head
freeness and smooth label `1` are derived, while guard exclusion is supplied
pointwise. -/
theorem bankPaperCanonicalZeroHeadValue_mem_guardedBroadCorrectionPool
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
    (deltaStar : Real)
    (hprime : ∀ p ∈ P, p.Prime) (E : Nat)
    (hpattern : B.sampleData.pattern =
      PaperHeadSimplex.pattern P hprime E)
    (hhead : primesUpTo B.sampleData.W ⊆ P)
    (hnotGuard : forall m : B.sampleData.Sample,
      B.sampleData.value m ∉
        R.roughCanonicalGuardSet certificate deltaStar)
    (m : B.sampleData.Sample) (sigma : PhysicalSign)
    (hcell : B.sampleData.cellOf m = (none, sigma))
    (hlower : B.sampleData.n < B.sampleData.value m)
    (hupper : B.sampleData.value m <=
      2 * B.sampleData.n -
        K * upperTailLength c B.sampleData.n) :
    B.sampleData.value m ∈
      R.roughCanonicalGuardedBroadCorrectionPool certificate
        deltaStar B.sampleData.W K 1 := by
  rw [BankPaperRealization.roughCanonicalGuardedBroadCorrectionPool,
    Finset.mem_sdiff]
  constructor
  · apply mem_completeRoughRowFiber.mpr
    constructor
    · apply mem_roughHeadFree.mpr
      constructor
      · rw [roughBroadLowerBlock, Finset.mem_Ioc]
        exact ⟨hlower, hupper⟩
      · exact bankPaperCanonicalZeroHeadValue_coprime_roughHeadModulus
          B.sampleData hprime E hpattern hhead m sigma hcell
    · exact (completeRoughLabel_eq_one_iff_mem_smoothNumbers
        (B.sampleData.value_pos m)).mpr
          (B.sampleData.value_mem_smoothNumbers m)
  · exact hnotGuard m

/-- Fixed physical intervals discharge the lower broad inequality.  The
only extra endpoint condition beyond the existing structured-support
theorem is the literal upper gap
`floor (b_sigma n) <= 2n-Kh`. -/
theorem bankPaperCanonicalZeroHeadValue_mem_guardedBroadCorrectionPool_of_physicalIntervals
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
    (deltaStar : Real)
    (hprime : ∀ p ∈ P, p.Prime) (E : Nat)
    (hpattern : B.sampleData.pattern =
      PaperHeadSimplex.pattern P hprime E)
    (hhead : primesUpTo B.sampleData.W ⊆ P)
    (I : PhysicalIntervals)
    (hlowerOne : forall sigma, 1 <= I.lower sigma)
    (hupperTwo : forall sigma, I.upper sigma <= 2)
    (hlo : forall sigma, B.sampleData.lo sigma =
      physicalBound (I.lower sigma) B.sampleData.n)
    (hhi : forall sigma, B.sampleData.hi sigma =
      physicalBound (I.upper sigma) B.sampleData.n)
    (hupperBroad : forall sigma,
      physicalBound (I.upper sigma) B.sampleData.n <=
        2 * B.sampleData.n -
          K * upperTailLength c B.sampleData.n)
    (hnotGuard : forall m : B.sampleData.Sample,
      B.sampleData.value m ∉
        R.roughCanonicalGuardSet certificate deltaStar)
    (m : B.sampleData.Sample) (sigma : PhysicalSign)
    (hcell : B.sampleData.cellOf m = (none, sigma)) :
    B.sampleData.value m ∈
      R.roughCanonicalGuardedBroadCorrectionPool certificate
        deltaStar B.sampleData.W K 1 := by
  have hbounds :=
    bankPaperCanonicalStructuredValue_bounds_of_physicalIntervals
      B I hlowerOne hupperTwo hlo hhi
  apply bankPaperCanonicalZeroHeadValue_mem_guardedBroadCorrectionPool
    B R certificate deltaStar hprime E hpattern hhead hnotGuard
      m sigma hcell (hbounds.1 m)
  calc
    B.sampleData.value m <=
        B.sampleData.hi (B.sampleData.cellOf m).2 :=
      B.sampleData.value_le_hi m
    _ = physicalBound (I.upper sigma) B.sampleData.n := by
      rw [hcell, hhi]
    _ <= 2 * B.sampleData.n -
        K * upperTailLength c B.sampleData.n := hupperBroad sigma

/-- Both literal zero-head physical cells are therefore produced at once.
This is the exact pair of hypotheses consumed by the two-cell prebridge
connector. -/
theorem bankPaperCanonicalTwoZeroHeadCells_subset_guardedBroadCorrectionPool_of_physicalIntervals
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
    (deltaStar : Real)
    (hprime : ∀ p ∈ P, p.Prime) (E : Nat)
    (hpattern : B.sampleData.pattern =
      PaperHeadSimplex.pattern P hprime E)
    (hhead : primesUpTo B.sampleData.W ⊆ P)
    (I : PhysicalIntervals)
    (hlowerOne : forall sigma, 1 <= I.lower sigma)
    (hupperTwo : forall sigma, I.upper sigma <= 2)
    (hlo : forall sigma, B.sampleData.lo sigma =
      physicalBound (I.lower sigma) B.sampleData.n)
    (hhi : forall sigma, B.sampleData.hi sigma =
      physicalBound (I.upper sigma) B.sampleData.n)
    (hupperBroad : forall sigma,
      physicalBound (I.upper sigma) B.sampleData.n <=
        2 * B.sampleData.n -
          K * upperTailLength c B.sampleData.n)
    (hnotGuard : forall m : B.sampleData.Sample,
      B.sampleData.value m ∉
        R.roughCanonicalGuardSet certificate deltaStar) :
    (forall m : B.sampleData.Sample,
      B.sampleData.cellOf m = (none, .minus) ->
        B.sampleData.value m ∈
          R.roughCanonicalGuardedBroadCorrectionPool certificate
            deltaStar B.sampleData.W K 1) ∧
      forall m : B.sampleData.Sample,
        B.sampleData.cellOf m = (none, .plus) ->
          B.sampleData.value m ∈
            R.roughCanonicalGuardedBroadCorrectionPool certificate
              deltaStar B.sampleData.W K 1 := by
  constructor
  · intro m hm
    exact
      bankPaperCanonicalZeroHeadValue_mem_guardedBroadCorrectionPool_of_physicalIntervals
        B R certificate deltaStar hprime E hpattern hhead I
          hlowerOne hupperTwo hlo hhi hupperBroad hnotGuard
          m .minus hm
  · intro m hm
    exact
      bankPaperCanonicalZeroHeadValue_mem_guardedBroadCorrectionPool_of_physicalIntervals
        B R certificate deltaStar hprime E hpattern hhead I
          hlowerOne hupperTwo hlo hhi hupperBroad hnotGuard
          m .plus hm

/-! ## Canonical symmetric mass choices -/















/-! ## Exact finite coordinate capacity -/















end BankPaperRealization

end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankPaperCanonicalSectionEightTwoZeroOneShotConnector -/
section


/-!
# One-shot Section 8 orchestration for the two zero-head cells

This file joins the three already audited layers of the literal Section 8
construction:

* the analytic ledger gives the `q0` and integer-height asymptotics;
* the two-zero-cell producer realizes the height change by `-d / 2` in
  each physical copy of the zero head cell; and
* the structured prebridge ledger transports the resulting integral row
  change and the exact head-prime moments.

The source selector is not postulated through a new interface.  It is the
canonical protected-plus-ambient selector, and its finite selector state is
read directly from the existing
`BankPaperCanonicalRoundedSelectorTangentInput`.  Consequently the only
new feasibility work is at the two coordinates that actually change.

The terminal eventual theorem uses the same `hcanonical` and
`cellMassMargin` arguments as the canonical Proposition 8.7 statement.  It
only assumes that the ledger and rough guard agree on the positive, smooth,
at-most-`2n` structured universe.  Together with the canonical sample guards,
this yields pointwise exclusion from the full rough guard without any global
Finset equality.  To invoke the existing actual P87 endpoint consumer after
the structured placement, one must additionally identify
the rebalanced seed with a bridge baseline (`Hmeasure` and `hseed`) and
supply the existing analytic `Hfit`; those are retained under their
existing names rather than hidden in a new assumption package.
-/

open Filter Topology Asymptotics Set
open scoped BigOperators

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

/-! ## A reusable two-cell scalar capacity lemma -/



/-! ## Height-only capacity from the Section 8 ledger -/









/-! ## Reusing the rounded source selector -/







/-! ## Exact quota transport -/











/-! ## Canonical P87-local one-shot orchestration -/



/-- The canonical-sample and local guard-agreement data expose exactly the
four finite geometry inputs later consumed by the actual active-measure
constructor: head-pattern separation, support in the guarded smooth row,
and guarded broad-pool membership of the two changed zero-head cells.

These facts were previously proved only inside the one-shot terminal.  This
projection has no selector, capacity, asymptotic, or choice input. -/
theorem bankPaperCanonicalSectionEight_twoZeroHeadCell_geometryInputs
    {P : Finset Nat} {Band : Type*}
    [Fintype Band] [DecidableEq Band]
    (hprime : ∀ p ∈ P, p.Prime) (E : Nat) (hE : 0 < E)
    (I : PhysicalIntervals)
    (hlowerOne : forall sigma, 1 <= I.lower sigma)
    (hupperTwo : forall sigma, I.upper sigma <= 2)
    (Cprom Cbank : Nat) (ledger : forall n, Ledger n Cprom Cbank)
    {c : Real} {depth K : Nat}
    (B : BridgeData (PaperHeadSimplex.Tag P) Band)
    (hhead : primesUpTo B.sampleData.W ⊆ P)
    (hsep : physicalBound (I.upper .minus) B.sampleData.n <
      physicalBound (I.lower .plus) B.sampleData.n)
    (hremaining : forall cell : Cell (PaperHeadSimplex.Tag P),
      (rawCell (PaperHeadSimplex.pattern P hprime E) I B.sampleData.n cell \
        (ledger B.sampleData.n).guards).Nonempty)
    (hcanonical : B.sampleData =
      canonicalSampleData (W := B.sampleData.W)
        (PaperHeadSimplex.pattern P hprime E) I
        (ledger B.sampleData.n) hsep hremaining)
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (deltaStar : Real)
    (hguardAgreement : BankPaperCanonicalBridgeGuardAgreement
      (ledger B.sampleData.n) R certificate deltaStar)
    (hKh : K * upperTailLength c B.sampleData.n <= B.sampleData.n)
    (hupperBroad : forall sigma,
      physicalBound (I.upper sigma) B.sampleData.n <=
        2 * B.sampleData.n -
          K * upperTailLength c B.sampleData.n) :
    B.sampleData.HeadPatternsSeparated ∧
      bankPaperCanonicalStructuredActiveValues B.sampleData ⊆
        R.roughCanonicalGuardedRow certificate deltaStar K 1 ∧
      (forall m : B.sampleData.Sample,
        B.sampleData.cellOf m = (none, .minus) ->
          B.sampleData.value m ∈
            R.roughCanonicalGuardedBroadCorrectionPool certificate
              deltaStar B.sampleData.W K 1) ∧
      forall m : B.sampleData.Sample,
        B.sampleData.cellOf m = (none, .plus) ->
          B.sampleData.value m ∈
            R.roughCanonicalGuardedBroadCorrectionPool certificate
              deltaStar B.sampleData.W K 1 := by
  have hpattern :
      B.sampleData.pattern =
        PaperHeadSimplex.pattern P hprime E := by
    calc
      B.sampleData.pattern =
          (canonicalSampleData (W := B.sampleData.W)
            (PaperHeadSimplex.pattern P hprime E) I
            (ledger B.sampleData.n) hsep hremaining).pattern :=
        congrArg
          (fun D : StructuredSampleData (PaperHeadSimplex.Tag P) =>
            D.pattern)
          hcanonical
      _ = PaperHeadSimplex.pattern P hprime E :=
        canonicalSampleData_pattern
          (PaperHeadSimplex.pattern P hprime E) I
          (ledger B.sampleData.n) hsep hremaining
  have hlo : forall sigma, B.sampleData.lo sigma =
      physicalBound (I.lower sigma) B.sampleData.n := by
    intro sigma
    calc
      B.sampleData.lo sigma =
          (canonicalSampleData (W := B.sampleData.W)
            (PaperHeadSimplex.pattern P hprime E) I
            (ledger B.sampleData.n) hsep hremaining).lo sigma :=
        congrArg
          (fun D : StructuredSampleData (PaperHeadSimplex.Tag P) =>
            D.lo sigma)
          hcanonical
      _ = physicalBound (I.lower sigma) B.sampleData.n :=
        canonicalSampleData_lo
          (PaperHeadSimplex.pattern P hprime E) I
          (ledger B.sampleData.n) hsep hremaining sigma
  have hhi : forall sigma, B.sampleData.hi sigma =
      physicalBound (I.upper sigma) B.sampleData.n := by
    intro sigma
    calc
      B.sampleData.hi sigma =
          (canonicalSampleData (W := B.sampleData.W)
            (PaperHeadSimplex.pattern P hprime E) I
            (ledger B.sampleData.n) hsep hremaining).hi sigma :=
        congrArg
          (fun D : StructuredSampleData (PaperHeadSimplex.Tag P) =>
            D.hi sigma)
          hcanonical
      _ = physicalBound (I.upper sigma) B.sampleData.n :=
        canonicalSampleData_hi
          (PaperHeadSimplex.pattern P hprime E) I
          (ledger B.sampleData.n) hsep hremaining sigma
  have hsampleGuards :
      B.sampleData.guards =
        (ledger B.sampleData.n).guards := by
    calc
      B.sampleData.guards =
          (canonicalSampleData (W := B.sampleData.W)
            (PaperHeadSimplex.pattern P hprime E) I
            (ledger B.sampleData.n) hsep hremaining).guards :=
        congrArg
          (fun D : StructuredSampleData (PaperHeadSimplex.Tag P) =>
            D.guards)
          hcanonical
      _ = (ledger B.sampleData.n).guards :=
        canonicalSampleData_guards
          (PaperHeadSimplex.pattern P hprime E) I
          (ledger B.sampleData.n) hsep hremaining
  have hbounds :=
    bankPaperCanonicalStructuredValue_bounds_of_physicalIntervals
      B I hlowerOne hupperTwo hlo hhi
  have hnotGuard : forall m : B.sampleData.Sample,
      B.sampleData.value m ∉
        R.roughCanonicalGuardSet certificate deltaStar := by
    intro m hfull
    apply B.sampleData.value_not_guard m
    rw [hsampleGuards]
    exact
      (hguardAgreement (B.sampleData.value m)
        (B.sampleData.value_pos m) (hbounds.2 m)
        (B.sampleData.value_mem_smoothNumbers m)).mpr hfull
  have hheadSep : B.sampleData.HeadPatternsSeparated :=
    Erdos390.Full.PaperBridgeFit.StructuredSampleData.headPatternsSeparated_of_paperHeadSimplex
      P hprime E hE B.sampleData hpattern
  have hactiveSmooth :
      bankPaperCanonicalStructuredActiveValues B.sampleData ⊆
        R.roughCanonicalGuardedRow certificate deltaStar K 1 :=
    bankPaperCanonicalStructuredActiveValues_subset_guardedSmoothRow_of_physicalIntervals
      (K := K) B R certificate deltaStar
      I hlowerOne hupperTwo hlo hhi hKh hnotGuard
  have hzeroCells :=
    bankPaperCanonicalTwoZeroHeadCells_subset_guardedBroadCorrectionPool_of_physicalIntervals
      (K := K) B R certificate deltaStar
      hprime E hpattern hhead I hlowerOne hupperTwo hlo hhi
      hupperBroad hnotGuard
  exact ⟨hheadSep, hactiveSmooth, hzeroCells.1, hzeroCells.2⟩





end BankPaperRealization

end

end Erdos390.WholePaper

end

universe u_1
theorem solution :
∀ {P : Finset.{0} Nat} {Band : Type u_1} [inst : Fintype.{u_1} Band] [inst_1 : DecidableEq.{u_1 + 1} Band]
  (hprime :
    ∀ (p : Nat),
      @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
          (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p →
        Nat.Prime p)
  (E : Nat),
  @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) E →
    ∀ (I : Erdos390.Full.PaperGuardCensus.PhysicalIntervals),
      (∀ (sigma : Erdos390.Full.PaperBridgeFit.PhysicalSign),
          @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
            (I.lower sigma)) →
        (∀ (sigma : Erdos390.Full.PaperBridgeFit.PhysicalSign),
            @LE.le.{0} Real Real.instLE (I.upper sigma)
              (@OfNat.ofNat.{0} Real (nat_lit 2)
                (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                  (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                    (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))) →
          ∀ (Cprom Cbank : Nat) (ledger : (n : Nat) → Erdos390.Full.PaperGuardCensus.Ledger n Cprom Cbank) {c : Real}
            {depth K : Nat}
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
                              (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P
                              p) =>
                      @Subtype.instDecidableEq.{1} Nat
                        (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                          (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P)
                        instDecidableEqNat a b)
                    a b)
                inst inst_1),
            @HasSubset.Subset.{0} (Finset.{0} Nat) (@Finset.instHasSubset.{0} Nat)
                (Erdos390.WholePaper.primesUpTo
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
                                    (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat))
                                    P p) =>
                            @Subtype.instDecidableEq.{1} Nat
                              (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P)
                              instDecidableEqNat a b)
                          a b)
                      inst inst_1 B)))
                P →
              ∀
                (hsep :
                  @LT.lt.{0} Nat instLTNat
                    (Erdos390.Full.ArithmeticModel.physicalBound
                      (I.upper Erdos390.Full.PaperBridgeFit.PhysicalSign.minus)
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
                    (Erdos390.Full.ArithmeticModel.physicalBound
                      (I.lower Erdos390.Full.PaperBridgeFit.PhysicalSign.plus)
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
                (hremaining :
                  ∀ (cell : Erdos390.Full.PaperBridgeFit.Cell.{0} (Erdos390.Full.PaperHeadSimplex.Tag P)),
                    @Finset.Nonempty.{0} Nat
                      (@SDiff.sdiff.{0} (Finset.{0} Nat) (@Finset.instSDiff.{0} Nat instDecidableEqNat)
                        (@Erdos390.Full.PaperGuardCensus.rawCell.{0} (Erdos390.Full.PaperHeadSimplex.Tag P)
                          (Erdos390.Full.PaperHeadSimplex.pattern P hprime E) I
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
                          cell)
                        (@Erdos390.Full.PaperGuardCensus.Ledger.guards
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
                          Cprom Cbank
                          (ledger
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
                                inst inst_1 B)))))),
                @Eq.{1}
                    (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.{0} (Erdos390.Full.PaperHeadSimplex.Tag P)
                      (@instFintypeOption.{0}
                        (@Subtype.{1} Nat fun (p : Nat) =>
                          @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                            (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                        (@Finset.Subtype.fintype.{0} Nat P)))
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
                      Cprom Cbank
                      (ledger
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
                      hsep hremaining) →
                  ∀
                    (R :
                      Erdos390.WholePaper.BankPaperRealization
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
                                inst inst_1 B)))))
                    (certificate :
                      Erdos390.WholePaper.GuardedCentralAnchorCertificate c depth
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
                        (@Erdos390.WholePaper.BankPaperRealization.anchorGuardLeftCore
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
                          (Erdos390.WholePaper.upperEndpoint
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
                          (Erdos390.WholePaper.upperEndpoint
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
                          (Erdos390.WholePaper.upperEndpoint
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
                          R depth))
                    (deltaStar : Real),
                    @Erdos390.WholePaper.BankPaperRealization.BankPaperCanonicalBridgeGuardAgreement c depth
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
                              inst inst_1 B)))
                        Cprom Cbank
                        (@Erdos390.WholePaper.BankPaperRealization.anchorGuardLeftCore
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
                          (Erdos390.WholePaper.upperEndpoint
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
                          (Erdos390.WholePaper.upperEndpoint
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
                          (Erdos390.WholePaper.upperEndpoint
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
                        (ledger
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
                              inst inst_1 B)))
                        R certificate deltaStar →
                      @LE.le.{0} Nat instLENat
                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) K
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
                              inst inst_1 B)) →
                        (∀ (sigma : Erdos390.Full.PaperBridgeFit.PhysicalSign),
                            @LE.le.{0} Nat instLENat
                              (Erdos390.Full.ArithmeticModel.physicalBound (I.upper sigma)
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
                                    inst inst_1 B)))
                              (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
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
                                      inst inst_1 B)))
                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) K
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
                                        inst inst_1 B)))))) →
                          And
                            (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.HeadPatternsSeparated.{0}
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
                            (And
                              (@HasSubset.Subset.{0} (Finset.{0} Nat) (@Finset.instHasSubset.{0} Nat)
                                (@Erdos390.WholePaper.bankPaperCanonicalStructuredActiveValues.{0}
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
                                (@Erdos390.WholePaper.BankPaperRealization.roughCanonicalGuardedRow c depth
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
                                        inst inst_1 B)))
                                  (@Erdos390.WholePaper.BankPaperRealization.anchorGuardLeftCore
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
                                  R certificate deltaStar K
                                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                              (And
                                (∀
                                  (m :
                                    @Erdos390.Full.PaperBridgeFit.StructuredSampleData.Sample.{0}
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
                                        inst inst_1 B)),
                                  @Eq.{1} (Erdos390.Full.PaperBridgeFit.Cell.{0} (Erdos390.Full.PaperHeadSimplex.Tag P))
                                      (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.cellOf.{0}
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
                                          inst inst_1 B)
                                        m)
                                      (@Prod.mk.{0, 0}
                                        (Option.{0}
                                          (@Subtype.{1} Nat fun (p : Nat) =>
                                            @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                              (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                (@Finset.instSetLike.{0} Nat))
                                              P p))
                                        Erdos390.Full.PaperBridgeFit.PhysicalSign
                                        (@Option.none.{0}
                                          (@Subtype.{1} Nat fun (p : Nat) =>
                                            @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                              (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                (@Finset.instSetLike.{0} Nat))
                                              P p))
                                        Erdos390.Full.PaperBridgeFit.PhysicalSign.minus) →
                                    @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                        (@Finset.instSetLike.{0} Nat))
                                      (@Erdos390.WholePaper.BankPaperRealization.roughCanonicalGuardedBroadCorrectionPool
                                        c depth
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
                                              inst inst_1 B)))
                                        (@Erdos390.WholePaper.BankPaperRealization.anchorGuardLeftCore
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
                                        R certificate deltaStar
                                        (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{0}
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
                                        K (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                                      (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.value.{0}
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
                                          inst inst_1 B)
                                        m))
                                (∀
                                  (m :
                                    @Erdos390.Full.PaperBridgeFit.StructuredSampleData.Sample.{0}
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
                                        inst inst_1 B)),
                                  @Eq.{1} (Erdos390.Full.PaperBridgeFit.Cell.{0} (Erdos390.Full.PaperHeadSimplex.Tag P))
                                      (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.cellOf.{0}
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
                                          inst inst_1 B)
                                        m)
                                      (@Prod.mk.{0, 0}
                                        (Option.{0}
                                          (@Subtype.{1} Nat fun (p : Nat) =>
                                            @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                              (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                (@Finset.instSetLike.{0} Nat))
                                              P p))
                                        Erdos390.Full.PaperBridgeFit.PhysicalSign
                                        (@Option.none.{0}
                                          (@Subtype.{1} Nat fun (p : Nat) =>
                                            @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                              (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                (@Finset.instSetLike.{0} Nat))
                                              P p))
                                        Erdos390.Full.PaperBridgeFit.PhysicalSign.plus) →
                                    @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                        (@Finset.instSetLike.{0} Nat))
                                      (@Erdos390.WholePaper.BankPaperRealization.roughCanonicalGuardedBroadCorrectionPool
                                        c depth
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
                                              inst inst_1 B)))
                                        (@Erdos390.WholePaper.BankPaperRealization.anchorGuardLeftCore
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
                                        R certificate deltaStar
                                        (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{0}
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
                                        K (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                                      (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.value.{0}
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
                                          inst inst_1 B)
                                        m)))) := by
  exact @Erdos390.WholePaper.BankPaperRealization.bankPaperCanonicalSectionEight_twoZeroHeadCell_geometryInputs
