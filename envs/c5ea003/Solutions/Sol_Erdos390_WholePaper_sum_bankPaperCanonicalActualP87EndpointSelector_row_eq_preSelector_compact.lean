-- Prove2me | solution 1 for Erdos390.WholePaper.sum_bankPaperCanonicalActualP87EndpointSelector_row_eq_preSelector_compact
-- status  : ACCEPTED   (prove)
-- author  : @doctosil
-- created : 2026-09-17T17:51:27.941549+00:00
-- url     : https://prove2.me/submissions/c841b126-af3e-4529-a5d9-3fc7f5abc1b7

import Definitions.Def_erdos390_remaining_analytic_propositions_008
import Mathlib
import Definitions.Def_erdos390_source_bank_interface
import Definitions.Def_erdos390_dickman_step_function
import Theorems.Thm_MediumPNT
import Definitions.Def_erdos390_analytic_foundations_001
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_product_bound
import Theorems.Thm_Erdos390_Full_DickmanBasic_rho_pos_on_zero_five
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_secondDerivative_first_bound
import Definitions.Def_erdos390_analytic_foundations_002
import Definitions.Def_erdos390_analytic_foundations_005
import Definitions.Def_erdos390_analytic_foundations_006
import Definitions.Def_erdos390_analytic_foundations_007
import Definitions.Def_erdos390_analytic_foundations_008

/- Source module: Erdos390.Full.FiniteExponentialFamily -/
section


/-!
# Finite exponential families

This file develops the exact finite exponential family used by the smooth-row
bridge.  The sample space is finite, the base weights are nonnegative with
positive total mass, and every score is a continuous linear functional on a
finite-dimensional real parameter space.  All normalization, positivity,
smoothness, and covariance-Jacobian statements are proved from these data.
-/

open scoped BigOperators

namespace Erdos390.Full

noncomputable section



namespace FiniteProbability

variable {Ω : Type*} [Fintype Ω]





end FiniteProbability



namespace FiniteExponentialFamily

variable {Ω Param : Type*} [Fintype Ω]
  [NormedAddCommGroup Param] [NormedSpace ℝ Param]
  [FiniteDimensional ℝ Param]































theorem activeWeight_sum (fam : FiniteExponentialFamily Ω Param) (ξ : Param) :
    ∑ ω, fam.activeWeight ξ ω = fam.baseMass := by
  simp only [FiniteExponentialFamily.activeWeight]
  rw [← Finset.mul_sum, fam.probabilityMass_sum ξ, mul_one]



























































end FiniteExponentialFamily

end

end Erdos390.Full

end

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







end StructuredSampleData

namespace BridgeData

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]
  (B : BridgeData Head Band)







/-- The active smooth-row mass is exactly fixed by every exponential tilt. -/
theorem sum_activeCoordinateWeight [Nonempty Head]
    (xi : B.ParamSpace) :
    (Finset.univ.sum fun m : B.sampleData.Sample =>
      B.activeCoordinateWeight xi m) = B.q := by
  change (Finset.univ.sum fun m : B.sampleData.Sample =>
    B.vectorFamily.scalarFamily.activeWeight xi m) = B.q
  rw [B.vectorFamily.scalarFamily.activeWeight_sum]
  exact B.vectorFamily_baseMass



/-! The paper uses a compact *effective-score* box, not the crude sum of
all score norms.  The next estimates therefore take the correct pointwise
score bound and have constants independent of the number of active cells. -/













/-! ## Actual natural-number coordinates -/







theorem ambientActiveWeight_eq_zero_of_not_value
    [Nonempty Head] (xi : B.ParamSpace) (a : Nat)
    (ha : forall m : B.sampleData.Sample, B.sampleData.value m ≠ a) :
    B.ambientActiveWeight xi a = 0 := by
  rw [ambientActiveWeight]
  apply Finset.sum_eq_zero
  intro m _
  rw [if_neg (ha m)]









/-! ## Frozen top/protected coordinates and the integer ledger -/

















end BridgeData

end

end Erdos390.Full.PaperBridgeFit

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









/-! ## Frozen layer and quota -/























/-! ## Baseline slack and ambient feasibility -/







end

end Erdos390.WholePaper

end

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













/-- Every active sample coordinate lies in the literal guarded candidate
set selected for the prebridge. -/
theorem bankPaperCanonicalActiveSeed_value_mem_candidates
    {Head : Type*} [Fintype Head] [Nonempty Head]
    {D : StructuredSampleData Head} {T : BarycentricTarget D}
    {candidates : Finset Nat} {preSelector : Nat -> Real}
    {activeSeed : D.Sample -> Real}
    (H : BankPaperCanonicalActualActiveMeasureConstructor
      D T candidates preSelector activeSeed)
    (m : D.Sample) : D.value m ∈ candidates := by
  exact H.2.2.1 m











/-! ## The actual scaled bridge data -/









/-! ## Tagged frozen remainder and exact push-forward -/













/-- The tagged frozen layer pushes forward to the literal protected
remainder `preSelector - activeSeedAmbient` on candidates and to zero
elsewhere. -/
theorem frozenAmbientWeight_eq_bankPaperCanonicalActualFrozenWeight
    {Head : Type*} [Fintype Head]
    (D : StructuredSampleData Head) (candidates : Finset Nat)
    (preSelector : Nat -> Real) (activeSeed : D.Sample -> Real)
    (a : Nat) :
    BridgeData.frozenAmbientWeight
        (bankPaperCanonicalActualFrozenValue (candidates := candidates))
        (bankPaperCanonicalActualFrozenWeight
          D candidates preSelector activeSeed) a =
      if a ∈ candidates then
        preSelector a -
          bankPaperCanonicalActiveSeedAmbientWeight D activeSeed a
      else 0 := by
  classical
  unfold BridgeData.frozenAmbientWeight
    bankPaperCanonicalActualFrozenValue
    bankPaperCanonicalActualFrozenWeight
  by_cases ha : a ∈ candidates
  · rw [if_pos ha, Finset.sum_eq_single (⟨a, ha⟩ : ↑candidates)]
    · simp
    · intro b _hb hba
      rw [if_neg]
      intro hvalue
      exact hba (Subtype.ext hvalue)
    · simp
  · rw [if_neg ha]
    apply Finset.sum_eq_zero
    intro b _hb
    rw [if_neg]
    intro hvalue
    apply ha
    rw [← hvalue]
    exact b.2







/-! ## The initial combined selector -/









/-! ## The literal active marked target and endpoint -/













/-! ## Smooth active support and unchanged complete-rough rows -/

/-- Every actual structured bridge coordinate lies in complete rough row
`1` of the guarded candidate set. -/
theorem bankPaperCanonicalActualActiveValues_subset_smoothRow
    {Head Band : Type*} [Fintype Head] [DecidableEq Head]
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData Head Band) (candidates : Finset Nat)
    (hvalues : forall m : B.sampleData.Sample,
      B.sampleData.value m ∈ candidates) :
    bankPaperCanonicalBridgeActiveValues B ⊆
      completeRoughRowFiber (yNat B.sampleData.n) candidates 1 := by
  intro a ha
  obtain ⟨m, hma⟩ := mem_bankPaperCanonicalBridgeActiveValues.mp ha
  subst a
  apply mem_completeRoughRowFiber.mpr
  exact ⟨hvalues m,
    (completeRoughLabel_eq_one_iff_mem_smoothNumbers
      (B.sampleData.value_pos m)).mpr
        (B.sampleData.value_mem_smoothNumbers m)⟩





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

/-- The live bridge layer has total mass `B.q` on any finite set containing
all active sample values. -/
theorem BridgeData.sum_ambientActiveWeight_eq_q_of_values_mem
    {Head Band : Type*} [Fintype Head] [DecidableEq Head]
    [Fintype Band] [DecidableEq Band] [Nonempty Head]
    (B : BridgeData Head Band) (xi : B.ParamSpace)
    (support : Finset Nat)
    (hvalues : forall m : B.sampleData.Sample,
      B.sampleData.value m ∈ support) :
    (∑ a ∈ support, B.ambientActiveWeight xi a) = B.q := by
  classical
  unfold BridgeData.ambientActiveWeight
  rw [Finset.sum_comm]
  calc
    (∑ m : B.sampleData.Sample,
      ∑ a ∈ support,
        if B.sampleData.value m = a then
          B.activeCoordinateWeight xi m else 0) =
        ∑ m : B.sampleData.Sample, B.activeCoordinateWeight xi m := by
      apply Finset.sum_congr rfl
      intro m _hm
      rw [Finset.sum_eq_single (B.sampleData.value m)]
      · simp
      · intro a _ha hne
        simp [hne.symm]
      · intro hnot
        exact (hnot (hvalues m)).elim
    _ = B.q := B.sum_activeCoordinateWeight xi

/-- Installing the literal seed as the bridge baseline identifies `B.q`
with the paper's literal active mass. -/
theorem BridgeData.q_eq_literalActiveMass_of_baseWeight_eq_seed
    {Head Band : Type*} [Fintype Head] [DecidableEq Head]
    [Fintype Band] [DecidableEq Band] [Nonempty Head]
    (B : BridgeData Head Band)
    (activeSeed : B.sampleData.Sample -> Real)
    (hseed : forall m, B.baseline.baseWeight m = activeSeed m) :
    B.q = bankPaperCanonicalLiteralActiveMass B.sampleData activeSeed := by
  calc
    B.q = ∑ m : B.sampleData.Sample, B.baseline.baseWeight m := by
      exact B.baseline.baseWeight_sum.symm
    _ = ∑ m : B.sampleData.Sample, activeSeed m := by
      apply Finset.sum_congr rfl
      intro m _hm
      exact hseed m
    _ = bankPaperCanonicalLiteralActiveMass B.sampleData activeSeed := rfl

/-- Pointwise form of the actual endpoint on candidate coordinates: frozen
protected remainder plus the live active layer.  It vanishes outside the
candidate set. -/
theorem bankPaperCanonicalActualP87EndpointSelector_eq
    {Head Band : Type*} [Fintype Head] [DecidableEq Head]
    [Fintype Band] [DecidableEq Band] [Nonempty Head]
    (B : BridgeData Head Band)
    (candidates : Finset Nat) (preSelector : Nat -> Real)
    (activeSeed : B.sampleData.Sample -> Real)
    (hvalues : forall m : B.sampleData.Sample,
      B.sampleData.value m ∈ candidates)
    (path : Real -> B.ParamSpace) (a : Nat) :
    bankPaperCanonicalActualP87EndpointSelector
        B candidates preSelector activeSeed path a =
      if a ∈ candidates then
        preSelector a -
            bankPaperCanonicalActiveSeedAmbientWeight
              B.sampleData activeSeed a +
          B.ambientActiveWeight (path 1) a
      else 0 := by
  unfold bankPaperCanonicalActualP87EndpointSelector
    bankPaperProposition87EndpointSelector
    bankPaperProposition87SelectorAt
    BridgeData.ambientCombinedWeight
  rw [frozenAmbientWeight_eq_bankPaperCanonicalActualFrozenWeight]
  by_cases ha : a ∈ candidates
  · simp [ha]
  ·
    have hnotValue : forall m : B.sampleData.Sample,
        B.sampleData.value m ≠ a := by
      intro m hma
      apply ha
      rw [← hma]
      exact hvalues m
    rw [B.ambientActiveWeight_eq_zero_of_not_value
      (path 1) a hnotValue]
    simp [ha]

/-- Every complete-rough-row mass of the endpoint equals the corresponding
prebridge row mass.  On nonsmooth rows both active terms vanish; on the
smooth row their common total is the fixed literal mass `q_n`. -/
theorem sum_bankPaperCanonicalActualP87EndpointSelector_row_eq_preSelector
    {Head Band : Type*} [Fintype Head] [DecidableEq Head]
    [Fintype Band] [DecidableEq Band] [Nonempty Head]
    (B : BridgeData Head Band)
    {T : BarycentricTarget B.sampleData}
    (candidates : Finset Nat) (preSelector : Nat -> Real)
    (activeSeed : B.sampleData.Sample -> Real)
    (H : BankPaperCanonicalActualActiveMeasureConstructor
      B.sampleData T candidates preSelector activeSeed)
    (hseed : forall m, B.baseline.baseWeight m = activeSeed m)
    (path : Real -> B.ParamSpace) (label : Nat) :
    (∑ a ∈ completeRoughRowFiber
        (yNat B.sampleData.n) candidates label,
      bankPaperCanonicalActualP87EndpointSelector
        B candidates preSelector activeSeed path a) =
      ∑ a ∈ completeRoughRowFiber
        (yNat B.sampleData.n) candidates label,
        preSelector a := by
  classical
  let row := completeRoughRowFiber
    (yNat B.sampleData.n) candidates label
  have hrowCandidates : row ⊆ candidates := by
    intro a ha
    exact (mem_completeRoughRowFiber.mp ha).1
  have hpoint : ∀ a ∈ row,
      bankPaperCanonicalActualP87EndpointSelector
          B candidates preSelector activeSeed path a =
        preSelector a -
            bankPaperCanonicalActiveSeedAmbientWeight
              B.sampleData activeSeed a +
          B.ambientActiveWeight (path 1) a := by
    intro a ha
    rw [bankPaperCanonicalActualP87EndpointSelector_eq
      B candidates preSelector activeSeed
        (fun m => bankPaperCanonicalActiveSeed_value_mem_candidates H m)
      path a, if_pos (hrowCandidates ha)]
  have hsplit :
      (∑ a ∈ row,
        bankPaperCanonicalActualP87EndpointSelector
          B candidates preSelector activeSeed path a) =
        (∑ a ∈ row, preSelector a) -
          (∑ a ∈ row,
            bankPaperCanonicalActiveSeedAmbientWeight
              B.sampleData activeSeed a) +
          ∑ a ∈ row, B.ambientActiveWeight (path 1) a := by
    calc
      _ = ∑ a ∈ row,
          (preSelector a -
              bankPaperCanonicalActiveSeedAmbientWeight
                B.sampleData activeSeed a +
            B.ambientActiveWeight (path 1) a) := by
        apply Finset.sum_congr rfl
        intro a ha
        exact hpoint a ha
      _ = _ := by
        rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [hsplit]
  by_cases hlabel : label = 1
  · subst label
    have hactiveValues :=
      bankPaperCanonicalActualActiveValues_subset_smoothRow B candidates
        (fun m => bankPaperCanonicalActiveSeed_value_mem_candidates H m)
    have hseedMass :=
      sum_bankPaperCanonicalActiveSeedAmbientWeight_eq_activeMass_of_subset
        B.sampleData activeSeed row (fun m => by
          apply hactiveValues
          exact mem_bankPaperCanonicalBridgeActiveValues.mpr ⟨m, rfl⟩)
    have hactiveMass :=
      Erdos390.WholePaper.BridgeData.sum_ambientActiveWeight_eq_q_of_values_mem
        B (path 1) row (fun m => by
          apply hactiveValues
          exact mem_bankPaperCanonicalBridgeActiveValues.mpr ⟨m, rfl⟩)
    rw [hseedMass, hactiveMass,
      Erdos390.WholePaper.BridgeData.q_eq_literalActiveMass_of_baseWeight_eq_seed
        B activeSeed hseed]
    ring
  · have hnotRow : forall m : B.sampleData.Sample,
        B.sampleData.value m ∉ row := by
      intro m hm
      have hmLabel := (mem_completeRoughRowFiber.mp hm).2
      have hmOne := (completeRoughLabel_eq_one_iff_mem_smoothNumbers
        (B.sampleData.value_pos m)).mpr
          (B.sampleData.value_mem_smoothNumbers m)
      exact hlabel (hmLabel.symm.trans hmOne)
    have hseedZero :
        (∑ a ∈ row,
          bankPaperCanonicalActiveSeedAmbientWeight
            B.sampleData activeSeed a) = 0 := by
      apply Finset.sum_eq_zero
      intro a ha
      apply bankPaperCanonicalActiveSeedAmbientWeight_eq_zero_of_not_value
      intro m hma
      apply hnotRow m
      rw [hma]
      exact ha
    have hactiveZero :
        (∑ a ∈ row, B.ambientActiveWeight (path 1) a) = 0 := by
      apply Finset.sum_eq_zero
      intro a ha
      apply B.ambientActiveWeight_eq_zero_of_not_value
      intro m hma
      apply hnotRow m
      rw [hma]
      exact ha
    rw [hseedZero, hactiveZero]
    ring





/-! ## Prime support, exact bands, and the derived prefix ledger -/











/-! ## Complete endpoint handoff -/



/-! ## Direct coupling to the guarded continuation -/



end

end Erdos390.WholePaper

end

universe u_1 u_2
theorem solution : Erdos390.RemainingAnalyticGoal008_033.{u_1, u_2} := by
  exact @Erdos390.WholePaper.sum_bankPaperCanonicalActualP87EndpointSelector_row_eq_preSelector
