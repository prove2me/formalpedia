-- Prove2me | solution 1 for Erdos390.WholePaper.BankPaperRealization.bankPaperCanonicalSectionNineFinalPayload_of_roundedSelector_guardedSlack_compact
-- status  : ACCEPTED   (prove)
-- author  : @doctosil
-- created : 2026-09-17T17:27:57.631008+00:00
-- url     : https://prove2.me/submissions/5988e1b0-0bbe-474c-bd53-b5d49a86fcf9

import Definitions.Def_erdos390_remaining_analytic_propositions_004
import Definitions.Def_erdos390_final_payload_cutoff_certificates
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
import Definitions.Def_erdos390_analytic_foundations_004
import Definitions.Def_erdos390_analytic_foundations_005
import Definitions.Def_erdos390_analytic_foundations_006
import Definitions.Def_erdos390_analytic_foundations_007
import Definitions.Def_erdos390_analytic_foundations_008
import Definitions.Def_erdos390_analytic_foundations_010
import Theorems.Thm_Erdos390_WholePaper_BankPaperRealization_canonicalDistributedCleanMultiplier_guardedBroadEndpoints
import Theorems.Thm_Erdos390_WholePaper_BankPaperRealization_exists_canonicalDistributedSectionNinePostTangentOutput_of_paperBudgets_on_candidates_compact
import Theorems.Thm_Erdos390_WholePaper_bankPaperCanonical_fixedRatioPrimeCounting_le_ratioCellCard_compact
import Theorems.Thm_Erdos390_WholePaper_bankPaperCanonical_ratioCell_occupied_of_fixedRatioPrimeInterval_compact
import Theorems.Thm_Erdos390_WholePaper_bankPaperCanonical_weightedPNTEnvelope_le_logGap_compact





section
theorem Erdos390.WholePaper.bankPaperCanonical_weightedPNTEnvelope_le_logGap : Erdos390.AnalyticCompactBatch005Goal001 := @Erdos390.WholePaper.bankPaperCanonical_weightedPNTEnvelope_le_logGap_compact
end
section
universe u_1
theorem Erdos390.WholePaper.BankPaperRealization.exists_canonicalDistributedSectionNinePostTangentOutput_of_paperBudgets_on_candidates : Erdos390.RemainingAnalyticGoal007_001.{u_1} := @Erdos390.WholePaper.BankPaperRealization.exists_canonicalDistributedSectionNinePostTangentOutput_of_paperBudgets_on_candidates_compact
end
section
theorem Erdos390.WholePaper.bankPaperCanonical_ratioCell_occupied_of_fixedRatioPrimeInterval : Erdos390.AnalyticCompactBatch002Goal003 := @Erdos390.WholePaper.bankPaperCanonical_ratioCell_occupied_of_fixedRatioPrimeInterval_compact
end
section
theorem Erdos390.WholePaper.bankPaperCanonical_fixedRatioPrimeCounting_le_ratioCellCard : Erdos390.AnalyticCompactBatch002Goal001 := @Erdos390.WholePaper.bankPaperCanonical_fixedRatioPrimeCounting_le_ratioCellCard_compact
end
/- Source module: Erdos390.Full.RegularRelativeMesh -/
section


/-!
# Existence of a finite regular relative mesh

Section 8.4 partitions the positive logarithmic interval `[delta,1]` into
geometric cells.  This file constructs such a mesh rather than leaving its
existence as a certificate.  Given `0 < delta < 1` and a requested upper
relative width `eta > 0`, the number of cells is the ceiling of the relevant
logarithmic ratio and the common relative width is adjusted so that the last
endpoint is exactly `1`.
-/

open scoped BigOperators

namespace Erdos390.Full.RegularRelativeMesh

noncomputable section



namespace Mesh

variable {delta eta : ℝ} (M : Mesh delta eta)













theorem endpoint_succ (k : ℕ) :
    M.endpoint (k + 1) = M.endpoint k * (1 + M.ratio) := by
  unfold endpoint
  rw [pow_succ]
  ring



theorem endpoint_pos (hdelta : 0 < delta) (k : ℕ) :
    0 < M.endpoint k := by
  unfold endpoint
  exact mul_pos hdelta (pow_pos (by linarith [M.ratio_pos]) k)

theorem lower_pos (hdelta : 0 < delta) (k : Fin M.cellCount) :
    0 < M.lower k := M.endpoint_pos hdelta k.1

theorem width_eq_ratio_mul_lower (k : Fin M.cellCount) :
    M.width k = M.ratio * M.lower k := by
  unfold width upper lower
  rw [M.endpoint_succ]
  ring

theorem width_pos (hdelta : 0 < delta) (k : Fin M.cellCount) :
    0 < M.width k := by
  rw [M.width_eq_ratio_mul_lower]
  exact mul_pos M.ratio_pos (M.lower_pos hdelta k)

theorem lower_lt_upper (hdelta : 0 < delta) (k : Fin M.cellCount) :
    M.lower k < M.upper k := by
  rw [← sub_pos, ← width]
  exact M.width_pos hdelta k



theorem upper_le_one (hdelta : 0 < delta) (k : Fin M.cellCount) :
    M.upper k ≤ 1 := by
  have hpow : (1 + M.ratio) ^ (k.1 + 1) ≤
      (1 + M.ratio) ^ M.cellCount :=
    pow_le_pow_right₀ (by linarith [M.ratio_pos]) (Nat.succ_le_iff.mpr k.2)
  unfold upper endpoint
  calc
    delta * (1 + M.ratio) ^ (k.1 + 1) ≤
        delta * (1 + M.ratio) ^ M.cellCount :=
      mul_le_mul_of_nonneg_left hpow hdelta.le
    _ = 1 := M.lastEndpoint



/-- The positive cells telescope exactly from `delta` to `1`. -/
theorem sum_width_eq_one_sub_delta :
    ∑ k : Fin M.cellCount, M.width k = 1 - delta := by
  change (∑ k : Fin M.cellCount,
      (fun i : ℕ ↦ M.endpoint (i + 1) - M.endpoint i) k.1) =
    1 - delta
  calc
    (∑ k : Fin M.cellCount,
        (fun i : ℕ ↦ M.endpoint (i + 1) - M.endpoint i) k.1) =
        ∑ k ∈ Finset.range M.cellCount,
          (M.endpoint (k + 1) - M.endpoint k) :=
      Fin.sum_univ_eq_sum_range
        (fun i : ℕ ↦ M.endpoint (i + 1) - M.endpoint i) M.cellCount
    _ = 1 - delta := by
      rw [Finset.sum_range_sub, M.endpoint_cellCount, M.endpoint_zero]

end Mesh



end

end Erdos390.Full.RegularRelativeMesh

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



































end StructuredSampleData



namespace BaselineAllocation

variable {Head : Type*} [Fintype Head]
  {D : StructuredSampleData Head}



















end BaselineAllocation









namespace BridgeData

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]
  (B : BridgeData Head Band)

















/-- The logarithmic smoothness scale is strictly positive on the actual
range `n > 1`; in particular all normalized logarithms below have a
nonzero denominator. -/
theorem log_y_pos : 0 < Real.log (ArithmeticModel.y B.sampleData.n) := by
  rw [Scale.log_y (Nat.zero_lt_of_lt B.n_gt_one)]
  exact mul_pos (by norm_num) (by simpa [Scale.L, L] using B.L_pos)































































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

/- Source module: Erdos390.Full.PrimeBandQuadrature -/
section


/-!
# Audited harmonic prime quadrature on moving positive cells

The continuum transfer in Lemma 8.4 uses prime cells whose endpoints are
powers of the smoothness scale.  This file starts the required arithmetic
quadrature from the actual Chebyshev function.  The key identity below has no
Mertens constant: it subtracts Abel summation at two endpoints and isolates
the quantitative PNT remainder exactly.
-/

open scoped BigOperators
open Set
open Filter Topology Asymptotics

noncomputable section

namespace Erdos390.Full.PrimeBandQuadrature

open MeasureTheory
open Erdos390.Full.PrimeSums
open Erdos390.Full.FriableAsymptotic



























/-! ## The first logarithmic moment -/















/-! ## Quantitative PNT remainder -/





















/-! ## Exact alignment with the paper's logarithmic coordinate -/





















theorem fullReciprocalSumUniformConstant_pos :
    0 < fullReciprocalSumUniformConstant :=
  (Classical.choose_spec
    exists_fullReciprocalSum_interval_error_bound).1



theorem fullReciprocalSumUniform_bound
    (A Y : ℕ) (hA : fullReciprocalSumUniformCutoff ≤ A)
    (hAY : A ≤ Y) :
    |fullReciprocalSum Y - fullReciprocalSum A -
        (Real.log (Real.log (Y : ℝ)) -
          Real.log (Real.log (A : ℝ)))| ≤
      5 * fullReciprocalSumUniformConstant / Real.log (A : ℝ) ^ 3 :=
  (Classical.choose_spec
    (Classical.choose_spec
      exists_fullReciprocalSum_interval_error_bound).2) A Y hA hAY



end Erdos390.Full.PrimeBandQuadrature

end

/- Source module: Erdos390.Full.RegularMeshMomentBounds -/
section


/-!
# Moment budgets for the regular relative mesh

This is the elementary continuum census behind the arithmetic estimates in
Lemma 8.6.  The moving-low cell provides the quadratic lower bound, while the
geometric positive cells have total `L¹` cost at most their common relative
width and total quadratic cost at most its square.
-/

open scoped BigOperators

namespace Erdos390.Full.RegularRelativeMesh

noncomputable section

namespace Mesh

variable {delta eta : ℝ} (M : Mesh delta eta)















theorem lower_le_one (hdelta : 0 < delta) (k : Fin M.cellCount) :
    M.lower k ≤ 1 :=
  (M.lower_lt_upper hdelta k).le.trans (M.upper_le_one hdelta k)

theorem width_le_ratio (hdelta : 0 < delta) (k : Fin M.cellCount) :
    M.width k ≤ M.ratio := by
  rw [M.width_eq_ratio_mul_lower]
  nlinarith [M.ratio_pos, M.lower_pos hdelta k,
    M.lower_le_one hdelta k]









end Mesh





















end

end Erdos390.Full.RegularRelativeMesh

end

/- Source module: Erdos390.Full.RegularMeshActualMomentBounds -/
section


/-!
# Actual arithmetic `L¹` and variance bounds for the regular mesh

The endpoints in this file are the explicit floored endpoints from
`RegularMeshPrimeCutoffs`, and every sum is over the actual primes.  The
first part proves the finite deterministic assembly.  The final part derives
its moment inputs from the proved PNT quadratures.
-/

open scoped BigOperators
open Filter

namespace Erdos390.Full.RegularMeshPrimeCutoffs

noncomputable section

open ArithmeticModel ArithmeticBandGeometry RegularRelativeMesh
open PositiveCellTransfer KernelPrimeQuadrature
open PrimeIntervalPartitionConstructor

theorem y_gt_one {n : ℕ} (hn : 1 < n) : 1 < y n := by
  have hlog : 0 < Real.log (y n) := by
    rw [Scale.log_y (Nat.zero_lt_of_lt hn)]
    exact mul_pos (by norm_num) (Real.log_pos (by exact_mod_cast hn))
  exact (Real.log_pos_iff (Scale.y_pos (Nat.zero_lt_of_lt hn)).le).mp hlog

theorem realLogCoordinate_scalePoint {n : ℕ} (hn : 1 < n) (t : ℝ) :
    realLogCoordinate (y n) (scalePoint n t) = t := by
  have hlog : Real.log (y n) ≠ 0 := ne_of_gt (Real.log_pos (y_gt_one hn))
  unfold realLogCoordinate scalePoint
  rw [Real.log_exp]
  field_simp [hlog]

theorem realLogCoordinate_floorScale_lt_prime
    {n p : ℕ} (hn : 1 < n) {t : ℝ}
    (hp : ⌊scalePoint n t⌋₊ < p) :
    t < tPrime n p := by
  have hscale : 0 ≤ scalePoint n t := (Real.exp_pos _).le
  have hreal : scalePoint n t < (p : ℝ) :=
    (Nat.floor_lt hscale).mp hp
  have hpPos : 0 < (p : ℝ) := (Real.exp_pos _).trans hreal
  have hlog := Real.strictMonoOn_log
    (show scalePoint n t ∈ Set.Ioi 0 from Real.exp_pos _)
    (show (p : ℝ) ∈ Set.Ioi 0 from hpPos) hreal
  have hlogy := Real.log_pos (y_gt_one hn)
  unfold tPrime
  rw [← realLogCoordinate_scalePoint hn t]
  unfold realLogCoordinate
  exact (div_lt_div_iff_of_pos_right hlogy).2 hlog

theorem prime_logCoordinate_le_of_le_floorScale
    {n p : ℕ} (hn : 1 < n) {t : ℝ}
    (hpPos : 0 < p) (hp : p ≤ ⌊scalePoint n t⌋₊) :
    tPrime n p ≤ t := by
  have hfloorLe : (⌊scalePoint n t⌋₊ : ℝ) ≤ scalePoint n t :=
    Nat.floor_le (Real.exp_pos _).le
  have hpCast : (p : ℝ) ≤ (⌊scalePoint n t⌋₊ : ℝ) := by
    exact_mod_cast hp
  have hpReal : (p : ℝ) ≤ scalePoint n t := hpCast.trans hfloorLe
  have hpRealPos : 0 < (p : ℝ) := by exact_mod_cast hpPos
  have hlog := Real.log_le_log hpRealPos hpReal
  have hlogy := Real.log_pos (y_gt_one hn)
  unfold tPrime
  rw [← realLogCoordinate_scalePoint hn t]
  unfold realLogCoordinate
  exact div_le_div_of_nonneg_right hlog hlogy.le

namespace Mesh

variable {delta eta : ℝ} (M : Mesh delta eta)
  {n W : ℕ} (P : Partition n W (Fin (M.cellCount + 1)))
  (E : IntervalCertificate P)
  (hLower : ∀ j, E.lower j = fullCutoff M n W j.1)
  (hUpper : ∀ j, E.upper j = fullCutoff M n W (j.1 + 1))

include E hLower hUpper



/-- Every actual prime in positive cell `k` lies in the intended continuum
cell, despite the use of floored natural endpoints. -/
theorem positive_coord_bounds (hn : 1 < n) (k : Fin M.cellCount)
    (p : BandPrime n W)
    (hp : p ∈ P.data.fiber k.succ) :
    tPrime n p.1 ∈ Set.Icc (M.lower k) (M.upper k) := by
  have hpBand : P.band p = k.succ :=
    (Erdos390.Lemma84.WeightedBandData.mem_fiber_iff P.data).mp hp
  have hpInterval :=
    (PositiveCellTransfer.IntervalCertificate.band_eq_iff E p k.succ).mp hpBand
  have hpLower := hpInterval.1
  have hpUpper := hpInterval.2
  rw [hLower k.succ] at hpLower
  rw [hUpper k.succ] at hpUpper
  have hsuccVal : k.succ.1 = k.1 + 1 := rfl
  simp only [hsuccVal, fullCutoff] at hpLower
  simp only [fullCutoff] at hpUpper
  exact ⟨(realLogCoordinate_floorScale_lt_prime hn hpLower).le,
    prime_logCoordinate_le_of_le_floorScale hn
      (prime_of_mem_primeBand p.2).pos hpUpper⟩











end Mesh

end

end Erdos390.Full.RegularMeshPrimeCutoffs

end

/- Source module: Erdos390.Full.CanonicalEndpointAnchorCoverage -/
section


/-!
# Uniform interior anchor coverage for the endpoint mesh

Flooring a power-scale endpoint changes its logarithmic coordinate by at
most `log 2 / log y` once the endpoint is at least two.  This proves that a
fixed strictly interior regular-mesh cell remains interior in the actual
endpoint mesh and retains at least half of its continuum length.
-/

open Filter Set

noncomputable section

namespace Erdos390.Full.RegularMeshPrimeCutoffs

open ArithmeticModel RegularRelativeMesh
open KernelPrimeQuadrature
open ContinuumCellGraph

theorem floor_scalePoint_coordinate_bounds
    {n : ℕ} (hn : 1 < n) {t : ℝ}
    (hxTwo : 2 ≤ scalePoint n t) :
    t - Real.log 2 / Real.log (y n) ≤
        realLogCoordinate (y n) (⌊scalePoint n t⌋₊ : ℝ) ∧
      realLogCoordinate (y n) (⌊scalePoint n t⌋₊ : ℝ) ≤ t := by
  let x := scalePoint n t
  let m := ⌊x⌋₊
  have hylog : 0 < Real.log (y n) := by
    rw [Scale.log_y (Nat.zero_lt_of_lt hn)]
    exact mul_pos (by norm_num) (Real.log_pos (by exact_mod_cast hn))
  have hxpos : 0 < x := by unfold x scalePoint; positivity
  have hmUpper : (m : ℝ) ≤ x := Nat.floor_le hxpos.le
  have hfloorLt : x < (m : ℝ) + 1 := by
    simpa only [m] using Nat.lt_floor_add_one x
  have hmLower : x / 2 ≤ (m : ℝ) := by linarith
  have hmpos : (0 : ℝ) < (m : ℝ) :=
    (div_pos hxpos (by norm_num)).trans_le hmLower
  have hlogLower : Real.log (x / 2) ≤ Real.log (m : ℝ) :=
    Real.log_le_log (div_pos hxpos (by norm_num)) hmLower
  have hlogUpper : Real.log (m : ℝ) ≤ Real.log x :=
    Real.log_le_log hmpos hmUpper
  have hlogX : Real.log x = t * Real.log (y n) := by
    unfold x scalePoint
    rw [Real.log_exp]
  have hlogDiv : Real.log (x / 2) = Real.log x - Real.log 2 := by
    rw [Real.log_div hxpos.ne' (by norm_num : (2 : ℝ) ≠ 0)]
  constructor
  · unfold realLogCoordinate
    apply (le_div_iff₀ hylog).2
    have hscaled :
        (t - Real.log 2 / Real.log (y n)) * Real.log (y n) =
          Real.log x - Real.log 2 := by
      rw [sub_mul, div_mul_cancel₀ _ hylog.ne', hlogX]
    rw [hscaled, ← hlogDiv]
    exact hlogLower
  · unfold realLogCoordinate
    apply (div_le_iff₀ hylog).2
    rw [hlogX] at hlogUpper
    exact hlogUpper

namespace Mesh

variable {delta eta : ℝ} (M : Mesh delta eta)







end Mesh
end Erdos390.Full.RegularMeshPrimeCutoffs

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

/- Source module: Erdos390.WholePaper.BankPaperPaths -/
section


/-!
# Actual full bank paths

For one signed rounding slot, the component index is the disjoint union of
the ordinary `p→5` sources and the relevant truncated bottom rows.  Each
index contributes exactly one state-zero endpoint and one state-one endpoint;
markers and donors belong to the component census, but never to either path
state.  Global occurrence disjointness makes both endpoint maps injective.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel

noncomputable section







@[simp] theorem bankBottomRelevantRequestToPaperRequest_ofMove
    {n : ℕ} (slot : SignedBankSlot (bankRoundingBetaOnSupport n))
    (move : ↑(bankBottomRelevantMoves slot.1.1)) :
    bankBottomRelevantRequestToPaperRequest
        (bankPaperBottomRelevantRequestOfMove slot move) =
      bankPaperBottomRequestOfMove slot move := rfl





namespace BankPaperRealization







theorem pathStateZeroValue_mem_componentOccurrences
    {n M : ℕ} (R : BankPaperRealization n M)
    (slot : SignedBankSlot (bankRoundingBetaOnSupport n))
    (component : BankPaperPathComponent slot) :
    R.pathStateZeroValue slot component ∈
      R.pathComponentOccurrences slot component := by
  cases component with
  | inl source =>
      cases hslot : slot.2
      · simpa [pathStateZeroValue, pathComponentOccurrences, hslot,
          BankOrdinaryPaperRealization.fromStateValue,
          BankOrdinaryPaperRealization.requestOfSource,
          bankOrdinaryPaperRequestPool, bankSignedSlotOrientation] using
          R.ordinary.occurrenceValue_mem_componentOccurrences
            (BankOrdinaryPaperRealization.requestOfSource slot source)
            .sourceState
      · simpa [pathStateZeroValue, pathComponentOccurrences, hslot,
          BankOrdinaryPaperRealization.fromStateValue,
          BankOrdinaryPaperRealization.requestOfSource,
          bankOrdinaryPaperRequestPool, bankSignedSlotOrientation] using
          R.ordinary.occurrenceValue_mem_componentOccurrences
            (BankOrdinaryPaperRealization.requestOfSource slot source)
            .targetState
  | inr move =>
      rw [pathComponentOccurrences,
        R.bottom.componentOccurrences_eq_states_insert_donor]
      cases hslot : slot.2 <;>
        simp [pathStateZeroValue, BankBottomPaperRealization.fromStateValue,
          bankSignedSlotOrientation, bankPaperBottomRequestOfMove, hslot]

theorem pathStateOneValue_mem_componentOccurrences
    {n M : ℕ} (R : BankPaperRealization n M)
    (slot : SignedBankSlot (bankRoundingBetaOnSupport n))
    (component : BankPaperPathComponent slot) :
    R.pathStateOneValue slot component ∈
      R.pathComponentOccurrences slot component := by
  cases component with
  | inl source =>
      cases hslot : slot.2
      · simpa [pathStateOneValue, pathComponentOccurrences, hslot,
          BankOrdinaryPaperRealization.toStateValue,
          BankOrdinaryPaperRealization.requestOfSource,
          bankOrdinaryPaperRequestPool, bankSignedSlotOrientation] using
          R.ordinary.occurrenceValue_mem_componentOccurrences
            (BankOrdinaryPaperRealization.requestOfSource slot source)
            .targetState
      · simpa [pathStateOneValue, pathComponentOccurrences, hslot,
          BankOrdinaryPaperRealization.toStateValue,
          BankOrdinaryPaperRealization.requestOfSource,
          bankOrdinaryPaperRequestPool, bankSignedSlotOrientation] using
          R.ordinary.occurrenceValue_mem_componentOccurrences
            (BankOrdinaryPaperRealization.requestOfSource slot source)
            .sourceState
  | inr move =>
      rw [pathComponentOccurrences,
        R.bottom.componentOccurrences_eq_states_insert_donor]
      cases hslot : slot.2 <;>
        simp [pathStateOneValue, BankBottomPaperRealization.toStateValue,
          bankSignedSlotOrientation, bankPaperBottomRequestOfMove, hslot]



















theorem pathStateZero_subset_componentCensus
    {n M : ℕ} (R : BankPaperRealization n M)
    (slot : SignedBankSlot (bankRoundingBetaOnSupport n)) :
    R.pathStateZero slot ⊆ R.pathComponentCensus slot := by
  intro occurrence hoccurrence
  rw [pathStateZero, indexedPathState, Finset.mem_image] at hoccurrence
  obtain ⟨component, _hcomponent, rfl⟩ := hoccurrence
  rw [pathComponentCensus, Finset.mem_biUnion]
  exact ⟨component, Finset.mem_univ _,
    R.pathStateZeroValue_mem_componentOccurrences slot component⟩

theorem pathStateOne_subset_componentCensus
    {n M : ℕ} (R : BankPaperRealization n M)
    (slot : SignedBankSlot (bankRoundingBetaOnSupport n)) :
    R.pathStateOne slot ⊆ R.pathComponentCensus slot := by
  intro occurrence hoccurrence
  rw [pathStateOne, indexedPathState, Finset.mem_image] at hoccurrence
  obtain ⟨component, _hcomponent, rfl⟩ := hoccurrence
  rw [pathComponentCensus, Finset.mem_biUnion]
  exact ⟨component, Finset.mem_univ _,
    R.pathStateOneValue_mem_componentOccurrences slot component⟩















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









end BankPaperRealization

end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankPaperFixedExceptionalBacking -/
section


/-!
# The literal fixed exceptional factors and their high-prime backing

The paper fixes every upper-tail factor whose complete rough row has real
scale `2n / R_y(a) < n ^ deltaStar`, except for the actual donor occurrences
already withheld for the precharged bank.  This file makes that set literal.

The definition deliberately uses the displayed real quotient and real power.
It is not the larger integral test obtained by flooring the rough scale and
ceiling the exceptional cutoff.

At every prime above the rough cutoff, replacing the donor set by the bank's
base state preserves factorization coordinatewise.  The fixed exceptional
factors and donors are disjoint subsets of the literal tail, so their union
is an unconditional backing product for the complete selector charge in
all such coordinates.  No small-prime charge estimate is asserted here.
-/

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel

noncomputable section







namespace BankPaperRealization





theorem paperFixedExceptionalFactors_subset_upperBlock
    {n h : ℕ}
    (R : BankPaperRealization n (upperEndpoint n h))
    (deltaStar : ℝ) :
    R.paperFixedExceptionalFactors deltaStar ⊆ roughUpperBlock n h := by
  intro a ha
  rw [paperFixedExceptionalFactors, Finset.mem_sdiff] at ha
  exact (mem_paperExceptionalUpperFactors.mp ha.1).1

/-- Every fixed exceptional factor is a literal upper-tail occurrence. -/
theorem paperFixedExceptionalFactors_subset_tail
    {n h : ℕ}
    (R : BankPaperRealization n (upperEndpoint n h))
    (deltaStar : ℝ) :
    R.paperFixedExceptionalFactors deltaStar ⊆
      Finset.Ioc (2 * n) (upperEndpoint n h) := by
  simpa only [roughUpperBlock, upperEndpoint] using
    R.paperFixedExceptionalFactors_subset_upperBlock deltaStar



















end BankPaperRealization

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







/-! ## Exact finite deletion counts -/















end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankPaperCanonicalGuardLocalRowLedger -/
section


/-!
# Guard-local canonical rough-row ledger

This module isolates the finite bookkeeping that occurs when the paper
passes from the raw canonical rough candidates to the candidates left after
the numerical guards

`Gamma_num = anchors ∪ G_fix ∪ E_donor ∪ G_bank^0 ∪ G_bank^1`.

Only literal finite-set identities are proved here.  In particular, this
file does **not** assume or assert a local guard census, a lower bound for a
guarded broad pool, or enough guarded-row capacity for a corrected selector.
Those still-missing estimates are exposed at the end as named propositions.

The postcharge target is kept in `Real` form for the correction algebra and
in `Int` form for its exact integrality witness.  Its nonnegativity is a
finite consequence of the actual donor/base row-preserving bijection and of
the disjoint upper-tail backing of the fixed exceptional factors and donors.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel

noncomputable section

namespace BankPaperRealization

/-! ## Literal guarded candidates and row pieces -/













theorem roughCanonicalGuardedCandidateSet_disjoint_guardSet
    {c : ℝ} {depth n h : ℕ} {left right : ℕ → ℕ}
    {changed : Finset ℕ}
    (R : BankPaperRealization n (upperEndpoint n h))
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (deltaStar : ℝ) (K : ℕ) :
    Disjoint
      (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
      (R.roughCanonicalGuardSet certificate deltaStar) := by
  exact Finset.sdiff_disjoint













/-! ## The donor/base row-preserving bijection -/









/-! ## Upper-tail ownership and the postcharge target -/





























/-! ## Exact local discrepancy ledger -/







/-! ## Exact support reduction for the local deletion set -/







/-! ## Explicit remaining finite/analytic obligations -/







end BankPaperRealization

end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankPaperAnchorExactificationGuards -/
section


/-!
# Central-anchor guards for the concrete exactification states

Every Boolean exactification state is one endpoint from every component in
one oppositely reindexed paper path.  Hence it is a subset of that path's
component census, and ultimately of the global actual bank census.  The
complete anchor/census collision theorem therefore supplies the anchor--bank
part of the final residual disjointness ledger.  (The `fixed` argument of
concrete exactification is the separate residual fixed set, not the external
anchors.)  The same argument is lifted through the literal `biUnion`
defining the base and an arbitrary chosen bank state.
-/

open Filter Topology

namespace Erdos390.WholePaper

noncomputable section

namespace BankPaperRealization

/-- Every component occurrence in one full path belongs to the global actual
bank census. -/
theorem pathComponentCensus_subset_allComponentOccurrences
    {n M : ℕ} (R : BankPaperRealization n M)
    (slot : SignedBankSlot (bankRoundingBetaOnSupport n)) :
    R.pathComponentCensus slot ⊆ R.allComponentOccurrences := by
  intro occurrence hoccurrence
  rw [pathComponentCensus, Finset.mem_biUnion] at hoccurrence
  obtain ⟨component, _hcomponent, hcomponentOccurrence⟩ := hoccurrence
  rw [allComponentOccurrences, Finset.mem_union]
  cases component with
  | inl source =>
      left
      rw [ordinaryComponentOccurrences, Finset.mem_biUnion]
      refine ⟨BankOrdinaryPaperRealization.requestOfSource slot source,
        Finset.mem_attach _ _, ?_⟩
      simpa only [pathComponentOccurrences] using hcomponentOccurrence
  | inr move =>
      right
      rw [bottomComponentOccurrences,
        BankBottomPaperRealization.relevantComponentOccurrences,
        Finset.mem_biUnion]
      refine ⟨bankPaperBottomRelevantRequestOfMove slot move,
        Finset.mem_attach _ _, ?_⟩
      simpa only [pathComponentOccurrences,
        bankBottomRelevantRequestToPaperRequest_ofMove] using
          hcomponentOccurrence

/-- In particular every oppositely reindexed Boolean exactification state is
a subset of the global actual bank census. -/
theorem exactificationState_subset_allComponentOccurrences
    {n M : ℕ} (R : BankPaperRealization n M)
    (slot : SignedBankSlot (bankRoundingBetaOnSupport n))
    (selected : Bool) :
    R.exactificationState slot selected ⊆ R.allComponentOccurrences := by
  intro occurrence hoccurrence
  apply R.pathComponentCensus_subset_allComponentOccurrences
    (bankPaperOppositeSlot slot)
  cases selected
  · exact R.pathStateZero_subset_componentCensus
      (bankPaperOppositeSlot slot)
      (by simpa only [exactificationState_false] using hoccurrence)
  · exact R.pathStateOne_subset_componentCensus
      (bankPaperOppositeSlot slot)
      (by simpa only [exactificationState_true] using hoccurrence)

/-- Any set disjoint from the global component census is disjoint from each
Boolean exactification state. -/
theorem disjoint_exactificationState_of_disjoint_allComponentOccurrences
    {n M : ℕ} (R : BankPaperRealization n M) (anchors : Finset ℕ)
    (hdisjoint : Disjoint anchors R.allComponentOccurrences)
    (slot : SignedBankSlot (bankRoundingBetaOnSupport n))
    (selected : Bool) :
    Disjoint anchors (R.exactificationState slot selected) :=
  hdisjoint.mono Finset.Subset.rfl
    (R.exactificationState_subset_allComponentOccurrences slot selected)





/-! ## Guarded-certificate specializations -/













end BankPaperRealization

end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.TangentPairArithmetic -/
section


/-!
# Finite arithmetic for tangent collision pairs

This file discharges the finite four-endpoint part of the
`hpairArithmetic` contract in `TangentSplitRequestLoads`.  It separates two
layers.

* Four per-equation bounds are assembled into the paper's one disjoint charge
  and two possible shared-label charges.  Distinct endpoints on the right
  request ensure that each left label can create at most one shared equation.
* A paper-scale specialization derives the per-equation bounds from a supplied
  effective list-density inequality

  `density * n <= lowerCard(request) * endpointLabel(request, side)`.

The specialization uses only `tangentBroadUpper n K h <= 2*n`, prime-label
positivity, and explicit hypotheses saying that every endpoint is at most a
cutoff whose first and second powers are at most `n`.  It yields the concrete
coefficients `12 / density^2` and `3 / density^2`.

No clean-list density estimate or cutoff asymptotic is proved here.  In a
paper application those are precisely the inputs needed to establish the
displayed effective-density and cutoff inequalities.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

noncomputable section

/-! ## Coefficients and elementary endpoint budgets -/









/-- The broad numerical endpoint never exceeds `2*n`. -/
theorem tangentBroadUpper_le_two_mul (n K h : ℕ) :
    tangentBroadUpper n K h ≤ 2 * n := by
  exact Nat.sub_le _ _





/-! ## Assembly of four endpoint equations -/





/-! ## Effective-density bounds for one endpoint equation -/





/-! ## Paper-scale pair arithmetic -/





/-! ## The literal `1/8` coefficient arithmetic -/





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

/-- The subtype-to-natural prime label map is injective. -/
theorem bankPaperCanonicalTangentPrimeLabel_injective
    {n W : ℕ} :
    Function.Injective
      (bankPaperCanonicalTangentPrimeLabel (n := n) (W := W)) := by
  intro p q hpq
  exact Subtype.ext hpq

/-- Every canonical tangent label is prime. -/
theorem bankPaperCanonicalTangentPrimeLabel_prime
    {n W : ℕ} (p : BankPaperCanonicalTangentPrime n W) :
    (bankPaperCanonicalTangentPrimeLabel p).Prime := by
  exact prime_of_mem_primeBand p.2











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

































/-- A band is the disjoint union of the prefix through `cut` and the
strict tail after `cut`. -/
theorem tangentRatioCellPrefixMass_add_tail_eq_bandSum
    {V Band : Type*} [Fintype V] [DecidableEq Band]
    (residual : V -> Real) (bandOf : V -> Band) (cellIndex : V -> Nat)
    (band : Band) (cut : Nat) :
    tangentRatioCellPrefixMass residual bandOf cellIndex band cut +
        (∑ v : V,
          if bandOf v = band ∧ cut < cellIndex v then residual v else 0) =
      ∑ v : V, if bandOf v = band then residual v else 0 := by
  unfold tangentRatioCellPrefixMass
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro v _hv
  by_cases hband : bandOf v = band
  · by_cases hcell : cellIndex v <= cut
    · have hnotTail : ¬cut < cellIndex v := Nat.not_lt_of_ge hcell
      simp [hband, hcell, hnotTail]
    · have htail : cut < cellIndex v := Nat.lt_of_not_ge hcell
      simp [hband, hcell, htail]
  · simp [hband]

/-- Exact band balance turns every prefix into the negative strict tail;
the pointwise residual estimate therefore supplies the paper's prefix
majorant without an additional selector-rounding assumption. -/
theorem abs_tangentRatioCellPrefixMass_le_tailPointwiseUpper
    {V Band : Type*} [Fintype V] [DecidableEq Band]
    (residual pointwiseUpper : V -> Real)
    (bandOf : V -> Band) (cellIndex : V -> Nat)
    (hbalance : forall band,
      (∑ v : V, if bandOf v = band then residual v else 0) = 0)
    (hpointwise : forall v, |residual v| <= pointwiseUpper v)
    (band : Band) (cut : Nat) :
    |tangentRatioCellPrefixMass residual bandOf cellIndex band cut| <=
      tangentRatioCellTailPointwiseUpper
        pointwiseUpper bandOf cellIndex band cut := by
  have hsplit := tangentRatioCellPrefixMass_add_tail_eq_bandSum
    residual bandOf cellIndex band cut
  have hprefix :
      tangentRatioCellPrefixMass residual bandOf cellIndex band cut =
        -(∑ v : V,
          if bandOf v = band ∧ cut < cellIndex v then residual v else 0) := by
    rw [hbalance band] at hsplit
    linarith
  rw [hprefix, abs_neg]
  calc
    |(∑ v : V,
        if bandOf v = band ∧ cut < cellIndex v then residual v else 0)| <=
        ∑ v : V,
          |if bandOf v = band ∧ cut < cellIndex v then residual v else 0| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ v : V,
        if bandOf v = band ∧ cut < cellIndex v then |residual v| else 0 := by
      apply Finset.sum_congr rfl
      intro v _hv
      by_cases htail : bandOf v = band ∧ cut < cellIndex v <;>
        simp [htail]
    _ <= tangentRatioCellTailPointwiseUpper
          pointwiseUpper bandOf cellIndex band cut := by
      unfold tangentRatioCellTailPointwiseUpper
      apply Finset.sum_le_sum
      intro v _hv
      by_cases htail : bandOf v = band ∧ cut < cellIndex v
      · simpa only [if_pos htail] using hpointwise v
      · simp [htail]

/-- Consequently the literal two-port load is bounded by the explicit
pointwise tail majorant.  The cell denominator is never replaced by an
analytic lower bound here. -/
theorem tangentRatioCellUniformPortLoad_le_pointwisePortUpper
    {V Band : Type*} [Fintype V] [DecidableEq Band]
    (residual pointwiseUpper : V -> Real)
    (bandOf : V -> Band) (cellIndex : V -> Nat)
    (hbalance : forall band,
      (∑ v : V, if bandOf v = band then residual v else 0) = 0)
    (hpointwise : forall v, |residual v| <= pointwiseUpper v)
    (v : V) :
    tangentRatioCellUniformPortLoad residual bandOf cellIndex v <=
      tangentRatioCellPointwisePortUpper
        pointwiseUpper bandOf cellIndex v := by
  unfold tangentRatioCellUniformPortLoad
    tangentRatioCellPointwisePortUpper tangentRatioCellLeftPrefixMass
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  by_cases hcell : cellIndex v = 0
  · simp only [hcell, if_true, abs_zero, zero_add]
    exact abs_tangentRatioCellPrefixMass_le_tailPointwiseUpper
      residual pointwiseUpper bandOf cellIndex hbalance hpointwise
        (bandOf v) 0
  · simp only [hcell, if_false]
    exact add_le_add
      (abs_tangentRatioCellPrefixMass_le_tailPointwiseUpper
        residual pointwiseUpper bandOf cellIndex hbalance hpointwise
          (bandOf v) (cellIndex v - 1))
      (abs_tangentRatioCellPrefixMass_le_tailPointwiseUpper
        residual pointwiseUpper bandOf cellIndex hbalance hpointwise
          (bandOf v) (cellIndex v))





/-! ## Visible hypotheses for a distributed construction -/

/- The construction estimates are deliberately *not* bundled into a
structure.  The repository audit discipline forbids hiding a claimed
traffic or incident estimate in a conclusion-bearing certificate.  Every
generic theorem below therefore displays the exact flow property that it
uses. -/

/-! ## Support, locality, and literal traffic consequences -/









/-! ## Boundary preservation for an arbitrary distributed flow -/









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



theorem bankPaperCanonicalRoundedSelectorTangentInput_residualBounds
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
    (forall band : Band,
      (∑ p : BankPaperCanonicalTangentPrime n W,
        if bandOf p = band then
          bankPaperCanonicalTangentResidual
            R certificate fixed candidates selector p
        else 0) = 0) ∧
      (forall p : BankPaperCanonicalTangentPrime n W,
        |bankPaperCanonicalTangentResidual
            R certificate fixed candidates selector p| <=
          pointwiseUpper p) ∧
      (forall band : Band, forall cut : Nat,
        |tangentRatioCellPrefixMass
            (bankPaperCanonicalTangentResidual
              R certificate fixed candidates selector)
            bandOf cellIndex band cut| <= prefixUpper band cut) := by
  exact ⟨S.2.2.2.2.1, S.2.2.2.2.2.1, S.2.2.2.2.2.2⟩

end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.TangentRatioCellEarthmover -/
section


/-!
# Explicit ratio-cell earthmover

This file implements the missing finite transport layer behind
`TangentDistributedFlowCensus`.

Inside every exponent band the occupied ratio cells are numbered
`0, ..., lastCell b`.  At the cut after cell `i` the signed prefix mass
`F_i` is spread uniformly over the complete bipartite graph joining cells
`i` and `i+1`, in the direction determined by the sign of `F_i`.  After
these boundary transports, the adjusted residual `q_p` has sum zero in
each cell.  It is transported by the canonical proportional matching from
`TangentBalancedProductFlow`.

The resulting flow is a visible formula, not a conclusion-bearing
certificate.  Its divergence, locality, traffic, and pointwise incident
estimates are theorems.  In particular, no final collision smallness bound
is assumed or stored here.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

noncomputable section

/-! ## Uniform cell weights and one boundary cut -/







































/-! ## Finite-sum linearity for flows -/







/-! ## All canonical cuts in one finite band family -/









/-! ## Prefix algebra and exact boundary divergence -/























/-! ## The balanced residual inside each cell -/































/-! ## Support locality -/











/-! ## The complete explicit earthmover -/

































/-! ## From full vertex incident mass to the positive-support census -/















/-- Prefix bounds from the rounded selector immediately bound the visible
canonical cut ledger. -/
theorem tangentRatioCellCanonicalCutTraffic_le_prefixUpper
    {V Band : Type*} [Fintype V] [Fintype Band] [DecidableEq Band]
    (lastCell : Band -> Nat) (residual : V -> Real)
    (bandOf : V -> Band) (cellIndex : V -> Nat)
    (prefixUpper : Band -> Nat -> Real)
    (hprefix : forall band cut,
      |tangentRatioCellPrefixMass residual bandOf cellIndex band cut| <=
        prefixUpper band cut) :
    tangentRatioCellCanonicalCutTraffic
        lastCell residual bandOf cellIndex <=
      ∑ band : Band, ∑ cut ∈ Finset.range (lastCell band),
        prefixUpper band cut := by
  unfold tangentRatioCellCanonicalCutTraffic
  exact Finset.sum_le_sum fun band _hband =>
    Finset.sum_le_sum fun cut _hcut => hprefix band cut

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



/-- Clean-list endpoints lie in the literal raw selector candidate set.
This is the exact candidate-closure fact needed by `tangentUpdate`. -/
theorem tangentSplitCleanMultiplier_endpoints_mem_roughRawCandidateSet
    {E : Type*} {edges : Finset E} {source target : E → ℕ}
    {L sigma : ℝ} {flow : E → ℝ}
    {n K h Phead X0 y : ℕ}
    {dedicatedRows numericalGuards : Finset ℕ}
    (request : TangentSplitRequest edges L sigma flow) {multiplier : ℕ}
    (hsourcePos : 0 < tangentSplitRequestSource source request)
    (htargetPos : 0 < tangentSplitRequestTarget target request)
    (hKh : K * h ≤ n)
    (hmultiplier : multiplier ∈
      tangentSplitCleanMultiplierLists edges source target L sigma flow
        n K h Phead X0 y dedicatedRows numericalGuards request) :
    tangentSplitRequestSource source request * multiplier ∈
        roughRawCandidateSet n h K ∧
      tangentSplitRequestTarget target request * multiplier ∈
        roughRawCandidateSet n h K := by
  let s := tangentSplitRequestSource source request
  let t := tangentSplitRequestTarget target request
  have hclean : multiplier ∈ tangentCleanCommonMultiplierList
      n K h Phead X0 y (max s t) (min s t)
        dedicatedRows numericalGuards := by
    simpa only [tangentSplitCleanMultiplierLists,
      tangentCleanMultiplierLists, s, t] using hmultiplier
  have hinterval : multiplier ∈
      tangentCommonMultiplierInterval n K h (max s t) (min s t) :=
    mem_tangentCommonMultiplierInterval.mpr
      (mem_tangentCleanCommonMultiplierList.mp hclean).1
  have hmaxPos : 0 < max s t :=
    hsourcePos.trans_le (le_max_left _ _)
  have hminPos : 0 < min s t := lt_min hsourcePos htargetPos
  have hendpoints := tangentCommonMultiplierInterval_endpoints
    hmaxPos hminPos min_le_max hinterval
  have hsIoc : s * multiplier ∈
      Finset.Ioc n (tangentBroadUpper n K h) := by
    rcases le_total s t with hst | hts
    · simpa only [min_eq_left hst] using hendpoints.2
    · simpa only [max_eq_left hts] using hendpoints.1
  have htIoc : t * multiplier ∈
      Finset.Ioc n (tangentBroadUpper n K h) := by
    rcases le_total s t with hst | hts
    · simpa only [max_eq_right hst] using hendpoints.1
    · simpa only [min_eq_right hts] using hendpoints.2
  rw [roughRawCandidateSet_eq_Ioc hKh]
  constructor
  · exact Finset.mem_Ioc.mpr
      ⟨(Finset.mem_Ioc.mp hsIoc).1,
        (Finset.mem_Ioc.mp hsIoc).2.trans
          (tangentBroadUpper_le_two_mul n K h)⟩
  · exact Finset.mem_Ioc.mpr
      ⟨(Finset.mem_Ioc.mp htIoc).1,
        (Finset.mem_Ioc.mp htIoc).2.trans
          (tangentBroadUpper_le_two_mul n K h)⟩



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





/-- A clean multiplier has both endpoints in the guarded candidate set when
that set is literally the raw universe minus the same numerical guards used
in the clean list.

This is the only place where guard avoidance is turned into candidate
membership.  The conclusion follows from `Finset.mem_sdiff`; it is not a
disjointness consequence of raw-set containment. -/
theorem tangentSplitCleanMultiplier_endpoints_mem_guardedCandidates
    {E : Type*} {edges : Finset E} {source target : E → Nat}
    {L sigma : Real} {flow : E → Real}
    {n K h Phead X0 y : Nat}
    {dedicatedRows numericalGuards : Finset Nat}
    (request : TangentSplitRequest edges L sigma flow) {multiplier : Nat}
    (hsourcePos : 0 < tangentSplitRequestSource source request)
    (htargetPos : 0 < tangentSplitRequestTarget target request)
    (hKh : K * h ≤ n)
    (hmultiplier : multiplier ∈
      tangentSplitCleanMultiplierLists edges source target L sigma flow
        n K h Phead X0 y dedicatedRows numericalGuards request) :
    tangentSplitRequestSource source request * multiplier ∈
        bankPaperCanonicalDistributedGuardedCandidates
          n h K numericalGuards ∧
      tangentSplitRequestTarget target request * multiplier ∈
        bankPaperCanonicalDistributedGuardedCandidates
          n h K numericalGuards := by
  let s := tangentSplitRequestSource source request
  let t := tangentSplitRequestTarget target request
  have hraw := tangentSplitCleanMultiplier_endpoints_mem_roughRawCandidateSet
    request hsourcePos htargetPos hKh hmultiplier
  have hclean : multiplier ∈ tangentCleanCommonMultiplierList
      n K h Phead X0 y (max s t) (min s t)
        dedicatedRows numericalGuards := by
    simpa only [tangentSplitCleanMultiplierLists,
      tangentCleanMultiplierLists, s, t] using hmultiplier
  have hdata := mem_tangentCleanCommonMultiplierList.mp hclean
  have hmaxNot : max s t * multiplier ∉ numericalGuards :=
    hdata.2.2.2.2.1
  have hminNot : min s t * multiplier ∉ numericalGuards :=
    hdata.2.2.2.2.2
  have hsNot : s * multiplier ∉ numericalGuards := by
    rcases le_total s t with hst | hts
    · simpa only [min_eq_left hst] using hminNot
    · simpa only [max_eq_left hts] using hmaxNot
  have htNot : t * multiplier ∉ numericalGuards := by
    rcases le_total s t with hst | hts
    · simpa only [max_eq_right hst] using hmaxNot
    · simpa only [min_eq_right hts] using hminNot
  unfold bankPaperCanonicalDistributedGuardedCandidates
  constructor
  · exact Finset.mem_sdiff.mpr ⟨hraw.1, by simpa only [s] using hsNot⟩
  · exact Finset.mem_sdiff.mpr ⟨hraw.2, by simpa only [t] using htNot⟩

/-- Canonical distributed requests satisfy the preceding guarded endpoint
closure automatically.  This is the adapter used when the generic assembly
is instantiated with `raw candidates \ numericalGuards`. -/
theorem bankPaperCanonicalDistributed_cleanEndpoints_mem_guardedCandidates
    {n W K h Phead X0 : Nat}
    {flow : BankPaperCanonicalTangentPrime n W →
      BankPaperCanonicalTangentPrime n W → Real}
    {L sigma : Real} {dedicatedRows numericalGuards : Finset Nat}
    (hKh : K * h ≤ n)
    (request : BankPaperCanonicalDistributedTangentSplitRequest
      flow L sigma) {multiplier : Nat}
    (hmultiplier : multiplier ∈
      tangentSplitCleanMultiplierLists
        (tangentPositiveFlowEdges flow)
        (tangentStarEdgeSource bankPaperCanonicalTangentPrimeLabel)
        (tangentStarEdgeTarget bankPaperCanonicalTangentPrimeLabel)
        L sigma
        (fun edge : BankPaperCanonicalTangentPrime n W ×
            BankPaperCanonicalTangentPrime n W =>
          flow edge.1 edge.2)
        n K h Phead X0 (yNat n) dedicatedRows numericalGuards request) :
    bankPaperCanonicalDistributedTangentRequestSource request * multiplier ∈
        bankPaperCanonicalDistributedGuardedCandidates
          n h K numericalGuards ∧
      bankPaperCanonicalDistributedTangentRequestTarget request * multiplier ∈
        bankPaperCanonicalDistributedGuardedCandidates
          n h K numericalGuards := by
  have hsourcePrime :
      (bankPaperCanonicalDistributedTangentRequestSource request).Prime := by
    simpa only [bankPaperCanonicalDistributedTangentRequestSource,
      tangentSplitRequestSource, tangentSplitRequestEdge,
      tangentStarEdgeSource] using
      bankPaperCanonicalTangentPrimeLabel_prime request.1.1.1
  have htargetPrime :
      (bankPaperCanonicalDistributedTangentRequestTarget request).Prime := by
    simpa only [bankPaperCanonicalDistributedTangentRequestTarget,
      tangentSplitRequestTarget, tangentSplitRequestEdge,
      tangentStarEdgeTarget] using
      bankPaperCanonicalTangentPrimeLabel_prime request.1.1.2
  exact tangentSplitCleanMultiplier_endpoints_mem_guardedCandidates
    request hsourcePrime.pos htargetPrime.pos hKh hmultiplier

namespace BankPaperRealization

/-! ## Generic deterministic post-choice socket -/



/-! ## Generic finite distributed assembly -/



end BankPaperRealization

end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankPaperCanonicalPrefixQuadrature -/
section


/-!
# Harmonic-prime majorants for the canonical prefix adapter

The prefix adapter reduces a signed ratio-cell prefix to the strict tail of
the declared pointwise residual bound.  In the paper that bound is a fixed
nonnegative scale times `1 / p`.  This file performs the remaining analytic
step from literal finite tails to the verified uniform Mertens estimate.

No distribution assertion about the ratio cells is built into the result.
The only geometric input says that every prime in a declared strict tail
lies in an explicit numerical interval `(A,Y]`.  The tail can be an arbitrary
subset of that interval; positivity then permits comparison with the full
prime harmonic sum.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel
open Erdos390.Full.PrimeSums
open Erdos390.Full.PrimeBandQuadrature

noncomputable section



/-- Multiplying the paper pointwise majorant by its literal prime label
recovers the prime-independent scale exactly. -/
theorem bankPaperCanonicalTangentPrimeLabel_mul_harmonicPointwiseUpper
    {n W : Nat} (scale : Real)
    (p : BankPaperCanonicalTangentPrime n W) :
    (bankPaperCanonicalTangentPrimeLabel p : Real) *
        bankPaperCanonicalHarmonicPointwiseUpper scale p = scale := by
  have hp : (bankPaperCanonicalTangentPrimeLabel p : Real) ≠ 0 := by
    exact_mod_cast
      (bankPaperCanonicalTangentPrimeLabel_prime p).pos.ne'
  unfold bankPaperCanonicalHarmonicPointwiseUpper
  field_simp [hp]



-- `WholePaper` also has a distinct presentation of `primesUpTo`; the
-- qualification here keeps this set definitionally aligned with
-- `Full.PrimeSums.fullReciprocalSum`.
private theorem bankPaperCanonical_primesUpTo_mono
    {A Y : Nat} (hAY : A <= Y) :
    Erdos390.Full.PrimeSums.primesUpTo A ⊆
      Erdos390.Full.PrimeSums.primesUpTo Y := by
  intro p hp
  simp only [Erdos390.Full.PrimeSums.primesUpTo,
    Finset.mem_filter, Finset.mem_Icc] at hp ⊢
  exact ⟨⟨hp.1.1, hp.1.2.trans hAY⟩, hp.2⟩

private theorem bankPaperCanonical_reciprocalPrimeInterval_eq_sub
    {A Y : Nat} (hAY : A <= Y) :
    (∑ p ∈ Erdos390.Full.PrimeSums.primesUpTo Y \
        Erdos390.Full.PrimeSums.primesUpTo A, 1 / (p : Real)) =
      fullReciprocalSum Y - fullReciprocalSum A := by
  have hsub := bankPaperCanonical_primesUpTo_mono hAY
  have hsum := Finset.sum_sdiff hsub
    (f := fun p : Nat => 1 / (p : Real))
  unfold fullReciprocalSum
  exact (eq_sub_iff_add_eq).2 hsum

/-- An arbitrary strict ratio-cell tail with pointwise bound `scale / p` is
bounded by the full harmonic prime mass of any numerical interval containing
that tail.

The interval condition is deliberately one-sided: it does not assert that
the ratio-cell tail contains every prime in `(A,Y]`. -/
theorem tangentRatioCellTail_harmonicPointwiseUpper_le_fullReciprocalSum_sub
    {n W : Nat} {Band : Type*} [DecidableEq Band]
    (bandOf : BankPaperCanonicalTangentPrime n W -> Band)
    (cellIndex : BankPaperCanonicalTangentPrime n W -> Nat)
    (scale : Real) (hscale : 0 <= scale)
    (band : Band) (cut A Y : Nat) (hAY : A <= Y)
    (hgeometry : forall p : BankPaperCanonicalTangentPrime n W,
      bandOf p = band -> cut < cellIndex p ->
        A < bankPaperCanonicalTangentPrimeLabel p ∧
          bankPaperCanonicalTangentPrimeLabel p <= Y) :
    tangentRatioCellTailPointwiseUpper
        (bankPaperCanonicalHarmonicPointwiseUpper scale)
        bandOf cellIndex band cut <=
      scale * (fullReciprocalSum Y - fullReciprocalSum A) := by
  let tail : Finset (BankPaperCanonicalTangentPrime n W) :=
    Finset.univ.filter
      (fun p => bandOf p = band ∧ cut < cellIndex p)
  let labelEmbedding : BankPaperCanonicalTangentPrime n W ↪ Nat :=
    ⟨bankPaperCanonicalTangentPrimeLabel,
      bankPaperCanonicalTangentPrimeLabel_injective⟩
  let labels : Finset Nat := tail.map labelEmbedding
  have hlabels : labels ⊆
      Erdos390.Full.PrimeSums.primesUpTo Y \
        Erdos390.Full.PrimeSums.primesUpTo A := by
    intro q hq
    have hq' : q ∈ tail.map labelEmbedding := by
      simpa only [labels] using hq
    obtain ⟨p, hpTail, hpq⟩ := Finset.mem_map.mp hq'
    subst q
    have hpCondition : bandOf p = band ∧ cut < cellIndex p :=
      (Finset.mem_filter.mp hpTail).2
    have hpInterval := hgeometry p hpCondition.1 hpCondition.2
    refine Finset.mem_sdiff.mpr ⟨?_, ?_⟩
    · simp only [Erdos390.Full.PrimeSums.primesUpTo,
        Finset.mem_filter, Finset.mem_Icc]
      exact ⟨⟨Nat.zero_le _, hpInterval.2⟩,
        bankPaperCanonicalTangentPrimeLabel_prime p⟩
    · intro hpA
      simp only [Erdos390.Full.PrimeSums.primesUpTo,
        Finset.mem_filter, Finset.mem_Icc] at hpA
      exact (Nat.not_lt_of_ge hpA.1.2) hpInterval.1
  have htail :
      tangentRatioCellTailPointwiseUpper
          (bankPaperCanonicalHarmonicPointwiseUpper scale)
          bandOf cellIndex band cut =
        ∑ p ∈ tail,
          scale / (bankPaperCanonicalTangentPrimeLabel p : Real) := by
    simp only [tangentRatioCellTailPointwiseUpper,
      bankPaperCanonicalHarmonicPointwiseUpper, tail, Finset.sum_filter]
  have hmap :
      (∑ p ∈ tail,
          scale / (bankPaperCanonicalTangentPrimeLabel p : Real)) =
        ∑ q ∈ labels, scale / (q : Real) := by
    simp only [labels, Finset.sum_map]
    rfl
  have hsum :
      (∑ q ∈ labels, scale / (q : Real)) <=
        ∑ q ∈ Erdos390.Full.PrimeSums.primesUpTo Y \
            Erdos390.Full.PrimeSums.primesUpTo A,
          scale / (q : Real) := by
    exact Finset.sum_le_sum_of_subset_of_nonneg hlabels
      (fun q _hq _hnot => div_nonneg hscale (Nat.cast_nonneg q))
  calc
    tangentRatioCellTailPointwiseUpper
        (bankPaperCanonicalHarmonicPointwiseUpper scale)
        bandOf cellIndex band cut =
      ∑ p ∈ tail,
        scale / (bankPaperCanonicalTangentPrimeLabel p : Real) := htail
    _ = ∑ q ∈ labels, scale / (q : Real) := hmap
    _ <= ∑ q ∈ Erdos390.Full.PrimeSums.primesUpTo Y \
          Erdos390.Full.PrimeSums.primesUpTo A,
        scale / (q : Real) := hsum
    _ = scale *
        (∑ q ∈ Erdos390.Full.PrimeSums.primesUpTo Y \
            Erdos390.Full.PrimeSums.primesUpTo A,
          1 / (q : Real)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro q _hq
      ring
    _ = scale * (fullReciprocalSum Y - fullReciprocalSum A) := by
      rw [bankPaperCanonical_reciprocalPrimeInterval_eq_sub hAY]

/-- Uniform log-log majorant for a literal canonical strict tail.  The same
global constant and cutoff work for every band, cut, and moving endpoint
pair satisfying the displayed geometry. -/
theorem tangentRatioCellTail_harmonicPointwiseUpper_le_uniformMajorant
    {n W : Nat} {Band : Type*} [DecidableEq Band]
    (bandOf : BankPaperCanonicalTangentPrime n W -> Band)
    (cellIndex : BankPaperCanonicalTangentPrime n W -> Nat)
    (scale : Real) (hscale : 0 <= scale)
    (band : Band) (cut A Y : Nat)
    (hA : fullReciprocalSumUniformCutoff <= A) (hAY : A <= Y)
    (hgeometry : forall p : BankPaperCanonicalTangentPrime n W,
      bandOf p = band -> cut < cellIndex p ->
        A < bankPaperCanonicalTangentPrimeLabel p ∧
          bankPaperCanonicalTangentPrimeLabel p <= Y) :
    tangentRatioCellTailPointwiseUpper
        (bankPaperCanonicalHarmonicPointwiseUpper scale)
        bandOf cellIndex band cut <=
      bankPaperCanonicalHarmonicTailMajorant scale A Y := by
  have hquadrature := fullReciprocalSumUniform_bound A Y hA hAY
  have hupper :
      fullReciprocalSum Y - fullReciprocalSum A <=
        Real.log (Real.log (Y : Real)) -
            Real.log (Real.log (A : Real)) +
          5 * fullReciprocalSumUniformConstant /
            Real.log (A : Real) ^ 3 := by
    have hdeviation :
        fullReciprocalSum Y - fullReciprocalSum A -
            (Real.log (Real.log (Y : Real)) -
              Real.log (Real.log (A : Real))) <=
          |fullReciprocalSum Y - fullReciprocalSum A -
            (Real.log (Real.log (Y : Real)) -
              Real.log (Real.log (A : Real)))| :=
      le_abs_self _
    linarith
  calc
    tangentRatioCellTailPointwiseUpper
        (bankPaperCanonicalHarmonicPointwiseUpper scale)
        bandOf cellIndex band cut <=
      scale * (fullReciprocalSum Y - fullReciprocalSum A) :=
        tangentRatioCellTail_harmonicPointwiseUpper_le_fullReciprocalSum_sub
          bandOf cellIndex scale hscale band cut A Y hAY hgeometry
    _ <= scale *
        (Real.log (Real.log (Y : Real)) -
            Real.log (Real.log (A : Real)) +
          5 * fullReciprocalSumUniformConstant /
            Real.log (A : Real) ^ 3) :=
      mul_le_mul_of_nonneg_left hupper hscale
    _ = bankPaperCanonicalHarmonicTailMajorant scale A Y := rfl



end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankPaperCanonicalGuardedSectionNineContinuation -/
section


/-!
# Guarded canonical Section 9 continuation

The guarded candidate set, the candidate-parametric tangent assembly, and
the harmonic prefix adapter now fit together definitionally.  What is not
yet available is a theorem constructing the required selector on the
guarded rows from the local capacity estimates.  This module records that
remaining front end without turning it into an axiom or silently replacing
the guarded set by the raw set.

`BankPaperCanonicalGuardedSectionNineContinuation` is an explicit `Prop`.
It keeps three kinds of input visible:

* the local guard census, guarded broad-pool capacity, and guarded-row
  capacity for the active nonexceptional rough rows from the finite ledger;
* an actual feasible guarded selector with the exact postcharge targets on
  active nonexceptional rows, zero mass on exceptional rows, a separate
  integer flexible quota on the smooth row, and the prime-coordinate
  properties used before the tangent; and
* the occupied-cell and harmonic-tail geometry used by the distributed
  earthmover and the prefix quadrature.

The extraction theorem uses the paper's three row cases: the postcharge
integer target on active nonexceptional labels, the proved zero target on
exceptional labels, and an independent integer `q_sm^flex(d)` when the
label is `1`.  It then obtains the full rounded-selector tangent input
through the proved harmonic quadrature.  Separate finite adapters provide
raw-set containment and clean-list endpoint closure.  Thus the remaining
traffic, collision-census, slack, and selector-charge hypotheses of the
existing candidate assembly can be supplied directly, with no extra
selector or geometry conversion layer.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel

noncomputable section

namespace BankPaperRealization

/-! ## The literal guarded set as a distributed candidate set -/

/-- The guard-local ledger and the candidate-parametric tangent use the
same literal set difference when the numerical guards are the actual paper
guards. -/
theorem roughCanonicalGuardedCandidateSet_eq_distributedGuardedCandidates
    {c : Real} {depth n K : Nat}
    (R : BankPaperRealization n
      (upperEndpoint n (upperTailLength c n)))
    (certificate : GuardedCentralAnchorCertificate c depth n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (deltaStar : Real) :
    R.roughCanonicalGuardedCandidateSet certificate deltaStar K =
      bankPaperCanonicalDistributedGuardedCandidates n
        (upperTailLength c n) K
        (R.tangentPaperNumericalGuardSet certificate
          (R.paperFixedExceptionalFactors deltaStar)) := by
  rfl

/-- Every clean common multiplier has both endpoints in the literal
guard-local candidate set.  This is the exact endpoint-closure premise of
the candidate-parametric distributed assembly. -/
theorem roughCanonicalGuardedCandidateSet_cleanEndpoints
    {c : Real} {depth n W K Phead X0 : Nat}
    (R : BankPaperRealization n
      (upperEndpoint n (upperTailLength c n)))
    (certificate : GuardedCentralAnchorCertificate c depth n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (deltaStar : Real)
    {flow : BankPaperCanonicalTangentPrime n W ->
      BankPaperCanonicalTangentPrime n W -> Real}
    {L sigma : Real}
    (hKh : K * upperTailLength c n <= n)
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
        n K (upperTailLength c n) Phead X0 (yNat n)
        R.tangentPaperDedicatedRows
        (R.tangentPaperNumericalGuardSet certificate
          (R.paperFixedExceptionalFactors deltaStar)) request) :
    bankPaperCanonicalDistributedTangentRequestSource request * common ∈
        R.roughCanonicalGuardedCandidateSet certificate deltaStar K ∧
      bankPaperCanonicalDistributedTangentRequestTarget request * common ∈
        R.roughCanonicalGuardedCandidateSet certificate deltaStar K := by
  simpa only [
      R.roughCanonicalGuardedCandidateSet_eq_distributedGuardedCandidates
        (K := K) certificate deltaStar] using
    (bankPaperCanonicalDistributed_cleanEndpoints_mem_guardedCandidates
      (n := n) (W := W) (K := K) (h := upperTailLength c n)
      (Phead := Phead) (X0 := X0)
      (dedicatedRows := R.tangentPaperDedicatedRows)
      (numericalGuards := R.tangentPaperNumericalGuardSet certificate
        (R.paperFixedExceptionalFactors deltaStar))
      hKh request hcommon)

/-! ## Explicit remaining continuation input -/







/-! ## Projections into the existing APIs -/







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





/-- On the guarded broad pool, the explicit corrected weight is the broad
raw value `beta / L` plus the single rowwise correction density. -/
theorem roughCanonicalGuardedPostchargeRowCorrectedWeight_apply_of_mem
    {c : Real} {depth n W K label : Nat}
    {R : BankPaperRealization n
      (upperEndpoint n (upperTailLength c n))}
    {certificate : GuardedCentralAnchorCertificate c depth n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth)}
    {deltaStar alpha beta L : Real} {a : Nat}
    (ha : a ∈ R.roughCanonicalGuardedBroadCorrectionPool certificate
      deltaStar W K label) :
    R.roughCanonicalGuardedPostchargeRowCorrectedWeight certificate
        deltaStar W K label alpha beta L a =
      beta / L +
        R.roughCanonicalGuardedPostchargeCorrectionDensity certificate
          deltaStar W K label alpha beta L := by
  rw [roughCanonicalGuardedPostchargeRowCorrectedWeight,
    bankPaperConstantPoolCorrection_apply_of_mem ha,
    roughHeadCompatibleRawWeight_eq_broad_of_mem_correctionPool
      (R.roughCanonicalGuardedBroadCorrectionPool_subset_broadPool
        certificate deltaStar W K label ha),
    roughCanonicalGuardedPostchargeCorrectionDensity]

/-- The paper's absolute correction-density bounds leave the exact
two-sided tangent margin on every guarded broad coordinate. -/
theorem roughCanonicalGuardedPostchargeRowCorrectedWeight_twoSidedSlack
    {c : Real} {depth n W K label : Nat}
    {R : BankPaperRealization n
      (upperEndpoint n (upperTailLength c n))}
    {certificate : GuardedCentralAnchorCertificate c depth n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth)}
    {deltaStar alpha beta L sigma : Real} {a : Nat}
    (hfloor :
      sigma / L +
          |R.roughCanonicalGuardedPostchargeCorrectionDensity certificate
            deltaStar W K label alpha beta L| ≤
        beta / L)
    (hceiling :
      beta / L +
          |R.roughCanonicalGuardedPostchargeCorrectionDensity certificate
            deltaStar W K label alpha beta L| ≤
        1 - sigma / L)
    (ha : a ∈ R.roughCanonicalGuardedBroadCorrectionPool certificate
      deltaStar W K label) :
    sigma / L ≤
        R.roughCanonicalGuardedPostchargeRowCorrectedWeight certificate
          deltaStar W K label alpha beta L a ∧
      R.roughCanonicalGuardedPostchargeRowCorrectedWeight certificate
          deltaStar W K label alpha beta L a ≤
        1 - sigma / L := by
  let d := R.roughCanonicalGuardedPostchargeCorrectionDensity certificate
    deltaStar W K label alpha beta L
  have hdLower : -|d| ≤ d := neg_abs_le d
  have hdUpper : d ≤ |d| := le_abs_self d
  rw [R.roughCanonicalGuardedPostchargeRowCorrectedWeight_apply_of_mem ha]
  change sigma / L ≤ beta / L + d ∧
    beta / L + d ≤ 1 - sigma / L
  change sigma / L + |d| ≤ beta / L at hfloor
  change beta / L + |d| ≤ 1 - sigma / L at hceiling
  constructor <;> linarith

/-! ## Clean endpoints lie in the appropriate guarded broad pool -/



/-! ## The isolated protected/corrected-selector construction output -/



/-- Either branch of the construction proposition gives two-sided slack on
one guarded broad coordinate. -/
theorem guardedEndpointSlackConstruction_twoSidedSlack_of_mem
    {c : Real} {depth n W K label : Nat}
    {R : BankPaperRealization n
      (upperEndpoint n (upperTailLength c n))}
    {certificate : GuardedCentralAnchorCertificate c depth n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth)}
    {deltaStar alpha beta L sigma : Real} {selector : Nat -> Real}
    (H : R.BankPaperCanonicalGuardedEndpointSlackConstruction certificate
      deltaStar W K alpha beta L sigma selector)
    {a : Nat}
    (ha : a ∈ R.roughCanonicalGuardedBroadCorrectionPool certificate
      deltaStar W K label)
    (hcase : label = 1 ∨
      RoughCanonicalActiveNonexceptionalLabel n deltaStar label) :
    sigma / L ≤ selector a ∧ selector a ≤ 1 - sigma / L := by
  rcases hcase with hlabel | hactiveLabel
  · subst label
    obtain ⟨protectedPart, active, hsmooth⟩ := H.1
    obtain ⟨hselector, hfloor, hactive, hceiling⟩ := hsmooth a ha
    rw [hselector]
    constructor <;> linarith
  · obtain ⟨hfloor, hceiling, hselector⟩ := H.2 label hactiveLabel
    rw [hselector a ha]
    exact R.roughCanonicalGuardedPostchargeRowCorrectedWeight_twoSidedSlack
      hfloor hceiling ha

/-! ## Adapter to the candidate-parametric distributed tangent -/

/-- The isolated construction output supplies the exact request-wise
two-sided slack premise of the distributed candidate-set assembly. -/
theorem guardedEndpointSlackConstruction_cleanMultiplierSlack
    {c : Real} {depth n W K : Nat}
    (R : BankPaperRealization n
      (upperEndpoint n (upperTailLength c n)))
    (certificate : GuardedCentralAnchorCertificate c depth n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (deltaStar alpha beta : Real)
    {flow : BankPaperCanonicalTangentPrime n W ->
      BankPaperCanonicalTangentPrime n W -> Real}
    {L sigma : Real} (selector : Nat -> Real)
    (H : R.BankPaperCanonicalGuardedEndpointSlackConstruction certificate
      deltaStar W K alpha beta L sigma selector)
    (request : BankPaperCanonicalDistributedTangentSplitRequest
      flow L sigma) (common : Nat)
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
    (sigma / L ≤ selector
          (bankPaperCanonicalDistributedTangentRequestSource request *
            common) ∧
        selector
          (bankPaperCanonicalDistributedTangentRequestSource request *
            common) ≤ 1 - sigma / L) ∧
      (sigma / L ≤ selector
          (bankPaperCanonicalDistributedTangentRequestTarget request *
            common) ∧
        selector
          (bankPaperCanonicalDistributedTangentRequestTarget request *
            common) ≤ 1 - sigma / L) := by
  have hendpoints := R.canonicalDistributedCleanMultiplier_guardedBroadEndpoints
    certificate deltaStar request hcommon
  let label := completeRoughLabel (yNat n) common
  have hcase : label = 1 ∨
      RoughCanonicalActiveNonexceptionalLabel n deltaStar label := by
    by_cases hlabel : label = 1
    · exact Or.inl hlabel
    · exact Or.inr (hendpoints.2 (by simpa only [label] using hlabel))
  constructor
  · apply R.guardedEndpointSlackConstruction_twoSidedSlack_of_mem H
      (label := label)
    · simpa only [label] using hendpoints.1.1
    · exact hcase
  · apply R.guardedEndpointSlackConstruction_twoSidedSlack_of_mem H
      (label := label)
    · simpa only [label] using hendpoints.1.2
    · exact hcase

/-- Ready-to-use pair of endpoint inputs for
`exists_canonicalDistributedSectionNinePostTangentOutput_of_paperBudgets_on_candidates`:
clean endpoints remain in the literal guarded candidate set, and every
allowed clean multiplier has the required two-sided selector slack. -/
theorem guardedEndpointSlackConstruction_candidateSetEndpointInputs
    {c : Real} {depth n W K : Nat}
    (R : BankPaperRealization n
      (upperEndpoint n (upperTailLength c n)))
    (certificate : GuardedCentralAnchorCertificate c depth n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (deltaStar alpha beta : Real)
    {flow : BankPaperCanonicalTangentPrime n W ->
      BankPaperCanonicalTangentPrime n W -> Real}
    {L sigma : Real} (selector : Nat -> Real)
    (hKh : K * upperTailLength c n ≤ n)
    (H : R.BankPaperCanonicalGuardedEndpointSlackConstruction certificate
      deltaStar W K alpha beta L sigma selector) :
    (∀ request : BankPaperCanonicalDistributedTangentSplitRequest
        flow L sigma,
      ∀ {common : Nat},
        common ∈
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
                (R.paperFixedExceptionalFactors deltaStar)) request ->
          bankPaperCanonicalDistributedTangentRequestSource request * common ∈
              R.roughCanonicalGuardedCandidateSet certificate deltaStar K ∧
            bankPaperCanonicalDistributedTangentRequestTarget request *
                common ∈
              R.roughCanonicalGuardedCandidateSet certificate deltaStar K) ∧
      (∀ request : BankPaperCanonicalDistributedTangentSplitRequest
          flow L sigma,
        ∀ common : Nat,
          common ∈
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
                  (R.paperFixedExceptionalFactors deltaStar)) request ->
            (sigma / L ≤ selector
                  (bankPaperCanonicalDistributedTangentRequestSource request *
                    common) ∧
              selector
                  (bankPaperCanonicalDistributedTangentRequestSource request *
                    common) ≤ 1 - sigma / L) ∧
            (sigma / L ≤ selector
                  (bankPaperCanonicalDistributedTangentRequestTarget request *
                    common) ∧
              selector
                  (bankPaperCanonicalDistributedTangentRequestTarget request *
                    common) ≤ 1 - sigma / L)) := by
  constructor
  · intro request common hcommon
    exact R.roughCanonicalGuardedCandidateSet_cleanEndpoints certificate
      deltaStar hKh request hcommon
  · intro request common hcommon
    exact R.guardedEndpointSlackConstruction_cleanMultiplierSlack
      certificate deltaStar alpha beta selector H request common hcommon

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





theorem tangentMultiplicativeRatioCutoff_mono
    {lower : Nat} {rho : Real} (hrho : 1 <= rho) :
    Monotone (tangentMultiplicativeRatioCutoff lower rho) := by
  intro i j hij
  unfold tangentMultiplicativeRatioCutoff
  apply Nat.floor_mono
  apply mul_le_mul_of_nonneg_left
  · exact pow_le_pow_right₀ (by linarith) hij
  · exact Nat.cast_nonneg lower





theorem label_le_tangentMultiplicativeRatioCutoff_rawCell_succ
    {lower label : Nat} {rho : Real}
    (hlower : 0 < lower) (hrho : 1 < rho) :
    label <= tangentMultiplicativeRatioCutoff lower rho
      (tangentMultiplicativeRawCellIndex lower label rho + 1) := by
  unfold tangentMultiplicativeRawCellIndex
  rw [dif_pos ⟨hlower, hrho⟩]
  exact Nat.find_spec
    (exists_label_le_tangentMultiplicativeRatioCutoff_succ
      hlower hrho label)

theorem tangentMultiplicativeRatioCutoff_rawCell_lt_label
    {lower label : Nat} {rho : Real}
    (hlower : 0 < lower) (hrho : 1 < rho) (hlabel : lower < label) :
    tangentMultiplicativeRatioCutoff lower rho
        (tangentMultiplicativeRawCellIndex lower label rho) < label := by
  let H := exists_label_le_tangentMultiplicativeRatioCutoff_succ
    hlower hrho label
  unfold tangentMultiplicativeRawCellIndex
  rw [dif_pos ⟨hlower, hrho⟩]
  by_cases hk : Nat.find H = 0
  · simpa only [hk, tangentMultiplicativeRatioCutoff_zero] using hlabel
  · have hkone : 1 <= Nat.find H := Nat.one_le_iff_ne_zero.mpr hk
    have hminimal := Nat.find_min H
      (m := Nat.find H - 1) (Nat.sub_one_lt hk)
    have hpred : Nat.find H - 1 + 1 = Nat.find H :=
      Nat.sub_add_cancel hkone
    rw [hpred] at hminimal
    exact Nat.lt_of_not_ge hminimal

theorem tangentMultiplicativeRawCellIndex_mono
    {lower x y : Nat} {rho : Real}
    (hlower : 0 < lower) (hrho : 1 < rho) (hxy : x <= y) :
    tangentMultiplicativeRawCellIndex lower x rho <=
      tangentMultiplicativeRawCellIndex lower y rho := by
  unfold tangentMultiplicativeRawCellIndex
  rw [dif_pos ⟨hlower, hrho⟩, dif_pos ⟨hlower, hrho⟩]
  apply Nat.find_min'
    (exists_label_le_tangentMultiplicativeRatioCutoff_succ
      hlower hrho x)
  exact hxy.trans
    (Nat.find_spec
      (exists_label_le_tangentMultiplicativeRatioCutoff_succ
        hlower hrho y))



theorem tangentMultiplicativeRawCell_real_lower_lt
    {lower label : Nat} {rho : Real}
    (hlower : 0 < lower) (hrho : 1 < rho) (hlabel : lower < label) :
    (lower : Real) *
        rho ^ tangentMultiplicativeRawCellIndex lower label rho <
      (label : Real) := by
  have hnat := tangentMultiplicativeRatioCutoff_rawCell_lt_label
    hlower hrho hlabel
  exact (Nat.floor_lt (mul_nonneg (Nat.cast_nonneg lower)
    (pow_nonneg (by linarith) _))).mp hnat

theorem tangentMultiplicativeRawCell_real_upper
    {lower label : Nat} {rho : Real}
    (hlower : 0 < lower) (hrho : 1 < rho) :
    (label : Real) <= (lower : Real) *
      rho ^ (tangentMultiplicativeRawCellIndex lower label rho + 1) := by
  have hnat :=
    label_le_tangentMultiplicativeRatioCutoff_rawCell_succ
      hlower hrho (label := label)
  have hcast : (label : Real) <=
      (tangentMultiplicativeRatioCutoff lower rho
        (tangentMultiplicativeRawCellIndex lower label rho + 1) : Nat) := by
    exact_mod_cast hnat
  exact hcast.trans (Nat.floor_le
    (mul_nonneg (Nat.cast_nonneg lower) (pow_nonneg (by linarith) _)))

/-! ## Merging the terminal fragment -/





theorem tangentMergedRatioCellIndex_le_lastCell
    (lastRaw raw : Nat) :
    tangentMergedRatioCellIndex lastRaw raw <=
      tangentMergedRatioLastCell lastRaw := by
  exact Nat.min_le_right _ _

theorem tangentMergedRatioCellIndex_le_raw
    (lastRaw raw : Nat) :
    tangentMergedRatioCellIndex lastRaw raw <= raw := by
  exact Nat.min_le_left _ _

theorem tangentMergedRatioCellIndex_eq_self
    {lastRaw raw : Nat} (hraw : raw <= tangentMergedRatioLastCell lastRaw) :
    tangentMergedRatioCellIndex lastRaw raw = raw := by
  exact Nat.min_eq_left hraw



theorem raw_le_tangentMergedRatioCellIndex_add_one
    {lastRaw raw : Nat} (hraw : raw <= lastRaw) :
    raw <= tangentMergedRatioCellIndex lastRaw raw + 1 := by
  by_cases hfull : raw <= lastRaw - 1
  · rw [tangentMergedRatioCellIndex_eq_self hfull]
    omega
  · have hcap : lastRaw - 1 <= raw := by omega
    unfold tangentMergedRatioCellIndex
    rw [Nat.min_eq_right hcap]
    omega



/-- Same or adjacent merged cells come from raw indices at distance at most
two.  The extra unit is precisely the possible terminal merge. -/
theorem rawCellIndices_within_two_of_merged_sameOrAdjacent
    {lastRaw a b : Nat} (ha : a <= lastRaw) (hb : b <= lastRaw)
    (hcell :
      tangentMergedRatioCellIndex lastRaw a =
          tangentMergedRatioCellIndex lastRaw b ∨
        tangentMergedRatioCellIndex lastRaw a + 1 =
          tangentMergedRatioCellIndex lastRaw b ∨
        tangentMergedRatioCellIndex lastRaw b + 1 =
          tangentMergedRatioCellIndex lastRaw a) :
    a <= b + 2 ∧ b <= a + 2 := by
  have haUpper := raw_le_tangentMergedRatioCellIndex_add_one ha
  have hbUpper := raw_le_tangentMergedRatioCellIndex_add_one hb
  have haLower := tangentMergedRatioCellIndex_le_raw lastRaw a
  have hbLower := tangentMergedRatioCellIndex_le_raw lastRaw b
  rcases hcell with hsame | hforward | hbackward <;> omega

/-- If two labels have raw indices at distance at most two in this
orientation, their ratio is strictly below `rho^3`. -/
theorem tangentMultiplicativeRawCell_ratio_lt_cube
    {lower x y : Nat} {rho : Real}
    (hlower : 0 < lower) (hrho : 1 < rho)
    (_hxLower : lower < x) (hyLower : lower < y)
    (hindex : tangentMultiplicativeRawCellIndex lower x rho <=
      tangentMultiplicativeRawCellIndex lower y rho + 2) :
    (x : Real) / (y : Real) < rho ^ 3 := by
  let ix := tangentMultiplicativeRawCellIndex lower x rho
  let iy := tangentMultiplicativeRawCellIndex lower y rho
  have hxUpper : (x : Real) <= (lower : Real) * rho ^ (ix + 1) := by
    simpa only [ix] using
      (tangentMultiplicativeRawCell_real_upper
        hlower hrho (label := x))
  have hyLowerReal : (lower : Real) * rho ^ iy < (y : Real) := by
    simpa only [iy] using
      (tangentMultiplicativeRawCell_real_lower_lt
        hlower hrho hyLower)
  have hpow : rho ^ (ix + 1) <= rho ^ (iy + 3) := by
    apply pow_le_pow_right₀ (by linarith)
    dsimp only [ix, iy]
    omega
  have hxToBoundary : (x : Real) <=
      (lower : Real) * rho ^ (iy + 3) :=
    hxUpper.trans
      (mul_le_mul_of_nonneg_left hpow (Nat.cast_nonneg lower))
  have hrhoCubePos : 0 < rho ^ 3 := pow_pos (by linarith) _
  have hboundary : (lower : Real) * rho ^ (iy + 3) <
      (y : Real) * rho ^ 3 := by
    rw [show iy + 3 = iy + 3 by rfl, pow_add]
    simpa only [mul_assoc] using
      (mul_lt_mul_of_pos_right hyLowerReal hrhoCubePos)
  have hyPos : (0 : Real) < y := by
    exact_mod_cast (hlower.trans hyLower)
  rw [div_lt_iff₀ hyPos]
  calc
    (x : Real) <= (lower : Real) * rho ^ (iy + 3) := hxToBoundary
    _ < (y : Real) * rho ^ 3 := hboundary
    _ = rho ^ 3 * (y : Real) := mul_comm _ _

/-! ## The canonical paper exponent bands -/









theorem bankPaperCanonicalExponentBandOf_mem_interval
    {delta eta : Real} (M : RegularRelativeMesh.Mesh delta eta)
    {n W : Nat} (hdelta : 0 < delta) (hn : 1 < n)
    (hW : W ≠ 0) (S : ScaleSeparation M n W)
    (p : BankPaperCanonicalTangentPrime n W) :
    bankPaperCanonicalExponentBandLower M n W
        (bankPaperCanonicalExponentBandOf M hdelta hn hW S p) < p.1 ∧
      p.1 <= bankPaperCanonicalExponentBandUpper M n W
        (bankPaperCanonicalExponentBandOf M hdelta hn hW S p) := by
  let P := RegularMeshPrimeCutoffs.Mesh.canonicalPartition
    M hdelta hn hW S
  let E := RegularMeshPrimeCutoffs.Mesh.canonicalCertificate
    M hdelta hn hW S
  have hp := (E.band_eq_iff p (P.band p)).mp rfl
  simpa only [P, E, bankPaperCanonicalExponentBandOf,
    bankPaperCanonicalExponentBandLower,
    bankPaperCanonicalExponentBandUpper,
    RegularMeshPrimeCutoffs.Mesh.canonicalCertificate_lower,
    RegularMeshPrimeCutoffs.Mesh.canonicalCertificate_upper] using hp

theorem bankPaperCanonicalExponentBandLower_pos
    {delta eta : Real} (M : RegularRelativeMesh.Mesh delta eta)
    {n W : Nat} (hdelta : 0 < delta) (hn : 1 < n)
    (hW : W ≠ 0) (S : ScaleSeparation M n W)
    (band : BankPaperCanonicalExponentBand M) :
    0 < bankPaperCanonicalExponentBandLower M n W band := by
  have hcut :=
    (RegularMeshPrimeCutoffs.Mesh.canonicalCertificate
      M hdelta hn hW S).cutoff_le_lower band
  have hWpos : 0 < W := Nat.pos_of_ne_zero hW
  simpa only [bankPaperCanonicalExponentBandLower,
    RegularMeshPrimeCutoffs.Mesh.canonicalCertificate_lower] using
      hWpos.trans_le hcut









/-- Every raw prime cell lies before the raw terminal fragment. -/
theorem bankPaperCanonicalRawRatioCellIndex_le_lastRaw
    {delta eta : Real} (M : RegularRelativeMesh.Mesh delta eta)
    {n W : Nat} (hdelta : 0 < delta) (hn : 1 < n)
    (hW : W ≠ 0) (S : ScaleSeparation M n W)
    (rho : Real) (hrho : 1 < rho)
    (p : BankPaperCanonicalTangentPrime n W) :
    bankPaperCanonicalRawRatioCellIndex M hdelta hn hW S rho p <=
      bankPaperCanonicalLastRawRatioCell M (n := n) (W := W) rho
        (bankPaperCanonicalExponentBandOf M hdelta hn hW S p) := by
  let band := bankPaperCanonicalExponentBandOf M hdelta hn hW S p
  have hlower := bankPaperCanonicalExponentBandLower_pos
    M hdelta hn hW S band
  have hpUpper :=
    (bankPaperCanonicalExponentBandOf_mem_interval
      M hdelta hn hW S p).2
  exact tangentMultiplicativeRawCellIndex_mono
    hlower hrho hpUpper

/-- Finite tail coverage in the exact shape required by
`tangentRatioCellEarthmoverFlow`. -/
theorem bankPaperCanonicalRatioCellIndex_le_lastCell
    {delta eta : Real} (M : RegularRelativeMesh.Mesh delta eta)
    {n W : Nat} (hdelta : 0 < delta) (hn : 1 < n)
    (hW : W ≠ 0) (S : ScaleSeparation M n W)
    (rho : Real) (p : BankPaperCanonicalTangentPrime n W) :
    bankPaperCanonicalRatioCellIndex M hdelta hn hW S rho p <=
      bankPaperCanonicalLastRatioCell M (n := n) (W := W) rho
        (bankPaperCanonicalExponentBandOf M hdelta hn hW S p) := by
  exact tangentMergedRatioCellIndex_le_lastCell _ _



/-- Same or adjacent canonical merged cells have label ratio below
`rho^3`. -/
theorem bankPaperCanonical_sameOrAdjacentRatioCell_ratio_lt_cube
    {delta eta : Real} (M : RegularRelativeMesh.Mesh delta eta)
    {n W : Nat} (hdelta : 0 < delta) (hn : 1 < n)
    (hW : W ≠ 0) (S : ScaleSeparation M n W)
    {rho : Real} (hrho : 1 < rho)
    {source target : BankPaperCanonicalTangentPrime n W}
    (hcell : TangentSameOrAdjacentRatioCell
      (bankPaperCanonicalExponentBandOf M hdelta hn hW S)
      (bankPaperCanonicalRatioCellIndex M hdelta hn hW S rho)
      source target) :
    (((max (bankPaperCanonicalTangentPrimeLabel source)
          (bankPaperCanonicalTangentPrimeLabel target) : Nat) : Real) /
      ((min (bankPaperCanonicalTangentPrimeLabel source)
          (bankPaperCanonicalTangentPrimeLabel target) : Nat) : Real)) <
        rho ^ 3 := by
  let band := bankPaperCanonicalExponentBandOf M hdelta hn hW S source
  let lower := bankPaperCanonicalExponentBandLower M n W band
  let lastRaw := bankPaperCanonicalLastRawRatioCell M
    (n := n) (W := W) rho band
  let sourceRaw :=
    bankPaperCanonicalRawRatioCellIndex M hdelta hn hW S rho source
  let targetRaw :=
    bankPaperCanonicalRawRatioCellIndex M hdelta hn hW S rho target
  have hband : band =
      bankPaperCanonicalExponentBandOf M hdelta hn hW S target := hcell.1
  have hlower : 0 < lower := by
    exact bankPaperCanonicalExponentBandLower_pos
      M hdelta hn hW S band
  have hsourceLower : lower < source.1 := by
    simpa only [band, lower] using
      (bankPaperCanonicalExponentBandOf_mem_interval
        M hdelta hn hW S source).1
  have htargetLower : lower < target.1 := by
    have ht :=
      (bankPaperCanonicalExponentBandOf_mem_interval
        M hdelta hn hW S target).1
    simpa only [lower, band, hband] using ht
  have hsourceRaw : sourceRaw <= lastRaw := by
    simpa only [sourceRaw, lastRaw, band] using
      bankPaperCanonicalRawRatioCellIndex_le_lastRaw
        M hdelta hn hW S rho hrho source
  have htargetRaw : targetRaw <= lastRaw := by
    have ht := bankPaperCanonicalRawRatioCellIndex_le_lastRaw
      M hdelta hn hW S rho hrho target
    simpa only [targetRaw, lastRaw, band, hband] using ht
  have hmerged :
      tangentMergedRatioCellIndex lastRaw sourceRaw =
          tangentMergedRatioCellIndex lastRaw targetRaw ∨
        tangentMergedRatioCellIndex lastRaw sourceRaw + 1 =
          tangentMergedRatioCellIndex lastRaw targetRaw ∨
        tangentMergedRatioCellIndex lastRaw targetRaw + 1 =
          tangentMergedRatioCellIndex lastRaw sourceRaw := by
    simpa only [bankPaperCanonicalRatioCellIndex, sourceRaw, targetRaw,
      lastRaw, band, hband] using hcell.2
  have hrawDistance :=
    rawCellIndices_within_two_of_merged_sameOrAdjacent
      hsourceRaw htargetRaw hmerged
  by_cases hlabels : source.1 <= target.1
  · change (((max source.1 target.1 : Nat) : Real) /
      ((min source.1 target.1 : Nat) : Real)) < rho ^ 3
    rw [max_eq_right hlabels, min_eq_left hlabels]
    apply tangentMultiplicativeRawCell_ratio_lt_cube
      hlower hrho htargetLower hsourceLower
    simpa only [sourceRaw, targetRaw,
      bankPaperCanonicalRawRatioCellIndex, lower, band, hband] using
      hrawDistance.2
  · have hreverse : target.1 <= source.1 := Nat.le_of_not_ge hlabels
    change (((max source.1 target.1 : Nat) : Real) /
      ((min source.1 target.1 : Nat) : Real)) < rho ^ 3
    rw [max_eq_left hreverse, min_eq_right hreverse]
    apply tangentMultiplicativeRawCell_ratio_lt_cube
      hlower hrho hsourceLower htargetLower
    simpa only [sourceRaw, targetRaw,
      bankPaperCanonicalRawRatioCellIndex, lower, band, hband] using
      hrawDistance.1

/-- Concrete constructor of the downstream fixed-ratio geometry predicate.
The only numerical fact used after the cell construction is
`rho^3 < r0`. -/
theorem bankPaperCanonical_tangentRatioCellGeometry
    {delta eta : Real} (M : RegularRelativeMesh.Mesh delta eta)
    {n W : Nat} (hdelta : 0 < delta) (hn : 1 < n)
    (hW : W ≠ 0) (S : ScaleSeparation M n W)
    {rho r0 : Real} (hrho : 1 < rho) (hratio : rho ^ 3 < r0) :
    TangentRatioCellGeometry bankPaperCanonicalTangentPrimeLabel
      (bankPaperCanonicalExponentBandOf M hdelta hn hW S)
      (bankPaperCanonicalRatioCellIndex M hdelta hn hW S rho) r0 := by
  intro source target hcell
  exact (bankPaperCanonical_sameOrAdjacentRatioCell_ratio_lt_cube
    M hdelta hn hW S hrho hcell).trans hratio |>.le

/-! ## Exact analytic occupancy boundary -/





/-- Complete finite geometry package consumed by the explicit ratio-cell
earthmover: bounded indices, occupancy, and fixed-ratio locality.  The only
analytic input is the transparent fixed-ratio prime-interval predicate. -/
theorem bankPaperCanonical_ratioCellGeometry_spec
    {delta eta : Real} (M : RegularRelativeMesh.Mesh delta eta)
    {n W : Nat} (hdelta : 0 < delta) (hn : 1 < n)
    (hW : W ≠ 0) (S : ScaleSeparation M n W)
    {rho r0 : Real} (hrho : 1 < rho) (hratio : rho ^ 3 < r0)
    (hprime : TangentFixedRatioPrimeIntervalOccupied W rho) :
    (forall p : BankPaperCanonicalTangentPrime n W,
      bankPaperCanonicalRatioCellIndex M hdelta hn hW S rho p <=
        bankPaperCanonicalLastRatioCell M (n := n) (W := W) rho
          (bankPaperCanonicalExponentBandOf M hdelta hn hW S p)) ∧
      (forall (band : BankPaperCanonicalExponentBand M) (cell : Nat),
        cell <= bankPaperCanonicalLastRatioCell M
          (n := n) (W := W) rho band ->
          tangentRatioCellCard
            (bankPaperCanonicalExponentBandOf M hdelta hn hW S)
            (bankPaperCanonicalRatioCellIndex M hdelta hn hW S rho)
            band cell ≠ 0) ∧
      TangentRatioCellGeometry bankPaperCanonicalTangentPrimeLabel
        (bankPaperCanonicalExponentBandOf M hdelta hn hW S)
        (bankPaperCanonicalRatioCellIndex M hdelta hn hW S rho) r0 := by
  exact ⟨bankPaperCanonicalRatioCellIndex_le_lastCell
      M hdelta hn hW S rho,
    bankPaperCanonical_ratioCell_occupied_of_fixedRatioPrimeInterval
      M hdelta hn hW S hrho hprime,
    bankPaperCanonical_tangentRatioCellGeometry
      M hdelta hn hW S hrho hratio⟩

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





theorem bankPaperCanonicalRatioCellTailLower_le_upper
    {delta eta : Real} (M : RegularRelativeMesh.Mesh delta eta)
    (n W : Nat) (rho : Real)
    (band : BankPaperCanonicalExponentBand M) (cut : Nat) :
    bankPaperCanonicalRatioCellTailLower M n W rho band cut <=
      bankPaperCanonicalRatioCellTailUpper M n W band := by
  exact Nat.min_le_right _ _

/-- The fixed cutoff lies below every canonical exponent-band lower
endpoint. -/
theorem bankPaperCanonical_fixedCutoff_le_exponentBandLower
    {delta eta : Real} (M : RegularRelativeMesh.Mesh delta eta)
    {n W : Nat} (hdelta : 0 < delta) (hn : 1 < n)
    (hW : W ≠ 0) (S : ScaleSeparation M n W)
    (band : BankPaperCanonicalExponentBand M) :
    W <= bankPaperCanonicalExponentBandLower M n W band := by
  have hcut :=
    (RegularMeshPrimeCutoffs.Mesh.canonicalCertificate
      M hdelta hn hW S).cutoff_le_lower band
  simpa only [bankPaperCanonicalExponentBandLower,
    RegularMeshPrimeCutoffs.Mesh.canonicalCertificate_lower] using hcut

/-- Both branches in the capped lower endpoint remain above the fixed
cutoff. -/
theorem bankPaperCanonical_fixedCutoff_le_ratioCellTailLower
    {delta eta : Real} (M : RegularRelativeMesh.Mesh delta eta)
    {n W : Nat} (hdelta : 0 < delta) (hn : 1 < n)
    (hW : W ≠ 0) (S : ScaleSeparation M n W)
    {rho : Real} (hrho : 1 < rho)
    (band : BankPaperCanonicalExponentBand M) (cut : Nat) :
    W <= bankPaperCanonicalRatioCellTailLower M n W rho band cut := by
  have hWLower := bankPaperCanonical_fixedCutoff_le_exponentBandLower
    M hdelta hn hW S band
  have hcutMono := tangentMultiplicativeRatioCutoff_mono
    (lower := bankPaperCanonicalExponentBandLower M n W band)
    (rho := rho) hrho.le
  have hWNext : W <= tangentMultiplicativeRatioCutoff
      (bankPaperCanonicalExponentBandLower M n W band) rho (cut + 1) := by
    exact hWLower.trans (by
      simpa only [tangentMultiplicativeRatioCutoff_zero] using
        hcutMono (Nat.zero_le (cut + 1)))
  have hWUpper : W <= bankPaperCanonicalExponentBandUpper M n W band := by
    obtain ⟨p, hp⟩ :=
      (RegularMeshPrimeCutoffs.Mesh.canonicalPartition
        M hdelta hn hW S).fiber_nonempty band
    have hpInterval :=
      ((RegularMeshPrimeCutoffs.Mesh.canonicalCertificate
        M hdelta hn hW S).band_eq_iff p band).mp hp
    exact hWLower.trans (hpInterval.1.le.trans hpInterval.2)
  exact le_min hWNext hWUpper

/-- Every prime in a declared strict merged-cell tail lies in the concrete
numerical interval used by the Mertens estimate. -/
theorem bankPaperCanonical_ratioCellTail_mem_interval
    {delta eta : Real} (M : RegularRelativeMesh.Mesh delta eta)
    {n W : Nat} (hdelta : 0 < delta) (hn : 1 < n)
    (hW : W ≠ 0) (S : ScaleSeparation M n W)
    {rho : Real} (hrho : 1 < rho)
    (band : BankPaperCanonicalExponentBand M) (cut : Nat)
    (p : BankPaperCanonicalTangentPrime n W)
    (hpBand : bankPaperCanonicalExponentBandOf M hdelta hn hW S p = band)
    (hpCut : cut <
      bankPaperCanonicalRatioCellIndex M hdelta hn hW S rho p) :
    bankPaperCanonicalRatioCellTailLower M n W rho band cut <
        bankPaperCanonicalTangentPrimeLabel p ∧
      bankPaperCanonicalTangentPrimeLabel p <=
        bankPaperCanonicalRatioCellTailUpper M n W band := by
  let lower := bankPaperCanonicalExponentBandLower M n W band
  let raw := bankPaperCanonicalRawRatioCellIndex
    M hdelta hn hW S rho p
  have hlower : 0 < lower := by
    exact bankPaperCanonicalExponentBandLower_pos
      M hdelta hn hW S band
  have hpLower : lower < p.1 := by
    have hp :=
      (bankPaperCanonicalExponentBandOf_mem_interval
        M hdelta hn hW S p).1
    simpa only [lower, hpBand] using hp
  have hpUpper : p.1 <= bankPaperCanonicalExponentBandUpper M n W band := by
    have hp :=
      (bankPaperCanonicalExponentBandOf_mem_interval
        M hdelta hn hW S p).2
    simpa only [hpBand] using hp
  have hmergedLeRaw :
      bankPaperCanonicalRatioCellIndex M hdelta hn hW S rho p <= raw := by
    unfold bankPaperCanonicalRatioCellIndex
    exact tangentMergedRatioCellIndex_le_raw _ _
  have hcutRaw : cut + 1 <= raw := by omega
  have hrawLower : tangentMultiplicativeRatioCutoff lower rho raw < p.1 := by
    have h := tangentMultiplicativeRatioCutoff_rawCell_lt_label
      hlower hrho hpLower
    simpa only [raw, lower, bankPaperCanonicalRawRatioCellIndex, hpBand] using h
  have hnextLower :
      tangentMultiplicativeRatioCutoff lower rho (cut + 1) < p.1 := by
    exact (tangentMultiplicativeRatioCutoff_mono
      (lower := lower) (rho := rho) hrho.le hcutRaw).trans_lt hrawLower
  constructor
  · exact (Nat.min_le_left _ _).trans_lt (by
      simpa only [bankPaperCanonicalRatioCellTailLower, lower] using hnextLower)
  · simpa only [bankPaperCanonicalTangentPrimeLabel,
      bankPaperCanonicalRatioCellTailUpper] using hpUpper

/-! ## Uniform Mertens envelope on the concrete tails -/



/-- Uniform Mertens bounds the literal harmonic mass of every concrete
strict cell tail. -/
theorem bankPaperCanonical_ratioCellTail_harmonic_le_majorant
    {delta eta : Real} (M : RegularRelativeMesh.Mesh delta eta)
    {n W : Nat} (hdelta : 0 < delta) (hn : 1 < n)
    (hW : W ≠ 0) (S : ScaleSeparation M n W)
    {rho scale : Real} (hrho : 1 < rho) (hscale : 0 <= scale)
    (hMertens : fullReciprocalSumUniformCutoff <= W)
    (band : BankPaperCanonicalExponentBand M) (cut : Nat) :
    tangentRatioCellTailPointwiseUpper
        (bankPaperCanonicalHarmonicPointwiseUpper scale)
        (bankPaperCanonicalExponentBandOf M hdelta hn hW S)
        (bankPaperCanonicalRatioCellIndex M hdelta hn hW S rho)
        band cut <=
      bankPaperCanonicalRatioCellTailMajorant
        M n W rho scale band cut := by
  apply tangentRatioCellTail_harmonicPointwiseUpper_le_uniformMajorant
    (bankPaperCanonicalExponentBandOf M hdelta hn hW S)
    (bankPaperCanonicalRatioCellIndex M hdelta hn hW S rho)
    scale hscale band cut
    (bankPaperCanonicalRatioCellTailLower M n W rho band cut)
    (bankPaperCanonicalRatioCellTailUpper M n W band)
  · exact hMertens.trans
      (bankPaperCanonical_fixedCutoff_le_ratioCellTailLower
        M hdelta hn hW S hrho band cut)
  · exact bankPaperCanonicalRatioCellTailLower_le_upper
      M n W rho band cut
  · intro p hpBand hpCut
    exact bankPaperCanonical_ratioCellTail_mem_interval
      M hdelta hn hW S hrho band cut p hpBand hpCut

/-- The explicit tail majorant is nonnegative.  This is deduced from the
nonnegative literal harmonic tail rather than by separately manipulating
the log-log formula. -/
theorem bankPaperCanonicalRatioCellTailMajorant_nonneg
    {delta eta : Real} (M : RegularRelativeMesh.Mesh delta eta)
    {n W : Nat} (hdelta : 0 < delta) (hn : 1 < n)
    (hW : W ≠ 0) (S : ScaleSeparation M n W)
    {rho scale : Real} (hrho : 1 < rho) (hscale : 0 <= scale)
    (hMertens : fullReciprocalSumUniformCutoff <= W)
    (band : BankPaperCanonicalExponentBand M) (cut : Nat) :
    0 <= bankPaperCanonicalRatioCellTailMajorant
      M n W rho scale band cut := by
  have htailNonneg : 0 <=
      tangentRatioCellTailPointwiseUpper
        (bankPaperCanonicalHarmonicPointwiseUpper scale)
        (bankPaperCanonicalExponentBandOf M hdelta hn hW S)
        (bankPaperCanonicalRatioCellIndex M hdelta hn hW S rho)
        band cut := by
    unfold tangentRatioCellTailPointwiseUpper
    apply Finset.sum_nonneg
    intro p _hp
    by_cases htail :
        bankPaperCanonicalExponentBandOf M hdelta hn hW S p = band ∧
          cut < bankPaperCanonicalRatioCellIndex M hdelta hn hW S rho p
    · simp only [if_pos htail]
      exact div_nonneg hscale (Nat.cast_nonneg _)
    · simp [htail]
  exact htailNonneg.trans
    (bankPaperCanonical_ratioCellTail_harmonic_le_majorant
      M hdelta hn hW S hrho hscale hMertens band cut)

/-! ## Quantitative PNT denominator inside an actual cell -/











/-- Quantitative PNT lower bound for the actual denominator of every merged
cell containing a full raw interval. -/
theorem bankPaperCanonical_ratioCellCard_PNT_lower
    {delta eta : Real} (M : RegularRelativeMesh.Mesh delta eta)
    {n W : Nat} (hdelta : 0 < delta) (hn : 1 < n)
    (hW : W ≠ 0) (S : ScaleSeparation M n W)
    {rho : Real} (hrho : 1 < rho)
    (hPNT : TangentFixedRatioPrimeCountLower W rho)
    (band : BankPaperCanonicalExponentBand M) (cell : Nat)
    (hcell : cell < bankPaperCanonicalLastRawRatioCell M
      (n := n) (W := W) rho band) :
    ((rho - 1) / 2) *
        ((tangentMultiplicativeRatioCutoff
            (bankPaperCanonicalExponentBandLower M n W band)
            rho cell : Real) /
          Real.log (tangentMultiplicativeRatioCutoff
            (bankPaperCanonicalExponentBandLower M n W band)
            rho cell : Real)) <=
      (tangentRatioCellCard
        (bankPaperCanonicalExponentBandOf M hdelta hn hW S)
        (bankPaperCanonicalRatioCellIndex M hdelta hn hW S rho)
        band cell : Real) := by
  let A := tangentMultiplicativeRatioCutoff
    (bankPaperCanonicalExponentBandLower M n W band) rho cell
  have hWA : W <= A := by
    exact (bankPaperCanonical_fixedCutoff_le_exponentBandLower
      M hdelta hn hW S band).trans (by
        have hmono := tangentMultiplicativeRatioCutoff_mono
          (lower := bankPaperCanonicalExponentBandLower M n W band)
          (rho := rho) hrho.le (Nat.zero_le cell)
        simpa only [A, tangentMultiplicativeRatioCutoff_zero] using hmono)
  exact (hPNT A hWA).trans (by
    exact_mod_cast
      (bankPaperCanonical_fixedRatioPrimeCounting_le_ratioCellCard
        M hdelta hn hW S hrho band cell hcell))

/-! ## Finite traffic envelopes before the final mesh sum -/











/-- The harmonic pointwise estimate immediately supplies the exact
weighted-residual budget `weightedResidual = scale`. -/
theorem bankPaperCanonical_weightedResidual_le_harmonicScale
    {n W : Nat} {scale : Real}
    (residual : BankPaperCanonicalTangentPrime n W -> Real)
    (hpointwise : forall p : BankPaperCanonicalTangentPrime n W,
      |residual p| <= bankPaperCanonicalHarmonicPointwiseUpper scale p)
    (p : BankPaperCanonicalTangentPrime n W) :
    (bankPaperCanonicalTangentPrimeLabel p : Real) * |residual p| <=
      scale := by
  calc
    (bankPaperCanonicalTangentPrimeLabel p : Real) * |residual p| <=
        (bankPaperCanonicalTangentPrimeLabel p : Real) *
          bankPaperCanonicalHarmonicPointwiseUpper scale p :=
      mul_le_mul_of_nonneg_left (hpointwise p) (Nat.cast_nonneg _)
    _ = scale :=
      bankPaperCanonicalTangentPrimeLabel_mul_harmonicPointwiseUpper scale p

/-- Uniform Mertens bounds the complete harmonic residual envelope on the
literal canonical prime band. -/
theorem bankPaperCanonicalHarmonicResidualL1Envelope_le_majorant
    {delta eta : Real} (M : RegularRelativeMesh.Mesh delta eta)
    {n W : Nat} (hdelta : 0 < delta) (hn : 1 < n)
    (hW : W ≠ 0) (S : ScaleSeparation M n W)
    {scale : Real} (hscale : 0 <= scale)
    (hMertens : fullReciprocalSumUniformCutoff <= W) :
    bankPaperCanonicalHarmonicResidualL1Envelope n W scale <=
      bankPaperCanonicalHarmonicResidualL1Majorant n W scale := by
  let bandOf : BankPaperCanonicalTangentPrime n W -> Unit := fun _ => ()
  let cellIndex : BankPaperCanonicalTangentPrime n W -> Nat := fun _ => 1
  have hWY : W <= yNat n := by
    let band : BankPaperCanonicalExponentBand M := ⟨0, by omega⟩
    let E := RegularMeshPrimeCutoffs.Mesh.canonicalCertificate
      M hdelta hn hW S
    exact (E.cutoff_le_lower band).trans
      ((E.lower_le_upper band).trans (E.upper_le_yNat band))
  have htail :=
    tangentRatioCellTail_harmonicPointwiseUpper_le_uniformMajorant
      bandOf cellIndex scale hscale () 0 W (yNat n)
      hMertens hWY (by
        intro p _hpBand _hpCut
        exact ⟨cutoff_lt_of_mem_primeBand p.2,
          le_yNat_of_mem_primeBand p.2⟩)
  simpa [bankPaperCanonicalHarmonicResidualL1Envelope,
    bankPaperCanonicalHarmonicResidualL1Majorant,
    tangentRatioCellTailPointwiseUpper, bandOf, cellIndex,
    bankPaperCanonicalTangentPrimeLabel] using htail









/-- If an exponent band has no full raw interval, terminal merging puts all
of its vertices in cell zero, so the strict tail after cell zero is empty. -/
theorem bankPaperCanonical_ratioCellTail_eq_zero_of_lastRaw_eq_zero
    {delta eta : Real} (M : RegularRelativeMesh.Mesh delta eta)
    {n W : Nat} (hdelta : 0 < delta) (hn : 1 < n)
    (hW : W ≠ 0) (S : ScaleSeparation M n W)
    (rho : Real)
    (pointwiseUpper : BankPaperCanonicalTangentPrime n W -> Real)
    (band : BankPaperCanonicalExponentBand M)
    (hlast : bankPaperCanonicalLastRawRatioCell M
      (n := n) (W := W) rho band = 0) :
    tangentRatioCellTailPointwiseUpper pointwiseUpper
        (bankPaperCanonicalExponentBandOf M hdelta hn hW S)
        (bankPaperCanonicalRatioCellIndex M hdelta hn hW S rho)
        band 0 = 0 := by
  unfold tangentRatioCellTailPointwiseUpper
  apply Finset.sum_eq_zero
  intro p _hp
  by_cases hpBand :
      bankPaperCanonicalExponentBandOf M hdelta hn hW S p = band
  · have hpIndex := bankPaperCanonicalRatioCellIndex_le_lastCell
      M hdelta hn hW S rho p
    have hpIndexLe :
        bankPaperCanonicalRatioCellIndex M hdelta hn hW S rho p <= 0 := by
      simpa only [hpBand, bankPaperCanonicalLastRatioCell,
        tangentMergedRatioLastCell, hlast] using hpIndex
    have hpIndexZero :
        bankPaperCanonicalRatioCellIndex M hdelta hn hW S rho p = 0 :=
      Nat.eq_zero_of_le_zero hpIndexLe
    simp [hpBand, hpIndexZero]
  · simp [hpBand]

/-- Correspondingly, the literal two-sided pointwise port majorant is zero
in a band with no full raw interval. -/
theorem bankPaperCanonical_ratioCellPointwisePortUpper_eq_zero_of_lastRaw_eq_zero
    {delta eta : Real} (M : RegularRelativeMesh.Mesh delta eta)
    {n W : Nat} (hdelta : 0 < delta) (hn : 1 < n)
    (hW : W ≠ 0) (S : ScaleSeparation M n W)
    (rho : Real)
    (pointwiseUpper : BankPaperCanonicalTangentPrime n W -> Real)
    (p : BankPaperCanonicalTangentPrime n W)
    (hlast : bankPaperCanonicalLastRawRatioCell M
      (n := n) (W := W) rho
      (bankPaperCanonicalExponentBandOf M hdelta hn hW S p) = 0) :
    tangentRatioCellPointwisePortUpper pointwiseUpper
        (bankPaperCanonicalExponentBandOf M hdelta hn hW S)
        (bankPaperCanonicalRatioCellIndex M hdelta hn hW S rho) p = 0 := by
  have hpIndex := bankPaperCanonicalRatioCellIndex_le_lastCell
    M hdelta hn hW S rho p
  have hpIndexLe :
      bankPaperCanonicalRatioCellIndex M hdelta hn hW S rho p <= 0 := by
    simpa only [bankPaperCanonicalLastRatioCell,
      tangentMergedRatioLastCell, hlast] using hpIndex
  have hpIndexZero :
      bankPaperCanonicalRatioCellIndex M hdelta hn hW S rho p = 0 :=
    Nat.eq_zero_of_le_zero hpIndexLe
  have htail := bankPaperCanonical_ratioCellTail_eq_zero_of_lastRaw_eq_zero
    M hdelta hn hW S rho pointwiseUpper
    (bankPaperCanonicalExponentBandOf M hdelta hn hW S p) hlast
  unfold tangentRatioCellPointwisePortUpper
  rw [if_pos hpIndexZero, hpIndexZero, htail]
  simp

/-- Mertens bounds the numerator in the literal pointwise-port quotient. -/
theorem bankPaperCanonical_ratioCellPointwisePortUpper_le_envelope_div_card
    {delta eta : Real} (M : RegularRelativeMesh.Mesh delta eta)
    {n W : Nat} (hdelta : 0 < delta) (hn : 1 < n)
    (hW : W ≠ 0) (S : ScaleSeparation M n W)
    {rho scale : Real} (hrho : 1 < rho) (hscale : 0 <= scale)
    (hMertens : fullReciprocalSumUniformCutoff <= W)
    (p : BankPaperCanonicalTangentPrime n W) :
    tangentRatioCellPointwisePortUpper
        (bankPaperCanonicalHarmonicPointwiseUpper scale)
        (bankPaperCanonicalExponentBandOf M hdelta hn hW S)
        (bankPaperCanonicalRatioCellIndex M hdelta hn hW S rho) p <=
      bankPaperCanonicalRatioCellPortNumeratorEnvelope
          M hdelta hn hW S rho scale p /
        tangentRatioCellCard
          (bankPaperCanonicalExponentBandOf M hdelta hn hW S)
          (bankPaperCanonicalRatioCellIndex M hdelta hn hW S rho)
          (bankPaperCanonicalExponentBandOf M hdelta hn hW S p)
          (bankPaperCanonicalRatioCellIndex M hdelta hn hW S rho p) := by
  unfold tangentRatioCellPointwisePortUpper
    bankPaperCanonicalRatioCellPortNumeratorEnvelope
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  by_cases hcell :
      bankPaperCanonicalRatioCellIndex M hdelta hn hW S rho p = 0
  · simpa only [if_pos hcell, zero_add] using
      (bankPaperCanonical_ratioCellTail_harmonic_le_majorant
        M hdelta hn hW S hrho hscale hMertens
        (bankPaperCanonicalExponentBandOf M hdelta hn hW S p)
        (bankPaperCanonicalRatioCellIndex M hdelta hn hW S rho p))
  · simpa only [if_neg hcell] using
      (add_le_add
        (bankPaperCanonical_ratioCellTail_harmonic_le_majorant
          M hdelta hn hW S hrho hscale hMertens
          (bankPaperCanonicalExponentBandOf M hdelta hn hW S p)
          (bankPaperCanonicalRatioCellIndex M hdelta hn hW S rho p - 1))
        (bankPaperCanonical_ratioCellTail_harmonic_le_majorant
          M hdelta hn hW S hrho hscale hMertens
          (bankPaperCanonicalExponentBandOf M hdelta hn hW S p)
          (bankPaperCanonicalRatioCellIndex M hdelta hn hW S rho p)))



/-- The PNT denominator is positive once the fixed cutoff is at least two. -/
theorem bankPaperCanonicalRatioCellPNTDenominator_pos
    {delta eta : Real} (M : RegularRelativeMesh.Mesh delta eta)
    {n W : Nat} (hdelta : 0 < delta) (hn : 1 < n)
    (hWtwo : 2 <= W) (S : ScaleSeparation M n W)
    {rho : Real} (hrho : 1 < rho)
    (p : BankPaperCanonicalTangentPrime n W) :
    0 < bankPaperCanonicalRatioCellPNTDenominator
      M hdelta hn (by omega) S rho p := by
  let band := bankPaperCanonicalExponentBandOf M hdelta hn
    (by omega : W ≠ 0) S p
  let cell := bankPaperCanonicalRatioCellIndex M hdelta hn
    (by omega : W ≠ 0) S rho p
  let A := tangentMultiplicativeRatioCutoff
    (bankPaperCanonicalExponentBandLower M n W band) rho cell
  have hWA : W <= A :=
    (bankPaperCanonical_fixedCutoff_le_exponentBandLower
      M hdelta hn (by omega) S band).trans (by
        have hmono := tangentMultiplicativeRatioCutoff_mono
          (lower := bankPaperCanonicalExponentBandLower M n W band)
          (rho := rho) hrho.le (Nat.zero_le cell)
        simpa only [A, tangentMultiplicativeRatioCutoff_zero] using hmono)
  have hAone : 1 < A := by omega
  have hApos : (0 : Real) < A := by exact_mod_cast (Nat.zero_lt_of_lt hAone)
  have hlogA : 0 < Real.log (A : Real) :=
    Real.log_pos (by exact_mod_cast hAone)
  simpa only [bankPaperCanonicalRatioCellPNTDenominator, A, band, cell] using
    mul_pos (div_pos (sub_pos.mpr hrho) (by norm_num))
      (div_pos hApos hlogA)

/-- The quantitative PNT and Mertens estimates give a completely explicit
weighted pointwise-port bound.  Bands with a full raw interval use the PNT
denominator; in a degenerate one-cell band the literal port load is zero. -/
theorem bankPaperCanonical_weightedRatioCellPointwisePortUpper_le_PNTEnvelope
    {delta eta : Real} (M : RegularRelativeMesh.Mesh delta eta)
    {n W : Nat} (hdelta : 0 < delta) (hn : 1 < n)
    (hWtwo : 2 <= W) (S : ScaleSeparation M n W)
    {rho scale : Real} (hrho : 1 < rho) (hscale : 0 <= scale)
    (hMertens : fullReciprocalSumUniformCutoff <= W)
    (hPNT : TangentFixedRatioPrimeCountLower W rho)
    (p : BankPaperCanonicalTangentPrime n W) :
    (bankPaperCanonicalTangentPrimeLabel p : Real) *
        tangentRatioCellPointwisePortUpper
          (bankPaperCanonicalHarmonicPointwiseUpper scale)
          (bankPaperCanonicalExponentBandOf M hdelta hn (by omega) S)
          (bankPaperCanonicalRatioCellIndex M hdelta hn (by omega) S rho) p <=
      (bankPaperCanonicalTangentPrimeLabel p : Real) *
        (bankPaperCanonicalRatioCellPortNumeratorEnvelope
            M hdelta hn (by omega) S rho scale p /
          bankPaperCanonicalRatioCellPNTDenominator
            M hdelta hn (by omega) S rho p) := by
  let band := bankPaperCanonicalExponentBandOf M hdelta hn
    (by omega : W ≠ 0) S p
  let cell := bankPaperCanonicalRatioCellIndex M hdelta hn
    (by omega : W ≠ 0) S rho p
  have hnumNonneg : 0 <= bankPaperCanonicalRatioCellPortNumeratorEnvelope
      M hdelta hn (by omega) S rho scale p := by
    unfold bankPaperCanonicalRatioCellPortNumeratorEnvelope
    change 0 <=
      (if cell = 0 then 0
        else bankPaperCanonicalRatioCellTailMajorant
          M n W rho scale band (cell - 1)) +
        bankPaperCanonicalRatioCellTailMajorant
          M n W rho scale band cell
    by_cases hcellZero : cell = 0
    · simpa only [if_pos hcellZero, zero_add] using
        (bankPaperCanonicalRatioCellTailMajorant_nonneg
          M hdelta hn (by omega) S hrho hscale hMertens band cell)
    · simpa only [if_neg hcellZero] using
        (add_nonneg
          (bankPaperCanonicalRatioCellTailMajorant_nonneg
            M hdelta hn (by omega) S hrho hscale hMertens band (cell - 1))
          (bankPaperCanonicalRatioCellTailMajorant_nonneg
            M hdelta hn (by omega) S hrho hscale hMertens band cell))
  have hport :=
    bankPaperCanonical_ratioCellPointwisePortUpper_le_envelope_div_card
      M hdelta hn (by omega) S hrho hscale hMertens p
  have hdenPos := bankPaperCanonicalRatioCellPNTDenominator_pos
    M hdelta hn hWtwo S hrho p
  by_cases hlastZero : bankPaperCanonicalLastRawRatioCell M
      (n := n) (W := W) rho band = 0
  · have hportZero :=
      bankPaperCanonical_ratioCellPointwisePortUpper_eq_zero_of_lastRaw_eq_zero
        M hdelta hn (by omega) S rho
        (bankPaperCanonicalHarmonicPointwiseUpper scale) p (by
          simpa only [band] using hlastZero)
    rw [hportZero, mul_zero]
    exact mul_nonneg (Nat.cast_nonneg _)
      (div_nonneg hnumNonneg hdenPos.le)
  · have hlast : 0 < bankPaperCanonicalLastRawRatioCell M
        (n := n) (W := W) rho band := Nat.pos_of_ne_zero hlastZero
    have hcell : cell < bankPaperCanonicalLastRawRatioCell M
        (n := n) (W := W) rho band := by
      have hindex : cell <=
          bankPaperCanonicalLastRawRatioCell M
            (n := n) (W := W) rho band - 1 := by
        simpa only [cell, band, bankPaperCanonicalLastRatioCell,
          tangentMergedRatioLastCell] using
            (bankPaperCanonicalRatioCellIndex_le_lastCell
              M hdelta hn (by omega) S rho p)
      omega
    have hdenLower : bankPaperCanonicalRatioCellPNTDenominator
        M hdelta hn (by omega) S rho p <=
        (tangentRatioCellCard
          (bankPaperCanonicalExponentBandOf M hdelta hn (by omega) S)
          (bankPaperCanonicalRatioCellIndex M hdelta hn (by omega) S rho)
          band cell : Real) := by
      simpa only [bankPaperCanonicalRatioCellPNTDenominator, band, cell] using
        bankPaperCanonical_ratioCellCard_PNT_lower
          M hdelta hn (by omega) S hrho hPNT band cell hcell
    have hratio :
        bankPaperCanonicalRatioCellPortNumeratorEnvelope
              M hdelta hn (by omega) S rho scale p /
            (tangentRatioCellCard
              (bankPaperCanonicalExponentBandOf M hdelta hn (by omega) S)
              (bankPaperCanonicalRatioCellIndex
                M hdelta hn (by omega) S rho)
              (bankPaperCanonicalExponentBandOf
                M hdelta hn (by omega) S p)
              (bankPaperCanonicalRatioCellIndex
                M hdelta hn (by omega) S rho p) : Real) <=
          bankPaperCanonicalRatioCellPortNumeratorEnvelope
              M hdelta hn (by omega) S rho scale p /
            bankPaperCanonicalRatioCellPNTDenominator
              M hdelta hn (by omega) S rho p := by
      exact div_le_div_of_nonneg_left hnumNonneg hdenPos
        (by simpa only [band, cell] using hdenLower)
    exact mul_le_mul_of_nonneg_left
      (hport.trans hratio) (Nat.cast_nonneg _)

/-- Direct assembly-facing form: exact band balance and the harmonic
pointwise residual bound first control the literal uniform port, after
which the concrete Mertens/PNT envelope supplies its weighted bound. -/
theorem bankPaperCanonical_weightedRatioCellUniformPortLoad_le_PNTEnvelope
    {delta eta : Real} (M : RegularRelativeMesh.Mesh delta eta)
    {n W : Nat} (hdelta : 0 < delta) (hn : 1 < n)
    (hWtwo : 2 <= W) (S : ScaleSeparation M n W)
    {rho scale : Real} (hrho : 1 < rho) (hscale : 0 <= scale)
    (hMertens : fullReciprocalSumUniformCutoff <= W)
    (hPNT : TangentFixedRatioPrimeCountLower W rho)
    (residual : BankPaperCanonicalTangentPrime n W -> Real)
    (hbalance : forall band : BankPaperCanonicalExponentBand M,
      (∑ q : BankPaperCanonicalTangentPrime n W,
        if bankPaperCanonicalExponentBandOf M hdelta hn (by omega) S q =
            band then residual q else 0) = 0)
    (hpointwise : forall q : BankPaperCanonicalTangentPrime n W,
      |residual q| <= bankPaperCanonicalHarmonicPointwiseUpper scale q)
    (p : BankPaperCanonicalTangentPrime n W) :
    (bankPaperCanonicalTangentPrimeLabel p : Real) *
        tangentRatioCellUniformPortLoad residual
          (bankPaperCanonicalExponentBandOf M hdelta hn (by omega) S)
          (bankPaperCanonicalRatioCellIndex M hdelta hn (by omega) S rho) p <=
      (bankPaperCanonicalTangentPrimeLabel p : Real) *
        (bankPaperCanonicalRatioCellPortNumeratorEnvelope
            M hdelta hn (by omega) S rho scale p /
          bankPaperCanonicalRatioCellPNTDenominator
            M hdelta hn (by omega) S rho p) := by
  calc
    (bankPaperCanonicalTangentPrimeLabel p : Real) *
          tangentRatioCellUniformPortLoad residual
            (bankPaperCanonicalExponentBandOf M hdelta hn (by omega) S)
            (bankPaperCanonicalRatioCellIndex M hdelta hn (by omega) S rho) p <=
        (bankPaperCanonicalTangentPrimeLabel p : Real) *
          tangentRatioCellPointwisePortUpper
            (bankPaperCanonicalHarmonicPointwiseUpper scale)
            (bankPaperCanonicalExponentBandOf M hdelta hn (by omega) S)
            (bankPaperCanonicalRatioCellIndex M hdelta hn (by omega) S rho) p :=
      mul_le_mul_of_nonneg_left
        (tangentRatioCellUniformPortLoad_le_pointwisePortUpper
          residual (bankPaperCanonicalHarmonicPointwiseUpper scale)
          (bankPaperCanonicalExponentBandOf M hdelta hn (by omega) S)
          (bankPaperCanonicalRatioCellIndex M hdelta hn (by omega) S rho)
          hbalance hpointwise p)
        (Nat.cast_nonneg _)
    _ <= (bankPaperCanonicalTangentPrimeLabel p : Real) *
        (bankPaperCanonicalRatioCellPortNumeratorEnvelope
            M hdelta hn (by omega) S rho scale p /
          bankPaperCanonicalRatioCellPNTDenominator
            M hdelta hn (by omega) S rho p) :=
      bankPaperCanonical_weightedRatioCellPointwisePortUpper_le_PNTEnvelope
        M hdelta hn hWtwo S hrho hscale hMertens hPNT p

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

/-- Summing all strict pointwise tails counts the upper bound at a vertex
exactly once for every cut strictly to the left of its cell. -/
theorem tangentRatioCell_sum_tailPointwiseUpper_eq_indexMoment
    {V Band : Type*} [Fintype V] [Fintype Band] [DecidableEq Band]
    (lastCell : Band -> Nat) (pointwiseUpper : V -> Real)
    (bandOf : V -> Band) (cellIndex : V -> Nat)
    (hindex : forall v, cellIndex v <= lastCell (bandOf v)) :
    (∑ band : Band,
      ∑ cut ∈ Finset.range (lastCell band),
        tangentRatioCellTailPointwiseUpper
          pointwiseUpper bandOf cellIndex band cut) =
      ∑ v : V, (cellIndex v : Real) * pointwiseUpper v := by
  classical
  calc
    (∑ band : Band,
        ∑ cut ∈ Finset.range (lastCell band),
          tangentRatioCellTailPointwiseUpper
            pointwiseUpper bandOf cellIndex band cut) =
        ∑ band : Band, ∑ v : V,
          if bandOf v = band then
            (cellIndex v : Real) * pointwiseUpper v
          else 0 := by
      apply Finset.sum_congr rfl
      intro band _hband
      unfold tangentRatioCellTailPointwiseUpper
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro v _hv
      by_cases hvBand : bandOf v = band
      · simp only [hvBand, true_and]
        have hfilter :
            (Finset.range (lastCell band)).filter
                (fun cut => cut < cellIndex v) =
              Finset.range (cellIndex v) := by
          ext cut
          simp only [Finset.mem_filter, Finset.mem_range]
          constructor
          · exact fun h => h.2
          · intro hcut
            exact ⟨hcut.trans_le (by simpa only [hvBand] using hindex v),
              hcut⟩
        rw [← Finset.sum_filter, hfilter]
        simp
      · simp [hvBand]
    _ = ∑ v : V, (cellIndex v : Real) * pointwiseUpper v := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro v _hv
      rw [Fintype.sum_eq_single (bandOf v)]
      · simp
      · intro band hband
        have hne : bandOf v ≠ band := Ne.symm hband
        simp [hne]

/-! ## Logarithmic control of the concrete cell index -/

/-- The merged canonical cell index is bounded by the logarithmic distance
from the actual natural lower endpoint of its exponent band. -/
theorem bankPaperCanonical_ratioCellIndex_le_logGap_div_logRho
    {delta eta : Real} (M : RegularRelativeMesh.Mesh delta eta)
    {n W : Nat} (hdelta : 0 < delta) (hn : 1 < n)
    (hW : W ≠ 0) (S : ScaleSeparation M n W)
    {rho : Real} (hrho : 1 < rho)
    (p : BankPaperCanonicalTangentPrime n W) :
    (bankPaperCanonicalRatioCellIndex M hdelta hn hW S rho p : Real) <=
      (Real.log (bankPaperCanonicalTangentPrimeLabel p : Real) -
          Real.log (bankPaperCanonicalExponentBandLower M n W
            (bankPaperCanonicalExponentBandOf M hdelta hn hW S p) :
              Real)) /
        Real.log rho := by
  let band := bankPaperCanonicalExponentBandOf M hdelta hn hW S p
  let lower := bankPaperCanonicalExponentBandLower M n W band
  let raw := bankPaperCanonicalRawRatioCellIndex
    M hdelta hn hW S rho p
  have hlower : 0 < lower := by
    exact bankPaperCanonicalExponentBandLower_pos
      M hdelta hn hW S band
  have hpLower : lower < p.1 := by
    simpa only [band, lower] using
      (bankPaperCanonicalExponentBandOf_mem_interval
        M hdelta hn hW S p).1
  have hrawReal : (lower : Real) * rho ^ raw < (p.1 : Real) := by
    simpa only [raw, lower, bankPaperCanonicalRawRatioCellIndex, band] using
      tangentMultiplicativeRawCell_real_lower_lt
        hlower hrho hpLower
  have hlowerReal : (0 : Real) < lower := by exact_mod_cast hlower
  have hpReal : (0 : Real) < p.1 := by
    exact_mod_cast (bankPaperCanonicalTangentPrimeLabel_prime p).pos
  have hrhoPos : 0 < rho := by linarith
  have hproductPos : 0 < (lower : Real) * rho ^ raw :=
    mul_pos hlowerReal (pow_pos hrhoPos raw)
  have hlogRaw := Real.strictMonoOn_log
    (show (lower : Real) * rho ^ raw ∈ Set.Ioi 0 from hproductPos)
    (show (p.1 : Real) ∈ Set.Ioi 0 from hpReal) hrawReal
  have hlogIdentity :
      Real.log ((lower : Real) * rho ^ raw) =
        Real.log (lower : Real) + (raw : Real) * Real.log rho := by
    rw [Real.log_mul hlowerReal.ne' (pow_ne_zero raw hrhoPos.ne'),
      Real.log_pow]
  rw [hlogIdentity] at hlogRaw
  have hmerged :
      bankPaperCanonicalRatioCellIndex M hdelta hn hW S rho p <= raw := by
    unfold bankPaperCanonicalRatioCellIndex
    exact tangentMergedRatioCellIndex_le_raw _ _
  have hlogRho : 0 < Real.log rho := Real.log_pos hrho
  apply (le_div_iff₀ hlogRho).2
  have hmergedReal :
      (bankPaperCanonicalRatioCellIndex M hdelta hn hW S rho p : Real) <=
        (raw : Real) := by exact_mod_cast hmerged
  change
    (bankPaperCanonicalRatioCellIndex M hdelta hn hW S rho p : Real) *
        Real.log rho <=
      Real.log (p.1 : Real) - Real.log (lower : Real)
  calc
    (bankPaperCanonicalRatioCellIndex M hdelta hn hW S rho p : Real) *
          Real.log rho <=
        (raw : Real) * Real.log rho :=
      mul_le_mul_of_nonneg_right hmergedReal hlogRho.le
    _ <= Real.log (p.1 : Real) - Real.log (lower : Real) := by
      linarith

/-- Coordinate form of the preceding bound.  This is the exact bridge
from the ratio-cell census to the canonical arithmetic moments. -/
theorem bankPaperCanonical_ratioCellIndex_le_coordinateGap
    {delta eta : Real} (M : RegularRelativeMesh.Mesh delta eta)
    {n W : Nat} (hdelta : 0 < delta) (hn : 1 < n)
    (hW : W ≠ 0) (S : ScaleSeparation M n W)
    {rho : Real} (hrho : 1 < rho)
    (p : BankPaperCanonicalTangentPrime n W) :
    (bankPaperCanonicalRatioCellIndex M hdelta hn hW S rho p : Real) <=
      (Real.log (y n) / Real.log rho) *
        (tPrime n p.1 -
          RegularMeshPrimeCutoffs.Mesh.cutoffCoordinate M n W
            (bankPaperCanonicalExponentBandOf M hdelta hn hW S p).1) := by
  have hlogy : 0 < Real.log (y n) := by
    rw [Scale.log_y (Nat.zero_lt_of_lt hn)]
    exact mul_pos (by norm_num)
      (Real.log_pos (by exact_mod_cast hn))
  have hlogrho : 0 < Real.log rho := Real.log_pos hrho
  have hraw := bankPaperCanonical_ratioCellIndex_le_logGap_div_logRho
    M hdelta hn hW S hrho p
  calc
    (bankPaperCanonicalRatioCellIndex M hdelta hn hW S rho p : Real) <=
        (Real.log (bankPaperCanonicalTangentPrimeLabel p : Real) -
            Real.log (bankPaperCanonicalExponentBandLower M n W
              (bankPaperCanonicalExponentBandOf M hdelta hn hW S p) :
                Real)) /
          Real.log rho := hraw
    _ = (Real.log (y n) / Real.log rho) *
        (tPrime n p.1 -
          RegularMeshPrimeCutoffs.Mesh.cutoffCoordinate M n W
            (bankPaperCanonicalExponentBandOf M hdelta hn hW S p).1) := by
      unfold tPrime RegularMeshPrimeCutoffs.Mesh.cutoffCoordinate
        KernelPrimeQuadrature.realLogCoordinate
        bankPaperCanonicalExponentBandLower
        bankPaperCanonicalTangentPrimeLabel
      field_simp [hlogy.ne', hlogrho.ne']

/-! ## The exact shifted-coordinate moment -/



/-- On one arithmetic fiber, the shifted-coordinate sum is exactly mass
times the shifted arithmetic center. -/
theorem bankPaperCanonical_fiber_shiftedCoordinate_eq
    {delta eta : Real} (M : RegularRelativeMesh.Mesh delta eta)
    {n W : Nat} (hdelta : 0 < delta) (hn : 1 < n)
    (hW : W ≠ 0) (S : ScaleSeparation M n W)
    (band : BankPaperCanonicalExponentBand M) :
    let P := RegularMeshPrimeCutoffs.Mesh.canonicalPartition
      M hdelta hn hW S
    (∑ p ∈ P.data.fiber band,
      (1 / (p.1 : Real)) *
        (tPrime n p.1 -
          RegularMeshPrimeCutoffs.Mesh.cutoffCoordinate M n W band.1)) =
      P.mass band *
        (P.center band -
          RegularMeshPrimeCutoffs.Mesh.cutoffCoordinate M n W band.1) := by
  dsimp only
  let P := RegularMeshPrimeCutoffs.Mesh.canonicalPartition
    M hdelta hn hW S
  let lowerCoord :=
    RegularMeshPrimeCutoffs.Mesh.cutoffCoordinate M n W band.1
  have hfirst :
      (∑ p ∈ P.data.fiber band,
        (1 / (p.1 : Real)) * tPrime n p.1) =
        P.mass band * P.center band := by
    change (∑ p ∈ P.data.fiber band,
        (1 / (p.1 : Real)) * tPrime n p.1) =
      P.data.mass band *
        ((∑ p ∈ P.data.fiber band,
          (1 / (p.1 : Real)) * tPrime n p.1) / P.data.mass band)
    field_simp [ne_of_gt (P.data.mass_pos band)]
  have hmass :
      (∑ p ∈ P.data.fiber band, 1 / (p.1 : Real)) =
        P.mass band := rfl
  calc
    (∑ p ∈ P.data.fiber band,
        (1 / (p.1 : Real)) * (tPrime n p.1 - lowerCoord)) =
        (∑ p ∈ P.data.fiber band,
          (1 / (p.1 : Real)) * tPrime n p.1) -
        lowerCoord *
          (∑ p ∈ P.data.fiber band, 1 / (p.1 : Real)) := by
      rw [Finset.mul_sum]
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro p _hp
      ring
    _ = P.mass band * (P.center band - lowerCoord) := by
      rw [hfirst, hmass]
      ring

/-- Reindexing the preceding fiber identities gives the complete shifted
coordinate moment over the literal canonical prime band. -/
theorem bankPaperCanonical_sum_shiftedCoordinate_eq_coordinateMoment
    {delta eta : Real} (M : RegularRelativeMesh.Mesh delta eta)
    {n W : Nat} (hdelta : 0 < delta) (hn : 1 < n)
    (hW : W ≠ 0) (S : ScaleSeparation M n W) :
    (∑ p : BankPaperCanonicalTangentPrime n W,
      (1 / (p.1 : Real)) *
        (tPrime n p.1 -
          RegularMeshPrimeCutoffs.Mesh.cutoffCoordinate M n W
            (bankPaperCanonicalExponentBandOf M hdelta hn hW S p).1)) =
      bankPaperCanonicalRatioCellCoordinateMoment
        M hdelta hn hW S := by
  let P := RegularMeshPrimeCutoffs.Mesh.canonicalPartition
    M hdelta hn hW S
  rw [← Finset.sum_fiberwise Finset.univ P.band
    (fun p : BankPaperCanonicalTangentPrime n W =>
      (1 / (p.1 : Real)) *
        (tPrime n p.1 -
          RegularMeshPrimeCutoffs.Mesh.cutoffCoordinate M n W
            (bankPaperCanonicalExponentBandOf
              M hdelta hn hW S p).1))]
  unfold bankPaperCanonicalRatioCellCoordinateMoment
  dsimp only
  apply Finset.sum_congr rfl
  intro band _hband
  calc
    (∑ p ∈ Finset.univ with P.band p = band,
        (1 / (p.1 : Real)) *
          (tPrime n p.1 -
            RegularMeshPrimeCutoffs.Mesh.cutoffCoordinate M n W
              (P.band p).1)) =
        ∑ p ∈ P.data.fiber band,
          (1 / (p.1 : Real)) *
            (tPrime n p.1 -
              RegularMeshPrimeCutoffs.Mesh.cutoffCoordinate M n W band.1) := by
      apply Finset.sum_congr rfl
      intro p hp
      have hpBand : P.band p = band := (Finset.mem_filter.mp hp).2
      rw [hpBand]
    _ = P.mass band *
        (P.center band -
          RegularMeshPrimeCutoffs.Mesh.cutoffCoordinate M n W band.1) := by
      simpa only [P] using
        bankPaperCanonical_fiber_shiftedCoordinate_eq
          M hdelta hn hW S band

/-! ## Canonical-mesh bound for the shifted moment -/



/-- The positive-cell contribution is controlled by its actual width and
one copy of the explicit floor loss. -/
theorem bankPaperCanonical_positive_shiftedCoordinate_le
    {delta eta : Real} (M : RegularRelativeMesh.Mesh delta eta)
    {n W : Nat} (hdelta : 0 < delta) (hn : 1 < n)
    (hW : W ≠ 0) (S : ScaleSeparation M n W)
    (k : Fin M.cellCount)
    (hTwo : 2 <= scalePoint n (M.lower k))
    (R : RegularMeshPrimeCutoffs.Mesh.MomentReady M
      (RegularMeshPrimeCutoffs.Mesh.canonicalPartition
        M hdelta hn hW S)) :
    let P := RegularMeshPrimeCutoffs.Mesh.canonicalPartition
      M hdelta hn hW S
    P.mass k.succ *
        (P.center k.succ -
          RegularMeshPrimeCutoffs.Mesh.cutoffCoordinate M n W (k.1 + 1)) <=
      3 * M.ratio *
        (M.width k + bankPaperCanonicalRatioCellFloorLoss n) := by
  dsimp only
  let P := RegularMeshPrimeCutoffs.Mesh.canonicalPartition
    M hdelta hn hW S
  let E := RegularMeshPrimeCutoffs.Mesh.canonicalCertificate
    M hdelta hn hW S
  let loss := bankPaperCanonicalRatioCellFloorLoss n
  have hlogy : 0 < Real.log (y n) := by
    rw [Scale.log_y (Nat.zero_lt_of_lt hn)]
    exact mul_pos (by norm_num)
      (Real.log_pos (by exact_mod_cast hn))
  have hloss : 0 <= loss := by
    unfold loss bankPaperCanonicalRatioCellFloorLoss
    exact div_nonneg (Real.log_nonneg (by norm_num)) hlogy.le
  have hlowerCoord :
      M.lower k - loss <=
        RegularMeshPrimeCutoffs.Mesh.cutoffCoordinate M n W (k.1 + 1) := by
    have hfloor := (floor_scalePoint_coordinate_bounds hn hTwo).1
    simpa only [loss, bankPaperCanonicalRatioCellFloorLoss,
      RegularMeshPrimeCutoffs.Mesh.cutoffCoordinate,
      RegularMeshPrimeCutoffs.Mesh.fullCutoff_succ,
      RegularRelativeMesh.Mesh.lower] using hfloor
  have hcoord :=
    RegularMeshPrimeCutoffs.Mesh.positive_coord_bounds
      M P E (fun _j => rfl) (fun _j => rfl) hn k
  have hwidthLoss : 0 <= M.width k + loss :=
    add_nonneg (M.width_pos hdelta k).le hloss
  change P.mass k.succ *
      (P.center k.succ -
        RegularMeshPrimeCutoffs.Mesh.cutoffCoordinate M n W k.succ.1) <=
    3 * M.ratio * (M.width k + bankPaperCanonicalRatioCellFloorLoss n)
  rw [← bankPaperCanonical_fiber_shiftedCoordinate_eq
    M hdelta hn hW S k.succ]
  calc
    (∑ p ∈ P.data.fiber k.succ,
        (1 / (p.1 : Real)) *
          (tPrime n p.1 -
            RegularMeshPrimeCutoffs.Mesh.cutoffCoordinate
              M n W (k.1 + 1))) <=
        ∑ p ∈ P.data.fiber k.succ,
          (1 / (p.1 : Real)) * (M.width k + loss) := by
      apply Finset.sum_le_sum
      intro p hp
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      have hpUpper := (hcoord p hp).2
      unfold RegularRelativeMesh.Mesh.width
      linarith
    _ = P.mass k.succ * (M.width k + loss) := by
      change (∑ p ∈ P.data.fiber k.succ,
          (1 / (p.1 : Real)) * (M.width k + loss)) =
        (∑ p ∈ P.data.fiber k.succ, 1 / (p.1 : Real)) *
          (M.width k + loss)
      rw [Finset.sum_mul]
    _ <= 3 * M.ratio * (M.width k + loss) :=
      mul_le_mul_of_nonneg_right (R.positiveMass k) hwidthLoss

/-- The moving low cell is controlled by the already-proved first-moment
part of `MomentReady`; subtracting its nonnegative fixed-cutoff coordinate
can only decrease it. -/
theorem bankPaperCanonical_low_shiftedCoordinate_le
    {delta eta : Real} (M : RegularRelativeMesh.Mesh delta eta)
    {n W : Nat} (hdelta : 0 < delta) (hn : 1 < n)
    (hWtwo : 2 <= W) (S : ScaleSeparation M n W)
    (R : RegularMeshPrimeCutoffs.Mesh.MomentReady M
      (RegularMeshPrimeCutoffs.Mesh.canonicalPartition
        M hdelta hn (by omega) S)) :
    let P := RegularMeshPrimeCutoffs.Mesh.canonicalPartition
      M hdelta hn (by omega) S
    P.mass 0 *
        (P.center 0 -
          RegularMeshPrimeCutoffs.Mesh.cutoffCoordinate M n W 0) <=
      2 * delta := by
  dsimp only
  let P := RegularMeshPrimeCutoffs.Mesh.canonicalPartition
    M hdelta hn (by omega : W ≠ 0) S
  have hlogy : 0 < Real.log (y n) := by
    rw [Scale.log_y (Nat.zero_lt_of_lt hn)]
    exact mul_pos (by norm_num)
      (Real.log_pos (by exact_mod_cast hn))
  have hWlog : 0 <= Real.log (W : Real) :=
    Real.log_nonneg (by exact_mod_cast (show 1 <= W by omega))
  have hlowerCoord :
      0 <= RegularMeshPrimeCutoffs.Mesh.cutoffCoordinate M n W 0 := by
    unfold RegularMeshPrimeCutoffs.Mesh.cutoffCoordinate
      KernelPrimeQuadrature.realLogCoordinate
    rw [RegularMeshPrimeCutoffs.Mesh.fullCutoff_zero]
    exact div_nonneg hWlog hlogy.le
  have hmass : 0 <= P.mass (0 : BankPaperCanonicalExponentBand M) :=
    (P.data.mass_pos 0).le
  calc
    P.mass 0 *
          (P.center 0 -
            RegularMeshPrimeCutoffs.Mesh.cutoffCoordinate M n W 0) <=
        P.mass 0 * P.center 0 := by
      exact mul_le_mul_of_nonneg_left
        (sub_le_self _ hlowerCoord) hmass
    _ <= 2 * delta := R.lowFirst

/-- Complete canonical shifted-coordinate budget.  The low cell contributes
`2*delta`; the positive mesh contributes `3*ratio`, plus the displayed
finite floor loss. -/
theorem bankPaperCanonical_ratioCellCoordinateMoment_le
    {delta eta : Real} (M : RegularRelativeMesh.Mesh delta eta)
    {n W : Nat} (hdelta : 0 < delta) (hn : 1 < n)
    (hWtwo : 2 <= W) (S : ScaleSeparation M n W)
    (hTwo : forall k : Fin M.cellCount,
      2 <= scalePoint n (M.lower k))
    (R : RegularMeshPrimeCutoffs.Mesh.MomentReady M
      (RegularMeshPrimeCutoffs.Mesh.canonicalPartition
        M hdelta hn (by omega) S)) :
    bankPaperCanonicalRatioCellCoordinateMoment
        M hdelta hn (by omega) S <=
      2 * delta + 3 * M.ratio *
        (1 + (M.cellCount : Real) *
          bankPaperCanonicalRatioCellFloorLoss n) := by
  let P := RegularMeshPrimeCutoffs.Mesh.canonicalPartition
    M hdelta hn (by omega : W ≠ 0) S
  let loss := bankPaperCanonicalRatioCellFloorLoss n
  have hloss : 0 <= loss := by
    unfold loss bankPaperCanonicalRatioCellFloorLoss
    have hlogy : 0 < Real.log (y n) := by
      rw [Scale.log_y (Nat.zero_lt_of_lt hn)]
      exact mul_pos (by norm_num)
        (Real.log_pos (by exact_mod_cast hn))
    exact div_nonneg (Real.log_nonneg (by norm_num)) hlogy.le
  unfold bankPaperCanonicalRatioCellCoordinateMoment
  dsimp only
  rw [Fin.sum_univ_succ]
  calc
    P.mass 0 *
          (P.center 0 -
            RegularMeshPrimeCutoffs.Mesh.cutoffCoordinate M n W 0) +
        ∑ k : Fin M.cellCount,
          P.mass k.succ *
            (P.center k.succ -
              RegularMeshPrimeCutoffs.Mesh.cutoffCoordinate
                M n W (k.1 + 1)) <=
        2 * delta +
          ∑ k : Fin M.cellCount,
            3 * M.ratio * (M.width k + loss) := by
      exact add_le_add
        (bankPaperCanonical_low_shiftedCoordinate_le
          M hdelta hn hWtwo S R)
        (Finset.sum_le_sum fun k _hk =>
          bankPaperCanonical_positive_shiftedCoordinate_le
            M hdelta hn (by omega) S k (hTwo k) R)
    _ = 2 * delta + 3 * M.ratio *
        (1 - delta + (M.cellCount : Real) * loss) := by
      rw [← Finset.mul_sum, Finset.sum_add_distrib,
        M.sum_width_eq_one_sub_delta]
      simp only [Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul]
    _ <= 2 * delta + 3 * M.ratio *
        (1 + (M.cellCount : Real) * loss) := by
      have hrho : 0 <= 3 * M.ratio :=
        mul_nonneg (by norm_num) M.ratio_pos.le
      gcongr
      linarith

/-! ## Moment majorants for the complete traffic ledger -/





/-- The exact cell-index moment is bounded by the canonical shifted
coordinate moment. -/
theorem bankPaperCanonical_ratioCellIndexMoment_le_coordinateMoment
    {delta eta : Real} (M : RegularRelativeMesh.Mesh delta eta)
    {n W : Nat} (hdelta : 0 < delta) (hn : 1 < n)
    (hW : W ≠ 0) (S : ScaleSeparation M n W)
    {rho scale : Real} (hrho : 1 < rho) (hscale : 0 <= scale) :
    (∑ p : BankPaperCanonicalTangentPrime n W,
      (bankPaperCanonicalRatioCellIndex M hdelta hn hW S rho p : Real) *
        bankPaperCanonicalHarmonicPointwiseUpper scale p) <=
      scale * Real.log (y n) / Real.log rho *
        bankPaperCanonicalRatioCellCoordinateMoment
          M hdelta hn hW S := by
  have hlogy : 0 < Real.log (y n) := by
    rw [Scale.log_y (Nat.zero_lt_of_lt hn)]
    exact mul_pos (by norm_num)
      (Real.log_pos (by exact_mod_cast hn))
  have hlogrho : 0 < Real.log rho := Real.log_pos hrho
  calc
    (∑ p : BankPaperCanonicalTangentPrime n W,
        (bankPaperCanonicalRatioCellIndex M hdelta hn hW S rho p : Real) *
          bankPaperCanonicalHarmonicPointwiseUpper scale p) <=
        ∑ p : BankPaperCanonicalTangentPrime n W,
          (scale * Real.log (y n) / Real.log rho) *
            ((1 / (p.1 : Real)) *
              (tPrime n p.1 -
                RegularMeshPrimeCutoffs.Mesh.cutoffCoordinate M n W
                  (bankPaperCanonicalExponentBandOf
                    M hdelta hn hW S p).1)) := by
      apply Finset.sum_le_sum
      intro p _hp
      have hpPos : (0 : Real) < p.1 := by
        exact_mod_cast (bankPaperCanonicalTangentPrimeLabel_prime p).pos
      have hidx := bankPaperCanonical_ratioCellIndex_le_coordinateGap
        M hdelta hn hW S hrho p
      unfold bankPaperCanonicalHarmonicPointwiseUpper
      calc
        (bankPaperCanonicalRatioCellIndex M hdelta hn hW S rho p : Real) *
              (scale / (bankPaperCanonicalTangentPrimeLabel p : Real)) <=
            ((Real.log (y n) / Real.log rho) *
              (tPrime n p.1 -
                RegularMeshPrimeCutoffs.Mesh.cutoffCoordinate M n W
                  (bankPaperCanonicalExponentBandOf
                    M hdelta hn hW S p).1)) *
              (scale / (p.1 : Real)) :=
          mul_le_mul_of_nonneg_right hidx (div_nonneg hscale hpPos.le)
        _ = (scale * Real.log (y n) / Real.log rho) *
            ((1 / (p.1 : Real)) *
              (tPrime n p.1 -
                RegularMeshPrimeCutoffs.Mesh.cutoffCoordinate M n W
                  (bankPaperCanonicalExponentBandOf
                    M hdelta hn hW S p).1)) := by
          field_simp [hpPos.ne', hlogrho.ne']
    _ = (scale * Real.log (y n) / Real.log rho) *
        (∑ p : BankPaperCanonicalTangentPrime n W,
          (1 / (p.1 : Real)) *
            (tPrime n p.1 -
              RegularMeshPrimeCutoffs.Mesh.cutoffCoordinate M n W
                (bankPaperCanonicalExponentBandOf
                  M hdelta hn hW S p).1)) := by
      rw [Finset.mul_sum]
    _ = scale * Real.log (y n) / Real.log rho *
        bankPaperCanonicalRatioCellCoordinateMoment
          M hdelta hn hW S := by
      rw [bankPaperCanonical_sum_shiftedCoordinate_eq_coordinateMoment]

/-- Exact balance and the harmonic pointwise residual estimate bound the
complete cut ledger by the moment majorant, without repeating a Mertens
error at every cut. -/
theorem bankPaperCanonical_ratioCellCutTraffic_le_momentMajorant
    {delta eta : Real} (M : RegularRelativeMesh.Mesh delta eta)
    {n W : Nat} (hdelta : 0 < delta) (hn : 1 < n)
    (hWtwo : 2 <= W) (S : ScaleSeparation M n W)
    {rho scale : Real} (hrho : 1 < rho) (hscale : 0 <= scale)
    (hTwo : forall k : Fin M.cellCount,
      2 <= scalePoint n (M.lower k))
    (R : RegularMeshPrimeCutoffs.Mesh.MomentReady M
      (RegularMeshPrimeCutoffs.Mesh.canonicalPartition
        M hdelta hn (by omega) S))
    (residual : BankPaperCanonicalTangentPrime n W -> Real)
    (hbalance : forall band : BankPaperCanonicalExponentBand M,
      (∑ p : BankPaperCanonicalTangentPrime n W,
        if bankPaperCanonicalExponentBandOf
            M hdelta hn (by omega) S p = band then residual p else 0) = 0)
    (hpointwise : forall p : BankPaperCanonicalTangentPrime n W,
      |residual p| <= bankPaperCanonicalHarmonicPointwiseUpper scale p) :
    tangentRatioCellCanonicalCutTraffic
        (bankPaperCanonicalLastRatioCell M (n := n) (W := W) rho)
        residual
        (bankPaperCanonicalExponentBandOf M hdelta hn (by omega) S)
        (bankPaperCanonicalRatioCellIndex
          M hdelta hn (by omega) S rho) <=
      bankPaperCanonicalRatioCellMomentCutMajorant M n rho scale := by
  let bandOf := bankPaperCanonicalExponentBandOf
    M hdelta hn (by omega : W ≠ 0) S
  let cellIndex := bankPaperCanonicalRatioCellIndex
    M hdelta hn (by omega : W ≠ 0) S rho
  let lastCell := bankPaperCanonicalLastRatioCell M
    (n := n) (W := W) rho
  have hindex : forall p : BankPaperCanonicalTangentPrime n W,
      cellIndex p <= lastCell (bandOf p) := by
    intro p
    exact bankPaperCanonicalRatioCellIndex_le_lastCell
      M hdelta hn (by omega) S rho p
  have hprefix : forall band cut,
      |tangentRatioCellPrefixMass residual bandOf cellIndex band cut| <=
        tangentRatioCellTailPointwiseUpper
          (bankPaperCanonicalHarmonicPointwiseUpper scale)
          bandOf cellIndex band cut := by
    intro band cut
    exact abs_tangentRatioCellPrefixMass_le_tailPointwiseUpper
      residual (bankPaperCanonicalHarmonicPointwiseUpper scale)
      bandOf cellIndex hbalance hpointwise band cut
  have hcut := tangentRatioCellCanonicalCutTraffic_le_prefixUpper
    lastCell residual bandOf cellIndex
    (tangentRatioCellTailPointwiseUpper
      (bankPaperCanonicalHarmonicPointwiseUpper scale) bandOf cellIndex)
    hprefix
  have htail := tangentRatioCell_sum_tailPointwiseUpper_eq_indexMoment
    lastCell (bankPaperCanonicalHarmonicPointwiseUpper scale)
    bandOf cellIndex hindex
  have hmoment := bankPaperCanonical_ratioCellIndexMoment_le_coordinateMoment
    M hdelta hn (by omega) S hrho hscale
  have hcoordinate := bankPaperCanonical_ratioCellCoordinateMoment_le
    M hdelta hn hWtwo S hTwo R
  have hfactor : 0 <= scale * Real.log (y n) / Real.log rho := by
    have hlogy : 0 < Real.log (y n) := by
      rw [Scale.log_y (Nat.zero_lt_of_lt hn)]
      exact mul_pos (by norm_num)
        (Real.log_pos (by exact_mod_cast hn))
    exact div_nonneg (mul_nonneg hscale hlogy.le)
      (Real.log_pos hrho).le
  calc
    tangentRatioCellCanonicalCutTraffic lastCell residual bandOf cellIndex <=
        ∑ band : BankPaperCanonicalExponentBand M,
          ∑ cut ∈ Finset.range (lastCell band),
            tangentRatioCellTailPointwiseUpper
              (bankPaperCanonicalHarmonicPointwiseUpper scale)
              bandOf cellIndex band cut := hcut
    _ = ∑ p : BankPaperCanonicalTangentPrime n W,
        (cellIndex p : Real) *
          bankPaperCanonicalHarmonicPointwiseUpper scale p := htail
    _ <= scale * Real.log (y n) / Real.log rho *
        bankPaperCanonicalRatioCellCoordinateMoment
          M hdelta hn (by omega) S := by
      simpa only [bandOf, cellIndex] using hmoment
    _ <= scale * Real.log (y n) / Real.log rho *
        (2 * delta + 3 * M.ratio *
          (1 + (M.cellCount : Real) *
            bankPaperCanonicalRatioCellFloorLoss n)) :=
      mul_le_mul_of_nonneg_left hcoordinate hfactor
    _ = bankPaperCanonicalRatioCellMomentCutMajorant
        M n rho scale := rfl

/-- Complete finite total-traffic bound using one global Mertens estimate
and the exact ratio-cell moment collapse. -/
theorem bankPaperCanonical_ratioCellTotalTraffic_le_momentMajorant
    {delta eta : Real} (M : RegularRelativeMesh.Mesh delta eta)
    {n W : Nat} (hdelta : 0 < delta) (hn : 1 < n)
    (hWtwo : 2 <= W) (S : ScaleSeparation M n W)
    {rho scale : Real} (hrho : 1 < rho) (hscale : 0 <= scale)
    (hMertens : fullReciprocalSumUniformCutoff <= W)
    (hTwo : forall k : Fin M.cellCount,
      2 <= scalePoint n (M.lower k))
    (R : RegularMeshPrimeCutoffs.Mesh.MomentReady M
      (RegularMeshPrimeCutoffs.Mesh.canonicalPartition
        M hdelta hn (by omega) S))
    (residual : BankPaperCanonicalTangentPrime n W -> Real)
    (hbalance : forall band : BankPaperCanonicalExponentBand M,
      (∑ p : BankPaperCanonicalTangentPrime n W,
        if bankPaperCanonicalExponentBandOf
            M hdelta hn (by omega) S p = band then residual p else 0) = 0)
    (hpointwise : forall p : BankPaperCanonicalTangentPrime n W,
      |residual p| <= bankPaperCanonicalHarmonicPointwiseUpper scale p) :
    tangentDistributedTotalTrafficLedger residual
        (tangentRatioCellCanonicalCutTraffic
          (bankPaperCanonicalLastRatioCell M (n := n) (W := W) rho)
          residual
          (bankPaperCanonicalExponentBandOf M hdelta hn (by omega) S)
          (bankPaperCanonicalRatioCellIndex
            M hdelta hn (by omega) S rho)) <=
      bankPaperCanonicalRatioCellMomentTotalTrafficMajorant
        M n W rho scale := by
  have hresidualEnvelope :
      (∑ p : BankPaperCanonicalTangentPrime n W, |residual p|) <=
        bankPaperCanonicalHarmonicResidualL1Envelope n W scale := by
    unfold bankPaperCanonicalHarmonicResidualL1Envelope
    exact Finset.sum_le_sum (fun p _hp => hpointwise p)
  have hresidualMajorant :=
    bankPaperCanonicalHarmonicResidualL1Envelope_le_majorant
      M hdelta hn (by omega) S hscale hMertens
  have hcut := bankPaperCanonical_ratioCellCutTraffic_le_momentMajorant
    M hdelta hn hWtwo S hrho hscale hTwo R residual hbalance hpointwise
  unfold tangentDistributedTotalTrafficLedger
    bankPaperCanonicalRatioCellMomentTotalTrafficMajorant
  exact add_le_add
    (div_le_div_of_nonneg_right
      (hresidualEnvelope.trans hresidualMajorant) (by norm_num))
    (mul_le_mul_of_nonneg_left hcut (by norm_num))

/-! ## Paper-scale scalar reduction -/





/-- The moment majorant at the paper scale has the required main/error
shape.  This is the smallest remaining scalar inequality for total traffic:
the first coefficient is fixed once `rho` is fixed, and every term in the
second coefficient contains `1 / log y`. -/
theorem bankPaperCanonical_ratioCellMomentTotalTrafficMajorant_paperScale
    {delta eta : Real} (M : RegularRelativeMesh.Mesh delta eta)
    {n W : Nat} {rho tangentConstant N : Real}
    (hdelta : 0 < delta) (hn : 1 < n) (hWtwo : 2 <= W)
    (hrho : 1 < rho)
    (htangent : 0 <= tangentConstant) (hN : 0 <= N) :
    bankPaperCanonicalRatioCellMomentTotalTrafficMajorant M n W rho
        (tangentConstant * N / Real.log (y n)) <=
      bankPaperCanonicalRatioCellTrafficConstant rho *
          tangentConstant * N * (delta + M.ratio) +
        bankPaperCanonicalRatioCellTrafficErrorCoefficient
          M n W rho tangentConstant * N := by
  have hlogy : 0 < Real.log (y n) := by
    rw [Scale.log_y (Nat.zero_lt_of_lt hn)]
    exact mul_pos (by norm_num)
      (Real.log_pos (by exact_mod_cast hn))
  have hlogrho : 0 < Real.log rho := Real.log_pos hrho
  have hlogW : 0 < Real.log (W : Real) :=
    Real.log_pos (by exact_mod_cast (show 1 < W by omega))
  have hmain :
      2 * (tangentConstant * N / Real.log rho) *
          (2 * delta + 3 * M.ratio) <=
        (6 / Real.log rho) * tangentConstant * N *
          (delta + M.ratio) := by
    have hfactor : 0 <= tangentConstant * N / Real.log rho :=
      div_nonneg (mul_nonneg htangent hN) hlogrho.le
    have hfactorDelta :
        0 <= (tangentConstant * N / Real.log rho) * delta :=
      mul_nonneg hfactor hdelta.le
    ring_nf at hfactorDelta ⊢
    nlinarith
  calc
    bankPaperCanonicalRatioCellMomentTotalTrafficMajorant M n W rho
        (tangentConstant * N / Real.log (y n)) =
      2 * (tangentConstant * N / Real.log rho) *
          (2 * delta + 3 * M.ratio) +
        bankPaperCanonicalRatioCellTrafficErrorCoefficient
          M n W rho tangentConstant * N := by
      unfold bankPaperCanonicalRatioCellMomentTotalTrafficMajorant
        bankPaperCanonicalRatioCellMomentCutMajorant
        bankPaperCanonicalHarmonicResidualL1Majorant
        bankPaperCanonicalHarmonicTailMajorant
        bankPaperCanonicalRatioCellFloorLoss
        bankPaperCanonicalRatioCellTrafficErrorCoefficient
      field_simp [hlogy.ne', hlogrho.ne', hlogW.ne']; ring
    _ <= (6 / Real.log rho) * tangentConstant * N *
          (delta + M.ratio) +
        bankPaperCanonicalRatioCellTrafficErrorCoefficient
          M n W rho tangentConstant * N :=
      add_le_add hmain le_rfl
    _ = bankPaperCanonicalRatioCellTrafficConstant rho *
          tangentConstant * N * (delta + M.ratio) +
        bankPaperCanonicalRatioCellTrafficErrorCoefficient
          M n W rho tangentConstant * N := rfl

/-! ## Concrete geometry for the normalized pointwise port -/



/-- The current cell start remains beyond the fixed arithmetic cutoff. -/
theorem bankPaperCanonical_fixedCutoff_le_ratioCellCurrentLower
    {delta eta : Real} (M : RegularRelativeMesh.Mesh delta eta)
    {n W : Nat} (hdelta : 0 < delta) (hn : 1 < n)
    (hW : W ≠ 0) (S : ScaleSeparation M n W)
    {rho : Real} (hrho : 1 < rho)
    (p : BankPaperCanonicalTangentPrime n W) :
    W <= bankPaperCanonicalRatioCellCurrentLower
      M hdelta hn hW S rho p := by
  let band := bankPaperCanonicalExponentBandOf M hdelta hn hW S p
  let cell := bankPaperCanonicalRatioCellIndex M hdelta hn hW S rho p
  exact (bankPaperCanonical_fixedCutoff_le_exponentBandLower
    M hdelta hn hW S band).trans (by
      have hmono := tangentMultiplicativeRatioCutoff_mono
        (lower := bankPaperCanonicalExponentBandLower M n W band)
        (rho := rho) hrho.le (Nat.zero_le cell)
      simpa only [bankPaperCanonicalRatioCellCurrentLower, band, cell,
        tangentMultiplicativeRatioCutoff_zero] using hmono)





/-! ## Scalar Mertens cancellation in one PNT-normalized port -/









/-! ## Collapse of the remaining band endpoint gap -/

/-- Every canonical exponent band has ordinary logarithmic width at most
`(delta + ratio) * log y`, up to the single `log 2` floor loss. -/
theorem bankPaperCanonical_exponentBand_logWidth_le
    {delta eta : Real} (M : RegularRelativeMesh.Mesh delta eta)
    {n W : Nat} (hdelta : 0 < delta) (hn : 1 < n)
    (hWtwo : 2 <= W) (S : ScaleSeparation M n W)
    (hTwo : forall k : Fin M.cellCount,
      2 <= scalePoint n (M.lower k))
    (band : BankPaperCanonicalExponentBand M) :
    Real.log (bankPaperCanonicalExponentBandUpper M n W band : Real) -
        Real.log (bankPaperCanonicalExponentBandLower M n W band : Real) <=
      (delta + M.ratio) * Real.log (y n) + Real.log 2 := by
  have hlogy : 0 < Real.log (y n) := by
    rw [Scale.log_y (Nat.zero_lt_of_lt hn)]
    exact mul_pos (by norm_num)
      (Real.log_pos (by exact_mod_cast hn))
  refine Fin.cases ?_ (fun k => ?_) band
  · have hxTwo : 2 <= scalePoint n delta := by
      have hWReal : (2 : Real) <= W := by exact_mod_cast hWtwo
      nlinarith [S.low]
    have hupperCoord := (floor_scalePoint_coordinate_bounds hn hxTwo).2
    have hupper :
        Real.log (fullCutoff M n W 1 : Real) <=
          delta * Real.log (y n) := by
      have hmul := mul_le_mul_of_nonneg_right hupperCoord hlogy.le
      simpa only [RegularMeshPrimeCutoffs.Mesh.fullCutoff_succ,
        M.endpoint_zero, KernelPrimeQuadrature.realLogCoordinate,
        div_mul_cancel₀ _ hlogy.ne'] using hmul
    have hlower : 0 <= Real.log (W : Real) :=
      Real.log_nonneg (by exact_mod_cast (show 1 <= W by omega))
    have hratioLog :
        0 <= M.ratio * Real.log (y n) :=
      mul_nonneg M.ratio_pos.le hlogy.le
    have hlogTwo : 0 <= Real.log 2 :=
      Real.log_nonneg (by norm_num)
    simp only [bankPaperCanonicalExponentBandUpper,
      bankPaperCanonicalExponentBandLower, Fin.val_zero,
      Nat.zero_add, RegularMeshPrimeCutoffs.Mesh.fullCutoff_zero]
    nlinarith
  · let q : Fin M.cellCount := k
    have hLower := (floor_scalePoint_coordinate_bounds hn (hTwo q)).1
    have hUpperTwo : 2 <= scalePoint n (M.upper q) := by
      have hsep := (S.positive q).2
      nlinarith [hTwo q]
    have hUpper := (floor_scalePoint_coordinate_bounds hn hUpperTwo).2
    have hcoordGap :
        KernelPrimeQuadrature.realLogCoordinate (y n)
              (fullCutoff M n W (q.1 + 2) : Real) -
            KernelPrimeQuadrature.realLogCoordinate (y n)
              (fullCutoff M n W (q.1 + 1) : Real) <=
          M.width q + Real.log 2 / Real.log (y n) := by
      have hLower' :
          M.lower q - Real.log 2 / Real.log (y n) <=
            KernelPrimeQuadrature.realLogCoordinate (y n)
              (fullCutoff M n W (q.1 + 1) : Real) := by
        simpa only [RegularMeshPrimeCutoffs.Mesh.fullCutoff_succ,
          RegularRelativeMesh.Mesh.lower] using hLower
      have hUpper' :
          KernelPrimeQuadrature.realLogCoordinate (y n)
              (fullCutoff M n W (q.1 + 2) : Real) <= M.upper q := by
        simpa only [show q.1 + 2 = (q.1 + 1) + 1 by omega,
          RegularMeshPrimeCutoffs.Mesh.fullCutoff_succ,
          RegularRelativeMesh.Mesh.upper] using hUpper
      unfold RegularRelativeMesh.Mesh.width
      linarith
    have hlogGap :
        Real.log (fullCutoff M n W (q.1 + 2) : Real) -
            Real.log (fullCutoff M n W (q.1 + 1) : Real) <=
          M.width q * Real.log (y n) + Real.log 2 := by
      have hmul := mul_le_mul_of_nonneg_right hcoordGap hlogy.le
      unfold KernelPrimeQuadrature.realLogCoordinate at hmul
      field_simp [hlogy.ne'] at hmul
      nlinarith
    have hwidth := M.width_le_ratio hdelta q
    have hscaled :
        M.width q * Real.log (y n) <=
          (delta + M.ratio) * Real.log (y n) := by
      apply mul_le_mul_of_nonneg_right _ hlogy.le
      linarith
    simpa only [bankPaperCanonicalExponentBandUpper,
      bankPaperCanonicalExponentBandLower, Fin.val_succ, q] using
      hlogGap.trans (by nlinarith [hscaled])

/-- Replacing the band lower endpoint by the later current-cell start can
only shorten the logarithmic gap. -/
theorem bankPaperCanonical_currentLower_bandUpper_logGap_le
    {delta eta : Real} (M : RegularRelativeMesh.Mesh delta eta)
    {n W : Nat} (hdelta : 0 < delta) (hn : 1 < n)
    (hWtwo : 2 <= W) (S : ScaleSeparation M n W)
    {rho : Real} (hrho : 1 < rho)
    (hTwo : forall k : Fin M.cellCount,
      2 <= scalePoint n (M.lower k))
    (p : BankPaperCanonicalTangentPrime n W) :
    let A := bankPaperCanonicalRatioCellCurrentLower
      M hdelta hn (by omega) S rho p
    let Y := bankPaperCanonicalExponentBandUpper M n W
      (bankPaperCanonicalExponentBandOf M hdelta hn (by omega) S p)
    Real.log (Y : Real) - Real.log (A : Real) <=
      (delta + M.ratio) * Real.log (y n) + Real.log 2 := by
  dsimp only
  let band := bankPaperCanonicalExponentBandOf M hdelta hn
    (by omega : W ≠ 0) S p
  let lower := bankPaperCanonicalExponentBandLower M n W band
  let A := bankPaperCanonicalRatioCellCurrentLower
    M hdelta hn (by omega : W ≠ 0) S rho p
  have hLowerA : lower <= A := by
    unfold A bankPaperCanonicalRatioCellCurrentLower lower
    have hmono := tangentMultiplicativeRatioCutoff_mono
      (lower := bankPaperCanonicalExponentBandLower M n W band)
      (rho := rho) hrho.le
      (Nat.zero_le (bankPaperCanonicalRatioCellIndex
        M hdelta hn (by omega) S rho p))
    simpa only [tangentMultiplicativeRatioCutoff_zero] using hmono
  have hlowerPos : (0 : Real) < lower := by
    exact_mod_cast bankPaperCanonicalExponentBandLower_pos
      M hdelta hn (by omega) S band
  have hlogLowerA : Real.log (lower : Real) <= Real.log (A : Real) :=
    Real.log_le_log hlowerPos (by exact_mod_cast hLowerA)
  calc
    Real.log (bankPaperCanonicalExponentBandUpper M n W band : Real) -
          Real.log (A : Real) <=
        Real.log (bankPaperCanonicalExponentBandUpper M n W band : Real) -
          Real.log (lower : Real) := sub_le_sub_left hlogLowerA _
    _ <= (delta + M.ratio) * Real.log (y n) + Real.log 2 :=
      bankPaperCanonical_exponentBand_logWidth_le
        M hdelta hn hWtwo S hTwo band

/-! ## Uniform paper-scale port envelope -/



/-- The PNT-normalized analytic envelope is uniformly bounded by the
paper-sized scalar port majorant. -/
theorem bankPaperCanonical_weightedPNTEnvelope_le_uniformPortMajorant
    {delta eta : Real} (M : RegularRelativeMesh.Mesh delta eta)
    {n W : Nat} (hdelta : 0 < delta) (hn : 1 < n)
    (hWtwo : 2 <= W) (S : ScaleSeparation M n W)
    {rho scale : Real} (hrho : 1 < rho) (hscale : 0 <= scale)
    (hMertens : fullReciprocalSumUniformCutoff <= W)
    (hTwo : forall k : Fin M.cellCount,
      2 <= scalePoint n (M.lower k))
    (p : BankPaperCanonicalTangentPrime n W) :
    (bankPaperCanonicalTangentPrimeLabel p : Real) *
        (bankPaperCanonicalRatioCellPortNumeratorEnvelope
            M hdelta hn (by omega) S rho scale p /
          bankPaperCanonicalRatioCellPNTDenominator
            M hdelta hn (by omega) S rho p) <=
      bankPaperCanonicalRatioCellUniformPortMajorant
        M n W rho scale := by
  let A := bankPaperCanonicalRatioCellCurrentLower
    M hdelta hn (by omega : W ≠ 0) S rho p
  let Y := bankPaperCanonicalExponentBandUpper M n W
    (bankPaperCanonicalExponentBandOf M hdelta hn (by omega) S p)
  have hWA : W <= A := by
    simpa only [A] using
      bankPaperCanonical_fixedCutoff_le_ratioCellCurrentLower
        M hdelta hn (by omega) S hrho p
  have hWlog : 0 < Real.log (W : Real) :=
    Real.log_pos (by exact_mod_cast (show 1 < W by omega))
  have hAlog : 0 < Real.log (A : Real) :=
    Real.log_pos (by exact_mod_cast (show 1 < A by omega))
  have hlogWA : Real.log (W : Real) <= Real.log (A : Real) :=
    Real.log_le_log (by positivity) (by exact_mod_cast hWA)
  have hpowWA : Real.log (W : Real) ^ 2 <=
      Real.log (A : Real) ^ 2 :=
    pow_le_pow_left₀ hWlog.le hlogWA 2
  have hconstant : 0 <=
      5 * fullReciprocalSumUniformConstant := by
    exact mul_nonneg (by norm_num)
      fullReciprocalSumUniformConstant_pos.le
  have herror :
      5 * fullReciprocalSumUniformConstant /
          Real.log (A : Real) ^ 2 <=
        5 * fullReciprocalSumUniformConstant /
          Real.log (W : Real) ^ 2 := by
    apply (div_le_div_iff₀ (sq_pos_of_pos hAlog) (sq_pos_of_pos hWlog)).2
    exact mul_le_mul_of_nonneg_left hpowWA hconstant
  have hgap := bankPaperCanonical_currentLower_bandUpper_logGap_le
    M hdelta hn hWtwo S hrho hTwo p
  have hinside :
      Real.log (Y : Real) - Real.log (A : Real) +
          5 * fullReciprocalSumUniformConstant /
            Real.log (A : Real) ^ 2 <=
        (delta + M.ratio) * Real.log (y n) + Real.log 2 +
          5 * fullReciprocalSumUniformConstant /
            Real.log (W : Real) ^ 2 := by
    linarith
  have hfactor : 0 <= (8 * rho ^ 2 / (rho - 1)) * scale := by
    exact mul_nonneg (div_nonneg (by positivity) (sub_pos.mpr hrho).le) hscale
  calc
    (bankPaperCanonicalTangentPrimeLabel p : Real) *
          (bankPaperCanonicalRatioCellPortNumeratorEnvelope
              M hdelta hn (by omega) S rho scale p /
            bankPaperCanonicalRatioCellPNTDenominator
              M hdelta hn (by omega) S rho p) <=
        (8 * rho ^ 2 / (rho - 1)) * scale *
          (Real.log (Y : Real) - Real.log (A : Real) +
            5 * fullReciprocalSumUniformConstant /
              Real.log (A : Real) ^ 2) := by
      simpa only [A, Y] using
        bankPaperCanonical_weightedPNTEnvelope_le_logGap
          M hdelta hn hWtwo S hrho hscale hMertens p
    _ <= (8 * rho ^ 2 / (rho - 1)) * scale *
        ((delta + M.ratio) * Real.log (y n) + Real.log 2 +
          5 * fullReciprocalSumUniformConstant /
            Real.log (W : Real) ^ 2) :=
      mul_le_mul_of_nonneg_left hinside hfactor
    _ = bankPaperCanonicalRatioCellUniformPortMajorant
        M n W rho scale := rfl

/-- Assembly-facing uniform-port form: the proved PNT envelope and its
uniform scalar collapse are composed in one statement. -/
theorem bankPaperCanonical_weightedRatioCellUniformPortLoad_le_majorant
    {delta eta : Real} (M : RegularRelativeMesh.Mesh delta eta)
    {n W : Nat} (hdelta : 0 < delta) (hn : 1 < n)
    (hWtwo : 2 <= W) (S : ScaleSeparation M n W)
    {rho scale : Real} (hrho : 1 < rho) (hscale : 0 <= scale)
    (hMertens : fullReciprocalSumUniformCutoff <= W)
    (hPNT : TangentFixedRatioPrimeCountLower W rho)
    (hTwo : forall k : Fin M.cellCount,
      2 <= scalePoint n (M.lower k))
    (residual : BankPaperCanonicalTangentPrime n W -> Real)
    (hbalance : forall band : BankPaperCanonicalExponentBand M,
      (∑ q : BankPaperCanonicalTangentPrime n W,
        if bankPaperCanonicalExponentBandOf
            M hdelta hn (by omega) S q = band then residual q else 0) = 0)
    (hpointwise : forall q : BankPaperCanonicalTangentPrime n W,
      |residual q| <= bankPaperCanonicalHarmonicPointwiseUpper scale q)
    (p : BankPaperCanonicalTangentPrime n W) :
    (bankPaperCanonicalTangentPrimeLabel p : Real) *
        tangentRatioCellUniformPortLoad residual
          (bankPaperCanonicalExponentBandOf M hdelta hn (by omega) S)
          (bankPaperCanonicalRatioCellIndex
            M hdelta hn (by omega) S rho) p <=
      bankPaperCanonicalRatioCellUniformPortMajorant
        M n W rho scale := by
  calc
    (bankPaperCanonicalTangentPrimeLabel p : Real) *
          tangentRatioCellUniformPortLoad residual
            (bankPaperCanonicalExponentBandOf M hdelta hn (by omega) S)
            (bankPaperCanonicalRatioCellIndex
              M hdelta hn (by omega) S rho) p <=
        (bankPaperCanonicalTangentPrimeLabel p : Real) *
          (bankPaperCanonicalRatioCellPortNumeratorEnvelope
              M hdelta hn (by omega) S rho scale p /
            bankPaperCanonicalRatioCellPNTDenominator
              M hdelta hn (by omega) S rho p) :=
      bankPaperCanonical_weightedRatioCellUniformPortLoad_le_PNTEnvelope
        M hdelta hn hWtwo S hrho hscale hMertens hPNT
          residual hbalance hpointwise p
    _ <= bankPaperCanonicalRatioCellUniformPortMajorant
        M n W rho scale :=
      bankPaperCanonical_weightedPNTEnvelope_le_uniformPortMajorant
        M hdelta hn hWtwo S hrho hscale hMertens hTwo p

/-! ## Paper-scale scalar reduction for the incident ledger -/







/-- The paper specialization of `weightedResidual + 2*weightedPort`.
The main constant is fixed by `rho`; the only remainder is the displayed
scalar multiple of `1/log y`. -/
theorem bankPaperCanonical_incidentMajorant_paperScale
    {delta eta : Real} (M : RegularRelativeMesh.Mesh delta eta)
    {W n : Nat} {rho tangentConstant N : Real}
    (hn : 1 < n) (hWtwo : 2 <= W) (hrho : 1 < rho) :
    tangentConstant * N / Real.log (y n) +
        2 * bankPaperCanonicalRatioCellUniformPortMajorant M n W rho
          (tangentConstant * N / Real.log (y n)) =
      bankPaperCanonicalRatioCellIncidentConstant rho *
          tangentConstant * N * (delta + M.ratio) +
        bankPaperCanonicalRatioCellIncidentErrorCoefficient
          W n rho tangentConstant * N := by
  have hlogy : Real.log (y n) ≠ 0 := by
    rw [Scale.log_y (Nat.zero_lt_of_lt hn)]
    exact (mul_pos (by norm_num)
      (Real.log_pos (by exact_mod_cast hn))).ne'
  have hrhoGap : rho - 1 ≠ 0 := (sub_pos.mpr hrho).ne'
  have hlogW : Real.log (W : Real) ≠ 0 :=
    (Real.log_pos (by exact_mod_cast (show 1 < W by omega))).ne'
  unfold bankPaperCanonicalRatioCellUniformPortMajorant
    bankPaperCanonicalRatioCellIncidentConstant
    bankPaperCanonicalRatioCellIncidentErrorCoefficient
  unfold bankPaperCanonicalRatioCellPortConstant
  field_simp [hlogy, hrhoGap, hlogW]; ring



/-! ## A manifestly vanishing upper coefficient for total traffic -/











/-! ## Explicit fixed choices for the paper budgets -/





















end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankPaperCanonicalActualP87RatioCellTrafficConnector -/
section


/-!
# Actual Proposition 8.7 residuals in the canonical ratio-cell traffic ledger

The actual Proposition 8.7 endpoint has primewise residual bound

`Cpost * q / (p * B.L)`,

where `q = B.q` is the literal active mass.  This file connects that bound to
the audited canonical ratio-cell moment and port estimates.  In particular,
the traffic scale below is always the literal

`Cpost * B.q / B.L`;

the active mass is never replaced by `1`.

There are two levels of output.

* The finite connector gives the weighted-residual, uniform-port, and total
  moment-traffic bounds at the actual scale, for the literal canonical
  partition.
* The paper-budget connector gives the scalar Section 9 main/error form after
  receiving the precise scale domination

  `Cpost * B.q / B.L <= tangentConstant * N / log y`.

The latter comparison is not manufactured here.  A reusable normalization
lemma shows that it follows from the equivalent numerator comparison after
using the exact identity `log y = (2/9) B.L`.

Finally, the eventual connector consumes the actual `MomentReady` producer.
It is uniform in the scale-separation proof and in every residual satisfying
the displayed balance and actual-scale pointwise hypotheses.  The quantitative
Mertens and fixed-ratio PNT hypotheses remain visible traffic inputs.
-/

open Filter
open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.PaperBridgeFit
open Erdos390.Full.PrimeBandQuadrature
open Erdos390.Full.RegularMeshPrimeCutoffs
open Erdos390.Full.RegularRelativeMesh

noncomputable section

/-! ## Exact comparison of the actual P87 and harmonic pointwise forms -/

/-- The literal actual-P87 pointwise upper bound is exactly the harmonic
majorant at scale `Cpost * B.q / B.L`. -/
theorem bankPaperCanonicalActualP87PointwiseUpper_eq_harmonicScale
    {Head Band : Type*} [Fintype Head] [DecidableEq Head]
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData Head Band) (Cpost : Real)
    (p : BankPaperCanonicalTangentPrime
      B.sampleData.n B.sampleData.W) :
    bankPaperCanonicalActualP87PointwiseUpper B B.q Cpost p =
      bankPaperCanonicalHarmonicPointwiseUpper
        (Cpost * B.q / B.L) p := by
  have hp : (p.1 : Real) ≠ 0 := by
    exact_mod_cast (bankPaperCanonicalTangentPrimeLabel_prime p).pos.ne'
  have hL : B.L ≠ 0 := B.L_pos.ne'
  unfold bankPaperCanonicalActualP87PointwiseUpper
    bankPaperCanonicalHarmonicPointwiseUpper
    bankPaperCanonicalTangentPrimeLabel
  field_simp [hp, hL]

/-- The harmonic primewise upper bound is monotone in its scalar scale. -/
theorem bankPaperCanonicalHarmonicPointwiseUpper_mono_scale
    {n W : Nat} {scale scale' : Real} (hscale : scale <= scale')
    (p : BankPaperCanonicalTangentPrime n W) :
    bankPaperCanonicalHarmonicPointwiseUpper scale p <=
      bankPaperCanonicalHarmonicPointwiseUpper scale' p := by
  unfold bankPaperCanonicalHarmonicPointwiseUpper
  exact div_le_div_of_nonneg_right hscale (Nat.cast_nonneg _)



/-! ## The common finite traffic payload -/

private theorem bankPaperCanonical_ratioCellMomentTraffic_payload
    {delta eta : Real} (M : RegularRelativeMesh.Mesh delta eta)
    {n W : Nat} (hdelta : 0 < delta) (hn : 1 < n)
    (hWtwo : 2 <= W) (S : ScaleSeparation M n W)
    {rho scale : Real} (hrho : 1 < rho) (hscale : 0 <= scale)
    (hMertens : fullReciprocalSumUniformCutoff <= W)
    (hPNT : TangentFixedRatioPrimeCountLower W rho)
    (hTwo : forall k : Fin M.cellCount,
      2 <= scalePoint n (M.lower k))
    (Hmoment : RegularMeshPrimeCutoffs.Mesh.MomentReady M
      (RegularMeshPrimeCutoffs.Mesh.canonicalPartition
        M hdelta hn (by omega) S))
    (residual : BankPaperCanonicalTangentPrime n W -> Real)
    (hbalance : forall band : BankPaperCanonicalExponentBand M,
      (∑ p : BankPaperCanonicalTangentPrime n W,
        if bankPaperCanonicalExponentBandOf
            M hdelta hn (by omega) S p = band then residual p else 0) = 0)
    (hpointwise : forall p : BankPaperCanonicalTangentPrime n W,
      |residual p| <= bankPaperCanonicalHarmonicPointwiseUpper scale p) :
    (forall p : BankPaperCanonicalTangentPrime n W,
      (bankPaperCanonicalTangentPrimeLabel p : Real) * |residual p| <=
        scale) ∧
      (forall p : BankPaperCanonicalTangentPrime n W,
        (bankPaperCanonicalTangentPrimeLabel p : Real) *
            tangentRatioCellUniformPortLoad residual
              (bankPaperCanonicalExponentBandOf
                M hdelta hn (by omega) S)
              (bankPaperCanonicalRatioCellIndex
                M hdelta hn (by omega) S rho) p <=
          bankPaperCanonicalRatioCellUniformPortMajorant
            M n W rho scale) ∧
      tangentDistributedTotalTrafficLedger residual
          (tangentRatioCellCanonicalCutTraffic
            (bankPaperCanonicalLastRatioCell M (n := n) (W := W) rho)
            residual
            (bankPaperCanonicalExponentBandOf
              M hdelta hn (by omega) S)
            (bankPaperCanonicalRatioCellIndex
              M hdelta hn (by omega) S rho)) <=
        bankPaperCanonicalRatioCellMomentTotalTrafficMajorant
          M n W rho scale := by
  refine ⟨?_, ?_, ?_⟩
  · intro p
    exact bankPaperCanonical_weightedResidual_le_harmonicScale
      residual hpointwise p
  · intro p
    exact
      bankPaperCanonical_weightedRatioCellUniformPortLoad_le_majorant
        M hdelta hn hWtwo S hrho hscale hMertens hPNT hTwo
        residual hbalance hpointwise p
  · exact bankPaperCanonical_ratioCellTotalTraffic_le_momentMajorant
      M hdelta hn hWtwo S hrho hscale hMertens hTwo Hmoment
      residual hbalance hpointwise

/-! ## Selector-facing actual-P87 traffic -/



/-! ## Assembly-facing paper main/error form -/

/-- If the literal actual-P87 scale is dominated by a chosen paper scale,
the same endpoint supplies the four quantitative premises used in the
distributed assembly:

* weighted residual;
* weighted uniform port;
* total traffic in fixed-main plus vanishing-error form; and
* the matching weighted-incident identity.

The domination premise is deliberately displayed.  It is the only bridge
from the actual active mass `B.q` to the assembly normalization `N`. -/
theorem bankPaperCanonical_actualP87RatioCellPaperTraffic_of_scale_le
    {delta eta : Real} (M : RegularRelativeMesh.Mesh delta eta)
    {Head : Type*} [Fintype Head] [DecidableEq Head]
    (B : BridgeData Head (BankPaperCanonicalExponentBand M))
    {c : Real} {depth : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (fixed candidates : Finset Nat) (selector : Nat -> Real)
    (hdelta : 0 < delta) (hWtwo : 2 <= B.sampleData.W)
    (S : ScaleSeparation M B.sampleData.n B.sampleData.W)
    (hpartition : B.partition =
      RegularMeshPrimeCutoffs.Mesh.canonicalPartition
        M hdelta B.n_gt_one (by omega) S)
    {rho Cpost tangentConstant N : Real}
    (hrho : 1 < rho) (htangent : 0 <= tangentConstant) (hN : 0 <= N)
    (hscaleDom : Cpost * B.q / B.L <=
      tangentConstant * N / Real.log (y B.sampleData.n))
    (hMertens : fullReciprocalSumUniformCutoff <= B.sampleData.W)
    (hPNT : TangentFixedRatioPrimeCountLower B.sampleData.W rho)
    (hTwo : forall k : Fin M.cellCount,
      2 <= scalePoint B.sampleData.n (M.lower k))
    (Hmoment : RegularMeshPrimeCutoffs.Mesh.MomentReady M
      (RegularMeshPrimeCutoffs.Mesh.canonicalPartition
        M hdelta B.n_gt_one (by omega) S))
    {prefixUpper : BankPaperCanonicalExponentBand M -> Nat -> Real}
    (Hselector : BankPaperCanonicalRoundedSelectorTangentInput
      R certificate fixed candidates
      B.partition.band
      (bankPaperCanonicalRatioCellIndex
        M hdelta B.n_gt_one (by omega) S rho)
      (bankPaperCanonicalActualP87PointwiseUpper B B.q Cpost)
      prefixUpper selector) :
    let residual :=
      bankPaperCanonicalTangentResidual R certificate
        fixed candidates selector
    let paperScale :=
      tangentConstant * N / Real.log (y B.sampleData.n)
    (forall p : BankPaperCanonicalTangentPrime
        B.sampleData.n B.sampleData.W,
      (bankPaperCanonicalTangentPrimeLabel p : Real) * |residual p| <=
        paperScale) ∧
      (forall p : BankPaperCanonicalTangentPrime
          B.sampleData.n B.sampleData.W,
        (bankPaperCanonicalTangentPrimeLabel p : Real) *
            tangentRatioCellUniformPortLoad residual
              (bankPaperCanonicalExponentBandOf
                M hdelta B.n_gt_one (by omega) S)
              (bankPaperCanonicalRatioCellIndex
                M hdelta B.n_gt_one (by omega) S rho) p <=
          bankPaperCanonicalRatioCellUniformPortMajorant M
            B.sampleData.n B.sampleData.W rho paperScale) ∧
      tangentDistributedTotalTrafficLedger residual
          (tangentRatioCellCanonicalCutTraffic
            (bankPaperCanonicalLastRatioCell M
              (n := B.sampleData.n) (W := B.sampleData.W) rho)
            residual
            (bankPaperCanonicalExponentBandOf
              M hdelta B.n_gt_one (by omega) S)
            (bankPaperCanonicalRatioCellIndex
              M hdelta B.n_gt_one (by omega) S rho)) <=
        bankPaperCanonicalRatioCellTrafficConstant rho *
            tangentConstant * N * (delta + M.ratio) +
          bankPaperCanonicalRatioCellTrafficErrorCoefficient M
            B.sampleData.n B.sampleData.W rho tangentConstant * N ∧
      paperScale +
          2 * bankPaperCanonicalRatioCellUniformPortMajorant M
            B.sampleData.n B.sampleData.W rho paperScale =
        bankPaperCanonicalRatioCellIncidentConstant rho *
            tangentConstant * N * (delta + M.ratio) +
          bankPaperCanonicalRatioCellIncidentErrorCoefficient
            B.sampleData.W B.sampleData.n rho tangentConstant * N := by
  dsimp only
  let residual : BankPaperCanonicalTangentPrime
      B.sampleData.n B.sampleData.W -> Real :=
    bankPaperCanonicalTangentResidual (W := B.sampleData.W)
      R certificate fixed candidates selector
  let paperScale :=
    tangentConstant * N / Real.log (y B.sampleData.n)
  have HselectorCanonical : BankPaperCanonicalRoundedSelectorTangentInput
      R certificate fixed candidates
      (bankPaperCanonicalExponentBandOf
        M hdelta B.n_gt_one (by omega) S)
      (bankPaperCanonicalRatioCellIndex
        M hdelta B.n_gt_one (by omega) S rho)
      (bankPaperCanonicalActualP87PointwiseUpper B B.q Cpost)
      prefixUpper selector := by
    simpa only [bankPaperCanonicalExponentBandOf, hpartition] using Hselector
  have hbounds :=
    bankPaperCanonicalRoundedSelectorTangentInput_residualBounds
      HselectorCanonical
  have hbalance : forall band : BankPaperCanonicalExponentBand M,
      (∑ p : BankPaperCanonicalTangentPrime
          B.sampleData.n B.sampleData.W,
        if bankPaperCanonicalExponentBandOf
            M hdelta B.n_gt_one (by omega) S p = band then
          residual p else 0) = 0 := by
    simpa only [residual] using hbounds.1
  have hpointwiseActual : forall p : BankPaperCanonicalTangentPrime
      B.sampleData.n B.sampleData.W,
      |residual p| <=
        bankPaperCanonicalHarmonicPointwiseUpper
          (Cpost * B.q / B.L) p := by
    intro p
    calc
      |residual p| <=
          bankPaperCanonicalActualP87PointwiseUpper B B.q Cpost p := by
        simpa only [residual] using hbounds.2.1 p
      _ = bankPaperCanonicalHarmonicPointwiseUpper
          (Cpost * B.q / B.L) p :=
        bankPaperCanonicalActualP87PointwiseUpper_eq_harmonicScale
          B Cpost p
  have hpointwise : forall p : BankPaperCanonicalTangentPrime
      B.sampleData.n B.sampleData.W,
      |residual p| <=
        bankPaperCanonicalHarmonicPointwiseUpper paperScale p := by
    intro p
    exact (hpointwiseActual p).trans
      (bankPaperCanonicalHarmonicPointwiseUpper_mono_scale
        hscaleDom p)
  have hpaperScale : 0 <= paperScale := by
    exact div_nonneg (mul_nonneg htangent hN) B.log_y_pos.le
  have hpayload :=
    bankPaperCanonical_ratioCellMomentTraffic_payload
      M hdelta B.n_gt_one hWtwo S hrho hpaperScale hMertens hPNT
      hTwo Hmoment residual hbalance hpointwise
  have htotalScalar :=
    bankPaperCanonical_ratioCellMomentTotalTrafficMajorant_paperScale
      M hdelta B.n_gt_one hWtwo hrho htangent hN
  have hincident :=
    bankPaperCanonical_incidentMajorant_paperScale
      M B.n_gt_one hWtwo hrho
      (tangentConstant := tangentConstant) (N := N)
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [residual, paperScale] using hpayload.1
  · simpa only [residual, paperScale] using hpayload.2.1
  · exact hpayload.2.2.trans htotalScalar
  · simpa only [paperScale] using hincident

/-! ## Eventual actual-scale moment traffic -/



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



/-- Every Boolean exactification state is already one of the two precharge
state families deleted by the literal guarded candidate set. -/
theorem exactificationState_subset_roughCanonicalGuardSet
    {c : Real} {depth n h : Nat}
    (R : BankPaperRealization n (upperEndpoint n h))
    (certificate : GuardedCentralAnchorCertificate c depth n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (deltaStar : Real)
    (slot : SignedBankSlot (bankRoundingBetaOnSupport n))
    (selected : Bool) :
    R.exactificationState slot selected ⊆
      R.roughCanonicalGuardSet certificate deltaStar := by
  intro occurrence hoccurrence
  cases selected with
  | false =>
      rw [R.exactificationState_false, pathStateZero, indexedPathState,
        Finset.mem_image] at hoccurrence
      obtain ⟨component, _hcomponent, rfl⟩ := hoccurrence
      have hbase :
          R.pathStateZeroValue (bankPaperOppositeSlot slot) component ∈
            R.prechargeBaseState := by
        rw [R.pathStateZeroValue_eq_prechargeBaseStateValue]
        exact R.prechargeBaseStateValue_mem_prechargeBaseState
          (bankPaperPathComponentRequest
            (bankPaperOppositeSlot slot) component)
      simp [roughCanonicalGuardSet, tangentPaperNumericalGuardSet]
  | true =>
      rw [R.exactificationState_true, pathStateOne, indexedPathState,
        Finset.mem_image] at hoccurrence
      obtain ⟨component, _hcomponent, rfl⟩ := hoccurrence
      have halternate :
          R.pathStateOneValue (bankPaperOppositeSlot slot) component ∈
            R.prechargeAlternateState := by
        rw [R.pathStateOneValue_eq_prechargeAlternateStateValue]
        exact R.prechargeAlternateStateValue_mem_prechargeAlternateState
          (bankPaperPathComponentRequest
            (bankPaperOppositeSlot slot) component)
      simp [roughCanonicalGuardSet, tangentPaperNumericalGuardSet]

/-! ## The exact final finite geometry -/





/-- All final geometry except the explicitly named fixed-component collision
is forced by the literal intervals and the five-family numerical guard. -/
theorem bankPaperCanonicalSectionNineFinalGeometry_of_fixedComponentCollisionFree
    {c : Real} {depth n K : Nat}
    (R : BankPaperRealization n
      (upperEndpoint n (upperTailLength c n)))
    (certificate : GuardedCentralAnchorCertificate c depth n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (deltaStar : Real)
    (hKh : K * upperTailLength c n ≤ n)
    (hfixedComponents :
      R.BankPaperCanonicalSectionNineFixedComponentCollisionFree deltaStar) :
    R.BankPaperCanonicalSectionNineFinalGeometry
      certificate deltaStar K := by
  let candidates :=
    R.roughCanonicalGuardedCandidateSet certificate deltaStar K
  let fixed := R.paperFixedExceptionalFactors deltaStar
  let guard := R.roughCanonicalGuardSet certificate deltaStar
  have hcandidateInterval :
      candidates ⊆
        factorInterval n (upperEndpoint n (upperTailLength c n)) := by
    intro a ha
    have hraw :
        a ∈ roughRawCandidateSet n (upperTailLength c n) K :=
      R.roughCanonicalGuardedCandidateSet_subset_rawCandidateSet
        certificate deltaStar K ha
    rw [roughRawCandidateSet_eq_Ioc hKh] at hraw
    simp only [factorInterval, Finset.mem_Ioc] at hraw ⊢
    unfold upperEndpoint
    omega
  have hfixedInterval :
      fixed ⊆
        factorInterval n (upperEndpoint n (upperTailLength c n)) := by
    intro a ha
    have htail :=
      R.paperFixedExceptionalFactors_subset_tail deltaStar ha
    simp only [factorInterval, Finset.mem_Ioc] at htail ⊢
    omega
  have hcandidateGuard : Disjoint candidates guard := by
    exact R.roughCanonicalGuardedCandidateSet_disjoint_guardSet
      certificate deltaStar K
  have hfixedGuard : fixed ⊆ guard := by
    intro a ha
    simp [guard, fixed, roughCanonicalGuardSet,
      tangentPaperNumericalGuardSet, ha]
  have hanchorsGuard : certificate.anchors ⊆ guard := by
    intro a ha
    simp [guard, roughCanonicalGuardSet,
      tangentPaperNumericalGuardSet, ha]
  have hfixedCandidate : Disjoint fixed candidates := by
    exact (hcandidateGuard.mono Finset.Subset.rfl hfixedGuard).symm
  have hfixedBank : ∀ slot selected,
      Disjoint fixed (R.exactificationState slot selected) := by
    intro slot selected
    exact R.disjoint_exactificationState_of_disjoint_allComponentOccurrences
      fixed hfixedComponents slot selected
  have hcandidateBank : ∀ slot selected,
      Disjoint candidates (R.exactificationState slot selected) := by
    intro slot selected
    exact hcandidateGuard.mono Finset.Subset.rfl
      (R.exactificationState_subset_roughCanonicalGuardSet
        certificate deltaStar slot selected)
  have hanchorsFixed : Disjoint certificate.anchors fixed := by
    rw [Finset.disjoint_left]
    intro a haAnchor haFixed
    have haAnchorInterval := certificate.anchors_subset haAnchor
    have haFixedInterval :=
      R.paperFixedExceptionalFactors_subset_tail deltaStar haFixed
    simp only [Finset.mem_Ioc] at haAnchorInterval haFixedInterval
    omega
  have hanchorsCandidate : Disjoint certificate.anchors candidates := by
    exact (hcandidateGuard.mono Finset.Subset.rfl hanchorsGuard).symm
  unfold BankPaperCanonicalSectionNineFinalGeometry
  exact ⟨hcandidateInterval, hfixedInterval, hfixedCandidate, hfixedBank,
    hcandidateBank, hanchorsFixed, hanchorsCandidate⟩

/-! ## Reusable finite flow and output package -/





/-! ## Actual Post-Hfit/P87 finite composition -/

/-- Feed the literal Post-Hfit endpoint, actual-`q` P87 traffic bounds,
occupied canonical ratio cells, and clean-list estimates into the finite
distributed supplier.  The conclusion also retains the fixed-ratio locality
part of the canonical cell geometry rather than discarding it after the
occupancy projections are used.

The scalar main/error/ceiling budgets and the actual-scale comparison remain
visible finite hypotheses.  The raw traffic-error coefficient is used
literally; replacing it by the eventual upper coefficient is a separate
monotonicity step.  The only geometric collision premise is the named
fixed-component statement above.

The Section 9 finite geometry only uses the rounded tangent input and
the guarded endpoint slack from the Post-Hfit package.  This source-agnostic
form exposes exactly those two inputs, so any verified selector source can
feed the existing distributed construction. -/
theorem bankPaperCanonicalSectionNineFinalPayload_of_roundedSelector_guardedSlack
    {delta eta : Real} (M : RegularRelativeMesh.Mesh delta eta)
    {P : Finset Nat}
    (B : BridgeData (PaperHeadSimplex.Tag P)
      (BankPaperCanonicalExponentBand M))
    {c : Real} {depth K0 : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (deltaStar alpha beta sigma : Real)
    (_radius : NNReal) (Cpost : Real)
    (endpoint : Nat → Real)
    (hdelta : 0 < delta) (hWtwo : 2 ≤ B.sampleData.W)
    (S : ScaleSeparation M B.sampleData.n B.sampleData.W)
    (hpartition : B.partition =
      RegularMeshPrimeCutoffs.Mesh.canonicalPartition
        M hdelta B.n_gt_one (by omega) S)
    (r0 rho tangentConstant N density : Real)
    (hrho : 1 < rho) (hratio : rho ^ 3 < r0)
    (htangent : 0 ≤ tangentConstant) (hN : 0 < N)
    (hscaleDom : Cpost * B.q / B.L ≤
      tangentConstant * N / Real.log (y B.sampleData.n))
    (hMertens : fullReciprocalSumUniformCutoff ≤ B.sampleData.W)
    (hPNT : TangentFixedRatioPrimeCountLower B.sampleData.W rho)
    (hprime : TangentFixedRatioPrimeIntervalOccupied
      B.sampleData.W rho)
    (hTwo : ∀ k : Fin M.cellCount,
      2 ≤ scalePoint B.sampleData.n (M.lower k))
    (Hmoment : RegularMeshPrimeCutoffs.Mesh.MomentReady M
      (RegularMeshPrimeCutoffs.Mesh.canonicalPartition
        M hdelta B.n_gt_one (by omega) S))
    (HselectorPartition :
      BankPaperCanonicalRoundedSelectorTangentInput R certificate
        (R.paperFixedExceptionalFactors deltaStar)
        (R.roughCanonicalGuardedCandidateSet certificate
          deltaStar (K0 + 1))
        B.partition.band
      (bankPaperCanonicalRatioCellIndex
        M hdelta B.n_gt_one (by omega) S rho)
        (bankPaperCanonicalActualP87PointwiseUpper B B.q Cpost)
        (tangentRatioCellTailPointwiseUpper
          (bankPaperCanonicalActualP87PointwiseUpper B B.q Cpost)
          B.partition.band
          (bankPaperCanonicalRatioCellIndex
            M hdelta B.n_gt_one (by omega) S rho))
        endpoint)
    (Hslack :
      R.BankPaperCanonicalGuardedEndpointSlackConstruction certificate
        deltaStar B.sampleData.W (K0 + 1)
        alpha beta B.L sigma endpoint)
    (hKh : (K0 + 1) * upperTailLength c B.sampleData.n ≤
      B.sampleData.n)
    (hdensity : 0 < density) (hsigma : 0 < sigma)
    (hscale : B.L * N = (B.sampleData.n : Real))
    (hchargeDvd :
      R.selectorTailCharge (R.paperFixedExceptionalFactors deltaStar) ∣
        certificate.prechargedTailTarget)
    (hfixedComponents :
      R.BankPaperCanonicalSectionNineFixedComponentCollisionFree deltaStar)
    (hmain : tangentDistributedPaperMainBudget
      (bankPaperCanonicalRatioCellTrafficConstant rho)
      (bankPaperCanonicalRatioCellIncidentConstant rho)
      tangentConstant (delta + M.ratio) sigma ≤ density ^ 2 / 48)
    (herror : tangentDistributedPaperErrorBudget
      (bankPaperCanonicalRatioCellTrafficErrorCoefficient M
        B.sampleData.n B.sampleData.W rho tangentConstant)
      (bankPaperCanonicalRatioCellIncidentErrorCoefficient
        B.sampleData.W B.sampleData.n rho tangentConstant)
      sigma ≤ density ^ 2 / 96)
    (hceiling : tangentDistributedPaperCeilingBudget
      B.sampleData.n (yNat B.sampleData.n)
      (tangentDistributedSupportCount
        (BankPaperCanonicalTangentPrime
          B.sampleData.n B.sampleData.W)) ≤ density ^ 2 / 96)
    (hlowerPos :
      let flow :=
        R.bankPaperCanonicalSectionNineRatioCellFlow
          M certificate deltaStar (K0 + 1) hdelta B.n_gt_one
            (by omega) S rho endpoint
      ∀ request :
          BankPaperCanonicalDistributedTangentSplitRequest
            flow B.L sigma,
        0 < bankPaperCanonicalDistributedTangentLowerCard
          (density := density) request)
    (hlower :
      let flow :=
        R.bankPaperCanonicalSectionNineRatioCellFlow
          M certificate deltaStar (K0 + 1) hdelta B.n_gt_one
            (by omega) S rho endpoint
      ∀ request :
          BankPaperCanonicalDistributedTangentSplitRequest
            flow B.L sigma,
        bankPaperCanonicalDistributedTangentLowerCard
            (density := density) request ≤
          (tangentSplitCleanMultiplierLists
            (tangentPositiveFlowEdges flow)
            (tangentStarEdgeSource bankPaperCanonicalTangentPrimeLabel)
            (tangentStarEdgeTarget bankPaperCanonicalTangentPrimeLabel)
            B.L sigma
            (fun edge : BankPaperCanonicalTangentPrime
                B.sampleData.n B.sampleData.W ×
                BankPaperCanonicalTangentPrime
                  B.sampleData.n B.sampleData.W =>
              flow edge.1 edge.2)
            B.sampleData.n (K0 + 1)
            (upperTailLength c B.sampleData.n)
            (roughHeadModulus B.sampleData.W)
            (tangentPaperExceptionalCutoff deltaStar B.sampleData.n)
            (yNat B.sampleData.n) R.tangentPaperDedicatedRows
            (R.tangentPaperNumericalGuardSet certificate
              (R.paperFixedExceptionalFactors deltaStar))
            request).card)
    (hlowerScale :
      let flow :=
        R.bankPaperCanonicalSectionNineRatioCellFlow
          M certificate deltaStar (K0 + 1) hdelta B.n_gt_one
            (by omega) S rho endpoint
      ∀ request :
          BankPaperCanonicalDistributedTangentSplitRequest
            flow B.L sigma,
        ∀ side,
          density * B.sampleData.n ≤
            (bankPaperCanonicalDistributedTangentLowerCard
              (density := density) request : Real) *
              tangentEndpointLabel
                bankPaperCanonicalDistributedTangentRequestSource
                bankPaperCanonicalDistributedTangentRequestTarget
                side request) :
    R.BankPaperCanonicalSectionNineFinalPayload (K := K0 + 1)
      certificate deltaStar
      endpoint
      (R.bankPaperCanonicalSectionNineRatioCellFlow
        M certificate deltaStar (K0 + 1) hdelta B.n_gt_one
        (by omega) S rho endpoint)
      B.L sigma ∧
    TangentRatioCellGeometry bankPaperCanonicalTangentPrimeLabel
      (bankPaperCanonicalExponentBandOf
        M hdelta B.n_gt_one (by omega) S)
      (bankPaperCanonicalRatioCellIndex
        M hdelta B.n_gt_one (by omega) S rho) r0 := by
  let fixed := R.paperFixedExceptionalFactors deltaStar
  let candidates :=
    R.roughCanonicalGuardedCandidateSet certificate deltaStar (K0 + 1)
  let lastCell :=
    bankPaperCanonicalLastRatioCell M
      (n := B.sampleData.n) (W := B.sampleData.W) rho
  let bandOf :=
    bankPaperCanonicalExponentBandOf
      M hdelta B.n_gt_one (by omega) S
  let cellIndex :=
    bankPaperCanonicalRatioCellIndex
      M hdelta B.n_gt_one (by omega) S rho
  let pointwiseUpper :=
    bankPaperCanonicalActualP87PointwiseUpper B B.q Cpost
  let prefixUpper :=
    tangentRatioCellTailPointwiseUpper pointwiseUpper bandOf cellIndex
  let residual :=
    bankPaperCanonicalTangentResidual (W := B.sampleData.W) R certificate
      fixed candidates endpoint
  let paperScale :=
    tangentConstant * N / Real.log (y B.sampleData.n)
  let weightedPort :=
    bankPaperCanonicalRatioCellUniformPortMajorant M
      B.sampleData.n B.sampleData.W rho paperScale
  let trafficError :=
    bankPaperCanonicalRatioCellTrafficErrorCoefficient M
      B.sampleData.n B.sampleData.W rho tangentConstant
  let incidentError :=
    bankPaperCanonicalRatioCellIncidentErrorCoefficient
      B.sampleData.W B.sampleData.n rho tangentConstant
  let flow :=
    tangentRatioCellEarthmoverFlow lastCell residual bandOf cellIndex
  have Hselector :
      BankPaperCanonicalRoundedSelectorTangentInput R certificate
        fixed candidates bandOf cellIndex pointwiseUpper prefixUpper
        endpoint := by
    simpa only [bandOf, prefixUpper, bankPaperCanonicalExponentBandOf,
      hpartition] using HselectorPartition
  have hgeometry :=
    bankPaperCanonical_ratioCellGeometry_spec
      M hdelta B.n_gt_one (by omega) S hrho hratio hprime
  have htraffic :=
    bankPaperCanonical_actualP87RatioCellPaperTraffic_of_scale_le
      M B R certificate fixed candidates endpoint hdelta hWtwo S
      hpartition hrho htangent hN.le hscaleDom hMertens hPNT
      hTwo Hmoment HselectorPartition
  have hendpointInputs :=
    R.guardedEndpointSlackConstruction_candidateSetEndpointInputs
      certificate deltaStar
      alpha beta
      (flow := flow) endpoint hKh Hslack
  have hfixedPositive : ∀ a ∈ fixed, 0 < a := by
    intro a ha
    have htail :=
      R.paperFixedExceptionalFactors_subset_tail deltaStar ha
    exact Nat.zero_lt_of_lt (Finset.mem_Ioc.mp htail).1
  have hcleanPos : ∀ request :
      BankPaperCanonicalDistributedTangentSplitRequest flow B.L sigma,
      0 < bankPaperCanonicalDistributedTangentLowerCard
        (density := density) request := by
    simpa only [flow, residual, lastCell, bandOf, cellIndex, fixed,
      candidates, bankPaperCanonicalSectionNineRatioCellFlow] using
      hlowerPos
  have hcleanCard : ∀ request :
      BankPaperCanonicalDistributedTangentSplitRequest flow B.L sigma,
      bankPaperCanonicalDistributedTangentLowerCard
          (density := density) request ≤
        (tangentSplitCleanMultiplierLists
          (tangentPositiveFlowEdges flow)
          (tangentStarEdgeSource bankPaperCanonicalTangentPrimeLabel)
          (tangentStarEdgeTarget bankPaperCanonicalTangentPrimeLabel)
          B.L sigma
          (fun edge : BankPaperCanonicalTangentPrime
              B.sampleData.n B.sampleData.W ×
              BankPaperCanonicalTangentPrime
                B.sampleData.n B.sampleData.W =>
            flow edge.1 edge.2)
          B.sampleData.n (K0 + 1)
          (upperTailLength c B.sampleData.n)
          (roughHeadModulus B.sampleData.W)
          (tangentPaperExceptionalCutoff deltaStar B.sampleData.n)
          (yNat B.sampleData.n) R.tangentPaperDedicatedRows
          (R.tangentPaperNumericalGuardSet certificate fixed)
          request).card := by
    simpa only [flow, residual, lastCell, bandOf, cellIndex, fixed,
      candidates, bankPaperCanonicalSectionNineRatioCellFlow] using
      hlower
  have hcleanScale : ∀ request :
      BankPaperCanonicalDistributedTangentSplitRequest flow B.L sigma,
      ∀ side,
        density * B.sampleData.n ≤
          (bankPaperCanonicalDistributedTangentLowerCard
            (density := density) request : Real) *
            tangentEndpointLabel
              bankPaperCanonicalDistributedTangentRequestSource
              bankPaperCanonicalDistributedTangentRequestTarget
              side request := by
    simpa only [flow, residual, lastCell, bandOf, cellIndex, fixed,
      candidates, bankPaperCanonicalSectionNineRatioCellFlow] using
      hlowerScale
  have hsupplier :=
    R.exists_canonicalDistributedSectionNinePostTangentOutput_of_paperBudgets_on_candidates
      certificate fixed fixed candidates endpoint
      lastCell bandOf cellIndex pointwiseUpper prefixUpper Hselector
      density B.L sigma N
      (bankPaperCanonicalRatioCellTrafficConstant rho)
      (bankPaperCanonicalRatioCellIncidentConstant rho)
      tangentConstant (delta + M.ratio)
      trafficError incidentError paperScale weightedPort
      (Nat.zero_lt_of_lt B.n_gt_one) hdensity B.L_pos hsigma hN hscale
      hfixedPositive hchargeDvd hgeometry.1 hgeometry.2.1
      (by
        simpa only [residual, paperScale] using htraffic.1)
      (by
        simpa only [residual, bandOf, cellIndex, weightedPort] using
          htraffic.2.1)
      (by
        simpa only [residual, lastCell, bandOf, cellIndex, trafficError]
          using htraffic.2.2.1)
      (by
        simpa only [paperScale, weightedPort, incidentError] using
          htraffic.2.2.2.le)
      hmain herror hceiling hcleanPos hcleanCard hcleanScale
      hendpointInputs.1 hendpointInputs.2
  obtain ⟨multiplier, hmultiplier, hdistinct, hdivergence,
    hboundary, output, houtput⟩ := hsupplier
  have hfinalGeometry :=
    R.bankPaperCanonicalSectionNineFinalGeometry_of_fixedComponentCollisionFree
      certificate deltaStar hKh hfixedComponents
  constructor
  · refine ⟨multiplier, ?_, ?_, ?_, ?_, output, ?_, hchargeDvd,
      hfinalGeometry⟩
    · simpa only [flow, residual, lastCell, bandOf, cellIndex, fixed,
        candidates, bankPaperCanonicalSectionNineRatioCellFlow] using
        hmultiplier
    · simpa only [flow, residual, lastCell, bandOf, cellIndex, fixed,
        candidates, bankPaperCanonicalSectionNineRatioCellFlow] using
        hdistinct
    · simpa only [flow, residual, lastCell, bandOf, cellIndex, fixed,
        candidates, bankPaperCanonicalSectionNineRatioCellFlow] using
        hdivergence
    · simpa only [flow, residual, lastCell, bandOf, cellIndex, fixed,
        candidates, bankPaperCanonicalSectionNineRatioCellFlow] using
        hboundary
    · simpa only [flow, residual, lastCell, bandOf, cellIndex, fixed,
        candidates, bankPaperCanonicalSectionNineRatioCellFlow] using
        houtput
  · exact hgeometry.2.2

end BankPaperRealization

end

end Erdos390.WholePaper

end

theorem solution : Erdos390.RemainingAnalyticGoal004_011 := by
  exact @Erdos390.WholePaper.BankPaperRealization.bankPaperCanonicalSectionNineFinalPayload_of_roundedSelector_guardedSlack
