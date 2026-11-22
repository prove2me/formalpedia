-- Prove2me | solution 1 for Erdos390.WholePaper.BankPaperRealization.bankPaperCanonicalSectionNinePostHeight_sourceFirstPreselectedPostHfitInput_compact
-- status  : ACCEPTED   (prove)
-- author  : @doctosil
-- created : 2026-09-17T17:51:28.77667+00:00
-- url     : https://prove2.me/submissions/d4a54022-198a-41c1-80f3-29f9f07d07ea

import Definitions.Def_erdos390_remaining_analytic_propositions_004
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
import Definitions.Def_erdos390_analytic_foundations_009
import Definitions.Def_erdos390_analytic_foundations_010
import Theorems.Thm_Erdos390_Full_RegularMeshPrimeCutoffs_Mesh_momentReady_of_endpointMomentBounds
import Theorems.Thm_Erdos390_WholePaper_BankPaperRealization_bankPaperCanonicalGuardedStructuredAdditivePrebridgeMomentLedger_of_arbitrarySeedReplacement
import Theorems.Thm_Erdos390_WholePaper_BankPaperRealization_bankPaperCanonicalSectionNinePostHeight_headMoments_eq_roundedSource_of_sourceState
import Theorems.Thm_Erdos390_WholePaper_BankPaperRealization_eventually_roughCanonicalBalancedNonsmoothBounds_compact
import Theorems.Thm_Erdos390_WholePaper_bankPaperCanonicalSectionNinePostHeight_activeSeed_ordinaryLogMoment
import Theorems.Thm_Erdos390_WholePaper_bankPaperCanonical_selectorLogDefect_eq_sum_log_mul_deficit
import Theorems.Thm_Erdos390_WholePaper_sum_bankPaperCanonicalActualP87EndpointSelector_row_eq_preSelector_compact



section
universe u_1 u_2
theorem Erdos390.WholePaper.sum_bankPaperCanonicalActualP87EndpointSelector_row_eq_preSelector : Erdos390.RemainingAnalyticGoal008_033.{u_1, u_2} := @Erdos390.WholePaper.sum_bankPaperCanonicalActualP87EndpointSelector_row_eq_preSelector_compact
end
section
theorem Erdos390.WholePaper.BankPaperRealization.eventually_roughCanonicalBalancedNonsmoothBounds : Erdos390.RemainingAnalyticGoal004_016 := @Erdos390.WholePaper.BankPaperRealization.eventually_roughCanonicalBalancedNonsmoothBounds_compact
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





























theorem activeWeight_nonneg (fam : FiniteExponentialFamily Ω Param)
    (ξ : Param) (ω : Ω) : 0 ≤ fam.activeWeight ξ ω :=
  mul_nonneg (le_of_lt fam.baseMass_pos) (fam.probabilityMass_nonneg ξ ω)





























































end FiniteExponentialFamily

end

end Erdos390.Full

end

/- Source module: Erdos390.Full.HeadPattern -/
section


/-!
# Exact finite head patterns

The marked smooth cells impose exact valuations at finitely many fixed head
primes.  This file records their integral factor and modulus and proves the
factorization/divisibility part of the inclusion--exclusion reduction.  No
smooth-number asymptotic is used here.
-/

open scoped BigOperators
open scoped ArithmeticFunction.Moebius

namespace Erdos390.Full.HeadPattern



namespace Pattern

variable (P : Pattern)











theorem modulus_ne_zero : P.modulus ≠ 0 := by
  rw [modulus]
  apply Finset.prod_ne_zero_iff.mpr
  intro p hp
  exact (P.prime_mem p hp).ne_zero























end Pattern

end Erdos390.Full.HeadPattern

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



theorem activeCoordinateWeight_nonneg [Nonempty Head]
    (xi : B.ParamSpace) (m : B.sampleData.Sample) :
    0 <= B.activeCoordinateWeight xi m :=
  B.vectorFamily.scalarFamily.activeWeight_nonneg xi m







/-! The paper uses a compact *effective-score* box, not the crude sum of
all score norms.  The next estimates therefore take the correct pointwise
score bound and have constants independent of the number of active cells. -/

theorem exp_neg_effectiveBound_mul_q_le_partition
    [Nonempty Head] (xi : B.ParamSpace) (R : Real)
    (hscore : forall m : B.sampleData.Sample,
      |B.vectorFamily.scalarFamily.score m xi / B.L| <= R) :
    Real.exp (-R) * B.q <=
      B.vectorFamily.scalarFamily.partition xi := by
  rw [FiniteExponentialFamily.partition]
  calc
    Real.exp (-R) * B.q =
        Finset.univ.sum fun m : B.sampleData.Sample =>
          B.baseline.baseWeight m * Real.exp (-R) := by
      rw [← Finset.sum_mul, B.baseline.baseWeight_sum]
      simp [q, mul_comm]
    _ <= Finset.univ.sum fun m : B.sampleData.Sample =>
        B.vectorFamily.scalarFamily.unnormalizedWeight xi m := by
      apply Finset.sum_le_sum
      intro m _
      simp only [FiniteExponentialFamily.unnormalizedWeight,
        vectorFamily, VectorExponentialFamily.scalarFamily]
      apply mul_le_mul_of_nonneg_left _ (B.baseline.baseWeight_nonneg m)
      apply Real.exp_le_exp.mpr
      exact (neg_le_neg (hscore m)).trans
        (neg_abs_le (B.vectorFamily.scalarFamily.score m xi / B.L))

theorem probabilityMass_le_exp_twoEffectiveBound_mul_baseline
    [Nonempty Head] (xi : B.ParamSpace) (R : Real)
    (hscore : forall m : B.sampleData.Sample,
      |B.vectorFamily.scalarFamily.score m xi / B.L| <= R)
    (m : B.sampleData.Sample) :
    B.vectorFamily.probabilityMass xi m <=
      Real.exp (2 * R) * B.vectorFamily.probabilityMass 0 m := by
  have hq : B.q ≠ 0 := ne_of_gt B.q_pos
  have hZ : 0 < B.vectorFamily.scalarFamily.partition xi :=
    B.vectorFamily.scalarFamily.partition_pos xi
  have hexp : Real.exp (2 * R) * Real.exp (-R) = Real.exp R := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [B.probabilityMass_zero m]
  change B.vectorFamily.scalarFamily.unnormalizedWeight xi m /
      B.vectorFamily.scalarFamily.partition xi <=
    Real.exp (2 * R) * (B.baseline.baseWeight m / B.q)
  apply (div_le_iff₀ hZ).2
  calc
    B.vectorFamily.scalarFamily.unnormalizedWeight xi m =
        B.baseline.baseWeight m *
          Real.exp (B.vectorFamily.scalarFamily.score m xi / B.L) := by
      rfl
    _ <= B.baseline.baseWeight m * Real.exp R := by
      apply mul_le_mul_of_nonneg_left _ (B.baseline.baseWeight_nonneg m)
      exact Real.exp_le_exp.mpr
        ((le_abs_self _).trans (hscore m))
    _ = (Real.exp (2 * R) * (B.baseline.baseWeight m / B.q)) *
        (Real.exp (-R) * B.q) := by
      field_simp [hq]
      calc
        B.baseline.baseWeight m * Real.exp R =
            B.baseline.baseWeight m *
              (Real.exp (2 * R) * Real.exp (-R)) := by rw [hexp]
        _ = B.baseline.baseWeight m * Real.exp (2 * R) *
              Real.exp (-R) := by ring
    _ <= (Real.exp (2 * R) * (B.baseline.baseWeight m / B.q)) *
        B.vectorFamily.scalarFamily.partition xi := by
      exact mul_le_mul_of_nonneg_left
        (B.exp_neg_effectiveBound_mul_q_le_partition xi R hscore)
        (mul_nonneg (le_of_lt (Real.exp_pos _))
          (div_nonneg (B.baseline.baseWeight_nonneg m)
            (le_of_lt B.q_pos)))

theorem activeCoordinateWeight_le_exp_twoEffectiveBound_mul_baseline
    [Nonempty Head] (xi : B.ParamSpace) (R : Real)
    (hscore : forall m : B.sampleData.Sample,
      |B.vectorFamily.scalarFamily.score m xi / B.L| <= R)
    (m : B.sampleData.Sample) :
    B.activeCoordinateWeight xi m <=
      Real.exp (2 * R) * B.baseline.baseWeight m := by
  rw [activeCoordinateWeight, FiniteExponentialFamily.activeWeight]
  change B.vectorFamily.baseMass * B.vectorFamily.probabilityMass xi m <=
    Real.exp (2 * R) * B.baseline.baseWeight m
  rw [B.vectorFamily_baseMass]
  calc
    B.q * B.vectorFamily.probabilityMass xi m <=
        B.q * (Real.exp (2 * R) *
          B.vectorFamily.probabilityMass 0 m) :=
      mul_le_mul_of_nonneg_left
        (B.probabilityMass_le_exp_twoEffectiveBound_mul_baseline
          xi R hscore m) (le_of_lt B.q_pos)
    _ = Real.exp (2 * R) * B.baseline.baseWeight m := by
      rw [B.probabilityMass_zero m]
      field_simp [ne_of_gt B.q_pos]







/-! ## Actual natural-number coordinates -/



theorem ambientActiveWeight_nonneg [Nonempty Head]
    (xi : B.ParamSpace) (a : Nat) :
    0 <= B.ambientActiveWeight xi a := by
  apply Finset.sum_nonneg
  intro m _
  split_ifs
  · exact B.activeCoordinateWeight_nonneg xi m
  · exact le_rfl

theorem ambientActiveWeight_eq_of_value
    [Nonempty Head]
    (hsep : B.sampleData.HeadPatternsSeparated)
    (xi : B.ParamSpace) (m : B.sampleData.Sample) :
    B.ambientActiveWeight xi (B.sampleData.value m) =
      B.activeCoordinateWeight xi m := by
  classical
  rw [ambientActiveWeight, Finset.sum_eq_single m]
  · simp
  · intro k _ hkm
    rw [if_neg]
    intro hvalue
    exact hkm
      (B.sampleData.value_injective_of_headPatternsSeparated hsep hvalue)
  · simp

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

/- Source module: Erdos390.Full.RegularMeshPrimeCutoffsEventually -/
section


/-!
# Eventual population of every explicit regular-mesh prime cell

For a fixed regular mesh, each positive logarithmic cell has fixed positive
width.  Its multiplicative size on the original prime scale therefore tends
to infinity.  This file proves the scale-separation hypotheses used by the
Bertrand construction automatically for all sufficiently large `n`, and
hence produces the arithmetic partition and interval certificate without a
mesh or prime-existence assumption.
-/

open Filter

namespace Erdos390.Full.RegularMeshPrimeCutoffs

noncomputable section

open ArithmeticModel RegularRelativeMesh PositiveCellTransfer

theorem tendsto_y_atTop :
    Tendsto (fun n : ℕ ↦ y n) atTop atTop := by
  unfold y
  exact (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 2 / 9)).comp
    tendsto_natCast_atTop_atTop

/-- Every fixed positive logarithmic coordinate tends to infinity on the
original prime scale. -/
theorem tendsto_scalePoint_atTop {t : ℝ} (ht : 0 < t) :
    Tendsto (fun n : ℕ ↦ scalePoint n t) atTop atTop := by
  have hpow : Tendsto (fun n : ℕ ↦ (y n) ^ t) atTop atTop :=
    (tendsto_rpow_atTop ht).comp tendsto_y_atTop
  apply hpow.congr'
  filter_upwards [eventually_gt_atTop 0] with n hn
  unfold scalePoint
  rw [Real.rpow_def_of_pos (Scale.y_pos hn)]
  congr 1
  ring



namespace Mesh

variable {delta eta : ℝ} (M : Mesh delta eta)









end Mesh

end

end Erdos390.Full.RegularMeshPrimeCutoffs

end

/- Source module: Erdos390.Full.PartitionPrimeDeviationGeometry -/
section


/-!
# Prime-deviation moments for an actual arithmetic partition

This is the sample-independent form of the arithmetic geometry in Lemma
8.6.  It works directly with `ArithmeticBandGeometry.Partition`, so the
regular mesh constructed from explicit natural endpoints can be audited
without first manufacturing the smooth-number probability space.
-/

open scoped BigOperators

namespace Erdos390.Full.ArithmeticBandGeometry.Partition

noncomputable section

open ArithmeticModel ArithmeticBandGeometry PositiveCellTransfer
open KernelPrimeQuadrature PrimeCoordinateSecondMoment

variable {n W : ℕ} {Band : Type*} [Fintype Band] [DecidableEq Band]
  (P : ArithmeticBandGeometry.Partition n W Band)











theorem totalL1_eq_sum_bandL1 : P.totalL1 = ∑ j : Band, P.bandL1 j := by
  unfold totalL1 bandL1
  rw [← Finset.sum_fiberwise Finset.univ P.band
    (fun p : BandPrime n W ↦ (1 / (p.1 : ℝ)) * |P.deviation p|)]
  apply Finset.sum_congr rfl
  intro j hj
  rfl











theorem center_mem_of_coord_bounds (j : Band) {a b : ℝ}
    (hcoord : ∀ p ∈ P.data.fiber j, tPrime n p.1 ∈ Set.Icc a b) :
    P.center j ∈ Set.Icc a b := by
  have hH := P.data.mass_pos j
  have hLower : a * P.mass j ≤
      ∑ p ∈ P.data.fiber j, (1 / (p.1 : ℝ)) * tPrime n p.1 := by
    change a * (∑ p ∈ P.data.fiber j, 1 / (p.1 : ℝ)) ≤ _
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro p hp
    simpa only [mul_comm] using mul_le_mul_of_nonneg_right
      (hcoord p hp).1 (by positivity : 0 ≤ 1 / (p.1 : ℝ))
  have hUpper :
      (∑ p ∈ P.data.fiber j, (1 / (p.1 : ℝ)) * tPrime n p.1) ≤
        P.mass j * b := by
    change _ ≤ (∑ p ∈ P.data.fiber j, 1 / (p.1 : ℝ)) * b
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro p hp
    exact mul_le_mul_of_nonneg_left (hcoord p hp).2 (by positivity)
  change ((∑ p ∈ P.data.fiber j,
    (1 / (p.1 : ℝ)) * tPrime n p.1) / P.mass j) ∈ Set.Icc a b
  exact ⟨(le_div_iff₀ hH).2 hLower,
    (div_le_iff₀ hH).2 (by simpa only [mul_comm] using hUpper)⟩

theorem abs_deviation_le_width_of_coord_bounds (j : Band) {a b : ℝ}
    (hcoord : ∀ p ∈ P.data.fiber j, tPrime n p.1 ∈ Set.Icc a b)
    (p : BandPrime n W) (hp : p ∈ P.data.fiber j) :
    |P.deviation p| ≤ b - a := by
  have hpj : P.band p = j :=
    (Erdos390.Lemma84.WeightedBandData.mem_fiber_iff P.data).mp hp
  have hc := P.center_mem_of_coord_bounds j hcoord
  unfold deviation
  rw [hpj, abs_le]
  constructor <;> linarith [(hcoord p hp).1, (hcoord p hp).2, hc.1, hc.2]

theorem bandL1_le_width_mul_mass_of_coord_bounds (j : Band) {a b : ℝ}
    (hcoord : ∀ p ∈ P.data.fiber j, tPrime n p.1 ∈ Set.Icc a b) :
    P.bandL1 j ≤ (b - a) * P.mass j := by
  unfold bandL1
  change (∑ p ∈ P.data.fiber j,
      (1 / (p.1 : ℝ)) * |P.deviation p|) ≤
    (b - a) * (∑ p ∈ P.data.fiber j, 1 / (p.1 : ℝ))
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro p hp
  have hw : 0 ≤ 1 / (p.1 : ℝ) := by positivity
  have hdev := P.abs_deviation_le_width_of_coord_bounds j hcoord p hp
  calc
    (1 / (p.1 : ℝ)) * |P.deviation p| ≤
        (1 / (p.1 : ℝ)) * (b - a) :=
      mul_le_mul_of_nonneg_left hdev hw
    _ = (b - a) * (1 / (p.1 : ℝ)) := by ring



theorem bandL1_le_two_mass_mul_center (j : Band)
    (hcoordNonneg : ∀ p ∈ P.data.fiber j, 0 ≤ tPrime n p.1) :
    P.bandL1 j ≤ 2 * P.mass j * P.center j := by
  have hc0 : 0 ≤ P.center j := by
    change 0 ≤ (∑ q ∈ P.data.fiber j,
      (1 / (q.1 : ℝ)) * tPrime n q.1) / P.mass j
    exact div_nonneg (Finset.sum_nonneg fun q hq ↦
      mul_nonneg (by positivity) (hcoordNonneg q hq)) (P.data.mass_pos j).le
  have hfirst :
      (∑ p ∈ P.data.fiber j,
        (1 / (p.1 : ℝ)) * tPrime n p.1) = P.mass j * P.center j := by
    change (∑ p ∈ P.data.fiber j,
        (1 / (p.1 : ℝ)) * tPrime n p.1) =
      P.data.mass j *
        ((∑ p ∈ P.data.fiber j,
          (1 / (p.1 : ℝ)) * tPrime n p.1) / P.data.mass j)
    field_simp [ne_of_gt (P.data.mass_pos j)]
  have hmass : (∑ p ∈ P.data.fiber j, 1 / (p.1 : ℝ)) = P.mass j := rfl
  unfold bandL1
  calc
    (∑ p ∈ P.data.fiber j, (1 / (p.1 : ℝ)) * |P.deviation p|) ≤
        ∑ p ∈ P.data.fiber j,
          (1 / (p.1 : ℝ)) * (P.center j + tPrime n p.1) := by
      apply Finset.sum_le_sum
      intro p hp
      have hpj : P.band p = j :=
        (Erdos390.Lemma84.WeightedBandData.mem_fiber_iff P.data).mp hp
      rw [deviation, hpj]
      exact mul_le_mul_of_nonneg_left (abs_sub_le_iff.2
        ⟨by linarith [hcoordNonneg p hp], by linarith [hcoordNonneg p hp]⟩)
        (by positivity)
    _ = 2 * P.mass j * P.center j := by
      simp_rw [mul_add]
      rw [Finset.sum_add_distrib, ← Finset.sum_mul, hmass, hfirst]
      ring

end

end Erdos390.Full.ArithmeticBandGeometry.Partition

end

/- Source module: Erdos390.Full.MovingLowMomentQuadrature -/
section


/-!
# Endpoint-uniform first logarithmic prime moment

For the moving low cell the lower cutoff is fixed while the upper endpoint
grows.  Keeping the integrable `1/(x log^3 x)` PNT majorant, rather than
freezing `log x` at the lower endpoint, gives an error independent of the
upper endpoint.  Division by the ambient logarithmic scale therefore tends
to zero and supplies the relative low-center transfer.
-/

open Set

noncomputable section

namespace Erdos390.Full.MovingLowMomentQuadrature

open MeasureTheory PrimeSums PrimeBandQuadrature



























theorem fullLogReciprocalSumUniform_bound
    (A Y : ℕ) (hA : fullLogReciprocalSumUniformCutoff ≤ A)
    (hAY : A ≤ Y) :
    |fullLogReciprocalSum Y - fullLogReciprocalSum A -
        (Real.log (Y : ℝ) - Real.log (A : ℝ))| ≤
      2 * fullLogReciprocalSumUniformConstant / Real.log (A : ℝ) ^ 3 +
        fullLogReciprocalSumUniformConstant /
          (2 * Real.log (A : ℝ) ^ 2) :=
  (Classical.choose_spec
    (Classical.choose_spec
      exists_fullLogReciprocalSum_interval_uniform_error_bound).2)
    A Y hA hAY



end Erdos390.Full.MovingLowMomentQuadrature

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







theorem upper_div_lower_eq_one_add_ratio
    (hdelta : 0 < delta) (k : Fin M.cellCount) :
    M.upper k / M.lower k = 1 + M.ratio := by
  rw [show M.upper k = M.lower k * (1 + M.ratio) by
    unfold upper lower
    exact M.endpoint_succ k.1]
  field_simp [ne_of_gt (M.lower_pos hdelta k)]

theorem cellHarmonicMass_eq_log_one_add_ratio
    (hdelta : 0 < delta) (k : Fin M.cellCount) :
    M.cellHarmonicMass k = Real.log (1 + M.ratio) := by
  unfold cellHarmonicMass
  rw [M.upper_div_lower_eq_one_add_ratio hdelta k]



theorem cellHarmonicMass_le_ratio
    (hdelta : 0 < delta) (k : Fin M.cellCount) :
    M.cellHarmonicMass k ≤ M.ratio := by
  rw [M.cellHarmonicMass_eq_log_one_add_ratio hdelta k]
  have h := Real.log_le_sub_one_of_pos (by linarith [M.ratio_pos] :
    0 < 1 + M.ratio)
  linarith













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

omit hLower in
/-- Every actual prime in the low fiber lies in `[0,delta]`. -/
theorem low_coord_bounds (hn : 1 < n)
    (p : BandPrime n W) (hp : p ∈ P.data.fiber (0 : Fin (M.cellCount + 1))) :
    tPrime n p.1 ∈ Set.Icc 0 delta := by
  have hpBand : P.band p = (0 : Fin (M.cellCount + 1)) :=
    (Erdos390.Lemma84.WeightedBandData.mem_fiber_iff P.data).mp hp
  have hpInterval :=
    (PositiveCellTransfer.IntervalCertificate.band_eq_iff E p 0).mp hpBand
  have hpUpper := hpInterval.2
  rw [hUpper 0] at hpUpper
  have hendpoint : M.endpoint 0 = delta := M.endpoint_zero
  simp only [Fin.val_zero, fullCutoff, hendpoint] at hpUpper
  constructor
  · have hpPrime := prime_of_mem_primeBand p.2
    unfold tPrime
    exact div_nonneg (Real.log_nonneg (by exact_mod_cast hpPrime.one_lt.le))
      (Real.log_pos (y_gt_one hn)).le
  · exact prime_logCoordinate_le_of_le_floorScale hn
      (prime_of_mem_primeBand p.2).pos hpUpper

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



/-- The first-moment part of the finite assembly is uniform for an
arbitrary relative-mesh upper parameter `eta`.  Unlike the variance lower
bound, it does not require `M.ratio ≤ delta`. -/
theorem actual_L1_bound_of_ready
    (hdelta : 0 < delta) (hn : 1 < n)
    (R : MomentReady M P) :
    P.totalL1 ≤ 7 * (delta + M.ratio) := by
  have hrho0 := M.ratio_pos.le
  have hlowCoord := low_coord_bounds M P E hUpper hn
  have hposCoord := positive_coord_bounds M P E hLower hUpper hn
  have hlowL1 := P.bandL1_le_two_mass_mul_center 0
    (fun p hp ↦ (hlowCoord p hp).1)
  have hposL1 (k : Fin M.cellCount) :
      P.bandL1 k.succ ≤ 3 * M.ratio * M.width k := by
    have hraw := P.bandL1_le_width_mul_mass_of_coord_bounds k.succ
      (hposCoord k)
    rw [show M.upper k - M.lower k = M.width k by rfl] at hraw
    calc
      P.bandL1 k.succ ≤ M.width k * P.mass k.succ := hraw
      _ ≤ M.width k * (3 * M.ratio) :=
        mul_le_mul_of_nonneg_left (R.positiveMass k)
          (M.width_pos hdelta k).le
      _ = 3 * M.ratio * M.width k := by ring
  rw [P.totalL1_eq_sum_bandL1, Fin.sum_univ_succ]
  calc
    P.bandL1 0 + ∑ k : Fin M.cellCount, P.bandL1 k.succ ≤
        4 * delta + ∑ k : Fin M.cellCount,
          3 * M.ratio * M.width k := by
      apply add_le_add
      · exact hlowL1.trans (by linarith [R.lowFirst])
      · exact Finset.sum_le_sum fun k hk ↦ hposL1 k
    _ = 4 * delta + 3 * M.ratio * (1 - delta) := by
      rw [← Finset.mul_sum, M.sum_width_eq_one_sub_delta]
    _ ≤ 7 * (delta + M.ratio) := by nlinarith







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

/- Source module: Erdos390.Full.RegularMeshActualMomentBoundsEventually -/
section


/-!
# Eventual actual-prime moment bounds on the canonical regular mesh

This file discharges the `MomentReady` inputs of
`RegularMeshActualMomentBounds` from the unconditional prime number theorem
quadratures.  The endpoint family is the canonical family of floored powers
of `y`; no continuum mesh, prime-population, or moment estimate is assumed.
-/

open scoped BigOperators
open Filter Topology

namespace Erdos390.Full.RegularMeshPrimeCutoffs

noncomputable section

open ArithmeticModel ArithmeticBandGeometry RegularRelativeMesh
open PositiveCellTransfer KernelPrimeQuadrature
open PrimeIntervalPartitionConstructor PrimeBandQuadrature
open PrimeCoordinateSecondMoment MovingLowMomentQuadrature

namespace Mesh

variable {delta eta : ℝ} (M : Mesh delta eta)



theorem tendsto_log_y_atTop :
    Tendsto (fun n : ℕ ↦ Real.log (y n)) atTop atTop :=
  Real.tendsto_log_atTop.comp tendsto_y_atTop

theorem tendsto_fixed_cutoffCoordinate_zero (W : ℕ) :
    Tendsto (fun n : ℕ ↦ realLogCoordinate (y n) (W : ℝ))
      atTop (nhds 0) := by
  have hInv : Tendsto (fun n : ℕ ↦ (Real.log (y n))⁻¹)
      atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp tendsto_log_y_atTop
  have hConst : Tendsto (fun _n : ℕ ↦ Real.log (W : ℝ)) atTop
      (nhds (Real.log (W : ℝ))) := tendsto_const_nhds
  simpa only [realLogCoordinate, div_eq_mul_inv, mul_zero] using
    hConst.mul hInv

theorem tendsto_floor_scalePoint_coordinate
    {t : ℝ} (ht : 0 < t) :
    Tendsto (fun n : ℕ ↦
      realLogCoordinate (y n) (⌊scalePoint n t⌋₊ : ℝ))
      atTop (nhds t) := by
  have hLoss : Tendsto (fun n : ℕ ↦ Real.log 2 / Real.log (y n))
      atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop tendsto_log_y_atTop
  have hLowerT : Tendsto
      (fun n : ℕ ↦ t - Real.log 2 / Real.log (y n))
      atTop (nhds t) := by
    simpa only [sub_zero] using tendsto_const_nhds.sub hLoss
  have hUpperT : Tendsto (fun _n : ℕ ↦ t) atTop (nhds t) :=
    tendsto_const_nhds
  have hTwo := (tendsto_scalePoint_atTop ht).eventually
    (eventually_ge_atTop (2 : ℝ))
  have hLower : ∀ᶠ n : ℕ in atTop,
      t - Real.log 2 / Real.log (y n) ≤
        realLogCoordinate (y n) (⌊scalePoint n t⌋₊ : ℝ) := by
    filter_upwards [eventually_gt_atTop 1, hTwo] with n hn hnTwo
    exact (floor_scalePoint_coordinate_bounds hn hnTwo).1
  have hUpper : ∀ᶠ n : ℕ in atTop,
      realLogCoordinate (y n) (⌊scalePoint n t⌋₊ : ℝ) ≤ t := by
    filter_upwards [eventually_gt_atTop 1, hTwo] with n hn hnTwo
    exact (floor_scalePoint_coordinate_bounds hn hnTwo).2
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
    hLowerT hUpperT hLower hUpper

theorem tendsto_positive_lowerCoordinate
    (hdelta : 0 < delta) (W : ℕ) (k : Fin M.cellCount) :
    Tendsto (fun n : ℕ ↦ cutoffCoordinate M n W (k.1 + 1))
      atTop (nhds (M.lower k)) := by
  simpa only [cutoffCoordinate, fullCutoff_succ,
    RegularRelativeMesh.Mesh.lower] using
      tendsto_floor_scalePoint_coordinate (M.lower_pos hdelta k)

theorem tendsto_positive_upperCoordinate
    (hdelta : 0 < delta) (W : ℕ) (k : Fin M.cellCount) :
    Tendsto (fun n : ℕ ↦ cutoffCoordinate M n W (k.1 + 2))
      atTop (nhds (M.upper k)) := by
  have hUpperPos : 0 < M.upper k :=
    (M.lower_pos hdelta k).trans (M.lower_lt_upper hdelta k)
  simpa only [cutoffCoordinate, show k.1 + 2 = (k.1 + 1) + 1 by omega,
    fullCutoff_succ, RegularRelativeMesh.Mesh.upper] using
      tendsto_floor_scalePoint_coordinate hUpperPos

theorem tendsto_low_upperCoordinate
    (hdelta : 0 < delta) (W : ℕ) :
    Tendsto (fun n : ℕ ↦ cutoffCoordinate M n W 1)
      atTop (nhds delta) := by
  simpa only [cutoffCoordinate, fullCutoff_succ, M.endpoint_zero] using
    tendsto_floor_scalePoint_coordinate hdelta







theorem tendsto_positiveContinuumMass
    (hdelta : 0 < delta) (W : ℕ) (k : Fin M.cellCount) :
    Tendsto (fun n : ℕ ↦ positiveContinuumMass M n W k) atTop
      (nhds (M.cellHarmonicMass k)) := by
  have hLower := tendsto_positive_lowerCoordinate M hdelta W k
  have hUpper := tendsto_positive_upperCoordinate M hdelta W k
  have hLogLower : Tendsto
      (fun n : ℕ ↦ Real.log (cutoffCoordinate M n W (k.1 + 1)))
      atTop (nhds (Real.log (M.lower k))) :=
    (Real.continuousAt_log (ne_of_gt (M.lower_pos hdelta k))).tendsto.comp
      hLower
  have hUpperPos : 0 < M.upper k :=
    (M.lower_pos hdelta k).trans (M.lower_lt_upper hdelta k)
  have hLogUpper : Tendsto
      (fun n : ℕ ↦ Real.log (cutoffCoordinate M n W (k.1 + 2)))
      atTop (nhds (Real.log (M.upper k))) :=
    (Real.continuousAt_log (ne_of_gt hUpperPos)).tendsto.comp hUpper
  have hDiff := hLogUpper.sub hLogLower
  simpa only [positiveContinuumMass,
    RegularRelativeMesh.Mesh.cellHarmonicMass,
    Real.log_div (ne_of_gt hUpperPos)
      (ne_of_gt (M.lower_pos hdelta k))] using hDiff

theorem tendsto_lowFirstContinuum
    (hdelta : 0 < delta) (W : ℕ) :
    Tendsto (fun n : ℕ ↦ lowFirstContinuum M n W)
      atTop (nhds delta) := by
  simpa only [lowFirstContinuum, sub_zero] using
    (tendsto_low_upperCoordinate M hdelta W).sub
      (tendsto_fixed_cutoffCoordinate_zero W)

theorem tendsto_lowSecondContinuum
    (hdelta : 0 < delta) (W : ℕ) :
    Tendsto (fun n : ℕ ↦ lowSecondContinuum M n W)
      atTop (nhds (delta ^ 2 / 2)) := by
  have hUpper := (tendsto_low_upperCoordinate M hdelta W).pow 2
  have hLower := (tendsto_fixed_cutoffCoordinate_zero W).pow 2
  have hDiff := hUpper.sub hLower
  have hDiv := hDiff.div_const (2 : ℝ)
  simpa only [lowSecondContinuum, zero_pow (by omega : 2 ≠ 0), sub_zero]
    using hDiv

theorem tendsto_positive_lowerCutoff_atTop
    (hdelta : 0 < delta) (W : ℕ) (k : Fin M.cellCount) :
    Tendsto (fun n : ℕ ↦ fullCutoff M n W (k.1 + 1))
      atTop atTop := by
  simpa only [fullCutoff_succ, RegularRelativeMesh.Mesh.lower] using
    tendsto_nat_floor_atTop.comp
      (tendsto_scalePoint_atTop (M.lower_pos hdelta k))

theorem tendsto_positive_massError_zero
    (hdelta : 0 < delta) (W : ℕ) (C : ℝ)
    (k : Fin M.cellCount) :
    Tendsto (fun n : ℕ ↦
      5 * C / Real.log (fullCutoff M n W (k.1 + 1) : ℝ) ^ 3)
      atTop (nhds 0) := by
  have hCutReal : Tendsto
      (fun n : ℕ ↦ (fullCutoff M n W (k.1 + 1) : ℝ))
      atTop atTop :=
    tendsto_natCast_atTop_atTop.comp
      (tendsto_positive_lowerCutoff_atTop M hdelta W k)
  have hLog : Tendsto
      (fun n : ℕ ↦ Real.log (fullCutoff M n W (k.1 + 1) : ℝ))
      atTop atTop := Real.tendsto_log_atTop.comp hCutReal
  have hInv : Tendsto (fun n : ℕ ↦
      (Real.log (fullCutoff M n W (k.1 + 1) : ℝ))⁻¹)
      atTop (nhds 0) := tendsto_inv_atTop_zero.comp hLog
  have hConst : Tendsto (fun _n : ℕ ↦ 5 * C) atTop (nhds (5 * C)) :=
    tendsto_const_nhds
  have hMain := hConst.mul (hInv.pow 3)
  simpa only [div_eq_mul_inv, inv_pow, mul_zero, zero_pow (by omega : 3 ≠ 0)]
    using hMain

theorem tendsto_lowFirstError_zero (C : ℝ) (W : ℕ) :
    Tendsto (fun n : ℕ ↦
      (2 * C / Real.log (W : ℝ) ^ 3 +
        C / (2 * Real.log (W : ℝ) ^ 2)) / Real.log (y n))
      atTop (nhds 0) := by
  exact tendsto_const_nhds.div_atTop tendsto_log_y_atTop

theorem tendsto_lowSecondError_zero
    (C : ℝ) {W : ℕ} (hW : 1 < W) :
    Tendsto (fun n : ℕ ↦
      3 * C / (Real.log (y n) ^ 2 * Real.log (W : ℝ)))
      atTop (nhds 0) := by
  have hInv : Tendsto (fun n : ℕ ↦ (Real.log (y n))⁻¹)
      atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp tendsto_log_y_atTop
  have hConst : Tendsto
      (fun _n : ℕ ↦ 3 * C / Real.log (W : ℝ)) atTop
      (nhds (3 * C / Real.log (W : ℝ))) := tendsto_const_nhds
  have hMain := hConst.mul (hInv.pow 2)
  have hMainZero : Tendsto (fun n : ℕ ↦
      (3 * C / Real.log (W : ℝ)) * (Real.log (y n))⁻¹ ^ 2)
      atTop (nhds 0) := by simpa using hMain
  apply hMainZero.congr'
  filter_upwards with n
  have hLogW : Real.log (W : ℝ) ≠ 0 :=
    ne_of_gt (Real.log_pos (by exact_mod_cast hW))
  field_simp [hLogW]

theorem tendsto_lowHarmonicMain_atTop
    (hdelta : 0 < delta) (W : ℕ) :
    Tendsto (fun n : ℕ ↦
      Real.log (Real.log (fullCutoff M n W 1 : ℝ)) -
        Real.log (Real.log (W : ℝ))) atTop atTop := by
  have hCutNat : Tendsto (fun n : ℕ ↦ fullCutoff M n W 1)
      atTop atTop := by
    simpa only [fullCutoff_succ, M.endpoint_zero] using
      tendsto_nat_floor_atTop.comp (tendsto_scalePoint_atTop hdelta)
  have hCutReal : Tendsto
      (fun n : ℕ ↦ (fullCutoff M n W 1 : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hCutNat
  have hLogLog := Real.tendsto_log_atTop.comp
    (Real.tendsto_log_atTop.comp hCutReal)
  rw [tendsto_atTop]
  intro b
  have hEvent := hLogLog.eventually
    (eventually_ge_atTop (b + Real.log (Real.log (W : ℝ))))
  filter_upwards [hEvent] with n hn
  change b + Real.log (Real.log (W : ℝ)) ≤
    Real.log (Real.log (fullCutoff M n W 1 : ℝ)) at hn
  linarith



theorem eventually_endpointMomentBounds
    (hdelta : 0 < delta) (W : ℕ) (Cmass Cfirst Csecond : ℝ)
    (hW : 1 < W) :
    ∀ᶠ n : ℕ in atTop,
      EndpointMomentBounds M n W Cmass Cfirst Csecond := by
  have hPositiveMain : ∀ᶠ n : ℕ in atTop,
      ∀ k : Fin M.cellCount,
        positiveContinuumMass M n W k ≤ 2 * M.ratio := by
    rw [Filter.eventually_all]
    intro k
    have hT := tendsto_positiveContinuumMass M hdelta W k
    have hLimit : M.cellHarmonicMass k < 2 * M.ratio :=
      (M.cellHarmonicMass_le_ratio hdelta k).trans_lt (by
        linarith [M.ratio_pos])
    exact hT.eventually (eventually_le_nhds hLimit)
  have hPositiveError : ∀ᶠ n : ℕ in atTop,
      ∀ k : Fin M.cellCount,
        5 * Cmass / Real.log (fullCutoff M n W (k.1 + 1) : ℝ) ^ 3 ≤
          M.ratio := by
    rw [Filter.eventually_all]
    intro k
    exact (tendsto_positive_massError_zero M hdelta W Cmass k).eventually
      (eventually_le_nhds M.ratio_pos)
  have hFirstMain : ∀ᶠ n : ℕ in atTop,
      lowFirstContinuum M n W ≤ 3 * delta / 2 := by
    have hLimit : delta < 3 * delta / 2 := by linarith
    exact (tendsto_lowFirstContinuum M hdelta W).eventually
      (eventually_le_nhds hLimit)
  have hFirstError : ∀ᶠ n : ℕ in atTop,
      (2 * Cfirst / Real.log (W : ℝ) ^ 3 +
        Cfirst / (2 * Real.log (W : ℝ) ^ 2)) / Real.log (y n) ≤
          delta / 2 := by
    exact (tendsto_lowFirstError_zero Cfirst W).eventually
      (eventually_le_nhds (by linarith : (0 : ℝ) < delta / 2))
  have hSecondLower : ∀ᶠ n : ℕ in atTop,
      5 * delta ^ 2 / 12 ≤ lowSecondContinuum M n W := by
    have hStrict : 5 * delta ^ 2 / 12 < delta ^ 2 / 2 := by
      nlinarith [sq_pos_of_pos hdelta]
    exact (tendsto_lowSecondContinuum M hdelta W).eventually
      (eventually_ge_nhds hStrict)
  have hSecondUpper : ∀ᶠ n : ℕ in atTop,
      lowSecondContinuum M n W ≤ 11 * delta ^ 2 / 12 := by
    have hStrict : delta ^ 2 / 2 < 11 * delta ^ 2 / 12 := by
      nlinarith [sq_pos_of_pos hdelta]
    exact (tendsto_lowSecondContinuum M hdelta W).eventually
      (eventually_le_nhds hStrict)
  have hSecondError : ∀ᶠ n : ℕ in atTop,
      3 * Csecond / (Real.log (y n) ^ 2 * Real.log (W : ℝ)) ≤
        delta ^ 2 / 12 := by
    have hStrict : (0 : ℝ) < delta ^ 2 / 12 := by positivity
    exact (tendsto_lowSecondError_zero Csecond hW).eventually
      (eventually_le_nhds hStrict)
  have hLowMass : ∀ᶠ n : ℕ in atTop,
      48 + 5 * Cmass / Real.log (W : ℝ) ^ 3 ≤
        Real.log (Real.log (fullCutoff M n W 1 : ℝ)) -
          Real.log (Real.log (W : ℝ)) :=
    (tendsto_lowHarmonicMain_atTop M hdelta W).eventually
      (eventually_ge_atTop
        (48 + 5 * Cmass / Real.log (W : ℝ) ^ 3))
  filter_upwards [eventually_gt_atTop 1, hPositiveMain, hPositiveError,
    hFirstMain, hFirstError, hSecondLower, hSecondUpper, hSecondError,
    hLowMass] with n hn hPM hPE hFM hFE hSL hSU hSE hLM
  exact ⟨hn, hPM, hPE, hFM, hFE, hSL, hSU, hSE, hLM⟩

variable {n W : ℕ}
  (P : Partition n W (Fin (M.cellCount + 1)))
  (E : IntervalCertificate P)
  (hLower : ∀ j, E.lower j = fullCutoff M n W j.1)
  (hUpper : ∀ j, E.upper j = fullCutoff M n W (j.1 + 1))

include E hLower hUpper











end Mesh

end

end Erdos390.Full.RegularMeshPrimeCutoffs

end

/- Source module: Erdos390.Full.PaperCanonicalNuisanceUniformFloor -/
section


/-!
# A root uniform lower floor for the canonical nuisance gap

The exact canonical nuisance gap is allowed to use a varying reference head
and a varying positive barycentric target.  This file bounds its two finite
dimensional constants by quantities depending only on the fixed head type,
and replaces the varying cell-mass margin by one prescribed positive floor.
The result is the uniform positive scalar needed before taking an eventual
Schur-smallness threshold.
-/

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

open ArithmeticModel PaperGuardCensus









namespace BridgeData

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]
  (B : BridgeData Head Band)

/-- The actual nuisance coordinate count is bounded by the full head count
plus the physical coordinate. -/
theorem nuisanceCoord_card_le_head_add_one :
    Fintype.card (NuisanceCoord B.HeadIndex) ≤ Fintype.card Head + 1 := by
  let f : NuisanceCoord B.HeadIndex → Option Head
    | .physical => none
    | .head h => some h.1
  have hf : Function.Injective f := by
    intro x y hxy
    cases x <;> cases y <;> simp_all [f, Subtype.ext_iff]
  simpa using Fintype.card_le_of_injective f hf

theorem sqrt_nuisanceCoord_card_le_ceiling :
    Real.sqrt (Fintype.card (NuisanceCoord B.HeadIndex) : ℝ) ≤
      nuisanceDimensionCeiling Head := by
  unfold nuisanceDimensionCeiling
  apply Real.sqrt_le_sqrt
  exact_mod_cast B.nuisanceCoord_card_le_head_add_one

theorem nuisanceStatisticCoefficient_le_ceiling
    {U : ℝ} (hU : 1 ≤ U) :
    B.nuisanceStatisticCoefficient U ≤
      nuisanceStatisticCoefficientCeiling Head U := by
  unfold nuisanceStatisticCoefficient nuisanceStatisticCoefficientCeiling
  have hmax : 0 ≤ max (PaperStatisticNorm.physicalLogCoefficient U)
      (3 / Real.log 2) := by
    exact (PaperStatisticNorm.physicalLogCoefficient_nonneg hU).trans
      (le_max_left _ _)
  exact mul_le_mul_of_nonneg_right
    B.sqrt_nuisanceCoord_card_le_ceiling hmax







end BridgeData

end

end Erdos390.Full.PaperBridgeFit

end

/- Source module: Erdos390.Full.PaperCanonicalActualMomentBoundsEventually -/
section


/-!
# Canonical actual-prime moment bounds, uniformly in the separation proof

`RegularMeshActualMomentBoundsEventually` constructs a partition
existentially.  For the paper-facing bridge we need the same estimates on
the literal canonical partition appearing in the bridge hypothesis, and we
need them for every proof of the scale-separation inequalities.  Proof
irrelevance is not used as an analytic input here: the endpoint inequalities
are established first and the canonical partition is then constructed from
any supplied separation proof.
-/

open scoped BigOperators
open Filter

noncomputable section

namespace Erdos390.Full.RegularMeshPrimeCutoffs

open ArithmeticModel ArithmeticBandGeometry RegularRelativeMesh
open PositiveCellTransfer KernelPrimeQuadrature PrimeBandQuadrature
open PrimeCoordinateSecondMoment MovingLowMomentQuadrature





theorem canonicalMassQuadratureBound
    (A Y : ℕ) (hA : canonicalMassQuadratureCutoff ≤ A)
    (hAY : A ≤ Y) :
    |PrimeSums.fullReciprocalSum Y - PrimeSums.fullReciprocalSum A -
        (Real.log (Real.log (Y : ℝ)) -
          Real.log (Real.log (A : ℝ)))| ≤
      5 * canonicalMassQuadratureConstant / Real.log (A : ℝ) ^ 3 :=
  (Classical.choose_spec
    (Classical.choose_spec
      PrimeBandQuadrature.exists_fullReciprocalSum_interval_error_bound).2)
    A Y hA hAY





theorem canonicalSecondMomentBound
    (z : ℝ) (hz : 1 < z) (A Y : ℕ)
    (hA : canonicalSecondMomentCutoff ≤ A) (hAY : A ≤ Y) :
    |KernelPrimeQuadrature.fullWeightedReciprocalSum
          PrimeCoordinateSecondMoment.squareCoordinate z Y -
        KernelPrimeQuadrature.fullWeightedReciprocalSum
          PrimeCoordinateSecondMoment.squareCoordinate z A -
        ((realLogCoordinate z (Y : ℝ) ^ 2 -
          realLogCoordinate z (A : ℝ) ^ 2) / 2)| ≤
      3 * canonicalSecondMomentConstant /
        (Real.log z ^ 2 * Real.log (A : ℝ)) :=
  (Classical.choose_spec
    (Classical.choose_spec
      PrimeCoordinateSecondMoment.exists_uniform_squarePrimeCell_error_bound).2)
    z hz A Y hA hAY



namespace Mesh

section DiagonalMomentMesh

variable {delta : ℝ} (M : Mesh delta delta)





end DiagonalMomentMesh

section GenericFirstMomentMesh

variable {delta eta : ℝ} (M : Mesh delta eta)











end GenericFirstMomentMesh

section DiagonalMesh

variable {delta : ℝ} (M : Mesh delta delta)





end DiagonalMesh

end Mesh
end Erdos390.Full.RegularMeshPrimeCutoffs

end

/- Source module: Erdos390.Full.PaperProposition87SpeedRadius -/
section


/-!
# Noncircular speed, radius, and eventual slack choices for Proposition 8.7

These are purely quantitative closure lemmas.  All structural bounds are
fixed first; the effective ODE speed is their maximum, and the box radius is
four times that speed.  The ambient threshold is then increased.  No bound
is inferred from an already constructed path.
-/

open Filter Topology

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

open scoped BigOperators

namespace BridgeData

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]
  (B : BridgeData Head Band)







end BridgeData







/-- Once all constants and the radius are fixed, the logarithmic ambient
slack inequality used by the feasibility ledger holds eventually. -/
theorem eventually_fixed_exponential_slack_le_L
    (Cfixed K Cactive : ℝ) :
    ∀ᶠ n : ℕ in atTop,
      Cfixed + Real.exp K * Cactive ≤ Scale.L n := by
  have hLTop : Tendsto Scale.L atTop atTop := by
    simpa only [Scale.L] using
      Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  exact hLTop.eventually
    (eventually_ge_atTop (Cfixed + Real.exp K * Cactive))

end

end Erdos390.Full.PaperBridgeFit

end

/- Source module: Erdos390.Full.PaperProposition87CanonicalFeasibilitySlackEventually -/
section


/-!
# Canonical eventual feasibility slack for Proposition 8.7

The finite ODE assembly asks for an exponential feasibility inequality whose
nuisance coefficient is attached to the current canonical bridge data.  The
coefficient is uniformly bounded by the head-cardinality ceiling.  Therefore,
after `W`, the head type, and the effective ball have been fixed, the required
inequality follows from `L(n) -> infinity`; it is not an analytic hypothesis
at the final Proposition 8.7 call site.
-/

open Filter

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

open ArithmeticModel PaperGuardCensus

namespace BridgeData

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]

/-- Uniform eventual form of the literal feasibility slack used by the
canonical ODE assembly. -/
theorem eventually_canonical_exponential_slack_le_L
    (U : ℝ) (hU : 1 ≤ U) (W : ℕ) (a : NNReal)
    (Cfixed Cactive : ℝ) (hCactive : 0 ≤ Cactive) :
    ∀ᶠ n : ℕ in atTop,
      ∀ (B : BridgeData Head Band),
        B.sampleData.n = n → B.sampleData.W = W →
        Cfixed +
            Real.exp (2 *
              ((PaperStatisticNorm.valuationLogCoefficient
                    U B.sampleData.W +
                  B.nuisanceStatisticCoefficient U) * (3 * (a : ℝ)))) *
              Cactive ≤ B.L := by
  let Kceiling : ℝ :=
    2 * ((PaperStatisticNorm.valuationLogCoefficient U W +
      nuisanceStatisticCoefficientCeiling Head U) * (3 * (a : ℝ)))
  have hlarge := eventually_fixed_exponential_slack_le_L
    Cfixed Kceiling Cactive
  filter_upwards [hlarge] with n hlargeN
  intro B hBn hBW
  have hcoeff :
      PaperStatisticNorm.valuationLogCoefficient U B.sampleData.W +
          B.nuisanceStatisticCoefficient U ≤
        PaperStatisticNorm.valuationLogCoefficient U W +
          nuisanceStatisticCoefficientCeiling Head U := by
    rw [hBW]
    linarith [B.nuisanceStatisticCoefficient_le_ceiling hU]
  have hscaleNonneg : 0 ≤ 3 * (a : ℝ) := by positivity
  have hexponent :
      2 * ((PaperStatisticNorm.valuationLogCoefficient U B.sampleData.W +
            B.nuisanceStatisticCoefficient U) * (3 * (a : ℝ))) ≤
        Kceiling := by
    dsimp only [Kceiling]
    nlinarith [mul_le_mul_of_nonneg_right hcoeff hscaleNonneg]
  have hexp :
      Real.exp (2 *
          ((PaperStatisticNorm.valuationLogCoefficient U B.sampleData.W +
            B.nuisanceStatisticCoefficient U) * (3 * (a : ℝ)))) ≤
        Real.exp Kceiling := Real.exp_le_exp.mpr hexponent
  have hscaled := mul_le_mul_of_nonneg_right hexp hCactive
  calc
    Cfixed +
          Real.exp (2 *
            ((PaperStatisticNorm.valuationLogCoefficient U B.sampleData.W +
              B.nuisanceStatisticCoefficient U) * (3 * (a : ℝ)))) *
            Cactive ≤
        Cfixed + Real.exp Kceiling * Cactive :=
      by linarith
    _ ≤ B.L := by
      change Cfixed + Real.exp Kceiling * Cactive ≤
        Scale.L B.sampleData.n
      rw [hBn]
      exact hlargeN

end BridgeData

end

end Erdos390.Full.PaperBridgeFit

end

/- Source module: Erdos390.WholePaper.CompleteRoughRowPartition -/
section


/-!
# The finite partition into complete rough rows

For a finite set `A`, its complete rough labels are precisely the labels
actually attained on `A`.  Filtering `A` at one such label gives the
corresponding row.  These rows form a literal finite partition of `A`:
they are nonempty, lie in `A`, have constant complete signature, are
pairwise disjoint, and have union exactly `A`.

The final results transport arbitrary additive weights across this
partition, including the factorization-coordinate weights used later in
the paper.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

noncomputable section

/-! ## Labels and row fibers -/











/-! ## Row support and constancy -/

/-- Every complete rough row is a subset of the original finite set. -/
theorem completeRoughRowFiber_subset
    (y : ℕ) (A : Finset ℕ) (label : ℕ) :
    completeRoughRowFiber y A label ⊆ A := by
  intro a ha
  exact (mem_completeRoughRowFiber.mp ha).1

/-- The integer rough label is constant throughout its row fiber. -/
theorem completeRoughLabel_eq_of_mem_rowFiber
    {y label a : ℕ} {A : Finset ℕ}
    (ha : a ∈ completeRoughRowFiber y A label) :
    completeRoughLabel y a = label :=
  (mem_completeRoughRowFiber.mp ha).2





/-! ## Exact finite partition -/

/-- Distinct attained labels have disjoint row fibers. -/
theorem completeRoughRowFibers_pairwiseDisjoint
    (y : ℕ) (A : Finset ℕ) :
    ((completeRoughLabelSet y A : Finset ℕ) : Set ℕ).PairwiseDisjoint
      (completeRoughRowFiber y A) := by
  intro label _hlabel other _hother hne
  change Disjoint (completeRoughRowFiber y A label)
    (completeRoughRowFiber y A other)
  rw [Finset.disjoint_left]
  intro a haLabel haOther
  have hlabelEq : completeRoughLabel y a = label :=
    completeRoughLabel_eq_of_mem_rowFiber haLabel
  have hotherEq : completeRoughLabel y a = other :=
    completeRoughLabel_eq_of_mem_rowFiber haOther
  exact hne (hlabelEq.symm.trans hotherEq)

/-- The union of all attained-label row fibers is exactly `A`. -/
theorem completeRoughLabelSet_biUnion_rowFibers
    (y : ℕ) (A : Finset ℕ) :
    (completeRoughLabelSet y A).biUnion
        (completeRoughRowFiber y A) = A := by
  ext a
  constructor
  · intro ha
    rw [Finset.mem_biUnion] at ha
    obtain ⟨label, _hlabel, haRow⟩ := ha
    exact (completeRoughRowFiber_subset y A label) haRow
  · intro ha
    rw [Finset.mem_biUnion]
    refine ⟨completeRoughLabel y a, ?_, ?_⟩
    · exact mem_completeRoughLabelSet.mpr ⟨a, ha, rfl⟩
    · exact mem_completeRoughRowFiber.mpr ⟨ha, rfl⟩

/-! ## Additive partition identities -/

/-- Every additive weight on `A` is the sum of its weights row by row. -/
theorem sum_eq_sum_completeRoughRowFibers
    {M : Type*} [AddCommMonoid M]
    (y : ℕ) (A : Finset ℕ) (weight : ℕ → M) :
    ∑ a ∈ A, weight a =
      ∑ label ∈ completeRoughLabelSet y A,
        ∑ a ∈ completeRoughRowFiber y A label, weight a := by
  classical
  calc
    ∑ a ∈ A, weight a =
        ∑ a ∈ (completeRoughLabelSet y A).biUnion
          (completeRoughRowFiber y A), weight a := by
      rw [completeRoughLabelSet_biUnion_rowFibers]
    _ = ∑ label ∈ completeRoughLabelSet y A,
          ∑ a ∈ completeRoughRowFiber y A label, weight a := by
      exact Finset.sum_biUnion
        (completeRoughRowFibers_pairwiseDisjoint y A)







end

end Erdos390.WholePaper

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









/-- The head modulus is always positive, including for an empty head. -/
theorem roughHeadModulus_pos (W : ℕ) :
    0 < roughHeadModulus W := by
  rw [← roughHeadZeroPattern_modulus]
  exact Nat.pos_of_ne_zero (roughHeadZeroPattern W).modulus_ne_zero



/-- The complete zero-head stratum has strictly positive density. -/
theorem roughHeadDensity_pos (W : ℕ) :
    0 < roughHeadDensity W := by
  have hmod : (0 : ℝ) < (roughHeadModulus W : ℝ) := by
    exact_mod_cast roughHeadModulus_pos W
  have htot : (0 : ℝ) < ((roughHeadModulus W).totient : ℝ) := by
    exact_mod_cast Nat.totient_pos.mpr (roughHeadModulus_pos W)
  exact div_pos htot hmod



































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











/-! ## Exact smooth-row quota initialization -/



























/-! ## Exact frozen-height ledger and centered adjustment -/



























/-! ## Literal Section 8 families -/

















/-- The family-level exact identity `qAct(d) = q0 - d`. -/
theorem bankPaperCanonicalSmoothFinalActiveMassFamily_eq_q0_sub_d
    (mu : Real) (logY Lambda0 mFrozen qTilde : Nat -> Real) (n : Nat) :
    bankPaperCanonicalSmoothFinalActiveMassFamily
        mu logY Lambda0 mFrozen qTilde n =
      bankPaperCanonicalSmoothQ0Family mFrozen qTilde n -
        bankPaperCanonicalSmoothDRealFamily
          mu logY Lambda0 mFrozen qTilde n :=
  rfl







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

/- Source module: Erdos390.WholePaper.CentralAnchorCutoff -/
section


/-!
# The fixed-prefix central-anchor cutoff

For a fixed prefix depth `R`, the paper splits the central prime blocks at
`n / (R + 1)`.  This file gives an explicit sufficient threshold for all
scale separations and then connects that literal cutoff directly to the
large-prime routing and central-anchor product APIs.
-/

open Filter
open scoped BigOperators

namespace Erdos390.WholePaper

noncomputable section







/-- At the explicit threshold, the cutoff is at least `4(R+1)`. -/
theorem four_mul_succ_le_centralAnchorCutoff
    {R n : ℕ} (hn : centralAnchorCutoffThreshold R ≤ n) :
    4 * (R + 1) ≤ centralAnchorCutoff R n := by
  rw [centralAnchorCutoff, Nat.le_div_iff_mul_le (by omega)]
  simpa only [centralAnchorCutoffThreshold, pow_two, mul_assoc] using hn



/-- The explicit threshold also puts `2n` strictly below the cutoff square. -/
theorem two_mul_lt_centralAnchorCutoff_sq
    {R n : ℕ} (hn : centralAnchorCutoffThreshold R ≤ n) :
    2 * n < (centralAnchorCutoff R n) ^ 2 := by
  let X := centralAnchorCutoff R n
  have hX : 4 * (R + 1) ≤ X := by
    simpa only [X] using four_mul_succ_le_centralAnchorCutoff hn
  have hXPos : 0 < X := by omega
  have hnUpper : n < (R + 1) * (X + 1) := by
    simpa only [X, centralAnchorCutoff] using
      Nat.lt_mul_div_succ n (by omega : 0 < R + 1)
  have hlinear : 2 * (R + 1) * (X + 1) ≤ X ^ 2 := by
    calc
      2 * (R + 1) * (X + 1) ≤ 2 * (R + 1) * (2 * X) := by
        exact Nat.mul_le_mul_left (2 * (R + 1)) (by omega)
      _ = (4 * (R + 1)) * X := by ring
      _ ≤ X * X := Nat.mul_le_mul_right X hX
      _ = X ^ 2 := by ring
  calc
    2 * n < 2 * ((R + 1) * (X + 1)) :=
      (Nat.mul_lt_mul_left (by omega : 0 < 2)).2 hnUpper
    _ = 2 * (R + 1) * (X + 1) := by ring
    _ ≤ X ^ 2 := hlinear







































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



/-- A positive divisor of the positive precharged tail leaves a positive
selector target. -/
theorem selectorTailTarget_pos
    {c : ℝ} {depth n : ℕ} {left right : ℕ → ℕ}
    {changed : Finset ℕ}
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (R : BankPaperRealization n
      (upperEndpoint n (upperTailLength c n)))
    (fixed : Finset ℕ)
    (hfixedPositive : ∀ a ∈ fixed, 0 < a)
    (hchargeDvd : R.selectorTailCharge fixed ∣
      certificate.prechargedTailTarget) :
    0 < certificate.selectorTailTarget R fixed := by
  apply Nat.div_pos
  · exact Nat.le_of_dvd certificate.prechargedTailTarget_pos hchargeDvd
  · exact R.selectorTailCharge_pos fixed hfixedPositive

/-- Division-free recovery of the precharged tail from the residual
selector target and its complete base charge. -/
theorem selectorTailTarget_mul_selectorTailCharge
    {c : ℝ} {depth n : ℕ} {left right : ℕ → ℕ}
    {changed : Finset ℕ}
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (R : BankPaperRealization n
      (upperEndpoint n (upperTailLength c n)))
    (fixed : Finset ℕ)
    (hchargeDvd : R.selectorTailCharge fixed ∣
      certificate.prechargedTailTarget) :
    certificate.selectorTailTarget R fixed *
        R.selectorTailCharge fixed =
      certificate.prechargedTailTarget := by
  rw [selectorTailTarget]
  exact Nat.div_mul_cancel hchargeDvd





end GuardedCentralAnchorCertificate

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

/- Source module: Erdos390.WholePaper.BankPaperProposition87EndpointSelector -/
section


/-!
# Proposition 8.7 endpoint as an ambient natural-number selector

The bridge is carried out on a tagged active sample, whereas Section 9 uses
one weight function on natural-number coordinates.  This file performs the
finite push-forward exactly.  The ambient selector is the sum of

* every frozen tagged contribution, including a protected contribution on a
  coordinate which may also be active; and
* the endpoint active weight produced by Proposition 8.7.

Thus no disjointness between the protected and active layers is imposed.
The proofs below use only the literal Proposition 8.7 path output.  In
particular, they do not claim the separate complete-rough-row integrality or
outside-band target identities still needed by the Section 9 tangent input.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.PaperBridgeFit
open Erdos390.Full.PaperGuardCensus
open Erdos390.Full.RegularMeshPrimeCutoffs
open Erdos390.Full.RegularRelativeMesh

noncomputable section

/-! ## Backward-compatible literal-mass bridge data -/









/-! ## Push-forward to natural-number coordinates -/







/-- Every frozen tag maps into the finite ambient support. -/
theorem fixedValue_mem_bankPaperProposition87SelectorSupport
    {Head Band Fixed : Type*}
    [Fintype Head] [DecidableEq Head]
    [Fintype Band] [DecidableEq Band] [Fintype Fixed]
    (B : BridgeData Head Band) (fixedValue : Fixed -> Nat) (f : Fixed) :
    fixedValue f ∈ bankPaperProposition87SelectorSupport B fixedValue := by
  classical
  simp [bankPaperProposition87SelectorSupport]

/-- Every active sample tag maps into the finite ambient support. -/
theorem sampleValue_mem_bankPaperProposition87SelectorSupport
    {Head Band Fixed : Type*}
    [Fintype Head] [DecidableEq Head]
    [Fintype Band] [DecidableEq Band] [Fintype Fixed]
    (B : BridgeData Head Band) (fixedValue : Fixed -> Nat)
    (m : B.sampleData.Sample) :
    B.sampleData.value m ∈
      bankPaperProposition87SelectorSupport B fixedValue := by
  classical
  simp [bankPaperProposition87SelectorSupport]

/-- The ambient selector has no hidden support outside the two tagged
layers. -/
theorem bankPaperProposition87SelectorAt_eq_zero_of_not_mem_support
    {Head Band Fixed : Type*}
    [Fintype Head] [DecidableEq Head]
    [Fintype Band] [DecidableEq Band] [Fintype Fixed]
    [Nonempty Head]
    (B : BridgeData Head Band)
    (fixedValue : Fixed -> Nat) (fixedWeight : Fixed -> Real)
    (path : Real -> B.ParamSpace) (t : Real) {a : Nat}
    (ha : a ∉ bankPaperProposition87SelectorSupport B fixedValue) :
    bankPaperProposition87SelectorAt
      B fixedValue fixedWeight path t a = 0 := by
  classical
  have hfixed : ∀ f : Fixed, fixedValue f ≠ a := by
    intro f hfa
    apply ha
    rw [← hfa]
    exact fixedValue_mem_bankPaperProposition87SelectorSupport
      B fixedValue f
  have hactive : ∀ m : B.sampleData.Sample,
      B.sampleData.value m ≠ a := by
    intro m hma
    apply ha
    rw [← hma]
    exact sampleValue_mem_bankPaperProposition87SelectorSupport
      B fixedValue m
  simp [bankPaperProposition87SelectorAt,
    BridgeData.ambientCombinedWeight, BridgeData.frozenAmbientWeight,
    BridgeData.ambientActiveWeight, hfixed, hactive]

private theorem sum_fiberWeight_mul
    {I : Type*} [Fintype I]
    (support : Finset Nat) (value : I -> Nat) (weight : I -> Real)
    (hvalue : ∀ i, value i ∈ support) (F : Nat -> Real) :
    (∑ a ∈ support, (∑ i : I,
      if value i = a then weight i else 0) * F a) =
      ∑ i : I, weight i * F (value i) := by
  classical
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.sum_eq_single (value i)]
  · simp
  · intro a ha hne
    simp [hne.symm]
  · intro hnot
    exact (hnot (hvalue i)).elim

/-- Exact push-forward identity for an arbitrary arithmetic statistic.  It
is valid even when several frozen tags, or a frozen and an active tag, share
one natural-number coordinate. -/
theorem sum_bankPaperProposition87SelectorAt_mul
    {Head Band Fixed : Type*}
    [Fintype Head] [DecidableEq Head]
    [Fintype Band] [DecidableEq Band] [Fintype Fixed]
    [Nonempty Head]
    (B : BridgeData Head Band)
    (fixedValue : Fixed -> Nat) (fixedWeight : Fixed -> Real)
    (path : Real -> B.ParamSpace) (t : Real) (F : Nat -> Real) :
    (∑ a ∈ bankPaperProposition87SelectorSupport B fixedValue,
      bankPaperProposition87SelectorAt
        B fixedValue fixedWeight path t a * F a) =
      (∑ f : Fixed, fixedWeight f * F (fixedValue f)) +
        B.paperMoment (fun m => F (B.sampleData.value m)) (path t) := by
  classical
  unfold bankPaperProposition87SelectorAt
  simp only [BridgeData.ambientCombinedWeight,
    BridgeData.frozenAmbientWeight, BridgeData.ambientActiveWeight, add_mul]
  rw [Finset.sum_add_distrib]
  rw [sum_fiberWeight_mul
    (bankPaperProposition87SelectorSupport B fixedValue)
    fixedValue fixedWeight
    (fixedValue_mem_bankPaperProposition87SelectorSupport B fixedValue) F]
  rw [sum_fiberWeight_mul
    (bankPaperProposition87SelectorSupport B fixedValue)
    B.sampleData.value (B.activeCoordinateWeight (path t))
    (sampleValue_mem_bankPaperProposition87SelectorSupport B fixedValue) F]
  rfl



/-! ## Literal marked residual at the pushed-forward endpoint -/





/-- After the exact push-forward, the full ambient residual is exactly the
active residual appearing in Proposition 8.7. -/
theorem bankPaperProposition87FullMarkedResidual_eq_activeResidual
    {Head Band Fixed : Type*}
    [Fintype Head] [DecidableEq Head]
    [Fintype Band] [DecidableEq Band] [Fintype Fixed]
    [Nonempty Head]
    (B : BridgeData Head Band)
    (fixedValue : Fixed -> Nat) (fixedWeight : Fixed -> Real)
    (markedTarget : Nat -> Real)
    (path : Real -> B.ParamSpace) (p : Nat) :
    bankPaperProposition87FullMarkedResidual
        B fixedValue fixedWeight markedTarget path p =
      markedTarget p -
        B.paperMoment (B.markedValuation p) (path 1) := by
  unfold bankPaperProposition87FullMarkedResidual
    bankPaperProposition87EndpointSelector
  rw [sum_bankPaperProposition87SelectorAt_mul]
  unfold bankPaperProposition87FullMarkedTarget BridgeData.markedValuation
  ring





/-! ## Direct extraction from the literal Proposition 8.7 conclusion -/









end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankAnchorCollisionFree -/
section


/-!
# Collision freedom between the complete central anchors and the actual bank

The large-anchor branch recovers the common prime marker from the complete
rough factorization above `yNat`.  Once the marker is recovered, the guarded
central-cofactor certificate excludes the two incident state cores.

The residual branch uses the more rigid shape
`2^k * p^e`.  A bottom marker is already above the residual cutoff.  For an
ordinary marker, divisibility first forces the residual base prime to be the
marker; its marker valuation is then one, so cancellation would make the
ordinary state core a power of two, contrary to the path certificate.

Donor-only occurrences do not create an extra case: ordinary donors and the
two nonterminal bottom donors lie above `2n`, while terminal bottom donors
are literally their upper endpoint state.
-/

open Filter Topology

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel

noncomputable section

/-! ## The two eventual scale separations used by marker recovery -/

/-- The elementary square bound behind the separation
`yNat n < centralAnchorCutoff depth n`. -/
theorem bankAnchor_yNat_mul_self_le_self
    {n : ℕ} (hn : 1 ≤ n) : yNat n * yNat n ≤ n := by
  have hnOne : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hyNonneg : 0 ≤ y n := Real.rpow_nonneg (by positivity) _
  have hyFloor : (yNat n : ℝ) ≤ y n := Nat.floor_le hyNonneg
  have hyFloorNonneg : (0 : ℝ) ≤ yNat n := by positivity
  have hsq : (yNat n : ℝ) ^ 2 ≤ y n ^ 2 :=
    (sq_le_sq₀ hyFloorNonneg hyNonneg).2 hyFloor
  have hpow : (n : ℝ) ^ (4 / 9 : ℝ) ≤ (n : ℝ) := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hnOne
        (by norm_num : (4 / 9 : ℝ) ≤ 1)
  rw [Erdos390.Full.Scale.y_pow_two] at hsq
  have hcast : ((yNat n * yNat n : ℕ) : ℝ) ≤ (n : ℝ) := by
    push_cast
    simpa only [pow_two] using hsq.trans hpow
  exact_mod_cast hcast





/-- At the literal central-anchor threshold, the moving smooth cutoff is
strictly below the residual/large-prime cutoff. -/
theorem yNat_lt_centralAnchorCutoff_of_threshold
    {depth n : ℕ} (hn : 1 ≤ n)
    (hnCutoff : centralAnchorCutoffThreshold depth ≤ n) :
    yNat n < centralAnchorCutoff depth n := by
  have hySq := bankAnchor_yNat_mul_self_le_self hn
  have hcutSq := two_mul_lt_centralAnchorCutoff_sq hnCutoff
  nlinarith

theorem eventually_yNat_lt_centralAnchorCutoff (depth : ℕ) :
    ∀ᶠ n : ℕ in atTop, yNat n < centralAnchorCutoff depth n := by
  filter_upwards [eventually_ge_atTop 1,
      eventually_ge_atTop (centralAnchorCutoffThreshold depth)]
      with n hn hnCutoff
  exact yNat_lt_centralAnchorCutoff_of_threshold hn hnCutoff

/-! ## Arithmetic collision kernels -/



namespace BankPaperRealization



/-! ## Literal recovery of the incident cores from actual requests -/





















/-! ## Complete finite collision theorem -/





end BankPaperRealization

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

/- Source module: Erdos390.WholePaper.BankPaperCanonicalPrefixAdapter -/
section


/-!
# Prefix adapter for the canonical rounded selector

The rounded selector already supplies exact mass balance in every declared
ratio band and a pointwise bound for every prime residual.  Those two facts
determine the required prefix estimate: a prefix is the negative strict tail
of its band, so its absolute value is bounded by the sum of the pointwise
majorants in that tail.

This file keeps that elementary conversion separate from the analytic work.
In particular, the constructor below does not ask for an independently
rounded prefix estimate.  For a user-chosen `prefixUpper`, its only extra
input is the analytic comparison from the deterministic tail sum to that
majorant.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel

noncomputable section

/-- Exact band balance and the pointwise canonical residual estimate imply
the primitive ratio-cell prefix bound.  The right side is the literal strict
tail sum of the pointwise upper bounds; no prefix-rounding hypothesis occurs
in this statement. -/
theorem bankPaperCanonicalTangentResidual_abs_prefixMass_le_tailPointwiseUpper
    {c : Real} {depth n W : Nat} {left right : Nat -> Nat}
    {changed : Finset Nat}
    (R : BankPaperRealization n
      (upperEndpoint n (upperTailLength c n)))
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (fixed candidates : Finset Nat)
    {Band : Type*} [DecidableEq Band]
    (bandOf : BankPaperCanonicalTangentPrime n W -> Band)
    (cellIndex : BankPaperCanonicalTangentPrime n W -> Nat)
    (pointwiseUpper : BankPaperCanonicalTangentPrime n W -> Real)
    (selector : Nat -> Real)
    (hbalance : forall band : Band,
      (∑ p : BankPaperCanonicalTangentPrime n W,
        if bandOf p = band then
          bankPaperCanonicalTangentResidual
            R certificate fixed candidates selector p
        else 0) = 0)
    (hpointwise : forall p : BankPaperCanonicalTangentPrime n W,
      |bankPaperCanonicalTangentResidual
          R certificate fixed candidates selector p| <= pointwiseUpper p)
    (band : Band) (cut : Nat) :
    |tangentRatioCellPrefixMass
        (bankPaperCanonicalTangentResidual
          R certificate fixed candidates selector)
        bandOf cellIndex band cut| <=
      tangentRatioCellTailPointwiseUpper
        pointwiseUpper bandOf cellIndex band cut := by
  exact abs_tangentRatioCellPrefixMass_le_tailPointwiseUpper
    (bankPaperCanonicalTangentResidual
      R certificate fixed candidates selector)
    pointwiseUpper bandOf cellIndex hbalance hpointwise band cut

/-- Constructor for the existing pre-tangent selector interface which
derives its prefix field from band balance and the pointwise residual bound.
The sole surviving prefix-side hypothesis is the analytic domination of the
literal pointwise tail sum by the requested `prefixUpper`. -/
theorem bankPaperCanonicalRoundedSelectorTangentInput_of_tailPointwiseMajorant
    {c : Real} {depth n W : Nat} {left right : Nat -> Nat}
    {changed : Finset Nat}
    (R : BankPaperRealization n
      (upperEndpoint n (upperTailLength c n)))
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (fixed candidates : Finset Nat)
    {Band : Type*} [DecidableEq Band]
    (bandOf : BankPaperCanonicalTangentPrime n W -> Band)
    (cellIndex : BankPaperCanonicalTangentPrime n W -> Nat)
    (pointwiseUpper : BankPaperCanonicalTangentPrime n W -> Real)
    (prefixUpper : Band -> Nat -> Real)
    (selector : Nat -> Real)
    (hselector : ∀ a ∈ candidates,
      0 <= selector a ∧ selector a <= 1)
    (hrowIntegral : BankPaperCanonicalSelectorRowIntegral
      n candidates selector)
    (hprimeBandBalance :
      BankPaperCanonicalPostRoundingPrimeBandBalance (W := W)
        R certificate fixed candidates selector)
    (hdeficitSupport :
      BankPaperCanonicalSelectorDeficitSupportedOnPrimeBand (W := W)
        R certificate fixed candidates selector)
    (hbalance : forall band : Band,
      (∑ p : BankPaperCanonicalTangentPrime n W,
        if bandOf p = band then
          bankPaperCanonicalTangentResidual
            R certificate fixed candidates selector p
        else 0) = 0)
    (hpointwise : forall p : BankPaperCanonicalTangentPrime n W,
      |bankPaperCanonicalTangentResidual
          R certificate fixed candidates selector p| <= pointwiseUpper p)
    (htailMajorant : forall band : Band, forall cut : Nat,
      tangentRatioCellTailPointwiseUpper
          pointwiseUpper bandOf cellIndex band cut <= prefixUpper band cut) :
    BankPaperCanonicalRoundedSelectorTangentInput
      R certificate fixed candidates bandOf cellIndex
        pointwiseUpper prefixUpper selector := by
  refine ⟨hselector, hrowIntegral, hprimeBandBalance, hdeficitSupport,
    hbalance, hpointwise, ?_⟩
  intro band cut
  exact le_trans
    (bankPaperCanonicalTangentResidual_abs_prefixMass_le_tailPointwiseUpper
      R certificate fixed candidates bandOf cellIndex pointwiseUpper selector
      hbalance hpointwise band cut)
    (htailMajorant band cut)

/-- In the primitive form no analytic simplification of the tail sum is
made at all: the existing selector input is obtained with the deterministic
tail sum itself as `prefixUpper`. -/
theorem bankPaperCanonicalRoundedSelectorTangentInput_of_balance_pointwise
    {c : Real} {depth n W : Nat} {left right : Nat -> Nat}
    {changed : Finset Nat}
    (R : BankPaperRealization n
      (upperEndpoint n (upperTailLength c n)))
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (fixed candidates : Finset Nat)
    {Band : Type*} [DecidableEq Band]
    (bandOf : BankPaperCanonicalTangentPrime n W -> Band)
    (cellIndex : BankPaperCanonicalTangentPrime n W -> Nat)
    (pointwiseUpper : BankPaperCanonicalTangentPrime n W -> Real)
    (selector : Nat -> Real)
    (hselector : ∀ a ∈ candidates,
      0 <= selector a ∧ selector a <= 1)
    (hrowIntegral : BankPaperCanonicalSelectorRowIntegral
      n candidates selector)
    (hprimeBandBalance :
      BankPaperCanonicalPostRoundingPrimeBandBalance (W := W)
        R certificate fixed candidates selector)
    (hdeficitSupport :
      BankPaperCanonicalSelectorDeficitSupportedOnPrimeBand (W := W)
        R certificate fixed candidates selector)
    (hbalance : forall band : Band,
      (∑ p : BankPaperCanonicalTangentPrime n W,
        if bandOf p = band then
          bankPaperCanonicalTangentResidual
            R certificate fixed candidates selector p
        else 0) = 0)
    (hpointwise : forall p : BankPaperCanonicalTangentPrime n W,
      |bankPaperCanonicalTangentResidual
          R certificate fixed candidates selector p| <= pointwiseUpper p) :
    BankPaperCanonicalRoundedSelectorTangentInput
      R certificate fixed candidates bandOf cellIndex pointwiseUpper
        (tangentRatioCellTailPointwiseUpper
          pointwiseUpper bandOf cellIndex) selector := by
  exact bankPaperCanonicalRoundedSelectorTangentInput_of_tailPointwiseMajorant
    R certificate fixed candidates bandOf cellIndex pointwiseUpper
      (tangentRatioCellTailPointwiseUpper pointwiseUpper bandOf cellIndex)
      selector hselector hrowIntegral hprimeBandBalance hdeficitSupport
      hbalance hpointwise (fun _band _cut => le_rfl)

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



/-- Integral mass on every attained complete-rough row makes the total
candidate mass integral. -/
theorem exists_bankPaperCanonicalTotalQuota_of_rowIntegral
    {n : Nat} {candidates : Finset Nat} {selector : Nat -> Real}
    (hrow : BankPaperCanonicalSelectorRowIntegral n candidates selector) :
    ∃ candidateQuota : Int,
      (∑ a ∈ candidates, selector a) = (candidateQuota : Real) := by
  classical
  let rowQuota : Nat -> Int := fun label =>
    if hlabel : label ∈ completeRoughLabelSet (yNat n) candidates then
      Classical.choose (hrow label hlabel)
    else 0
  have hrowQuota : forall label
      (hlabel : label ∈ completeRoughLabelSet (yNat n) candidates),
      (∑ a ∈ completeRoughRowFiber (yNat n) candidates label,
          selector a) = (rowQuota label : Real) := by
    intro label hlabel
    simp only [rowQuota, dif_pos hlabel]
    exact Classical.choose_spec (hrow label hlabel)
  refine ⟨(∑ label ∈ completeRoughLabelSet (yNat n) candidates,
      rowQuota label), ?_⟩
  rw [sum_eq_sum_completeRoughRowFibers]
  calc
    (∑ label ∈ completeRoughLabelSet (yNat n) candidates,
        ∑ a ∈ completeRoughRowFiber (yNat n) candidates label,
          selector a) =
        ∑ label ∈ completeRoughLabelSet (yNat n) candidates,
          (rowQuota label : Real) := by
      apply Finset.sum_congr rfl
      intro label hlabel
      exact hrowQuota label hlabel
    _ = ((∑ label ∈ completeRoughLabelSet (yNat n) candidates,
          rowQuota label : Int) : Real) := by
      push_cast
      rfl

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

/-- In particular, every active bridge value is an actual guarded
candidate. -/
theorem bankPaperCanonicalBridgeActiveValues_subset_guardedCandidates
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
      R.roughCanonicalGuardedCandidateSet certificate deltaStar K := by
  intro a ha
  exact (mem_completeRoughRowFiber.mp
    (bankPaperCanonicalBridgeActiveValues_subset_guardedSmoothRow
      B R certificate deltaStar hKh hlower hupper hnotGuard ha)).1





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

/-- The active seed is nonnegative coordinatewise. -/
theorem bankPaperCanonicalActiveSeed_nonneg
    {Head : Type*} [Fintype Head] [Nonempty Head]
    {D : StructuredSampleData Head} {T : BarycentricTarget D}
    {candidates : Finset Nat} {preSelector : Nat -> Real}
    {activeSeed : D.Sample -> Real}
    (H : BankPaperCanonicalActualActiveMeasureConstructor
      D T candidates preSelector activeSeed)
    (m : D.Sample) : 0 <= activeSeed m := by
  rw [bankPaperCanonicalActiveSeed_eq_mass_mul_baseline H m]
  exact mul_nonneg
    (zero_le_one.trans (bankPaperCanonicalLiteralActiveMass_one_le H))
    (T.baseline.baseWeight_nonneg m)

/-- The ambient seed is dominated by the guarded pre-selector on every
candidate coordinate. -/
theorem bankPaperCanonicalActiveSeedAmbientWeight_le_preSelector
    {Head : Type*} [Fintype Head] [Nonempty Head]
    {D : StructuredSampleData Head} {T : BarycentricTarget D}
    {candidates : Finset Nat} {preSelector : Nat -> Real}
    {activeSeed : D.Sample -> Real}
    (H : BankPaperCanonicalActualActiveMeasureConstructor
      D T candidates preSelector activeSeed)
    {a : Nat} (ha : a ∈ candidates) :
    bankPaperCanonicalActiveSeedAmbientWeight D activeSeed a <=
      preSelector a := by
  exact H.2.2.2 a ha







/-! ## The actual scaled bridge data -/









/-! ## Tagged frozen remainder and exact push-forward -/







/-- The ambient active seed is nonnegative. -/
theorem bankPaperCanonicalActiveSeedAmbientWeight_nonneg
    {Head : Type*} [Fintype Head] [Nonempty Head]
    {D : StructuredSampleData Head} {T : BarycentricTarget D}
    {candidates : Finset Nat} {preSelector : Nat -> Real}
    {activeSeed : D.Sample -> Real}
    (H : BankPaperCanonicalActualActiveMeasureConstructor
      D T candidates preSelector activeSeed) (a : Nat) :
    0 <= bankPaperCanonicalActiveSeedAmbientWeight D activeSeed a := by
  unfold bankPaperCanonicalActiveSeedAmbientWeight
  apply Finset.sum_nonneg
  intro m _hm
  split_ifs
  · exact bankPaperCanonicalActiveSeed_nonneg H m
  · exact le_rfl

/-- The ambient active seed vanishes off the candidate set. -/
theorem bankPaperCanonicalActiveSeedAmbientWeight_eq_zero_of_not_mem
    {Head : Type*} [Fintype Head] [Nonempty Head]
    {D : StructuredSampleData Head} {T : BarycentricTarget D}
    {candidates : Finset Nat} {preSelector : Nat -> Real}
    {activeSeed : D.Sample -> Real}
    (H : BankPaperCanonicalActualActiveMeasureConstructor
      D T candidates preSelector activeSeed)
    {a : Nat} (ha : a ∉ candidates) :
    bankPaperCanonicalActiveSeedAmbientWeight D activeSeed a = 0 := by
  unfold bankPaperCanonicalActiveSeedAmbientWeight
  apply Finset.sum_eq_zero
  intro m _hm
  rw [if_neg]
  intro hma
  apply ha
  rw [← hma]
  exact bankPaperCanonicalActiveSeed_value_mem_candidates H m

/-- Summing the ambient push-forward over all guarded candidates recovers
the tagged active mass exactly, even before using value-map injectivity. -/
theorem sum_bankPaperCanonicalActiveSeedAmbientWeight_eq_activeMass
    {Head : Type*} [Fintype Head] [Nonempty Head]
    {D : StructuredSampleData Head} {T : BarycentricTarget D}
    {candidates : Finset Nat} {preSelector : Nat -> Real}
    {activeSeed : D.Sample -> Real}
    (H : BankPaperCanonicalActualActiveMeasureConstructor
      D T candidates preSelector activeSeed) :
    (∑ a ∈ candidates,
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
    exact (hnot (bankPaperCanonicalActiveSeed_value_mem_candidates H m)).elim

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

/-- Feasibility of the guarded pre-selector and dominance of the active
seed imply feasibility of the complete frozen protected remainder. -/
theorem bankPaperCanonicalActualFrozenWeight_mem_Icc
    {Head : Type*} [Fintype Head] [Nonempty Head]
    {D : StructuredSampleData Head} {T : BarycentricTarget D}
    {candidates : Finset Nat} {preSelector : Nat -> Real}
    {activeSeed : D.Sample -> Real}
    (H : BankPaperCanonicalActualActiveMeasureConstructor
      D T candidates preSelector activeSeed)
    (hselector : ∀ a ∈ candidates,
      0 <= preSelector a ∧ preSelector a <= 1) :
    forall a,
      BridgeData.frozenAmbientWeight
        (bankPaperCanonicalActualFrozenValue (candidates := candidates))
        (bankPaperCanonicalActualFrozenWeight
          D candidates preSelector activeSeed) a ∈ Set.Icc (0 : Real) 1 := by
  intro a
  rw [frozenAmbientWeight_eq_bankPaperCanonicalActualFrozenWeight]
  by_cases ha : a ∈ candidates
  · rw [if_pos ha]
    constructor
    · exact sub_nonneg.mpr
        (bankPaperCanonicalActiveSeedAmbientWeight_le_preSelector H ha)
    · exact (sub_le_self _
        (bankPaperCanonicalActiveSeedAmbientWeight_nonneg H a)).trans
          (hselector a ha).2
  · simp [ha]

/-- The total frozen remainder is the pre-selector mass minus the literal
active mass. -/
theorem sum_bankPaperCanonicalActualFrozenWeight
    {Head : Type*} [Fintype Head] [Nonempty Head]
    {D : StructuredSampleData Head} {T : BarycentricTarget D}
    {candidates : Finset Nat} {preSelector : Nat -> Real}
    {activeSeed : D.Sample -> Real}
    (H : BankPaperCanonicalActualActiveMeasureConstructor
      D T candidates preSelector activeSeed) :
    (∑ a : BankPaperCanonicalActualFrozenIndex candidates,
      bankPaperCanonicalActualFrozenWeight
        D candidates preSelector activeSeed a) =
      (∑ a ∈ candidates, preSelector a) -
        bankPaperCanonicalLiteralActiveMass D activeSeed := by
  classical
  unfold bankPaperCanonicalActualFrozenWeight
  rw [Finset.sum_sub_distrib]
  rw [← Finset.sum_subtype candidates (fun _ => Iff.rfl)
    (fun a => preSelector a)]
  rw [← Finset.sum_subtype candidates (fun _ => Iff.rfl)
    (fun a => bankPaperCanonicalActiveSeedAmbientWeight D activeSeed a)]
  rw [sum_bankPaperCanonicalActiveSeedAmbientWeight_eq_activeMass H]

/-- Complete-rough-row integrality of the guarded selector supplies the
integer total quota required by Proposition 8.7, with no new quota premise. -/
theorem exists_bankPaperCanonicalActualP87IntegerQuota
    {Head : Type*} [Fintype Head] [Nonempty Head]
    {D : StructuredSampleData Head} {T : BarycentricTarget D}
    {candidates : Finset Nat} {preSelector : Nat -> Real}
    {activeSeed : D.Sample -> Real}
    (H : BankPaperCanonicalActualActiveMeasureConstructor
      D T candidates preSelector activeSeed)
    (hrow : BankPaperCanonicalSelectorRowIntegral
      D.n candidates preSelector) :
    ∃ quota : Int,
      (quota : Real) =
        (∑ a : BankPaperCanonicalActualFrozenIndex candidates,
          bankPaperCanonicalActualFrozenWeight
            D candidates preSelector activeSeed a) +
          bankPaperCanonicalLiteralActiveMass D activeSeed := by
  obtain ⟨quota, hquota⟩ :=
    exists_bankPaperCanonicalTotalQuota_of_rowIntegral hrow
  refine ⟨quota, ?_⟩
  rw [sum_bankPaperCanonicalActualFrozenWeight H]
  linarith

/-! ## The initial combined selector -/

/-- At parameter zero the bridge active weight is exactly its supplied
baseline coordinate weight. -/
theorem BridgeData.activeCoordinateWeight_zero_eq_baseline
    {Head Band : Type*} [Fintype Head] [DecidableEq Head]
    [Fintype Band] [DecidableEq Band] [Nonempty Head]
    (B : BridgeData Head Band) (m : B.sampleData.Sample) :
    B.activeCoordinateWeight 0 m = B.baseline.baseWeight m := by
  unfold Erdos390.Full.PaperBridgeFit.BridgeData.activeCoordinateWeight
    Erdos390.Full.FiniteExponentialFamily.activeWeight
  change B.vectorFamily.baseMass * B.vectorFamily.probabilityMass 0 m =
    B.baseline.baseWeight m
  rw [
    Erdos390.Full.PaperBridgeFit.BridgeData.probabilityMass_zero B m,
    Erdos390.Full.PaperBridgeFit.BridgeData.vectorFamily_baseMass B]
  field_simp [ne_of_gt B.q_pos]

/-- If the bridge baseline is the actual seed, its ambient time-zero active
layer is the ambient push-forward of that seed. -/
theorem BridgeData.ambientActiveWeight_zero_eq_activeSeedAmbient
    {Head Band : Type*} [Fintype Head] [DecidableEq Head]
    [Fintype Band] [DecidableEq Band] [Nonempty Head]
    (B : BridgeData Head Band)
    (activeSeed : B.sampleData.Sample -> Real)
    (hseed : forall m, B.baseline.baseWeight m = activeSeed m)
    (a : Nat) :
    B.ambientActiveWeight 0 a =
      bankPaperCanonicalActiveSeedAmbientWeight
        B.sampleData activeSeed a := by
  unfold BridgeData.ambientActiveWeight
    bankPaperCanonicalActiveSeedAmbientWeight
  apply Finset.sum_congr rfl
  intro m _hm
  rw [
    Erdos390.WholePaper.BridgeData.activeCoordinateWeight_zero_eq_baseline
      B m,
    hseed m]

/-- With the frozen protected remainder retained, the combined bridge at
time zero is exactly the guarded pre-selector on candidates and zero off
the candidate set. -/
theorem bankPaperCanonicalActualSelectorAt_zero_eq_preSelector
    {Head Band : Type*} [Fintype Head] [DecidableEq Head]
    [Fintype Band] [DecidableEq Band] [Nonempty Head]
    (B : BridgeData Head Band)
    {T : BarycentricTarget B.sampleData}
    (candidates : Finset Nat) (preSelector : Nat -> Real)
    (activeSeed : B.sampleData.Sample -> Real)
    (H : BankPaperCanonicalActualActiveMeasureConstructor
      B.sampleData T candidates preSelector activeSeed)
    (hseed : forall m, B.baseline.baseWeight m = activeSeed m)
    (path : Real -> B.ParamSpace) (t : Real) (ht : path t = 0)
    (a : Nat) :
    bankPaperProposition87SelectorAt B
        (bankPaperCanonicalActualFrozenValue (candidates := candidates))
        (bankPaperCanonicalActualFrozenWeight
          B.sampleData candidates preSelector activeSeed)
        path t a =
      if a ∈ candidates then preSelector a else 0 := by
  unfold bankPaperProposition87SelectorAt
    BridgeData.ambientCombinedWeight
  rw [frozenAmbientWeight_eq_bankPaperCanonicalActualFrozenWeight, ht,
    Erdos390.WholePaper.BridgeData.ambientActiveWeight_zero_eq_activeSeedAmbient
      B activeSeed hseed a]
  by_cases ha : a ∈ candidates
  · rw [if_pos ha]
    simp [ha]
  · rw [if_neg ha,
      bankPaperCanonicalActiveSeedAmbientWeight_eq_zero_of_not_mem H ha]
    simp [ha]

/-- The finite support used by the pushed-forward Proposition 8.7 selector
is exactly the literal guarded candidate set. -/
theorem bankPaperCanonicalActualP87SelectorSupport_eq_candidates
    {Head Band : Type*} [Fintype Head] [DecidableEq Head]
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData Head Band)
    (candidates : Finset Nat)
    (hvalues : forall m : B.sampleData.Sample,
      B.sampleData.value m ∈ candidates) :
    bankPaperProposition87SelectorSupport B
      (bankPaperCanonicalActualFrozenValue (candidates := candidates)) =
        candidates := by
  classical
  ext a
  constructor
  · intro ha
    rw [bankPaperProposition87SelectorSupport, Finset.mem_union] at ha
    rcases ha with haFrozen | haActive
    · obtain ⟨f, _hf, rfl⟩ := Finset.mem_image.mp haFrozen
      exact f.2
    · obtain ⟨m, _hm, hma⟩ := Finset.mem_image.mp haActive
      rw [← hma]
      exact hvalues m
  · intro ha
    apply Finset.mem_union_left
    exact Finset.mem_image.mpr ⟨(⟨a, ha⟩ : ↑candidates),
      Finset.mem_univ _, rfl⟩

/-! ## The literal active marked target and endpoint -/





/-- Adding the tagged frozen target contribution back to the active marked
target recovers the literal residual selector target exactly. -/
theorem bankPaperCanonicalActualFullMarkedTarget_eq_selectorTailTarget
    {Head Band : Type*} [Fintype Head] [DecidableEq Head]
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData Head Band)
    {c : Real} {depth : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (fixed candidates : Finset Nat) (preSelector : Nat -> Real)
    (activeSeed : B.sampleData.Sample -> Real) (p : Nat) :
    bankPaperProposition87FullMarkedTarget
        (bankPaperCanonicalActualFrozenValue (candidates := candidates))
        (bankPaperCanonicalActualFrozenWeight
          B.sampleData candidates preSelector activeSeed)
        (bankPaperCanonicalActualActiveMarkedTarget B R certificate
          fixed candidates preSelector activeSeed) p =
      ((certificate.selectorTailTarget R fixed).factorization p : Real) := by
  unfold bankPaperProposition87FullMarkedTarget
    bankPaperCanonicalActualActiveMarkedTarget
  ring

/-- The canonical target-minus-selector deficit of the actual endpoint is
literally the active residual appearing in Proposition 8.7. -/
theorem bankPaperCanonicalActualEndpoint_deficit_eq_activeResidual
    {Head Band : Type*} [Fintype Head] [DecidableEq Head]
    [Fintype Band] [DecidableEq Band] [Nonempty Head]
    (B : BridgeData Head Band)
    {c : Real} {depth : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (fixed candidates : Finset Nat) (preSelector : Nat -> Real)
    (activeSeed : B.sampleData.Sample -> Real)
    (hvalues : forall m : B.sampleData.Sample,
      B.sampleData.value m ∈ candidates)
    (path : Real -> B.ParamSpace) (p : Nat) :
    bankPaperCanonicalSelectorValuationDeficit R certificate fixed candidates
        (bankPaperCanonicalActualP87EndpointSelector
          B candidates preSelector activeSeed path) p =
      bankPaperCanonicalActualActiveMarkedTarget B R certificate
          fixed candidates preSelector activeSeed p -
        B.paperMoment (B.markedValuation p) (path 1) := by
  have hres := bankPaperProposition87FullMarkedResidual_eq_activeResidual
    B
    (bankPaperCanonicalActualFrozenValue (candidates := candidates))
    (bankPaperCanonicalActualFrozenWeight
      B.sampleData candidates preSelector activeSeed)
    (bankPaperCanonicalActualActiveMarkedTarget B R certificate
      fixed candidates preSelector activeSeed) path p
  unfold bankPaperProposition87FullMarkedResidual at hres
  rw [bankPaperCanonicalActualFullMarkedTarget_eq_selectorTailTarget,
    bankPaperCanonicalActualP87SelectorSupport_eq_candidates B candidates
      hvalues] at hres
  simpa only [bankPaperCanonicalSelectorValuationDeficit,
    bankPaperCanonicalActualP87EndpointSelector] using hres

/-- At the initial point, the active residual is exactly the prebridge
canonical selector deficit. -/
theorem bankPaperCanonicalActualInitial_deficit_eq_activeResidual
    {Head Band : Type*} [Fintype Head] [DecidableEq Head]
    [Fintype Band] [DecidableEq Band] [Nonempty Head]
    (B : BridgeData Head Band)
    {c : Real} {depth : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (fixed candidates : Finset Nat) (preSelector : Nat -> Real)
    (activeSeed : B.sampleData.Sample -> Real)
    {T : BarycentricTarget B.sampleData}
    (H : BankPaperCanonicalActualActiveMeasureConstructor
      B.sampleData T candidates preSelector activeSeed)
    (hseed : forall m, B.baseline.baseWeight m = activeSeed m)
    (p : Nat) :
    bankPaperCanonicalSelectorValuationDeficit R certificate fixed candidates
        preSelector p =
      bankPaperCanonicalActualActiveMarkedTarget B R certificate
          fixed candidates preSelector activeSeed p -
        B.paperMoment (B.markedValuation p) 0 := by
  let path0 : Real -> B.ParamSpace := fun _ => 0
  have hendpoint := bankPaperCanonicalActualEndpoint_deficit_eq_activeResidual
    B R certificate fixed candidates preSelector activeSeed
    (fun m => bankPaperCanonicalActiveSeed_value_mem_candidates H m)
    path0 p
  calc
    bankPaperCanonicalSelectorValuationDeficit R certificate fixed candidates
        preSelector p =
      bankPaperCanonicalSelectorValuationDeficit R certificate fixed candidates
        (bankPaperCanonicalActualP87EndpointSelector
          B candidates preSelector activeSeed path0) p := by
        unfold bankPaperCanonicalSelectorValuationDeficit
        apply congrArg (fun x : Real =>
          ((certificate.selectorTailTarget R fixed).factorization p : Real) - x)
        apply Finset.sum_congr rfl
        intro a ha
        rw [bankPaperCanonicalActualP87EndpointSelector,
          bankPaperProposition87EndpointSelector,
          bankPaperCanonicalActualSelectorAt_zero_eq_preSelector
            B candidates preSelector activeSeed H hseed path0 1 rfl a,
          if_pos ha]
    _ = bankPaperCanonicalActualActiveMarkedTarget B R certificate
          fixed candidates preSelector activeSeed p -
        B.paperMoment (B.markedValuation p) 0 := by
      simpa only [path0] using hendpoint

/-- The pushed-forward endpoint has no support outside the guarded candidate
set. -/
theorem bankPaperCanonicalActualP87EndpointSelector_eq_zero_of_not_mem
    {Head Band : Type*} [Fintype Head] [DecidableEq Head]
    [Fintype Band] [DecidableEq Band] [Nonempty Head]
    (B : BridgeData Head Band)
    (candidates : Finset Nat) (preSelector : Nat -> Real)
    (activeSeed : B.sampleData.Sample -> Real)
    (hvalues : forall m : B.sampleData.Sample,
      B.sampleData.value m ∈ candidates)
    (path : Real -> B.ParamSpace) {a : Nat} (ha : a ∉ candidates) :
    bankPaperCanonicalActualP87EndpointSelector
      B candidates preSelector activeSeed path a = 0 := by
  unfold bankPaperCanonicalActualP87EndpointSelector
    bankPaperProposition87EndpointSelector
  apply bankPaperProposition87SelectorAt_eq_zero_of_not_mem_support
  rw [bankPaperCanonicalActualP87SelectorSupport_eq_candidates
    B candidates hvalues]
  exact ha

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

/-- A prime above the smooth cutoff has zero valuation on every structured
active coordinate. -/
theorem StructuredSampleData.valuation_eq_zero_of_yNat_lt
    {Head : Type*} [Fintype Head]
    (D : StructuredSampleData Head) (m : D.Sample)
    {p : Nat} (hp : p.Prime) (hpy : yNat D.n < p) :
    valuation p (D.value m) = 0 := by
  unfold valuation
  have hnotDvd : ¬ p ∣ D.value m := by
    intro hpdvd
    have hpFactors : p ∈ (D.value m).primeFactors :=
      hp.mem_primeFactors hpdvd (Nat.ne_of_gt (D.value_pos m))
    have hpBelow := Nat.primeFactors_subset_of_mem_smoothNumbers
      (D.value_mem_smoothNumbers m) hpFactors
    have hpLt : p < yNat D.n + 1 := (Nat.mem_primesBelow.mp hpBelow).1
    omega
  exact_mod_cast Nat.factorization_eq_zero_of_not_dvd hnotDvd

/-- Hence every active marked moment at such a prime is zero at every bridge
parameter. -/
theorem BridgeData.paperMoment_markedValuation_eq_zero_of_yNat_lt
    {Head Band : Type*} [Fintype Head] [DecidableEq Head]
    [Fintype Band] [DecidableEq Band] [Nonempty Head]
    (B : BridgeData Head Band) (xi : B.ParamSpace)
    {p : Nat} (hp : p.Prime) (hpy : yNat B.sampleData.n < p) :
    B.paperMoment (B.markedValuation p) xi = 0 := by
  unfold BridgeData.paperMoment FiniteExponentialFamily.moment
  apply Finset.sum_eq_zero
  intro m _hm
  rw [show B.markedValuation p m = 0 by
    exact
      Erdos390.WholePaper.StructuredSampleData.valuation_eq_zero_of_yNat_lt
        B.sampleData m hp hpy]
  ring



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







/-- Therefore complete-rough-row integrality is preserved by the actual
Proposition 8.7 endpoint. -/
theorem bankPaperCanonicalActualP87EndpointSelector_rowIntegral
    {Head Band : Type*} [Fintype Head] [DecidableEq Head]
    [Fintype Band] [DecidableEq Band] [Nonempty Head]
    (B : BridgeData Head Band)
    {T : BarycentricTarget B.sampleData}
    (candidates : Finset Nat) (preSelector : Nat -> Real)
    (activeSeed : B.sampleData.Sample -> Real)
    (H : BankPaperCanonicalActualActiveMeasureConstructor
      B.sampleData T candidates preSelector activeSeed)
    (hseed : forall m, B.baseline.baseWeight m = activeSeed m)
    (path : Real -> B.ParamSpace)
    (hrow : BankPaperCanonicalSelectorRowIntegral
      B.sampleData.n candidates preSelector) :
    BankPaperCanonicalSelectorRowIntegral B.sampleData.n candidates
      (bankPaperCanonicalActualP87EndpointSelector
        B candidates preSelector activeSeed path) := by
  intro label hlabel
  obtain ⟨k, hk⟩ := hrow label hlabel
  refine ⟨k, ?_⟩
  rw [sum_bankPaperCanonicalActualP87EndpointSelector_row_eq_preSelector
    B candidates preSelector activeSeed H hseed path label]
  exact hk

/-! ## Prime support, exact bands, and the derived prefix ledger -/



/-- Exact target agreement outside `W < p <= y` is preserved by the
Proposition 8.7 endpoint.  Low-prime active moments are explicit P87
invariants; above `y` every active marked valuation is identically zero. -/
theorem bankPaperCanonicalActualP87EndpointSelector_deficitSupportedOnPrimeBand
    {Head Band : Type*} [Fintype Head] [DecidableEq Head]
    [Fintype Band] [DecidableEq Band] [Nonempty Head]
    (B : BridgeData Head Band)
    {c : Real} {depth : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (fixed candidates : Finset Nat) (preSelector : Nat -> Real)
    (activeSeed : B.sampleData.Sample -> Real)
    {T : BarycentricTarget B.sampleData}
    (H : BankPaperCanonicalActualActiveMeasureConstructor
      B.sampleData T candidates preSelector activeSeed)
    (hseed : forall m, B.baseline.baseWeight m = activeSeed m)
    (path : Real -> B.ParamSpace)
    (hpre : BankPaperCanonicalSelectorDeficitSupportedOnPrimeBand
      (W := B.sampleData.W) R certificate fixed candidates preSelector)
    (hsmall : forall p : Nat, p.Prime -> p <= B.sampleData.W ->
      B.paperMoment (B.markedValuation p) (path 1) =
        B.paperMoment (B.markedValuation p) 0) :
    BankPaperCanonicalSelectorDeficitSupportedOnPrimeBand
      (W := B.sampleData.W) R certificate fixed candidates
      (bankPaperCanonicalActualP87EndpointSelector
        B candidates preSelector activeSeed path) := by
  intro p hp hnotBand
  have hendpoint := bankPaperCanonicalActualEndpoint_deficit_eq_activeResidual
    B R certificate fixed candidates preSelector activeSeed
    (fun m => bankPaperCanonicalActiveSeed_value_mem_candidates H m) path p
  have hinitial := bankPaperCanonicalActualInitial_deficit_eq_activeResidual
    B R certificate fixed candidates preSelector activeSeed H hseed p
  have hpreZero := hpre p hp hnotBand
  by_cases hpW : p <= B.sampleData.W
  · calc
      bankPaperCanonicalSelectorValuationDeficit R certificate fixed candidates
          (bankPaperCanonicalActualP87EndpointSelector
            B candidates preSelector activeSeed path) p =
        bankPaperCanonicalActualActiveMarkedTarget B R certificate
            fixed candidates preSelector activeSeed p -
          B.paperMoment (B.markedValuation p) (path 1) := hendpoint
      _ = bankPaperCanonicalActualActiveMarkedTarget B R certificate
            fixed candidates preSelector activeSeed p -
          B.paperMoment (B.markedValuation p) 0 := by rw [hsmall p hp hpW]
      _ = bankPaperCanonicalSelectorValuationDeficit
            R certificate fixed candidates preSelector p := hinitial.symm
      _ = 0 := hpreZero
  · have hWp : B.sampleData.W < p := Nat.lt_of_not_ge hpW
    have hyp : yNat B.sampleData.n < p := by
      by_contra hnotY
      have hpY : p <= yNat B.sampleData.n := Nat.le_of_not_gt hnotY
      exact hnotBand (mem_primeBand.mpr ⟨hp, hWp, hpY⟩)
    have hzeroOne :=
      BridgeData.paperMoment_markedValuation_eq_zero_of_yNat_lt
        B (path 1) hp hyp
    have hzeroZero :=
      BridgeData.paperMoment_markedValuation_eq_zero_of_yNat_lt
        B 0 hp hyp
    calc
      bankPaperCanonicalSelectorValuationDeficit R certificate fixed candidates
          (bankPaperCanonicalActualP87EndpointSelector
            B candidates preSelector activeSeed path) p =
        bankPaperCanonicalActualActiveMarkedTarget B R certificate
            fixed candidates preSelector activeSeed p -
          B.paperMoment (B.markedValuation p) (path 1) := hendpoint
      _ = bankPaperCanonicalActualActiveMarkedTarget B R certificate
            fixed candidates preSelector activeSeed p -
          B.paperMoment (B.markedValuation p) 0 := by
        rw [hzeroOne, hzeroZero]
      _ = bankPaperCanonicalSelectorValuationDeficit
            R certificate fixed candidates preSelector p := hinitial.symm
      _ = 0 := hpreZero

/-- The exact P87 residual cancellation in every arithmetic prime band is
the exact band balance required by the canonical tangent interface. -/
theorem bankPaperCanonicalActualP87EndpointSelector_bandBalance
    {Head Band : Type*} [Fintype Head] [DecidableEq Head]
    [Fintype Band] [DecidableEq Band] [Nonempty Head]
    (B : BridgeData Head Band)
    {c : Real} {depth : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (fixed candidates : Finset Nat) (preSelector : Nat -> Real)
    (activeSeed : B.sampleData.Sample -> Real)
    (hvalues : forall m : B.sampleData.Sample,
      B.sampleData.value m ∈ candidates)
    (path : Real -> B.ParamSpace)
    (hbands : forall band : Band,
      B.markedBandResidual
        (bankPaperCanonicalActualActiveMarkedTarget B R certificate
          fixed candidates preSelector activeSeed) (path 1) band = 0) :
    forall band : Band,
      (∑ p : BankPaperCanonicalTangentPrime
          B.sampleData.n B.sampleData.W,
        if B.partition.band p = band then
          bankPaperCanonicalTangentResidual R certificate fixed candidates
            (bankPaperCanonicalActualP87EndpointSelector
              B candidates preSelector activeSeed path) p
        else 0) = 0 := by
  intro band
  rw [← Finset.sum_filter]
  change (∑ p ∈ B.partition.data.fiber band,
    bankPaperCanonicalTangentResidual R certificate fixed candidates
      (bankPaperCanonicalActualP87EndpointSelector
        B candidates preSelector activeSeed path) p) = 0
  calc
    _ = ∑ p ∈ B.partition.data.fiber band,
        (bankPaperCanonicalActualActiveMarkedTarget B R certificate
            fixed candidates preSelector activeSeed p.1 -
          B.paperMoment (B.markedValuation p.1) (path 1)) := by
      apply Finset.sum_congr rfl
      intro p _hp
      exact bankPaperCanonicalActualEndpoint_deficit_eq_activeResidual
        B R certificate fixed candidates preSelector activeSeed hvalues path p.1
    _ = 0 := hbands band

/-- Summing the exact partition-band equations gives the global prime-band
balance field of the rounded-selector tangent input. -/
theorem bankPaperCanonicalActualP87EndpointSelector_primeBandBalance
    {Head Band : Type*} [Fintype Head] [DecidableEq Head]
    [Fintype Band] [DecidableEq Band] [Nonempty Head]
    (B : BridgeData Head Band)
    {c : Real} {depth : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (fixed candidates : Finset Nat) (preSelector : Nat -> Real)
    (activeSeed : B.sampleData.Sample -> Real)
    (path : Real -> B.ParamSpace)
    (hbalance : forall band : Band,
      (∑ p : BankPaperCanonicalTangentPrime
          B.sampleData.n B.sampleData.W,
        if B.partition.band p = band then
          bankPaperCanonicalTangentResidual R certificate fixed candidates
            (bankPaperCanonicalActualP87EndpointSelector
              B candidates preSelector activeSeed path) p
        else 0) = 0) :
    BankPaperCanonicalPostRoundingPrimeBandBalance
      (W := B.sampleData.W) R certificate fixed candidates
      (bankPaperCanonicalActualP87EndpointSelector
        B candidates preSelector activeSeed path) := by
  let residual : BankPaperCanonicalTangentPrime
      B.sampleData.n B.sampleData.W -> Real := fun p =>
    bankPaperCanonicalTangentResidual R certificate fixed candidates
      (bankPaperCanonicalActualP87EndpointSelector
        B candidates preSelector activeSeed path) p
  have htotal : (∑ p : BankPaperCanonicalTangentPrime
      B.sampleData.n B.sampleData.W, residual p) = 0 := by
    rw [← Finset.sum_fiberwise Finset.univ B.partition.band residual]
    apply Finset.sum_eq_zero
    intro band _hband
    rw [Finset.sum_filter]
    simpa only [residual] using hbalance band
  unfold BankPaperCanonicalPostRoundingPrimeBandBalance
  calc
    (∑ p ∈ primeBand B.sampleData.n B.sampleData.W,
      bankPaperCanonicalSelectorValuationDeficit R certificate fixed candidates
        (bankPaperCanonicalActualP87EndpointSelector
          B candidates preSelector activeSeed path) p) =
      ∑ p : BankPaperCanonicalTangentPrime
          B.sampleData.n B.sampleData.W, residual p := by
        simpa only [Finset.univ_eq_attach, residual,
          bankPaperCanonicalTangentResidual] using
          (Finset.sum_attach (primeBand B.sampleData.n B.sampleData.W)
            (fun p => bankPaperCanonicalSelectorValuationDeficit
              R certificate fixed candidates
                (bankPaperCanonicalActualP87EndpointSelector
                  B candidates preSelector activeSeed path) p)).symm
    _ = 0 := htotal

/-- The P87 primewise rate is exactly the canonical tangent residual rate
for the pushed-forward guarded endpoint. -/
theorem bankPaperCanonicalActualP87EndpointSelector_pointwise
    {Head Band : Type*} [Fintype Head] [DecidableEq Head]
    [Fintype Band] [DecidableEq Band] [Nonempty Head]
    (B : BridgeData Head Band)
    {c : Real} {depth : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (fixed candidates : Finset Nat) (preSelector : Nat -> Real)
    (activeSeed : B.sampleData.Sample -> Real)
    (hvalues : forall m : B.sampleData.Sample,
      B.sampleData.value m ∈ candidates)
    (path : Real -> B.ParamSpace) (N Cpost : Real)
    (hmarked : ∀ p ∈ primeBand B.sampleData.n B.sampleData.W,
      abs (bankPaperCanonicalActualActiveMarkedTarget B R certificate
          fixed candidates preSelector activeSeed p -
        B.paperMoment (B.markedValuation p) (path 1)) <=
          Cpost * N / ((p : Real) * B.L)) :
    forall p : BankPaperCanonicalTangentPrime
        B.sampleData.n B.sampleData.W,
      abs (bankPaperCanonicalTangentResidual R certificate fixed candidates
        (bankPaperCanonicalActualP87EndpointSelector
          B candidates preSelector activeSeed path) p) <=
        bankPaperCanonicalActualP87PointwiseUpper B N Cpost p := by
  intro p
  rw [bankPaperCanonicalTangentResidual,
    bankPaperCanonicalActualEndpoint_deficit_eq_activeResidual
      B R certificate fixed candidates preSelector activeSeed hvalues path p.1]
  exact hmarked p.1 p.2

/-! ## Complete endpoint handoff -/



/-! ## Direct coupling to the guarded continuation -/



end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankPaperCanonicalActualActiveMeasureConstruction -/
section


/-!
# Constructing the actual active measure and isolating its irreducible fit

The paper's baseline realization has two logically different parts.

* Once a normalized barycentric target and its literal active mass `q_n`
  are fixed, the active coordinates are forced:

  `z_m^0 = q_n * T.baseline.baseWeight m`.

  Their sum is definitionally finite and is proved below to be exactly
  `q_n`.  No analytic or selector input is needed for this part.

* For a *previously fixed* guarded pre-selector, one must still know that
  the pre-selector carries this active mass at every active numerical
  coordinate.  Under the already available head-pattern separation and
  candidate feasibility, this reduces exactly to the coordinatewise
  inequality

  `q_n * T.baseline.baseWeight m <= preSelector (D.value m)`.

The latter is named `BankPaperCanonicalActualCoordinateFit`.  It is the
irreducible coupling absent from `BankPaperCanonicalGuardedSectionNineContinuation`:
that continuation records feasibility, row sums, and prime residuals, but
no pointwise relation between its selector and the later active baseline.

The module also gives a completely unconditional self-selector
construction, proves the guarded-support part from the existing geometry,
and shows that the older guarded bridge selector constructor supplies the
coordinate fit whenever it is instantiated with the literal active-mass
baseline.
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

/-! ## The forced finite active seed -/



/-- A nonnegative literal mass gives a nonnegative active seed. -/
theorem bankPaperCanonicalScaledActiveSeed_nonneg
    {Head : Type*} [Fintype Head]
    {D : StructuredSampleData Head} (T : BarycentricTarget D)
    {q : Real} (hq : 0 <= q) (m : D.Sample) :
    0 <= bankPaperCanonicalScaledActiveSeed T q m := by
  exact mul_nonneg hq (T.baseline.baseWeight_nonneg m)



/-- The ambient push-forward of a nonnegative scaled seed is nonnegative,
without assuming an active-measure constructor. -/
theorem bankPaperCanonicalActiveSeedAmbientWeight_scaled_nonneg
    {Head : Type*} [Fintype Head]
    {D : StructuredSampleData Head} (T : BarycentricTarget D)
    {q : Real} (hq : 0 <= q) (a : Nat) :
    0 <= bankPaperCanonicalActiveSeedAmbientWeight D
      (bankPaperCanonicalScaledActiveSeed T q) a := by
  unfold bankPaperCanonicalActiveSeedAmbientWeight
  apply Finset.sum_nonneg
  intro m _hm
  split_ifs
  · exact bankPaperCanonicalScaledActiveSeed_nonneg T hq m
  · exact le_rfl



/-! ## Canonical finite support and a self-selector witness -/











/-! ## Exact minimization for a fixed guarded pre-selector -/



/-- For the canonical scaled seed, the original constructor is equivalent
to `q >= 1` and the finite placement condition.  In particular its seed
equation is not an independent missing input. -/
theorem bankPaperCanonicalActualActiveMeasureConstructor_scaled_iff
    {Head : Type*} [Fintype Head] [Nonempty Head]
    (D : StructuredSampleData Head) (T : BarycentricTarget D)
    (candidates : Finset Nat) (preSelector : Nat -> Real)
    (q : Real) :
    BankPaperCanonicalActualActiveMeasureConstructor D T candidates
        preSelector (bankPaperCanonicalScaledActiveSeed T q) ↔
      1 <= q ∧
        BankPaperCanonicalActualActivePlacement
          D T candidates preSelector q := by
  unfold BankPaperCanonicalActualActiveMeasureConstructor
    BankPaperCanonicalActualActivePlacement
  rw [bankPaperCanonicalLiteralActiveMass_scaledActiveSeed]
  constructor
  · intro H
    exact ⟨H.1, H.2.2.1, H.2.2.2⟩
  · intro H
    exact ⟨H.1, (fun _m => rfl), H.2.1, H.2.2⟩





/-- Candidate support, nonnegativity of the pre-selector, and coordinate
fit imply full ambient placement.  Coordinates outside the active image
carry zero active mass; head-pattern separation handles the occupied
coordinates without a collision loss. -/
theorem bankPaperCanonicalActualActivePlacement_of_coordinateFit
    {Head : Type*} [Fintype Head]
    (D : StructuredSampleData Head) (T : BarycentricTarget D)
    (candidates : Finset Nat) (preSelector : Nat -> Real)
    (q : Real) (hsep : D.HeadPatternsSeparated)
    (hvalues : ∀ m : D.Sample, D.value m ∈ candidates)
    (hselectorNonneg : ∀ a ∈ candidates, 0 <= preSelector a)
    (hfit : BankPaperCanonicalActualCoordinateFit D T preSelector q) :
    BankPaperCanonicalActualActivePlacement
      D T candidates preSelector q := by
  refine ⟨hvalues, ?_⟩
  intro a ha
  by_cases hactive : ∃ m : D.Sample, D.value m = a
  · rcases hactive with ⟨m, rfl⟩
    rw [bankPaperCanonicalActiveSeedAmbientWeight_scaled_eq_of_value
      D T q hsep m]
    exact hfit m
  · have hzero : bankPaperCanonicalActiveSeedAmbientWeight D
        (bankPaperCanonicalScaledActiveSeed T q) a = 0 := by
      apply bankPaperCanonicalActiveSeedAmbientWeight_eq_zero_of_not_value
      intro m hma
      exact hactive ⟨m, hma⟩
    rw [hzero]
    exact hselectorNonneg a ha

/-- Under the fixed structural/feasibility facts, full placement is
equivalent to coordinate fit. -/
theorem bankPaperCanonicalActualActivePlacement_iff_coordinateFit
    {Head : Type*} [Fintype Head]
    (D : StructuredSampleData Head) (T : BarycentricTarget D)
    (candidates : Finset Nat) (preSelector : Nat -> Real)
    (q : Real) (hsep : D.HeadPatternsSeparated)
    (hvalues : ∀ m : D.Sample, D.value m ∈ candidates)
    (hselectorNonneg : ∀ a ∈ candidates, 0 <= preSelector a) :
    BankPaperCanonicalActualActivePlacement D T candidates preSelector q ↔
      BankPaperCanonicalActualCoordinateFit D T preSelector q := by
  constructor
  · intro H m
    rw [← bankPaperCanonicalActiveSeedAmbientWeight_scaled_eq_of_value
      D T q hsep m]
    exact H.2 (D.value m) (H.1 m)
  · exact bankPaperCanonicalActualActivePlacement_of_coordinateFit
      D T candidates preSelector q hsep hvalues hselectorNonneg

/-- Consequently, once guarded support and selector nonnegativity are
available, the original active-measure constructor is *exactly* `q >= 1`
plus the pointwise coordinate fit. -/
theorem bankPaperCanonicalActualActiveMeasureConstructor_iff_coordinateFit
    {Head : Type*} [Fintype Head] [Nonempty Head]
    (D : StructuredSampleData Head) (T : BarycentricTarget D)
    (candidates : Finset Nat) (preSelector : Nat -> Real)
    (q : Real) (hsep : D.HeadPatternsSeparated)
    (hvalues : ∀ m : D.Sample, D.value m ∈ candidates)
    (hselectorNonneg : ∀ a ∈ candidates, 0 <= preSelector a) :
    BankPaperCanonicalActualActiveMeasureConstructor D T candidates
        preSelector (bankPaperCanonicalScaledActiveSeed T q) ↔
      1 <= q ∧
        BankPaperCanonicalActualCoordinateFit D T preSelector q := by
  rw [bankPaperCanonicalActualActiveMeasureConstructor_scaled_iff]
  constructor
  · intro H
    exact ⟨H.1,
      (bankPaperCanonicalActualActivePlacement_iff_coordinateFit
        D T candidates preSelector q hsep hvalues hselectorNonneg).mp H.2⟩
  · intro H
    exact ⟨H.1,
      (bankPaperCanonicalActualActivePlacement_iff_coordinateFit
        D T candidates preSelector q hsep hvalues hselectorNonneg).mpr H.2⟩

/-- Direct constructor from the irreducible coordinate fit. -/
theorem bankPaperCanonicalActualActiveMeasureConstructor_of_coordinateFit
    {Head : Type*} [Fintype Head] [Nonempty Head]
    (D : StructuredSampleData Head) (T : BarycentricTarget D)
    (candidates : Finset Nat) (preSelector : Nat -> Real)
    (q : Real) (hq : 1 <= q) (hsep : D.HeadPatternsSeparated)
    (hvalues : ∀ m : D.Sample, D.value m ∈ candidates)
    (hselectorNonneg : ∀ a ∈ candidates, 0 <= preSelector a)
    (hfit : BankPaperCanonicalActualCoordinateFit D T preSelector q) :
    BankPaperCanonicalActualActiveMeasureConstructor D T candidates
      preSelector (bankPaperCanonicalScaledActiveSeed T q) := by
  exact
    (bankPaperCanonicalActualActiveMeasureConstructor_iff_coordinateFit
      D T candidates preSelector q hsep hvalues hselectorNonneg).mpr
        ⟨hq, hfit⟩



/-! ## Guarded geometry and the older bridge-selector constructor -/

/-- Pointwise avoidance of the full numerical guard and interval geometry
already prove the support part of the actual active-measure construction. -/
theorem bankPaperCanonicalStructuredValue_mem_guardedCandidates
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
        R.roughCanonicalGuardSet certificate deltaStar)
    (m : B.sampleData.Sample) :
    B.sampleData.value m ∈
      R.roughCanonicalGuardedCandidateSet certificate deltaStar K := by
  apply bankPaperCanonicalBridgeActiveValues_subset_guardedCandidates
    B R certificate deltaStar hKh hlower hupper hnotGuard
  exact mem_bankPaperCanonicalBridgeActiveValues.mpr ⟨m, rfl⟩

/-- On the literal guarded candidate set, all structural fields are now
derived; only `q >= 1`, candidate nonnegativity, and coordinate fit remain. -/
theorem bankPaperCanonicalActualActiveMeasureConstructor_guarded_of_coordinateFit
    {Head Band : Type*} [Fintype Head] [DecidableEq Head]
    [Fintype Band] [DecidableEq Band] [Nonempty Head]
    (B : BridgeData Head Band)
    {c : Real} {depth K : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (deltaStar : Real) (T : BarycentricTarget B.sampleData)
    (preSelector : Nat -> Real) (q : Real) (hq : 1 <= q)
    (hsep : B.sampleData.HeadPatternsSeparated)
    (hKh : K * upperTailLength c B.sampleData.n <= B.sampleData.n)
    (hlower : forall m : B.sampleData.Sample,
      B.sampleData.n < B.sampleData.value m)
    (hupper : forall m : B.sampleData.Sample,
      B.sampleData.value m <= 2 * B.sampleData.n)
    (hnotGuard : forall m : B.sampleData.Sample,
      B.sampleData.value m ∉
        R.roughCanonicalGuardSet certificate deltaStar)
    (hselectorNonneg : ∀ a ∈
      R.roughCanonicalGuardedCandidateSet certificate deltaStar K,
      0 <= preSelector a)
    (hfit : BankPaperCanonicalActualCoordinateFit
      B.sampleData T preSelector q) :
    BankPaperCanonicalActualActiveMeasureConstructor B.sampleData T
      (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
      preSelector (bankPaperCanonicalScaledActiveSeed T q) := by
  apply bankPaperCanonicalActualActiveMeasureConstructor_of_coordinateFit
    B.sampleData T
      (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
      preSelector q hq hsep
  · intro m
    exact bankPaperCanonicalStructuredValue_mem_guardedCandidates
      B R certificate deltaStar hKh hlower hupper hnotGuard m
  · exact hselectorNonneg
  · exact hfit



/-! ## The literal mass already stored by the paper head simplex -/





end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankPaperCanonicalProposition87EndpointSlack -/
section


/-!
# Proposition 8.7 endpoint slack on the guarded smooth row

The endpoint emitted by Proposition 8.7 is the literal sum of a frozen
ambient layer and an active exponential-family layer.  This file keeps that
overlap visible and proves the quantitative smooth-row part of the tangent
slack argument.

The active upper bound is not an assumption: it follows from the effective
box in `IsPaperProposition87Path`, the baseline `Cactive / L` ledger, and the
proved density-ratio estimate.  The sole construction datum not currently
present in the guarded-selector development is named
`BankPaperCanonicalGuardedSmoothProtectedWindow`: on every guarded smooth
broad coordinate the actual frozen ambient layer contains the protected
floor and is itself `O(1 / L)`.  This is exactly the finite realization of
the protected summand in the paper's smooth additive decomposition and
tangent endpoint-slack argument;
it does not assume endpoint slack or any tangent conclusion.

After that one window is supplied, the endpoint selector has the required
strict upper reserve, the existing nonsmooth constant-pool correction joins
it to form `BankPaperCanonicalGuardedEndpointSlackConstruction`, and the
existing clean-list candidate adapter applies without any further premise.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.PaperBridgeFit
open Erdos390.Full.PaperGuardCensus
open Filter

noncomputable section

/-! ## The one missing finite protected-layer estimate -/



/-- Push-forward through the identity-valued subtype index has exactly one
tag above each member of the finite support.  This is the finite adapter used
by the actual-data connector, whose frozen index is the subtype of guarded
candidates. -/
theorem frozenAmbientWeight_subtype_apply
    (support : Finset Nat) (weight : ↥support -> Real)
    {x : Nat} (hx : x ∈ support) :
    BridgeData.frozenAmbientWeight
        (fun f : ↥support => f.1) weight x = weight ⟨x, hx⟩ := by
  classical
  unfold BridgeData.frozenAmbientWeight
  rw [Finset.sum_eq_single (⟨x, hx⟩ : ↥support)]
  · simp
  · intro f hf hne
    rw [if_neg]
    intro hvalue
    apply hne
    apply Subtype.ext
    exact hvalue
  · intro hnot
    exact (hnot (Finset.mem_univ _)).elim



/-- For an identity-valued guarded-candidate frozen layer, it is enough to
verify the protected window directly on its tagged coordinate weights.  No
injectivity or support conclusion remains to be supplied downstream. -/
theorem bankPaperCanonicalGuardedSmoothProtectedWindow_of_subtypeBounds
    {Head Band : Type*} [Fintype Head] [DecidableEq Head]
    [Fintype Band] [DecidableEq Band] [Nonempty Head]
    (B : BridgeData Head Band)
    {c : Real} {depth K : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (deltaStar : Real) (candidates : Finset Nat)
    (fixedWeight : ↥candidates -> Real) (sigma Cfixed : Real)
    (hpool : R.roughCanonicalGuardedBroadCorrectionPool certificate
      deltaStar B.sampleData.W K 1 ⊆ candidates)
    (hweight : forall x
      (hx : x ∈ R.roughCanonicalGuardedBroadCorrectionPool certificate
        deltaStar B.sampleData.W K 1),
      sigma / B.L <= fixedWeight ⟨x, hpool hx⟩ ∧
        fixedWeight ⟨x, hpool hx⟩ <= Cfixed / B.L) :
    BankPaperCanonicalGuardedSmoothProtectedWindow (K := K)
      B R certificate deltaStar (fun f : ↥candidates => f.1)
        fixedWeight sigma Cfixed := by
  unfold BankPaperCanonicalGuardedSmoothProtectedWindow
  intro x hx
  rw [frozenAmbientWeight_subtype_apply candidates fixedWeight (hpool hx)]
  exact hweight x hx

/-- Concrete subtraction form used by the actual-paper-data connector.  If
`activeSeedAmbient` is nonnegative, the pre-selector has its broad
`Cfixed / L` upper bound, and it dominates the seed by the protected amount
`sigma / L`, then the frozen remainder
`preSelector - activeSeedAmbient` satisfies the exact protected window.

Thus subtraction and finite push-forward introduce no additional gap: the
only lower estimate left to the rough/smooth realization is the displayed
protected reserve before subtraction. -/
theorem bankPaperCanonicalGuardedSmoothProtectedWindow_of_subtypeRemainder
    {Head Band : Type*} [Fintype Head] [DecidableEq Head]
    [Fintype Band] [DecidableEq Band] [Nonempty Head]
    (B : BridgeData Head Band)
    {c : Real} {depth K : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (deltaStar : Real) (candidates : Finset Nat)
    (preSelector activeSeedAmbient : Nat -> Real)
    (sigma Cfixed : Real)
    (hpool : R.roughCanonicalGuardedBroadCorrectionPool certificate
      deltaStar B.sampleData.W K 1 ⊆ candidates)
    (hactiveNonneg : ∀ x ∈
      R.roughCanonicalGuardedBroadCorrectionPool certificate
        deltaStar B.sampleData.W K 1,
      0 <= activeSeedAmbient x)
    (hprotectedReserve : ∀ x ∈
      R.roughCanonicalGuardedBroadCorrectionPool certificate
        deltaStar B.sampleData.W K 1,
      sigma / B.L + activeSeedAmbient x <= preSelector x)
    (hpreUpper : ∀ x ∈
      R.roughCanonicalGuardedBroadCorrectionPool certificate
        deltaStar B.sampleData.W K 1,
      preSelector x <= Cfixed / B.L) :
    BankPaperCanonicalGuardedSmoothProtectedWindow (K := K)
      B R certificate deltaStar (fun f : ↥candidates => f.1)
        (fun f => preSelector f.1 - activeSeedAmbient f.1)
        sigma Cfixed := by
  apply bankPaperCanonicalGuardedSmoothProtectedWindow_of_subtypeBounds
    B R certificate deltaStar candidates
      (fun f => preSelector f.1 - activeSeedAmbient f.1)
      sigma Cfixed hpool
  intro x hx
  constructor <;> dsimp
  · linarith [hprotectedReserve x hx]
  · linarith [hactiveNonneg x hx, hpreUpper x hx]

/-! ## Quantitative active-coordinate bound at the actual P87 endpoint -/

/-- A pointwise effective-score bound and the baseline coordinate ledger
give an ambient active upper bound at every natural coordinate.  At a sample
coordinate this is the proved P87 density-ratio estimate; away from the
sample support the ambient active weight is exactly zero. -/
theorem bankPaperProposition87AmbientActiveWeight_le_of_effectiveScoreBound
    {Head Band : Type*} [Fintype Head] [DecidableEq Head]
    [Fintype Band] [DecidableEq Band] [Nonempty Head]
    (B : BridgeData Head Band)
    (hsep : B.sampleData.HeadPatternsSeparated)
    (xi : B.ParamSpace) (Rbound Cactive : Real)
    (hscore : forall m : B.sampleData.Sample,
      |B.vectorFamily.scalarFamily.score m xi / B.L| <= Rbound)
    (hCactive : 0 <= Cactive)
    (hactive : forall m : B.sampleData.Sample,
      B.baseline.baseWeight m <= Cactive / B.L) :
    forall x : Nat,
      B.ambientActiveWeight xi x <=
        Real.exp (2 * Rbound) * Cactive / B.L := by
  intro x
  by_cases hx : exists m : B.sampleData.Sample,
      B.sampleData.value m = x
  · obtain ⟨m, rfl⟩ := hx
    rw [B.ambientActiveWeight_eq_of_value hsep]
    calc
      B.activeCoordinateWeight xi m <=
          Real.exp (2 * Rbound) * B.baseline.baseWeight m :=
        B.activeCoordinateWeight_le_exp_twoEffectiveBound_mul_baseline
          xi Rbound hscore m
      _ <= Real.exp (2 * Rbound) * (Cactive / B.L) :=
        mul_le_mul_of_nonneg_left (hactive m) (Real.exp_pos _).le
      _ = Real.exp (2 * Rbound) * Cactive / B.L := by ring
  · rw [B.ambientActiveWeight_eq_zero_of_not_value xi x
      (fun m hm => hx ⟨m, hm⟩)]
    exact div_nonneg
      (mul_nonneg (Real.exp_pos _).le hCactive) B.L_pos.le

/-- The preceding ambient bound specialized to the literal endpoint of an
`IsPaperProposition87Path`.  Its effective-score radius is obtained from the
path's proved `paperEffectiveSize <= 3 * a` clause; no endpoint estimate is
added as a premise. -/
theorem bankPaperProposition87AmbientActiveWeight_endpoint_le_of_path
    {Head Band Fixed : Type*}
    [Fintype Head] [DecidableEq Head]
    [Fintype Band] [DecidableEq Band] [Fintype Fixed]
    [Nonempty Head]
    (B : BridgeData Head Band)
    (Delta : Band -> Real) (radius : NNReal)
    (markedTarget : Nat -> Real) (N Cpost : Real)
    (fixedValue : Fixed -> Nat) (fixedWeight : Fixed -> Real)
    (quota : Int) (path : Real -> B.ParamSpace)
    (H : B.IsPaperProposition87Path Delta radius markedTarget N Cpost
      fixedValue fixedWeight quota path)
    (C Cactive : Real) (hC : 1 <= C)
    (hW : 1 < B.sampleData.W)
    (hhi : forall sign,
      B.sampleData.hi sign <= physicalBound C B.sampleData.n)
    (hsep : B.sampleData.HeadPatternsSeparated)
    (hCactive : 0 <= Cactive)
    (hactive : forall m : B.sampleData.Sample,
      B.baseline.baseWeight m <= Cactive / B.L) :
    forall x : Nat,
      B.ambientActiveWeight (path 1) x <=
        Real.exp (2 *
          ((Erdos390.Full.PaperStatisticNorm.valuationLogCoefficient
              C B.sampleData.W +
            B.nuisanceStatisticCoefficient C) *
              (3 * (radius : Real)))) * Cactive / B.L := by
  have hsize : ∀ t ∈ Set.Icc (0 : Real) 1,
      B.paperEffectiveSize (path t) <= 3 * (radius : Real) :=
    H.2.2.1
  have hsizeOne : B.paperEffectiveSize (path 1) <=
      3 * (radius : Real) := hsize 1 (by constructor <;> norm_num)
  have hscore := B.effectiveScoreBound_of_paperEffectiveSize
    hC hW hhi (path 1) hsizeOne
  exact bankPaperProposition87AmbientActiveWeight_le_of_effectiveScoreBound
    B hsep (path 1)
      ((Erdos390.Full.PaperStatisticNorm.valuationLogCoefficient
          C B.sampleData.W +
        B.nuisanceStatisticCoefficient C) * (3 * (radius : Real)))
      Cactive hscore hCactive hactive



/-- If the active structured sample lies in the guarded smooth row, its
ambient active layer vanishes on every guarded nonsmooth broad coordinate.
This is the support fact which lets the frozen nonsmooth selector pass
through the P87 endpoint unchanged. -/
theorem bankPaperProposition87AmbientActiveWeight_eq_zero_on_nonsmoothPool
    {Head Band : Type*} [Fintype Head] [DecidableEq Head]
    [Fintype Band] [DecidableEq Band] [Nonempty Head]
    (B : BridgeData Head Band)
    {c : Real} {depth K : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (deltaStar : Real) (path : Real -> B.ParamSpace)
    (hactiveSmooth : forall m : B.sampleData.Sample,
      B.sampleData.value m ∈
        R.roughCanonicalGuardedRow certificate deltaStar K 1)
    {label x : Nat} (hlabel : label ≠ 1)
    (hx : x ∈ R.roughCanonicalGuardedBroadCorrectionPool certificate
      deltaStar B.sampleData.W K label) :
    B.ambientActiveWeight (path 1) x = 0 := by
  apply B.ambientActiveWeight_eq_zero_of_not_value
  intro m hm
  have hxSmooth : x ∈
      R.roughCanonicalGuardedRow certificate deltaStar K 1 := by
    simpa only [hm] using hactiveSmooth m
  have hxLabel : x ∈
      R.roughCanonicalGuardedRow certificate deltaStar K label :=
    R.roughCanonicalGuardedBroadCorrectionPool_subset_guardedRow
      certificate deltaStar B.sampleData.W K label hx
  have hsmoothEq := (mem_completeRoughRowFiber.mp hxSmooth).2
  have hlabelEq := (mem_completeRoughRowFiber.mp hxLabel).2
  exact hlabel (hlabelEq.symm.trans hsmoothEq)

/-! ## Smooth protected floor and strict upper reserve -/

/-- The actual P87 endpoint selector has the paper's two-sided tangent slack
on every guarded smooth broad coordinate.

The witnesses are not artificial copies: `protected` is the literal frozen
ambient weight and `active` is the literal endpoint active weight.  Thus the
proof remains valid when the two tagged layers overlap at a natural-number
coordinate. -/
theorem exists_bankPaperProposition87EndpointSelector_smoothSlackLayers
    {Head Band Fixed : Type*}
    [Fintype Head] [DecidableEq Head]
    [Fintype Band] [DecidableEq Band] [Fintype Fixed]
    [Nonempty Head]
    (B : BridgeData Head Band)
    {c : Real} {depth K : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (deltaStar : Real)
    (Delta : Band -> Real) (radius : NNReal)
    (markedTarget : Nat -> Real) (N Cpost : Real)
    (fixedValue : Fixed -> Nat) (fixedWeight : Fixed -> Real)
    (quota : Int) (path : Real -> B.ParamSpace)
    (Hpath : B.IsPaperProposition87Path Delta radius markedTarget N Cpost
      fixedValue fixedWeight quota path)
    (C sigma Cfixed Cactive : Real)
    (hC : 1 <= C) (hW : 1 < B.sampleData.W)
    (hhi : forall sign,
      B.sampleData.hi sign <= physicalBound C B.sampleData.n)
    (hsep : B.sampleData.HeadPatternsSeparated)
    (hCactive : 0 <= Cactive)
    (hactive : forall m : B.sampleData.Sample,
      B.baseline.baseWeight m <= Cactive / B.L)
    (hprotected : BankPaperCanonicalGuardedSmoothProtectedWindow (K := K)
      B R certificate deltaStar fixedValue fixedWeight sigma Cfixed)
    (hlarge : Cfixed +
        Real.exp (2 *
          ((Erdos390.Full.PaperStatisticNorm.valuationLogCoefficient
              C B.sampleData.W +
            B.nuisanceStatisticCoefficient C) *
              (3 * (radius : Real)))) * Cactive + sigma <= B.L) :
    ∃ protectedPart active : Nat -> Real,
      ∀ x ∈ R.roughCanonicalGuardedBroadCorrectionPool certificate
          deltaStar B.sampleData.W K 1,
        bankPaperProposition87EndpointSelector
              B fixedValue fixedWeight path x =
            protectedPart x + active x ∧
          sigma / B.L <= protectedPart x ∧
          0 <= active x ∧
          protectedPart x + active x <= 1 - sigma / B.L := by
  let protectedPart : Nat -> Real :=
    BridgeData.frozenAmbientWeight fixedValue fixedWeight
  let active : Nat -> Real := B.ambientActiveWeight (path 1)
  refine ⟨protectedPart, active, ?_⟩
  intro x hx
  have hprotectedX := hprotected x hx
  have hactiveNonneg : 0 <= active x := by
    exact B.ambientActiveWeight_nonneg (path 1) x
  have hactiveUpper : active x <=
      Real.exp (2 *
        ((Erdos390.Full.PaperStatisticNorm.valuationLogCoefficient
            C B.sampleData.W +
          B.nuisanceStatisticCoefficient C) *
            (3 * (radius : Real)))) * Cactive / B.L := by
    exact bankPaperProposition87AmbientActiveWeight_endpoint_le_of_path
      B Delta radius markedTarget N Cpost fixedValue fixedWeight quota path
        Hpath C Cactive hC hW hhi hsep hCactive hactive x
  have hcoefficient : Cfixed +
        Real.exp (2 *
          ((Erdos390.Full.PaperStatisticNorm.valuationLogCoefficient
              C B.sampleData.W +
            B.nuisanceStatisticCoefficient C) *
              (3 * (radius : Real)))) * Cactive <= B.L - sigma := by
    linarith
  have hsum : protectedPart x + active x <=
      (Cfixed +
        Real.exp (2 *
          ((Erdos390.Full.PaperStatisticNorm.valuationLogCoefficient
              C B.sampleData.W +
            B.nuisanceStatisticCoefficient C) *
              (3 * (radius : Real)))) * Cactive) / B.L := by
    calc
      protectedPart x + active x <=
          Cfixed / B.L +
            Real.exp (2 *
              ((Erdos390.Full.PaperStatisticNorm.valuationLogCoefficient
                  C B.sampleData.W +
                B.nuisanceStatisticCoefficient C) *
                  (3 * (radius : Real)))) * Cactive / B.L :=
        add_le_add hprotectedX.2 hactiveUpper
      _ = (Cfixed +
          Real.exp (2 *
            ((Erdos390.Full.PaperStatisticNorm.valuationLogCoefficient
                C B.sampleData.W +
              B.nuisanceStatisticCoefficient C) *
                (3 * (radius : Real)))) * Cactive) / B.L := by ring
  have hreserve : (Cfixed +
        Real.exp (2 *
          ((Erdos390.Full.PaperStatisticNorm.valuationLogCoefficient
              C B.sampleData.W +
            B.nuisanceStatisticCoefficient C) *
              (3 * (radius : Real)))) * Cactive) / B.L <=
      1 - sigma / B.L := by
    calc
      (Cfixed +
          Real.exp (2 *
            ((Erdos390.Full.PaperStatisticNorm.valuationLogCoefficient
                C B.sampleData.W +
              B.nuisanceStatisticCoefficient C) *
                (3 * (radius : Real)))) * Cactive) / B.L <=
          (B.L - sigma) / B.L :=
        div_le_div_of_nonneg_right hcoefficient B.L_pos.le
      _ = 1 - sigma / B.L := by
        field_simp [ne_of_gt B.L_pos]
  refine ⟨?_, hprotectedX.1, hactiveNonneg, hsum.trans hreserve⟩
  rfl

namespace BankPaperRealization

/-! ## Join to the already proved nonsmooth correction -/

/-- The P87 smooth endpoint layers and the already existing nonsmooth
constant-pool output form the exact guarded endpoint-slack construction.
The active-support premise and frozen-row identity show that P87 changes no
nonsmooth coordinate; the remaining nonsmooth hypotheses are only the two
already isolated correction-density bounds.  The smooth half is proved above
from the protected window and the P87 path. -/
theorem guardedEndpointSlackConstruction_of_proposition87EndpointSelector
    {Head Band Fixed : Type*}
    [Fintype Head] [DecidableEq Head]
    [Fintype Band] [DecidableEq Band] [Fintype Fixed]
    [Nonempty Head]
    (B : BridgeData Head Band)
    {c : Real} {depth K : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (deltaStar alpha beta : Real)
    (Delta : Band -> Real) (radius : NNReal)
    (markedTarget : Nat -> Real) (N Cpost : Real)
    (fixedValue : Fixed -> Nat) (fixedWeight : Fixed -> Real)
    (quota : Int) (path : Real -> B.ParamSpace)
    (Hpath : B.IsPaperProposition87Path Delta radius markedTarget N Cpost
      fixedValue fixedWeight quota path)
    (C sigma Cfixed Cactive : Real)
    (hC : 1 <= C) (hW : 1 < B.sampleData.W)
    (hhi : forall sign,
      B.sampleData.hi sign <= physicalBound C B.sampleData.n)
    (hsep : B.sampleData.HeadPatternsSeparated)
    (hCactive : 0 <= Cactive)
    (hactive : forall m : B.sampleData.Sample,
      B.baseline.baseWeight m <= Cactive / B.L)
    (hprotected : BankPaperCanonicalGuardedSmoothProtectedWindow (K := K)
      B R certificate deltaStar fixedValue fixedWeight sigma Cfixed)
    (hlarge : Cfixed +
        Real.exp (2 *
          ((Erdos390.Full.PaperStatisticNorm.valuationLogCoefficient
              C B.sampleData.W +
            B.nuisanceStatisticCoefficient C) *
              (3 * (radius : Real)))) * Cactive + sigma <= B.L)
    (hactiveSmooth : forall m : B.sampleData.Sample,
      B.sampleData.value m ∈
        R.roughCanonicalGuardedRow certificate deltaStar K 1)
    (hnonsmoothBounds : forall label,
      RoughCanonicalActiveNonexceptionalLabel B.sampleData.n deltaStar label ->
        sigma / B.L +
            |R.roughCanonicalGuardedPostchargeCorrectionDensity certificate
              deltaStar B.sampleData.W K label alpha beta B.L| <=
          beta / B.L ∧
        beta / B.L +
            |R.roughCanonicalGuardedPostchargeCorrectionDensity certificate
              deltaStar B.sampleData.W K label alpha beta B.L| <=
          1 - sigma / B.L)
    (hfrozenNonsmooth : forall label,
      RoughCanonicalActiveNonexceptionalLabel B.sampleData.n deltaStar label ->
        ∀ x ∈ R.roughCanonicalGuardedBroadCorrectionPool certificate
            deltaStar B.sampleData.W K label,
          BridgeData.frozenAmbientWeight fixedValue fixedWeight x =
            R.roughCanonicalGuardedPostchargeRowCorrectedWeight certificate
              deltaStar B.sampleData.W K label alpha beta B.L x) :
    R.BankPaperCanonicalGuardedEndpointSlackConstruction certificate
      deltaStar B.sampleData.W K alpha beta B.L sigma
      (bankPaperProposition87EndpointSelector
        B fixedValue fixedWeight path) := by
  constructor
  · exact exists_bankPaperProposition87EndpointSelector_smoothSlackLayers
      B R certificate deltaStar Delta radius markedTarget N Cpost
        fixedValue fixedWeight quota path Hpath C sigma Cfixed Cactive
        hC hW hhi hsep hCactive hactive hprotected hlarge
  · intro label hlabel
    obtain ⟨hfloor, hceiling⟩ := hnonsmoothBounds label hlabel
    refine ⟨hfloor, hceiling, ?_⟩
    intro x hx
    change BridgeData.frozenAmbientWeight fixedValue fixedWeight x +
        B.ambientActiveWeight (path 1) x =
      R.roughCanonicalGuardedPostchargeRowCorrectedWeight certificate
        deltaStar B.sampleData.W K label alpha beta B.L x
    rw [bankPaperProposition87AmbientActiveWeight_eq_zero_on_nonsmoothPool
      B R certificate deltaStar path hactiveSmooth hlabel.1 hx, add_zero]
    exact hfrozenNonsmooth label hlabel x hx



end BankPaperRealization

end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankPaperCanonicalActualEndpointSlackConnector -/
section


/-!
# Actual paper-data connector for guarded P87 endpoint slack

This file joins the literal Proposition 8.7 data realization to the guarded
smooth-row slack theorem.  The actual frozen tag at a guarded candidate has
weight

`preSelector a - activeSeedAmbient a`.

Guarded broad-pool containment and nonnegativity of the active seed are
already consequences of the existing finite ledger and active-measure
constructor, so they disappear here.  The only quantitative smooth-row
inputs left visible are exactly the paper estimates

* `sigma / L + activeSeedAmbient a <= preSelector a`, the protected reserve;
* `preSelector a <= Cfixed / L`, the raw broad upper bound.

The second theorem then identifies the generic frozen-plus-active endpoint
with `bankPaperCanonicalActualP87EndpointSelector` definitionally and
supplies its two-sided smooth tangent slack.
-/

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.PaperBridgeFit
open Erdos390.Full.PaperGuardCensus

noncomputable section

namespace BankPaperRealization

/-! ## The literal protected window -/

/-- The actual frozen remainder has the required protected window once the
two literal broad-selector estimates are known.  Pool containment and
active-seed nonnegativity are derived, not repeated as premises. -/
theorem bankPaperCanonicalActualSmoothProtectedWindow_of_reserve
    {Head Band : Type*} [Fintype Head] [DecidableEq Head]
    [Fintype Band] [DecidableEq Band] [Nonempty Head]
    (B : BridgeData Head Band)
    {c : Real} {depth K : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (deltaStar : Real) (preSelector : Nat -> Real)
    (activeSeed : B.sampleData.Sample -> Real)
    {T : BarycentricTarget B.sampleData}
    (Hmeasure : BankPaperCanonicalActualActiveMeasureConstructor
      B.sampleData T
        (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
        preSelector activeSeed)
    (sigma Cfixed : Real)
    (hprotectedReserve : ∀ x ∈
      R.roughCanonicalGuardedBroadCorrectionPool certificate
        deltaStar B.sampleData.W K 1,
      sigma / B.L +
          bankPaperCanonicalActiveSeedAmbientWeight
            B.sampleData activeSeed x <=
        preSelector x)
    (hpreUpper : ∀ x ∈
      R.roughCanonicalGuardedBroadCorrectionPool certificate
        deltaStar B.sampleData.W K 1,
      preSelector x <= Cfixed / B.L) :
    BankPaperCanonicalGuardedSmoothProtectedWindow (K := K)
      B R certificate deltaStar
      (bankPaperCanonicalActualFrozenValue
        (candidates := R.roughCanonicalGuardedCandidateSet
          certificate deltaStar K))
      (bankPaperCanonicalActualFrozenWeight B.sampleData
        (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
        preSelector activeSeed)
      sigma Cfixed := by
  have hpool :
      R.roughCanonicalGuardedBroadCorrectionPool certificate
          deltaStar B.sampleData.W K 1 ⊆
        R.roughCanonicalGuardedCandidateSet certificate deltaStar K := by
    intro x hx
    exact (mem_completeRoughRowFiber.mp
      (R.roughCanonicalGuardedBroadCorrectionPool_subset_guardedRow
        certificate deltaStar B.sampleData.W K 1 hx)).1
  have hactiveNonneg : ∀ x ∈
      R.roughCanonicalGuardedBroadCorrectionPool certificate
        deltaStar B.sampleData.W K 1,
      0 <= bankPaperCanonicalActiveSeedAmbientWeight
        B.sampleData activeSeed x := by
    intro x _hx
    exact bankPaperCanonicalActiveSeedAmbientWeight_nonneg Hmeasure x
  simpa only [bankPaperCanonicalActualFrozenValue,
      bankPaperCanonicalActualFrozenWeight] using
    (bankPaperCanonicalGuardedSmoothProtectedWindow_of_subtypeRemainder
      B R certificate deltaStar
      (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
      preSelector
      (bankPaperCanonicalActiveSeedAmbientWeight B.sampleData activeSeed)
      sigma Cfixed hpool hactiveNonneg hprotectedReserve hpreUpper)

/-! ## Smooth slack for the actual endpoint -/



/-! ## Actual endpoint plus nonsmooth correction -/

/-- Join the actual smooth P87 endpoint to the existing nonsmooth
constant-pool correction.  On a nonsmooth row the structured active seed
vanishes by complete-rough-label separation, so the actual frozen remainder
is just `preSelector`; consequently the nonsmooth identification premise is
stated directly for that selector rather than for an opaque frozen layer. -/
theorem bankPaperCanonicalActualP87EndpointSelector_guardedSlackConstruction_of_reserve
    {Head Band : Type*} [Fintype Head] [DecidableEq Head]
    [Fintype Band] [DecidableEq Band] [Nonempty Head]
    (B : BridgeData Head Band)
    {c : Real} {depth K : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (deltaStar alpha beta : Real) (preSelector : Nat -> Real)
    (activeSeed : B.sampleData.Sample -> Real)
    {T : BarycentricTarget B.sampleData}
    (Hmeasure : BankPaperCanonicalActualActiveMeasureConstructor
      B.sampleData T
        (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
        preSelector activeSeed)
    (hseed : forall m : B.sampleData.Sample,
      B.baseline.baseWeight m = activeSeed m)
    (Delta : Band -> Real) (radius : NNReal)
    (markedTarget : Nat -> Real) (N Cpost : Real)
    (quota : Int) (path : Real -> B.ParamSpace)
    (Hpath : B.IsPaperProposition87Path Delta radius markedTarget N Cpost
      (bankPaperCanonicalActualFrozenValue
        (candidates := R.roughCanonicalGuardedCandidateSet
          certificate deltaStar K))
      (bankPaperCanonicalActualFrozenWeight B.sampleData
        (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
        preSelector activeSeed)
      quota path)
    (C sigma Cfixed Cactive : Real)
    (hC : 1 <= C) (hW : 1 < B.sampleData.W)
    (hhi : forall sign,
      B.sampleData.hi sign <= physicalBound C B.sampleData.n)
    (hsep : B.sampleData.HeadPatternsSeparated)
    (hCactive : 0 <= Cactive)
    (hactiveSeed : forall m : B.sampleData.Sample,
      activeSeed m <= Cactive / B.L)
    (hprotectedReserve : ∀ x ∈
      R.roughCanonicalGuardedBroadCorrectionPool certificate
        deltaStar B.sampleData.W K 1,
      sigma / B.L +
          bankPaperCanonicalActiveSeedAmbientWeight
            B.sampleData activeSeed x <=
        preSelector x)
    (hpreUpper : ∀ x ∈
      R.roughCanonicalGuardedBroadCorrectionPool certificate
        deltaStar B.sampleData.W K 1,
      preSelector x <= Cfixed / B.L)
    (hlarge : Cfixed +
        Real.exp (2 *
          ((Erdos390.Full.PaperStatisticNorm.valuationLogCoefficient
              C B.sampleData.W +
            B.nuisanceStatisticCoefficient C) *
              (3 * (radius : Real)))) * Cactive + sigma <= B.L)
    (hnonsmoothBounds : forall label,
      RoughCanonicalActiveNonexceptionalLabel B.sampleData.n deltaStar label ->
        sigma / B.L +
            |R.roughCanonicalGuardedPostchargeCorrectionDensity certificate
              deltaStar B.sampleData.W K label alpha beta B.L| <=
          beta / B.L ∧
        beta / B.L +
            |R.roughCanonicalGuardedPostchargeCorrectionDensity certificate
              deltaStar B.sampleData.W K label alpha beta B.L| <=
          1 - sigma / B.L)
    (hpreNonsmooth : forall label,
      RoughCanonicalActiveNonexceptionalLabel B.sampleData.n deltaStar label ->
        ∀ x ∈ R.roughCanonicalGuardedBroadCorrectionPool certificate
            deltaStar B.sampleData.W K label,
          preSelector x =
            R.roughCanonicalGuardedPostchargeRowCorrectedWeight certificate
              deltaStar B.sampleData.W K label alpha beta B.L x) :
    R.BankPaperCanonicalGuardedEndpointSlackConstruction certificate
      deltaStar B.sampleData.W K alpha beta B.L sigma
      (bankPaperCanonicalActualP87EndpointSelector B
        (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
        preSelector activeSeed path) := by
  let candidates :=
    R.roughCanonicalGuardedCandidateSet certificate deltaStar K
  have hprotected :=
    bankPaperCanonicalActualSmoothProtectedWindow_of_reserve
      B R certificate deltaStar preSelector activeSeed Hmeasure
        sigma Cfixed hprotectedReserve hpreUpper
  have hactive : forall m : B.sampleData.Sample,
      B.baseline.baseWeight m <= Cactive / B.L := by
    intro m
    rw [hseed m]
    exact hactiveSeed m
  have hvalues : forall m : B.sampleData.Sample,
      B.sampleData.value m ∈ candidates := by
    intro m
    exact bankPaperCanonicalActiveSeed_value_mem_candidates Hmeasure m
  have hactiveSmooth : forall m : B.sampleData.Sample,
      B.sampleData.value m ∈
        R.roughCanonicalGuardedRow certificate deltaStar K 1 := by
    intro m
    have hm := bankPaperCanonicalActualActiveValues_subset_smoothRow
      B candidates hvalues
        (mem_bankPaperCanonicalBridgeActiveValues.mpr ⟨m, rfl⟩)
    simpa only [candidates, roughCanonicalGuardedRow] using hm
  have hfrozenNonsmooth : forall label,
      RoughCanonicalActiveNonexceptionalLabel B.sampleData.n deltaStar label ->
        ∀ x ∈ R.roughCanonicalGuardedBroadCorrectionPool certificate
            deltaStar B.sampleData.W K label,
          BridgeData.frozenAmbientWeight
              (bankPaperCanonicalActualFrozenValue
                (candidates := candidates))
              (bankPaperCanonicalActualFrozenWeight B.sampleData candidates
                preSelector activeSeed) x =
            R.roughCanonicalGuardedPostchargeRowCorrectedWeight certificate
              deltaStar B.sampleData.W K label alpha beta B.L x := by
    intro label hlabel x hx
    rw [frozenAmbientWeight_eq_bankPaperCanonicalActualFrozenWeight]
    have hxCandidate : x ∈ candidates := by
      exact (mem_completeRoughRowFiber.mp
        (R.roughCanonicalGuardedBroadCorrectionPool_subset_guardedRow
          certificate deltaStar B.sampleData.W K label hx)).1
    rw [if_pos hxCandidate]
    have hseedZero :
        bankPaperCanonicalActiveSeedAmbientWeight
            B.sampleData activeSeed x = 0 := by
      apply bankPaperCanonicalActiveSeedAmbientWeight_eq_zero_of_not_value
      intro m hmx
      have hxSmooth : x ∈
          R.roughCanonicalGuardedRow certificate deltaStar K 1 := by
        simpa only [hmx] using hactiveSmooth m
      have hxLabel : x ∈
          R.roughCanonicalGuardedRow certificate deltaStar K label :=
        R.roughCanonicalGuardedBroadCorrectionPool_subset_guardedRow
          certificate deltaStar B.sampleData.W K label hx
      have hsmoothEq := (mem_completeRoughRowFiber.mp hxSmooth).2
      have hlabelEq := (mem_completeRoughRowFiber.mp hxLabel).2
      exact hlabel.1 (hlabelEq.symm.trans hsmoothEq)
    rw [hseedZero, sub_zero]
    exact hpreNonsmooth label hlabel x hx
  simpa only [bankPaperCanonicalActualP87EndpointSelector, candidates] using
    (guardedEndpointSlackConstruction_of_proposition87EndpointSelector
      B R certificate deltaStar alpha beta Delta radius markedTarget N Cpost
      (bankPaperCanonicalActualFrozenValue
        (candidates := R.roughCanonicalGuardedCandidateSet
          certificate deltaStar K))
      (bankPaperCanonicalActualFrozenWeight B.sampleData
        (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
        preSelector activeSeed)
      quota path Hpath C sigma Cfixed Cactive hC hW hhi hsep hCactive
      hactive hprotected hlarge hactiveSmooth hnonsmoothBounds
      hfrozenNonsmooth)

end BankPaperRealization

end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankPaperCanonicalSmoothProtectedAdditiveRefinement -/
section


/-!
# Additive protected refinement on the guarded smooth broad pool

The literal raw selector already has constant broad weight `beta / L`.
The paper splits `beta = betaProt + betaAct`, freezes the first summand,
and replaces the second by the structured active seed.  The earlier
guarded continuation records only the resulting smooth-row integer quota;
it does not retain this pointwise additive identity.

This file restores that identity by an explicit local refinement.  On the
guarded smooth broad pool it sets

`preSelector = betaProt / L + activeSeedAmbient`,

and away from that pool it leaves an already constructed base selector
unchanged.  Thus nonsmooth corrected rows are untouched, while the actual
frozen remainder is definitionally the protected constant `betaProt / L`.
The existing raw-point theorem proves that this constant is precisely the
protected part of the paper's head-compatible raw broad weight.

This closes the positive-remainder and pre-selector-upper algebra without a
new selector assumption.  It deliberately does not claim that replacing an
arbitrary smooth row preserves its integer quota or prime moments: those are
the separate smooth-ledger/active-measure construction obligations.
-/

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.PaperBridgeFit
open Erdos390.Full.PaperGuardCensus

noncomputable section

namespace BankPaperRealization

/-! ## The explicit protected layer and additive refinement -/









/-- On the clean smooth broad pool, the explicit protected layer is exactly
the paper's head-compatible raw weight with broad parameter `betaProt`. -/
theorem bankPaperCanonicalGuardedSmoothProtectedLayer_eq_rawWeight_of_mem
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
    {deltaStar alpha betaProt : Real} {a : Nat}
    (ha : a ∈ R.roughCanonicalGuardedBroadCorrectionPool certificate
      deltaStar B.sampleData.W K 1) :
    bankPaperCanonicalGuardedSmoothProtectedLayer (K := K)
      B R certificate
        deltaStar betaProt a =
      roughHeadCompatibleRawWeight B.sampleData.W B.sampleData.n
        (upperTailLength c B.sampleData.n) K alpha betaProt B.L a := by
  rw [bankPaperCanonicalGuardedSmoothProtectedLayer_apply_of_mem
    B R certificate ha]
  exact (roughHeadCompatibleRawWeight_eq_broad_of_mem_correctionPool
    (R.roughCanonicalGuardedBroadCorrectionPool_subset_broadPool
      certificate deltaStar B.sampleData.W K 1 ha)).symm

















/-! ## Derived active and pre-selector upper bounds -/







/-- The protected reserve inequality is definitionally built into the
refinement; only the fixed comparison `sigma <= betaProt` remains. -/
theorem bankPaperCanonicalGuardedSmoothAdditiveRefinement_protectedReserve
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
    {deltaStar betaProt sigma : Real} (baseSelector : Nat -> Real)
    (activeSeed : B.sampleData.Sample -> Real)
    (hsigma : sigma <= betaProt) {a : Nat}
    (ha : a ∈ R.roughCanonicalGuardedBroadCorrectionPool certificate
      deltaStar B.sampleData.W K 1) :
    sigma / B.L +
        bankPaperCanonicalActiveSeedAmbientWeight B.sampleData activeSeed a <=
      bankPaperCanonicalGuardedSmoothAdditiveRefinement (K := K)
        B R certificate
        deltaStar betaProt baseSelector activeSeed a := by
  rw [bankPaperCanonicalGuardedSmoothAdditiveRefinement_apply_of_mem
    B R certificate baseSelector activeSeed ha]
  exact add_le_add
    (div_le_div_of_nonneg_right hsigma B.L_pos.le) le_rfl

/-! ## Exact protected window and actual endpoint -/







end BankPaperRealization

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



/-- A nonnegative base selector and nonnegative protected/active pieces make
the additive refinement nonnegative on the entire guarded candidate set. -/
theorem bankPaperCanonicalGuardedSmoothAdditiveRefinement_nonneg
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
    (deltaStar betaProt : Real) (baseSelector : Nat -> Real)
    (T : BarycentricTarget B.sampleData) (q : Real)
    (hq : 0 <= q) (hbetaProt : 0 <= betaProt)
    (hbaseSelectorNonneg : ∀ a ∈
      R.roughCanonicalGuardedCandidateSet certificate deltaStar K,
      0 <= baseSelector a) :
    ∀ a ∈ R.roughCanonicalGuardedCandidateSet
        certificate deltaStar K,
      0 <= bankPaperCanonicalGuardedSmoothAdditiveRefinement (K := K)
        B R certificate deltaStar betaProt baseSelector
          (bankPaperCanonicalScaledActiveSeed T q) a := by
  intro a ha
  by_cases hpool : a ∈
      R.roughCanonicalGuardedBroadCorrectionPool certificate
        deltaStar B.sampleData.W K 1
  · rw [bankPaperCanonicalGuardedSmoothAdditiveRefinement_apply_of_mem
      B R certificate baseSelector
        (bankPaperCanonicalScaledActiveSeed T q) hpool]
    exact add_nonneg (div_nonneg hbetaProt B.L_pos.le)
      (bankPaperCanonicalActiveSeedAmbientWeight_scaled_nonneg T hq a)
  · rw [bankPaperCanonicalGuardedSmoothAdditiveRefinement_apply_of_not_mem
      B R certificate baseSelector
        (bankPaperCanonicalScaledActiveSeed T q) hpool]
    exact hbaseSelectorNonneg a ha

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









/-- On the original correction pool the extended selector is exactly the
old protected refinement, including at the two zero-head active cells. -/
theorem bankPaperCanonicalGuardedStructuredAdditivePlacementSelector_eq_refinement_of_mem_pool
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
    {deltaStar betaProt : Real} (baseSelector : Nat -> Real)
    (activeSeed : B.sampleData.Sample -> Real) {a : Nat}
    (ha : a ∈ R.roughCanonicalGuardedBroadCorrectionPool certificate
      deltaStar B.sampleData.W K 1) :
    bankPaperCanonicalGuardedStructuredAdditivePlacementSelector (K := K)
        B R certificate deltaStar betaProt baseSelector activeSeed a =
      bankPaperCanonicalGuardedSmoothAdditiveRefinement (K := K) B R certificate
        deltaStar betaProt baseSelector activeSeed a := by
  by_cases hactive :
      a ∈ bankPaperCanonicalStructuredActiveValues B.sampleData
  · rw [bankPaperCanonicalGuardedStructuredAdditivePlacementSelector_apply_of_mem
      (K := K) B R certificate baseSelector activeSeed hactive,
    bankPaperCanonicalGuardedSmoothProtectedLayer_apply_of_mem
      B R certificate ha,
    bankPaperCanonicalGuardedSmoothAdditiveRefinement_apply_of_mem
      B R certificate baseSelector activeSeed ha]
  · rw [bankPaperCanonicalGuardedStructuredAdditivePlacementSelector_apply_of_not_mem
      (K := K) B R certificate baseSelector activeSeed hactive]

/-- If both possible modification supports are known to lie in the smooth
row, the extended selector leaves every coordinate outside that row equal to
the supplied base selector. -/
theorem bankPaperCanonicalGuardedStructuredAdditivePlacementSelector_eq_base_outside_smoothRow
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
    {deltaStar betaProt : Real} (baseSelector : Nat -> Real)
    (activeSeed : B.sampleData.Sample -> Real)
    (hactiveSmooth :
      bankPaperCanonicalStructuredActiveValues B.sampleData ⊆
        R.roughCanonicalGuardedRow certificate deltaStar K 1)
    {a : Nat}
    (ha : a ∉ R.roughCanonicalGuardedRow certificate deltaStar K 1) :
    bankPaperCanonicalGuardedStructuredAdditivePlacementSelector (K := K)
        B R certificate deltaStar betaProt baseSelector activeSeed a =
      baseSelector a := by
  have hnotActive :
      a ∉ bankPaperCanonicalStructuredActiveValues B.sampleData := by
    intro hactive
    exact ha (hactiveSmooth hactive)
  have hnotPool :
      a ∉ R.roughCanonicalGuardedBroadCorrectionPool certificate
        deltaStar B.sampleData.W K 1 := by
    intro hpool
    exact ha
      (R.roughCanonicalGuardedBroadCorrectionPool_subset_guardedRow
        certificate deltaStar B.sampleData.W K 1 hpool)
  rw [bankPaperCanonicalGuardedStructuredAdditivePlacementSelector_apply_of_not_mem
      (K := K) B R certificate baseSelector activeSeed hnotActive,
    bankPaperCanonicalGuardedSmoothAdditiveRefinement_apply_of_not_mem
      B R certificate baseSelector activeSeed hnotPool]

/-- The protected layer is nonnegative everywhere, not merely on its pool. -/
theorem bankPaperCanonicalGuardedSmoothProtectedLayer_nonneg
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
    {deltaStar betaProt : Real} (hbetaProt : 0 <= betaProt)
    (a : Nat) :
    0 <= bankPaperCanonicalGuardedSmoothProtectedLayer (K := K)
      B R certificate deltaStar betaProt a := by
  by_cases ha : a ∈ R.roughCanonicalGuardedBroadCorrectionPool
      certificate deltaStar B.sampleData.W K 1
  · rw [bankPaperCanonicalGuardedSmoothProtectedLayer_apply_of_mem
      B R certificate ha]
    exact div_nonneg hbetaProt B.L_pos.le
  · rw [bankPaperCanonicalGuardedSmoothProtectedLayer_apply_of_not_mem
      B R certificate ha]





/-! ## Exact frozen remainder of the corrected placement -/







/-- The corrected structured placement has coordinate fit without the false
head-free-support premise. -/
theorem bankPaperCanonicalGuardedStructuredAdditivePlacementSelector_coordinateFit
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
    (deltaStar betaProt : Real) (baseSelector : Nat -> Real)
    (T : BarycentricTarget B.sampleData) (q : Real)
    (hsep : B.sampleData.HeadPatternsSeparated)
    (hbetaProt : 0 <= betaProt) :
    BankPaperCanonicalActualCoordinateFit B.sampleData T
      (bankPaperCanonicalGuardedStructuredAdditivePlacementSelector (K := K)
        B R certificate deltaStar betaProt baseSelector
          (bankPaperCanonicalScaledActiveSeed T q)) q := by
  intro m
  rw [bankPaperCanonicalGuardedStructuredAdditivePlacementSelector_scaled_apply_of_value
    (K := K) B R certificate deltaStar betaProt baseSelector T q hsep m]
  exact le_add_of_nonneg_left
    (bankPaperCanonicalGuardedSmoothProtectedLayer_nonneg
      (K := K) (deltaStar := deltaStar)
      B R certificate hbetaProt (B.sampleData.value m))

/-- Nonnegative base, protected, and active layers give a nonnegative
corrected selector on the complete guarded candidate set. -/
theorem bankPaperCanonicalGuardedStructuredAdditivePlacementSelector_nonneg
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
    (deltaStar betaProt : Real) (baseSelector : Nat -> Real)
    (T : BarycentricTarget B.sampleData) (q : Real)
    (hq : 0 <= q) (hbetaProt : 0 <= betaProt)
    (hbaseSelectorNonneg : ∀ a ∈
      R.roughCanonicalGuardedCandidateSet certificate deltaStar K,
      0 <= baseSelector a) :
    ∀ a ∈ R.roughCanonicalGuardedCandidateSet
        certificate deltaStar K,
      0 <= bankPaperCanonicalGuardedStructuredAdditivePlacementSelector (K := K)
        B R certificate deltaStar betaProt baseSelector
          (bankPaperCanonicalScaledActiveSeed T q) a := by
  intro a ha
  by_cases hactive :
      a ∈ bankPaperCanonicalStructuredActiveValues B.sampleData
  · rw [bankPaperCanonicalGuardedStructuredAdditivePlacementSelector_apply_of_mem
      (K := K) B R certificate baseSelector
        (bankPaperCanonicalScaledActiveSeed T q) hactive]
    exact add_nonneg
      (bankPaperCanonicalGuardedSmoothProtectedLayer_nonneg
        (K := K) (deltaStar := deltaStar)
        B R certificate hbetaProt a)
      (bankPaperCanonicalActiveSeedAmbientWeight_scaled_nonneg T hq a)
  · rw [bankPaperCanonicalGuardedStructuredAdditivePlacementSelector_apply_of_not_mem
      (K := K) B R certificate baseSelector
        (bankPaperCanonicalScaledActiveSeed T q) hactive]
    exact bankPaperCanonicalGuardedSmoothAdditiveRefinement_nonneg
      B R certificate deltaStar betaProt baseSelector T q hq hbetaProt
        hbaseSelectorNonneg a ha

/-! ## Exact coordinate capacity and selector feasibility -/



/-- The exact capacity predicate is sufficient for full `[0,1]`
feasibility on the guarded candidate set. -/
theorem bankPaperCanonicalGuardedStructuredAdditivePlacementSelector_mem_Icc
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
    (deltaStar betaProt : Real) (baseSelector : Nat -> Real)
    (T : BarycentricTarget B.sampleData) (q : Real)
    (hq : 0 <= q) (hbetaProt : 0 <= betaProt)
    (hsep : B.sampleData.HeadPatternsSeparated)
    (hbaseSelectorFeasible : ∀ a ∈
      R.roughCanonicalGuardedCandidateSet certificate deltaStar K,
      baseSelector a ∈ Set.Icc (0 : Real) 1)
    (hcapacity : BankPaperCanonicalStructuredAdditivePlacementCapacity (K := K)
      B R certificate deltaStar betaProt T q) :
    ∀ a ∈ R.roughCanonicalGuardedCandidateSet
        certificate deltaStar K,
      bankPaperCanonicalGuardedStructuredAdditivePlacementSelector (K := K)
          B R certificate deltaStar betaProt baseSelector
            (bankPaperCanonicalScaledActiveSeed T q) a ∈
        Set.Icc (0 : Real) 1 := by
  intro a haCandidate
  by_cases hactive :
      a ∈ bankPaperCanonicalStructuredActiveValues B.sampleData
  · obtain ⟨m, hm⟩ :=
      mem_bankPaperCanonicalStructuredActiveValues.mp hactive
    subst a
    rw [bankPaperCanonicalGuardedStructuredAdditivePlacementSelector_scaled_apply_of_value
      (K := K) B R certificate deltaStar betaProt baseSelector T q hsep m]
    exact ⟨add_nonneg
      (bankPaperCanonicalGuardedSmoothProtectedLayer_nonneg
        (K := K) (deltaStar := deltaStar)
        B R certificate hbetaProt (B.sampleData.value m))
      (bankPaperCanonicalScaledActiveSeed_nonneg T hq m),
      hcapacity.2 m⟩
  · rw [bankPaperCanonicalGuardedStructuredAdditivePlacementSelector_apply_of_not_mem
      (K := K) B R certificate baseSelector
        (bankPaperCanonicalScaledActiveSeed T q) hactive]
    by_cases hpool : a ∈
        R.roughCanonicalGuardedBroadCorrectionPool certificate
          deltaStar B.sampleData.W K 1
    · rw [bankPaperCanonicalGuardedSmoothAdditiveRefinement_apply_of_mem
        B R certificate baseSelector
          (bankPaperCanonicalScaledActiveSeed T q) hpool]
      have hzero :
          bankPaperCanonicalActiveSeedAmbientWeight B.sampleData
              (bankPaperCanonicalScaledActiveSeed T q) a = 0 := by
        apply bankPaperCanonicalActiveSeedAmbientWeight_eq_zero_of_not_value
        intro m hm
        exact hactive
          (mem_bankPaperCanonicalStructuredActiveValues.mpr ⟨m, hm⟩)
      rw [hzero, add_zero]
      exact ⟨div_nonneg hbetaProt B.L_pos.le, hcapacity.1⟩
    · rw [bankPaperCanonicalGuardedSmoothAdditiveRefinement_apply_of_not_mem
        B R certificate baseSelector
          (bankPaperCanonicalScaledActiveSeed T q) hpool]
      exact hbaseSelectorFeasible a haCandidate

/-- A pointwise `Cactive/L` active-seed bound and one fixed large-`L`
inequality imply the exact placement capacity. -/
theorem bankPaperCanonicalStructuredAdditivePlacementCapacity_of_div_log_bound
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
    (deltaStar betaProt : Real)
    (T : BarycentricTarget B.sampleData) (q : Real)
    (hbetaProt : 0 <= betaProt)
    (Cactive : Real) (hCactive : 0 <= Cactive)
    (hactiveSeed : forall m : B.sampleData.Sample,
      bankPaperCanonicalScaledActiveSeed T q m <= Cactive / B.L)
    (hlarge : betaProt + Cactive <= B.L) :
    BankPaperCanonicalStructuredAdditivePlacementCapacity (K := K)
      B R certificate deltaStar betaProt T q := by
  constructor
  · have hbetaLe : betaProt <= B.L :=
      (le_add_of_nonneg_right hCactive).trans hlarge
    calc
      betaProt / B.L <= B.L / B.L :=
        div_le_div_of_nonneg_right hbetaLe B.L_pos.le
      _ = 1 := div_self (ne_of_gt B.L_pos)
  · intro m
    have hprotected :
        bankPaperCanonicalGuardedSmoothProtectedLayer (K := K) B R certificate
            deltaStar betaProt (B.sampleData.value m) <=
          betaProt / B.L := by
      by_cases hpool : B.sampleData.value m ∈
          R.roughCanonicalGuardedBroadCorrectionPool certificate
            deltaStar B.sampleData.W K 1
      · rw [bankPaperCanonicalGuardedSmoothProtectedLayer_apply_of_mem
          B R certificate hpool]
      · rw [bankPaperCanonicalGuardedSmoothProtectedLayer_apply_of_not_mem
          B R certificate hpool]
        exact div_nonneg hbetaProt B.L_pos.le
    calc
      bankPaperCanonicalGuardedSmoothProtectedLayer (K := K) B R certificate
            deltaStar betaProt (B.sampleData.value m) +
          bankPaperCanonicalScaledActiveSeed T q m <=
        betaProt / B.L + Cactive / B.L :=
          add_le_add hprotected (hactiveSeed m)
      _ = (betaProt + Cactive) / B.L := by ring
      _ <= B.L / B.L :=
        div_le_div_of_nonneg_right hlarge B.L_pos.le
      _ = 1 := div_self (ne_of_gt B.L_pos)



/-! ## Full guarded constructor with the corrected placement -/

/-- The complete actual-active-measure constructor on the guarded candidate
set.  Unlike the older refinement connector, it requires only the real
interval support and pointwise rough-guard avoidance; no head-free-support
premise remains. -/
theorem bankPaperCanonicalActualActiveMeasureConstructor_of_structuredAdditivePlacement
    {Head Band : Type*} [Fintype Head] [DecidableEq Head]
    [Fintype Band] [DecidableEq Band] [Nonempty Head]
    (B : BridgeData Head Band)
    {c : Real} {depth K : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (deltaStar betaProt : Real) (baseSelector : Nat -> Real)
    (T : BarycentricTarget B.sampleData) (q : Real) (hq : 1 <= q)
    (hsep : B.sampleData.HeadPatternsSeparated)
    (hKh : K * upperTailLength c B.sampleData.n <= B.sampleData.n)
    (hlower : forall m : B.sampleData.Sample,
      B.sampleData.n < B.sampleData.value m)
    (hupper : forall m : B.sampleData.Sample,
      B.sampleData.value m <= 2 * B.sampleData.n)
    (hnotGuard : forall m : B.sampleData.Sample,
      B.sampleData.value m ∉
        R.roughCanonicalGuardSet certificate deltaStar)
    (hbetaProt : 0 <= betaProt)
    (hbaseSelectorNonneg : ∀ a ∈
      R.roughCanonicalGuardedCandidateSet certificate deltaStar K,
      0 <= baseSelector a) :
    BankPaperCanonicalActualActiveMeasureConstructor B.sampleData T
      (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
      (bankPaperCanonicalGuardedStructuredAdditivePlacementSelector (K := K)
        B R certificate deltaStar betaProt baseSelector
          (bankPaperCanonicalScaledActiveSeed T q))
      (bankPaperCanonicalScaledActiveSeed T q) := by
  apply bankPaperCanonicalActualActiveMeasureConstructor_guarded_of_coordinateFit
    B R certificate deltaStar T
      (bankPaperCanonicalGuardedStructuredAdditivePlacementSelector (K := K)
        B R certificate deltaStar betaProt baseSelector
          (bankPaperCanonicalScaledActiveSeed T q))
      q hq hsep hKh hlower hupper hnotGuard
  · exact bankPaperCanonicalGuardedStructuredAdditivePlacementSelector_nonneg
      B R certificate deltaStar betaProt baseSelector T q
        (zero_le_one.trans hq) hbetaProt hbaseSelectorNonneg
  · exact bankPaperCanonicalGuardedStructuredAdditivePlacementSelector_coordinateFit
      (K := K) B R certificate deltaStar betaProt baseSelector T q hsep
        hbetaProt

/-- Constructor and `[0,1]` selector feasibility packaged together.  The
capacity premise is exactly the one discharged above by cell density. -/
theorem bankPaperCanonicalActualActiveMeasureConstructor_and_feasible_of_structuredAdditivePlacement
    {Head Band : Type*} [Fintype Head] [DecidableEq Head]
    [Fintype Band] [DecidableEq Band] [Nonempty Head]
    (B : BridgeData Head Band)
    {c : Real} {depth K : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (deltaStar betaProt : Real) (baseSelector : Nat -> Real)
    (T : BarycentricTarget B.sampleData) (q : Real) (hq : 1 <= q)
    (hsep : B.sampleData.HeadPatternsSeparated)
    (hKh : K * upperTailLength c B.sampleData.n <= B.sampleData.n)
    (hlower : forall m : B.sampleData.Sample,
      B.sampleData.n < B.sampleData.value m)
    (hupper : forall m : B.sampleData.Sample,
      B.sampleData.value m <= 2 * B.sampleData.n)
    (hnotGuard : forall m : B.sampleData.Sample,
      B.sampleData.value m ∉
        R.roughCanonicalGuardSet certificate deltaStar)
    (hbetaProt : 0 <= betaProt)
    (hbaseSelectorFeasible : ∀ a ∈
      R.roughCanonicalGuardedCandidateSet certificate deltaStar K,
      baseSelector a ∈ Set.Icc (0 : Real) 1)
    (hcapacity : BankPaperCanonicalStructuredAdditivePlacementCapacity (K := K)
      B R certificate deltaStar betaProt T q) :
    BankPaperCanonicalActualActiveMeasureConstructor B.sampleData T
        (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
        (bankPaperCanonicalGuardedStructuredAdditivePlacementSelector (K := K)
          B R certificate deltaStar betaProt baseSelector
            (bankPaperCanonicalScaledActiveSeed T q))
        (bankPaperCanonicalScaledActiveSeed T q) ∧
      (∀ a ∈ R.roughCanonicalGuardedCandidateSet
          certificate deltaStar K,
        bankPaperCanonicalGuardedStructuredAdditivePlacementSelector (K := K)
            B R certificate deltaStar betaProt baseSelector
              (bankPaperCanonicalScaledActiveSeed T q) a ∈
          Set.Icc (0 : Real) 1) := by
  constructor
  · exact bankPaperCanonicalActualActiveMeasureConstructor_of_structuredAdditivePlacement
      B R certificate deltaStar betaProt baseSelector T q hq hsep
        hKh hlower hupper hnotGuard hbetaProt
        (fun a ha => (hbaseSelectorFeasible a ha).1)
  · exact bankPaperCanonicalGuardedStructuredAdditivePlacementSelector_mem_Icc
      B R certificate deltaStar betaProt baseSelector T q
        (zero_le_one.trans hq) hbetaProt hsep hbaseSelectorFeasible hcapacity

/-- Fixed physical endpoints discharge both numerical support inequalities
in the constructor-plus-feasibility package. -/
theorem bankPaperCanonicalActualActiveMeasureConstructor_and_feasible_of_structuredAdditivePlacement_physicalIntervals
    {Head Band : Type*} [Fintype Head] [DecidableEq Head]
    [Fintype Band] [DecidableEq Band] [Nonempty Head]
    (B : BridgeData Head Band)
    {c : Real} {depth K : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (deltaStar betaProt : Real) (baseSelector : Nat -> Real)
    (T : BarycentricTarget B.sampleData) (q : Real) (hq : 1 <= q)
    (hsep : B.sampleData.HeadPatternsSeparated)
    (I : PhysicalIntervals)
    (hlowerOne : forall sigma, 1 <= I.lower sigma)
    (hupperTwo : forall sigma, I.upper sigma <= 2)
    (hlo : forall sigma, B.sampleData.lo sigma =
      physicalBound (I.lower sigma) B.sampleData.n)
    (hhi : forall sigma, B.sampleData.hi sigma =
      physicalBound (I.upper sigma) B.sampleData.n)
    (hKh : K * upperTailLength c B.sampleData.n <= B.sampleData.n)
    (hnotGuard : forall m : B.sampleData.Sample,
      B.sampleData.value m ∉
        R.roughCanonicalGuardSet certificate deltaStar)
    (hbetaProt : 0 <= betaProt)
    (hbaseSelectorFeasible : ∀ a ∈
      R.roughCanonicalGuardedCandidateSet certificate deltaStar K,
      baseSelector a ∈ Set.Icc (0 : Real) 1)
    (hcapacity : BankPaperCanonicalStructuredAdditivePlacementCapacity (K := K)
      B R certificate deltaStar betaProt T q) :
    BankPaperCanonicalActualActiveMeasureConstructor B.sampleData T
        (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
        (bankPaperCanonicalGuardedStructuredAdditivePlacementSelector (K := K)
          B R certificate deltaStar betaProt baseSelector
            (bankPaperCanonicalScaledActiveSeed T q))
        (bankPaperCanonicalScaledActiveSeed T q) ∧
      (∀ a ∈ R.roughCanonicalGuardedCandidateSet
          certificate deltaStar K,
        bankPaperCanonicalGuardedStructuredAdditivePlacementSelector (K := K)
            B R certificate deltaStar betaProt baseSelector
              (bankPaperCanonicalScaledActiveSeed T q) a ∈
          Set.Icc (0 : Real) 1) := by
  have hbounds := bankPaperCanonicalStructuredValue_bounds_of_physicalIntervals
    B I hlowerOne hupperTwo hlo hhi
  exact
    bankPaperCanonicalActualActiveMeasureConstructor_and_feasible_of_structuredAdditivePlacement
      B R certificate deltaStar betaProt baseSelector T q hq hsep
        hKh hbounds.1 hbounds.2 hnotGuard hbetaProt
        hbaseSelectorFeasible hcapacity



end BankPaperRealization

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



/-- Uniform spreading realizes the requested cell mass exactly. -/
theorem sum_bankPaperCanonicalUniformCellIncrement
    {Head : Type*} [Fintype Head]
    (D : StructuredSampleData Head) (cell : Cell Head)
    (mass : Real) :
    (∑ m : D.Sample,
      bankPaperCanonicalUniformCellIncrement D cell mass m) = mass := by
  classical
  rw [Fintype.sum_sigma, Finset.sum_eq_single cell]
  · simp only [bankPaperCanonicalUniformCellIncrement,
      StructuredSampleData.cellOf, if_true, Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul]
    have hcard : (Fintype.card (D.SampleAt cell) : Real) ≠ 0 := by
      exact_mod_cast Nat.ne_of_gt (D.sampleAt_card_pos cell)
    field_simp [hcard]
  · intro other _hother hne
    apply Finset.sum_eq_zero
    intro m _hm
    simp [bankPaperCanonicalUniformCellIncrement,
      StructuredSampleData.cellOf, hne]
  · intro hnot
    exact (hnot (Finset.mem_univ cell)).elim



/-- The two zero-head pool changes alter the tagged active mass by exactly
the sum of their two requested masses. -/
theorem sum_bankPaperCanonicalTwoZeroHeadCellRebalance_sub
    {P : Finset Nat}
    (D : StructuredSampleData (PaperHeadSimplex.Tag P))
    (seed : D.Sample -> Real) (minusMass plusMass : Real) :
    (∑ m : D.Sample,
        (bankPaperCanonicalTwoZeroHeadCellRebalance D seed
            minusMass plusMass m - seed m)) = minusMass + plusMass := by
  calc
    (∑ m : D.Sample,
        (bankPaperCanonicalTwoZeroHeadCellRebalance D seed
            minusMass plusMass m - seed m)) =
        (∑ m : D.Sample,
          bankPaperCanonicalUniformCellIncrement
            D (none, .minus) minusMass m) +
        ∑ m : D.Sample,
          bankPaperCanonicalUniformCellIncrement
            D (none, .plus) plusMass m := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro m _hm
      unfold bankPaperCanonicalTwoZeroHeadCellRebalance
      ring
    _ = minusMass + plusMass := by
      rw [sum_bankPaperCanonicalUniformCellIncrement,
        sum_bankPaperCanonicalUniformCellIncrement]

/-- Literal active mass after the two pool changes. -/
theorem bankPaperCanonicalLiteralActiveMass_twoZeroHeadCellRebalance
    {P : Finset Nat}
    (D : StructuredSampleData (PaperHeadSimplex.Tag P))
    (seed : D.Sample -> Real) (minusMass plusMass : Real) :
    bankPaperCanonicalLiteralActiveMass D
        (bankPaperCanonicalTwoZeroHeadCellRebalance D seed
          minusMass plusMass) =
      bankPaperCanonicalLiteralActiveMass D seed +
        minusMass + plusMass := by
  unfold bankPaperCanonicalLiteralActiveMass
  have hchange := sum_bankPaperCanonicalTwoZeroHeadCellRebalance_sub
    D seed minusMass plusMass
  rw [add_assoc, ← hchange]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro m _hm
  ring

/-- For a canonical scaled seed, the preceding identity reads
`q + deltaMinus + deltaPlus` with no normalization surrogate. -/
theorem bankPaperCanonicalLiteralActiveMass_rebalancedScaledActiveSeed
    {P : Finset Nat}
    (D : StructuredSampleData (PaperHeadSimplex.Tag P))
    (T : BarycentricTarget D) (q minusMass plusMass : Real) :
    bankPaperCanonicalLiteralActiveMass D
        (bankPaperCanonicalTwoZeroHeadCellRebalance D
          (bankPaperCanonicalScaledActiveSeed T q)
          minusMass plusMass) = q + minusMass + plusMass := by
  rw [bankPaperCanonicalLiteralActiveMass_twoZeroHeadCellRebalance,
    bankPaperCanonicalLiteralActiveMass_scaledActiveSeed]









/-! ## The head-free correction-pool ledger -/











/-! ## Structured head-cell realization -/



















/-! ## Exact support boundary -/



/-! ## Signed whole-smooth-row placement ledger -/





/-- Every valuation moment of the corrected placement above the smooth
cutoff vanishes.  This uses the complete smooth row itself, so it applies
equally to the old head-free correction pool and to the added structured
head coordinates. -/
theorem bankPaperCanonicalGuardedStructuredAdditivePlacementValuationMoment_eq_zero_of_yNat_lt
    {Head GeoBand : Type*} [Fintype Head] [DecidableEq Head]
    [Fintype GeoBand] [DecidableEq GeoBand]
    (B : BridgeData Head GeoBand)
    {c : Real} {depth K : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    {deltaStar betaProt : Real} (baseSelector : Nat -> Real)
    (activeSeed : B.sampleData.Sample -> Real) {q : Nat}
    (hqPrime : q.Prime) (hqLarge : yNat B.sampleData.n < q) :
    bankPaperCanonicalGuardedStructuredAdditivePlacementValuationMoment (K := K)
      B R certificate deltaStar betaProt baseSelector activeSeed q = 0 := by
  unfold
    bankPaperCanonicalGuardedStructuredAdditivePlacementValuationMoment
  apply Finset.sum_eq_zero
  intro a ha
  have haData := mem_completeRoughRowFiber.mp ha
  have haRaw : a ∈ roughRawCandidateSet B.sampleData.n
      (upperTailLength c B.sampleData.n) K :=
    R.roughCanonicalGuardedCandidateSet_subset_rawCandidateSet
      certificate deltaStar K haData.1
  have haPos : 0 < a := by
    rw [roughRawCandidateSet, Finset.mem_union] at haRaw
    rcases haRaw with haHigh | haBroad
    · rw [roughHighLowerBlock, Finset.mem_Ioc] at haHigh
      omega
    · rw [roughBroadLowerBlock, Finset.mem_Ioc] at haBroad
      omega
  have haSmooth :
      a ∈ Nat.smoothNumbers (yNat B.sampleData.n + 1) :=
    (completeRoughLabel_eq_one_iff_mem_smoothNumbers haPos).mp haData.2
  have hnotDvd : ¬q ∣ a := by
    intro hqa
    have hqSmall :=
      (Nat.mem_smoothNumbers').mp haSmooth q hqPrime hqa
    omega
  rw [Nat.factorization_eq_zero_of_not_dvd hnotDvd]
  simp

/-- The signed smooth-row moment is exactly the change of the weighted
candidate sum.  The corrected placement equals the base selector off the
smooth row once the structured image is known to lie in that row. -/
theorem sum_guardedCandidates_structuredAdditivePlacement_factorization_sub_base_eq_moment
    {Head GeoBand : Type*} [Fintype Head] [DecidableEq Head]
    [Fintype GeoBand] [DecidableEq GeoBand]
    (B : BridgeData Head GeoBand)
    {c : Real} {depth K : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    {deltaStar betaProt : Real} (baseSelector : Nat -> Real)
    (activeSeed : B.sampleData.Sample -> Real)
    (hactiveSmooth :
      bankPaperCanonicalStructuredActiveValues B.sampleData ⊆
        R.roughCanonicalGuardedRow certificate deltaStar K 1)
    (q : Nat) :
    (∑ a ∈ R.roughCanonicalGuardedCandidateSet certificate deltaStar K,
        bankPaperCanonicalGuardedStructuredAdditivePlacementSelector (K := K)
            B R certificate deltaStar betaProt baseSelector activeSeed a *
          (a.factorization q : Real)) -
        ∑ a ∈ R.roughCanonicalGuardedCandidateSet certificate deltaStar K,
          baseSelector a * (a.factorization q : Real) =
      bankPaperCanonicalGuardedStructuredAdditivePlacementValuationMoment (K := K)
        B R certificate deltaStar betaProt baseSelector activeSeed q := by
  rw [← Finset.sum_sub_distrib]
  have hsmooth :
      R.roughCanonicalGuardedRow certificate deltaStar K 1 ⊆
        R.roughCanonicalGuardedCandidateSet certificate deltaStar K := by
    intro a ha
    exact (mem_completeRoughRowFiber.mp ha).1
  calc
    (∑ a ∈ R.roughCanonicalGuardedCandidateSet certificate deltaStar K,
        (bankPaperCanonicalGuardedStructuredAdditivePlacementSelector (K := K)
              B R certificate deltaStar betaProt baseSelector activeSeed a *
            (a.factorization q : Real) -
          baseSelector a * (a.factorization q : Real))) =
      ∑ a ∈ R.roughCanonicalGuardedRow certificate deltaStar K 1,
        (bankPaperCanonicalGuardedStructuredAdditivePlacementSelector (K := K)
              B R certificate deltaStar betaProt baseSelector activeSeed a *
            (a.factorization q : Real) -
          baseSelector a * (a.factorization q : Real)) := by
      symm
      apply Finset.sum_subset hsmooth
      intro a _haCandidate haNotSmooth
      rw [
        bankPaperCanonicalGuardedStructuredAdditivePlacementSelector_eq_base_outside_smoothRow
          B R certificate baseSelector activeSeed hactiveSmooth haNotSmooth]
      ring
    _ = bankPaperCanonicalGuardedStructuredAdditivePlacementValuationMoment (K := K)
        B R certificate deltaStar betaProt baseSelector activeSeed q := by
      unfold
        bankPaperCanonicalGuardedStructuredAdditivePlacementValuationMoment
      apply Finset.sum_congr rfl
      intro a _ha
      ring

/-- Exact transport of the literal selector valuation deficit under the
corrected whole-row placement. -/
theorem bankPaperCanonicalSelectorValuationDeficit_structuredAdditivePlacement_eq_sub_moment
    {Head GeoBand : Type*} [Fintype Head] [DecidableEq Head]
    [Fintype GeoBand] [DecidableEq GeoBand]
    (B : BridgeData Head GeoBand)
    {c : Real} {depth K : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (fixed : Finset Nat)
    {deltaStar betaProt : Real} (baseSelector : Nat -> Real)
    (activeSeed : B.sampleData.Sample -> Real)
    (hactiveSmooth :
      bankPaperCanonicalStructuredActiveValues B.sampleData ⊆
        R.roughCanonicalGuardedRow certificate deltaStar K 1)
    (q : Nat) :
    bankPaperCanonicalSelectorValuationDeficit R certificate fixed
        (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
        (bankPaperCanonicalGuardedStructuredAdditivePlacementSelector (K := K)
          B R certificate deltaStar betaProt baseSelector activeSeed) q =
      bankPaperCanonicalSelectorValuationDeficit R certificate fixed
          (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
          baseSelector q -
        bankPaperCanonicalGuardedStructuredAdditivePlacementValuationMoment (K := K)
          B R certificate deltaStar betaProt baseSelector activeSeed q := by
  have hmoment :=
    sum_guardedCandidates_structuredAdditivePlacement_factorization_sub_base_eq_moment
      (betaProt := betaProt)
      B R certificate baseSelector activeSeed hactiveSmooth q
  unfold bankPaperCanonicalSelectorValuationDeficit
  rw [← hmoment]
  ring

/-- An integral signed change on the complete smooth row preserves every
complete-row integer quota for the corrected placement.  Other rows are
unchanged pointwise. -/
theorem bankPaperCanonicalSelectorRowIntegral_structuredAdditivePlacement_of_prebridgeMomentLedger
    {Head GeoBand : Type*} [Fintype Head] [DecidableEq Head]
    [Fintype GeoBand] [DecidableEq GeoBand]
    (B : BridgeData Head GeoBand)
    {c : Real} {depth K : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    {deltaStar betaProt : Real} (baseSelector : Nat -> Real)
    (activeSeed : B.sampleData.Sample -> Real)
    (hbase : BankPaperCanonicalSelectorRowIntegral B.sampleData.n
      (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
      baseSelector)
    (hledger :
      BankPaperCanonicalGuardedStructuredAdditivePrebridgeMomentLedger (K := K)
        B R certificate deltaStar betaProt baseSelector activeSeed) :
    BankPaperCanonicalSelectorRowIntegral B.sampleData.n
      (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
      (bankPaperCanonicalGuardedStructuredAdditivePlacementSelector (K := K)
        B R certificate deltaStar betaProt baseSelector activeSeed) := by
  intro label hlabelMem
  obtain ⟨quota, hquota⟩ := hbase label hlabelMem
  by_cases hlabel : label = 1
  · subst label
    obtain ⟨rowChange, hrowChange⟩ := hledger.2.1
    refine ⟨quota + rowChange, ?_⟩
    change
      (∑ a ∈ R.roughCanonicalGuardedRow certificate deltaStar K 1,
          bankPaperCanonicalGuardedStructuredAdditivePlacementSelector (K := K)
            B R certificate deltaStar betaProt baseSelector activeSeed a) =
        ((quota + rowChange : Int) : Real)
    change
      (∑ a ∈ R.roughCanonicalGuardedRow certificate deltaStar K 1,
          baseSelector a) = (quota : Real) at hquota
    have hchange :
        (∑ a ∈ R.roughCanonicalGuardedRow certificate deltaStar K 1,
            bankPaperCanonicalGuardedStructuredAdditivePlacementSelector (K := K)
              B R certificate deltaStar betaProt baseSelector activeSeed a) -
          ∑ a ∈ R.roughCanonicalGuardedRow certificate deltaStar K 1,
            baseSelector a = (rowChange : Real) := by
      rw [← Finset.sum_sub_distrib]
      exact hrowChange
    calc
      (∑ a ∈ R.roughCanonicalGuardedRow certificate deltaStar K 1,
          bankPaperCanonicalGuardedStructuredAdditivePlacementSelector (K := K)
            B R certificate deltaStar betaProt baseSelector activeSeed a) =
        (∑ a ∈ R.roughCanonicalGuardedRow certificate deltaStar K 1,
          baseSelector a) + (rowChange : Real) := by linarith
      _ = (quota : Real) + (rowChange : Real) := by rw [hquota]
      _ = ((quota + rowChange : Int) : Real) := by norm_num
  · refine ⟨quota, ?_⟩
    change
      (∑ a ∈ R.roughCanonicalGuardedRow certificate deltaStar K label,
          bankPaperCanonicalGuardedStructuredAdditivePlacementSelector (K := K)
            B R certificate deltaStar betaProt baseSelector activeSeed a) =
        (quota : Real)
    change
      (∑ a ∈ R.roughCanonicalGuardedRow certificate deltaStar K label,
          baseSelector a) = (quota : Real) at hquota
    calc
      (∑ a ∈ R.roughCanonicalGuardedRow certificate deltaStar K label,
          bankPaperCanonicalGuardedStructuredAdditivePlacementSelector (K := K)
            B R certificate deltaStar betaProt baseSelector activeSeed a) =
        ∑ a ∈ R.roughCanonicalGuardedRow certificate deltaStar K label,
          baseSelector a := by
        apply Finset.sum_congr rfl
        intro a ha
        apply
          bankPaperCanonicalGuardedStructuredAdditivePlacementSelector_eq_base_outside_smoothRow
            B R certificate baseSelector activeSeed hledger.1
        intro haSmooth
        have hsmoothEq := (mem_completeRoughRowFiber.mp haSmooth).2
        have hlabelEq := (mem_completeRoughRowFiber.mp ha).2
        exact hlabel (hlabelEq.symm.trans hsmoothEq)
      _ = (quota : Real) := hquota

/-- The signed head moments from the ledger, together with automatic
vanishing above `y`, preserve exact selector-target agreement outside the
medium-prime tangent band. -/
theorem bankPaperCanonicalSelectorDeficitSupportedOnPrimeBand_structuredAdditivePlacement_of_prebridgeMomentLedger
    {Head GeoBand : Type*} [Fintype Head] [DecidableEq Head]
    [Fintype GeoBand] [DecidableEq GeoBand]
    (B : BridgeData Head GeoBand)
    {c : Real} {depth K : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (fixed : Finset Nat)
    {deltaStar betaProt : Real} (baseSelector : Nat -> Real)
    (activeSeed : B.sampleData.Sample -> Real)
    (hbase : BankPaperCanonicalSelectorDeficitSupportedOnPrimeBand
      (W := B.sampleData.W) R certificate fixed
      (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
      baseSelector)
    (hledger :
      BankPaperCanonicalGuardedStructuredAdditivePrebridgeMomentLedger (K := K)
        B R certificate deltaStar betaProt baseSelector activeSeed) :
    BankPaperCanonicalSelectorDeficitSupportedOnPrimeBand
      (W := B.sampleData.W) R certificate fixed
      (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
      (bankPaperCanonicalGuardedStructuredAdditivePlacementSelector (K := K)
        B R certificate deltaStar betaProt baseSelector activeSeed) := by
  intro q hqPrime hqNotBand
  have hmoment :
      bankPaperCanonicalGuardedStructuredAdditivePlacementValuationMoment (K := K)
        B R certificate deltaStar betaProt baseSelector activeSeed q = 0 := by
    by_cases hqHead : q <= B.sampleData.W
    · exact hledger.2.2 q hqPrime hqHead
    · have hWq : B.sampleData.W < q := Nat.lt_of_not_ge hqHead
      have hyq : yNat B.sampleData.n < q := by
        by_contra hnotY
        have hqy : q <= yNat B.sampleData.n := Nat.le_of_not_gt hnotY
        exact hqNotBand (mem_primeBand.mpr ⟨hqPrime, hWq, hqy⟩)
      exact
        bankPaperCanonicalGuardedStructuredAdditivePlacementValuationMoment_eq_zero_of_yNat_lt
          B R certificate baseSelector activeSeed hqPrime hyq
  rw [
    bankPaperCanonicalSelectorValuationDeficit_structuredAdditivePlacement_eq_sub_moment
      B R certificate fixed baseSelector activeSeed hledger.1 q,
    hmoment, sub_zero]
  exact hbase q hqPrime hqNotBand







/-- Feasibility of the corrected selector and the signed whole-row ledger
give the corrected additive placement predicate exactly. -/
theorem bankPaperCanonicalGuardedStructuredAdditivePlacement_of_prebridgeMomentLedger
    {Head GeoBand : Type*} [Fintype Head] [DecidableEq Head]
    [Fintype GeoBand] [DecidableEq GeoBand]
    (B : BridgeData Head GeoBand)
    {c : Real} {depth K : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (fixed : Finset Nat)
    {deltaStar betaProt : Real} (baseSelector : Nat -> Real)
    (activeSeed : B.sampleData.Sample -> Real)
    (hfeasible : ∀ a ∈
      R.roughCanonicalGuardedCandidateSet certificate deltaStar K,
      0 <= bankPaperCanonicalGuardedStructuredAdditivePlacementSelector (K := K)
          B R certificate deltaStar betaProt baseSelector activeSeed a ∧
        bankPaperCanonicalGuardedStructuredAdditivePlacementSelector (K := K)
          B R certificate deltaStar betaProt baseSelector activeSeed a <= 1)
    (hbaseRow : BankPaperCanonicalSelectorRowIntegral B.sampleData.n
      (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
      baseSelector)
    (hbaseSupport : BankPaperCanonicalSelectorDeficitSupportedOnPrimeBand
      (W := B.sampleData.W) R certificate fixed
      (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
      baseSelector)
    (hledger :
      BankPaperCanonicalGuardedStructuredAdditivePrebridgeMomentLedger (K := K)
        B R certificate deltaStar betaProt baseSelector activeSeed) :
    BankPaperCanonicalGuardedStructuredAdditivePlacement (K := K)
      B R certificate fixed deltaStar betaProt baseSelector activeSeed := by
  unfold BankPaperCanonicalGuardedStructuredAdditivePlacement
  refine ⟨hfeasible, ?_, ?_⟩
  · exact
      bankPaperCanonicalSelectorRowIntegral_structuredAdditivePlacement_of_prebridgeMomentLedger
        B R certificate baseSelector activeSeed hbaseRow hledger
  · exact
      bankPaperCanonicalSelectorDeficitSupportedOnPrimeBand_structuredAdditivePlacement_of_prebridgeMomentLedger
        B R certificate fixed baseSelector activeSeed hbaseSupport hledger













end BankPaperRealization

/-! ## Weaker actual-endpoint preselector interface -/

/-- The actual Proposition 8.7 endpoint needs only row integrality and
outside-band deficit support from its pre-selector.  Exact endpoint band
balance, pointwise control, and the deterministic prefix bounds all come
from the P87 path and its existing prefix adapter. -/
theorem exists_bankPaperCanonicalActualP87EndpointSelector_of_rowIntegral_deficitSupported
    {Head Band : Type*} [Fintype Head] [DecidableEq Head]
    [Fintype Band] [DecidableEq Band] [Nonempty Head]
    (B : BridgeData Head Band)
    {c : Real} {depth : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (fixed candidates : Finset Nat) (preSelector : Nat -> Real)
    (activeSeed : B.sampleData.Sample -> Real)
    {T : BarycentricTarget B.sampleData}
    (Hmeasure : BankPaperCanonicalActualActiveMeasureConstructor
      B.sampleData T candidates preSelector activeSeed)
    (hseed : forall m, B.baseline.baseWeight m = activeSeed m)
    (hpreRow : BankPaperCanonicalSelectorRowIntegral
      B.sampleData.n candidates preSelector)
    (hpreSupport : BankPaperCanonicalSelectorDeficitSupportedOnPrimeBand
      (W := B.sampleData.W) R certificate fixed candidates preSelector)
    (Delta : Band -> Real) (radius : NNReal) (N Cpost : Real)
    (quota : Int)
    (Hfit : B.HasPaperProposition87Conclusion Delta radius
      (bankPaperCanonicalActualActiveMarkedTarget B R certificate
        fixed candidates preSelector activeSeed)
      N Cpost
      (bankPaperCanonicalActualFrozenValue (candidates := candidates))
      (bankPaperCanonicalActualFrozenWeight
        B.sampleData candidates preSelector activeSeed)
      quota)
    (cellIndex : BankPaperCanonicalTangentPrime
      B.sampleData.n B.sampleData.W -> Nat) :
    ∃ path : Real -> B.ParamSpace, ∃ endpoint : Nat -> Real,
      B.IsPaperProposition87Path Delta radius
        (bankPaperCanonicalActualActiveMarkedTarget B R certificate
          fixed candidates preSelector activeSeed)
        N Cpost
        (bankPaperCanonicalActualFrozenValue (candidates := candidates))
        (bankPaperCanonicalActualFrozenWeight
          B.sampleData candidates preSelector activeSeed)
        quota path ∧
      endpoint = bankPaperCanonicalActualP87EndpointSelector
        B candidates preSelector activeSeed path ∧
      bankPaperProposition87SelectorSupport B
        (bankPaperCanonicalActualFrozenValue (candidates := candidates)) =
          candidates ∧
      (forall p : Nat,
        bankPaperProposition87FullMarkedTarget
            (bankPaperCanonicalActualFrozenValue (candidates := candidates))
            (bankPaperCanonicalActualFrozenWeight
              B.sampleData candidates preSelector activeSeed)
            (bankPaperCanonicalActualActiveMarkedTarget B R certificate
              fixed candidates preSelector activeSeed) p =
          ((certificate.selectorTailTarget R fixed).factorization p : Real)) ∧
      (forall x, x ∉ candidates -> endpoint x = 0) ∧
      BankPaperCanonicalRoundedSelectorTangentInput
        R certificate fixed candidates B.partition.band cellIndex
        (bankPaperCanonicalActualP87PointwiseUpper B N Cpost)
        (tangentRatioCellTailPointwiseUpper
          (bankPaperCanonicalActualP87PointwiseUpper B N Cpost)
          B.partition.band cellIndex)
        endpoint := by
  obtain ⟨path, hpath, hbands⟩ := Hfit
  let endpoint := bankPaperCanonicalActualP87EndpointSelector
    B candidates preSelector activeSeed path
  have hpathData := hpath
  rcases hpathData with
    ⟨_hzero, _hball, _hsize, _hderiv, _hbandMoments, _hphysical,
      _hlog, _hheads, hsmall, _hprimeLog, hmarked, hfeasible,
      _hfixed, _hmass, _hquota⟩
  have hvalues : forall m : B.sampleData.Sample,
      B.sampleData.value m ∈ candidates :=
    fun m => bankPaperCanonicalActiveSeed_value_mem_candidates Hmeasure m
  have hselector : ∀ x ∈ candidates,
      0 <= endpoint x ∧ endpoint x <= 1 := by
    intro x _hx
    exact hfeasible 1 (by simp) x
  have hrow : BankPaperCanonicalSelectorRowIntegral
      B.sampleData.n candidates endpoint := by
    exact bankPaperCanonicalActualP87EndpointSelector_rowIntegral
      B candidates preSelector activeSeed Hmeasure hseed path hpreRow
  have hsupport : BankPaperCanonicalSelectorDeficitSupportedOnPrimeBand
      (W := B.sampleData.W) R certificate fixed candidates endpoint := by
    exact
      bankPaperCanonicalActualP87EndpointSelector_deficitSupportedOnPrimeBand
        B R certificate fixed candidates preSelector activeSeed Hmeasure hseed
        path hpreSupport hsmall
  have hbalance : forall band : Band,
      (∑ p : BankPaperCanonicalTangentPrime
          B.sampleData.n B.sampleData.W,
        if B.partition.band p = band then
          bankPaperCanonicalTangentResidual R certificate fixed candidates
            endpoint p
        else 0) = 0 := by
    exact bankPaperCanonicalActualP87EndpointSelector_bandBalance
      B R certificate fixed candidates preSelector activeSeed hvalues path
        hbands
  have hprimeBandBalance : BankPaperCanonicalPostRoundingPrimeBandBalance
      (W := B.sampleData.W) R certificate fixed candidates endpoint := by
    exact bankPaperCanonicalActualP87EndpointSelector_primeBandBalance
      B R certificate fixed candidates preSelector activeSeed path hbalance
  have hpointwise : forall p : BankPaperCanonicalTangentPrime
      B.sampleData.n B.sampleData.W,
      abs (bankPaperCanonicalTangentResidual R certificate fixed candidates
        endpoint p) <= bankPaperCanonicalActualP87PointwiseUpper B N Cpost p := by
    exact bankPaperCanonicalActualP87EndpointSelector_pointwise
      B R certificate fixed candidates preSelector activeSeed hvalues path
        N Cpost hmarked
  have Sendpoint : BankPaperCanonicalRoundedSelectorTangentInput
      R certificate fixed candidates B.partition.band cellIndex
      (bankPaperCanonicalActualP87PointwiseUpper B N Cpost)
      (tangentRatioCellTailPointwiseUpper
        (bankPaperCanonicalActualP87PointwiseUpper B N Cpost)
        B.partition.band cellIndex)
      endpoint := by
    exact bankPaperCanonicalRoundedSelectorTangentInput_of_balance_pointwise
      R certificate fixed candidates B.partition.band cellIndex
      (bankPaperCanonicalActualP87PointwiseUpper B N Cpost) endpoint
      hselector hrow hprimeBandBalance hsupport hbalance hpointwise
  refine ⟨path, endpoint, hpath, rfl, ?_, ?_, ?_, Sendpoint⟩
  · exact bankPaperCanonicalActualP87SelectorSupport_eq_candidates
      B candidates hvalues
  · intro p
    exact bankPaperCanonicalActualFullMarkedTarget_eq_selectorTailTarget
      B R certificate fixed candidates preSelector activeSeed p
  · intro x hx
    exact bankPaperCanonicalActualP87EndpointSelector_eq_zero_of_not_mem
      B candidates preSelector activeSeed hvalues path hx

namespace BankPaperRealization







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



/-! ## Canonical symmetric mass choices -/















/-! ## Exact finite coordinate capacity -/















end BankPaperRealization

end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankPaperCanonicalTwoZeroHeadCellHfitConnector -/
section


/-!
# Proposition 8.7 fit inputs for the two-zero-cell placement

This file discharges the finite inputs of the actual Proposition 8.7 call
which are forced by the already constructed placement.

There is one quantitative distinction which matters.  The final structured
placement uses the rebalanced seed, whereas the actual bridge keeps the
original scaled seed.  Consequently its frozen remainder is not literally
`betaProt / L` on a changed zero-head coordinate.  It is

`protected + rebalanced - original`.

The height increment is little-o of `n / log n`.  Applying the existing
cell-absorption theorem to its negative gives the missing upper estimate,
and hence the uniform frozen ledger `(betaProt + 1) / L`.

The final adapter also derives the integer quota, ambient frozen
feasibility, the choice `N = B.q`, the mass bound with `Cmass = 1`, and the
conversion of the selector residual into the literal initial marked
residual.  The target envelope, the primewise selector-residual rate, and
the active-coordinate `Cactive / L` estimate remain visible: the current
prebridge ledger deliberately does not constrain medium-prime moments, and
no uniform all-cell active-coordinate bound is hidden here.
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

/-! ## The missing upper half of the frozen height ledger -/







/-! ## The exact finite P87-tail adapter -/

/-- A selector-deficit estimate is exactly the initial marked estimate for
the actual tagged active target. -/
theorem bankPaperCanonicalActualInitialMarkedRate_of_selectorDeficit
    {Head Band : Type*} [Fintype Head] [DecidableEq Head]
    [Fintype Band] [DecidableEq Band] [Nonempty Head]
    (B : BridgeData Head Band)
    {c : Real} {depth : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (fixed candidates : Finset Nat) (preSelector : Nat -> Real)
    (activeSeed : B.sampleData.Sample -> Real)
    {T : BarycentricTarget B.sampleData}
    (Hmeasure : BankPaperCanonicalActualActiveMeasureConstructor
      B.sampleData T candidates preSelector activeSeed)
    (hseed : forall m, B.baseline.baseWeight m = activeSeed m)
    (Cinitial : Real)
    (hdeficit : ∀ p ∈
      primeBand B.sampleData.n B.sampleData.W,
      abs (bankPaperCanonicalSelectorValuationDeficit
        R certificate fixed candidates preSelector p) <=
          Cinitial * B.q / ((p : Real) * B.L)) :
    ∀ p ∈ primeBand B.sampleData.n B.sampleData.W,
      abs (bankPaperCanonicalActualActiveMarkedTarget
          B R certificate fixed candidates preSelector activeSeed p -
        B.paperMoment (B.markedValuation p) 0) <=
          Cinitial * B.q / ((p : Real) * B.L) := by
  intro p hp
  rw [← bankPaperCanonicalActualInitial_deficit_eq_activeResidual
    B R certificate fixed candidates preSelector activeSeed
      Hmeasure hseed p]
  exact hdeficit p hp

/-- Tail adapter for a local instance of canonical Proposition 8.7.

The argument `hP87` is precisely the local tail obtained after the global
canonical theorem has fixed its mesh, threshold, radius, and post-fit
constant and after the structural bridge hypotheses and active baseline
have been supplied.  This theorem removes every remaining finite premise
which follows from the actual-measure constructor and selector state.
-/
theorem exists_bankPaperCanonicalActualP87Conclusion_of_localCanonical
    {Head Band : Type*} [Fintype Head] [DecidableEq Head]
    [Fintype Band] [DecidableEq Band] [Nonempty Head]
    (B : BridgeData Head Band)
    {c : Real} {depth : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (fixed candidates : Finset Nat) (preSelector : Nat -> Real)
    (activeSeed : B.sampleData.Sample -> Real)
    {T : BarycentricTarget B.sampleData}
    (Hmeasure : BankPaperCanonicalActualActiveMeasureConstructor
      B.sampleData T candidates preSelector activeSeed)
    (hseed : forall m, B.baseline.baseWeight m = activeSeed m)
    (hselector : ∀ a ∈ candidates,
      0 <= preSelector a ∧ preSelector a <= 1)
    (hrow : BankPaperCanonicalSelectorRowIntegral
      B.sampleData.n candidates preSelector)
    (hhead : B.sampleData.HeadPatternsSeparated)
    (Ctarget Cinitial Cfixed Cactive : Real)
    (henv : B.HasTargetEnvelopes Ctarget
      (fun j => B.markedBandResidual
        (bankPaperCanonicalActualActiveMarkedTarget
          B R certificate fixed candidates preSelector activeSeed) 0 j))
    (hdeficit : ∀ p ∈
      primeBand B.sampleData.n B.sampleData.W,
      abs (bankPaperCanonicalSelectorValuationDeficit
        R certificate fixed candidates preSelector p) <=
          Cinitial * B.q / ((p : Real) * B.L))
    (hfrozenLedger : forall m : B.sampleData.Sample,
      BridgeData.frozenAmbientWeight
          (bankPaperCanonicalActualFrozenValue
            (candidates := candidates))
          (bankPaperCanonicalActualFrozenWeight
            B.sampleData candidates preSelector activeSeed)
          (B.sampleData.value m) <= Cfixed / B.L)
    (hactiveLedger : forall m : B.sampleData.Sample,
      B.baseline.baseWeight m <= Cactive / B.L)
    (radius : NNReal) (Cpost : Real)
    (hP87 :
      forall (Delta : Band -> Real),
        B.HasTargetEnvelopes Ctarget Delta ->
        forall (markedTarget : Nat -> Real) (N : Real),
          0 <= N ->
          B.q <= (1 : Real) * N ->
          (∀ p ∈ primeBand B.sampleData.n B.sampleData.W,
            abs (markedTarget p -
              B.paperMoment (B.markedValuation p) 0) <=
                Cinitial * N / ((p : Real) * B.L)) ->
          (forall j,
            Delta j = B.markedBandResidual markedTarget 0 j) ->
          forall {Fixed : Type} [Fintype Fixed]
            (fixedValue : Fixed -> Nat) (fixedWeight : Fixed -> Real)
            (quota : Int),
            (quota : Real) = (∑ f, fixedWeight f) + B.q ->
            B.sampleData.HeadPatternsSeparated ->
            (forall x,
              BridgeData.frozenAmbientWeight
                fixedValue fixedWeight x ∈ Icc (0 : Real) 1) ->
            (forall m : B.sampleData.Sample,
              BridgeData.frozenAmbientWeight fixedValue fixedWeight
                (B.sampleData.value m) <= Cfixed / B.L) ->
            (forall m : B.sampleData.Sample,
              B.baseline.baseWeight m <= Cactive / B.L) ->
            B.HasPaperProposition87Conclusion Delta radius
              markedTarget N Cpost fixedValue fixedWeight quota) :
    ∃ quota : Int,
      B.HasPaperProposition87Conclusion
        (fun j => B.markedBandResidual
          (bankPaperCanonicalActualActiveMarkedTarget
            B R certificate fixed candidates preSelector activeSeed) 0 j)
        radius
        (bankPaperCanonicalActualActiveMarkedTarget
          B R certificate fixed candidates preSelector activeSeed)
        B.q Cpost
        (bankPaperCanonicalActualFrozenValue (candidates := candidates))
        (bankPaperCanonicalActualFrozenWeight
          B.sampleData candidates preSelector activeSeed)
        quota := by
  obtain ⟨quota, hquotaLiteral⟩ :=
    exists_bankPaperCanonicalActualP87IntegerQuota Hmeasure hrow
  have hqLiteral :
      B.q = bankPaperCanonicalLiteralActiveMass
        B.sampleData activeSeed :=
    Erdos390.WholePaper.BridgeData.q_eq_literalActiveMass_of_baseWeight_eq_seed
      B activeSeed hseed
  have hquota :
      (quota : Real) =
        (∑ a : BankPaperCanonicalActualFrozenIndex candidates,
          bankPaperCanonicalActualFrozenWeight
            B.sampleData candidates preSelector activeSeed a) + B.q := by
    rw [hqLiteral]
    exact hquotaLiteral
  have hfrozenFeasible :
      forall x,
        BridgeData.frozenAmbientWeight
          (bankPaperCanonicalActualFrozenValue
            (candidates := candidates))
          (bankPaperCanonicalActualFrozenWeight
            B.sampleData candidates preSelector activeSeed) x ∈
          Icc (0 : Real) 1 :=
    bankPaperCanonicalActualFrozenWeight_mem_Icc Hmeasure hselector
  have hinitial :=
    bankPaperCanonicalActualInitialMarkedRate_of_selectorDeficit
      B R certificate fixed candidates preSelector activeSeed
        Hmeasure hseed Cinitial hdeficit
  refine ⟨quota, hP87
    (fun j => B.markedBandResidual
      (bankPaperCanonicalActualActiveMarkedTarget
        B R certificate fixed candidates preSelector activeSeed) 0 j)
    henv
    (bankPaperCanonicalActualActiveMarkedTarget
      B R certificate fixed candidates preSelector activeSeed)
    B.q B.q_pos.le (by simp) hinitial (fun _j => rfl)
    (Fixed := BankPaperCanonicalActualFrozenIndex candidates)
    (bankPaperCanonicalActualFrozenValue (candidates := candidates))
    (bankPaperCanonicalActualFrozenWeight
      B.sampleData candidates preSelector activeSeed)
    quota hquota hhead hfrozenFeasible hfrozenLedger hactiveLedger⟩

end BankPaperRealization

end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankPaperCanonicalTwoZeroHeadCellPostHfitConnector -/
section


/-!
# Post-Hfit handoff from Section 8 to Section 9

The two-zero-cell Hfit connector ends with the literal
`HasPaperProposition87Conclusion` required by the actual endpoint theorem.
This file performs that previously implicit composition.

The production theorems below first obtain the integer quota and Hfit
conclusion from the local canonical Proposition 8.7 tail.  They then return
the actual P87 path, its pushed-forward selector, and
`BankPaperCanonicalRoundedSelectorTangentInput`.  The latter is exactly the
selector input `S` of
`exists_canonicalDistributedSectionNinePostTangentOutput_of_paperBudgets_on_candidates`.
The split-seed overload uses the weaker row-integral/deficit-supported
endpoint eliminator so that the structured placement may use a rebalanced
seed while the actual bridge measure retains its original baseline seed.

No Section 9 collision, endpoint-slack, occupied-cell, or analytic budget
premise is hidden here; those remain obligations of the downstream assembly.
-/

open Set
open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.PaperBridgeFit
open Erdos390.Full.PaperGuardCensus

noncomputable section

namespace BankPaperRealization



/-- Split-seed form of the local canonical Post-Hfit handoff.

The structured placement selector is built from `placementSeed`, while the
actual active measure, bridge baseline, marked target, frozen weights, P87
path, and pushed-forward endpoint all retain `activeSeed`.  This is the
literal interface needed by the two-zero-cell construction: its placement
uses the rebalanced seed, whereas its actual bridge measure remains based on
the original scaled barycentric seed.

Only the row-integrality and outside-band deficit-support fields are
extracted from the placement predicate.  The endpoint is then produced by
the weaker row-integral/deficit-supported eliminator, so no equality between
the two seeds is assumed or hidden. -/
theorem
    exists_bankPaperCanonicalActualP87EndpointSelector_of_localCanonical_structuredAdditivePlacement_splitSeed
    {Head Band : Type*} [Fintype Head] [DecidableEq Head]
    [Fintype Band] [DecidableEq Band] [Nonempty Head]
    (B : BridgeData Head Band)
    {c : Real} {depth K : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (fixed : Finset Nat) (deltaStar betaProt : Real)
    (baseSelector : Nat -> Real)
    (placementSeed activeSeed : B.sampleData.Sample -> Real)
    {T : BarycentricTarget B.sampleData}
    (Hmeasure : BankPaperCanonicalActualActiveMeasureConstructor
      B.sampleData T
      (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
      (bankPaperCanonicalGuardedStructuredAdditivePlacementSelector (K := K)
        B R certificate deltaStar betaProt baseSelector placementSeed)
      activeSeed)
    (hseed : forall m, B.baseline.baseWeight m = activeSeed m)
    (Hplacement : BankPaperCanonicalGuardedStructuredAdditivePlacement (K := K)
      B R certificate fixed deltaStar betaProt baseSelector placementSeed)
    (hhead : B.sampleData.HeadPatternsSeparated)
    (Ctarget Cinitial Cfixed Cactive : Real)
    (henv : B.HasTargetEnvelopes Ctarget
      (fun j => B.markedBandResidual
        (bankPaperCanonicalActualActiveMarkedTarget B R certificate fixed
          (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
          (bankPaperCanonicalGuardedStructuredAdditivePlacementSelector
            (K := K) B R certificate deltaStar betaProt baseSelector
              placementSeed)
          activeSeed) 0 j))
    (hdeficit : ∀ p ∈ primeBand B.sampleData.n B.sampleData.W,
      abs (bankPaperCanonicalSelectorValuationDeficit
        R certificate fixed
          (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
          (bankPaperCanonicalGuardedStructuredAdditivePlacementSelector
            (K := K) B R certificate deltaStar betaProt baseSelector
              placementSeed) p) <=
        Cinitial * B.q / ((p : Real) * B.L))
    (hfrozenLedger : forall m : B.sampleData.Sample,
      BridgeData.frozenAmbientWeight
          (bankPaperCanonicalActualFrozenValue
            (candidates :=
              R.roughCanonicalGuardedCandidateSet certificate deltaStar K))
          (bankPaperCanonicalActualFrozenWeight B.sampleData
            (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
            (bankPaperCanonicalGuardedStructuredAdditivePlacementSelector
              (K := K) B R certificate deltaStar betaProt baseSelector
                placementSeed)
            activeSeed)
          (B.sampleData.value m) <= Cfixed / B.L)
    (hactiveLedger : forall m : B.sampleData.Sample,
      B.baseline.baseWeight m <= Cactive / B.L)
    (radius : NNReal) (Cpost : Real)
    (hP87 :
      forall (Delta : Band -> Real),
        B.HasTargetEnvelopes Ctarget Delta ->
        forall (markedTarget : Nat -> Real) (N : Real),
          0 <= N ->
          B.q <= (1 : Real) * N ->
          (∀ p ∈ primeBand B.sampleData.n B.sampleData.W,
            abs (markedTarget p -
              B.paperMoment (B.markedValuation p) 0) <=
                Cinitial * N / ((p : Real) * B.L)) ->
          (forall j,
            Delta j = B.markedBandResidual markedTarget 0 j) ->
          forall {Fixed : Type} [Fintype Fixed]
            (fixedValue : Fixed -> Nat) (fixedWeight : Fixed -> Real)
            (quota : Int),
            (quota : Real) = (∑ f, fixedWeight f) + B.q ->
            B.sampleData.HeadPatternsSeparated ->
            (forall x,
              BridgeData.frozenAmbientWeight
                fixedValue fixedWeight x ∈ Icc (0 : Real) 1) ->
            (forall m : B.sampleData.Sample,
              BridgeData.frozenAmbientWeight fixedValue fixedWeight
                (B.sampleData.value m) <= Cfixed / B.L) ->
            (forall m : B.sampleData.Sample,
              B.baseline.baseWeight m <= Cactive / B.L) ->
            B.HasPaperProposition87Conclusion Delta radius
              markedTarget N Cpost fixedValue fixedWeight quota)
    (cellIndex : BankPaperCanonicalTangentPrime
      B.sampleData.n B.sampleData.W -> Nat) :
    ∃ quota : Int, ∃ path : Real -> B.ParamSpace,
    ∃ endpoint : Nat -> Real,
      B.HasPaperProposition87Conclusion
          (fun j => B.markedBandResidual
            (bankPaperCanonicalActualActiveMarkedTarget B R certificate fixed
              (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
              (bankPaperCanonicalGuardedStructuredAdditivePlacementSelector
                (K := K) B R certificate deltaStar betaProt baseSelector
                  placementSeed)
              activeSeed) 0 j)
          radius
          (bankPaperCanonicalActualActiveMarkedTarget B R certificate fixed
            (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
            (bankPaperCanonicalGuardedStructuredAdditivePlacementSelector
              (K := K) B R certificate deltaStar betaProt baseSelector
                placementSeed)
            activeSeed)
          B.q Cpost
          (bankPaperCanonicalActualFrozenValue
            (candidates :=
              R.roughCanonicalGuardedCandidateSet certificate deltaStar K))
          (bankPaperCanonicalActualFrozenWeight B.sampleData
            (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
            (bankPaperCanonicalGuardedStructuredAdditivePlacementSelector
              (K := K) B R certificate deltaStar betaProt baseSelector
                placementSeed)
            activeSeed)
          quota ∧
      B.IsPaperProposition87Path
          (fun j => B.markedBandResidual
            (bankPaperCanonicalActualActiveMarkedTarget B R certificate fixed
              (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
              (bankPaperCanonicalGuardedStructuredAdditivePlacementSelector
                (K := K) B R certificate deltaStar betaProt baseSelector
                  placementSeed)
              activeSeed) 0 j)
          radius
          (bankPaperCanonicalActualActiveMarkedTarget B R certificate fixed
            (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
            (bankPaperCanonicalGuardedStructuredAdditivePlacementSelector
              (K := K) B R certificate deltaStar betaProt baseSelector
                placementSeed)
            activeSeed)
          B.q Cpost
          (bankPaperCanonicalActualFrozenValue
            (candidates :=
              R.roughCanonicalGuardedCandidateSet certificate deltaStar K))
          (bankPaperCanonicalActualFrozenWeight B.sampleData
            (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
            (bankPaperCanonicalGuardedStructuredAdditivePlacementSelector
              (K := K) B R certificate deltaStar betaProt baseSelector
                placementSeed)
            activeSeed)
          quota path ∧
      endpoint =
        bankPaperCanonicalActualP87EndpointSelector B
          (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
          (bankPaperCanonicalGuardedStructuredAdditivePlacementSelector
            (K := K) B R certificate deltaStar betaProt baseSelector
              placementSeed)
          activeSeed path ∧
      BankPaperCanonicalRoundedSelectorTangentInput R certificate fixed
        (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
        B.partition.band cellIndex
        (bankPaperCanonicalActualP87PointwiseUpper B B.q Cpost)
        (tangentRatioCellTailPointwiseUpper
          (bankPaperCanonicalActualP87PointwiseUpper B B.q Cpost)
          B.partition.band cellIndex)
        endpoint := by
  have hplacement := Hplacement
  unfold BankPaperCanonicalGuardedStructuredAdditivePlacement at hplacement
  obtain ⟨quota, Hfit⟩ :=
    exists_bankPaperCanonicalActualP87Conclusion_of_localCanonical
      B R certificate fixed
      (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
      (bankPaperCanonicalGuardedStructuredAdditivePlacementSelector (K := K)
        B R certificate deltaStar betaProt baseSelector placementSeed)
      activeSeed Hmeasure hseed hplacement.1 hplacement.2.1 hhead
      Ctarget Cinitial Cfixed Cactive henv hdeficit
      hfrozenLedger hactiveLedger radius Cpost hP87
  obtain
      ⟨path, endpoint, hpath, hendpoint, _hsupport, _htarget,
        _houtside, Sendpoint⟩ :=
    exists_bankPaperCanonicalActualP87EndpointSelector_of_rowIntegral_deficitSupported
      B R certificate fixed
      (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
      (bankPaperCanonicalGuardedStructuredAdditivePlacementSelector (K := K)
        B R certificate deltaStar betaProt baseSelector placementSeed)
      activeSeed Hmeasure hseed hplacement.2.1 hplacement.2.2
      (fun j => B.markedBandResidual
        (bankPaperCanonicalActualActiveMarkedTarget B R certificate fixed
          (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
          (bankPaperCanonicalGuardedStructuredAdditivePlacementSelector
            (K := K) B R certificate deltaStar betaProt baseSelector
              placementSeed)
          activeSeed) 0 j)
      radius B.q Cpost quota Hfit cellIndex
  exact ⟨quota, path, endpoint, Hfit, hpath, hendpoint, Sendpoint⟩

end BankPaperRealization

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

/-- Head-pattern separation transports an arbitrary pointwise seed upper
bound to its ambient push-forward.  Unlike the older bridge-baseline lemma,
this form applies directly to a rebalanced placement seed. -/
theorem bankPaperCanonicalActiveSeedAmbientWeight_le_of_pointwise
    {Head Band : Type*} [Fintype Head] [DecidableEq Head]
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData Head Band)
    (hsep : B.sampleData.HeadPatternsSeparated)
    (seed : B.sampleData.Sample -> Real)
    (Cactive : Real) (hCactive : 0 <= Cactive)
    (hseedUpper : forall m : B.sampleData.Sample,
      seed m <= Cactive / B.L) :
    forall a : Nat,
      bankPaperCanonicalActiveSeedAmbientWeight
          B.sampleData seed a <= Cactive / B.L := by
  intro a
  by_cases ha : exists m : B.sampleData.Sample,
      B.sampleData.value m = a
  · obtain ⟨m, rfl⟩ := ha
    calc
      bankPaperCanonicalActiveSeedAmbientWeight B.sampleData seed
          (B.sampleData.value m) =
        seed m :=
          bankPaperCanonicalActiveSeedAmbientWeight_eq_of_value_of_headPatternsSeparated
            B.sampleData seed hsep m
      _ <= Cactive / B.L := hseedUpper m
  · rw [bankPaperCanonicalActiveSeedAmbientWeight_eq_zero_of_not_value
      B.sampleData seed a (fun m hm => ha ⟨m, hm⟩)]
    exact div_nonneg hCactive B.L_pos.le







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

/-- On every nonsmooth guarded row, changing the structured active seed is
pointwise invisible.  Active nonexceptional rows use the same corrected
weight for both seeds, while exceptional rows are zero for both seeds. -/
theorem bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop_eq_of_mem_nonsmoothRow
    {P : Finset Nat} {Band : Type*}
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData (PaperHeadSimplex.Tag P) Band)
    {c : Real} {depth K label : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (deltaStar betaProt alpha betaTotal : Real)
    (oldSeed₁ oldSeed₂ : B.sampleData.Sample -> Real) {a : Nat}
    (hlabel : label ≠ 1)
    (ha : a ∈ R.roughCanonicalGuardedRow certificate deltaStar K label) :
    bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop (K := K)
        B R certificate deltaStar betaProt alpha betaTotal oldSeed₁ a =
      bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop (K := K)
        B R certificate deltaStar betaProt alpha betaTotal oldSeed₂ a := by
  have haLabel :
      completeRoughLabel (yNat B.sampleData.n) a = label :=
    (mem_completeRoughRowFiber.mp ha).2
  have hnotSmoothPool :
      a ∉ R.roughCanonicalGuardedBroadCorrectionPool certificate
        deltaStar B.sampleData.W K 1 := by
    intro haSmooth
    have haSmoothRow :
        a ∈ R.roughCanonicalGuardedRow certificate deltaStar K 1 :=
      R.roughCanonicalGuardedBroadCorrectionPool_subset_guardedRow
        certificate deltaStar B.sampleData.W K 1 haSmooth
    have haSmoothLabel :
        completeRoughLabel (yNat B.sampleData.n) a = 1 :=
      (mem_completeRoughRowFiber.mp haSmoothRow).2
    exact hlabel (haLabel.symm.trans haSmoothLabel)
  simp only [bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop,
    bankPaperCanonicalTwoZeroHeadCellSourceSelector, hnotSmoothPool,
    if_false, bankPaperCanonicalGlobalCorrectedOutsideSelectorWithTop,
    haLabel, hlabel]

/-- On an active nonexceptional nonsmooth guarded row, the frozen-top source
is the explicit postcharge corrected row weight. -/
theorem bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop_apply_of_mem_nonsmoothRow
    {P : Finset Nat} {Band : Type*}
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData (PaperHeadSimplex.Tag P) Band)
    {c : Real} {depth K label : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (deltaStar betaProt alpha betaTotal : Real)
    (oldSeed : B.sampleData.Sample -> Real) {a : Nat}
    (hactive :
      RoughCanonicalActiveNonexceptionalLabel
        B.sampleData.n deltaStar label)
    (ha : a ∈ R.roughCanonicalGuardedRow certificate deltaStar K label) :
    bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop (K := K)
        B R certificate deltaStar betaProt alpha betaTotal oldSeed a =
      R.roughCanonicalGuardedPostchargeRowCorrectedWeight certificate
        deltaStar B.sampleData.W K label alpha betaTotal B.L a := by
  have haLabel :
      completeRoughLabel (yNat B.sampleData.n) a = label :=
    (mem_completeRoughRowFiber.mp ha).2
  have hnotSmoothPool :
      a ∉ R.roughCanonicalGuardedBroadCorrectionPool certificate
        deltaStar B.sampleData.W K 1 := by
    intro haSmooth
    have haSmoothRow :
        a ∈ R.roughCanonicalGuardedRow certificate deltaStar K 1 :=
      R.roughCanonicalGuardedBroadCorrectionPool_subset_guardedRow
        certificate deltaStar B.sampleData.W K 1 haSmooth
    have haSmoothLabel :
        completeRoughLabel (yNat B.sampleData.n) a = 1 :=
      (mem_completeRoughRowFiber.mp haSmoothRow).2
    exact hactive.1 (haLabel.symm.trans haSmoothLabel)
  have haNotOne :
      completeRoughLabel (yNat B.sampleData.n) a ≠ 1 := by
    intro haOne
    exact hactive.1 (haLabel.symm.trans haOne)
  have hnonexceptional :
      ¬ RoughCanonicalExceptionalLabel
        B.sampleData.n deltaStar label :=
    not_lt_of_ge hactive.2
  unfold bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop
  unfold bankPaperCanonicalTwoZeroHeadCellSourceSelector
  rw [if_neg hnotSmoothPool]
  unfold bankPaperCanonicalGlobalCorrectedOutsideSelectorWithTop
  rw [if_neg haNotOne, haLabel, if_neg hnonexceptional]



/-- Replacing `qTilde` by `q0` is pointwise invisible on every nonsmooth
guarded row. -/
theorem bankPaperCanonicalTopFrozenRoundedSourceSelector_eq_qTildeSource_of_mem_nonsmoothRow
    {P : Finset Nat} {Band : Type*}
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData (PaperHeadSimplex.Tag P) Band)
    {c : Real} {depth K label : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (T : BarycentricTarget B.sampleData)
    (deltaStar betaProt alpha betaTotal qTilde : Real)
    {a : Nat} (hlabel : label ≠ 1)
    (ha : a ∈ R.roughCanonicalGuardedRow certificate deltaStar K label) :
    bankPaperCanonicalTopFrozenRoundedSourceSelector (K := K)
        B R certificate T deltaStar betaProt alpha betaTotal qTilde a =
      bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop (K := K)
        B R certificate deltaStar betaProt alpha betaTotal
          (bankPaperCanonicalScaledActiveSeed T qTilde) a := by
  unfold bankPaperCanonicalTopFrozenRoundedSourceSelector
  exact
    bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop_eq_of_mem_nonsmoothRow
      (K := K) B R certificate deltaStar betaProt alpha betaTotal
        (bankPaperCanonicalTopFrozenRoundedActiveSeed (K := K)
          B R certificate T deltaStar betaProt alpha qTilde)
        (bankPaperCanonicalScaledActiveSeed T qTilde) hlabel ha

/-! ## Exact smooth and nonsmooth row ledgers -/

/-- The two zero-head corrections replace the literal active mass
`qTilde` by exactly `q0`. -/
theorem bankPaperCanonicalLiteralActiveMass_topFrozenRoundedActiveSeed
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
    (deltaStar betaProt alpha qTilde : Real) :
    bankPaperCanonicalLiteralActiveMass B.sampleData
        (bankPaperCanonicalTopFrozenRoundedActiveSeed (K := K)
          B R certificate T deltaStar betaProt alpha qTilde) =
      bankPaperCanonicalTopFrozenRoundedActiveMass (K := K)
        B R certificate deltaStar betaProt alpha qTilde := by
  unfold bankPaperCanonicalTopFrozenRoundedActiveSeed
  rw [bankPaperCanonicalLiteralActiveMass_rebalancedScaledActiveSeed]
  unfold bankPaperCanonicalTopFrozenNearestIntegerCellMass
  ring









/-! ## Exact feasibility transport through the two zero cells -/



/-! ## Complete-row integrality and the source-state handoff -/







end BankPaperRealization

end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankPaperCanonicalArbitrarySourcePostHfitConnector -/
section


/-!
# Post-Hfit production from an arbitrary verified source

The original Post-Hfit connector fixes
`bankPaperCanonicalPostHfitGlobalSourceSelector` in both its placement and
its output package.  This file separates the part of that construction which
only needs a verified selector source state from the identities special to
that old source.

For an arbitrary `sourceSelector`, the exact additional inputs are:

* the signed whole-smooth-row prebridge ledger for `placementSeed`;
* pointwise feasibility of the resulting structured placement; and
* the nonsmooth-row identification of the source.

The source state supplies row integrality and exact agreement outside the
medium-prime band.  The prebridge theorem transports those two fields to the
structured placement.  Everything after that point--Proposition 8.7, the
split-seed endpoint, the rounded tangent input, and endpoint slack--is
source-agnostic.

The final section specializes this producer to the frozen-top
nearest-integer selector.  Its nonsmooth-row identification is proved here,
so the specialization does not route through the older no-top global source.
-/

open Set
open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.PaperBridgeFit
open Erdos390.Full.PaperGuardCensus

noncomputable section

namespace BankPaperRealization

/-! ## Source-parameterized preselector and package -/





/-! ## Generic slack inputs -/

/-- On the smooth correction pool, the structured placement has the same
`O(1/L)` upper bound for every base selector.  The base selector is
overwritten on that pool, so no source-specific identity is used. -/
theorem bankPaperCanonicalPostHfitStructuredPreSelectorOfSource_hpreUpper
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
    (deltaStar betaProt : Real)
    (sourceSelector : Nat -> Real)
    (placementSeed : B.sampleData.Sample -> Real)
    (hsep : B.sampleData.HeadPatternsSeparated)
    (Cplacement : Real) (hCplacement : 0 <= Cplacement)
    (hplacementSeedUpper : forall m : B.sampleData.Sample,
      placementSeed m <= Cplacement / B.L)
    (Cfixed : Real) (hfixed : betaProt + Cplacement <= Cfixed) :
    ∀ a ∈ R.roughCanonicalGuardedBroadCorrectionPool certificate
        deltaStar B.sampleData.W K 1,
      bankPaperCanonicalPostHfitStructuredPreSelectorOfSource (K := K)
          B R certificate deltaStar betaProt sourceSelector placementSeed a <=
        Cfixed / B.L := by
  intro a ha
  rw [bankPaperCanonicalPostHfitStructuredPreSelectorOfSource,
    bankPaperCanonicalGuardedStructuredAdditivePlacementSelector_eq_refinement_of_mem_pool
      B R certificate sourceSelector placementSeed ha,
    bankPaperCanonicalGuardedSmoothAdditiveRefinement_apply_of_mem
      B R certificate sourceSelector placementSeed ha]
  have hambient :=
    bankPaperCanonicalActiveSeedAmbientWeight_le_of_pointwise
      B hsep placementSeed Cplacement hCplacement hplacementSeedUpper a
  calc
    betaProt / B.L +
          bankPaperCanonicalActiveSeedAmbientWeight
            B.sampleData placementSeed a <=
        betaProt / B.L + Cplacement / B.L :=
      add_le_add le_rfl hambient
    _ = (betaProt + Cplacement) / B.L := by ring
    _ <= Cfixed / B.L :=
      div_le_div_of_nonneg_right hfixed B.L_pos.le

/-- A source identity on nonsmooth active rows passes unchanged through the
structured placement, provided the structured active image is contained in
the smooth row. -/
theorem bankPaperCanonicalPostHfitStructuredPreSelectorOfSource_hpreNonsmooth
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
    (deltaStar betaProt alpha beta : Real)
    (sourceSelector : Nat -> Real)
    (placementSeed : B.sampleData.Sample -> Real)
    (hactiveSmooth :
      bankPaperCanonicalStructuredActiveValues B.sampleData ⊆
        R.roughCanonicalGuardedRow certificate deltaStar K 1)
    (hsourceNonsmooth : forall label,
      RoughCanonicalActiveNonexceptionalLabel
          B.sampleData.n deltaStar label ->
        ∀ a ∈ R.roughCanonicalGuardedBroadCorrectionPool certificate
            deltaStar B.sampleData.W K label,
          sourceSelector a =
            R.roughCanonicalGuardedPostchargeRowCorrectedWeight certificate
              deltaStar B.sampleData.W K label alpha beta B.L a) :
    forall label,
      RoughCanonicalActiveNonexceptionalLabel
          B.sampleData.n deltaStar label ->
        ∀ a ∈ R.roughCanonicalGuardedBroadCorrectionPool certificate
            deltaStar B.sampleData.W K label,
          bankPaperCanonicalPostHfitStructuredPreSelectorOfSource (K := K)
                B R certificate deltaStar betaProt
                  sourceSelector placementSeed a =
            R.roughCanonicalGuardedPostchargeRowCorrectedWeight certificate
              deltaStar B.sampleData.W K label alpha beta B.L a := by
  intro label hlabel a ha
  have hnotSmoothRow :
      a ∉ R.roughCanonicalGuardedRow certificate deltaStar K 1 :=
    R.roughCanonicalGuardedBroadCorrectionPool_not_mem_smoothRow_of_ne_one
      certificate hlabel.1 ha
  rw [bankPaperCanonicalPostHfitStructuredPreSelectorOfSource,
    bankPaperCanonicalGuardedStructuredAdditivePlacementSelector_eq_base_outside_smoothRow
      B R certificate sourceSelector placementSeed hactiveSmooth
        hnotSmoothRow]
  exact hsourceNonsmooth label hlabel a ha

/-! ## Arbitrary-source producer -/

/-- Produce the exact Post-Hfit endpoint and slack package from any verified
selector source state.

The source state is used, rather than merely carried: its row-integrality
and outside-band support fields are transported across the supplied signed
prebridge ledger. -/
theorem
    exists_bankPaperCanonicalPostHfitGuardedSlackPackageOfSource_of_sourceState
    {Head Band : Type*} [Fintype Head] [DecidableEq Head]
    [Fintype Band] [DecidableEq Band] [Nonempty Head]
    (B : BridgeData Head Band)
    {c : Real} {depth K : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (fixed : Finset Nat)
    (deltaStar betaProt alpha beta sigma : Real)
    (sourceSelector : Nat -> Real)
    (placementSeed activeSeed : B.sampleData.Sample -> Real)
    (Ssource : BankPaperCanonicalSelectorSourceState
      (W := B.sampleData.W) R certificate fixed
      (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
      sourceSelector)
    (hplacedFeasible : ∀ a ∈
      R.roughCanonicalGuardedCandidateSet certificate deltaStar K,
      0 <= bankPaperCanonicalPostHfitStructuredPreSelectorOfSource (K := K)
          B R certificate deltaStar betaProt
            sourceSelector placementSeed a ∧
        bankPaperCanonicalPostHfitStructuredPreSelectorOfSource (K := K)
          B R certificate deltaStar betaProt
            sourceSelector placementSeed a <= 1)
    (hprebridge :
      BankPaperCanonicalGuardedStructuredAdditivePrebridgeMomentLedger
        (K := K) B R certificate deltaStar betaProt
          sourceSelector placementSeed)
    (hsourceNonsmooth : forall label,
      RoughCanonicalActiveNonexceptionalLabel
          B.sampleData.n deltaStar label ->
        ∀ a ∈ R.roughCanonicalGuardedBroadCorrectionPool certificate
            deltaStar B.sampleData.W K label,
          sourceSelector a =
            R.roughCanonicalGuardedPostchargeRowCorrectedWeight certificate
              deltaStar B.sampleData.W K label alpha beta B.L a)
    {T : BarycentricTarget B.sampleData}
    (Hmeasure : BankPaperCanonicalActualActiveMeasureConstructor
      B.sampleData T
      (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
      (bankPaperCanonicalPostHfitStructuredPreSelectorOfSource (K := K)
        B R certificate deltaStar betaProt sourceSelector placementSeed)
      activeSeed)
    (hseed : forall m, B.baseline.baseWeight m = activeSeed m)
    (hsep : B.sampleData.HeadPatternsSeparated)
    (Ctarget Cinitial Cfixed Cactive : Real)
    (henv : B.HasTargetEnvelopes Ctarget
      (fun j => B.markedBandResidual
        (bankPaperCanonicalActualActiveMarkedTarget B R certificate fixed
          (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
          (bankPaperCanonicalPostHfitStructuredPreSelectorOfSource (K := K)
            B R certificate deltaStar betaProt
              sourceSelector placementSeed)
          activeSeed) 0 j))
    (hdeficit : ∀ p ∈ primeBand B.sampleData.n B.sampleData.W,
      abs (bankPaperCanonicalSelectorValuationDeficit
        R certificate fixed
          (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
          (bankPaperCanonicalPostHfitStructuredPreSelectorOfSource (K := K)
            B R certificate deltaStar betaProt
              sourceSelector placementSeed) p) <=
        Cinitial * B.q / ((p : Real) * B.L))
    (hfrozenLedger : forall m : B.sampleData.Sample,
      BridgeData.frozenAmbientWeight
          (bankPaperCanonicalActualFrozenValue
            (candidates :=
              R.roughCanonicalGuardedCandidateSet certificate deltaStar K))
          (bankPaperCanonicalActualFrozenWeight B.sampleData
            (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
            (bankPaperCanonicalPostHfitStructuredPreSelectorOfSource (K := K)
              B R certificate deltaStar betaProt
                sourceSelector placementSeed)
            activeSeed)
          (B.sampleData.value m) <= Cfixed / B.L)
    (hactiveLedger : forall m : B.sampleData.Sample,
      B.baseline.baseWeight m <= Cactive / B.L)
    (radius : NNReal) (Cpost : Real)
    (hP87 :
      forall (Delta : Band -> Real),
        B.HasTargetEnvelopes Ctarget Delta ->
        forall (markedTarget : Nat -> Real) (N : Real),
          0 <= N ->
          B.q <= (1 : Real) * N ->
          (∀ p ∈ primeBand B.sampleData.n B.sampleData.W,
            abs (markedTarget p -
              B.paperMoment (B.markedValuation p) 0) <=
                Cinitial * N / ((p : Real) * B.L)) ->
          (forall j,
            Delta j = B.markedBandResidual markedTarget 0 j) ->
          forall {Fixed : Type} [Fintype Fixed]
            (fixedValue : Fixed -> Nat) (fixedWeight : Fixed -> Real)
            (quota : Int),
            (quota : Real) = (∑ f, fixedWeight f) + B.q ->
            B.sampleData.HeadPatternsSeparated ->
            (forall x,
              BridgeData.frozenAmbientWeight
                fixedValue fixedWeight x ∈ Icc (0 : Real) 1) ->
            (forall m : B.sampleData.Sample,
              BridgeData.frozenAmbientWeight fixedValue fixedWeight
                (B.sampleData.value m) <= Cfixed / B.L) ->
            (forall m : B.sampleData.Sample,
              B.baseline.baseWeight m <= Cactive / B.L) ->
            B.HasPaperProposition87Conclusion Delta radius
              markedTarget N Cpost fixedValue fixedWeight quota)
    (cellIndex : BankPaperCanonicalTangentPrime
      B.sampleData.n B.sampleData.W -> Nat)
    (Cplacement : Real) (hCplacement : 0 <= Cplacement)
    (hplacementSeedUpper : forall m : B.sampleData.Sample,
      placementSeed m <= Cplacement / B.L)
    (hfixed : betaProt + Cplacement <= Cfixed)
    (C : Real) (hC : 1 <= C) (hW : 1 < B.sampleData.W)
    (hhi : forall sign,
      B.sampleData.hi sign <= physicalBound C B.sampleData.n)
    (hCactive : 0 <= Cactive)
    (hprotectedReserve : ∀ x ∈
      R.roughCanonicalGuardedBroadCorrectionPool certificate
        deltaStar B.sampleData.W K 1,
      sigma / B.L +
          bankPaperCanonicalActiveSeedAmbientWeight
            B.sampleData activeSeed x <=
        bankPaperCanonicalPostHfitStructuredPreSelectorOfSource (K := K)
          B R certificate deltaStar betaProt
            sourceSelector placementSeed x)
    (hlarge : Cfixed +
        Real.exp (2 *
          ((Erdos390.Full.PaperStatisticNorm.valuationLogCoefficient
              C B.sampleData.W +
            B.nuisanceStatisticCoefficient C) *
              (3 * (radius : Real)))) * Cactive + sigma <= B.L)
    (hnonsmoothBounds : forall label,
      RoughCanonicalActiveNonexceptionalLabel
          B.sampleData.n deltaStar label ->
        sigma / B.L +
            |R.roughCanonicalGuardedPostchargeCorrectionDensity certificate
              deltaStar B.sampleData.W K label alpha beta B.L| <=
          beta / B.L ∧
        beta / B.L +
            |R.roughCanonicalGuardedPostchargeCorrectionDensity certificate
              deltaStar B.sampleData.W K label alpha beta B.L| <=
          1 - sigma / B.L) :
    ∃ quota : Int, ∃ path : Real -> B.ParamSpace,
    ∃ endpoint : Nat -> Real,
      BankPaperCanonicalPostHfitGuardedSlackPackageOfSource (K := K)
        B R certificate fixed deltaStar betaProt alpha beta sigma
          sourceSelector placementSeed activeSeed radius Cpost cellIndex
          quota path endpoint := by
  have Hplacement :
      BankPaperCanonicalGuardedStructuredAdditivePlacement (K := K)
        B R certificate fixed deltaStar betaProt
          sourceSelector placementSeed := by
    exact
      bankPaperCanonicalGuardedStructuredAdditivePlacement_of_prebridgeMomentLedger
        B R certificate fixed sourceSelector placementSeed
          hplacedFeasible Ssource.rowIntegral
            Ssource.deficitSupportedOnPrimeBand hprebridge
  have hpreUpper :=
    bankPaperCanonicalPostHfitStructuredPreSelectorOfSource_hpreUpper
      (K := K) B R certificate deltaStar betaProt sourceSelector
        placementSeed hsep Cplacement hCplacement hplacementSeedUpper
        Cfixed hfixed
  have hpreNonsmooth :=
    bankPaperCanonicalPostHfitStructuredPreSelectorOfSource_hpreNonsmooth
      (K := K) B R certificate deltaStar betaProt alpha beta
        sourceSelector placementSeed hprebridge.1 hsourceNonsmooth
  obtain ⟨quota, path, endpoint, Hfit, Hpath, hendpoint, Sendpoint⟩ :=
    exists_bankPaperCanonicalActualP87EndpointSelector_of_localCanonical_structuredAdditivePlacement_splitSeed
      (K := K) B R certificate fixed deltaStar betaProt
        sourceSelector placementSeed activeSeed Hmeasure hseed
        Hplacement hsep Ctarget Cinitial Cfixed Cactive henv hdeficit
        hfrozenLedger hactiveLedger radius Cpost hP87 cellIndex
  have hactiveSeed : forall m : B.sampleData.Sample,
      activeSeed m <= Cactive / B.L := by
    intro m
    rw [← hseed m]
    exact hactiveLedger m
  have HslackActual :=
    bankPaperCanonicalActualP87EndpointSelector_guardedSlackConstruction_of_reserve
      (K := K) B R certificate deltaStar alpha beta
      (bankPaperCanonicalPostHfitStructuredPreSelectorOfSource (K := K)
        B R certificate deltaStar betaProt sourceSelector placementSeed)
      activeSeed Hmeasure hseed
      (fun j => B.markedBandResidual
        (bankPaperCanonicalActualActiveMarkedTarget B R certificate fixed
          (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
          (bankPaperCanonicalPostHfitStructuredPreSelectorOfSource (K := K)
            B R certificate deltaStar betaProt
              sourceSelector placementSeed)
          activeSeed) 0 j)
      radius
      (bankPaperCanonicalActualActiveMarkedTarget B R certificate fixed
        (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
        (bankPaperCanonicalPostHfitStructuredPreSelectorOfSource (K := K)
          B R certificate deltaStar betaProt sourceSelector placementSeed)
        activeSeed)
      B.q Cpost quota path Hpath C sigma Cfixed Cactive
      hC hW hhi hsep hCactive hactiveSeed hprotectedReserve hpreUpper
      hlarge hnonsmoothBounds hpreNonsmooth
  have Hslack :
      R.BankPaperCanonicalGuardedEndpointSlackConstruction certificate
        deltaStar B.sampleData.W K alpha beta B.L sigma endpoint := by
    rw [hendpoint]
    exact HslackActual
  refine ⟨quota, path, endpoint, ?_⟩
  unfold BankPaperCanonicalPostHfitGuardedSlackPackageOfSource
  exact ⟨Hplacement, Hfit, Hpath, hendpoint, Sendpoint, Hslack⟩

/-! ## Frozen-top rounded specialization -/





/-- The nearest-integer frozen-top source has the exact nonsmooth identity
required by the source-parameterized Post-Hfit producer. -/
theorem bankPaperCanonicalTopFrozenRoundedSourceSelector_hsourceNonsmooth
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
    (deltaStar betaProt alpha beta qTilde : Real) :
    forall label,
      RoughCanonicalActiveNonexceptionalLabel
          B.sampleData.n deltaStar label ->
        ∀ a ∈ R.roughCanonicalGuardedBroadCorrectionPool certificate
            deltaStar B.sampleData.W K label,
          bankPaperCanonicalTopFrozenRoundedSourceSelector (K := K)
                B R certificate T deltaStar betaProt alpha beta qTilde a =
            R.roughCanonicalGuardedPostchargeRowCorrectedWeight certificate
              deltaStar B.sampleData.W K label alpha beta B.L a := by
  intro label hlabel a ha
  have haRow :
      a ∈ R.roughCanonicalGuardedRow certificate deltaStar K label :=
    R.roughCanonicalGuardedBroadCorrectionPool_subset_guardedRow
      certificate deltaStar B.sampleData.W K label ha
  simpa only [bankPaperCanonicalTopFrozenRoundedSourceSelector] using
    (bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop_apply_of_mem_nonsmoothRow
      (K := K) B R certificate deltaStar betaProt alpha beta
        (bankPaperCanonicalTopFrozenRoundedActiveSeed (K := K)
          B R certificate T deltaStar betaProt alpha qTilde)
        hlabel haRow)

/-- Run Post-Hfit directly from the verified nearest-integer frozen-top
source state.  No equality with
`bankPaperCanonicalPostHfitGlobalSourceSelector` is assumed. -/
theorem
    exists_bankPaperCanonicalTopFrozenRoundedPostHfitGuardedSlackPackage_of_sourceState
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
    (Tsource : BarycentricTarget B.sampleData)
    (deltaStar betaProt alpha beta qTilde sigma : Real)
    (placementSeed activeSeed : B.sampleData.Sample -> Real)
    (Ssource : BankPaperCanonicalSelectorSourceState
      (W := B.sampleData.W) R certificate fixed
      (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
      (bankPaperCanonicalTopFrozenRoundedSourceSelector (K := K)
        B R certificate Tsource deltaStar betaProt alpha beta qTilde))
    (hplacedFeasible : ∀ a ∈
      R.roughCanonicalGuardedCandidateSet certificate deltaStar K,
      0 <=
          bankPaperCanonicalTopFrozenRoundedPostHfitStructuredPreSelector
            (K := K) B R certificate Tsource deltaStar betaProt alpha beta
              qTilde placementSeed a ∧
        bankPaperCanonicalTopFrozenRoundedPostHfitStructuredPreSelector
            (K := K) B R certificate Tsource deltaStar betaProt alpha beta
              qTilde placementSeed a <= 1)
    (hprebridge :
      BankPaperCanonicalGuardedStructuredAdditivePrebridgeMomentLedger
        (K := K) B R certificate deltaStar betaProt
          (bankPaperCanonicalTopFrozenRoundedSourceSelector (K := K)
            B R certificate Tsource deltaStar betaProt alpha beta qTilde)
          placementSeed)
    {T : BarycentricTarget B.sampleData}
    (Hmeasure : BankPaperCanonicalActualActiveMeasureConstructor
      B.sampleData T
      (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
      (bankPaperCanonicalTopFrozenRoundedPostHfitStructuredPreSelector
        (K := K) B R certificate Tsource deltaStar betaProt alpha beta
          qTilde placementSeed)
      activeSeed)
    (hseed : forall m, B.baseline.baseWeight m = activeSeed m)
    (hsep : B.sampleData.HeadPatternsSeparated)
    (Ctarget Cinitial Cfixed Cactive : Real)
    (henv : B.HasTargetEnvelopes Ctarget
      (fun j => B.markedBandResidual
        (bankPaperCanonicalActualActiveMarkedTarget B R certificate fixed
          (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
          (bankPaperCanonicalTopFrozenRoundedPostHfitStructuredPreSelector
            (K := K) B R certificate Tsource deltaStar betaProt alpha beta
              qTilde placementSeed)
          activeSeed) 0 j))
    (hdeficit : ∀ p ∈ primeBand B.sampleData.n B.sampleData.W,
      abs (bankPaperCanonicalSelectorValuationDeficit
        R certificate fixed
          (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
          (bankPaperCanonicalTopFrozenRoundedPostHfitStructuredPreSelector
            (K := K) B R certificate Tsource deltaStar betaProt alpha beta
              qTilde placementSeed) p) <=
        Cinitial * B.q / ((p : Real) * B.L))
    (hfrozenLedger : forall m : B.sampleData.Sample,
      BridgeData.frozenAmbientWeight
          (bankPaperCanonicalActualFrozenValue
            (candidates :=
              R.roughCanonicalGuardedCandidateSet certificate deltaStar K))
          (bankPaperCanonicalActualFrozenWeight B.sampleData
            (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
            (bankPaperCanonicalTopFrozenRoundedPostHfitStructuredPreSelector
              (K := K) B R certificate Tsource deltaStar betaProt alpha beta
                qTilde placementSeed)
            activeSeed)
          (B.sampleData.value m) <= Cfixed / B.L)
    (hactiveLedger : forall m : B.sampleData.Sample,
      B.baseline.baseWeight m <= Cactive / B.L)
    (radius : NNReal) (Cpost : Real)
    (hP87 :
      forall (Delta : Band -> Real),
        B.HasTargetEnvelopes Ctarget Delta ->
        forall (markedTarget : Nat -> Real) (N : Real),
          0 <= N ->
          B.q <= (1 : Real) * N ->
          (∀ p ∈ primeBand B.sampleData.n B.sampleData.W,
            abs (markedTarget p -
              B.paperMoment (B.markedValuation p) 0) <=
                Cinitial * N / ((p : Real) * B.L)) ->
          (forall j,
            Delta j = B.markedBandResidual markedTarget 0 j) ->
          forall {Fixed : Type} [Fintype Fixed]
            (fixedValue : Fixed -> Nat) (fixedWeight : Fixed -> Real)
            (quota : Int),
            (quota : Real) = (∑ f, fixedWeight f) + B.q ->
            B.sampleData.HeadPatternsSeparated ->
            (forall x,
              BridgeData.frozenAmbientWeight
                fixedValue fixedWeight x ∈ Icc (0 : Real) 1) ->
            (forall m : B.sampleData.Sample,
              BridgeData.frozenAmbientWeight fixedValue fixedWeight
                (B.sampleData.value m) <= Cfixed / B.L) ->
            (forall m : B.sampleData.Sample,
              B.baseline.baseWeight m <= Cactive / B.L) ->
            B.HasPaperProposition87Conclusion Delta radius
              markedTarget N Cpost fixedValue fixedWeight quota)
    (cellIndex : BankPaperCanonicalTangentPrime
      B.sampleData.n B.sampleData.W -> Nat)
    (Cplacement : Real) (hCplacement : 0 <= Cplacement)
    (hplacementSeedUpper : forall m : B.sampleData.Sample,
      placementSeed m <= Cplacement / B.L)
    (hfixed : betaProt + Cplacement <= Cfixed)
    (C : Real) (hC : 1 <= C) (hW : 1 < B.sampleData.W)
    (hhi : forall sign,
      B.sampleData.hi sign <= physicalBound C B.sampleData.n)
    (hCactive : 0 <= Cactive)
    (hprotectedReserve : ∀ x ∈
      R.roughCanonicalGuardedBroadCorrectionPool certificate
        deltaStar B.sampleData.W K 1,
      sigma / B.L +
          bankPaperCanonicalActiveSeedAmbientWeight
            B.sampleData activeSeed x <=
        bankPaperCanonicalTopFrozenRoundedPostHfitStructuredPreSelector
          (K := K) B R certificate Tsource deltaStar betaProt alpha beta
            qTilde placementSeed x)
    (hlarge : Cfixed +
        Real.exp (2 *
          ((Erdos390.Full.PaperStatisticNorm.valuationLogCoefficient
              C B.sampleData.W +
            B.nuisanceStatisticCoefficient C) *
              (3 * (radius : Real)))) * Cactive + sigma <= B.L)
    (hnonsmoothBounds : forall label,
      RoughCanonicalActiveNonexceptionalLabel
          B.sampleData.n deltaStar label ->
        sigma / B.L +
            |R.roughCanonicalGuardedPostchargeCorrectionDensity certificate
              deltaStar B.sampleData.W K label alpha beta B.L| <=
          beta / B.L ∧
        beta / B.L +
            |R.roughCanonicalGuardedPostchargeCorrectionDensity certificate
              deltaStar B.sampleData.W K label alpha beta B.L| <=
          1 - sigma / B.L) :
    ∃ quota : Int, ∃ path : Real -> B.ParamSpace,
    ∃ endpoint : Nat -> Real,
      BankPaperCanonicalTopFrozenRoundedPostHfitGuardedSlackPackage
        (K := K) B R certificate fixed Tsource deltaStar betaProt alpha
          beta qTilde sigma placementSeed activeSeed radius Cpost cellIndex
          quota path endpoint := by
  simpa only [
    bankPaperCanonicalTopFrozenRoundedPostHfitStructuredPreSelector,
    BankPaperCanonicalTopFrozenRoundedPostHfitGuardedSlackPackage] using
    (exists_bankPaperCanonicalPostHfitGuardedSlackPackageOfSource_of_sourceState
      (K := K) B R certificate fixed deltaStar betaProt alpha beta sigma
        (bankPaperCanonicalTopFrozenRoundedSourceSelector (K := K)
          B R certificate Tsource deltaStar betaProt alpha beta qTilde)
        placementSeed activeSeed Ssource hplacedFeasible hprebridge
        (bankPaperCanonicalTopFrozenRoundedSourceSelector_hsourceNonsmooth
          (K := K) B R certificate Tsource deltaStar betaProt alpha beta
            qTilde)
        Hmeasure hseed hsep Ctarget Cinitial Cfixed Cactive henv hdeficit
        hfrozenLedger hactiveLedger radius Cpost hP87 cellIndex
        Cplacement hCplacement hplacementSeedUpper hfixed C hC hW hhi
        hCactive hprotectedReserve hlarge hnonsmoothBounds)

end BankPaperRealization

end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankPaperCanonicalSectionNinePostHeightPlacedMeasureConnector -/
section


/-!
# The post-height baseline under the literal frozen-top placement

The nearest-integer source, the height-changing placement, and the final
barycentric baseline are three different finite objects in the paper.  In
particular, the final baseline has literal mass

`q_n = q0 - d`

and need not equal the two-zero-cell seed used to change the integral row
height.

This file installs the scaled seed of
`bankPaperCanonicalSectionNinePostHeightTarget` directly as the active
layer of the literal frozen-top structured preselector.  The protected
layer then gives pointwise domination, hence the full
`BankPaperCanonicalActualActiveMeasureConstructor` at mass `q0-d`.

The optional feasibility theorem below isolates the remaining upper-bound
issue as the paper's finite geometry: an `O(n / log n)` bound for `q_n`,
a linear lower bound for every structured cell cardinality, and one large
`log n` inequality.  No abstract redistribution contract or equality with
the earlier rounding seed is assumed.
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

/-! ## Literal post-height placed preselector -/





/-! ## Exact pointwise domination and active measure -/





/-! ## The finite capacity supplied by post-height geometry -/

/-- An `O(n / log n)` upper bound for the final mass and a linear lower
bound for every structured cell cardinality give the required pointwise
`O(1 / log n)` bound for the redistributed post-height seed.

The normalized target cell masses need no extra hypothesis: positivity and
their exact sum one imply that each is at most one. -/
theorem
    bankPaperCanonicalSectionNinePostHeightActiveSeed_le_of_massAndCellDensity
    {P : Finset Nat} {Band : Type*}
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData (PaperHeadSimplex.Tag P) Band)
    (I : PhysicalIntervals)
    (hlo : ∀ sigma, B.sampleData.lo sigma =
      physicalBound (I.lower sigma) B.sampleData.n)
    (hhi : ∀ sigma, B.sampleData.hi sigma =
      physicalBound (I.upper sigma) B.sampleData.n)
    {q0 A0 : Real} {d : Int} {exponent : Nat}
    {activeHeadTarget : {p : Nat // p ∈ P} → Real}
    (H : BankPaperCanonicalSectionNinePostHeightBaselineTargetInputs
      B I q0 A0 d exponent activeHeadTarget)
    (Cmass density : Real)
    (hCmass : 0 ≤ Cmass)
    (hdensity : 0 < density)
    (hmass :
      bankPaperCanonicalSectionNinePostHeightActiveMass q0 d ≤
        Cmass * (B.sampleData.n : Real) / B.L)
    (hcard : ∀ cell : Cell (PaperHeadSimplex.Tag P),
      density * (B.sampleData.n : Real) ≤
        (Fintype.card (B.sampleData.SampleAt cell) : Real)) :
    ∀ m : B.sampleData.Sample,
      bankPaperCanonicalSectionNinePostHeightActiveSeed
          B I hlo hhi H m ≤
        (Cmass / density) / B.L := by
  intro m
  let Tpost :=
    bankPaperCanonicalSectionNinePostHeightTarget B I hlo hhi H
  let qn := bankPaperCanonicalSectionNinePostHeightActiveMass q0 d
  let cell := B.sampleData.cellOf m
  have hcardPos :
      0 < (Fintype.card (B.sampleData.SampleAt cell) : Real) := by
    exact_mod_cast B.sampleData.sampleAt_card_pos cell
  have hden : 0 < density * B.L :=
    mul_pos hdensity B.L_pos
  have hfactor : 0 ≤ Cmass / (density * B.L) :=
    div_nonneg hCmass hden.le
  have hscaled :
      (Cmass / (density * B.L)) *
          (density * (B.sampleData.n : Real)) ≤
        (Cmass / (density * B.L)) *
          (Fintype.card (B.sampleData.SampleAt cell) : Real) :=
    mul_le_mul_of_nonneg_left (hcard cell) hfactor
  have hcellLeOne : Tpost.baseline.cellMass cell ≤ 1 := by
    calc
      Tpost.baseline.cellMass cell ≤
          ∑ cell' : Cell (PaperHeadSimplex.Tag P),
            Tpost.baseline.cellMass cell' :=
        Finset.single_le_sum
          (fun cell' _ => (Tpost.baseline.cellMass_pos cell').le)
          (Finset.mem_univ cell)
      _ = Tpost.baseline.totalMass := rfl
      _ = 1 := Tpost.baseline_totalMass
  have hcellMass :
      qn * Tpost.baseline.cellMass cell ≤
        Cmass * (B.sampleData.n : Real) / B.L := by
    calc
      qn * Tpost.baseline.cellMass cell ≤ qn * 1 :=
        mul_le_mul_of_nonneg_left hcellLeOne H.activeMass_pos.le
      _ = qn := mul_one qn
      _ ≤ Cmass * (B.sampleData.n : Real) / B.L := hmass
  change qn * Tpost.baseline.baseWeight m ≤
    (Cmass / density) / B.L
  unfold BaselineAllocation.baseWeight
  change
    qn * (Tpost.baseline.cellMass cell /
      (Fintype.card (B.sampleData.SampleAt cell) : Real)) ≤
        (Cmass / density) / B.L
  rw [← mul_div_assoc]
  apply (div_le_iff₀ hcardPos).2
  calc
    qn * Tpost.baseline.cellMass cell ≤
        Cmass * (B.sampleData.n : Real) / B.L := hcellMass
    _ = (Cmass / (density * B.L)) *
          (density * (B.sampleData.n : Real)) := by
      field_simp [ne_of_gt hdensity, ne_of_gt B.L_pos]
    _ ≤ (Cmass / (density * B.L)) *
          (Fintype.card (B.sampleData.SampleAt cell) : Real) := hscaled
    _ = ((Cmass / density) / B.L) *
          (Fintype.card (B.sampleData.SampleAt cell) : Real) := by
      field_simp [ne_of_gt hdensity, ne_of_gt B.L_pos]

/-- The preceding mass/cardinality geometry and one large-`log n`
inequality discharge the exact structured-placement capacity predicate for
the post-height target. -/
theorem
    bankPaperCanonicalSectionNinePostHeightPlacementCapacity_of_massAndCellDensity
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
    (I : PhysicalIntervals)
    (hlo : ∀ sigma, B.sampleData.lo sigma =
      physicalBound (I.lower sigma) B.sampleData.n)
    (hhi : ∀ sigma, B.sampleData.hi sigma =
      physicalBound (I.upper sigma) B.sampleData.n)
    {q0 A0 : Real} {d : Int} {exponent : Nat}
    {activeHeadTarget : {p : Nat // p ∈ P} → Real}
    (H : BankPaperCanonicalSectionNinePostHeightBaselineTargetInputs
      B I q0 A0 d exponent activeHeadTarget)
    (deltaStar betaProt Cmass density : Real)
    (hbetaProt : 0 ≤ betaProt)
    (hCmass : 0 ≤ Cmass)
    (hdensity : 0 < density)
    (hmass :
      bankPaperCanonicalSectionNinePostHeightActiveMass q0 d ≤
        Cmass * (B.sampleData.n : Real) / B.L)
    (hcard : ∀ cell : Cell (PaperHeadSimplex.Tag P),
      density * (B.sampleData.n : Real) ≤
        (Fintype.card (B.sampleData.SampleAt cell) : Real))
    (hlarge : betaProt + Cmass / density ≤ B.L) :
    BankPaperCanonicalStructuredAdditivePlacementCapacity (K := K)
      B R certificate deltaStar betaProt
        (bankPaperCanonicalSectionNinePostHeightTarget B I hlo hhi H)
        (bankPaperCanonicalSectionNinePostHeightActiveMass q0 d) := by
  apply
    bankPaperCanonicalStructuredAdditivePlacementCapacity_of_div_log_bound
      (K := K) B R certificate deltaStar betaProt
        (bankPaperCanonicalSectionNinePostHeightTarget B I hlo hhi H)
        (bankPaperCanonicalSectionNinePostHeightActiveMass q0 d)
        hbetaProt (Cmass / density)
        (div_nonneg hCmass hdensity.le)
  · exact
      bankPaperCanonicalSectionNinePostHeightActiveSeed_le_of_massAndCellDensity
        B I hlo hhi H Cmass density hCmass hdensity hmass hcard
  · exact hlarge

/-! ## Actual measure and full selector feasibility -/

/-- The complete paper-facing result.  The post-height seed of exact mass
`q0-d` is an actual active measure under the literal frozen-top placed
preselector, and that preselector lies in `[0,1]` throughout the guarded
candidate set.

All upper feasibility is discharged by explicit finite mass and cell
density geometry, rather than by a separate redistribution contract. -/
theorem
    bankPaperCanonicalSectionNinePostHeightPlaced_actualMeasure_and_feasible_of_massAndCellDensity
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
    (Tsource : BarycentricTarget B.sampleData)
    (I : PhysicalIntervals)
    (hlowerOne : ∀ sigma, 1 ≤ I.lower sigma)
    (hupperTwo : ∀ sigma, I.upper sigma ≤ 2)
    (hlo : ∀ sigma, B.sampleData.lo sigma =
      physicalBound (I.lower sigma) B.sampleData.n)
    (hhi : ∀ sigma, B.sampleData.hi sigma =
      physicalBound (I.upper sigma) B.sampleData.n)
    {q0 A0 : Real} {d : Int} {exponent : Nat}
    {activeHeadTarget : {p : Nat // p ∈ P} → Real}
    (H : BankPaperCanonicalSectionNinePostHeightBaselineTargetInputs
      B I q0 A0 d exponent activeHeadTarget)
    (deltaStar betaProt alpha beta qTilde : Real)
    (hqn : 1 ≤ bankPaperCanonicalSectionNinePostHeightActiveMass q0 d)
    (hsep : B.sampleData.HeadPatternsSeparated)
    (hKh : K * upperTailLength c B.sampleData.n ≤ B.sampleData.n)
    (hnotGuard : ∀ m : B.sampleData.Sample,
      B.sampleData.value m ∉
        R.roughCanonicalGuardSet certificate deltaStar)
    (hbetaProt : 0 ≤ betaProt)
    (hsourceFeasible : ∀ a ∈
      R.roughCanonicalGuardedCandidateSet certificate deltaStar K,
      bankPaperCanonicalTopFrozenRoundedSourceSelector (K := K)
          B R certificate Tsource deltaStar betaProt
            alpha beta qTilde a ∈ Set.Icc (0 : Real) 1)
    (Cmass density : Real)
    (hCmass : 0 ≤ Cmass)
    (hdensity : 0 < density)
    (hmass :
      bankPaperCanonicalSectionNinePostHeightActiveMass q0 d ≤
        Cmass * (B.sampleData.n : Real) / B.L)
    (hcard : ∀ cell : Cell (PaperHeadSimplex.Tag P),
      density * (B.sampleData.n : Real) ≤
        (Fintype.card (B.sampleData.SampleAt cell) : Real))
    (hlarge : betaProt + Cmass / density ≤ B.L) :
    BankPaperCanonicalActualActiveMeasureConstructor B.sampleData
        (bankPaperCanonicalSectionNinePostHeightTarget B I hlo hhi H)
        (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
        (bankPaperCanonicalSectionNinePostHeightPlacedPreSelector (K := K)
          B R certificate Tsource I hlo hhi H
            deltaStar betaProt alpha beta qTilde)
        (bankPaperCanonicalSectionNinePostHeightActiveSeed
          B I hlo hhi H) ∧
      (∀ a ∈ R.roughCanonicalGuardedCandidateSet
          certificate deltaStar K,
        bankPaperCanonicalSectionNinePostHeightPlacedPreSelector (K := K)
            B R certificate Tsource I hlo hhi H
              deltaStar betaProt alpha beta qTilde a ∈
          Set.Icc (0 : Real) 1) := by
  have hcapacity :=
    bankPaperCanonicalSectionNinePostHeightPlacementCapacity_of_massAndCellDensity
      (K := K) B R certificate I hlo hhi H deltaStar betaProt
        Cmass density hbetaProt hCmass hdensity hmass hcard hlarge
  simpa only [
    bankPaperCanonicalSectionNinePostHeightPlacedPreSelector,
    bankPaperCanonicalTopFrozenRoundedPostHfitStructuredPreSelector,
    bankPaperCanonicalPostHfitStructuredPreSelectorOfSource,
    bankPaperCanonicalSectionNinePostHeightActiveSeed] using
    (bankPaperCanonicalActualActiveMeasureConstructor_and_feasible_of_structuredAdditivePlacement_physicalIntervals
      B R certificate deltaStar betaProt
        (bankPaperCanonicalTopFrozenRoundedSourceSelector (K := K)
          B R certificate Tsource deltaStar betaProt
            alpha beta qTilde)
        (bankPaperCanonicalSectionNinePostHeightTarget B I hlo hhi H)
        (bankPaperCanonicalSectionNinePostHeightActiveMass q0 d)
        hqn hsep I hlowerOne hupperTwo hlo hhi hKh hnotGuard
        hbetaProt hsourceFeasible hcapacity)

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













/-! ## Literal rounded frozen-top source reduction -/









/-! ## The two literal non-placement defect inputs -/







/-! ## Source-parametric two-zero placement moment -/





/-! ## Literal frozen-top placement specialization -/





/-- Vanishing of the restored top weight supplies the exact outside
compatibility, by unfolding the label-one branch on the guarded smooth row. -/
theorem
    bankPaperCanonicalTopFrozenRoundedPlacementOutsideCompatibility_of_topInvisible
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
    (deltaStar betaProt alpha beta qTilde : Real)
    (hactiveSmooth :
      bankPaperCanonicalStructuredActiveValues B.sampleData ⊆
        R.roughCanonicalGuardedRow certificate deltaStar K 1)
    (htop :
      BankPaperCanonicalTopFrozenSmoothTopInvisibleOnStructuredActive
        (K := K) B R certificate deltaStar alpha) :
    BankPaperCanonicalTopFrozenRoundedPlacementOutsideCompatibility
      (K := K) B R certificate T deltaStar betaProt alpha beta qTilde := by
  intro a haActive haNotPool
  have haRow := hactiveSmooth haActive
  have haLabel :
      completeRoughLabel (yNat B.sampleData.n) a = 1 :=
    (mem_completeRoughRowFiber.mp haRow).2
  unfold bankPaperCanonicalGlobalCorrectedOutsideSelectorWithTop
  rw [if_pos haLabel, htop a haActive haNotPool]
  ring





/-! ## Complete three-input constructor -/



end BankPaperRealization

end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankPaperCanonicalTopFrozenSmoothFeasibilityConnector -/
section


/-!
# Smooth-row feasibility for the frozen-top source

The classification theorem for the frozen-top source leaves one local
premise on complete rough label `1`.  This file discharges that premise for
the literal scaled active seed.

There are two elementary points.

* At a surviving smooth coordinate in the broad lower block, the protected
  layer is exactly the raw head-compatible weight.  If the coordinate is
  head-free it lies in the guarded smooth correction pool; otherwise both
  weights vanish.
* Away from the structured active image the ambient scaled seed vanishes.
  On the image, the existing
  `BankPaperCanonicalStructuredAdditivePlacementCapacity` is precisely the
  required upper bound.

Thus the only geometric input is that the structured active values lie in
the broad lower block.  This is the finite form of the strict physical
upper-endpoint gap already used in the canonical Section 8 geometry.
-/

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.PaperBridgeFit
open Erdos390.Full.PaperGuardCensus

noncomputable section

namespace BankPaperRealization

/-! ## Broad support from the physical endpoint gap -/

/-- The same strict upper-endpoint gap used by the canonical Section 8
geometry puts every structured sample value in the broad lower block.

This is stated separately because the earlier geometry projection exports
smooth-row support but only exports guarded-broad membership for the two
zero-head cells. -/
theorem
    bankPaperCanonicalStructuredValue_mem_roughBroadLowerBlock_of_physicalIntervals
    {Head Band : Type*} [Fintype Head] [DecidableEq Head]
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData Head Band)
    (I : PhysicalIntervals) (h K : Nat)
    (hlowerOne : ∀ sigma, 1 <= I.lower sigma)
    (hupperTwo : ∀ sigma, I.upper sigma <= 2)
    (hlo : ∀ sigma, B.sampleData.lo sigma =
      physicalBound (I.lower sigma) B.sampleData.n)
    (hhi : ∀ sigma, B.sampleData.hi sigma =
      physicalBound (I.upper sigma) B.sampleData.n)
    (hupperBroad : ∀ sigma,
      physicalBound (I.upper sigma) B.sampleData.n <=
        2 * B.sampleData.n - K * h) :
    ∀ m : B.sampleData.Sample,
      B.sampleData.value m ∈
        roughBroadLowerBlock B.sampleData.n h K := by
  have hbounds :=
    bankPaperCanonicalStructuredValue_bounds_of_physicalIntervals
      B I hlowerOne hupperTwo hlo hhi
  intro m
  rw [roughBroadLowerBlock, Finset.mem_Ioc]
  refine ⟨hbounds.1 m, ?_⟩
  calc
    B.sampleData.value m <=
        B.sampleData.hi (B.sampleData.cellOf m).2 :=
      B.sampleData.value_le_hi m
    _ = physicalBound (I.upper (B.sampleData.cellOf m).2)
          B.sampleData.n :=
      hhi (B.sampleData.cellOf m).2
    _ <= 2 * B.sampleData.n - K * h :=
      hupperBroad (B.sampleData.cellOf m).2

/-! ## Identification of the protected layer on the broad smooth row -/

/-- On every surviving smooth-row coordinate in the broad lower block, the
explicit protected layer equals the raw head-compatible weight with broad
parameter `betaProt`.

The existing pointwise theorem handles the head-free case.  In the
non-head-free case the coordinate is outside the correction pool and both
sides are zero. -/
theorem
    bankPaperCanonicalGuardedSmoothProtectedLayer_eq_rawWeight_of_mem_smoothBroadRow
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
    {deltaStar alpha betaProt : Real} {a : Nat}
    (haSmooth :
      a ∈ R.roughCanonicalGuardedRow certificate deltaStar K 1)
    (haBroad :
      a ∈ roughBroadLowerBlock B.sampleData.n
        (upperTailLength c B.sampleData.n) K) :
    bankPaperCanonicalGuardedSmoothProtectedLayer (K := K)
        B R certificate deltaStar betaProt a =
      roughHeadCompatibleRawWeight B.sampleData.W B.sampleData.n
        (upperTailLength c B.sampleData.n) K alpha betaProt B.L a := by
  by_cases hcop : Nat.Coprime a (roughHeadModulus B.sampleData.W)
  · have haCandidate :
        a ∈ R.roughCanonicalGuardedCandidateSet certificate deltaStar K :=
      (mem_completeRoughRowFiber.mp haSmooth).1
    have haSurvives :
        a ∉ R.roughCanonicalGuardSet certificate deltaStar :=
      (Finset.disjoint_left.mp
        (R.roughCanonicalGuardedCandidateSet_disjoint_guardSet
          certificate deltaStar K)) haCandidate
    have haRawPool :
        a ∈ roughCanonicalBroadCorrectionPool B.sampleData.W
          B.sampleData.n (upperTailLength c B.sampleData.n) K
            (yNat B.sampleData.n) 1 := by
      apply mem_completeRoughRowFiber.mpr
      exact
        ⟨mem_roughHeadFree.mpr ⟨haBroad, hcop⟩,
          (mem_completeRoughRowFiber.mp haSmooth).2⟩
    have haPool :
        a ∈ R.roughCanonicalGuardedBroadCorrectionPool certificate
          deltaStar B.sampleData.W K 1 := by
      rw [roughCanonicalGuardedBroadCorrectionPool, Finset.mem_sdiff]
      exact ⟨haRawPool, haSurvives⟩
    exact
      bankPaperCanonicalGuardedSmoothProtectedLayer_eq_rawWeight_of_mem
        B R certificate haPool
  · have hnotPool :
        a ∉ R.roughCanonicalGuardedBroadCorrectionPool certificate
          deltaStar B.sampleData.W K 1 := by
      intro haPool
      have haRawPool :=
        R.roughCanonicalGuardedBroadCorrectionPool_subset_broadPool
          certificate deltaStar B.sampleData.W K 1 haPool
      have haHeadFree :=
        (mem_completeRoughRowFiber.mp haRawPool).1
      exact hcop (mem_roughHeadFree.mp haHeadFree).2
    rw [
      bankPaperCanonicalGuardedSmoothProtectedLayer_apply_of_not_mem
        B R certificate hnotPool]
    simp [roughHeadCompatibleRawWeight, hcop]

/-! ## The atomic smooth-row premise -/



/-! ## Full finite feasibility -/





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







/-! ## Selector-tail support transport -/

/-- On the guarded candidate set, replacing `qTilde` by the nearest-integer
seed changes the frozen-top source by exactly the corresponding ambient seed
change.  On the smooth row the frozen raw layer cancels; on every nonsmooth
row both sources agree and both active ambient weights vanish. -/
theorem
    bankPaperCanonicalTopFrozenRoundedSourceSelector_sub_qTildeSource_eq_ambient_sub
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
    (hactiveSmooth :
      bankPaperCanonicalStructuredActiveValues B.sampleData ⊆
        R.roughCanonicalGuardedRow certificate deltaStar K 1)
    {a : Nat}
    (ha : a ∈
      R.roughCanonicalGuardedCandidateSet certificate deltaStar K) :
    bankPaperCanonicalTopFrozenRoundedSourceSelector (K := K)
          B R certificate T deltaStar betaProt alpha betaTotal qTilde a -
        bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop (K := K)
          B R certificate deltaStar betaProt alpha betaTotal
            (bankPaperCanonicalScaledActiveSeed T qTilde) a =
      bankPaperCanonicalActiveSeedAmbientWeight B.sampleData
          (bankPaperCanonicalTopFrozenRoundedActiveSeed (K := K)
            B R certificate T deltaStar betaProt alpha qTilde) a -
        bankPaperCanonicalActiveSeedAmbientWeight B.sampleData
          (bankPaperCanonicalScaledActiveSeed T qTilde) a := by
  by_cases hlabel :
      completeRoughLabel (yNat B.sampleData.n) a = 1
  · have haSmooth :
        a ∈ R.roughCanonicalGuardedRow certificate deltaStar K 1 := by
      simpa only [BankPaperRealization.roughCanonicalGuardedRow] using
        (mem_completeRoughRowFiber.mpr ⟨ha, hlabel⟩)
    rw [bankPaperCanonicalTopFrozenRoundedSourceSelector,
      bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop_apply_of_mem_smoothRow
        B R certificate
          (bankPaperCanonicalTopFrozenRoundedActiveSeed (K := K)
            B R certificate T deltaStar betaProt alpha qTilde)
          haSmooth,
      bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop_apply_of_mem_smoothRow
        B R certificate (bankPaperCanonicalScaledActiveSeed T qTilde)
          haSmooth]
    ring
  · have haRow :
        a ∈ R.roughCanonicalGuardedRow certificate deltaStar K
          (completeRoughLabel (yNat B.sampleData.n) a) := by
      simpa only [BankPaperRealization.roughCanonicalGuardedRow] using
        (mem_completeRoughRowFiber.mpr ⟨ha, rfl⟩)
    have hsourceEq :=
      bankPaperCanonicalTopFrozenRoundedSourceSelector_eq_qTildeSource_of_mem_nonsmoothRow
        (K := K) B R certificate T deltaStar betaProt alpha betaTotal
          qTilde hlabel haRow
    have hnewZero :
        bankPaperCanonicalActiveSeedAmbientWeight B.sampleData
            (bankPaperCanonicalTopFrozenRoundedActiveSeed (K := K)
              B R certificate T deltaStar betaProt alpha qTilde) a = 0 := by
      apply bankPaperCanonicalActiveSeedAmbientWeight_eq_zero_of_not_value
      intro m hma
      have hmSmooth :=
        hactiveSmooth
          (mem_bankPaperCanonicalStructuredActiveValues.mpr ⟨m, hma⟩)
      have hmLabel := (mem_completeRoughRowFiber.mp hmSmooth).2
      exact hlabel hmLabel
    have holdZero :
        bankPaperCanonicalActiveSeedAmbientWeight B.sampleData
            (bankPaperCanonicalScaledActiveSeed T qTilde) a = 0 := by
      apply bankPaperCanonicalActiveSeedAmbientWeight_eq_zero_of_not_value
      intro m hma
      have hmSmooth :=
        hactiveSmooth
          (mem_bankPaperCanonicalStructuredActiveValues.mpr ⟨m, hma⟩)
      have hmLabel := (mem_completeRoughRowFiber.mp hmSmooth).2
      exact hlabel hmLabel
    rw [hsourceEq, hnewZero, holdZero]
    ring







/-! ## Exact residual input -/



/-! ## Finite assembly -/



/-! ## Eventual canonical supplier -/



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

/-- Broad-lower-block support makes the restored smooth top invisible at
every occupied structured coordinate outside the protected pool.  Hence
the literal rounded frozen-top source has the exact outside compatibility
needed for active-seed replacement.

This discharges the earlier compatibility predicate from concrete support
geometry rather than retaining it as an abstract contract. -/
theorem
    bankPaperCanonicalTopFrozenRoundedPlacementOutsideCompatibility_of_broadSupport
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
    (Tsource : BarycentricTarget B.sampleData)
    (deltaStar betaProt alpha beta qTilde : Real)
    (hactiveSmooth :
      bankPaperCanonicalStructuredActiveValues B.sampleData ⊆
        R.roughCanonicalGuardedRow certificate deltaStar K 1)
    (hactiveBroad : ∀ m : B.sampleData.Sample,
      B.sampleData.value m ∈
        roughBroadLowerBlock B.sampleData.n
          (upperTailLength c B.sampleData.n) K) :
    BankPaperCanonicalTopFrozenRoundedPlacementOutsideCompatibility
      (K := K) B R certificate Tsource deltaStar betaProt
        alpha beta qTilde := by
  apply
    bankPaperCanonicalTopFrozenRoundedPlacementOutsideCompatibility_of_topInvisible
      (K := K) B R certificate Tsource deltaStar betaProt alpha beta qTilde
        hactiveSmooth
  intro a haActive haNotPool
  obtain ⟨m, rfl⟩ :=
    mem_bankPaperCanonicalStructuredActiveValues.mp haActive
  have hmActive :
      B.sampleData.value m ∈
        bankPaperCanonicalStructuredActiveValues B.sampleData :=
    mem_bankPaperCanonicalStructuredActiveValues.mpr ⟨m, rfl⟩
  have hmSmooth := hactiveSmooth hmActive
  calc
    bankPaperCanonicalSmoothTopWeight B.sampleData.W B.sampleData.n
        (upperTailLength c B.sampleData.n) K alpha B.L
          (B.sampleData.value m) =
      roughHeadCompatibleRawWeight B.sampleData.W B.sampleData.n
        (upperTailLength c B.sampleData.n) K alpha betaProt B.L
          (B.sampleData.value m) :=
      bankPaperCanonicalSmoothTopWeight_eq_rawWeight_of_mem_guardedSmoothRow_of_not_mem_broadPool
        B R certificate hmSmooth haNotPool
    _ =
      bankPaperCanonicalGuardedSmoothProtectedLayer (K := K)
        B R certificate deltaStar betaProt
          (B.sampleData.value m) :=
      (bankPaperCanonicalGuardedSmoothProtectedLayer_eq_rawWeight_of_mem_smoothBroadRow
        B R certificate hmSmooth (hactiveBroad m)).symm
    _ = 0 :=
      bankPaperCanonicalGuardedSmoothProtectedLayer_apply_of_not_mem
        B R certificate haNotPool

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



/-! ## Recovering the old head moment from the literal source state -/



/-! ## The paper's `q0-d` prebridge ledger -/

/-- The literal rounded frozen-top source and the fresh post-height target
have the exact signed prebridge ledger.  The post-height input is
specialized to the literal rounded mass, so the total replacement mass is
definitionally `-d`. -/
theorem
    bankPaperCanonicalSectionNinePostHeight_sourcePrebridgeMomentLedger_of_sourceState
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
    (Tsource : BarycentricTarget B.sampleData)
    (I : PhysicalIntervals)
    (hlo : ∀ sigma, B.sampleData.lo sigma =
      physicalBound (I.lower sigma) B.sampleData.n)
    (hhi : ∀ sigma, B.sampleData.hi sigma =
      physicalBound (I.upper sigma) B.sampleData.n)
    {q0 A0 : Real} {d : Int} {exponent : Nat}
    {activeHeadTarget : {p : Nat // p ∈ P} → Real}
    (deltaStar betaProt alpha beta qTilde : Real)
    (H : BankPaperCanonicalSectionNinePostHeightBaselineTargetInputs
      B I q0 A0 d exponent activeHeadTarget)
    (hq0 : q0 =
      bankPaperCanonicalTopFrozenRoundedActiveMass (K := K)
        B R certificate deltaStar betaProt alpha qTilde)
    (hprime : ∀ p ∈ P, p.Prime)
    (hpattern : B.sampleData.pattern =
      PaperHeadSimplex.pattern P hprime exponent)
    (hactiveSmooth :
      bankPaperCanonicalStructuredActiveValues B.sampleData ⊆
        R.roughCanonicalGuardedRow certificate deltaStar K 1)
    (hactiveBroad : ∀ m : B.sampleData.Sample,
      B.sampleData.value m ∈
        roughBroadLowerBlock B.sampleData.n
          (upperTailLength c B.sampleData.n) K)
    (hhead : primesUpTo B.sampleData.W ⊆ P)
    (htarget : ∀ p : {p : Nat // p ∈ P},
      p.1 ≤ B.sampleData.W →
        activeHeadTarget p =
          ((certificate.selectorTailTarget R
            (R.paperFixedExceptionalFactors deltaStar)).factorization p.1 :
              Real))
    (Ssource : BankPaperCanonicalSelectorSourceState
      (W := B.sampleData.W) R certificate
      (R.paperFixedExceptionalFactors deltaStar)
      (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
      (bankPaperCanonicalTopFrozenRoundedSourceSelector (K := K)
        B R certificate Tsource deltaStar betaProt
          alpha beta qTilde)) :
    BankPaperCanonicalGuardedStructuredAdditivePrebridgeMomentLedger
      (K := K) B R certificate deltaStar betaProt
        (bankPaperCanonicalTopFrozenRoundedSourceSelector (K := K)
          B R certificate Tsource deltaStar betaProt
            alpha beta qTilde)
        (bankPaperCanonicalSectionNinePostHeightActiveSeed
          B I hlo hhi H) := by
  let oldSeed :=
    bankPaperCanonicalTopFrozenRoundedActiveSeed (K := K)
      B R certificate Tsource deltaStar betaProt alpha qTilde
  let newSeed :=
    bankPaperCanonicalSectionNinePostHeightActiveSeed
      B I hlo hhi H
  have hmass :
      bankPaperCanonicalLiteralActiveMass B.sampleData newSeed -
          bankPaperCanonicalLiteralActiveMass B.sampleData oldSeed =
        ((-d : Int) : Real) := by
    dsimp only [newSeed, oldSeed]
    rw [
      bankPaperCanonicalSectionNinePostHeight_literalActiveMass_activeSeed,
      bankPaperCanonicalLiteralActiveMass_topFrozenRoundedActiveSeed]
    simp only [bankPaperCanonicalSectionNinePostHeightActiveMass_eq,
      Int.cast_neg]
    rw [hq0]
    ring
  have hmoments : ∀ q : Nat, q.Prime → q ≤ B.sampleData.W →
      (∑ m : B.sampleData.Sample,
          newSeed m * valuation q (B.sampleData.value m)) =
        ∑ m : B.sampleData.Sample,
          oldSeed m * valuation q (B.sampleData.value m) := by
    simpa only [newSeed, oldSeed] using
      (bankPaperCanonicalSectionNinePostHeight_headMoments_eq_roundedSource_of_sourceState
        (K := K) B R certificate Tsource I hlo hhi H
          deltaStar betaProt alpha beta qTilde hprime hpattern
          hactiveSmooth hhead htarget Ssource)
  have hcompat :
      BankPaperCanonicalTopFrozenRoundedPlacementOutsideCompatibility
        (K := K) B R certificate Tsource deltaStar betaProt
          alpha beta qTilde :=
    bankPaperCanonicalTopFrozenRoundedPlacementOutsideCompatibility_of_broadSupport
      (K := K) B R certificate Tsource deltaStar betaProt
        alpha beta qTilde hactiveSmooth hactiveBroad
  simpa only [
    oldSeed, newSeed,
    bankPaperCanonicalTopFrozenRoundedSourceSelector,
    bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop] using
    (bankPaperCanonicalGuardedStructuredAdditivePrebridgeMomentLedger_of_arbitrarySeedReplacement
      (K := K) B R certificate deltaStar betaProt oldSeed newSeed
        (bankPaperCanonicalGlobalCorrectedOutsideSelectorWithTop (K := K)
          B R certificate deltaStar alpha beta oldSeed)
        hcompat hactiveSmooth (-d) hmass hmoments)

/-! ## Row quota and full placement -/



/-- Source feasibility, source row/support state, and the exact new
prebridge ledger give the complete guarded structured placement. -/
theorem
    bankPaperCanonicalSectionNinePostHeightPlaced_structuredPlacement_of_sourceState
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
    (Tsource : BarycentricTarget B.sampleData)
    (I : PhysicalIntervals)
    (hlo : ∀ sigma, B.sampleData.lo sigma =
      physicalBound (I.lower sigma) B.sampleData.n)
    (hhi : ∀ sigma, B.sampleData.hi sigma =
      physicalBound (I.upper sigma) B.sampleData.n)
    {q0 A0 : Real} {d : Int} {exponent : Nat}
    {activeHeadTarget : {p : Nat // p ∈ P} → Real}
    (H : BankPaperCanonicalSectionNinePostHeightBaselineTargetInputs
      B I q0 A0 d exponent activeHeadTarget)
    (deltaStar betaProt alpha beta qTilde : Real)
    (Ssource : BankPaperCanonicalSelectorSourceState
      (W := B.sampleData.W) R certificate
      (R.paperFixedExceptionalFactors deltaStar)
      (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
      (bankPaperCanonicalTopFrozenRoundedSourceSelector (K := K)
        B R certificate Tsource deltaStar betaProt
          alpha beta qTilde))
    (hplacedFeasible : ∀ a ∈
      R.roughCanonicalGuardedCandidateSet certificate deltaStar K,
      0 ≤
          bankPaperCanonicalSectionNinePostHeightPlacedPreSelector (K := K)
            B R certificate Tsource I hlo hhi H
              deltaStar betaProt alpha beta qTilde a ∧
        bankPaperCanonicalSectionNinePostHeightPlacedPreSelector (K := K)
            B R certificate Tsource I hlo hhi H
              deltaStar betaProt alpha beta qTilde a ≤ 1)
    (hledger :
      BankPaperCanonicalGuardedStructuredAdditivePrebridgeMomentLedger
        (K := K) B R certificate deltaStar betaProt
          (bankPaperCanonicalTopFrozenRoundedSourceSelector (K := K)
            B R certificate Tsource deltaStar betaProt
              alpha beta qTilde)
          (bankPaperCanonicalSectionNinePostHeightActiveSeed
            B I hlo hhi H)) :
    BankPaperCanonicalGuardedStructuredAdditivePlacement (K := K)
      B R certificate (R.paperFixedExceptionalFactors deltaStar)
        deltaStar betaProt
        (bankPaperCanonicalTopFrozenRoundedSourceSelector (K := K)
          B R certificate Tsource deltaStar betaProt
            alpha beta qTilde)
        (bankPaperCanonicalSectionNinePostHeightActiveSeed
          B I hlo hhi H) := by
  apply
    bankPaperCanonicalGuardedStructuredAdditivePlacement_of_prebridgeMomentLedger
      B R certificate (R.paperFixedExceptionalFactors deltaStar)
        (bankPaperCanonicalTopFrozenRoundedSourceSelector (K := K)
          B R certificate Tsource deltaStar betaProt
            alpha beta qTilde)
        (bankPaperCanonicalSectionNinePostHeightActiveSeed
          B I hlo hhi H)
  · simpa only [
      bankPaperCanonicalSectionNinePostHeightPlacedPreSelector,
      bankPaperCanonicalTopFrozenRoundedPostHfitStructuredPreSelector,
      bankPaperCanonicalPostHfitStructuredPreSelectorOfSource] using
      hplacedFeasible
  · exact Ssource.rowIntegral
  · exact Ssource.deficitSupportedOnPrimeBand
  · exact hledger

/-! ## One-shot geometric source-to-post-height construction -/

/-- The literal finite source-to-post-height handoff in one theorem.

Physical interval and guard geometry supply smooth/broad support.  The
source state and selector-tail target supply the old row quotas and head
moments.  The post-height target supplies the new mass and head moments.
Finally, mass/cardinality geometry supplies `[0,1]` feasibility.

The output contains:

1. the signed source-to-`Tpost` prebridge ledger;
2. the actual active measure of exact mass `q0-d`;
3. the full structured placement, including all complete-row integer
   quotas and deficit support outside the tangent prime band.
-/
theorem
    bankPaperCanonicalSectionNinePostHeight_sourcePrebridge_actualMeasure_and_placement_of_sourceState
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
    (Tsource : BarycentricTarget B.sampleData)
    (I : PhysicalIntervals)
    (hlowerOne : ∀ sigma, 1 ≤ I.lower sigma)
    (hupperTwo : ∀ sigma, I.upper sigma ≤ 2)
    (hlo : ∀ sigma, B.sampleData.lo sigma =
      physicalBound (I.lower sigma) B.sampleData.n)
    (hhi : ∀ sigma, B.sampleData.hi sigma =
      physicalBound (I.upper sigma) B.sampleData.n)
    (hupperBroad : ∀ sigma,
      physicalBound (I.upper sigma) B.sampleData.n ≤
        2 * B.sampleData.n -
          K * upperTailLength c B.sampleData.n)
    {q0 A0 : Real} {d : Int} {exponent : Nat}
    {activeHeadTarget : {p : Nat // p ∈ P} → Real}
    (deltaStar betaProt alpha beta qTilde : Real)
    (H : BankPaperCanonicalSectionNinePostHeightBaselineTargetInputs
      B I q0 A0 d exponent activeHeadTarget)
    (hq0 : q0 =
      bankPaperCanonicalTopFrozenRoundedActiveMass (K := K)
        B R certificate deltaStar betaProt alpha qTilde)
    (hqn : 1 ≤
      bankPaperCanonicalSectionNinePostHeightActiveMass q0 d)
    (hprime : ∀ p ∈ P, p.Prime)
    (hpattern : B.sampleData.pattern =
      PaperHeadSimplex.pattern P hprime exponent)
    (hhead : primesUpTo B.sampleData.W ⊆ P)
    (htarget : ∀ p : {p : Nat // p ∈ P},
      p.1 ≤ B.sampleData.W →
        activeHeadTarget p =
          ((certificate.selectorTailTarget R
            (R.paperFixedExceptionalFactors deltaStar)).factorization p.1 :
              Real))
    (hsep : B.sampleData.HeadPatternsSeparated)
    (hKh : K * upperTailLength c B.sampleData.n ≤ B.sampleData.n)
    (hnotGuard : ∀ m : B.sampleData.Sample,
      B.sampleData.value m ∉
        R.roughCanonicalGuardSet certificate deltaStar)
    (hbetaProt : 0 ≤ betaProt)
    (Ssource : BankPaperCanonicalSelectorSourceState
      (W := B.sampleData.W) R certificate
      (R.paperFixedExceptionalFactors deltaStar)
      (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
      (bankPaperCanonicalTopFrozenRoundedSourceSelector (K := K)
        B R certificate Tsource deltaStar betaProt
          alpha beta qTilde))
    (Cmass density : Real)
    (hCmass : 0 ≤ Cmass)
    (hdensity : 0 < density)
    (hmass :
      bankPaperCanonicalSectionNinePostHeightActiveMass q0 d ≤
        Cmass * (B.sampleData.n : Real) / B.L)
    (hcard : ∀ cell : Cell (PaperHeadSimplex.Tag P),
      density * (B.sampleData.n : Real) ≤
        (Fintype.card (B.sampleData.SampleAt cell) : Real))
    (hlarge : betaProt + Cmass / density ≤ B.L) :
    BankPaperCanonicalGuardedStructuredAdditivePrebridgeMomentLedger
        (K := K) B R certificate deltaStar betaProt
          (bankPaperCanonicalTopFrozenRoundedSourceSelector (K := K)
            B R certificate Tsource deltaStar betaProt
              alpha beta qTilde)
          (bankPaperCanonicalSectionNinePostHeightActiveSeed
            B I hlo hhi H) ∧
      BankPaperCanonicalActualActiveMeasureConstructor B.sampleData
        (bankPaperCanonicalSectionNinePostHeightTarget B I hlo hhi H)
        (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
        (bankPaperCanonicalSectionNinePostHeightPlacedPreSelector (K := K)
          B R certificate Tsource I hlo hhi H
            deltaStar betaProt alpha beta qTilde)
        (bankPaperCanonicalSectionNinePostHeightActiveSeed
          B I hlo hhi H) ∧
      BankPaperCanonicalGuardedStructuredAdditivePlacement (K := K)
        B R certificate (R.paperFixedExceptionalFactors deltaStar)
          deltaStar betaProt
          (bankPaperCanonicalTopFrozenRoundedSourceSelector (K := K)
            B R certificate Tsource deltaStar betaProt
              alpha beta qTilde)
          (bankPaperCanonicalSectionNinePostHeightActiveSeed
            B I hlo hhi H) := by
  have hactiveSmooth :
      bankPaperCanonicalStructuredActiveValues B.sampleData ⊆
        R.roughCanonicalGuardedRow certificate deltaStar K 1 :=
    bankPaperCanonicalStructuredActiveValues_subset_guardedSmoothRow_of_physicalIntervals
      B R certificate deltaStar I hlowerOne hupperTwo hlo hhi
        hKh hnotGuard
  have hactiveBroad : ∀ m : B.sampleData.Sample,
      B.sampleData.value m ∈
        roughBroadLowerBlock B.sampleData.n
          (upperTailLength c B.sampleData.n) K :=
    bankPaperCanonicalStructuredValue_mem_roughBroadLowerBlock_of_physicalIntervals
      B I (upperTailLength c B.sampleData.n) K
        hlowerOne hupperTwo hlo hhi hupperBroad
  have hledger :=
    bankPaperCanonicalSectionNinePostHeight_sourcePrebridgeMomentLedger_of_sourceState
      (K := K) B R certificate Tsource I hlo hhi
        deltaStar betaProt alpha beta qTilde H hq0 hprime hpattern
        hactiveSmooth hactiveBroad hhead htarget Ssource
  have hmeasureFeasible :=
    bankPaperCanonicalSectionNinePostHeightPlaced_actualMeasure_and_feasible_of_massAndCellDensity
      (K := K) B R certificate Tsource I hlowerOne hupperTwo hlo hhi H
        deltaStar betaProt alpha beta qTilde hqn hsep hKh hnotGuard
        hbetaProt
        (fun a ha => Ssource.feasible a ha)
        Cmass density hCmass hdensity hmass hcard hlarge
  have hplacement :=
    bankPaperCanonicalSectionNinePostHeightPlaced_structuredPlacement_of_sourceState
      (K := K) B R certificate Tsource I hlo hhi H
        deltaStar betaProt alpha beta qTilde Ssource
        (fun a ha => hmeasureFeasible.2 a ha)
        hledger
  exact ⟨hledger, hmeasureFeasible.1, hplacement⟩

end BankPaperRealization

end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankPaperCanonicalSectionNinePostHeightFrozenLogInvarianceConnector -/
section


/-!
# Frozen-log invariance under the post-height active-seed replacement

The rounded frozen-top source and the final post-height placement use
different active seeds.  The structured placement changes the selector by
exactly the corresponding change of ambient active weight.  Therefore,
after subtracting the active weight in
`bankPaperCanonicalActualFrozenWeight`, the tagged frozen remainder is
unchanged.

This file records that cancellation first for an arbitrary replacement
seed, and then for the literal rounded source and post-height barycentric
seed.  Summing the pointwise identity gives equality of the finite
candidate-log contribution and hence of
`bankPaperCanonicalActualFrozenLogMass`.  The proof is purely finite and
introduces no compatibility or redistribution contract: the specialized
result obtains the already existing outside compatibility from broad
support.
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

/-! ## Arbitrary-seed frozen remainder -/

/-- Replacing the active seed in a structured placement leaves every
tagged frozen candidate weight unchanged.

The pointwise signed placement identity says that the selector changes by
the difference of the new and old ambient active weights.  Subtracting the
new ambient active weight therefore recovers the old frozen remainder. -/
theorem
    bankPaperCanonicalGuardedStructuredAdditivePlacement_actualFrozenWeight_eq_source_of_arbitrarySeedReplacement
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
    (candidates : Finset Nat)
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
    (a : BankPaperCanonicalActualFrozenIndex candidates) :
    bankPaperCanonicalActualFrozenWeight B.sampleData candidates
        (bankPaperCanonicalGuardedStructuredAdditivePlacementSelector
          (K := K) B R certificate deltaStar betaProt
          (bankPaperCanonicalTwoZeroHeadCellSourceSelector (K := K)
            B R certificate deltaStar betaProt oldSeed outsideSelector)
          newSeed)
        newSeed a =
      bankPaperCanonicalActualFrozenWeight B.sampleData candidates
        (bankPaperCanonicalTwoZeroHeadCellSourceSelector (K := K)
          B R certificate deltaStar betaProt oldSeed outsideSelector)
        oldSeed a := by
  have hchange :=
    bankPaperCanonicalGuardedStructuredAdditivePlacementSelector_arbitrarySeed_sub_twoZeroSource_of_active
      (K := K) B R certificate deltaStar betaProt
        oldSeed newSeed outsideSelector houtsideActive a.1
  unfold bankPaperCanonicalActualFrozenWeight
  linarith only [hchange]







/-! ## Literal rounded-source to post-height specialization -/

/-- Pointwise tagged frozen-weight invariance from the rounded frozen-top
source to the literal post-height placed selector.

The only geometric inputs are the smooth-row and broad-lower-block support
facts already used by the post-height prebridge.  They construct the
outside compatibility through
`bankPaperCanonicalTopFrozenRoundedPlacementOutsideCompatibility_of_broadSupport`;
no compatibility proposition is assumed. -/
theorem
    bankPaperCanonicalSectionNinePostHeightPlaced_actualFrozenWeight_eq_roundedSource
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
    (Tsource : BarycentricTarget B.sampleData)
    (I : PhysicalIntervals)
    (hlo : ∀ sigma, B.sampleData.lo sigma =
      physicalBound (I.lower sigma) B.sampleData.n)
    (hhi : ∀ sigma, B.sampleData.hi sigma =
      physicalBound (I.upper sigma) B.sampleData.n)
    {q0 A0 : Real} {d : Int} {exponent : Nat}
    {activeHeadTarget : {p : Nat // p ∈ P} → Real}
    (H : BankPaperCanonicalSectionNinePostHeightBaselineTargetInputs
      B I q0 A0 d exponent activeHeadTarget)
    (deltaStar betaProt alpha beta qTilde : Real)
    (hactiveSmooth :
      bankPaperCanonicalStructuredActiveValues B.sampleData ⊆
        R.roughCanonicalGuardedRow certificate deltaStar K 1)
    (hactiveBroad : ∀ m : B.sampleData.Sample,
      B.sampleData.value m ∈
        roughBroadLowerBlock B.sampleData.n
          (upperTailLength c B.sampleData.n) K)
    (a : BankPaperCanonicalActualFrozenIndex
      (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)) :
    bankPaperCanonicalActualFrozenWeight B.sampleData
        (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
        (bankPaperCanonicalSectionNinePostHeightPlacedPreSelector (K := K)
          B R certificate Tsource I hlo hhi H
            deltaStar betaProt alpha beta qTilde)
        (bankPaperCanonicalSectionNinePostHeightActiveSeed
          B I hlo hhi H) a =
      bankPaperCanonicalActualFrozenWeight B.sampleData
        (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
        (bankPaperCanonicalTopFrozenRoundedSourceSelector (K := K)
          B R certificate Tsource deltaStar betaProt
            alpha beta qTilde)
        (bankPaperCanonicalTopFrozenRoundedActiveSeed (K := K)
          B R certificate Tsource deltaStar betaProt
            alpha qTilde) a := by
  have hcompat :
      BankPaperCanonicalTopFrozenRoundedPlacementOutsideCompatibility
        (K := K) B R certificate Tsource deltaStar betaProt
          alpha beta qTilde :=
    bankPaperCanonicalTopFrozenRoundedPlacementOutsideCompatibility_of_broadSupport
      (K := K) B R certificate Tsource deltaStar betaProt
        alpha beta qTilde hactiveSmooth hactiveBroad
  simpa only [
    bankPaperCanonicalSectionNinePostHeightPlacedPreSelector,
    bankPaperCanonicalTopFrozenRoundedPostHfitStructuredPreSelector,
    bankPaperCanonicalPostHfitStructuredPreSelectorOfSource,
    bankPaperCanonicalTopFrozenRoundedSourceSelector,
    bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop] using
    (bankPaperCanonicalGuardedStructuredAdditivePlacement_actualFrozenWeight_eq_source_of_arbitrarySeedReplacement
      (K := K) B R certificate
        (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
        deltaStar betaProt
        (bankPaperCanonicalTopFrozenRoundedActiveSeed (K := K)
          B R certificate Tsource deltaStar betaProt alpha qTilde)
        (bankPaperCanonicalSectionNinePostHeightActiveSeed B I hlo hhi H)
        (bankPaperCanonicalGlobalCorrectedOutsideSelectorWithTop (K := K)
          B R certificate deltaStar alpha beta
            (bankPaperCanonicalTopFrozenRoundedActiveSeed (K := K)
              B R certificate Tsource deltaStar betaProt alpha qTilde))
        hcompat a)

/-- The candidate part of the frozen logarithmic mass is unchanged by the
literal rounded-source to post-height replacement. -/
theorem
    sum_bankPaperCanonicalSectionNinePostHeightPlaced_actualFrozenWeight_mul_log_eq_roundedSource
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
    (Tsource : BarycentricTarget B.sampleData)
    (I : PhysicalIntervals)
    (hlo : ∀ sigma, B.sampleData.lo sigma =
      physicalBound (I.lower sigma) B.sampleData.n)
    (hhi : ∀ sigma, B.sampleData.hi sigma =
      physicalBound (I.upper sigma) B.sampleData.n)
    {q0 A0 : Real} {d : Int} {exponent : Nat}
    {activeHeadTarget : {p : Nat // p ∈ P} → Real}
    (H : BankPaperCanonicalSectionNinePostHeightBaselineTargetInputs
      B I q0 A0 d exponent activeHeadTarget)
    (deltaStar betaProt alpha beta qTilde : Real)
    (hactiveSmooth :
      bankPaperCanonicalStructuredActiveValues B.sampleData ⊆
        R.roughCanonicalGuardedRow certificate deltaStar K 1)
    (hactiveBroad : ∀ m : B.sampleData.Sample,
      B.sampleData.value m ∈
        roughBroadLowerBlock B.sampleData.n
          (upperTailLength c B.sampleData.n) K) :
    (∑ a : BankPaperCanonicalActualFrozenIndex
          (R.roughCanonicalGuardedCandidateSet certificate deltaStar K),
        bankPaperCanonicalActualFrozenWeight B.sampleData
            (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
            (bankPaperCanonicalSectionNinePostHeightPlacedPreSelector
              (K := K) B R certificate Tsource I hlo hhi H
                deltaStar betaProt alpha beta qTilde)
            (bankPaperCanonicalSectionNinePostHeightActiveSeed
              B I hlo hhi H) a *
          Real.log (bankPaperCanonicalActualFrozenValue a : Real)) =
      ∑ a : BankPaperCanonicalActualFrozenIndex
          (R.roughCanonicalGuardedCandidateSet certificate deltaStar K),
        bankPaperCanonicalActualFrozenWeight B.sampleData
            (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
            (bankPaperCanonicalTopFrozenRoundedSourceSelector (K := K)
              B R certificate Tsource deltaStar betaProt
                alpha beta qTilde)
            (bankPaperCanonicalTopFrozenRoundedActiveSeed (K := K)
              B R certificate Tsource deltaStar betaProt
                alpha qTilde) a *
          Real.log (bankPaperCanonicalActualFrozenValue a : Real) := by
  classical
  apply Finset.sum_congr rfl
  intro a _ha
  rw [
    bankPaperCanonicalSectionNinePostHeightPlaced_actualFrozenWeight_eq_roundedSource
      (K := K) B R certificate Tsource I hlo hhi H
        deltaStar betaProt alpha beta qTilde
        hactiveSmooth hactiveBroad a]

/-- The complete finite frozen logarithmic mass, including fixed factors
and the state-zero bank, is the same before and after the post-height
active-seed replacement. -/
theorem
    bankPaperCanonicalSectionNinePostHeightPlaced_actualFrozenLogMass_eq_roundedSource
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
    (fixed bankBase : Finset Nat)
    (Tsource : BarycentricTarget B.sampleData)
    (I : PhysicalIntervals)
    (hlo : ∀ sigma, B.sampleData.lo sigma =
      physicalBound (I.lower sigma) B.sampleData.n)
    (hhi : ∀ sigma, B.sampleData.hi sigma =
      physicalBound (I.upper sigma) B.sampleData.n)
    {q0 A0 : Real} {d : Int} {exponent : Nat}
    {activeHeadTarget : {p : Nat // p ∈ P} → Real}
    (H : BankPaperCanonicalSectionNinePostHeightBaselineTargetInputs
      B I q0 A0 d exponent activeHeadTarget)
    (deltaStar betaProt alpha beta qTilde : Real)
    (hactiveSmooth :
      bankPaperCanonicalStructuredActiveValues B.sampleData ⊆
        R.roughCanonicalGuardedRow certificate deltaStar K 1)
    (hactiveBroad : ∀ m : B.sampleData.Sample,
      B.sampleData.value m ∈
        roughBroadLowerBlock B.sampleData.n
          (upperTailLength c B.sampleData.n) K) :
    bankPaperCanonicalActualFrozenLogMass B.sampleData fixed bankBase
        (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
        (bankPaperCanonicalSectionNinePostHeightPlacedPreSelector (K := K)
          B R certificate Tsource I hlo hhi H
            deltaStar betaProt alpha beta qTilde)
        (bankPaperCanonicalSectionNinePostHeightActiveSeed
          B I hlo hhi H) =
      bankPaperCanonicalActualFrozenLogMass B.sampleData fixed bankBase
        (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
        (bankPaperCanonicalTopFrozenRoundedSourceSelector (K := K)
          B R certificate Tsource deltaStar betaProt
            alpha beta qTilde)
        (bankPaperCanonicalTopFrozenRoundedActiveSeed (K := K)
          B R certificate Tsource deltaStar betaProt
            alpha qTilde) := by
  unfold bankPaperCanonicalActualFrozenLogMass
  rw [
    sum_bankPaperCanonicalSectionNinePostHeightPlaced_actualFrozenWeight_mul_log_eq_roundedSource
      (K := K) B R certificate Tsource I hlo hhi H
        deltaStar betaProt alpha beta qTilde
        hactiveSmooth hactiveBroad]

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



/-! ## General finite residual algebra -/

/-- Exact compensated-sum identity for a residual distributed over the
actual arithmetic bands. -/
theorem bankPaperCanonicalBandCenterResidual_eq_primeDeviationResidual
    {Head Band : Type*} [Fintype Head] [DecidableEq Head]
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData Head Band)
    (Delta : Band -> Real)
    (residual : BandPrime B.sampleData.n B.sampleData.W -> Real)
    (hDelta : forall j,
      Delta j =
        ∑ p ∈ B.partition.data.fiber j, residual p)
    (hordinary :
      (∑ p : BandPrime B.sampleData.n B.sampleData.W,
        tPrime B.sampleData.n p.1 * residual p) = 0) :
    (∑ j : Band, B.bandCenter j * Delta j) =
      ∑ p : BandPrime B.sampleData.n B.sampleData.W,
        B.primeDeviation p * residual p := by
  have hcenter :
      (∑ j : Band, B.bandCenter j * Delta j) =
        ∑ p : BandPrime B.sampleData.n B.sampleData.W,
          B.bandCenter (B.partition.band p) * residual p := by
    calc
      (∑ j : Band, B.bandCenter j * Delta j) =
          ∑ j : Band, B.bandCenter j *
            (∑ p ∈ B.partition.data.fiber j, residual p) := by
        apply Finset.sum_congr rfl
        intro j _hj
        rw [hDelta j]
      _ = ∑ p : BandPrime B.sampleData.n B.sampleData.W,
          B.bandCenter (B.partition.band p) * residual p := by
        rw [← Finset.sum_fiberwise Finset.univ B.partition.band
          (fun p : BandPrime B.sampleData.n B.sampleData.W =>
            B.bandCenter (B.partition.band p) * residual p)]
        apply Finset.sum_congr rfl
        intro j _hj
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro p hp
        have hpj : B.partition.band p = j :=
          (Erdos390.Lemma84.WeightedBandData.mem_fiber_iff
            B.partition.data).mp hp
        rw [hpj]
  calc
    (∑ j : Band, B.bandCenter j * Delta j) =
        ∑ p : BandPrime B.sampleData.n B.sampleData.W,
          B.bandCenter (B.partition.band p) * residual p := hcenter
    _ = (∑ p : BandPrime B.sampleData.n B.sampleData.W,
          B.bandCenter (B.partition.band p) * residual p) -
        ∑ p : BandPrime B.sampleData.n B.sampleData.W,
          tPrime B.sampleData.n p.1 * residual p := by
      rw [hordinary, sub_zero]
    _ = ∑ p : BandPrime B.sampleData.n B.sampleData.W,
        B.primeDeviation p * residual p := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro p _hp
      unfold BridgeData.primeDeviation
      ring

/-- Pointwise residual control, exact ordinary-log compatibility, and the
canonical `L¹` mesh estimate imply both target envelopes. -/
theorem bankPaperCanonicalHasTargetEnvelopes_seven_of_primeResidual
    {Head Band : Type*} [Fintype Head] [DecidableEq Head]
    [Fintype Band] [DecidableEq Band] [Nonempty Head]
    (B : BridgeData Head Band)
    (Delta : Band -> Real)
    (residual : BandPrime B.sampleData.n B.sampleData.W -> Real)
    (Cinitial : Real) (hCinitial : 0 <= Cinitial)
    (hDelta : forall j,
      Delta j =
        ∑ p ∈ B.partition.data.fiber j, residual p)
    (hpointwise : forall p,
      abs (residual p) <=
        Cinitial * B.q / ((p.1 : Real) * B.L))
    (hordinary :
      (∑ p : BandPrime B.sampleData.n B.sampleData.W,
        tPrime B.sampleData.n p.1 * residual p) = 0)
    (hdeviation : B.primeDeviationL1 <= 7 * B.w) :
    B.HasTargetEnvelopes (7 * Cinitial) Delta := by
  have hqL : 0 <= B.q / B.L :=
    (div_pos B.q_pos B.L_pos).le
  have hCseven : Cinitial <= 7 * Cinitial := by
    linarith
  constructor
  · intro j
    have hrateSum :
        (∑ p ∈ B.partition.data.fiber j,
          Cinitial * B.q / ((p.1 : Real) * B.L)) =
            (B.q / B.L) * Cinitial * B.harmonicMass j := by
      unfold BridgeData.harmonicMass
      change
        (∑ p ∈ B.partition.data.fiber j,
          Cinitial * B.q / ((p.1 : Real) * B.L)) =
            (B.q / B.L) * Cinitial *
              (∑ p ∈ B.partition.data.fiber j,
                1 / (p.1 : Real))
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p _hp
      have hpPos : (0 : Real) < (p.1 : Real) := by
        exact_mod_cast (prime_of_mem_primeBand p.2).pos
      field_simp [ne_of_gt hpPos, ne_of_gt B.L_pos]
    calc
      abs (Delta j) =
          abs (∑ p ∈ B.partition.data.fiber j, residual p) := by
        rw [hDelta j]
      _ <= ∑ p ∈ B.partition.data.fiber j, abs (residual p) :=
        Finset.abs_sum_le_sum_abs _ _
      _ <= ∑ p ∈ B.partition.data.fiber j,
          Cinitial * B.q / ((p.1 : Real) * B.L) := by
        exact Finset.sum_le_sum fun p _hp => hpointwise p
      _ = (B.q / B.L) * Cinitial * B.harmonicMass j :=
        hrateSum
      _ = (B.q / B.L) * Cinitial * abs (B.harmonicMass j) := by
        rw [abs_of_pos (B.harmonicMass_pos j)]
      _ <= (B.q / B.L) * (7 * Cinitial) *
          abs (B.harmonicMass j) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hCseven hqL) (abs_nonneg _)
  · rw [bankPaperCanonicalBandCenterResidual_eq_primeDeviationResidual
      B Delta residual hDelta hordinary]
    have hweightedRate :
        (∑ p : BandPrime B.sampleData.n B.sampleData.W,
          abs (B.primeDeviation p) *
            (Cinitial * B.q / ((p.1 : Real) * B.L))) =
          (B.q / B.L) * Cinitial * B.primeDeviationL1 := by
      unfold BridgeData.primeDeviationL1
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p _hp
      have hpPos : (0 : Real) < (p.1 : Real) := by
        exact_mod_cast (prime_of_mem_primeBand p.2).pos
      field_simp [ne_of_gt hpPos, ne_of_gt B.L_pos]
    have hfactor : 0 <= (B.q / B.L) * Cinitial :=
      mul_nonneg hqL hCinitial
    calc
      abs (∑ p : BandPrime B.sampleData.n B.sampleData.W,
          B.primeDeviation p * residual p) <=
          ∑ p : BandPrime B.sampleData.n B.sampleData.W,
            abs (B.primeDeviation p * residual p) :=
        Finset.abs_sum_le_sum_abs _ _
      _ <= ∑ p : BandPrime B.sampleData.n B.sampleData.W,
          abs (B.primeDeviation p) *
            (Cinitial * B.q / ((p.1 : Real) * B.L)) := by
        apply Finset.sum_le_sum
        intro p _hp
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left
          (hpointwise p) (abs_nonneg _)
      _ = (B.q / B.L) * Cinitial * B.primeDeviationL1 :=
        hweightedRate
      _ <= (B.q / B.L) * Cinitial * (7 * B.w) :=
        mul_le_mul_of_nonneg_left hdeviation hfactor
      _ = (B.q / B.L) * (7 * Cinitial) * B.w := by
        ring

/-! ## Specialization to the literal initial P87 residual -/

/-- The actual initial marked-band target has the required envelopes once
the selector deficit has the pointwise rate and the explicit normalized
ordinary-log compatibility identity.

The conversion from selector deficit to the active marked residual is
derived from the actual-measure constructor and the initial-seed identity;
it is not an additional hypothesis. -/
theorem bankPaperCanonicalActualInitialHasTargetEnvelopes_of_selectorDeficit
    {Head Band : Type*} [Fintype Head] [DecidableEq Head]
    [Fintype Band] [DecidableEq Band] [Nonempty Head]
    (B : BridgeData Head Band)
    {c : Real} {depth : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (fixed candidates : Finset Nat) (preSelector : Nat -> Real)
    (activeSeed : B.sampleData.Sample -> Real)
    {T : BarycentricTarget B.sampleData}
    (Hmeasure : BankPaperCanonicalActualActiveMeasureConstructor
      B.sampleData T candidates preSelector activeSeed)
    (hseed : forall m, B.baseline.baseWeight m = activeSeed m)
    (Cinitial : Real) (hCinitial : 0 <= Cinitial)
    (hdeficit : ∀ p ∈
      primeBand B.sampleData.n B.sampleData.W,
      abs (bankPaperCanonicalSelectorValuationDeficit
        R certificate fixed candidates preSelector p) <=
          Cinitial * B.q / ((p : Real) * B.L))
    (hordinary : BankPaperCanonicalSelectorOrdinaryLogCompatible
      (W := B.sampleData.W)
      R certificate fixed candidates preSelector)
    (hdeviation : B.primeDeviationL1 <= 7 * B.w) :
    B.HasTargetEnvelopes (7 * Cinitial)
      (fun j => B.markedBandResidual
        (bankPaperCanonicalActualActiveMarkedTarget
          B R certificate fixed candidates preSelector activeSeed) 0 j) := by
  let markedTarget : Nat -> Real :=
    bankPaperCanonicalActualActiveMarkedTarget
      B R certificate fixed candidates preSelector activeSeed
  let residual : BandPrime B.sampleData.n B.sampleData.W -> Real :=
    fun p =>
      bankPaperCanonicalTangentResidual
        R certificate fixed candidates preSelector p
  have hDelta : forall j : Band,
      B.markedBandResidual markedTarget 0 j =
        ∑ p ∈ B.partition.data.fiber j, residual p := by
    intro j
    unfold BridgeData.markedBandResidual
    apply Finset.sum_congr rfl
    intro p _hp
    dsimp only [markedTarget, residual,
      bankPaperCanonicalTangentResidual]
    exact (bankPaperCanonicalActualInitial_deficit_eq_activeResidual
      B R certificate fixed candidates preSelector activeSeed
        Hmeasure hseed p.1).symm
  have hpointwise : forall p,
      abs (residual p) <=
        Cinitial * B.q / ((p.1 : Real) * B.L) := by
    intro p
    simpa only [residual, bankPaperCanonicalTangentResidual] using
      hdeficit p.1 p.2
  have hordinaryResidual :
      (∑ p : BandPrime B.sampleData.n B.sampleData.W,
        tPrime B.sampleData.n p.1 * residual p) = 0 := by
    simpa only [BankPaperCanonicalSelectorOrdinaryLogCompatible,
      residual] using hordinary
  exact bankPaperCanonicalHasTargetEnvelopes_seven_of_primeResidual
    B
    (fun j => B.markedBandResidual markedTarget 0 j)
    residual Cinitial hCinitial hDelta hpointwise
      hordinaryResidual hdeviation

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







/-! ## Ordinary logarithm equals the logarithmically weighted deficit -/



/-- Normalizing the preceding identity by `log y` gives exactly the
`tPrime`-weighted residual used by Proposition 8.7. -/
theorem bankPaperCanonical_selectorWeightedResidual_eq_selectorLogDefect_div
    {c : Real} {depth n W : Nat} {left right : Nat -> Nat}
    {changed : Finset Nat}
    (R : BankPaperRealization n
      (upperEndpoint n (upperTailLength c n)))
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (fixed candidates : Finset Nat) (selector : Nat -> Real)
    (hsupport : BankPaperCanonicalSelectorDeficitSupportedOnPrimeBand
      (W := W) R certificate fixed candidates selector) :
    (∑ p : BankPaperCanonicalTangentPrime n W,
        tPrime n p.1 *
          bankPaperCanonicalTangentResidual
            R certificate fixed candidates selector p) =
      (Real.log (certificate.selectorTailTarget R fixed : Real) -
          ∑ a ∈ candidates, selector a * Real.log (a : Real)) /
        Real.log (y n) := by
  have hattach :
      (∑ p : BankPaperCanonicalTangentPrime n W,
          tPrime n p.1 *
            bankPaperCanonicalTangentResidual
              R certificate fixed candidates selector p) =
        ∑ p ∈ primeBand n W,
          tPrime n p *
            bankPaperCanonicalSelectorValuationDeficit
              R certificate fixed candidates selector p := by
    simpa only [Finset.univ_eq_attach,
      bankPaperCanonicalTangentResidual] using
      (Finset.sum_attach (primeBand n W)
        (fun p =>
          tPrime n p *
            bankPaperCanonicalSelectorValuationDeficit
              R certificate fixed candidates selector p))
  rw [hattach]
  calc
    (∑ p ∈ primeBand n W,
        tPrime n p *
          bankPaperCanonicalSelectorValuationDeficit
            R certificate fixed candidates selector p) =
        (∑ p ∈ primeBand n W,
          bankPaperCanonicalSelectorValuationDeficit
              R certificate fixed candidates selector p *
            Real.log (p : Real)) /
          Real.log (y n) := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro p _hp
      unfold tPrime
      ring
    _ =
        (Real.log (certificate.selectorTailTarget R fixed : Real) -
            ∑ a ∈ candidates, selector a * Real.log (a : Real)) /
          Real.log (y n) := by
      rw [
        bankPaperCanonical_selectorLogDefect_eq_sum_log_mul_deficit
          R certificate fixed candidates selector hsupport]

/-- Exact equality of the selector logarithm and target logarithm therefore
supplies exact ordinary-log compatibility, with no mesh constant. -/
theorem bankPaperCanonicalSelector_ordinaryLogCompatible_of_selectorLog
    {c : Real} {depth n W : Nat} {left right : Nat -> Nat}
    {changed : Finset Nat}
    (R : BankPaperRealization n
      (upperEndpoint n (upperTailLength c n)))
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (fixed candidates : Finset Nat) (selector : Nat -> Real)
    (hsupport : BankPaperCanonicalSelectorDeficitSupportedOnPrimeBand
      (W := W) R certificate fixed candidates selector)
    (hlog :
      Real.log (certificate.selectorTailTarget R fixed : Real) =
        ∑ a ∈ candidates, selector a * Real.log (a : Real)) :
    BankPaperCanonicalSelectorOrdinaryLogCompatible
      (W := W) R certificate fixed candidates selector := by
  unfold BankPaperCanonicalSelectorOrdinaryLogCompatible
  rw [
    bankPaperCanonical_selectorWeightedResidual_eq_selectorLogDefect_div
      R certificate fixed candidates selector hsupport,
    hlog, sub_self, zero_div]

/-! ## Exact active/frozen logarithmic decomposition -/

/-- The ambient push-forward preserves every finite weighted statistic, not
just total mass. -/
theorem sum_bankPaperCanonicalActiveSeedAmbientWeight_mul
    {Head : Type*} [Fintype Head] [Nonempty Head]
    {D : StructuredSampleData Head} {T : BarycentricTarget D}
    {candidates : Finset Nat} {preSelector : Nat -> Real}
    {activeSeed : D.Sample -> Real}
    (H : BankPaperCanonicalActualActiveMeasureConstructor
      D T candidates preSelector activeSeed)
    (F : Nat -> Real) :
    (∑ a ∈ candidates,
        bankPaperCanonicalActiveSeedAmbientWeight D activeSeed a * F a) =
      ∑ m : D.Sample, activeSeed m * F (D.value m) := by
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
    exact (hnot (bankPaperCanonicalActiveSeed_value_mem_candidates H m)).elim

/-- Adding the literal active ordinary-log moment back to the exact frozen
logarithmic mass recovers the fixed charges plus the logarithm of the whole
pre-selector. -/
theorem bankPaperCanonicalActualFrozenLogMass_add_activeOrdinaryLog_eq
    {Head : Type*} [Fintype Head] [Nonempty Head]
    (D : StructuredSampleData Head) (T : BarycentricTarget D)
    (fixed bankBase candidates : Finset Nat) (preSelector : Nat -> Real)
    (activeSeed : D.Sample -> Real)
    (H : BankPaperCanonicalActualActiveMeasureConstructor
      D T candidates preSelector activeSeed) :
    bankPaperCanonicalActualFrozenLogMass
          D fixed bankBase candidates preSelector activeSeed +
        (∑ m : D.Sample,
          activeSeed m * Real.log (D.value m : Real)) =
      (∑ a ∈ fixed, Real.log (a : Real)) +
        (∑ a ∈ bankBase, Real.log (a : Real)) +
        ∑ a ∈ candidates,
          preSelector a * Real.log (a : Real) := by
  classical
  have hpush :=
    sum_bankPaperCanonicalActiveSeedAmbientWeight_mul
      H (fun a => Real.log (a : Real))
  have hcandidates :
      (∑ a : BankPaperCanonicalActualFrozenIndex candidates,
          bankPaperCanonicalActualFrozenWeight
              D candidates preSelector activeSeed a *
            Real.log (bankPaperCanonicalActualFrozenValue a : Real)) +
          (∑ m : D.Sample,
            activeSeed m * Real.log (D.value m : Real)) =
        ∑ a ∈ candidates,
          preSelector a * Real.log (a : Real) := by
    rw [← hpush]
    unfold bankPaperCanonicalActualFrozenWeight
      bankPaperCanonicalActualFrozenValue
    rw [← Finset.sum_subtype candidates (fun _ => Iff.rfl)
      (fun a =>
        (preSelector a -
            bankPaperCanonicalActiveSeedAmbientWeight D activeSeed a) *
          Real.log (a : Real))]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro a _ha
    ring
  unfold bankPaperCanonicalActualFrozenLogMass
  linarith only [hcandidates]

/-! ## The exact selector-tail charge -/

/-- Logarithm of a positive natural-number product as a sum of logarithms. -/
theorem bankPaperCanonical_log_finset_prod_id
    (s : Finset Nat) (hpos : ∀ a ∈ s, 0 < a) :
    Real.log ((s.prod (fun a : Nat => a) : Nat) : Real) =
      ∑ a ∈ s, Real.log (a : Real) := by
  rw [Nat.cast_prod]
  apply Real.log_prod
  intro a ha
  exact_mod_cast (hpos a ha).ne'

/-- The quotient identity for `selectorTailTarget` gives the exact
fixed-plus-bank logarithmic charge of the precharged target. -/
theorem GuardedCentralAnchorCertificate.selectorTailTarget_log_charge
    {c : Real} {depth n : Nat} {left right : Nat -> Nat}
    {changed : Finset Nat}
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (R : BankPaperRealization n
      (upperEndpoint n (upperTailLength c n)))
    (fixed : Finset Nat)
    (hfixedPositive : ∀ a ∈ fixed, 0 < a)
    (hchargeDvd :
      R.selectorTailCharge fixed ∣ certificate.prechargedTailTarget) :
    Real.log (certificate.prechargedTailTarget : Real) =
      (∑ a ∈ fixed, Real.log (a : Real)) +
        (∑ a ∈ baseBankFactors R.exactificationState,
          Real.log (a : Real)) +
        Real.log (certificate.selectorTailTarget R fixed : Real) := by
  have hbasePositive :
      ∀ a ∈ baseBankFactors R.exactificationState, 0 < a := by
    intro a ha
    rw [R.baseExactificationBank_eq_prechargeBaseState] at ha
    have hinterval := R.prechargeBaseState_subset_factorInterval ha
    exact Nat.zero_lt_of_lt (Finset.mem_Ioc.mp hinterval).1
  have hfixedProdPos :
      0 < ((fixed.prod (fun a : Nat => a) : Nat) : Real) := by
    exact_mod_cast
      (Finset.prod_pos fun a ha => hfixedPositive a ha)
  have hbaseProdPos :
      0 <
        (((baseBankFactors R.exactificationState).prod
          (fun a : Nat => a) : Nat) : Real) := by
    exact_mod_cast
      (Finset.prod_pos fun a ha => hbasePositive a ha)
  have htargetPos :
      0 < certificate.selectorTailTarget R fixed :=
    certificate.selectorTailTarget_pos
      R fixed hfixedPositive hchargeDvd
  have hchargePos : 0 < R.selectorTailCharge fixed :=
    R.selectorTailCharge_pos fixed hfixedPositive
  have hproduct :=
    certificate.selectorTailTarget_mul_selectorTailCharge
      R fixed hchargeDvd
  calc
    Real.log (certificate.prechargedTailTarget : Real) =
        Real.log
          ((certificate.selectorTailTarget R fixed *
            R.selectorTailCharge fixed : Nat) : Real) := by
      rw [hproduct]
    _ =
        Real.log (certificate.selectorTailTarget R fixed : Real) +
          Real.log (R.selectorTailCharge fixed : Real) := by
      rw [Nat.cast_mul, Real.log_mul]
      · exact_mod_cast htargetPos.ne'
      · exact_mod_cast hchargePos.ne'
    _ =
        Real.log (certificate.selectorTailTarget R fixed : Real) +
          (Real.log
              ((fixed.prod (fun a : Nat => a) : Nat) : Real) +
            Real.log
              (((baseBankFactors R.exactificationState).prod
                (fun a : Nat => a) : Nat) : Real)) := by
      unfold BankPaperRealization.selectorTailCharge
      simp only [id_eq] at hfixedProdPos hbaseProdPos ⊢
      rw [Nat.cast_mul,
        Real.log_mul hfixedProdPos.ne' hbaseProdPos.ne']
    _ =
        (∑ a ∈ fixed, Real.log (a : Real)) +
          (∑ a ∈ baseBankFactors R.exactificationState,
            Real.log (a : Real)) +
          Real.log (certificate.selectorTailTarget R fixed : Real) := by
      rw [
        bankPaperCanonical_log_finset_prod_id fixed hfixedPositive,
        bankPaperCanonical_log_finset_prod_id
          (baseBankFactors R.exactificationState) hbasePositive]
      ring

/-! ## The fresh post-height seed realizes `logY - Lambda0` -/

/-- The exact post-height ordinary-log moment is `logY - Lambda0` whenever
the scalar height input is the literal frozen-height defect. -/
theorem
    bankPaperCanonicalSectionNinePostHeight_activeSeed_ordinaryLogMoment_eq_logY_sub_Lambda0
    {P : Finset Nat} {Band : Type*}
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData (PaperHeadSimplex.Tag P) Band)
    (I : PhysicalIntervals)
    (hlo : ∀ sigma, B.sampleData.lo sigma =
      physicalBound (I.lower sigma) B.sampleData.n)
    (hhi : ∀ sigma, B.sampleData.hi sigma =
      physicalBound (I.upper sigma) B.sampleData.n)
    {q0 A0 : Real} {d : Int} {exponent : Nat}
    {activeHeadTarget : {p : Nat // p ∈ P} -> Real}
    (H : BankPaperCanonicalSectionNinePostHeightBaselineTargetInputs
      B I q0 A0 d exponent activeHeadTarget)
    (logY Lambda0 : Real)
    (hA0 : A0 = logY - Lambda0 - q0 * B.L) :
    (∑ m : B.sampleData.Sample,
        bankPaperCanonicalSectionNinePostHeightActiveSeed
            B I hlo hhi H m *
          B.ordinaryLogScore m) =
      logY - Lambda0 := by
  rw [
    bankPaperCanonicalSectionNinePostHeight_activeSeed_ordinaryLogMoment
      B I hlo hhi H]
  unfold bankPaperCanonicalSectionNinePostHeightActiveHeight
    bankPaperCanonicalSectionNinePostHeightActiveMass
  rw [hA0]
  ring

/-! ## Complete post-height selector ledger -/

/-- The active/frozen split and the scalar post-height identity recover the
exact logarithm of the whole pre-selector.  The charge premise is a source
product ledger, not an ordinary-log compatibility assumption. -/
theorem bankPaperCanonicalSectionNinePostHeight_selectorLog_eq_target
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
    (fixed bankBase candidates : Finset Nat)
    (preSelector : Nat -> Real)
    (I : PhysicalIntervals)
    (hlo : ∀ sigma, B.sampleData.lo sigma =
      physicalBound (I.lower sigma) B.sampleData.n)
    (hhi : ∀ sigma, B.sampleData.hi sigma =
      physicalBound (I.upper sigma) B.sampleData.n)
    {q0 A0 : Real} {d : Int} {exponent : Nat}
    {activeHeadTarget : {p : Nat // p ∈ P} -> Real}
    (H : BankPaperCanonicalSectionNinePostHeightBaselineTargetInputs
      B I q0 A0 d exponent activeHeadTarget)
    (Hmeasure : BankPaperCanonicalActualActiveMeasureConstructor
      B.sampleData
        (bankPaperCanonicalSectionNinePostHeightTarget B I hlo hhi H)
      candidates preSelector
        (bankPaperCanonicalSectionNinePostHeightActiveSeed B I hlo hhi H))
    (logY Lambda0 : Real)
    (hA0 : A0 = logY - Lambda0 - q0 * B.L)
    (hLambda0 :
      Lambda0 =
        bankPaperCanonicalActualFrozenLogMass B.sampleData
          fixed bankBase candidates preSelector
            (bankPaperCanonicalSectionNinePostHeightActiveSeed
              B I hlo hhi H))
    (hcharge :
      logY =
        (∑ a ∈ fixed, Real.log (a : Real)) +
          (∑ a ∈ bankBase, Real.log (a : Real)) +
          Real.log (certificate.selectorTailTarget R fixed : Real)) :
    Real.log (certificate.selectorTailTarget R fixed : Real) =
      ∑ a ∈ candidates, preSelector a * Real.log (a : Real) := by
  have hactive :=
    bankPaperCanonicalSectionNinePostHeight_activeSeed_ordinaryLogMoment_eq_logY_sub_Lambda0
      B I hlo hhi H logY Lambda0 hA0
  have hfrozen :=
    bankPaperCanonicalActualFrozenLogMass_add_activeOrdinaryLog_eq
      B.sampleData
      (bankPaperCanonicalSectionNinePostHeightTarget B I hlo hhi H)
      fixed bankBase candidates preSelector
      (bankPaperCanonicalSectionNinePostHeightActiveSeed B I hlo hhi H)
      Hmeasure
  have htotal :
      (∑ a ∈ fixed, Real.log (a : Real)) +
          (∑ a ∈ bankBase, Real.log (a : Real)) +
          ∑ a ∈ candidates, preSelector a * Real.log (a : Real) =
        logY := by
    calc
      (∑ a ∈ fixed, Real.log (a : Real)) +
            (∑ a ∈ bankBase, Real.log (a : Real)) +
            ∑ a ∈ candidates, preSelector a * Real.log (a : Real) =
          bankPaperCanonicalActualFrozenLogMass B.sampleData
                fixed bankBase candidates preSelector
                  (bankPaperCanonicalSectionNinePostHeightActiveSeed
                    B I hlo hhi H) +
            (∑ m : B.sampleData.Sample,
              bankPaperCanonicalSectionNinePostHeightActiveSeed
                    B I hlo hhi H m *
                Real.log (B.sampleData.value m : Real)) := hfrozen.symm
      _ = Lambda0 +
            (∑ m : B.sampleData.Sample,
              bankPaperCanonicalSectionNinePostHeightActiveSeed
                    B I hlo hhi H m *
                B.ordinaryLogScore m) := by
          rw [hLambda0]
          rfl
      _ = Lambda0 + (logY - Lambda0) := by rw [hactive]
      _ = logY := by ring
  linarith only [htotal, hcharge]

/-- Specialization of the preceding theorem to the literal quotient target:
`logY` is the logarithm of `prechargedTailTarget`, and the frozen integral
charges are exactly the selector-fixed factors and state-zero bank. -/
theorem
    bankPaperCanonicalSectionNinePostHeight_selectorLog_eq_target_of_prechargedTail
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
    (fixed candidates : Finset Nat) (preSelector : Nat -> Real)
    (I : PhysicalIntervals)
    (hlo : ∀ sigma, B.sampleData.lo sigma =
      physicalBound (I.lower sigma) B.sampleData.n)
    (hhi : ∀ sigma, B.sampleData.hi sigma =
      physicalBound (I.upper sigma) B.sampleData.n)
    {q0 A0 : Real} {d : Int} {exponent : Nat}
    {activeHeadTarget : {p : Nat // p ∈ P} -> Real}
    (H : BankPaperCanonicalSectionNinePostHeightBaselineTargetInputs
      B I q0 A0 d exponent activeHeadTarget)
    (Hmeasure : BankPaperCanonicalActualActiveMeasureConstructor
      B.sampleData
        (bankPaperCanonicalSectionNinePostHeightTarget B I hlo hhi H)
      candidates preSelector
        (bankPaperCanonicalSectionNinePostHeightActiveSeed B I hlo hhi H))
    (Lambda0 : Real)
    (hA0 :
      A0 =
        Real.log (certificate.prechargedTailTarget : Real) -
          Lambda0 - q0 * B.L)
    (hLambda0 :
      Lambda0 =
        bankPaperCanonicalActualFrozenLogMass B.sampleData
          fixed (baseBankFactors R.exactificationState)
          candidates preSelector
            (bankPaperCanonicalSectionNinePostHeightActiveSeed
              B I hlo hhi H))
    (hfixedPositive : ∀ a ∈ fixed, 0 < a)
    (hchargeDvd :
      R.selectorTailCharge fixed ∣ certificate.prechargedTailTarget) :
    Real.log (certificate.selectorTailTarget R fixed : Real) =
      ∑ a ∈ candidates, preSelector a * Real.log (a : Real) := by
  apply bankPaperCanonicalSectionNinePostHeight_selectorLog_eq_target
    B R certificate fixed (baseBankFactors R.exactificationState)
      candidates preSelector I hlo hhi H Hmeasure
      (Real.log (certificate.prechargedTailTarget : Real)) Lambda0
      hA0 hLambda0
  exact certificate.selectorTailTarget_log_charge
    R fixed hfixedPositive hchargeDvd

/-- The literal quotient charge, exact post-height moment, actual frozen
ledger, and prime-band source support imply exact initial compatibility. -/
theorem
    bankPaperCanonicalSectionNinePostHeight_initialSelector_ordinaryLogCompatible
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
    (fixed candidates : Finset Nat) (preSelector : Nat -> Real)
    (I : PhysicalIntervals)
    (hlo : ∀ sigma, B.sampleData.lo sigma =
      physicalBound (I.lower sigma) B.sampleData.n)
    (hhi : ∀ sigma, B.sampleData.hi sigma =
      physicalBound (I.upper sigma) B.sampleData.n)
    {q0 A0 : Real} {d : Int} {exponent : Nat}
    {activeHeadTarget : {p : Nat // p ∈ P} -> Real}
    (H : BankPaperCanonicalSectionNinePostHeightBaselineTargetInputs
      B I q0 A0 d exponent activeHeadTarget)
    (Hmeasure : BankPaperCanonicalActualActiveMeasureConstructor
      B.sampleData
        (bankPaperCanonicalSectionNinePostHeightTarget B I hlo hhi H)
      candidates preSelector
        (bankPaperCanonicalSectionNinePostHeightActiveSeed B I hlo hhi H))
    (hsupport : BankPaperCanonicalSelectorDeficitSupportedOnPrimeBand
      (W := B.sampleData.W) R certificate fixed candidates preSelector)
    (Lambda0 : Real)
    (hA0 :
      A0 =
        Real.log (certificate.prechargedTailTarget : Real) -
          Lambda0 - q0 * B.L)
    (hLambda0 :
      Lambda0 =
        bankPaperCanonicalActualFrozenLogMass B.sampleData
          fixed (baseBankFactors R.exactificationState)
          candidates preSelector
            (bankPaperCanonicalSectionNinePostHeightActiveSeed
              B I hlo hhi H))
    (hfixedPositive : ∀ a ∈ fixed, 0 < a)
    (hchargeDvd :
      R.selectorTailCharge fixed ∣ certificate.prechargedTailTarget) :
    BankPaperCanonicalSelectorOrdinaryLogCompatible
      (W := B.sampleData.W) R certificate fixed candidates preSelector := by
  apply bankPaperCanonicalSelector_ordinaryLogCompatible_of_selectorLog
    R certificate fixed candidates preSelector hsupport
  exact
    bankPaperCanonicalSectionNinePostHeight_selectorLog_eq_target_of_prechargedTail
      B R certificate fixed candidates preSelector I hlo hhi H Hmeasure
        Lambda0 hA0 hLambda0 hfixedPositive hchargeDvd



end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankPaperCanonicalActualMomentReadyEventually -/
section


/-!
# Eventual canonical `MomentReady` data for the Section 9 traffic input

The canonical actual-moment theorem constructs
`RegularMeshPrimeCutoffs.Mesh.MomentReady` from its three endpoint
quadratures, uses it to prove the displayed moment inequalities, and then
discards the structure.  Section 9's ratio-cell moment argument consumes the
structure itself.

This connector exports that already-proved finite payload for the literal
canonical partition, uniformly in the supplied `ScaleSeparation` proof.  It
also records the independent eventual fact needed by the ratio-cell
coordinate argument: every positive-cell lower scale point eventually
exceeds any fixed real threshold, uniformly over the finite mesh.  The
combined theorem specializes this fact at the downstream threshold `2`.

No residual, balance, selector, Mertens, or traffic bound is asserted here.
-/

open scoped BigOperators
open Filter

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.ArithmeticBandGeometry
open Erdos390.Full.RegularRelativeMesh
open Erdos390.Full.RegularMeshPrimeCutoffs
open Erdos390.Full.PositiveCellTransfer
open Erdos390.Full.KernelPrimeQuadrature
open Erdos390.Full.PrimeBandQuadrature
open Erdos390.Full.PrimeCoordinateSecondMoment
open Erdos390.Full.MovingLowMomentQuadrature

noncomputable section

/-! ## Uniform positive-cell scale growth -/

/-- Every fixed real threshold is eventually below every positive-cell
lower scale point.  The threshold is fixed before the asymptotic index, and
the conclusion is uniform over the finite mesh. -/
theorem eventually_bankPaperCanonical_all_le_scalePoint_lower
    {delta eta : Real} (M : RegularRelativeMesh.Mesh delta eta)
    (hdelta : 0 < delta) (A : Real) :
    ∀ᶠ n : Nat in atTop,
      ∀ k : Fin M.cellCount, A ≤ scalePoint n (M.lower k) := by
  rw [Filter.eventually_all]
  intro k
  exact
    (tendsto_scalePoint_atTop (M.lower_pos hdelta k)).eventually
      (eventually_ge_atTop A)

/-! ## Literal canonical-partition moment readiness -/

/-- The actual endpoint quadratures supply `MomentReady` for every literal
canonical partition obtained from a scale-separation proof.  At the same
asymptotic index, every positive-cell lower scale point is at least `2`, as
required by the ratio-cell coordinate bound.

The only cutoff premise is the existing structural condition
`canonicalActualMomentCutoff ≤ W`; in particular, no traffic hypothesis is
folded into this statement. -/
theorem eventually_bankPaperCanonical_actualMomentReady
    {delta eta : Real} (M : RegularRelativeMesh.Mesh delta eta)
    (hdelta : 0 < delta) :
    ∀ W : Nat, canonicalActualMomentCutoff ≤ W →
      ∀ᶠ n : Nat in atTop,
        ∃ hWne : W ≠ 0, ∃ hn : 1 < n,
          (∀ k : Fin M.cellCount,
            (2 : Real) ≤ scalePoint n (M.lower k)) ∧
          ∀ S : ScaleSeparation M n W,
            RegularMeshPrimeCutoffs.Mesh.MomentReady M
              (RegularMeshPrimeCutoffs.Mesh.canonicalPartition
                M hdelta hn hWne S) := by
  let Cmass : Real := canonicalMassQuadratureConstant
  let Xmass : Nat := canonicalMassQuadratureCutoff
  let Cfirst : Real :=
    MovingLowMomentQuadrature.fullLogReciprocalSumUniformConstant
  let Xfirst : Nat :=
    MovingLowMomentQuadrature.fullLogReciprocalSumUniformCutoff
  let Csecond : Real := canonicalSecondMomentConstant
  let Xsecond : Nat := canonicalSecondMomentCutoff
  have hMass : ∀ A Y : Nat, Xmass ≤ A → A ≤ Y →
      |PrimeSums.fullReciprocalSum Y - PrimeSums.fullReciprocalSum A -
          (Real.log (Real.log (Y : Real)) -
            Real.log (Real.log (A : Real)))| ≤
        5 * Cmass / Real.log (A : Real) ^ 3 := by
    intro A Y hA hAY
    simpa only [Cmass, Xmass] using
      canonicalMassQuadratureBound A Y hA hAY
  have hFirst : ∀ A Y : Nat, Xfirst ≤ A → A ≤ Y →
      |PrimeSums.fullLogReciprocalSum Y -
          PrimeSums.fullLogReciprocalSum A -
          (Real.log (Y : Real) - Real.log (A : Real))| ≤
        2 * Cfirst / Real.log (A : Real) ^ 3 +
          Cfirst / (2 * Real.log (A : Real) ^ 2) := by
    intro A Y hA hAY
    simpa only [Cfirst, Xfirst] using
      MovingLowMomentQuadrature.fullLogReciprocalSumUniform_bound A Y hA hAY
  have hSecond : ∀ z : Real, 1 < z → ∀ A Y : Nat,
      Xsecond ≤ A → A ≤ Y →
      |KernelPrimeQuadrature.fullWeightedReciprocalSum
            PrimeCoordinateSecondMoment.squareCoordinate z Y -
          KernelPrimeQuadrature.fullWeightedReciprocalSum
            PrimeCoordinateSecondMoment.squareCoordinate z A -
          ((realLogCoordinate z (Y : Real) ^ 2 -
            realLogCoordinate z (A : Real) ^ 2) / 2)| ≤
        3 * Csecond / (Real.log z ^ 2 * Real.log (A : Real)) := by
    intro z hz A Y hA hAY
    simpa only [Csecond, Xsecond] using
      canonicalSecondMomentBound z hz A Y hA hAY
  intro W hW
  have hW8 : 8 ≤ W :=
    (le_max_left 8 (max Xmass (max Xfirst Xsecond))).trans hW
  have hXmass : Xmass ≤ W :=
    ((le_max_left Xmass (max Xfirst Xsecond)).trans
      (le_max_right 8 (max Xmass (max Xfirst Xsecond)))).trans hW
  have hXfirst : Xfirst ≤ W :=
    ((le_max_left Xfirst Xsecond).trans
      ((le_max_right Xmass (max Xfirst Xsecond)).trans
        (le_max_right 8 (max Xmass (max Xfirst Xsecond))))).trans hW
  have hXsecond : Xsecond ≤ W :=
    ((le_max_right Xfirst Xsecond).trans
      ((le_max_right Xmass (max Xfirst Xsecond)).trans
        (le_max_right 8 (max Xmass (max Xfirst Xsecond))))).trans hW
  have hWne : W ≠ 0 := by omega
  have hEndpoint :=
    RegularMeshPrimeCutoffs.Mesh.eventually_endpointMomentBounds
      M hdelta W Cmass Cfirst Csecond (by omega : 1 < W)
  have hTwo :=
    eventually_bankPaperCanonical_all_le_scalePoint_lower
      M hdelta (2 : Real)
  filter_upwards [hEndpoint, hTwo] with n R hTwoN
  let hn : 1 < n := R.n_gt_one
  refine ⟨hWne, hn, hTwoN, ?_⟩
  intro S
  let P :=
    RegularMeshPrimeCutoffs.Mesh.canonicalPartition M hdelta hn hWne S
  let E :=
    RegularMeshPrimeCutoffs.Mesh.canonicalCertificate M hdelta hn hWne S
  exact
    RegularMeshPrimeCutoffs.Mesh.momentReady_of_endpointMomentBounds M P E
      (fun j ↦ rfl) (fun j ↦ rfl)
      hW8 hXmass hXfirst hXsecond hMass hFirst hSecond R

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











/-! ## The fresh post-height bridge -/



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







end BankPaperCanonicalSectionNinePostHeightBridgeInputsAt

/-! ## Literal source and finite geometry -/



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

/-- Physical geometry puts every occupied active coordinate in the complete
guarded smooth row. -/
theorem activeSmooth
    (S : BankPaperCanonicalSectionNinePostHeightSourceInputsAt
      M Bsource R certificate I deltaStar hdelta J) :
    bankPaperCanonicalStructuredActiveValues
        J.postHeightBridge.sampleData ⊆
      R.roughCanonicalGuardedRow certificate deltaStar (K0 + 1) 1 :=
  bankPaperCanonicalStructuredActiveValues_subset_guardedSmoothRow_of_physicalIntervals
    J.postHeightBridge R certificate deltaStar I S.lowerOne S.upperTwo
      J.postHeightHlo J.postHeightHhi S.roughDepth S.outsideGuard

/-- The same interval geometry places every occupied active value in the
broad lower block used by arbitrary-seed replacement. -/
theorem activeBroad
    (S : BankPaperCanonicalSectionNinePostHeightSourceInputsAt
      M Bsource R certificate I deltaStar hdelta J)
    (m : J.postHeightBridge.sampleData.Sample) :
    J.postHeightBridge.sampleData.value m ∈
      roughBroadLowerBlock J.postHeightBridge.sampleData.n
        (upperTailLength c J.postHeightBridge.sampleData.n)
        (K0 + 1) :=
  bankPaperCanonicalStructuredValue_mem_roughBroadLowerBlock_of_physicalIntervals
    J.postHeightBridge I
      (upperTailLength c J.postHeightBridge.sampleData.n)
      (K0 + 1) S.lowerOne S.upperTwo J.postHeightHlo
      J.postHeightHhi S.upperBroad m

/-- Every fixed exceptional factor is positive because it lies in the
literal upper tail. -/
theorem fixedPositive
    (S : BankPaperCanonicalSectionNinePostHeightSourceInputsAt
      M Bsource R certificate I deltaStar hdelta J) :
    ∀ a ∈ R.paperFixedExceptionalFactors deltaStar, 0 < a := by
  have _hS : S = S := rfl
  intro a ha
  have htail :=
    R.paperFixedExceptionalFactors_subset_tail deltaStar ha
  exact Nat.zero_lt_of_lt (Finset.mem_Ioc.mp htail).1

/-- The existing one-shot source-prebridge theorem supplies the signed
ledger, actual measure, and full structured placement.  Its only remaining
numerical input is the already-required placement room. -/
theorem sourceToPostHeight
    (S : BankPaperCanonicalSectionNinePostHeightSourceInputsAt
      M Bsource R certificate I deltaStar hdelta J)
    (hroom : J.betaProt + S.Cmass / S.density ≤
      J.postHeightBridge.L) :
    BankPaperCanonicalGuardedStructuredAdditivePrebridgeMomentLedger
        (K := K0 + 1) J.postHeightBridge R certificate deltaStar
          J.betaProt J.roundedSourceSelector J.postHeightActiveSeed ∧
      BankPaperCanonicalActualActiveMeasureConstructor
        J.postHeightBridge.sampleData J.postHeightTarget
        (R.roughCanonicalGuardedCandidateSet certificate
          deltaStar (K0 + 1))
        J.placedPreSelector J.postHeightActiveSeed ∧
      BankPaperCanonicalGuardedStructuredAdditivePlacement
        (K := K0 + 1) J.postHeightBridge R certificate
        (R.paperFixedExceptionalFactors deltaStar) deltaStar J.betaProt
        J.roundedSourceSelector J.postHeightActiveSeed := by
  exact
    bankPaperCanonicalSectionNinePostHeight_sourcePrebridge_actualMeasure_and_placement_of_sourceState
      (K := K0 + 1) J.postHeightBridge R certificate J.Tsource I
        S.lowerOne S.upperTwo J.postHeightHlo J.postHeightHhi
        S.upperBroad deltaStar J.betaProt J.alpha J.beta J.qTilde
        J.postHeightTargetInputs J.roundedQ0_eq_postHeightBridge
        S.qn_one_le S.hprime S.hpattern S.headPrimes
        (by intro p _hp; rfl) S.headSeparated S.roughDepth
        S.outsideGuard S.betaProt_nonneg S.sourceState
        S.Cmass S.density S.Cmass_nonneg S.density_pos
        S.massUpper S.cellDensity hroom

/-- The finite post-height seed has the pointwise `1/L` capacity supplied by
the mass and cell-density inputs. -/
theorem activeSeedUpper
    (S : BankPaperCanonicalSectionNinePostHeightSourceInputsAt
      M Bsource R certificate I deltaStar hdelta J)
    (m : J.postHeightBridge.sampleData.Sample) :
    J.postHeightActiveSeed m ≤
      (S.Cmass / S.density) / J.postHeightBridge.L := by
  exact
    bankPaperCanonicalSectionNinePostHeightActiveSeed_le_of_massAndCellDensity
      J.postHeightBridge I J.postHeightHlo J.postHeightHhi
        J.postHeightTargetInputs S.Cmass S.density S.Cmass_nonneg
        S.density_pos S.massUpper S.cellDensity m

end BankPaperCanonicalSectionNinePostHeightSourceInputsAt

/-! ## Remaining Proposition 8.7 and slack inputs -/



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

/-- Nonnegativity of the pointwise active capacity. -/
theorem activeCapacity_nonneg
    (A : BankPaperCanonicalSectionNinePostHeightDependentInputsAt
      M Bsource R certificate I deltaStar sigma Cpost hdelta J S) :
    0 ≤ S.Cmass / S.density :=
  (fun _ =>
    div_nonneg S.Cmass_nonneg S.density_pos.le) A

/-- The final large-`L` inequality contains the placement-room inequality
needed by the source-to-post-height one-shot theorem. -/
theorem placementRoom
    (A : BankPaperCanonicalSectionNinePostHeightDependentInputsAt
      M Bsource R certificate I deltaStar sigma Cpost hdelta J S) :
    J.betaProt + S.Cmass / S.density ≤ J.postHeightBridge.L := by
  have hexp :
      0 ≤ Real.exp (2 *
        ((Erdos390.Full.PaperStatisticNorm.valuationLogCoefficient
              2 J.postHeightBridge.sampleData.W +
          J.postHeightBridge.nuisanceStatisticCoefficient 2) *
            (3 * (A.radius : Real)))) :=
    (Real.exp_pos _).le
  have hproduct :
      0 ≤ Real.exp (2 *
          ((Erdos390.Full.PaperStatisticNorm.valuationLogCoefficient
                2 J.postHeightBridge.sampleData.W +
            J.postHeightBridge.nuisanceStatisticCoefficient 2) *
              (3 * (A.radius : Real)))) *
        (S.Cmass / S.density) :=
    mul_nonneg hexp A.activeCapacity_nonneg
  calc
    J.betaProt + S.Cmass / S.density ≤ A.Cfixed := A.fixedRoom
    _ ≤ A.Cfixed +
          Real.exp (2 *
            ((Erdos390.Full.PaperStatisticNorm.valuationLogCoefficient
                  2 J.postHeightBridge.sampleData.W +
              J.postHeightBridge.nuisanceStatisticCoefficient 2) *
                (3 * (A.radius : Real)))) *
            (S.Cmass / S.density) + sigma := by
        linarith [hproduct, A.sigma_nonneg]
    _ ≤ J.postHeightBridge.L := A.largeL

/-- Frozen-log invariance identifies the rounded `Lambda0` with the
post-height placed frozen ledger. -/
theorem Lambda0_eq_placedFrozenLogMass
    (A : BankPaperCanonicalSectionNinePostHeightDependentInputsAt
      M Bsource R certificate I deltaStar sigma Cpost hdelta J S) :
    J.Lambda0 =
      bankPaperCanonicalActualFrozenLogMass
        J.postHeightBridge.sampleData
        (R.paperFixedExceptionalFactors deltaStar)
        (baseBankFactors R.exactificationState)
        (R.roughCanonicalGuardedCandidateSet certificate
          deltaStar (K0 + 1))
        J.placedPreSelector J.postHeightActiveSeed := by
  have _hA : A = A := rfl
  calc
    J.Lambda0 =
        bankPaperCanonicalActualFrozenLogMass
          J.postHeightBridge.sampleData
          (R.paperFixedExceptionalFactors deltaStar)
          (baseBankFactors R.exactificationState)
          (R.roughCanonicalGuardedCandidateSet certificate
            deltaStar (K0 + 1))
          J.roundedSourceSelector J.roundedActiveSeed :=
      J.roundedLambda0_eq_postHeightBridge
    _ =
        bankPaperCanonicalActualFrozenLogMass
          J.postHeightBridge.sampleData
          (R.paperFixedExceptionalFactors deltaStar)
          (baseBankFactors R.exactificationState)
          (R.roughCanonicalGuardedCandidateSet certificate
            deltaStar (K0 + 1))
          J.placedPreSelector J.postHeightActiveSeed := by
      symm
      exact
        bankPaperCanonicalSectionNinePostHeightPlaced_actualFrozenLogMass_eq_roundedSource
          (K := K0 + 1) J.postHeightBridge R certificate
            (R.paperFixedExceptionalFactors deltaStar)
            (baseBankFactors R.exactificationState) J.Tsource I
            J.postHeightHlo J.postHeightHhi J.postHeightTargetInputs
            deltaStar J.betaProt J.alpha J.beta J.qTilde
            S.activeSmooth S.activeBroad

/-- The ordinary logarithmic target is now an output, not an input field. -/
theorem ordinaryLogCompatible
    (A : BankPaperCanonicalSectionNinePostHeightDependentInputsAt
      M Bsource R certificate I deltaStar sigma Cpost hdelta J S) :
    BankPaperCanonicalSelectorOrdinaryLogCompatible
      (W := J.postHeightBridge.sampleData.W) R certificate
      (R.paperFixedExceptionalFactors deltaStar)
      (R.roughCanonicalGuardedCandidateSet certificate
        deltaStar (K0 + 1))
      J.placedPreSelector := by
  have Hconstruction := S.sourceToPostHeight A.placementRoom
  exact
    bankPaperCanonicalSectionNinePostHeight_initialSelector_ordinaryLogCompatible
      J.postHeightBridge R certificate
        (R.paperFixedExceptionalFactors deltaStar)
        (R.roughCanonicalGuardedCandidateSet certificate
          deltaStar (K0 + 1))
        J.placedPreSelector I J.postHeightHlo J.postHeightHhi
        J.postHeightTargetInputs Hconstruction.2.1
        Hconstruction.2.2.2.2 J.Lambda0 (by rfl)
        A.Lambda0_eq_placedFrozenLogMass S.fixedPositive S.charge_dvd

/-- The placed frozen pointwise ledger follows from the rounded one by the
pointwise arbitrary-seed cancellation. -/
theorem placedFrozenLedger
    (A : BankPaperCanonicalSectionNinePostHeightDependentInputsAt
      M Bsource R certificate I deltaStar sigma Cpost hdelta J S)
    (m : J.postHeightBridge.sampleData.Sample) :
    BridgeData.frozenAmbientWeight
        (bankPaperCanonicalActualFrozenValue
          (candidates :=
            R.roughCanonicalGuardedCandidateSet certificate
              deltaStar (K0 + 1)))
        (bankPaperCanonicalActualFrozenWeight
          J.postHeightBridge.sampleData
          (R.roughCanonicalGuardedCandidateSet certificate
            deltaStar (K0 + 1))
          J.placedPreSelector J.postHeightActiveSeed)
        (J.postHeightBridge.sampleData.value m) ≤
      A.Cfixed / J.postHeightBridge.L := by
  calc
    BridgeData.frozenAmbientWeight
        (bankPaperCanonicalActualFrozenValue
          (candidates :=
            R.roughCanonicalGuardedCandidateSet certificate
              deltaStar (K0 + 1)))
        (bankPaperCanonicalActualFrozenWeight
          J.postHeightBridge.sampleData
          (R.roughCanonicalGuardedCandidateSet certificate
            deltaStar (K0 + 1))
          J.placedPreSelector J.postHeightActiveSeed)
        (J.postHeightBridge.sampleData.value m) =
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
        (J.postHeightBridge.sampleData.value m) := by
      classical
      unfold BridgeData.frozenAmbientWeight
      unfold
        BankPaperCanonicalSectionNinePostHeightBridgeInputsAt.placedPreSelector
        BankPaperCanonicalSectionNinePostHeightBridgeInputsAt.postHeightActiveSeed
        BankPaperCanonicalSectionNinePostHeightBridgeInputsAt.roundedSourceSelector
        BankPaperCanonicalSectionNinePostHeightBridgeInputsAt.roundedActiveSeed
      apply Finset.sum_congr rfl
      intro a _ha
      rw [
        bankPaperCanonicalSectionNinePostHeightPlaced_actualFrozenWeight_eq_roundedSource
          (K := K0 + 1) J.postHeightBridge R certificate J.Tsource I
            J.postHeightHlo J.postHeightHhi J.postHeightTargetInputs
            deltaStar J.betaProt J.alpha J.beta J.qTilde
            S.activeSmooth S.activeBroad a]
    _ ≤ A.Cfixed / J.postHeightBridge.L :=
      A.roundedFrozenLedger m

/-- The fresh active baseline has the same pointwise capacity as its scaled
seed. -/
theorem activeLedger
    (A : BankPaperCanonicalSectionNinePostHeightDependentInputsAt
      M Bsource R certificate I deltaStar sigma Cpost hdelta J S)
    (m : J.postHeightBridge.sampleData.Sample) :
    J.postHeightBridge.baseline.baseWeight m ≤
      (S.Cmass / S.density) / J.postHeightBridge.L := by
  have _hA : A = A := rfl
  rw [J.postHeightBridge_baseWeight]
  exact S.activeSeedUpper m

/-- The exact ordinary-log identity and the placed deficit rate produce the
marked-band target envelopes required by Proposition 8.7. -/
theorem targetEnvelopes
    (A : BankPaperCanonicalSectionNinePostHeightDependentInputsAt
      M Bsource R certificate I deltaStar sigma Cpost hdelta J S) :
    J.postHeightBridge.HasTargetEnvelopes (7 * A.Cinitial)
      (fun j => J.postHeightBridge.markedBandResidual
        (bankPaperCanonicalActualActiveMarkedTarget
          J.postHeightBridge R certificate
          (R.paperFixedExceptionalFactors deltaStar)
          (R.roughCanonicalGuardedCandidateSet certificate
            deltaStar (K0 + 1))
          J.placedPreSelector J.postHeightActiveSeed) 0 j) := by
  have Hconstruction := S.sourceToPostHeight A.placementRoom
  exact
    bankPaperCanonicalActualInitialHasTargetEnvelopes_of_selectorDeficit
      J.postHeightBridge R certificate
        (R.paperFixedExceptionalFactors deltaStar)
        (R.roughCanonicalGuardedCandidateSet certificate
          deltaStar (K0 + 1))
        J.placedPreSelector J.postHeightActiveSeed
        Hconstruction.2.1 J.postHeightBridge_baseWeight
        A.Cinitial A.Cinitial_nonneg A.selectorDeficit
        A.ordinaryLogCompatible A.primeDeviation

/-- The protected reserve is built into the smooth additive refinement. -/
theorem protectedReserve
    (A : BankPaperCanonicalSectionNinePostHeightDependentInputsAt
      M Bsource R certificate I deltaStar sigma Cpost hdelta J S)
    (x : Nat)
    (hx : x ∈ R.roughCanonicalGuardedBroadCorrectionPool certificate
      deltaStar J.postHeightBridge.sampleData.W (K0 + 1) 1) :
    sigma / J.postHeightBridge.L +
        bankPaperCanonicalActiveSeedAmbientWeight
          J.postHeightBridge.sampleData J.postHeightActiveSeed x ≤
      J.placedPreSelector x := by
  have hrefine :=
    bankPaperCanonicalGuardedSmoothAdditiveRefinement_protectedReserve
      (K := K0 + 1) J.postHeightBridge R certificate
        J.roundedSourceSelector J.postHeightActiveSeed
        A.sigma_le_betaProt hx
  rw [←
    bankPaperCanonicalGuardedStructuredAdditivePlacementSelector_eq_refinement_of_mem_pool
      (K := K0 + 1) J.postHeightBridge R certificate
        J.roundedSourceSelector J.postHeightActiveSeed hx] at hrefine
  simpa only [
    BankPaperCanonicalSectionNinePostHeightBridgeInputsAt.placedPreSelector,
    bankPaperCanonicalSectionNinePostHeightPlacedPreSelector,
    bankPaperCanonicalTopFrozenRoundedPostHfitStructuredPreSelector,
    bankPaperCanonicalPostHfitStructuredPreSelectorOfSource] using
    hrefine

/-- The interval cap `I.upper ≤ 2` supplies the producer's physical upper
bound with the fixed value `C = 2`. -/
theorem physicalUpper
    (A : BankPaperCanonicalSectionNinePostHeightDependentInputsAt
      M Bsource R certificate I deltaStar sigma Cpost hdelta J S)
    (sign : PhysicalSign) :
    J.postHeightBridge.sampleData.hi sign ≤
      physicalBound 2 J.postHeightBridge.sampleData.n := by
  have _hA : A = A := rfl
  rw [J.postHeightHhi sign]
  unfold physicalBound
  exact Nat.floor_mono
    (mul_le_mul_of_nonneg_right (S.upperTwo sign) (by positivity))

end BankPaperCanonicalSectionNinePostHeightDependentInputsAt

/-! ## Exact placement-rate transport -/



/-! ## Finite package producer and synchronized adapter -/

/-- Produce the top-frozen rounded Post-hfit guarded-slack package on the
fresh post-height bridge. -/
theorem
    exists_bankPaperCanonicalTopFrozenRoundedPostHfitGuardedSlackPackage_of_postHeightInputs
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
      M Bsource R certificate I deltaStar hdelta J)
    (A : BankPaperCanonicalSectionNinePostHeightDependentInputsAt
      M Bsource R certificate I deltaStar sigma Cpost hdelta J S) :
    ∃ quota : Int, ∃ path : Real → J.postHeightBridge.ParamSpace,
      ∃ endpoint : Nat → Real,
        BankPaperCanonicalTopFrozenRoundedPostHfitGuardedSlackPackage
          (K := K0 + 1) J.postHeightBridge R certificate
          (R.paperFixedExceptionalFactors deltaStar) J.Tsource
          deltaStar J.betaProt J.alpha J.beta J.qTilde sigma
          J.postHeightActiveSeed J.postHeightActiveSeed
          A.radius Cpost A.cellIndex quota path endpoint := by
  have Hconstruction := S.sourceToPostHeight A.placementRoom
  have hfeasible :
      ∀ a ∈ R.roughCanonicalGuardedCandidateSet certificate
          deltaStar (K0 + 1),
        0 ≤
            bankPaperCanonicalTopFrozenRoundedPostHfitStructuredPreSelector
              (K := K0 + 1) J.postHeightBridge R certificate
                J.Tsource deltaStar J.betaProt J.alpha J.beta
                J.qTilde J.postHeightActiveSeed a ∧
          bankPaperCanonicalTopFrozenRoundedPostHfitStructuredPreSelector
              (K := K0 + 1) J.postHeightBridge R certificate
                J.Tsource deltaStar J.betaProt J.alpha J.beta
                J.qTilde J.postHeightActiveSeed a ≤ 1 := by
    simpa only [
      BankPaperCanonicalSectionNinePostHeightBridgeInputsAt.placedPreSelector,
      bankPaperCanonicalSectionNinePostHeightPlacedPreSelector,
      bankPaperCanonicalTopFrozenRoundedPostHfitStructuredPreSelector,
      bankPaperCanonicalPostHfitStructuredPreSelectorOfSource] using
      Hconstruction.2.2.1
  exact
    exists_bankPaperCanonicalTopFrozenRoundedPostHfitGuardedSlackPackage_of_sourceState
      (K := K0 + 1) (T := J.postHeightTarget)
      J.postHeightBridge R certificate
      (R.paperFixedExceptionalFactors deltaStar) J.Tsource
      deltaStar J.betaProt J.alpha J.beta J.qTilde sigma
      J.postHeightActiveSeed J.postHeightActiveSeed S.sourceState
      hfeasible Hconstruction.1 Hconstruction.2.1
      J.postHeightBridge_baseWeight S.headSeparated
      (7 * A.Cinitial) A.Cinitial A.Cfixed
      (S.Cmass / S.density) A.targetEnvelopes A.selectorDeficit
      A.placedFrozenLedger A.activeLedger A.radius Cpost A.localP87
      A.cellIndex (S.Cmass / S.density) A.activeCapacity_nonneg
      S.activeSeedUpper A.fixedRoom 2 (by norm_num) A.W_large
      A.physicalUpper A.activeCapacity_nonneg A.protectedReserve
      A.largeL A.nonsmooth

/-- Package one fixed post-height construction as the public synchronized
top-frozen input.  Every witness is the same witness used to define
`logY`, `Lambda0`, `Tpost`, and `Bpost`. -/
theorem
    bankPaperCanonicalSectionNineTopFrozenSynchronizedPostHfitInputAt_of_postHeightInputs
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
      M Bsource R certificate I deltaStar hdelta J)
    (A : BankPaperCanonicalSectionNinePostHeightDependentInputsAt
      M Bsource R certificate I deltaStar sigma Cpost hdelta J S)
    (hcellIndex :
      A.cellIndex =
        bankPaperCanonicalRatioCellIndex M hdelta
          J.postHeightBridge.n_gt_one J.hW J.scaleSeparation rho) :
    BankPaperCanonicalSectionNineTopFrozenSynchronizedPostHfitInputAt
      M J.postHeightBridge c depth K0 deltaStar rho sigma Cpost hdelta := by
  obtain ⟨quota, path, endpoint, Hpost⟩ :=
    exists_bankPaperCanonicalTopFrozenRoundedPostHfitGuardedSlackPackage_of_postHeightInputs
      M Bsource R certificate I deltaStar sigma Cpost hdelta J S A
  refine
    ⟨R, certificate, S.combined_dvd, S.base_dvd, S.charge_dvd,
      S.target_tail, J.hW, J.scaleSeparation, J.postHeightBridge_partition,
      J.Tsource, J.betaProt, J.alpha, J.beta, J.qTilde,
      J.postHeightActiveSeed, J.postHeightActiveSeed, A.radius,
      quota, path, endpoint, ?_⟩
  rw [hcellIndex] at Hpost
  exact Hpost

end BankPaperRealization

end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankPaperCanonicalPostHfitBalancedAlphaEventually -/
section


/-!
# Eventual feasibility of the canonical Post-Hfit balanced coefficient

The paper first chooses a positive total broad coefficient
`beta < c / (3 * roughHeadDensity W)` and then takes the fixed high-block
multiplicity sufficiently large.  This file records that choice at the
exact finite level.

No quota or height-ledger asymptotic is needed.  The defining ceiling gives

`c * n / log n <= upperTailLength c n`

pointwise, which already makes the numerator of the balanced coefficient
nonnegative.  Taking the multiplicity at least the reciprocal head density
makes the same numerator at most its denominator.
-/

open Filter Set

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.PaperBridgeFit

noncomputable section

/-! ## Finite balanced-coefficient algebra -/

/-- The exact two inequalities behind feasibility of the balanced raw
coefficient.  The hypotheses are deliberately stated before specializing
`h` to the paper's integral upper-tail length. -/
theorem roughHeadBalancedAlpha_mem_Icc_of_tail_lower
    {W n h K : Nat} {c beta ell : Real}
    (hc : 0 < c) (hn : 0 < n) (hKpos : 0 < K)
    (hell : 0 < ell) (hbeta : 0 ≤ beta)
    (hbetaUpper : beta ≤ c / roughHeadDensity W)
    (hKlarge : 1 / roughHeadDensity W ≤ (K : Real))
    (htail : c * (n : Real) / ell ≤ (h : Real)) :
    roughHeadBalancedAlpha W n h K beta ell ∈
      Icc (0 : Real) 1 := by
  have hdensity : 0 < roughHeadDensity W :=
    roughHeadDensity_pos W
  have hnReal : (0 : Real) < (n : Real) := by
    exact_mod_cast hn
  have htailBase : 0 < c * (n : Real) / ell :=
    div_pos (mul_pos hc hnReal) hell
  have hhReal : (0 : Real) < (h : Real) :=
    htailBase.trans_le htail
  have hh : 0 < h := by
    exact_mod_cast hhReal
  have hden :
      0 < (((K * h : Nat) : Real)) := by
    exact_mod_cast Nat.mul_pos hKpos hh
  have hsub :
      (((n - K * h : Nat) : Real)) ≤ (n : Real) := by
    exact_mod_cast Nat.sub_le n (K * h)
  have hbetaDiv : 0 ≤ beta / ell :=
    div_nonneg hbeta hell.le
  have htermNonneg :
      0 ≤ (beta / ell) * (((n - K * h : Nat) : Real)) :=
    mul_nonneg hbetaDiv (Nat.cast_nonneg _)
  have htermUpper :
      (beta / ell) * (((n - K * h : Nat) : Real)) ≤
        (h : Real) / roughHeadDensity W := by
    calc
      (beta / ell) * (((n - K * h : Nat) : Real)) ≤
          (beta / ell) * (n : Real) :=
        mul_le_mul_of_nonneg_left hsub hbetaDiv
      _ = beta * ((n : Real) / ell) := by ring
      _ ≤ (c / roughHeadDensity W) * ((n : Real) / ell) :=
        mul_le_mul_of_nonneg_right hbetaUpper
          (div_nonneg hnReal.le hell.le)
      _ = (c * (n : Real) / ell) / roughHeadDensity W := by ring
      _ ≤ (h : Real) / roughHeadDensity W :=
        div_le_div_of_nonneg_right htail hdensity.le
  have hnumNonneg :
      0 ≤ (h : Real) / roughHeadDensity W -
        (beta / ell) * (((n - K * h : Nat) : Real)) :=
    sub_nonneg.mpr htermUpper
  have hheadUpper :
      (h : Real) / roughHeadDensity W ≤
        (((K * h : Nat) : Real)) := by
    calc
      (h : Real) / roughHeadDensity W =
          (1 / roughHeadDensity W) * (h : Real) := by ring
      _ ≤ (K : Real) * (h : Real) :=
        mul_le_mul_of_nonneg_right hKlarge hhReal.le
      _ = (((K * h : Nat) : Real)) := by
        norm_num only [Nat.cast_mul]
  constructor
  · rw [roughHeadBalancedAlpha]
    exact div_nonneg hnumNonneg hden.le
  · rw [roughHeadBalancedAlpha]
    exact
      (div_le_one hden).2
        ((sub_le_self _ htermNonneg).trans hheadUpper)

namespace BankPaperRealization

/-! ## Canonical bridge specialization -/

/-- Pointwise feasibility for the literal Post-Hfit coefficient.  The only
scale input is the paper's exact upper-tail ceiling. -/
theorem bankPaperCanonicalPostHfitBalancedAlpha_mem_Icc_of_paperBounds
    {Head Band : Type*} [Fintype Head] [DecidableEq Head]
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData Head Band) {c : Real} (K0 : Nat)
    (betaProt betaAct : Real) (hc : 0 < c)
    (hbeta : 0 ≤ betaProt + betaAct)
    (hbetaUpper :
      betaProt + betaAct ≤
        c / roughHeadDensity B.sampleData.W)
    (hKlarge :
      1 / roughHeadDensity B.sampleData.W ≤
        (((K0 + 1 : Nat) : Real))) :
    bankPaperCanonicalPostHfitBalancedAlpha
        B c K0 betaProt betaAct ∈ Icc (0 : Real) 1 := by
  have htail :
      c * (B.sampleData.n : Real) / B.L ≤
        (upperTailLength c B.sampleData.n : Real) := by
    calc
      c * (B.sampleData.n : Real) / B.L =
          c * secondOrderScale B.sampleData.n := by
        unfold BridgeData.L secondOrderScale
        ring
      _ ≤ (upperTailLength c B.sampleData.n : Real) := by
        simpa only [upperTailLength] using
          (Nat.le_ceil
            (c * secondOrderScale B.sampleData.n))
  simpa only [bankPaperCanonicalPostHfitBalancedAlpha] using
    (roughHeadBalancedAlpha_mem_Icc_of_tail_lower
      (W := B.sampleData.W) (n := B.sampleData.n)
      (h := upperTailLength c B.sampleData.n) (K := K0 + 1)
      (c := c) (beta := betaProt + betaAct) (ell := B.L)
      hc (Nat.zero_lt_of_lt B.n_gt_one) (by omega)
      B.L_pos hbeta hbetaUpper hKlarge htail)

/-- Uniform family form used by the Section 9 supplier.  It applies to every
bridge with the synchronized width, hence in particular to the coherent
canonical/post-height bridge family. -/
theorem eventually_bankPaperCanonicalPostHfitBalancedAlpha_mem_Icc
    {Head Band : Type*} [Fintype Head] [DecidableEq Head]
    [Fintype Band] [DecidableEq Band]
    (W K0 : Nat) {c betaProt betaAct : Real} (hc : 0 < c)
    (hbeta : 0 ≤ betaProt + betaAct)
    (hbetaUpper :
      betaProt + betaAct ≤ c / roughHeadDensity W)
    (hKlarge :
      1 / roughHeadDensity W ≤ (((K0 + 1 : Nat) : Real))) :
    ∀ᶠ n : Nat in atTop,
      ∀ B : BridgeData Head Band,
        B.sampleData.n = n →
        B.sampleData.W = W →
        bankPaperCanonicalPostHfitBalancedAlpha
            B c K0 betaProt betaAct ∈ Icc (0 : Real) 1 := by
  refine Eventually.of_forall ?_
  intro n B _hBn hBW
  apply
    bankPaperCanonicalPostHfitBalancedAlpha_mem_Icc_of_paperBounds
      B K0 betaProt betaAct hc hbeta
  · simpa only [hBW] using hbetaUpper
  · simpa only [hBW] using hKlarge





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



/-- Package the outputs of the already-exported finite/eventual chains into
the non-final local reduction.

The hypotheses after `Hgap` are not genuine gap fields:

* `hselector` is the selected output of the placed-selector rate theorem;
* `hroundedFrozenLedger` is the additive-placement frozen invariance chain;
* `hprimeDeviation` is `actualMomentReady` plus
  `MomentReady.actual_L1_bound_of_ready`;
* `hlocalP87` is the varying-active-mass canonical P87 output chosen after
  `Cinitial`;
* `hlargeL` and `hnonsmooth` are the exported exponential-slack and
  balanced-nonsmooth events.

They remain separate arguments here because eventual intersection is a
family-level operation, while the primitive producer obligation above
is still open.  The signature fixes `Cinitial`, then `radius` and `Cpost`,
before the later mesh, matching the canonical varying-mass P87 order. -/
theorem
    bankPaperCanonicalSectionNinePostHeightLocalInputReduction_of_exportedFields
    {c : Real} {depth K0 E : Nat}
    {mu sourceMarginFloor headMarginFloor physicalEtaFloor
      postMarginFloor : Real}
    {logY Lambda0 mFrozen qTilde : Nat → Real}
    (deltaStar rho sigma Cinitial : Real)
    (hCinitial : 0 ≤ Cinitial)
    (radius : NNReal)
    (Cpost : Real)
    {delta eta : Real} (M : RegularRelativeMesh.Mesh delta eta)
    {P : Finset Nat}
    (Bsource : BridgeData (PaperHeadSimplex.Tag P)
      (BankPaperCanonicalExponentBand M))
    (R : BankPaperRealization Bsource.sampleData.n
      (upperEndpoint Bsource.sampleData.n
        (upperTailLength c Bsource.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth
      Bsource.sampleData.n R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (I : PhysicalIntervals)
    (hdelta : 0 < delta)
    (J : BankPaperCanonicalSectionNinePostHeightBridgeInputsAt
      (K0 := K0) M Bsource R certificate I deltaStar hdelta)
    (S : BankPaperCanonicalSectionNinePostHeightSourceInputsAt
      M Bsource R certificate I deltaStar hdelta J)
    (_Hgap : BankPaperCanonicalSectionNinePostHeightPrimitiveGapsAt
      M Bsource R certificate I E deltaStar mu sourceMarginFloor
        headMarginFloor physicalEtaFloor postMarginFloor
        logY Lambda0 mFrozen qTilde hdelta J S)
    (halpha : 0 ≤ J.alpha ∧ J.alpha ≤ 1)
    (hselector :
      ∀ p ∈ primeBand J.postHeightBridge.sampleData.n
          J.postHeightBridge.sampleData.W,
        abs (bankPaperCanonicalSelectorValuationDeficit
          R certificate (R.paperFixedExceptionalFactors deltaStar)
            (R.roughCanonicalGuardedCandidateSet certificate
              deltaStar (K0 + 1))
            J.placedPreSelector p) ≤
          Cinitial * J.postHeightBridge.q /
            ((p : Real) * J.postHeightBridge.L))
    (hroundedFrozenLedger :
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
          (J.betaProt + S.Cmass / S.density) /
            J.postHeightBridge.L)
    (hprimeDeviation :
      J.postHeightBridge.primeDeviationL1 ≤
        7 * J.postHeightBridge.w)
    (hlocalP87 :
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
                  fixedValue fixedWeight quota)
    (hTwoW : 2 ≤ J.postHeightBridge.sampleData.W)
    (hsigma : 0 < sigma)
    (hsigmaProt : sigma ≤ J.betaProt)
    (hlargeL :
      (J.betaProt + S.Cmass / S.density) +
          Real.exp (2 *
            ((Erdos390.Full.PaperStatisticNorm.valuationLogCoefficient
                  2 J.postHeightBridge.sampleData.W +
              J.postHeightBridge.nuisanceStatisticCoefficient 2) *
                (3 * (radius : Real)))) *
            (S.Cmass / S.density) + sigma ≤
        J.postHeightBridge.L)
    (hnonsmooth :
      ∀ label,
        RoughCanonicalActiveNonexceptionalLabel
            J.postHeightBridge.sampleData.n deltaStar label →
          sigma / J.postHeightBridge.L +
              |R.roughCanonicalGuardedPostchargeCorrectionDensity
                certificate deltaStar
                J.postHeightBridge.sampleData.W (K0 + 1) label
                  J.alpha J.beta J.postHeightBridge.L| ≤
            J.beta / J.postHeightBridge.L ∧
          J.beta / J.postHeightBridge.L +
              |R.roughCanonicalGuardedPostchargeCorrectionDensity
                certificate deltaStar
                J.postHeightBridge.sampleData.W (K0 + 1) label
                  J.alpha J.beta J.postHeightBridge.L| ≤
            1 - sigma / J.postHeightBridge.L) :
    BankPaperCanonicalSectionNinePostHeightLocalInputReductionAt
      M Bsource R certificate I deltaStar rho sigma Cpost hdelta J S := by
  let A :
      BankPaperCanonicalSectionNinePostHeightDependentInputsAt
        M Bsource R certificate I deltaStar sigma Cpost hdelta J S :=
    { Cinitial := Cinitial
      Cfixed := J.betaProt + S.Cmass / S.density
      Cinitial_nonneg := hCinitial
      selectorDeficit := hselector
      roundedFrozenLedger := by
        exact hroundedFrozenLedger
      primeDeviation := hprimeDeviation
      radius := radius
      localP87 := by
        exact hlocalP87
      cellIndex :=
        bankPaperCanonicalRatioCellIndex M hdelta
          J.postHeightBridge.n_gt_one J.hW J.scaleSeparation rho
      fixedRoom := le_rfl
      W_large := by omega
      sigma_nonneg := hsigma.le
      sigma_le_betaProt := hsigmaProt
      largeL := by
        exact hlargeL
      nonsmooth := hnonsmooth }
  exact ⟨halpha, ⟨A, rfl⟩⟩

end BankPaperRealization

end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankPaperCanonicalSectionNinePostHeightSourceFirstFiniteExportedFields -/
section


/-!
# Finite exported fields for the source-first post-height bridge

This file isolates three finite consequences of the source-first `J`/`S`/
primitive-gap package which are needed by the eventual Section 9
orchestrator.

* The rounded frozen-top source has pointwise frozen remainder at most
  `(betaProt + Cactive) / L`.
* The guarded broad correction pool is nonempty.
* The local integer height adjustment is exactly the Section 8 analytic
  `d` family.

No eventual intersection or Proposition 8.7 parameter choice occurs here.
-/

open Set
open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.PaperBridgeFit
open Erdos390.Full.PaperGuardCensus
open Erdos390.Full.PaperHeadSimplex
open Erdos390.Full.RegularRelativeMesh

noncomputable section

namespace BankPaperRealization

section FiniteSourceFields

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
    (J : BankPaperCanonicalSectionNinePostHeightBridgeInputsAt
      (K0 := K0) M Bsource R certificate I deltaStar hdelta)
    (S : BankPaperCanonicalSectionNinePostHeightSourceInputsAt
      M Bsource R certificate I deltaStar hdelta J)

include S

/-! ## Rounded frozen ledger -/

/-- At an occupied post-height coordinate, the rounded source's frozen
remainder is exactly the explicit protected layer.  Floating rounding
changes the selector and its ambient active seed by the same amount. -/
theorem
    bankPaperCanonicalSectionNinePostHeight_roundedFrozenAmbientWeight_eq_protectedLayer
    (m : J.postHeightBridge.sampleData.Sample) :
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
        (J.postHeightBridge.sampleData.value m) =
      bankPaperCanonicalGuardedSmoothProtectedLayer (K := K0 + 1)
        J.postHeightBridge R certificate deltaStar J.betaProt
          (J.postHeightBridge.sampleData.value m) := by
  have hmActive :
      J.postHeightBridge.sampleData.value m ∈
        bankPaperCanonicalStructuredActiveValues
          J.postHeightBridge.sampleData :=
    mem_bankPaperCanonicalStructuredActiveValues.mpr ⟨m, rfl⟩
  have hmSmooth :
      J.postHeightBridge.sampleData.value m ∈
        R.roughCanonicalGuardedRow certificate
          deltaStar (K0 + 1) 1 :=
    S.activeSmooth hmActive
  have hmCandidate :
      J.postHeightBridge.sampleData.value m ∈
        R.roughCanonicalGuardedCandidateSet certificate
          deltaStar (K0 + 1) :=
    (mem_completeRoughRowFiber.mp hmSmooth).1
  rw [frozenAmbientWeight_eq_bankPaperCanonicalActualFrozenWeight,
    if_pos hmCandidate]
  have hchange :
      J.roundedSourceSelector
            (J.postHeightBridge.sampleData.value m) -
          bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop
            (K := K0 + 1) J.postHeightBridge R certificate
              deltaStar J.betaProt J.alpha J.beta
              (bankPaperCanonicalScaledActiveSeed
                J.Tsource J.qTilde)
              (J.postHeightBridge.sampleData.value m) =
        bankPaperCanonicalActiveSeedAmbientWeight
            J.postHeightBridge.sampleData J.roundedActiveSeed
            (J.postHeightBridge.sampleData.value m) -
          bankPaperCanonicalActiveSeedAmbientWeight
            J.postHeightBridge.sampleData
            (bankPaperCanonicalScaledActiveSeed J.Tsource J.qTilde)
            (J.postHeightBridge.sampleData.value m) := by
    simpa only [
      BankPaperCanonicalSectionNinePostHeightBridgeInputsAt.roundedSourceSelector,
      BankPaperCanonicalSectionNinePostHeightBridgeInputsAt.roundedActiveSeed] using
      (bankPaperCanonicalTopFrozenRoundedSourceSelector_sub_qTildeSource_eq_ambient_sub
        (K := K0 + 1) J.postHeightBridge R certificate J.Tsource
          deltaStar J.betaProt J.alpha J.beta J.qTilde
          S.activeSmooth hmCandidate)
  calc
    J.roundedSourceSelector
          (J.postHeightBridge.sampleData.value m) -
        bankPaperCanonicalActiveSeedAmbientWeight
          J.postHeightBridge.sampleData J.roundedActiveSeed
          (J.postHeightBridge.sampleData.value m) =
      bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop
          (K := K0 + 1) J.postHeightBridge R certificate
            deltaStar J.betaProt J.alpha J.beta
            (bankPaperCanonicalScaledActiveSeed J.Tsource J.qTilde)
            (J.postHeightBridge.sampleData.value m) -
        bankPaperCanonicalActiveSeedAmbientWeight
          J.postHeightBridge.sampleData
          (bankPaperCanonicalScaledActiveSeed J.Tsource J.qTilde)
          (J.postHeightBridge.sampleData.value m) := by
      linarith only [hchange]
    _ =
      roughHeadCompatibleRawWeight
        J.postHeightBridge.sampleData.W
        J.postHeightBridge.sampleData.n
        (upperTailLength c J.postHeightBridge.sampleData.n)
        (K0 + 1) J.alpha J.betaProt J.postHeightBridge.L
        (J.postHeightBridge.sampleData.value m) := by
      rw [
        bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop_apply_of_mem_smoothRow
          (K := K0 + 1) J.postHeightBridge R certificate
            (bankPaperCanonicalScaledActiveSeed J.Tsource J.qTilde)
            hmSmooth]
      ring
    _ =
      bankPaperCanonicalGuardedSmoothProtectedLayer (K := K0 + 1)
        J.postHeightBridge R certificate deltaStar J.betaProt
          (J.postHeightBridge.sampleData.value m) :=
      (bankPaperCanonicalGuardedSmoothProtectedLayer_eq_rawWeight_of_mem_smoothBroadRow
        (K := K0 + 1) J.postHeightBridge R certificate
          hmSmooth (S.activeBroad m)).symm

/-- The rounded source satisfies the precise pointwise frozen-ledger bound
used by
`bankPaperCanonicalSectionNinePostHeightLocalInputReduction_of_exportedFields`.
-/
theorem
    bankPaperCanonicalSectionNinePostHeight_roundedFrozenLedger_of_sourceInputs
    (m : J.postHeightBridge.sampleData.Sample) :
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
      (J.betaProt + S.Cmass / S.density) /
        J.postHeightBridge.L := by
  rw [
    bankPaperCanonicalSectionNinePostHeight_roundedFrozenAmbientWeight_eq_protectedLayer
      J S m]
  have hactiveCapacity : 0 ≤ S.Cmass / S.density :=
    div_nonneg S.Cmass_nonneg S.density_pos.le
  by_cases hpool :
      J.postHeightBridge.sampleData.value m ∈
        R.roughCanonicalGuardedBroadCorrectionPool certificate
          deltaStar J.postHeightBridge.sampleData.W (K0 + 1) 1
  · rw [
      bankPaperCanonicalGuardedSmoothProtectedLayer_apply_of_mem
        J.postHeightBridge R certificate hpool]
    exact div_le_div_of_nonneg_right
      (le_add_of_nonneg_right hactiveCapacity)
      J.postHeightBridge.L_pos.le
  · rw [
      bankPaperCanonicalGuardedSmoothProtectedLayer_apply_of_not_mem
        J.postHeightBridge R certificate hpool]
    exact div_nonneg
      (add_nonneg S.betaProt_nonneg hactiveCapacity)
      J.postHeightBridge.L_pos.le

/-! ## Broad-pool nonemptiness -/

/-- One zero-head physical cell supplies a literal member of the guarded
broad correction pool.  The witness comes from the nonempty structured
sample cell stored in `StructuredSampleData`; all arithmetic support facts
are already fields or consequences of `S`. -/
theorem
    bankPaperCanonicalSectionNinePostHeight_guardedBroadCorrectionPool_nonempty_of_sourceInputs :
    (R.roughCanonicalGuardedBroadCorrectionPool certificate
      deltaStar J.postHeightBridge.sampleData.W (K0 + 1) 1).Nonempty := by
  have hcellCard :
      0 < Fintype.card
        (J.postHeightBridge.sampleData.SampleAt
          ((none, .minus) : Cell (PaperHeadSimplex.Tag P))) :=
    J.postHeightBridge.sampleData.sampleAt_card_pos (none, .minus)
  let mAt :
      J.postHeightBridge.sampleData.SampleAt
        ((none, .minus) : Cell (PaperHeadSimplex.Tag P)) :=
    Classical.choice (Fintype.card_pos_iff.mp hcellCard)
  let m : J.postHeightBridge.sampleData.Sample :=
    ⟨(none, .minus), mAt⟩
  refine ⟨J.postHeightBridge.sampleData.value m, ?_⟩
  exact
    bankPaperCanonicalZeroHeadValue_mem_guardedBroadCorrectionPool_of_physicalIntervals
      (K := K0 + 1) J.postHeightBridge R certificate deltaStar
        S.hprime J.exponent S.hpattern S.headPrimes I
        S.lowerOne S.upperTwo J.postHeightHlo J.postHeightHhi
        S.upperBroad S.outsideGuard m .minus (by rfl)

/-! ## Exact analytic-family synchronization -/

variable
    {E : Nat}
    {mu sourceMarginFloor headMarginFloor physicalEtaFloor
      postMarginFloor : Real}
    {logY Lambda0 mFrozen qTilde : Nat → Real}
    (Hgap : BankPaperCanonicalSectionNinePostHeightPrimitiveGapsAt
      M Bsource R certificate I E deltaStar mu sourceMarginFloor
        headMarginFloor physicalEtaFloor postMarginFloor
        logY Lambda0 mFrozen qTilde hdelta J S)

include Hgap

/-- The local rounded `q0` is the literal Section 8 smooth `q0` family at
the source index. -/
theorem
    bankPaperCanonicalSectionNinePostHeight_q0_eq_smoothQ0Family_of_primitiveGaps :
    J.q0 =
      bankPaperCanonicalSmoothQ0Family
        mFrozen qTilde Bsource.sampleData.n := by
  rw [J.roundedQ0_eq_postHeightBridge]
  unfold bankPaperCanonicalTopFrozenRoundedActiveMass
    bankPaperCanonicalSmoothQ0Family
  rw [← Hgap.mFrozen_family, Hgap.qTilde_family]

/-- The integer selected in the finite post-height target is exactly the
analytic Section 8 integer-height family, viewed in `Real`. -/
theorem
    bankPaperCanonicalSectionNinePostHeight_d_eq_smoothDRealFamily_of_primitiveGaps :
    (J.d : Real) =
      bankPaperCanonicalSmoothDRealFamily
        mu logY Lambda0 mFrozen qTilde
          J.postHeightBridge.sampleData.n := by
  have hfinal :
      J.q0 - (J.d : Real) =
        bankPaperCanonicalSmoothQ0Family
            mFrozen qTilde Bsource.sampleData.n -
          bankPaperCanonicalSmoothDRealFamily
            mu logY Lambda0 mFrozen qTilde Bsource.sampleData.n := by
    simpa only [
      BankPaperCanonicalSectionNinePostHeightBridgeInputsAt.qn,
      bankPaperCanonicalSectionNinePostHeightActiveMass_eq,
      bankPaperCanonicalSmoothFinalActiveMassFamily_eq_q0_sub_d] using
      Hgap.finalActiveMass_family
  rw [
    bankPaperCanonicalSectionNinePostHeight_q0_eq_smoothQ0Family_of_primitiveGaps
      J S Hgap] at hfinal
  have hdSource :
      (J.d : Real) =
        bankPaperCanonicalSmoothDRealFamily
          mu logY Lambda0 mFrozen qTilde Bsource.sampleData.n := by
    linarith only [hfinal]
  simpa only [J.postHeightBridge_sampleData] using hdSource

end FiniteSourceFields

end BankPaperRealization

end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankPaperCanonicalSectionNinePostHeightSourceFirstPreselectedPostHfitConnector -/
section


/-!
# Fixed-mesh Post-Hfit consumption with preselected constants

The global source-first orchestration chooses the placed-selector constant
and the uniform Proposition 8.7 constants before it selects the final mesh.
This file is the fixed-mesh consumption kernel for those choices.

It assumes the mesh-uniform placed-selector callback and the already
specialized one-mesh Proposition 8.7 callback.  It only intersects their
eventual fields with the genuine coherent bridge/source obligation and the
remaining exported numerical events.  In particular, it does not choose a
new selector constant, radius, or post-adjustment constant.
-/

open Filter Topology Set
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

/-- Consume constants selected before the final mesh and construct the
eventual synchronized frozen-top Post-Hfit input on that mesh.

`Hselector` is uniform in every later mesh; this theorem specializes it to
the displayed `M`.  `HP87` is already the corresponding single-mesh
callback.  The conclusion uses the supplied public bridge family `B` and
the preselected constant `CP87` literally. -/
theorem
    bankPaperCanonicalSectionNinePostHeight_sourceFirstPreselectedPostHfitInput
    {delta eta : Real} (M : RegularRelativeMesh.Mesh delta eta)
    {P : Finset Nat}
    (Patterns : PaperHeadSimplex.Tag P → Pattern)
    (I : PhysicalIntervals)
    (Cprom Cbank : Nat) (G : ∀ n, Ledger n Cprom Cbank)
    {c : Real} (depth W K0 E Ntail : Nat)
    (F : BankPaperCanonicalGuardedTailFamily c depth Ntail)
    (deltaStar betaProt betaAct mu sourceMarginFloor headMarginFloor
      physicalEtaFloor postMarginFloor Cmass density : Real)
    (logY Lambda0 mFrozen qTilde : Nat → Real)
    (rho sigma : Real)
    (Cinitial : Real) (radius : NNReal) (CP87 : Real)
    (hdelta : 0 < delta)
    (B : Nat → BridgeData (PaperHeadSimplex.Tag P)
      (BankPaperCanonicalExponentBand M))
    (Hsource :
      BankPaperCanonicalSectionNinePostHeightEventualCoherentBridgeSourceObligation
        P Patterns I Cprom Cbank G depth W K0 E Ntail F
          deltaStar betaProt betaAct mu sourceMarginFloor headMarginFloor
          physicalEtaFloor postMarginFloor Cmass density
          logY Lambda0 mFrozen qTilde M hdelta B)
    (Hselector :
      BankPaperCanonicalSectionNinePostHeightSourceFirstPreMeshPlacedSelectorCallback
        Patterns I Cprom Cbank G (c := c) depth W K0
          deltaStar betaProt betaAct mu
          logY Lambda0 mFrozen qTilde Cinitial)
    (HP87 :
      BankPaperCanonicalSectionNinePostHeightSourceFirstSpecializedEventualLocalP87Callback
        (c := c) M Patterns I Cprom Cbank G depth W K0 deltaStar
          betaProt betaAct postMarginFloor Cmass density
          (bankPaperCanonicalSmoothFinalActiveMassFamily
            mu logY Lambda0 mFrozen qTilde)
          Cinitial radius CP87 hdelta)
    (hCinitial : 0 ≤ Cinitial)
    (_hradius : 0 < (radius : Real))
    (_hCP87 : 0 ≤ CP87)
    (hc : 0 < c)
    (hTwoW : 2 ≤ W)
    (hdeltaStar : 0 < deltaStar)
    (hbetaProt : 0 ≤ betaProt)
    (hbetaAct : 0 < betaAct)
    (hbetaUpper :
      betaProt + betaAct ≤ c / roughHeadDensity W)
    (hKlarge :
      1 / roughHeadDensity W ≤ (((K0 + 1 : Nat) : Real)))
    (hCmass : 0 ≤ Cmass)
    (hdensity : 0 < density)
    (hsigma : 0 < sigma)
    (hsigmaProt : sigma ≤ betaProt)
    (hMoment : canonicalActualMomentCutoff ≤ W) :
    BankPaperCanonicalSectionNineTopFrozenSynchronizedPostHfitInput
      M B c depth K0 deltaStar rho sigma CP87 hdelta := by
  have Halpha :=
    eventually_bankPaperCanonicalPostHfitBalancedAlpha_mem_Icc
      (Head := PaperHeadSimplex.Tag P)
      (Band := BankPaperCanonicalExponentBand M)
      W K0 hc (add_nonneg hbetaProt hbetaAct.le)
        hbetaUpper hKlarge
  have Hmoment :=
    eventually_bankPaperCanonical_actualMomentReady
      M hdelta W hMoment
  have Hnonsmooth :=
    eventually_roughCanonicalBalancedNonsmoothBounds
      W K0 hc hdeltaStar hbetaAct hsigmaProt
  have hLTop : Tendsto L atTop atTop := by
    simpa only [L] using
      Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have HbetaRoom :
      ∀ᶠ n : Nat in atTop, betaProt + betaAct ≤ L n :=
    hLTop.eventually (eventually_ge_atTop (betaProt + betaAct))
  have hCactive : 0 ≤ Cmass / density :=
    div_nonneg hCmass hdensity.le
  have HlargeL :=
    BridgeData.eventually_canonical_exponential_slack_le_L
      (Head := PaperHeadSimplex.Tag P)
      (Band := BankPaperCanonicalExponentBand M)
      2 (by norm_num) W radius
        ((betaProt + Cmass / density) + sigma)
        (Cmass / density) hCactive
  simp only
    [BankPaperCanonicalSectionNinePostHeightEventualCoherentBridgeSourceObligation]
    at Hsource
  simp only
    [BankPaperCanonicalSectionNinePostHeightSourceFirstPreMeshPlacedSelectorCallback]
    at Hselector
  simp only
    [BankPaperCanonicalSectionNinePostHeightSourceFirstSpecializedEventualLocalP87Callback]
    at HP87
  simp only
    [BankPaperCanonicalSectionNineTopFrozenSynchronizedPostHfitInput]
  filter_upwards [
      Hsource, Halpha, Hselector, HP87, Hmoment, Hnonsmooth,
      HbetaRoom, HlargeL,
      eventually_ge_atTop (centralAnchorCutoffThreshold depth),
      eventually_yNat_lt_centralAnchorCutoff depth]
      with n hsourceN halphaN hselectorN hP87N hmomentN
        hnonsmoothN hbetaRoomN hlargeLN hnCutoff hyCutoff
  rcases hsourceN with
    ⟨Bsource, hnTail, J, S, Hgap, hsep, hremaining,
      hbridge, hBn, hBW, hbetaProtSync, hbetaActSync,
      hcanonical, hqTilde, hCmassSync, hdensitySync⟩
  subst n
  let R := F.realization Bsource.sampleData.n hnTail
  let certificate := F.certificate Bsource.sampleData.n hnTail
  have halpha : 0 ≤ J.alpha ∧ J.alpha ≤ 1 := by
    apply Set.mem_Icc.mp
    simpa only [
        BankPaperCanonicalSectionNinePostHeightBridgeInputsAt.alpha,
        hbetaProtSync, hbetaActSync] using
      halphaN Bsource rfl hBW
  have hbetaBox :
      0 ≤ J.beta / J.postHeightBridge.L ∧
        J.beta / J.postHeightBridge.L ≤ 1 := by
    have hbetaNonneg : 0 ≤ J.beta := by
      simpa only [
        BankPaperCanonicalSectionNinePostHeightBridgeInputsAt.beta,
        hbetaProtSync, hbetaActSync] using
        add_nonneg hbetaProt hbetaAct.le
    have hbetaLe : J.beta ≤ J.postHeightBridge.L := by
      simpa only [
        BankPaperCanonicalSectionNinePostHeightBridgeInputsAt.beta,
        hbetaProtSync, hbetaActSync,
        BankPaperCanonicalSectionNinePostHeightBridgeInputsAt.postHeightBridge_sampleData,
        BridgeData.L] using hbetaRoomN
    exact
      ⟨div_nonneg hbetaNonneg J.postHeightBridge.L_pos.le,
        (div_le_one J.postHeightBridge.L_pos).2 hbetaLe⟩
  have hpool :
      (R.roughCanonicalGuardedBroadCorrectionPool certificate
        deltaStar J.postHeightBridge.sampleData.W
          (K0 + 1) 1).Nonempty :=
    bankPaperCanonicalSectionNinePostHeight_guardedBroadCorrectionPool_nonempty_of_sourceInputs
      J S
  have hdFamily :
      (J.d : Real) =
        bankPaperCanonicalSmoothDRealFamily
          mu logY Lambda0 mFrozen qTilde Bsource.sampleData.n := by
    simpa only [
      BankPaperCanonicalSectionNinePostHeightBridgeInputsAt.postHeightBridge_sampleData] using
      (bankPaperCanonicalSectionNinePostHeight_d_eq_smoothDRealFamily_of_primitiveGaps
        J S Hgap)
  have hqFamily :
      J.postHeightBridge.q =
        bankPaperCanonicalSmoothFinalActiveMassFamily
          mu logY Lambda0 mFrozen qTilde Bsource.sampleData.n := by
    calc
      J.postHeightBridge.q = J.qn := J.postHeightBridge_q
      _ =
          bankPaperCanonicalSmoothFinalActiveMassFamily
            mu logY Lambda0 mFrozen qTilde Bsource.sampleData.n :=
        Hgap.finalActiveMass_family
  have hselector :
      ∀ p ∈ primeBand J.postHeightBridge.sampleData.n
          J.postHeightBridge.sampleData.W,
        abs (bankPaperCanonicalSelectorValuationDeficit
          R certificate (R.paperFixedExceptionalFactors deltaStar)
            (R.roughCanonicalGuardedCandidateSet certificate
              deltaStar (K0 + 1))
            J.placedPreSelector p) ≤
          Cinitial * J.postHeightBridge.q /
            ((p : Real) * J.postHeightBridge.L) :=
    hselectorN M hdelta Bsource rfl hBW R certificate J S
      hbetaProtSync hbetaActSync hsep hremaining hcanonical hqTilde
      halpha hbetaBox hpool hdFamily hqFamily
  have hroundedFrozenLedger :
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
          (J.betaProt + S.Cmass / S.density) /
            J.postHeightBridge.L :=
    bankPaperCanonicalSectionNinePostHeight_roundedFrozenLedger_of_sourceInputs
      J S
  have hprimeDeviation :
      J.postHeightBridge.primeDeviationL1 ≤
        7 * J.postHeightBridge.w := by
    rcases hmomentN with ⟨hWne, _hnOne, _hscalePoints, hready⟩
    let Pmesh :=
      RegularMeshPrimeCutoffs.Mesh.canonicalPartition
        M hdelta J.postHeightBridge.n_gt_one J.hW J.scaleSeparation
    let Emesh :=
      RegularMeshPrimeCutoffs.Mesh.canonicalCertificate
        M hdelta J.postHeightBridge.n_gt_one J.hW J.scaleSeparation
    have hreadyMesh :
        RegularMeshPrimeCutoffs.Mesh.MomentReady M Pmesh := by
      subst W
      simpa only [Pmesh] using hready J.scaleSeparation
    have hL1 :=
      RegularMeshPrimeCutoffs.Mesh.actual_L1_bound_of_ready
        M Pmesh Emesh (fun _ ↦ rfl) (fun _ ↦ rfl)
          hdelta J.postHeightBridge.n_gt_one hreadyMesh
    calc
      J.postHeightBridge.primeDeviationL1 =
          Pmesh.totalL1 := rfl
      _ ≤ 7 * (delta + M.ratio) := hL1
      _ ≤ 7 * (delta + eta) := by
        nlinarith [M.ratio_le_eta]
      _ = 7 * J.postHeightBridge.w := rfl
  have hlocalP87 :
      BankPaperCanonicalSectionNinePostHeightSourceFirstSpecializedLocalP87At
        M Cinitial radius CP87 J S :=
    hP87N Bsource rfl hBW R certificate J S
      hbetaProtSync hbetaActSync hsep hremaining hcanonical
      Hgap.postHeightTarget_margin hCmassSync hdensitySync hqFamily
  have hTwoWJ : 2 ≤ J.postHeightBridge.sampleData.W := by
    simpa only [
      BankPaperCanonicalSectionNinePostHeightBridgeInputsAt.postHeightBridge_sampleData,
      hBW] using hTwoW
  have hsigmaProtJ : sigma ≤ J.betaProt := by
    simpa only [hbetaProtSync] using hsigmaProt
  have hlargeL :
      (J.betaProt + S.Cmass / S.density) +
          Real.exp (2 *
            ((Erdos390.Full.PaperStatisticNorm.valuationLogCoefficient
                  2 J.postHeightBridge.sampleData.W +
              J.postHeightBridge.nuisanceStatisticCoefficient 2) *
                (3 * (radius : Real)))) *
            (S.Cmass / S.density) + sigma ≤
        J.postHeightBridge.L := by
    have hraw :=
      hlargeLN J.postHeightBridge
        (by rfl)
        (by
          simpa only [
            BankPaperCanonicalSectionNinePostHeightBridgeInputsAt.postHeightBridge_sampleData]
            using hBW)
    rw [hbetaProtSync, hCmassSync, hdensitySync]
    linarith only [hraw]
  have hnonsmooth :
      ∀ label,
        RoughCanonicalActiveNonexceptionalLabel
            J.postHeightBridge.sampleData.n deltaStar label →
          sigma / J.postHeightBridge.L +
              |R.roughCanonicalGuardedPostchargeCorrectionDensity
                certificate deltaStar
                J.postHeightBridge.sampleData.W (K0 + 1) label
                  J.alpha J.beta J.postHeightBridge.L| ≤
            J.beta / J.postHeightBridge.L ∧
          J.beta / J.postHeightBridge.L +
              |R.roughCanonicalGuardedPostchargeCorrectionDensity
                certificate deltaStar
                J.postHeightBridge.sampleData.W (K0 + 1) label
                  J.alpha J.beta J.postHeightBridge.L| ≤
            1 - sigma / J.postHeightBridge.L := by
    have hraw :=
      hnonsmoothN depth R certificate
        hnCutoff hyCutoff
    simpa only [
      RoughCanonicalBalancedNonsmoothBounds,
      BankPaperCanonicalSectionNinePostHeightBridgeInputsAt.alpha,
      bankPaperCanonicalPostHfitBalancedAlpha,
      BankPaperCanonicalSectionNinePostHeightBridgeInputsAt.beta,
      BankPaperCanonicalSectionNinePostHeightBridgeInputsAt.postHeightBridge_sampleData,
      BridgeData.L, hBW, hbetaProtSync, hbetaActSync] using hraw
  have Hlocal :=
    bankPaperCanonicalSectionNinePostHeightLocalInputReduction_of_exportedFields
      deltaStar rho sigma Cinitial hCinitial radius CP87 M
        Bsource R certificate I hdelta J S Hgap
        halpha hselector hroundedFrozenLedger hprimeDeviation
        hlocalP87 hTwoWJ hsigma hsigmaProtJ hlargeL hnonsmooth
  rcases Hlocal with ⟨_halpha, A, hcellIndex⟩
  have Hpublic :=
    bankPaperCanonicalSectionNineTopFrozenSynchronizedPostHfitInputAt_of_postHeightInputs
      M Bsource R certificate I deltaStar rho sigma CP87
        hdelta J S A hcellIndex
  rw [hbridge]
  exact Hpublic

end BankPaperRealization

end

end Erdos390.WholePaper

end

theorem solution : Erdos390.RemainingAnalyticGoal004_012 := by
  exact @Erdos390.WholePaper.BankPaperRealization.bankPaperCanonicalSectionNinePostHeight_sourceFirstPreselectedPostHfitInput
