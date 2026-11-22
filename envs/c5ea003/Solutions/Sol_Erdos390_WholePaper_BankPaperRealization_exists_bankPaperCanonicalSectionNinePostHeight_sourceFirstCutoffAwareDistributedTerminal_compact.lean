-- Prove2me | solution 1 for Erdos390.WholePaper.BankPaperRealization.exists_bankPaperCanonicalSectionNinePostHeight_sourceFirstCutoffAwareDistributedTerminal_compact
-- status  : ACCEPTED   (prove)
-- author  : @doctosil
-- created : 2026-09-17T17:38:06.228438+00:00
-- url     : https://prove2.me/submissions/da1100be-e196-4c92-80de-0ad2b85c1174

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
import Theorems.Thm_Erdos390_WholePaper_BankPaperRealization_bankPaperCanonicalSectionNineFinalPayload_of_roundedSelector_guardedSlack_compact
import Theorems.Thm_Erdos390_WholePaper_BankPaperRealization_exists_bankPaperCanonicalSectionNinePostHeight_sourceFirstCutoffAwareAnalyticCompletion_compact
import Theorems.Thm_Erdos390_WholePaper_eventually_bankPaperCanonicalSectionNineBudgetClosure_compact
import Theorems.Thm_Erdos390_WholePaper_exists_depth_bankPaperCombinedChargeTerminal_uniform_deltaStar_compact





section
theorem Erdos390.WholePaper.exists_depth_bankPaperCombinedChargeTerminal_uniform_deltaStar : Erdos390.RemainingAnalyticGoal008_010 := @Erdos390.WholePaper.exists_depth_bankPaperCombinedChargeTerminal_uniform_deltaStar_compact
end
section
universe u_1
theorem Erdos390.WholePaper.eventually_bankPaperCanonicalSectionNineBudgetClosure : Erdos390.RemainingAnalyticGoal008_005.{u_1} := @Erdos390.WholePaper.eventually_bankPaperCanonicalSectionNineBudgetClosure_compact
end
section
theorem Erdos390.WholePaper.BankPaperRealization.exists_bankPaperCanonicalSectionNinePostHeight_sourceFirstCutoffAwareAnalyticCompletion : Erdos390.RemainingAnalyticGoal004_019 := @Erdos390.WholePaper.BankPaperRealization.exists_bankPaperCanonicalSectionNinePostHeight_sourceFirstCutoffAwareAnalyticCompletion_compact
end
section
theorem Erdos390.WholePaper.BankPaperRealization.bankPaperCanonicalSectionNineFinalPayload_of_roundedSelector_guardedSlack : Erdos390.RemainingAnalyticGoal004_011 := @Erdos390.WholePaper.BankPaperRealization.bankPaperCanonicalSectionNineFinalPayload_of_roundedSelector_guardedSlack_compact
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









end Mesh



end

end Erdos390.Full.RegularRelativeMesh

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

/- Source module: Erdos390.WholePaper.SafePrimeCounting -/
section


/-!
# A prime-counting asymptotic with an audited dependency closure

The pinned auxiliary package contains stronger convenience theorems whose
transitive imports include unfinished declarations.  This file instead
derives `π(x) ~ x / log x` from the already audited `MediumPNT` route used by
`FriableAsymptotic.theta_error_isBigO_log_power` and Mathlib's elementary
comparison between `π` and `θ`.
-/

open Filter Topology Asymptotics

namespace Erdos390.WholePaper.SafePrimeCounting

private theorem div_log_isLittleO_id :
    (fun x : ℝ => x / Real.log x) =o[atTop] (fun x : ℝ => x) := by
  apply (isLittleO_iff_tendsto (fun x hx => by simp [hx])).mpr
  apply Real.tendsto_log_atTop.inv_tendsto_atTop.congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
  have hx0 : x ≠ 0 := ne_of_gt (lt_trans zero_lt_one hx)
  have hlog : Real.log x ≠ 0 := (Real.log_pos hx).ne'
  field_simp
  exact inv_mul_cancel₀ hlog

private theorem div_log_sq_isLittleO_div_log :
    (fun x : ℝ => x / Real.log x ^ 2) =o[atTop]
      (fun x : ℝ => x / Real.log x) := by
  apply (isLittleO_iff_tendsto (fun x hx => by
    apply div_eq_zero_iff.mpr
    rcases (div_eq_zero_iff.mp hx) with hx | hx
    · exact Or.inl hx
    · exact Or.inr (by simp [hx]))).mpr
  apply Real.tendsto_log_atTop.inv_tendsto_atTop.congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
  have hx0 : x ≠ 0 := ne_of_gt (lt_trans zero_lt_one hx)
  have hlog : Real.log x ≠ 0 := (Real.log_pos hx).ne'
  field_simp
  exact inv_mul_cancel₀ hlog

theorem theta_sub_id_isLittleO :
    (Chebyshev.theta - id) =o[atTop] (id : ℝ → ℝ) := by
  have htheta :
      (Chebyshev.theta - id) =O[atTop]
        (fun x : ℝ => x / Real.log x) := by
    simpa using
      Erdos390.Full.FriableAsymptotic.theta_error_isBigO_log_power 1
  exact htheta.trans_isLittleO div_log_isLittleO_id

theorem theta_div_log_sub_main_isLittleO :
    (fun x : ℝ =>
      Chebyshev.theta x / Real.log x - x / Real.log x) =o[atTop]
        (fun x : ℝ => x / Real.log x) := by
  have hmul := theta_sub_id_isLittleO.mul_isBigO
    (isBigO_refl (fun x : ℝ => (Real.log x)⁻¹) atTop)
  apply hmul.congr'
  · exact Eventually.of_forall fun x => by
      simp only [Pi.sub_apply, id_eq]
      rw [div_eq_mul_inv, div_eq_mul_inv]
      ring
  · exact Eventually.of_forall fun x => by
      simp only [id_eq]
      rw [div_eq_mul_inv]

theorem primeCounting_sub_main_isLittleO :
    (fun x : ℝ =>
      (Nat.primeCounting ⌊x⌋₊ : ℝ) - x / Real.log x) =o[atTop]
        (fun x : ℝ => x / Real.log x) := by
  have hpi :
      (fun x : ℝ =>
        (Nat.primeCounting ⌊x⌋₊ : ℝ) -
          Chebyshev.theta x / Real.log x) =o[atTop]
          (fun x : ℝ => x / Real.log x) :=
    Chebyshev.primeCounting_sub_theta_div_log_isBigO.trans_isLittleO
      div_log_sq_isLittleO_div_log
  have hadd := hpi.add theta_div_log_sub_main_isLittleO
  apply hadd.congr' (Eventually.of_forall fun x => by ring) (Eventually.of_forall fun _ => rfl)

/-- Safe real-variable prime number theorem. -/
theorem primeCounting_real_isEquivalent :
    (fun x : ℝ => (Nat.primeCounting ⌊x⌋₊ : ℝ)) ~[atTop]
      (fun x : ℝ => x / Real.log x) :=
  primeCounting_sub_main_isLittleO



end Erdos390.WholePaper.SafePrimeCounting

end

/- Source module: Erdos390.WholePaper.ScaledPrimeCounting -/
section


/-!
# Prime counting at fixed positive dilates

This is the uniformity-free fixed-scale consequence needed for each of the
thirteen lower-bound layers.  Moving endpoints will later be sandwiched
between fixed dilates.
-/

open Filter Topology Asymptotics

namespace Erdos390.WholePaper.SafePrimeCounting

theorem tendsto_log_natCast_atTop :
    Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
  Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop

theorem tendsto_log_natCast_div_log_const_mul (a : ℝ) (ha : 0 < a) :
    Tendsto
      (fun n : ℕ =>
        Real.log (n : ℝ) / Real.log (a * (n : ℝ)))
      atTop (nhds 1) := by
  have hsmall : Tendsto
      (fun n : ℕ => Real.log a / Real.log (n : ℝ))
      atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop tendsto_log_natCast_atTop
  have hden : Tendsto
      (fun n : ℕ => 1 + Real.log a / Real.log (n : ℝ))
      atTop (nhds 1) := by
    simpa using tendsto_const_nhds.add hsmall
  have hinv : Tendsto
      (fun n : ℕ => 1 / (1 + Real.log a / Real.log (n : ℝ)))
      atTop (nhds 1) := by
    have hnum : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 1) :=
      tendsto_const_nhds
    convert hnum.div hden (by norm_num : (1 : ℝ) ≠ 0) using 1
    norm_num
  apply hinv.congr'
  filter_upwards [eventually_gt_atTop 1] with n hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast (Nat.zero_lt_of_lt hn)
  have hlogn : Real.log (n : ℝ) ≠ 0 := (Real.log_pos (by exact_mod_cast hn)).ne'
  rw [Real.log_mul ha.ne' hnR.ne']
  field_simp
  ring

theorem div_log_const_mul_isEquivalent (a : ℝ) (ha : 0 < a) :
    (fun n : ℕ =>
      (a * (n : ℝ)) / Real.log (a * (n : ℝ))) ~[atTop]
      (fun n : ℕ =>
        (a * (n : ℝ)) / Real.log (n : ℝ)) := by
  have hscaleTop :
      Tendsto (fun n : ℕ => a * (n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.const_mul_atTop ha
  have htargetNe :
      ∀ᶠ n : ℕ in atTop,
        (a * (n : ℝ)) / Real.log (n : ℝ) ≠ 0 := by
    filter_upwards [eventually_gt_atTop 1] with n hn
    have hnR : (0 : ℝ) < n := by exact_mod_cast (Nat.zero_lt_of_lt hn)
    exact div_ne_zero (mul_ne_zero ha.ne' hnR.ne')
      (Real.log_pos (by exact_mod_cast hn)).ne'
  apply (isEquivalent_iff_tendsto_one htargetNe).mpr
  apply (tendsto_log_natCast_div_log_const_mul a ha).congr'
  filter_upwards [eventually_gt_atTop 1,
      hscaleTop.eventually (eventually_gt_atTop 1)] with n hn han
  have hnR : (0 : ℝ) < n := by exact_mod_cast (Nat.zero_lt_of_lt hn)
  have hlogn : Real.log (n : ℝ) ≠ 0 := (Real.log_pos (by exact_mod_cast hn)).ne'
  have hlogaN : Real.log (a * (n : ℝ)) ≠ 0 := (Real.log_pos han).ne'
  have han0 : a * (n : ℝ) ≠ 0 := mul_ne_zero ha.ne' hnR.ne'
  change Real.log (n : ℝ) / Real.log (a * (n : ℝ)) =
    ((a * (n : ℝ)) / Real.log (a * (n : ℝ))) /
      ((a * (n : ℝ)) / Real.log (n : ℝ))
  field_simp

/-- For each fixed `a>0`, the count of primes up to `a n` has the expected
`a n / log n` asymptotic. -/
theorem primeCounting_const_mul_nat_isEquivalent (a : ℝ) (ha : 0 < a) :
    (fun n : ℕ =>
      (Nat.primeCounting ⌊a * (n : ℝ)⌋₊ : ℝ)) ~[atTop]
      (fun n : ℕ =>
        (a * (n : ℝ)) / Real.log (n : ℝ)) := by
  have hscaleTop :
      Tendsto (fun n : ℕ => a * (n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.const_mul_atTop ha
  exact (primeCounting_real_isEquivalent.comp_tendsto hscaleTop).trans
    (div_log_const_mul_isEquivalent a ha)

end Erdos390.WholePaper.SafePrimeCounting

end

/- Source module: Erdos390.WholePaper.PrimeLayerCounts -/
section


/-!
# Fixed prime-interval counts

This converts the safe fixed-dilate PNT into the exact difference form used
by each stationary layer of Section 3.
-/

open Filter Topology Asymptotics

namespace Erdos390.WholePaper.SafePrimeCounting

private theorem eventually_secondOrderScale_ne_zero :
    ∀ᶠ n : ℕ in atTop,
      (n : ℝ) / Real.log (n : ℝ) ≠ 0 := by
  filter_upwards [eventually_gt_atTop 1] with n hn
  have hnPos : (0 : ℝ) < n := by exact_mod_cast (Nat.zero_lt_of_lt hn)
  exact div_ne_zero hnPos.ne'
    (Real.log_pos (by exact_mod_cast hn)).ne'

theorem primeCounting_const_mul_normalized_tendsto (a : ℝ) (ha : 0 < a) :
    Tendsto
      (fun n : ℕ =>
        (Nat.primeCounting ⌊a * (n : ℝ)⌋₊ : ℝ) /
          ((n : ℝ) / Real.log (n : ℝ)))
      atTop (nhds a) := by
  have hdenNe :
      ∀ᶠ n : ℕ in atTop,
        (a * (n : ℝ)) / Real.log (n : ℝ) ≠ 0 := by
    filter_upwards [eventually_gt_atTop 1] with n hn
    have hnPos : (0 : ℝ) < n := by exact_mod_cast (Nat.zero_lt_of_lt hn)
    exact div_ne_zero (mul_ne_zero ha.ne' hnPos.ne')
      (Real.log_pos (by exact_mod_cast hn)).ne'
  have hone := (isEquivalent_iff_tendsto_one hdenNe).mp
    (primeCounting_const_mul_nat_isEquivalent a ha)
  have hmul := hone.const_mul a
  have hmul' : Tendsto
      (fun n : ℕ =>
        a * ((Nat.primeCounting ⌊a * (n : ℝ)⌋₊ : ℝ) /
          ((a * (n : ℝ)) / Real.log (n : ℝ))))
      atTop (nhds a) := by
    simpa only [mul_one] using hmul
  apply hmul'.congr'
  filter_upwards [eventually_gt_atTop 1] with n hn
  have hnPos : (0 : ℝ) < n := by exact_mod_cast (Nat.zero_lt_of_lt hn)
  have hlog : Real.log (n : ℝ) ≠ 0 :=
    (Real.log_pos (by exact_mod_cast hn)).ne'
  change
    a * ((Nat.primeCounting ⌊a * (n : ℝ)⌋₊ : ℝ) /
        ((a * (n : ℝ)) / Real.log (n : ℝ))) =
      (Nat.primeCounting ⌊a * (n : ℝ)⌋₊ : ℝ) /
        ((n : ℝ) / Real.log (n : ℝ))
  field_simp

theorem primeCounting_interval_normalized_tendsto
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    Tendsto
      (fun n : ℕ =>
        ((Nat.primeCounting ⌊b * (n : ℝ)⌋₊ : ℝ) -
          (Nat.primeCounting ⌊a * (n : ℝ)⌋₊ : ℝ)) /
            ((n : ℝ) / Real.log (n : ℝ)))
      atTop (nhds (b - a)) := by
  have hsub := (primeCounting_const_mul_normalized_tendsto b hb).sub
    (primeCounting_const_mul_normalized_tendsto a ha)
  apply hsub.congr'
  filter_upwards [eventually_secondOrderScale_ne_zero] with n hn
  field_simp

/-- Natural-cardinality version for the prime interval `(a n, b n]`. -/
theorem primeCounting_interval_natSub_normalized_tendsto
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    Tendsto
      (fun n : ℕ =>
        ((Nat.primeCounting ⌊b * (n : ℝ)⌋₊ -
            Nat.primeCounting ⌊a * (n : ℝ)⌋₊ : ℕ) : ℝ) /
          ((n : ℝ) / Real.log (n : ℝ)))
      atTop (nhds (b - a)) := by
  have hb : 0 < b := ha.trans_le hab
  apply (primeCounting_interval_normalized_tendsto ha hb).congr'
  exact Eventually.of_forall fun n => by
    have harg : a * (n : ℝ) ≤ b * (n : ℝ) :=
      mul_le_mul_of_nonneg_right hab (Nat.cast_nonneg n)
    have hfloor : ⌊a * (n : ℝ)⌋₊ ≤ ⌊b * (n : ℝ)⌋₊ :=
      Nat.floor_mono harg
    have hpi := Nat.monotone_primeCounting hfloor
    change
      ((Nat.primeCounting ⌊b * (n : ℝ)⌋₊ : ℝ) -
          (Nat.primeCounting ⌊a * (n : ℝ)⌋₊ : ℝ)) /
          ((n : ℝ) / Real.log (n : ℝ)) =
        ((Nat.primeCounting ⌊b * (n : ℝ)⌋₊ -
          Nat.primeCounting ⌊a * (n : ℝ)⌋₊ : ℕ) : ℝ) /
          ((n : ℝ) / Real.log (n : ℝ))
    rw [Nat.cast_sub hpi]

end Erdos390.WholePaper.SafePrimeCounting

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





/-- The elementary logarithmic comparison `log n / n → 0`, made public
for later upper-bound estimates. -/
theorem log_natCast_div_natCast_tendsto_zero :
    Tendsto
      (fun n : ℕ ↦ Real.log (n : ℝ) / (n : ℝ))
      atTop (nhds 0) := by
  simpa only [Function.comp_apply, id_eq] using
    (Real.isLittleO_log_id_atTop.comp_tendsto
      (tendsto_natCast_atTop_atTop (R := ℝ))).tendsto_div_nhds_zero

/-- The second-order scale `n / log n` diverges to infinity. -/
theorem secondOrderScale_tendsto_atTop :
    Tendsto secondOrderScale atTop atTop := by
  have hpos :
      ∀ᶠ n : ℕ in atTop,
        0 < Real.log (n : ℝ) / (n : ℝ) := by
    filter_upwards [eventually_gt_atTop 1] with n hn
    exact div_pos (Real.log_pos (by exact_mod_cast hn)) (by positivity)
  have hright :
      Tendsto
        (fun n : ℕ ↦ Real.log (n : ℝ) / (n : ℝ))
        atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.mpr
      ⟨log_natCast_div_natCast_tendsto_zero, hpos⟩
  apply hright.inv_tendsto_nhdsGT_zero.congr'
  exact Eventually.of_forall fun n ↦ by
    change (Real.log (n : ℝ) / (n : ℝ))⁻¹ =
      secondOrderScale n
    rw [secondOrderScale, inv_div]

/-- A pointwise positivity criterion for the second-order scale. -/
theorem secondOrderScale_pos {n : ℕ} (hn : 2 ≤ n) :
    0 < secondOrderScale n := by
  rw [secondOrderScale]
  exact div_pos (by positivity)
    (Real.log_pos (by exact_mod_cast hn))

/-- Eventually the second-order scale is strictly positive. -/
theorem eventually_secondOrderScale_pos :
    ∀ᶠ n : ℕ in atTop, 0 < secondOrderScale n := by
  filter_upwards [eventually_ge_atTop 2] with n hn
  exact secondOrderScale_pos hn

/-- The second-order scale is sublinear. -/
theorem secondOrderScale_ratio_tendsto_zero :
    Tendsto
      (fun n : ℕ ↦ secondOrderScale n / (n : ℝ))
      atTop (nhds 0) := by
  have hinvLog :
      Tendsto (fun n : ℕ ↦ 1 / Real.log (n : ℝ))
        atTop (nhds 0) := by
    simpa only [one_div] using
      (Real.tendsto_log_atTop.comp
        (tendsto_natCast_atTop_atTop (R := ℝ))).inv_tendsto_atTop
  apply hinvLog.congr'
  filter_upwards [eventually_gt_atTop 1] with n hn
  rw [secondOrderScale]
  have hnNe : (n : ℝ) ≠ 0 := by positivity
  have hlogNe : Real.log (n : ℝ) ≠ 0 :=
    (Real.log_pos (by exact_mod_cast hn)).ne'
  field_simp





/-- Ceiling changes `c n/log n` only by a negligible relative error. -/
theorem upperTailLength_normalized_tendsto {c : ℝ} (hc : 0 < c) :
    Tendsto
      (fun n : ℕ ↦
        (upperTailLength c n : ℝ) / secondOrderScale n)
      atTop (nhds c) := by
  simpa only [upperTailLength] using
    (tendsto_nat_ceil_mul_div_atTop (R := ℝ) hc.le).comp
      secondOrderScale_tendsto_atTop

/-- The chosen upper tail is `o(n)`. -/
theorem upperTailLength_ratio_tendsto_zero {c : ℝ} (hc : 0 < c) :
    Tendsto
      (fun n : ℕ ↦ (upperTailLength c n : ℝ) / (n : ℝ))
      atTop (nhds 0) := by
  have hmul :=
    (upperTailLength_normalized_tendsto hc).mul
      secondOrderScale_ratio_tendsto_zero
  rw [mul_zero] at hmul
  apply hmul.congr'
  filter_upwards [eventually_secondOrderScale_pos,
      eventually_gt_atTop 1] with n hscale hn
  have hscaleNe : secondOrderScale n ≠ 0 := hscale.ne'
  have hnNe : (n : ℝ) ≠ 0 := by positivity
  field_simp





















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

/- Source module: Erdos390.WholePaper.BankBottomMarkerPoolScale -/
section


/-!
# Prime-counting scales for bottom marker pools

The bottom intervals have length of order `n / log n`, while their prime
cardinality has order `n / log n ^ 2`.  Consequently their cardinality
divided by `secondOrderScale n = n / log n` tends to zero, not to a positive
constant.  This file records that coarse-scale fact and then applies the
audited `theta`-difference squeeze to obtain the positive constants on the
finer scale `secondOrderScale n / log n`.
-/

open Filter Topology

namespace Erdos390.WholePaper

noncomputable section





























































/-- The scaled endpoint is eventually narrow enough for all four rows, and
hence all eight oriented pools, to be disjoint. -/
theorem eventually_bankBottom_scaledEndpoint_narrow
    {c : ℝ} (hc : 0 < c) :
    ∀ᶠ n : ℕ in atTop,
      5 * upperEndpoint n (upperTailLength c n) ≤ 12 * n := by
  have hsmall := (upperTailLength_ratio_tendsto_zero hc).eventually
    (eventually_lt_nhds (by norm_num : (0 : ℝ) < 2 / 5))
  filter_upwards [hsmall, eventually_gt_atTop 0] with n hratio hn
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have htailR :
      5 * (upperTailLength c n : ℝ) < 2 * (n : ℝ) := by
    have := (div_lt_iff₀ hnR).mp hratio
    linarith
  have htail : 5 * upperTailLength c n ≤ 2 * n := by
    exact_mod_cast htailR.le
  unfold upperEndpoint
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





























/-! The four paper rows, with the marker made explicit. -/









/-- In both terminal rows the donor value is the upper state value. -/
theorem donorFactor_eq_upperStateFactor_of_terminalMove
    (request : ↑(bankBottomPaperRequests n))
    (hmove : realization.move request = .threeToTwo ∨
      realization.move request = .twoToOne) :
    realization.donorFactor request =
      realization.upperStateFactor request := by
  rcases hmove with hmove | hmove
  · simpa only [donorFactor, upperStateFactor, hmove] using
      bankBottomDonor_threeToTwo_eq_upperState
        (realization.marker request)
  · simpa only [donorFactor, upperStateFactor, hmove] using
      bankBottomDonor_twoToOne_eq_upperState
        (realization.marker request)



/-! ## Orientation-aware realized row and slot changes -/























end BankBottomPaperRealization

/-! ## Complete occurrence sets and rough signatures -/









namespace BankBottomPaperRealization

variable {n M : ℕ} (realization : BankBottomPaperRealization n M)























































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











































































/-! ## The three actual occurrences and global collision-freedom -/

theorem targetStateValue_lt_sourceStateValue
    {n M : ℕ} (R : BankOrdinaryPaperRealization n M)
    (request : ↑(bankOrdinaryPaperRequests n)) :
    R.targetStateValue request < R.sourceStateValue request := by
  have htarget :=
    (bankOrdinaryPaperRequest_component_spec request.1).2.2.2.2.1
  exact Nat.mul_lt_mul_of_pos_left htarget (R.marker_prime request).pos

theorem sourceStateValue_le_two_mul_n
    {n M : ℕ} (R : BankOrdinaryPaperRealization n M)
    (request : ↑(bankOrdinaryPaperRequests n)) :
    R.sourceStateValue request ≤ 2 * n := by
  have heligible := mem_bankOrdinaryEligibleRelation.mp
    (R.markerDonorPair_mem request)
  have hspec := bankOrdinaryPaperRequest_component_spec request.1
  let P := R.marker request
  let q := bankOrdinaryPaperRequestSource request.1
  let Q := bankOrdinaryScale
    (bankOrdinaryPaperRequestPool n request.1).1
  have hPnonneg : (0 : ℚ) ≤ P := by positivity
  have hqUpper := mul_le_mul_of_nonneg_left
    hspec.2.2.2.2.2.2.1.2 hPnonneg
  have hmarkerUpper := heligible.2.2.2.1.2
  change (P : ℚ) * q ≤ (P : ℚ) * (4 * Q / 3) at hqUpper
  change 2 * Q * (P : ℚ) ≤ 3 * (n : ℚ) at hmarkerUpper
  have hcellSourceUpper : (P : ℚ) * (4 * Q / 3) ≤
      2 * (n : ℚ) := by
    have hscaled := mul_le_mul_of_nonneg_left hmarkerUpper
      (by norm_num : (0 : ℚ) ≤ 2 / 3)
    convert hscaled using 1 <;> ring
  have hsourceUpperQ : (P : ℚ) * q ≤ 2 * n := by
    exact hqUpper.trans hcellSourceUpper
  exact_mod_cast hsourceUpperQ



































/-! ## Realized component and signed-slot changes -/























end BankOrdinaryPaperRealization

/-! ## Eventual realized allocation -/



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

/-- The set difference in the definition makes the fixed factors and all
designated donors literally disjoint. -/
theorem paperFixedExceptionalFactors_disjoint_prechargeDonorSet
    {n h : ℕ}
    (R : BankPaperRealization n (upperEndpoint n h))
    (deltaStar : ℝ) :
    Disjoint (R.paperFixedExceptionalFactors deltaStar)
      R.prechargeDonorSet := by
  rw [Finset.disjoint_left]
  intro a haFixed haDonor
  rw [paperFixedExceptionalFactors, Finset.mem_sdiff] at haFixed
  exact haFixed.2 haDonor

















end BankPaperRealization

end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.TangentExceptionalCanonicalBounds -/
section


/-!
# Analytic bounds for the canonical exceptional-row Lambda-squared sieve

This file closes the two analytic inputs left open by
`TangentExceptionalLambdaSquareSieve`.  The constants are deliberately
coarse and fixed.  The PNT error constant and cutoff inherited from
`PrimeBandQuadrature` are named noncomputable choices, rather than numerical
values.  The proof has three ingredients.

* The verified interval Mertens theorem in `Full.PrimeBandQuadrature`
  gives a lower bound for the Euler product
  `prod_{p <= y} (1 + 1/(p-1))`.
* A logarithmic first-moment argument shows that truncating the squarefree
  divisor sum at `y^2` retains at least one tenth of that Euler product.
* A nonnegative Dirichlet-convolution majorant bounds the canonical
  Lambda `l1` norm by `exp 4 * y^2 / G`.

Thus the only constants in the final result are a named finite Mertens
loss, `10 * exp(loss)` for the main term, and an additional factor `exp 4`
for the Lambda norm.  No prime-product or coefficient estimate is assumed.
-/

open scoped BigOperators ArithmeticFunction ArithmeticFunction.Moebius
  ArithmeticFunction.sigma ArithmeticFunction.zeta
open Filter Set Topology

namespace Erdos390.WholePaper

noncomputable section

open Erdos390.Full.PrimeSums
open Erdos390.Full.PrimeBandQuadrature

/-! ## Multiplicative functions used in the Euler-product ledgers -/

































/-! ## Full density and logarithmic first moment -/









/-! A powerset moment inequality.  It is the finite probabilistic estimate
behind the truncation: the first moment of independent nonnegative local
weights is at most their partition function times `sum b_p a_p`. -/





/-! ## Prime sums at the rough-head modulus -/











/-! ## Mertens lower bound for the full Euler product -/



theorem tangentSelbergMertensBase_ge_cutoff :
    fullReciprocalSumUniformCutoff ≤ tangentSelbergMertensBase :=
  le_max_left _ _

theorem tangentSelbergMertensBase_ge_two :
    2 ≤ tangentSelbergMertensBase :=
  le_max_right _ _













/-! ## Retaining a fixed fraction below level `y^2` -/





/-! ## A universal `exp 4` coefficient-mean bound -/















/-! ## The canonical Lambda norm -/







/-! ## Fixed eventual constants and the closed interval theorem -/





theorem tangentSelbergCanonicalMainConstant_pos :
    0 < tangentSelbergCanonicalMainConstant := by
  unfold tangentSelbergCanonicalMainConstant
  positivity













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







/-- The fixed-head gap is positive whenever the endpoint-ratio cap is below
two. -/
theorem tangentPaperHeadGap_pos
    (W : ℕ) {r0 : ℝ} (hr0 : r0 < 2) :
    0 < tangentPaperHeadGap W r0 := by
  unfold tangentPaperHeadGap
  exact mul_pos (roughHeadDensity_pos W) (sub_pos.mpr hr0)

/-- The retained one-sixteenth clean-list density is positive under the same
ratio cap. -/
theorem tangentPaperCleanListDensity_pos
    (W : ℕ) {r0 : ℝ} (hr0 : r0 < 2) :
    0 < tangentPaperCleanListDensity W r0 := by
  unfold tangentPaperCleanListDensity
  exact div_pos (tangentPaperHeadGap_pos W hr0) (by norm_num)











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

/- Source module: Erdos390.WholePaper.BankPaperFixedExceptionalChargeAsymptotic -/
section


/-!
# Asymptotic package for the fixed exceptional low-prime charge

This file records the constants and scale arithmetic used after the finite
weighted Selberg decomposition of `G_fix` has been proved.  In the notation
of the paper,

* `paperExceptionalSelbergMainConstant` is `C_S`;
* `paperExceptionalSelbergRemainderConstant` is `C_R`;
* `paperExceptionalChargeConstant c` is `A_exc(c)`;
* `paperExceptionalChargeEpsilon deltaStar n` is the normalized
  endpoint/remainder coefficient.

The finite majorant below is obtained by composing the separate finite
rough/smooth-fibre argument with the elementary valuation-prefix estimates.
Nothing in this file assumes that the actual exceptional charge satisfies
that majorant.  We prove the finite charge bound and its analytic packaging,
together with the independent arithmetic support fact that, under the
displayed paper-range hypotheses, the actual low-prime charge is exactly
zero above twice the paper's literal real exceptional cutoff.  The
corresponding safe integral-cutoff statement is retained as a corollary.
-/

open Filter Topology
open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel
open Erdos390.Full.Scale

noncomputable section

/-! ## Auditable paper constants -/









theorem paperExceptionalTheta_pos :
    0 < paperExceptionalTheta := by
  norm_num [paperExceptionalTheta]

theorem paperExceptionalSelbergMainConstant_pos :
    0 < paperExceptionalSelbergMainConstant := by
  exact tangentSelbergCanonicalMainConstant_pos



theorem paperExceptionalChargeConstant_pos
    {c : ℝ} (hc : 0 < c) :
    0 < paperExceptionalChargeConstant c := by
  unfold paperExceptionalChargeConstant
  exact mul_pos (mul_pos (by norm_num) hc)
    paperExceptionalSelbergMainConstant_pos

/-! ## The finite Selberg output and its normalized remainder -/











/-! ## The endpoint remainder tends to zero -/





/-! ## Uniform packaging of the finite majorant -/









/-! ## Exact support cutoff for the actual fixed charge -/







/-! ## Closing the finite weighted Selberg estimate -/













end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankPaperCombinedChargeTerminal -/
section


/-!
# The honest combined fixed-factor and precharge terminal

The precharge terminal leaves one twelfth of the `c-C0` valuation reserve
after the base bank has been charged on the fixed anchor support.  The
literal fixed exceptional factors use at most one twenty-fourth of that
reserve for a sufficiently small positive `deltaStar`; hence another
twenty-fourth remains after the complete selector charge.

Away from the fixed anchor support there is no anchor valuation.  For primes
up to `yNat`, the fixed exceptional estimate is combined with the already
proved moving-prime `o(secondOrderScale)` bank/Legendre cost.  Above `yNat`,
the exact donor-backing identity pays the complete selector charge directly
from the literal upper tail.  Thus the conclusion below is actual natural
divisibility, with no divisibility or charge-bound premise.
-/

open Filter Topology

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel
open Erdos390.Full.Scale

noncomputable section

/-! ## An explicit admissible exceptional exponent -/





theorem paperCombinedChargeDeltaStar_spec
    {c : ℝ} (hc : C0 < c) :
    IsPaperCombinedChargeDeltaStar c
      (paperCombinedChargeDeltaStar c) := by
  have hC0Pos : (0 : ℝ) < C0 := by norm_num [C0]
  have hcPos : 0 < c := hC0Pos.trans hc
  have hgap : 0 < c - C0 := sub_pos.mpr hc
  have htheta : 0 < paperExceptionalTheta :=
    paperExceptionalTheta_pos
  have hcharge : 0 < paperExceptionalChargeConstant c :=
    paperExceptionalChargeConstant_pos hcPos
  have hden : 0 < 48 * paperExceptionalChargeConstant c := by
    positivity
  have hchoicePos : 0 < paperCombinedChargeDeltaStar c := by
    rw [paperCombinedChargeDeltaStar]
    exact lt_min (by norm_num)
      (div_pos (mul_pos hgap htheta) hden)
  have hchoiceLe :
      paperCombinedChargeDeltaStar c ≤
        (c - C0) * paperExceptionalTheta /
          (48 * paperExceptionalChargeConstant c) := by
    exact min_le_right _ _
  have hchoiceUpper : paperCombinedChargeDeltaStar c < 1 / 18 := by
    have hsmall : paperCombinedChargeDeltaStar c ≤ 1 / 36 := by
      exact min_le_left _ _
    nlinarith
  have hscaled :
      paperCombinedChargeDeltaStar c *
          (48 * paperExceptionalChargeConstant c) ≤
        (c - C0) * paperExceptionalTheta :=
    (le_div_iff₀ hden).mp hchoiceLe
  have hscaledFortyEight :
      paperCombinedChargeDeltaStar c *
          paperExceptionalChargeConstant c ≤
        (c - C0) * paperExceptionalTheta / 48 := by
    nlinarith
  have hbudget :
      paperExceptionalChargeConstant c *
          (paperCombinedChargeDeltaStar c / paperExceptionalTheta) ≤
        (c - C0) / 48 := by
    calc
      paperExceptionalChargeConstant c *
          (paperCombinedChargeDeltaStar c / paperExceptionalTheta) =
          (paperCombinedChargeDeltaStar c *
            paperExceptionalChargeConstant c) /
              paperExceptionalTheta := by ring
      _ ≤ ((c - C0) * paperExceptionalTheta / 48) /
            paperExceptionalTheta :=
        div_le_div_of_nonneg_right hscaledFortyEight htheta.le
      _ = (c - C0) / 48 := by
        field_simp [htheta.ne']
  exact ⟨hchoicePos, hchoiceUpper, hbudget⟩

theorem paperCombinedChargeDeltaStar_pos
    {c : ℝ} (hc : C0 < c) :
    0 < paperCombinedChargeDeltaStar c :=
  (paperCombinedChargeDeltaStar_spec hc).1



/-! ## Uniform low-prime fixed charge -/



/-! ## Combined terminal -/





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





/-- The canonical combined exponent satisfies every charge constraint and
the strict tangent head-gap constraint. -/
theorem paperCombinedTangentDeltaStar_spec
    {c r0 : Real} (W : Nat) (hc : C0 < c) (hr0 : r0 < 2) :
    IsPaperCombinedTangentDeltaStar c W r0
      (paperCombinedTangentDeltaStar c W r0) := by
  have hchargeSpec := paperCombinedChargeDeltaStar_spec hc
  have hmainPos : 0 < tangentSelbergCanonicalMainConstant :=
    tangentSelbergCanonicalMainConstant_pos
  have hgapPos : 0 < tangentPaperHeadGap W r0 :=
    tangentPaperHeadGap_pos W hr0
  have hdenPos :
      0 < 160 * tangentSelbergCanonicalMainConstant := by
    positivity
  have hdeltaPos :
      0 < paperCombinedTangentDeltaStar c W r0 := by
    rw [paperCombinedTangentDeltaStar]
    exact lt_min (paperCombinedChargeDeltaStar_pos hc)
      (div_pos hgapPos hdenPos)
  have hdeltaCharge :
      paperCombinedTangentDeltaStar c W r0 ≤
        paperCombinedChargeDeltaStar c := by
    exact min_le_left _ _
  have hdeltaGap :
      paperCombinedTangentDeltaStar c W r0 ≤
        tangentPaperHeadGap W r0 /
          (160 * tangentSelbergCanonicalMainConstant) := by
    exact min_le_right _ _
  have hdeltaUpper :
      paperCombinedTangentDeltaStar c W r0 < 1 / 18 :=
    hdeltaCharge.trans_lt hchargeSpec.2.1
  have hC0Pos : (0 : Real) < C0 := by norm_num [C0]
  have hcPos : 0 < c := hC0Pos.trans hc
  have hthetaPos : 0 < paperExceptionalTheta :=
    paperExceptionalTheta_pos
  have hchargePos : 0 < paperExceptionalChargeConstant c :=
    paperExceptionalChargeConstant_pos hcPos
  have hdiv :
      paperCombinedTangentDeltaStar c W r0 / paperExceptionalTheta ≤
        paperCombinedChargeDeltaStar c / paperExceptionalTheta :=
    div_le_div_of_nonneg_right hdeltaCharge hthetaPos.le
  have hchargeBudget :
      paperExceptionalChargeConstant c *
          (paperCombinedTangentDeltaStar c W r0 /
            paperExceptionalTheta) ≤
        (c - C0) / 48 := by
    exact (mul_le_mul_of_nonneg_left hdiv hchargePos.le).trans
      hchargeSpec.2.2
  have hscaled :
      paperCombinedTangentDeltaStar c W r0 *
          (160 * tangentSelbergCanonicalMainConstant) ≤
        tangentPaperHeadGap W r0 :=
    (le_div_iff₀ hdenPos).mp hdeltaGap
  have hmainSmall :
      80 * tangentSelbergCanonicalMainConstant *
          paperCombinedTangentDeltaStar c W r0 <
        tangentPaperHeadGap W r0 := by
    nlinarith
  exact ⟨⟨hdeltaPos, hdeltaUpper, hchargeBudget⟩, hmainSmall⟩







namespace BankPaperRealization

/-! ## The explicit guarded nonsmooth correction -/









/-! ## Clean endpoints lie in the appropriate guarded broad pool -/



/-! ## The isolated protected/corrected-selector construction output -/





/-! ## Adapter to the candidate-parametric distributed tangent -/





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

/-- A fixed multiple of the upper-tail length is eventually at most the
ambient sample size. -/
theorem eventually_mul_upperTailLength_le_self
    (K : Nat) {c : Real} (hc : 0 < c) :
    ∀ᶠ n : Nat in atTop,
      K * upperTailLength c n <= n := by
  have hT : Tendsto
      (fun n : Nat => (K : Real) *
        ((upperTailLength c n : Real) / (n : Real)))
      atTop (nhds 0) := by
    simpa only [mul_zero] using
      (upperTailLength_ratio_tendsto_zero hc).const_mul (K : Real)
  have hsmall := hT.eventually
    (eventually_lt_nhds (by norm_num : (0 : Real) < 1))
  filter_upwards [hsmall, eventually_gt_atTop 0] with n hn hnPos
  have hn' :
      (K : Real) *
          ((upperTailLength c n : Real) / (n : Real)) < 1 := hn
  have hnReal : 0 < (n : Real) := by exact_mod_cast hnPos
  have hnDiv :
      ((K : Real) * (upperTailLength c n : Real)) / (n : Real) < 1 := by
    calc
      ((K : Real) * (upperTailLength c n : Real)) / (n : Real) =
          (K : Real) *
            ((upperTailLength c n : Real) / (n : Real)) := by ring
      _ < 1 := hn'
  have hcross :
      (K : Real) * (upperTailLength c n : Real) < (n : Real) := by
    simpa only [one_mul] using (div_lt_iff₀ hnReal).mp hnDiv
  have hcast :
      ((K * upperTailLength c n : Nat) : Real) < (n : Real) := by
    push_cast
    exact hcross
  exact_mod_cast hcast.le







end BankPaperRealization

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

/- Source module: Erdos390.WholePaper.BankPaperCanonicalRatioCellOccupancy -/
section


/-!
# PNT occupancy for canonical multiplicative ratio cells

The geometry file reduces cell occupancy to one uniform fixed-ratio prime
interval statement.  Here that statement is proved from the already audited
safe prime number theorem.  For every fixed `rho > 1`, there is one natural
cutoff `W` such that every interval

`(A, floor (rho * A)]`, `A >= W`,

contains a prime.  Consequently all full raw `rho`-cells of every later
canonical exponent mesh are occupied; the possibly short terminal fragment
is handled by the deterministic merge.
-/

open Filter Topology

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.RegularRelativeMesh
open Erdos390.Full.RegularMeshPrimeCutoffs

noncomputable section

/-- The safe PNT makes the prime-count difference in every fixed-ratio
interval eventually positive. -/
theorem eventually_primeCounting_fixedRatio_difference_pos
    {rho : Real} (hrho : 1 < rho) :
    ∀ᶠ A : Nat in atTop,
      0 < Nat.primeCounting ⌊rho * (A : Real)⌋₊ -
        Nat.primeCounting A := by
  have hLimit :=
    SafePrimeCounting.primeCounting_interval_natSub_normalized_tendsto
      (a := (1 : Real)) (b := rho) zero_lt_one hrho.le
  have hRatioPos : ∀ᶠ A : Nat in atTop,
      0 <
        ((Nat.primeCounting ⌊rho * (A : Real)⌋₊ -
            Nat.primeCounting A : Nat) : Real) /
          ((A : Real) / Real.log (A : Real)) := by
    have hEventually := hLimit.eventually
      (eventually_gt_nhds (sub_pos.mpr hrho))
    simpa using hEventually
  filter_upwards [hRatioPos, eventually_gt_atTop 1] with A hRatio hA
  have hAPos : (0 : Real) < A := by
    exact_mod_cast (Nat.zero_lt_of_lt hA)
  have hLogPos : 0 < Real.log (A : Real) :=
    Real.log_pos (by exact_mod_cast hA)
  have hScalePos : 0 < (A : Real) / Real.log (A : Real) :=
    div_pos hAPos hLogPos
  have hCountReal :
      0 <
        ((Nat.primeCounting ⌊rho * (A : Real)⌋₊ -
          Nat.primeCounting A : Nat) : Real) :=
    (div_pos_iff_of_pos_right hScalePos).mp hRatio
  exact_mod_cast hCountReal

/-- Quantitative form retained for the later port-load estimate: a fixed
positive fraction of the PNT main term lies in every sufficiently large
fixed-ratio interval. -/
theorem eventually_fixedRatio_primeCounting_lower
    {rho : Real} (hrho : 1 < rho) :
    ∀ᶠ A : Nat in atTop,
      ((rho - 1) / 2) *
          ((A : Real) / Real.log (A : Real)) <=
        (Nat.primeCounting ⌊rho * (A : Real)⌋₊ -
          Nat.primeCounting A : Nat) := by
  have hLimit :=
    SafePrimeCounting.primeCounting_interval_natSub_normalized_tendsto
      (a := (1 : Real)) (b := rho) zero_lt_one hrho.le
  have hhalf : (rho - 1) / 2 < rho - 1 := by
    have : 0 < rho - 1 := sub_pos.mpr hrho
    linarith
  have hRatio : ∀ᶠ A : Nat in atTop,
      (rho - 1) / 2 <
        ((Nat.primeCounting ⌊rho * (A : Real)⌋₊ -
            Nat.primeCounting A : Nat) : Real) /
          ((A : Real) / Real.log (A : Real)) := by
    have hEventually := hLimit.eventually (eventually_gt_nhds hhalf)
    simpa using hEventually
  filter_upwards [hRatio, eventually_gt_atTop 1] with A hRatioA hA
  have hAPos : (0 : Real) < A := by
    exact_mod_cast (Nat.zero_lt_of_lt hA)
  have hLogPos : 0 < Real.log (A : Real) :=
    Real.log_pos (by exact_mod_cast hA)
  have hScalePos : 0 < (A : Real) / Real.log (A : Real) :=
    div_pos hAPos hLogPos
  exact (le_div_iff₀ hScalePos).mp hRatioA.le

/-- Every sufficiently large natural lower endpoint has a prime in its
fixed-ratio interval. -/
theorem eventually_exists_prime_in_fixedRatio_interval
    {rho : Real} (hrho : 1 < rho) :
    ∀ᶠ A : Nat in atTop,
      ∃ p : Nat, p.Prime ∧ A < p ∧ p <= ⌊rho * (A : Real)⌋₊ := by
  filter_upwards [eventually_primeCounting_fixedRatio_difference_pos hrho]
    with A hCount
  let upper : Nat := ⌊rho * (A : Real)⌋₊
  have hPrimeCounting :
      Nat.primeCounting A < Nat.primeCounting upper := by
    exact Nat.sub_pos_iff_lt.mp hCount
  have hCounting :
      Nat.count Nat.Prime (A + 1) < Nat.count Nat.Prime (upper + 1) := by
    simpa [Nat.primeCounting, Nat.primeCounting'] using hPrimeCounting
  obtain ⟨p, hpInterval, hpPrime⟩ :=
    Nat.exists_of_count_lt_count (p := Nat.Prime) hCounting
  rcases hpInterval with ⟨hpLower, hpUpper⟩
  exact ⟨p, hpPrime, by omega, by simpa only [upper] using (show p <= upper by omega)⟩

/-- Existential paper-order form: choose one fixed head cutoff after `rho`,
and every later fixed-ratio interval is occupied. -/
theorem exists_fixedRatioPrimeIntervalOccupancy_cutoff
    {rho : Real} (hrho : 1 < rho) :
    ∃ W : Nat, 2 <= W ∧ TangentFixedRatioPrimeIntervalOccupied W rho := by
  obtain ⟨W₀, hW₀⟩ :=
    eventually_atTop.1 (eventually_exists_prime_in_fixedRatio_interval hrho)
  let W := max 2 W₀
  exact ⟨W, le_max_left _ _, by
    intro A hWA
    exact hW₀ A ((le_max_right 2 W₀).trans hWA)⟩





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













/-! ## Uniform Mertens envelope on the concrete tails -/







/-! ## Quantitative PNT denominator inside an actual cell -/



/-- The safe PNT supplies a single cutoff for the quantitative fixed-ratio
lower bound. -/
theorem exists_fixedRatioPrimeCountLower_cutoff
    {rho : Real} (hrho : 1 < rho) :
    exists W : Nat, 2 <= W ∧ TangentFixedRatioPrimeCountLower W rho := by
  obtain ⟨W0, hW0⟩ :=
    eventually_atTop.1 (eventually_fixedRatio_primeCounting_lower hrho)
  let W := max 2 W0
  exact ⟨W, le_max_left _ _, by
    intro A hWA
    exact hW0 A ((le_max_right 2 W0).trans hWA)⟩

/-- One fixed cutoff simultaneously supports the quantitative PNT cell
lower bound and the uniform Mertens tail estimate. -/
theorem exists_fixedRatioPrimeCountLower_and_Mertens_cutoff
    {rho : Real} (hrho : 1 < rho) :
    exists W : Nat,
      2 <= W ∧ fullReciprocalSumUniformCutoff <= W ∧
        TangentFixedRatioPrimeCountLower W rho := by
  obtain ⟨W0, hW0two, hW0PNT⟩ :=
    exists_fixedRatioPrimeCountLower_cutoff hrho
  let W := max W0 fullReciprocalSumUniformCutoff
  exact ⟨W, hW0two.trans (le_max_left _ _), le_max_right _ _, by
    intro A hWA
    exact hW0PNT A ((le_max_left W0 fullReciprocalSumUniformCutoff).trans hWA)⟩







/-! ## Finite traffic envelopes before the final mesh sum -/





































end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankPaperCanonicalSectionNineTopFrozenFinalGeometryConnector -/
section


/-!
# Section 9 final geometry from the frozen-top source

This connector extracts the only two Post-Hfit fields consumed by the
Section 9 distributed construction--the rounded tangent input and guarded
endpoint slack--from the verified nearest-integer frozen-top package.
No identification with the older no-top global source is used.
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

/-- Feed a frozen-top rounded Post-Hfit package directly into the literal
Section 9 final geometry theorem. -/
theorem
    bankPaperCanonicalSectionNineFinalPayload_of_topFrozenRoundedPostHfit
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
    (Tsource : BarycentricTarget B.sampleData)
    (deltaStar betaProt alpha beta qTilde sigma : Real)
    (placementSeed activeSeed : B.sampleData.Sample → Real)
    (radius : NNReal) (Cpost : Real)
    (quota : Int) (path : Real → B.ParamSpace)
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
    (Hpost :
      BankPaperCanonicalTopFrozenRoundedPostHfitGuardedSlackPackage
        (K := K0 + 1) B R certificate
        (R.paperFixedExceptionalFactors deltaStar) Tsource
        deltaStar betaProt alpha beta qTilde sigma
        placementSeed activeSeed radius Cpost
        (bankPaperCanonicalRatioCellIndex
          M hdelta B.n_gt_one (by omega) S rho)
        quota path endpoint)
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
      certificate deltaStar endpoint
      (R.bankPaperCanonicalSectionNineRatioCellFlow
        M certificate deltaStar (K0 + 1) hdelta B.n_gt_one
          (by omega) S rho endpoint)
      B.L sigma ∧
    TangentRatioCellGeometry bankPaperCanonicalTangentPrimeLabel
      (bankPaperCanonicalExponentBandOf
        M hdelta B.n_gt_one (by omega) S)
      (bankPaperCanonicalRatioCellIndex
        M hdelta B.n_gt_one (by omega) S rho) r0 := by
  have Hpost' := Hpost
  unfold BankPaperCanonicalTopFrozenRoundedPostHfitGuardedSlackPackage at Hpost'
  unfold BankPaperCanonicalPostHfitGuardedSlackPackageOfSource at Hpost'
  have HselectorPartition :
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
        endpoint := by
    exact Hpost'.2.2.2.2.1
  have Hslack :
      R.BankPaperCanonicalGuardedEndpointSlackConstruction certificate
        deltaStar B.sampleData.W (K0 + 1)
        alpha beta B.L sigma endpoint := by
    exact Hpost'.2.2.2.2.2
  exact
    bankPaperCanonicalSectionNineFinalPayload_of_roundedSelector_guardedSlack
      (M := M) (B := B) (c := c) (depth := depth) (K0 := K0)
      (R := R) (certificate := certificate)
      (deltaStar := deltaStar) (alpha := alpha) (beta := beta)
      (sigma := sigma) (_radius := radius) (Cpost := Cpost)
      (endpoint := endpoint) (hdelta := hdelta) (hWtwo := hWtwo)
      (S := S) (hpartition := hpartition) (r0 := r0) (rho := rho)
      (tangentConstant := tangentConstant) (N := N) (density := density)
      (hrho := hrho) (hratio := hratio) (htangent := htangent)
      (hN := hN) (hscaleDom := hscaleDom) (hMertens := hMertens)
      (hPNT := hPNT) (hprime := hprime) (hTwo := hTwo)
      (Hmoment := Hmoment) (HselectorPartition := HselectorPartition)
      (Hslack := Hslack) (hKh := hKh) (hdensity := hdensity)
      (hsigma := hsigma) (hscale := hscale) (hchargeDvd := hchargeDvd)
      (hfixedComponents := hfixedComponents) (hmain := hmain)
      (herror := herror) (hceiling := hceiling)
      (hlowerPos := hlowerPos) (hlower := hlower)
      (hlowerScale := hlowerScale)

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



/-! ## Uniform admissible exponent after capacity -/



/-! ## Tangent-compatible exponent after capacity -/

/-- After the capacity depth has been selected, every later choice of
`W` and every `r0 < 2` has a simultaneous charge/clean-list exponent and
the fixed-depth combined-charge terminal for that same exponent. -/
theorem exists_depth_bankPaperCombinedChargeTerminal_uniform_tangentChoice
    {c : ℝ} (hc : C0 < c) :
    ∃ depth : ℕ, 201 ≤ depth ∧
      ∀ (W : ℕ) (r0 : ℝ), r0 < 2 →
        IsPaperCombinedTangentDeltaStar c W r0
            (paperCombinedTangentDeltaStar c W r0) ∧
          BankPaperCombinedChargeTerminalAtDepth c
            (paperCombinedTangentDeltaStar c W r0) depth := by
  obtain ⟨depth, hdepth, huniform⟩ :=
    exists_depth_bankPaperCombinedChargeTerminal_uniform_deltaStar hc
  refine ⟨depth, hdepth, ?_⟩
  intro W r0 hr0
  have hspec := paperCombinedTangentDeltaStar_spec W hc hr0
  exact ⟨hspec, huniform _ hspec.1⟩

end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankPaperCanonicalRatioCellGeometryTrafficConnector -/
section


/-!
# Same-cutoff connector for canonical ratio-cell geometry and traffic

The qualitative occupancy theorem and the quantitative traffic theorem each
choose a fixed cutoff.  Their uniform predicates are both preserved when the
cutoff is increased, so their witnesses can be synchronized by taking a
maximum.

The already packaged geometry output cannot itself simply be transported to a
larger cutoff: its finite prime type, band map, and cell map all depend on the
old cutoff.  Instead this connector transports the underlying uniform prime
interval predicate and invokes `bankPaperCanonical_ratioCellGeometry_spec`
anew at the common cutoff.  The terminal exposes, for that same `W`,

* the quantitative PNT and Mertens inputs used by the traffic envelopes;
* the bounded-index and occupied-cell inputs;
* the exact tail endpoint data used by the guarded continuation; and
* the fixed-ratio locality used by the distributed clean-list adapter.

No new analytic or geometric assumption is introduced.
-/

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.PrimeBandQuadrature
open Erdos390.Full.RegularRelativeMesh
open Erdos390.Full.RegularMeshPrimeCutoffs

noncomputable section

/-! ## Monotonicity of the two uniform cutoff predicates -/

/-- Uniform prime-interval occupancy remains valid after increasing its
lower cutoff. -/
theorem tangentFixedRatioPrimeIntervalOccupied_mono_cutoff
    {W W' : Nat} {rho : Real} (hWW' : W <= W')
    (hprime : TangentFixedRatioPrimeIntervalOccupied W rho) :
    TangentFixedRatioPrimeIntervalOccupied W' rho := by
  intro A hW'A
  exact hprime A (hWW'.trans hW'A)

/-- The quantitative fixed-ratio prime-count lower bound remains valid after
increasing its lower cutoff. -/
theorem tangentFixedRatioPrimeCountLower_mono_cutoff
    {W W' : Nat} {rho : Real} (hWW' : W <= W')
    (hPNT : TangentFixedRatioPrimeCountLower W rho) :
    TangentFixedRatioPrimeCountLower W' rho := by
  intro A hW'A
  exact hPNT A (hWW'.trans hW'A)

/-! ## One common cutoff for geometry, continuation tails, and traffic -/



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



private theorem paperFixedExceptionalFactors_disjoint_ordinaryComponentOccurrences
    {n h : Nat}
    (R : BankPaperRealization n (upperEndpoint n h))
    (deltaStar : Real) :
    Disjoint (R.paperFixedExceptionalFactors deltaStar)
      R.ordinaryComponentOccurrences := by
  classical
  rw [Finset.disjoint_left]
  intro occurrence hfixed hordinary
  rw [ordinaryComponentOccurrences, Finset.mem_biUnion] at hordinary
  obtain ⟨request, _hrequest, hrequestOccurrence⟩ := hordinary
  rw [BankOrdinaryPaperRealization.componentOccurrences,
    Finset.mem_image] at hrequestOccurrence
  obtain ⟨kind, _hkind, rfl⟩ := hrequestOccurrence
  cases kind with
  | sourceState =>
      have htail :=
        R.paperFixedExceptionalFactors_subset_tail deltaStar hfixed
      have hsource :=
        R.ordinary.sourceStateValue_le_two_mul_n request
      simp only [BankOrdinaryPaperRealization.occurrenceValue_sourceState,
        Finset.mem_Ioc] at htail
      omega
  | targetState =>
      have htail :=
        R.paperFixedExceptionalFactors_subset_tail deltaStar hfixed
      have htargetSource :=
        R.ordinary.targetStateValue_lt_sourceStateValue request
      have hsource :=
        R.ordinary.sourceStateValue_le_two_mul_n request
      simp only [BankOrdinaryPaperRealization.occurrenceValue_targetState,
        Finset.mem_Ioc] at htail
      omega
  | donor =>
      have hdonor :
          R.ordinary.occurrenceValue request
              BankOrdinaryPaperOccurrenceKind.donor ∈
            R.prechargeDonorSet := by
        simpa only [BankOrdinaryPaperRealization.occurrenceValue_donor,
          prechargeDonorValue] using
          R.prechargeDonorValue_mem_prechargeDonorSet
            (Sum.inr request : BankPaperMarkerRequest n)
      exact (Finset.disjoint_left.mp
        (R.paperFixedExceptionalFactors_disjoint_prechargeDonorSet
          deltaStar)) hfixed hdonor

private theorem bottomComponentOccurrence_mem_allComponentOccurrences
    {n M : Nat} (R : BankPaperRealization n M)
    (request : ↑(bankBottomRelevantPaperRequests n))
    {occurrence : Nat}
    (hoccurrence :
      occurrence ∈
        R.bottom.componentOccurrences
          (bankBottomRelevantRequestToPaperRequest request)) :
    occurrence ∈ R.allComponentOccurrences := by
  rw [allComponentOccurrences, Finset.mem_union]
  right
  rw [bottomComponentOccurrences,
    BankBottomPaperRealization.relevantComponentOccurrences,
    Finset.mem_biUnion]
  exact ⟨request, Finset.mem_attach _ _, hoccurrence⟩

/-- Exact finite collision reduction.

There are no hidden ordinary-component or donor exclusions: those follow
from the strict-tail interval and the set difference in the definition of
the fixed factors.  The displayed bottom-state exclusions are therefore
equivalent to disjointness from the full actual occurrence census. -/
theorem bankPaperCanonicalSectionNineFixedComponentCollisionFree_iff_bottomStateExclusions
    {c : Real} {n : Nat}
    (R : BankPaperRealization n
      (upperEndpoint n (upperTailLength c n)))
    (deltaStar : Real) :
    R.BankPaperCanonicalSectionNineFixedComponentCollisionFree deltaStar ↔
      R.BankPaperCanonicalSectionNineBottomStateCollisionExclusions
        deltaStar := by
  classical
  constructor
  · intro hcollision request
    let fullRequest :=
      bankBottomRelevantRequestToPaperRequest request
    change Disjoint (R.paperFixedExceptionalFactors deltaStar)
      R.allComponentOccurrences at hcollision
    constructor
    · intro hlowerFixed
      apply (Finset.disjoint_left.mp hcollision) hlowerFixed
      apply R.bottomComponentOccurrence_mem_allComponentOccurrences request
      rw [R.bottom.componentOccurrences_eq_states_insert_donor fullRequest]
      exact Finset.mem_insert_self _ _
    · intro _hupperNeDonor hupperFixed
      apply (Finset.disjoint_left.mp hcollision) hupperFixed
      apply R.bottomComponentOccurrence_mem_allComponentOccurrences request
      rw [R.bottom.componentOccurrences_eq_states_insert_donor fullRequest]
      exact Finset.mem_insert.mpr
        (Or.inr (Finset.mem_insert_self _ _))
  · intro hexclusions
    unfold BankPaperCanonicalSectionNineFixedComponentCollisionFree
    rw [Finset.disjoint_left]
    intro occurrence hfixed hoccurrence
    rw [allComponentOccurrences, Finset.mem_union] at hoccurrence
    rcases hoccurrence with hordinary | hbottom
    · exact (Finset.disjoint_left.mp
        (paperFixedExceptionalFactors_disjoint_ordinaryComponentOccurrences
          R deltaStar)) hfixed hordinary
    · rw [bottomComponentOccurrences,
        BankBottomPaperRealization.relevantComponentOccurrences,
        Finset.mem_biUnion] at hbottom
      obtain ⟨request, _hrequest, hrequestOccurrence⟩ := hbottom
      let fullRequest :=
        bankBottomRelevantRequestToPaperRequest request
      have hstateExclusions := hexclusions request
      rw [R.bottom.componentOccurrences_eq_states_insert_donor fullRequest]
        at hrequestOccurrence
      simp only [Finset.mem_insert, Finset.mem_singleton]
        at hrequestOccurrence
      rcases hrequestOccurrence with hlower | hupper | hdonor
      · subst occurrence
        exact hstateExclusions.1 hfixed
      · subst occurrence
        by_cases hupperDonor :
            R.bottom.upperStateFactor fullRequest =
              R.bottom.donorFactor fullRequest
        · have hdonorMem :
              R.bottom.upperStateFactor fullRequest ∈
                R.prechargeDonorSet := by
            rw [hupperDonor]
            simpa only [prechargeDonorValue, fullRequest] using
              R.prechargeDonorValue_mem_prechargeDonorSet
                (Sum.inl request : BankPaperMarkerRequest n)
          exact (Finset.disjoint_left.mp
            (R.paperFixedExceptionalFactors_disjoint_prechargeDonorSet
              deltaStar)) hfixed hdonorMem
        · exact (hstateExclusions.2 hupperDonor) hfixed
      · subst occurrence
        have hdonorMem :
            R.bottom.donorFactor fullRequest ∈ R.prechargeDonorSet := by
          simpa only [prechargeDonorValue, fullRequest] using
            R.prechargeDonorValue_mem_prechargeDonorSet
              (Sum.inl request : BankPaperMarkerRequest n)
        exact (Finset.disjoint_left.mp
          (R.paperFixedExceptionalFactors_disjoint_prechargeDonorSet
            deltaStar)) hfixed hdonorMem

private theorem bottomLowerStateFactor_le_two_mul_n_of_scaledEndpoint_narrow
    {n M : Nat} (R : BankPaperRealization n M)
    (hnarrow : 5 * M ≤ 12 * n)
    (request : ↑(bankBottomRelevantPaperRequests n)) :
    R.bottom.lowerStateFactor
        (bankBottomRelevantRequestToPaperRequest request) ≤
      2 * n := by
  let fullRequest :=
    bankBottomRelevantRequestToPaperRequest request
  change R.bottom.lowerStateFactor fullRequest ≤ 2 * n
  have hrow := R.bottom.marker_mem_row
    R.ordinary.two_mul_n_le_M fullRequest
  cases hmove : R.bottom.move fullRequest <;>
    simp only [hmove, bankBottomMarkerInterval, bankBottomMarkerLower,
      bankBottomMarkerUpper, Finset.mem_Ioc,
      BankBottomPaperRealization.lowerStateFactor, bankBottomLowerState,
      bankBottomLowerStateMultiplier] at hrow ⊢ <;>
    omega

private theorem bottomUpperStateFactor_le_two_mul_n_or_eq_donor_of_scaledEndpoint_narrow
    {n M : Nat} (R : BankPaperRealization n M)
    (hnarrow : 5 * M ≤ 12 * n)
    (request : ↑(bankBottomRelevantPaperRequests n)) :
    let fullRequest :=
      bankBottomRelevantRequestToPaperRequest request
    R.bottom.upperStateFactor fullRequest ≤ 2 * n ∨
      R.bottom.upperStateFactor fullRequest =
        R.bottom.donorFactor fullRequest := by
  let fullRequest :=
    bankBottomRelevantRequestToPaperRequest request
  change R.bottom.upperStateFactor fullRequest ≤ 2 * n ∨
    R.bottom.upperStateFactor fullRequest =
      R.bottom.donorFactor fullRequest
  have hrow := R.bottom.marker_mem_row
    R.ordinary.two_mul_n_le_M fullRequest
  cases hmove : R.bottom.move fullRequest
  · left
    simp only [hmove, bankBottomMarkerInterval, bankBottomMarkerLower,
      bankBottomMarkerUpper, Finset.mem_Ioc,
      BankBottomPaperRealization.upperStateFactor, bankBottomUpperState,
      bankBottomUpperStateMultiplier] at hrow ⊢
    omega
  · left
    simp only [hmove, bankBottomMarkerInterval, bankBottomMarkerLower,
      bankBottomMarkerUpper, Finset.mem_Ioc,
      BankBottomPaperRealization.upperStateFactor, bankBottomUpperState,
      bankBottomUpperStateMultiplier] at hrow ⊢
    omega
  · right
    exact (R.bottom.donorFactor_eq_upperStateFactor_of_terminalMove
      fullRequest (Or.inl hmove)).symm
  · right
    exact (R.bottom.donorFactor_eq_upperStateFactor_of_terminalMove
      fullRequest (Or.inr hmove)).symm

/-- The paper's narrow-endpoint inequality rules out every remaining finite
collision, so the literal fixed factors avoid the full component census. -/
theorem bankPaperCanonicalSectionNineFixedComponentCollisionFree_of_scaledEndpoint_narrow
    {c : Real} {n : Nat}
    (R : BankPaperRealization n
      (upperEndpoint n (upperTailLength c n)))
    (deltaStar : Real)
    (hnarrow :
      5 * upperEndpoint n (upperTailLength c n) ≤ 12 * n) :
    R.BankPaperCanonicalSectionNineFixedComponentCollisionFree
      deltaStar := by
  rw [R.bankPaperCanonicalSectionNineFixedComponentCollisionFree_iff_bottomStateExclusions
    deltaStar]
  intro request
  let fullRequest :=
    bankBottomRelevantRequestToPaperRequest request
  constructor
  · intro hlowerFixed
    have hlowerTail :=
      R.paperFixedExceptionalFactors_subset_tail deltaStar hlowerFixed
    have hlowerBound :=
      bottomLowerStateFactor_le_two_mul_n_of_scaledEndpoint_narrow
        R hnarrow request
    simp only [Finset.mem_Ioc] at hlowerTail
    omega
  · intro hupperNeDonor hupperFixed
    have hupperTail :=
      R.paperFixedExceptionalFactors_subset_tail deltaStar hupperFixed
    rcases
        bottomUpperStateFactor_le_two_mul_n_or_eq_donor_of_scaledEndpoint_narrow
          R hnarrow request with hupperBound | hupperDonor
    · simp only [Finset.mem_Ioc] at hupperTail
      omega
    · exact hupperNeDonor hupperDonor

end BankPaperRealization

/-- At the literal paper endpoint the fixed/component collision premise is
eventually automatic, uniformly over every realized bank and every value of
the exceptional exponent. -/
theorem eventually_bankPaperCanonicalSectionNineFixedComponentCollisionFree
    {c : Real} (hc : 0 < c) :
    ∀ᶠ n : Nat in atTop,
      ∀ (R : BankPaperRealization n
          (upperEndpoint n (upperTailLength c n)))
        (deltaStar : Real),
        R.BankPaperCanonicalSectionNineFixedComponentCollisionFree
          deltaStar := by
  filter_upwards [eventually_bankBottom_scaledEndpoint_narrow hc]
    with n hnarrow
  intro R deltaStar
  exact
    R.bankPaperCanonicalSectionNineFixedComponentCollisionFree_of_scaledEndpoint_narrow
      deltaStar hnarrow

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





/-! ## Public one-index assembly -/

set_option maxHeartbeats 2000000 in
theorem bankPaperCanonicalSectionNineTopFrozenFinalPayload_eventStep
    {delta eta : Real} (M : RegularRelativeMesh.Mesh delta eta)
    {P : Finset Nat}
    (B : BridgeData (PaperHeadSimplex.Tag P)
      (BankPaperCanonicalExponentBand M))
    {c r0 deltaStar sigma rho tangentConstant Cpost : Real}
    {depth K0 n W : Nat}
    (hdelta : 0 < delta)
    (hBn : B.sampleData.n = n) (hBW : B.sampleData.W = W)
    (hWtwo : 2 ≤ W)
    (hr0three : r0 < 3 / 2)
    (hrho : 1 < rho) (hratio : rho ^ 3 < r0)
    (htangent : 0 < tangentConstant) (hsigma : 0 < sigma)
    (hMertens : fullReciprocalSumUniformCutoff ≤ W)
    (hPNT : TangentFixedRatioPrimeCountLower W rho)
    (hprime : TangentFixedRatioPrimeIntervalOccupied W rho)
    (Hinput :
      BankPaperCanonicalSectionNineTopFrozenSynchronizedPostHfitInputAt
        M B c depth K0 deltaStar rho sigma Cpost hdelta)
    (Hbudget :
      ∀ (hn : 1 < n) (hW : W ≠ 0)
        (R : BankPaperRealization n
          (upperEndpoint n (upperTailLength c n)))
        (certificate : GuardedCentralAnchorCertificate c depth n
          R.anchorGuardLeftCore R.anchorGuardRightCore
          (R.centralChangedMarkers depth))
        (S : ScaleSeparation M n W)
        (endpoint : Nat → Real),
        BankPaperCanonicalSectionNineBudgetClosure
          (K0 := K0) M B R certificate deltaStar sigma
          hdelta hn hW S r0 rho tangentConstant Cpost endpoint)
    (Hmoment :
      ∃ hWne : W ≠ 0, ∃ hn : 1 < n,
        (∀ k : Fin M.cellCount,
          (2 : Real) ≤ scalePoint n (M.lower k)) ∧
        ∀ S : ScaleSeparation M n W,
          RegularMeshPrimeCutoffs.Mesh.MomentReady M
            (RegularMeshPrimeCutoffs.Mesh.canonicalPartition
              M hdelta hn hWne S))
    (Hcollision :
      ∀ (R : BankPaperRealization n
          (upperEndpoint n (upperTailLength c n)))
        (deltaStar : Real),
        R.BankPaperCanonicalSectionNineFixedComponentCollisionFree
          deltaStar)
    (hKh : (K0 + 1) * upperTailLength c n ≤ n) :
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
          ∃ W' K : Nat,
            ∃ selector : Nat → Real,
              ∃ flow : BankPaperCanonicalTangentPrime n W' →
                  BankPaperCanonicalTangentPrime n W' → Real,
                ∃ L sigma' : Real,
                  R.BankPaperCanonicalSectionNineFinalPayload (K := K)
                    certificate deltaStar selector flow L sigma' := by
  subst n
  subst W
  obtain ⟨R, certificate, hcombined, hbaseDvd, hchargeDvd,
    htargetTail, hWne, S, hpartition, Tsource, betaProt, alpha,
    beta, qTilde, placementSeed, activeSeed, radius, quota, path,
    endpoint, Hpost⟩ := Hinput
  obtain ⟨hWmoment, hn, hTwo, HmomentReady⟩ := Hmoment
  have Hbudget' :
      BankPaperCanonicalSectionNineBudgetClosure
        (K0 := K0) M B R certificate deltaStar sigma
          hdelta hn hWmoment S r0 rho tangentConstant Cpost endpoint :=
    Hbudget hn hWmoment R certificate S endpoint
  unfold BankPaperCanonicalSectionNineBudgetClosure at Hbudget'
  obtain ⟨_hBnBudget, _hBWBudget, hlowerPos, hlower, hlowerScale,
    hmain, herror, hceiling, hscaleDom, hscale⟩ := Hbudget'
  have hdensity :
      0 < tangentPaperCleanListDensity B.sampleData.W r0 :=
    tangentPaperCleanListDensity_pos B.sampleData.W
      (hr0three.trans (by norm_num))
  have hN : 0 < secondOrderScale B.sampleData.n :=
    secondOrderScale_pos (by omega)
  have hfixedComponents :
      R.BankPaperCanonicalSectionNineFixedComponentCollisionFree
        deltaStar :=
    Hcollision R deltaStar
  let flow :
      BankPaperCanonicalTangentPrime B.sampleData.n B.sampleData.W →
        BankPaperCanonicalTangentPrime B.sampleData.n B.sampleData.W → Real :=
    R.bankPaperCanonicalSectionNineRatioCellFlow
      M certificate deltaStar (K0 + 1) hdelta B.n_gt_one
        hWne S rho endpoint
  have hpayload :
      R.BankPaperCanonicalSectionNineFinalPayload (K := K0 + 1)
        certificate deltaStar endpoint flow B.L sigma := by
    exact
      (BankPaperRealization.bankPaperCanonicalSectionNineFinalPayload_of_topFrozenRoundedPostHfit
        (M := M) (B := B) (c := c) (depth := depth) (K0 := K0)
        (R := R) (certificate := certificate) (Tsource := Tsource)
        (deltaStar := deltaStar) (betaProt := betaProt)
        (alpha := alpha) (beta := beta) (qTilde := qTilde)
        (sigma := sigma) (placementSeed := placementSeed)
        (activeSeed := activeSeed) (radius := radius) (Cpost := Cpost)
        (quota := quota) (path := path) (endpoint := endpoint)
        (hdelta := hdelta) (hWtwo := hWtwo) (S := S)
        (hpartition := hpartition) (r0 := r0) (rho := rho)
        (tangentConstant := tangentConstant)
        (N := secondOrderScale B.sampleData.n)
        (density := tangentPaperCleanListDensity B.sampleData.W r0)
        (hrho := hrho) (hratio := hratio) (htangent := htangent.le)
        (hN := hN) (hscaleDom := hscaleDom)
        (hMertens := hMertens) (hPNT := hPNT) (hprime := hprime)
        (hTwo := hTwo) (Hmoment := HmomentReady S) (Hpost := Hpost)
        (hKh := hKh) (hdensity := hdensity) (hsigma := hsigma)
        (hscale := hscale) (hchargeDvd := hchargeDvd)
        (hfixedComponents := hfixedComponents) (hmain := hmain)
        (herror := herror) (hceiling := hceiling)
        (hlowerPos := hlowerPos) (hlower := hlower)
        (hlowerScale := hlowerScale)).1
  exact ⟨R, certificate, hcombined, hbaseDvd, htargetTail,
    B.sampleData.W, K0 + 1, endpoint, flow, B.L, sigma, hpayload⟩

/-! ## Eventual direct terminal packaging -/

/-- Assemble a same-depth distributed Section 9 terminal from an eventual
frozen-top synchronized input.  All source-independent Section 9 estimates
are supplied by the existing automatic eventual theorems. -/
theorem
    bankPaperCanonicalDistributedSectionNineTerminalAtDepth_of_topFrozenSynchronizedPostHfit
    {delta eta : Real} (M : RegularRelativeMesh.Mesh delta eta)
    {P : Finset Nat}
    (B : Nat → BridgeData (PaperHeadSimplex.Tag P)
      (BankPaperCanonicalExponentBand M))
    (W K0 depth : Nat)
    {c r0 deltaStar rho tangentConstant sigma Cpost Cq : Real}
    (hdelta : 0 < delta) (hc : 0 < c)
    (hr0one : 1 < r0) (hr0three : r0 < 3 / 2)
    (hdeltaStar :
      IsPaperCombinedTangentDeltaStar c W r0 deltaStar)
    (hWtwo : 2 ≤ W) (hprefix : 2 * depth + 1 ≤ W)
    (hMoment : canonicalActualMomentCutoff ≤ W)
    (hMertens : fullReciprocalSumUniformCutoff ≤ W)
    (hrho : 1 < rho) (hratio : rho ^ 3 < r0)
    (htangent : 0 < tangentConstant) (hsigma : 0 < sigma)
    (hwidth :
      delta + M.ratio ≤
        bankPaperCanonicalRatioCellPaperWidthChoice
          (tangentPaperCleanListDensity W r0)
          sigma rho tangentConstant)
    (hCpost : 0 ≤ Cpost)
    (hcoefficient :
      (2 / 9 : Real) * Cpost * Cq ≤ tangentConstant)
    (hPNT : TangentFixedRatioPrimeCountLower W rho)
    (hprime :
      TangentFixedRatioPrimeIntervalOccupied W rho)
    (hsync :
      ∀ᶠ n : Nat in atTop,
        (B n).sampleData.n = n ∧
          (B n).sampleData.W = W)
    (hqUpper :
      ∀ᶠ n : Nat in atTop,
        (B n).q ≤ Cq * secondOrderScale n)
    (Hinput :
      BankPaperCanonicalSectionNineTopFrozenSynchronizedPostHfitInput
        M B c depth K0 deltaStar rho sigma Cpost hdelta) :
    BankPaperCanonicalDistributedSectionNineTerminalAtDepth
      c deltaStar depth := by
  have Hbudget :=
    eventually_bankPaperCanonicalSectionNineBudgetClosure
      M B W K0 depth hdelta hc hr0one hr0three
      hdeltaStar.1.1 hdeltaStar.1.2.1 hdeltaStar.2
      hWtwo hprefix hrho hratio htangent hsigma hwidth
      hCpost hcoefficient hsync hqUpper
  have HmomentReady :=
    eventually_bankPaperCanonical_actualMomentReady
      M hdelta W hMoment
  have Hcollision :=
    eventually_bankPaperCanonicalSectionNineFixedComponentCollisionFree hc
  have HKh :=
    BankPaperRealization.eventually_mul_upperTailLength_le_self
      (K0 + 1) hc
  simp only
    [BankPaperCanonicalSectionNineTopFrozenSynchronizedPostHfitInput]
    at Hinput
  simp only [BankPaperCanonicalDistributedSectionNineTerminalAtDepth]
  filter_upwards [Hinput, hsync, Hbudget, HmomentReady, Hcollision, HKh] with
    n HinputN hsyncN HbudgetN HmomentN HcollisionN hKhN
  exact
    bankPaperCanonicalSectionNineTopFrozenFinalPayload_eventStep
      M (B n) hdelta hsyncN.1 hsyncN.2 hWtwo hr0three
      hrho hratio htangent hsigma hMertens hPNT hprime
      HinputN HbudgetN HmomentN HcollisionN hKhN

end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankPaperCanonicalSectionNinePostHeightSourceFirstCutoffAwareDistributedTerminalConnector -/
section


/-!
# Cutoff-aware source-first distributed Section 9 terminal

The source-first analytic completion chooses its Proposition 8.7 width
cutoff only after the common capacity depth has been fixed.  Consequently
the final paper width must be chosen after that cutoff is known.  This
connector performs that choice in the required order: it first obtains the
depth-uniform combined-charge terminal, then the analytic cutoff `W0`, and
finally takes one width dominating `W0` together with the anchor, Mertens,
moment, prime-count, and prime-occupancy cutoffs.

The tangent exponent and the combined-charge terminal are specialized only
at that final width.  Thus the analytic completion and the distributed
finite-payload event step use the same `W`, `deltaStar`, and capacity depth.
-/

open Filter

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel
open Erdos390.Full.PrimeBandQuadrature
open Erdos390.Full.RegularMeshPrimeCutoffs

noncomputable section

namespace BankPaperRealization

/-- The cutoff-aware source-first analytic construction produces a
distributed Section 9 terminal at the same depth and tangent exponent as the
depth-uniform combined-charge terminal.

The conclusion retains the paper-range tangent certificate and the actual
combined-charge terminal.  In the proof, the final width is selected only
after the Proposition 8.7 cutoff supplied by the analytic completion. -/
theorem
    exists_bankPaperCanonicalSectionNinePostHeight_sourceFirstCutoffAwareDistributedTerminal
    {c : Real} (hc : C0 < c) :
    ∃ depth W : Nat, ∃ r0 deltaStar : Real,
      201 ≤ depth ∧
        2 ≤ W ∧
        2 * depth + 1 ≤ W ∧
        fullReciprocalSumUniformCutoff ≤ W ∧
        canonicalActualMomentCutoff ≤ W ∧
        1 < r0 ∧
        r0 < 3 / 2 ∧
        IsPaperCombinedTangentDeltaStar c W r0 deltaStar ∧
        BankPaperCombinedChargeTerminalAtDepth c deltaStar depth ∧
        BankPaperCanonicalDistributedSectionNineTerminalAtDepth
          c deltaStar depth := by
  obtain ⟨depth, hdepth, huniform⟩ :=
    exists_depth_bankPaperCombinedChargeTerminal_uniform_tangentChoice hc
  obtain ⟨W0, Hcompletion⟩ :=
    exists_bankPaperCanonicalSectionNinePostHeight_sourceFirstCutoffAwareAnalyticCompletion
      hc depth hdepth
  let r0 : Real := 5 / 4
  let rho : Real := 21 / 20
  have hr0one : 1 < r0 := by norm_num [r0]
  have hr0three : r0 < 3 / 2 := by norm_num [r0]
  have hr0two : r0 < 2 := by norm_num [r0]
  have hrho : 1 < rho := by norm_num [rho]
  have hratio : rho ^ 3 < r0 := by norm_num [rho, r0]
  obtain ⟨WPNT, _hWPNTtwo, _hWPNTMertens, hWPNT⟩ :=
    exists_fixedRatioPrimeCountLower_and_Mertens_cutoff hrho
  obtain ⟨Woccupancy, _hWoccupancyTwo, hWoccupancy⟩ :=
    exists_fixedRatioPrimeIntervalOccupancy_cutoff hrho
  let Wpaper : Nat :=
    max (2 * depth + 1)
      (max tangentSelbergMertensBase
        (max canonicalActualMomentCutoff (max WPNT Woccupancy)))
  let W : Nat := max W0 Wpaper
  have hW0 : W0 ≤ W := by
    dsimp only [W]
    exact le_max_left _ _
  have hWpaper : Wpaper ≤ W := by
    dsimp only [W]
    exact le_max_right _ _
  have hprefixPaper : 2 * depth + 1 ≤ Wpaper := by
    dsimp only [Wpaper]
    exact le_max_left _ _
  have hprefix : 2 * depth + 1 ≤ W :=
    hprefixPaper.trans hWpaper
  have hMertensBasePaper :
      tangentSelbergMertensBase ≤ Wpaper := by
    dsimp only [Wpaper]
    exact
      (le_max_left tangentSelbergMertensBase
        (max canonicalActualMomentCutoff (max WPNT Woccupancy))).trans
          (le_max_right _ _)
  have hMertensBase : tangentSelbergMertensBase ≤ W :=
    hMertensBasePaper.trans hWpaper
  have hWtwo : 2 ≤ W :=
    tangentSelbergMertensBase_ge_two.trans hMertensBase
  have hMertens : fullReciprocalSumUniformCutoff ≤ W :=
    tangentSelbergMertensBase_ge_cutoff.trans hMertensBase
  have hMomentPaper : canonicalActualMomentCutoff ≤ Wpaper := by
    dsimp only [Wpaper]
    exact
      ((le_max_left canonicalActualMomentCutoff
        (max WPNT Woccupancy)).trans
          (le_max_right tangentSelbergMertensBase
            (max canonicalActualMomentCutoff (max WPNT Woccupancy)))).trans
        (le_max_right _ _)
  have hMoment : canonicalActualMomentCutoff ≤ W :=
    hMomentPaper.trans hWpaper
  have hWPNTpaper : WPNT ≤ Wpaper := by
    dsimp only [Wpaper]
    exact
      (((le_max_left WPNT Woccupancy).trans
        (le_max_right canonicalActualMomentCutoff
          (max WPNT Woccupancy))).trans
          (le_max_right tangentSelbergMertensBase
            (max canonicalActualMomentCutoff (max WPNT Woccupancy)))).trans
        (le_max_right _ _)
  have hWPNTW : WPNT ≤ W :=
    hWPNTpaper.trans hWpaper
  have hWoccupancyPaper : Woccupancy ≤ Wpaper := by
    dsimp only [Wpaper]
    exact
      (((le_max_right WPNT Woccupancy).trans
        (le_max_right canonicalActualMomentCutoff
          (max WPNT Woccupancy))).trans
          (le_max_right tangentSelbergMertensBase
            (max canonicalActualMomentCutoff (max WPNT Woccupancy)))).trans
        (le_max_right _ _)
  have hWoccupancyW : Woccupancy ≤ W :=
    hWoccupancyPaper.trans hWpaper
  have hPNT : TangentFixedRatioPrimeCountLower W rho :=
    tangentFixedRatioPrimeCountLower_mono_cutoff hWPNTW hWPNT
  have hprime : TangentFixedRatioPrimeIntervalOccupied W rho :=
    tangentFixedRatioPrimeIntervalOccupied_mono_cutoff
      hWoccupancyW hWoccupancy
  let deltaStar := paperCombinedTangentDeltaStar c W r0
  obtain ⟨hdeltaStar, Hcharge⟩ :=
    huniform W r0 hr0two
  have Hanalytic :=
    Hcompletion W hW0 hWtwo hprefix hMertens hMoment
      r0 deltaStar hr0one hr0three hdeltaStar Hcharge
  unfold
    BankPaperCanonicalSectionNineTopFrozenSynchronizedAnalyticCompletion
    at Hanalytic
  obtain
      ⟨delta, eta, M, P, B, K0, tangentConstant, sigma,
        Cpost, Cq, hdelta, htangent, hsigma, hwidth, hCpost,
        hcoefficient, hsync, hqUpper, Hinput⟩ :=
    Hanalytic
  have hcPos : 0 < c := by
    have hC0Pos : (0 : Real) < C0 := by norm_num [C0]
    exact hC0Pos.trans hc
  have Hterminal :
      BankPaperCanonicalDistributedSectionNineTerminalAtDepth
        c deltaStar depth :=
    bankPaperCanonicalDistributedSectionNineTerminalAtDepth_of_topFrozenSynchronizedPostHfit
      M B W K0 depth hdelta hcPos hr0one hr0three hdeltaStar
      hWtwo hprefix hMoment hMertens hrho hratio htangent hsigma
      hwidth hCpost hcoefficient hPNT hprime hsync hqUpper Hinput
  exact
    ⟨depth, W, r0, deltaStar, hdepth, hWtwo, hprefix, hMertens,
      hMoment, hr0one, hr0three, hdeltaStar, Hcharge, Hterminal⟩

end BankPaperRealization

end

end Erdos390.WholePaper

end

theorem solution : Erdos390.RemainingAnalyticGoal004_020 := by
  exact @Erdos390.WholePaper.BankPaperRealization.exists_bankPaperCanonicalSectionNinePostHeight_sourceFirstCutoffAwareDistributedTerminal
