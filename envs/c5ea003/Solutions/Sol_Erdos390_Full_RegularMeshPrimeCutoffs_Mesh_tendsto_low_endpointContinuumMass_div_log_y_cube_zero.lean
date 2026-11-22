-- Prove2me | solution 1 for Erdos390.Full.RegularMeshPrimeCutoffs.Mesh.tendsto_low_endpointContinuumMass_div_log_y_cube_zero
-- status  : ACCEPTED   (prove)
-- author  : @doctosil
-- created : 2026-09-17T15:30:15.411042+00:00
-- url     : https://prove2.me/submissions/ae9ad2d9-79e9-48d7-bda8-4919228b2add

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
import Definitions.Def_erdos390_analytic_foundations_005

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











end Mesh



end

end Erdos390.Full.RegularRelativeMesh

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

theorem scalePoint_add (n : ℕ) (a b : ℝ) :
    scalePoint n (a + b) = scalePoint n a * scalePoint n b := by
  unfold scalePoint
  rw [add_mul, Real.exp_add]

namespace Mesh

variable {delta eta : ℝ} (M : Mesh delta eta)

/-- The multiplicative ratio of a positive cell tends beyond two. -/
theorem eventually_two_mul_scalePoint_lower_le_upper
    (hdelta : 0 < delta) (k : Fin M.cellCount) :
    ∀ᶠ n : ℕ in atTop,
      2 * scalePoint n (M.lower k) ≤ scalePoint n (M.upper k) := by
  have hwidth := tendsto_scalePoint_atTop (M.width_pos hdelta k)
  have hevent := hwidth.eventually (eventually_ge_atTop (2 : ℝ))
  filter_upwards [hevent] with n hn
  have hsum : M.upper k = M.lower k + M.width k := by
    unfold RegularRelativeMesh.Mesh.width
    ring
  rw [hsum, scalePoint_add]
  have hlower : 0 ≤ scalePoint n (M.lower k) := by
    unfold scalePoint
    exact (Real.exp_pos _).le
  simpa only [mul_comm] using mul_le_mul_of_nonneg_left hn hlower

/-- The lower endpoint of every fixed positive cell eventually exceeds
one. -/
theorem eventually_one_le_scalePoint_lower
    (hdelta : 0 < delta) (k : Fin M.cellCount) :
    ∀ᶠ n : ℕ in atTop, 1 ≤ scalePoint n (M.lower k) :=
  (tendsto_scalePoint_atTop (M.lower_pos hdelta k)).eventually
    (eventually_ge_atTop (1 : ℝ))

/-- All explicit separation inequalities hold simultaneously because the
mesh has finitely many cells. -/
theorem eventually_scaleSeparation
    (hdelta : 0 < delta) (W : ℕ) :
    ∀ᶠ n : ℕ in atTop, ScaleSeparation M n W := by
  have hlow := (tendsto_scalePoint_atTop hdelta).eventually
    (eventually_ge_atTop (2 * W : ℝ))
  have hpositive : ∀ᶠ n : ℕ in atTop,
      ∀ k : Fin M.cellCount,
        1 ≤ scalePoint n (M.lower k) ∧
          2 * scalePoint n (M.lower k) ≤ scalePoint n (M.upper k) := by
    rw [Filter.eventually_all]
    intro k
    exact (eventually_one_le_scalePoint_lower M hdelta k).and
      (eventually_two_mul_scalePoint_lower_le_upper M hdelta k)
  filter_upwards [hlow, hpositive] with n hnLow hnPositive
  exact ⟨hnLow, hnPositive⟩



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

/- Source module: Erdos390.Full.CanonicalEndpointDoubleKernelRowEventually -/
section


/-!
# Canonical sharp-row aggregation of the double-kernel quadrature

This file closes the two-index application-layer item in the audit of paper
Lemma 8.4.  The normalized double-prime estimate is applied to the literal
canonical endpoints and then summed in the sharp arithmetic norm.  The low
output and low input are treated separately; in particular no factor
`1 / alpha_0` is hidden in a finite-dimensional constant.
-/

open scoped BigOperators
open Filter Topology Set

noncomputable section

namespace Erdos390.Full.RegularMeshPrimeCutoffs

open ArithmeticModel ArithmeticBandGeometry RegularRelativeMesh
open KernelPrimeQuadrature DoubleKernelPrimeQuadrature
open ContinuumCellGraph ContinuumCellGraph.IntervalMesh
open CompressedArithmeticOperator PositiveCellTransfer PrimeBandQuadrature

namespace Mesh

variable {delta eta : ℝ} (M : Mesh delta eta)











/-- The moving low continuum harmonic mass grows much more slowly than the
cube of the ambient logarithm.  This is the rate needed when a positive
input column is divided by the moving low centre. -/
theorem tendsto_low_endpointContinuumMass_div_log_y_cube_zero
    (hdelta : 0 < delta) {W : ℕ} (hWTwo : 2 ≤ W) :
    Tendsto (fun n : ℕ ↦
      endpointContinuumMass M n W (lowBand M) /
        Real.log (y n) ^ 3) atTop (nhds 0) := by
  have hUpperCoord : Tendsto (fun n : ℕ ↦
      actualCutoffCoordinate M n W 1) atTop (nhds delta) := by
    simpa only [actualCutoffCoordinate, fullCutoff_succ, M.endpoint_zero] using
      tendsto_floor_scalePoint_coordinate hdelta
  have hUpperLog : Tendsto (fun n : ℕ ↦
      Real.log (actualCutoffCoordinate M n W 1)) atTop
      (nhds (Real.log delta)) :=
    (Real.continuousAt_log (ne_of_gt hdelta)).tendsto.comp hUpperCoord
  have hLogY : Tendsto (fun n : ℕ ↦ Real.log (y n)) atTop atTop :=
    tendsto_log_y_atTop
  have hInvLogY : Tendsto (fun n : ℕ ↦ (Real.log (y n))⁻¹)
      atTop (nhds 0) := tendsto_inv_atTop_zero.comp hLogY
  have hUpperPart : Tendsto (fun n : ℕ ↦
      Real.log (actualCutoffCoordinate M n W 1) /
        Real.log (y n) ^ 3) atTop (nhds 0) := by
    have h := hUpperLog.mul (hInvLogY.pow 3)
    simpa only [mul_zero, zero_pow (by norm_num : 3 ≠ 0),
      div_eq_mul_inv, inv_pow] using h
  have hWlog : 0 < Real.log (W : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < W by omega))
  have hConstPart : Tendsto (fun n : ℕ ↦
      Real.log (Real.log (W : ℝ)) / Real.log (y n) ^ 3)
      atTop (nhds 0) := by
    have h := (tendsto_const_nhds : Tendsto
      (fun _n : ℕ ↦ Real.log (Real.log (W : ℝ))) atTop
      (nhds (Real.log (Real.log (W : ℝ))))).mul (hInvLogY.pow 3)
    simpa only [mul_zero, zero_pow (by norm_num : 3 ≠ 0),
      div_eq_mul_inv, inv_pow] using h
  have hLogLogRatio : Tendsto (fun n : ℕ ↦
      Real.log (Real.log (y n)) / Real.log (y n)) atTop (nhds 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp hLogY
  have hLogLogPart : Tendsto (fun n : ℕ ↦
      Real.log (Real.log (y n)) / Real.log (y n) ^ 3)
      atTop (nhds 0) := by
    have hInvSq := hInvLogY.pow 2
    have h := hLogLogRatio.mul hInvSq
    have h0 : Tendsto (fun n : ℕ ↦
        (Real.log (Real.log (y n)) / Real.log (y n)) *
          (Real.log (y n))⁻¹ ^ 2) atTop (nhds 0) := by
      simpa only [mul_zero, zero_mul, zero_pow (by norm_num : 2 ≠ 0)] using h
    apply h0.congr'
    have hne : ∀ᶠ n : ℕ in atTop, Real.log (y n) ≠ 0 :=
      hLogY.eventually (eventually_ne_atTop 0)
    filter_upwards [hne] with n hnlog
    field_simp [hnlog]
  have hSum := (hUpperPart.sub hConstPart).add hLogLogPart
  have hSum0 : Tendsto (fun n : ℕ ↦
      Real.log (actualCutoffCoordinate M n W 1) / Real.log (y n) ^ 3 -
        Real.log (Real.log (W : ℝ)) / Real.log (y n) ^ 3 +
        Real.log (Real.log (y n)) / Real.log (y n) ^ 3)
      atTop (nhds 0) := by simpa using hSum
  apply hSum0.congr'
  filter_upwards [eventually_gt_atTop 1,
    eventually_scaleSeparation M hdelta W] with n hn S
  have hylog : 0 < Real.log (y n) := by
    rw [Scale.log_y (Nat.zero_lt_of_lt hn)]
    exact mul_pos (by norm_num) (Real.log_pos (by exact_mod_cast hn))
  have hUpperPos : 0 < actualCutoffCoordinate M n W 1 := by
    unfold actualCutoffCoordinate realLogCoordinate
    apply div_pos
    · apply Real.log_pos
      exact_mod_cast (show 1 < fullCutoff M n W 1 by
        exact (show 1 < W by omega).trans_le (W_le_first_fullCutoff M S))
    · exact hylog
  have hLowerCoord :
      actualCutoffCoordinate M n W 0 =
        Real.log (W : ℝ) / Real.log (y n) := by rfl
  have hLowerPos : 0 < actualCutoffCoordinate M n W 0 := by
    rw [hLowerCoord]
    exact div_pos hWlog hylog
  unfold endpointContinuumMass lowBand
  simp only [Nat.zero_add, fullCutoff_zero]
  rw [show Real.log (fullCutoff M n W 1 : ℝ) =
      actualCutoffCoordinate M n W 1 * Real.log (y n) by
        unfold actualCutoffCoordinate realLogCoordinate
        field_simp [ne_of_gt hylog],
    show Real.log (W : ℝ) =
      actualCutoffCoordinate M n W 0 * Real.log (y n) by
        rw [hLowerCoord]
        field_simp [ne_of_gt hylog],
    Real.log_mul (ne_of_gt hUpperPos) (ne_of_gt hylog),
    Real.log_mul (ne_of_gt hLowerPos) (ne_of_gt hylog)]
  rw [hLowerCoord, Real.log_div (ne_of_gt hWlog) (ne_of_gt hylog)]
  ring































end Mesh
end Erdos390.Full.RegularMeshPrimeCutoffs

end

theorem solution :
∀ {delta eta : Real} (M : Erdos390.Full.RegularRelativeMesh.Mesh delta eta),
  LT.lt.{0} (0 : Real) delta →
    ∀ {W : Nat},
      LE.le.{0} (2 : Nat) W →
        Filter.Tendsto.{0, 0}
          (fun n =>
            HDiv.hDiv.{0, 0, 0}
              (Erdos390.Full.RegularMeshPrimeCutoffs.Mesh.endpointContinuumMass M n W
                (Erdos390.Full.RegularMeshPrimeCutoffs.Mesh.lowBand M))
              (HPow.hPow.{0, 0, 0} (Real.log (Erdos390.Full.ArithmeticModel.y n)) (3 : Nat)))
          Filter.atTop.{0} (nhds.{0} (0 : Real)) := by
  exact @Erdos390.Full.RegularMeshPrimeCutoffs.Mesh.tendsto_low_endpointContinuumMass_div_log_y_cube_zero
