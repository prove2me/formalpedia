-- Prove2me | solution 1 for Erdos390.Full.RegularMeshPrimeCutoffs.Mesh.eventually_endpointRelativeCenterBound_le
-- status  : ACCEPTED   (prove)
-- author  : @doctosil
-- created : 2026-09-17T15:28:25.017869+00:00
-- url     : https://prove2.me/submissions/1c23819a-b275-41f6-b738-e36c5a3acb45

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

theorem lower_lt_upper (hdelta : 0 < delta) (k : Fin M.cellCount) :
    M.lower k < M.upper k := by
  rw [← sub_pos, ← width]
  exact M.width_pos hdelta k









end Mesh



end

end Erdos390.Full.RegularRelativeMesh

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





/-- Rescaling both endpoints by `log z` leaves their harmonic-coordinate
length unchanged. -/
lemma log_logCoordinate_sub {z : ℝ} {A Y : ℕ}
    (hz : 1 < z) (hA : 2 ≤ A) (hAY : A ≤ Y) :
    Real.log (logCoordinate z Y) - Real.log (logCoordinate z A) =
      Real.log (Real.log (Y : ℝ)) -
        Real.log (Real.log (A : ℝ)) := by
  have hY : 2 ≤ Y := hA.trans hAY
  have hlogz0 : Real.log z ≠ 0 := ne_of_gt (Real.log_pos hz)
  have hlogA0 : Real.log (A : ℝ) ≠ 0 :=
    ne_of_gt (Real.log_pos (by exact_mod_cast (show 1 < A by omega)))
  have hlogY0 : Real.log (Y : ℝ) ≠ 0 :=
    ne_of_gt (Real.log_pos (by exact_mod_cast (show 1 < Y by omega)))
  unfold logCoordinate
  rw [Real.log_div hlogY0 hlogz0, Real.log_div hlogA0 hlogz0]
  ring























end Erdos390.Full.PrimeBandQuadrature

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

/- Source module: Erdos390.Full.CanonicalRegularMeshEndpointFamily -/
section


/-!
# The canonical `n`-indexed endpoint family for a regular mesh

This module exposes the actual partition constructed from the explicit
cutoffs, rather than only asserting its existence.  Consequently the low
cell and every later lower endpoint can be audited definitionally.
-/

open Filter

noncomputable section

namespace Erdos390.Full.RegularMeshPrimeCutoffs

open ArithmeticModel ArithmeticBandGeometry
open RegularRelativeMesh
open PrimeIntervalPartitionConstructor PositiveCellTransfer

namespace Mesh

variable {delta eta : ℝ} (M : Mesh delta eta)





















/-- Each fixed non-low lower endpoint crosses every prescribed PNT
threshold. -/
theorem eventually_threshold_le_nonlow_fullCutoff
    (hdelta : 0 < delta) (W X : ℕ)
    (j : Fin (M.cellCount + 1)) (hj : j ≠ lowBand M) :
    ∀ᶠ n : ℕ in atTop, X ≤ fullCutoff M n W j.1 := by
  have hjpos : 0 < j.1 := by
    by_contra hnot
    apply hj
    exact Fin.ext (Nat.eq_zero_of_not_pos hnot)
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hjpos)
  have hklt : k < M.cellCount := by omega
  let q : Fin M.cellCount := ⟨k, hklt⟩
  have htop := tendsto_scalePoint_atTop (M.endpoint_pos hdelta k)
  have hevent := htop.eventually (eventually_ge_atTop (X : ℝ))
  filter_upwards [hevent] with n hn
  rw [hk, fullCutoff_succ]
  apply Nat.le_floor
  simpa only [q, RegularRelativeMesh.Mesh.lower] using hn



end Mesh
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

/- Source module: Erdos390.Full.CanonicalEndpointMeshGeometryEventually -/
section


/-!
# Eventual geometry of the literal canonical endpoint mesh

The first endpoint is the fixed cutoff `W` and the last is `floor y`.
This file proves, rather than assumes, that the two omitted tails vanish and
that every actual floored cell inherits any strict upper bound satisfied by
its ideal regular-mesh length.
-/

open Filter Topology

noncomputable section

namespace Erdos390.Full.RegularMeshPrimeCutoffs

open ArithmeticModel RegularRelativeMesh KernelPrimeQuadrature

namespace Mesh

variable {delta eta : ℝ} (M : Mesh delta eta)



theorem tendsto_low_actualCoordinateLength
    (hdelta : 0 < delta) (W : ℕ) :
    Tendsto (fun n : ℕ ↦
      actualCutoffCoordinate M n W 1 - actualCutoffCoordinate M n W 0)
      atTop (nhds delta) := by
  have hUpper : Tendsto (fun n : ℕ ↦ actualCutoffCoordinate M n W 1)
      atTop (nhds delta) := by
    simpa only [actualCutoffCoordinate, fullCutoff_succ, M.endpoint_zero] using
      tendsto_floor_scalePoint_coordinate hdelta
  have hLower := tendsto_fixed_cutoffCoordinate_zero W
  have hLower' : Tendsto
      (fun n : ℕ ↦ actualCutoffCoordinate M n W 0)
      atTop (nhds 0) := by
    simpa only [actualCutoffCoordinate, fullCutoff_zero] using hLower
  simpa only [sub_zero] using hUpper.sub hLower'

theorem tendsto_positive_actualCoordinateLength
    (hdelta : 0 < delta) (W : ℕ) (k : Fin M.cellCount) :
    Tendsto (fun n : ℕ ↦
      actualCutoffCoordinate M n W (k.1 + 2) -
      actualCutoffCoordinate M n W (k.1 + 1))
      atTop (nhds (M.width k)) := by
  have hUpper : Tendsto (fun n : ℕ ↦
      actualCutoffCoordinate M n W (k.1 + 2))
      atTop (nhds (M.upper k)) := by
    have hpos : 0 < M.upper k :=
      (M.lower_pos hdelta k).trans (M.lower_lt_upper hdelta k)
    simpa only [actualCutoffCoordinate,
      show k.1 + 2 = (k.1 + 1) + 1 by omega,
      fullCutoff_succ, RegularRelativeMesh.Mesh.upper] using
        tendsto_floor_scalePoint_coordinate hpos
  have hLower : Tendsto (fun n : ℕ ↦
      actualCutoffCoordinate M n W (k.1 + 1))
      atTop (nhds (M.lower k)) := by
    simpa only [actualCutoffCoordinate, fullCutoff_succ,
      RegularRelativeMesh.Mesh.lower] using
        tendsto_floor_scalePoint_coordinate (M.lower_pos hdelta k)
  simpa only [RegularRelativeMesh.Mesh.width] using hUpper.sub hLower







end Mesh
end Erdos390.Full.RegularMeshPrimeCutoffs

end

/- Source module: Erdos390.Full.CanonicalEndpointRelativeCenterEventually -/
section


/-!
# Relative centre convergence for the canonical endpoint family

This is the endpoint-level convergence needed by the moving-low sharp
projection.  In particular the conclusion is relative even on the low band,
whose centre tends to zero.  Constants in the two PNT estimates are selected
before the cutoff and before `n`.
-/

open Filter Topology

noncomputable section

namespace Erdos390.Full.RegularMeshPrimeCutoffs

open ArithmeticModel ArithmeticBandGeometry RegularRelativeMesh
open PositiveCellTransfer PrimeBandQuadrature MovingLowMomentQuadrature
open MovingLowGaugeTransfer KernelPrimeQuadrature

/- The cutoff is chosen solely from the two global prime-sum estimates.  In
particular it is definitionally independent of every later regular mesh. -/


namespace Mesh

variable {delta eta : ℝ} (M : Mesh delta eta)











theorem endpointContinuumMoment_eq_coordinateLength
    {n W : ℕ} (hn : 1 < n) (j : Fin (M.cellCount + 1)) :
    endpointContinuumMoment M n W j =
      actualCutoffCoordinate M n W (j.1 + 1) -
        actualCutoffCoordinate M n W j.1 := by
  have hlog : Real.log (y n) ≠ 0 := by
    rw [Scale.log_y (Nat.zero_lt_of_lt hn)]
    exact mul_ne_zero (by norm_num) (ne_of_gt
      (Real.log_pos (by exact_mod_cast hn)))
  unfold endpointContinuumMoment actualCutoffCoordinate realLogCoordinate
  field_simp [hlog]

theorem tendsto_low_endpointContinuumMoment
    (hdelta : 0 < delta) (W : ℕ) :
    Tendsto (fun n : ℕ ↦
      endpointContinuumMoment M n W (lowBand M))
      atTop (nhds delta) := by
  have hcoord := tendsto_low_actualCoordinateLength M hdelta W
  apply hcoord.congr'
  filter_upwards [eventually_gt_atTop 1] with n hn
  rw [endpointContinuumMoment_eq_coordinateLength M hn]
  rfl

theorem tendsto_positive_endpointContinuumMoment
    (hdelta : 0 < delta) (W : ℕ) (k : Fin M.cellCount) :
    Tendsto (fun n : ℕ ↦
      endpointContinuumMoment M n W (positiveBand M k))
      atTop (nhds (M.width k)) := by
  have hcoord := tendsto_positive_actualCoordinateLength M hdelta W k
  apply hcoord.congr'
  filter_upwards [eventually_gt_atTop 1] with n hn
  rw [endpointContinuumMoment_eq_coordinateLength M hn]
  rfl

theorem tendsto_positive_endpointContinuumMass
    (hdelta : 0 < delta) (W : ℕ) (k : Fin M.cellCount) :
    Tendsto (fun n : ℕ ↦
      endpointContinuumMass M n W (positiveBand M k))
      atTop (nhds (Real.log (M.upper k) - Real.log (M.lower k))) := by
  have hLower : Tendsto (fun n : ℕ ↦
      actualCutoffCoordinate M n W (k.1 + 1))
      atTop (nhds (M.lower k)) := by
    simpa only [actualCutoffCoordinate, fullCutoff_succ,
      RegularRelativeMesh.Mesh.lower] using
        tendsto_floor_scalePoint_coordinate (M.lower_pos hdelta k)
  have hUpper : Tendsto (fun n : ℕ ↦
      actualCutoffCoordinate M n W (k.1 + 2))
      atTop (nhds (M.upper k)) := by
    have hup : 0 < M.upper k :=
      (M.lower_pos hdelta k).trans (M.lower_lt_upper hdelta k)
    simpa only [actualCutoffCoordinate,
      show k.1 + 2 = (k.1 + 1) + 1 by omega,
      fullCutoff_succ, RegularRelativeMesh.Mesh.upper] using
        tendsto_floor_scalePoint_coordinate hup
  have hLogLower :=
    (Real.continuousAt_log (ne_of_gt (M.lower_pos hdelta k))).tendsto.comp
      hLower
  have hup : 0 < M.upper k :=
    (M.lower_pos hdelta k).trans (M.lower_lt_upper hdelta k)
  have hLogUpper :=
    (Real.continuousAt_log (ne_of_gt hup)).tendsto.comp hUpper
  have hCoordMass := hLogUpper.sub hLogLower
  apply hCoordMass.congr'
  have hTwo := eventually_threshold_le_nonlow_fullCutoff M hdelta W 2
    (positiveBand M k) (by
      intro h
      have := congrArg Fin.val h
      simp only [positiveBand, lowBand, Fin.val_mk] at this
      omega)
  filter_upwards [eventually_gt_atTop 1,
    eventually_scaleSeparation M hdelta W, hTwo] with n hn S hLowerTwo
  have hAY : fullCutoff M n W (k.1 + 1) ≤
      fullCutoff M n W (k.1 + 2) :=
    fullCutoff_monotone M hdelta hn (W_le_first_fullCutoff M S) (by omega)
  have hmass := log_logCoordinate_sub
    (show 1 < y n by
      have hlog : 0 < Real.log (y n) := by
        rw [Scale.log_y (Nat.zero_lt_of_lt hn)]
        exact mul_pos (by norm_num) (Real.log_pos (by exact_mod_cast hn))
      exact (Real.log_pos_iff (Scale.y_pos
        (Nat.zero_lt_of_lt hn)).le).mp hlog)
    hLowerTwo hAY
  simpa only [endpointContinuumMass, positiveBand,
    actualCutoffCoordinate, realLogCoordinate,
    PrimeBandQuadrature.logCoordinate] using hmass

theorem tendsto_low_endpointContinuumMass_atTop
    (hdelta : 0 < delta) (W : ℕ) :
    Tendsto (fun n : ℕ ↦
      endpointContinuumMass M n W (lowBand M)) atTop atTop := by
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
  unfold endpointContinuumMass lowBand
  simp only [Nat.zero_add, fullCutoff_zero]
  linarith

theorem tendsto_general_positive_lowerCutoff_atTop
    (hdelta : 0 < delta) (W : ℕ) (k : Fin M.cellCount) :
    Tendsto (fun n : ℕ ↦ fullCutoff M n W (k.1 + 1))
      atTop atTop := by
  simpa only [fullCutoff_succ, RegularRelativeMesh.Mesh.lower] using
    tendsto_nat_floor_atTop.comp
      (tendsto_scalePoint_atTop (M.lower_pos hdelta k))

theorem tendsto_positive_endpointMassError_zero
    (hdelta : 0 < delta) (C : ℝ) (W : ℕ) (k : Fin M.cellCount) :
    Tendsto (fun n : ℕ ↦
      endpointMassError M C n W (positiveBand M k))
      atTop (nhds 0) := by
  have hReal : Tendsto (fun n : ℕ ↦
      (fullCutoff M n W (k.1 + 1) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp
      (tendsto_general_positive_lowerCutoff_atTop M hdelta W k)
  have hLog := Real.tendsto_log_atTop.comp hReal
  have hInv := tendsto_inv_atTop_zero.comp hLog
  have hMain := (tendsto_const_nhds : Tendsto
    (fun _n : ℕ ↦ 5 * C) atTop (nhds (5 * C))).mul (hInv.pow 3)
  have hMainZero : Tendsto (fun n : ℕ ↦
      5 * C * (Real.log (fullCutoff M n W (k.1 + 1) : ℝ))⁻¹ ^ 3)
      atTop (nhds 0) := by simpa using hMain
  apply hMainZero.congr'
  filter_upwards with n
  unfold endpointMassError positiveBand
  rw [div_eq_mul_inv, inv_pow]

theorem tendsto_positive_endpointMomentError_zero
    (hdelta : 0 < delta) (C : ℝ) (W : ℕ) (k : Fin M.cellCount) :
    Tendsto (fun n : ℕ ↦
      endpointMomentError M C n W (positiveBand M k))
      atTop (nhds 0) := by
  have hReal : Tendsto (fun n : ℕ ↦
      (fullCutoff M n W (k.1 + 1) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp
      (tendsto_general_positive_lowerCutoff_atTop M hdelta W k)
  have hLog := Real.tendsto_log_atTop.comp hReal
  have hInvA := tendsto_inv_atTop_zero.comp hLog
  have hInvY := tendsto_inv_atTop_zero.comp tendsto_log_y_atTop
  have hNumerator : Tendsto (fun n : ℕ ↦
      2 * C * (Real.log (fullCutoff M n W (k.1 + 1) : ℝ))⁻¹ ^ 3 +
        (C / 2) *
          (Real.log (fullCutoff M n W (k.1 + 1) : ℝ))⁻¹ ^ 2)
      atTop (nhds 0) := by
    convert ((tendsto_const_nhds.mul (hInvA.pow 3)).add
      (tendsto_const_nhds.mul (hInvA.pow 2))) using 1
    all_goals ring
  have hMain := hNumerator.mul hInvY
  have hMainZero : Tendsto (fun n : ℕ ↦
      (2 * C * (Real.log (fullCutoff M n W (k.1 + 1) : ℝ))⁻¹ ^ 3 +
        (C / 2) *
          (Real.log (fullCutoff M n W (k.1 + 1) : ℝ))⁻¹ ^ 2) *
        (Real.log (y n))⁻¹) atTop (nhds 0) := by
    simpa using hMain
  apply hMainZero.congr'
  filter_upwards with n
  unfold endpointMomentError positiveBand
  ring

theorem tendsto_low_endpointMomentError_zero
    (C : ℝ) (W : ℕ) :
    Tendsto (fun n : ℕ ↦
      endpointMomentError M C n W (lowBand M))
      atTop (nhds 0) := by
  have hInvY := tendsto_inv_atTop_zero.comp tendsto_log_y_atTop
  have hMain := (tendsto_const_nhds : Tendsto (fun _n : ℕ ↦
      2 * C / Real.log (W : ℝ) ^ 3 +
        C / (2 * Real.log (W : ℝ) ^ 2)) atTop
      (nhds (2 * C / Real.log (W : ℝ) ^ 3 +
        C / (2 * Real.log (W : ℝ) ^ 2)))).mul hInvY
  simpa only [endpointMomentError, lowBand, Fin.val_mk,
    fullCutoff_zero, div_eq_mul_inv, mul_zero] using hMain

/-- For every fixed admissible cutoff, the full relative centre bound tends
to zero simultaneously in all canonical bands. -/
theorem eventually_endpointRelativeCenterBound_le
    (hdelta : 0 < delta) {W : ℕ}
    (Cmass Cmoment : ℝ) {e : ℝ} (he : 0 < e) :
    ∀ᶠ n : ℕ in atTop, ∀ j : Fin (M.cellCount + 1),
      0 < endpointContinuumMass M n W j ∧
      0 < endpointContinuumMoment M n W j ∧
      endpointMassError M Cmass n W j ≤
        endpointContinuumMass M n W j / 2 ∧
      endpointRelativeCenterBound M Cmass Cmoment n W j ≤ e := by
  have hLowMass := tendsto_low_endpointContinuumMass_atTop M hdelta W
  have hLowMoment := tendsto_low_endpointContinuumMoment M hdelta W
  have hLowMomentErr := tendsto_low_endpointMomentError_zero M Cmoment W
  let lowMassErr := 5 * Cmass / Real.log (W : ℝ) ^ 3
  have hLowMassErrEq : ∀ n,
      endpointMassError M Cmass n W (lowBand M) = lowMassErr := by
    intro n
    rfl
  have hLowReady : ∀ᶠ n : ℕ in atTop,
      0 < endpointContinuumMass M n W (lowBand M) ∧
      0 < endpointContinuumMoment M n W (lowBand M) ∧
      endpointMassError M Cmass n W (lowBand M) ≤
        endpointContinuumMass M n W (lowBand M) / 2 ∧
      endpointRelativeCenterBound M Cmass Cmoment n W (lowBand M) ≤ e := by
    have hMassPos := hLowMass.eventually (eventually_gt_atTop 0)
    have hMomentPos := hLowMoment.eventually
      (eventually_gt_nhds hdelta)
    have hMassSmall := hLowMass.eventually
      (eventually_ge_atTop (2 * lowMassErr))
    have hRel : Tendsto (fun n : ℕ ↦
        endpointRelativeCenterBound M Cmass Cmoment n W (lowBand M))
        atTop (nhds 0) := by
      unfold endpointRelativeCenterBound
      have hTwo : Tendsto (fun _n : ℕ ↦ (2 : ℝ)) atTop (nhds 2) :=
        tendsto_const_nhds
      have hFirst := (hTwo.mul hLowMomentErr).div hLowMoment
        (ne_of_gt hdelta)
      have hMassErrT : Tendsto (fun n : ℕ ↦
          endpointMassError M Cmass n W (lowBand M))
          atTop (nhds lowMassErr) := by
        apply tendsto_const_nhds.congr'
        exact Filter.Eventually.of_forall hLowMassErrEq
      have hSecond := (hTwo.mul hMassErrT).div_atTop hLowMass
      simpa only [Pi.div_apply, mul_zero, zero_div, add_zero] using
        hFirst.add hSecond
    have hRelSmall := hRel.eventually (eventually_le_nhds he)
    filter_upwards [hMassPos, hMomentPos, hMassSmall, hRelSmall] with
      n hm hmo hsmall hrel
    refine ⟨hm, hmo, ?_, hrel⟩
    rw [hLowMassErrEq]
    linarith
  have hPositiveReady : ∀ᶠ n : ℕ in atTop,
      ∀ k : Fin M.cellCount,
      0 < endpointContinuumMass M n W (positiveBand M k) ∧
      0 < endpointContinuumMoment M n W (positiveBand M k) ∧
      endpointMassError M Cmass n W (positiveBand M k) ≤
        endpointContinuumMass M n W (positiveBand M k) / 2 ∧
      endpointRelativeCenterBound M Cmass Cmoment n W
        (positiveBand M k) ≤ e := by
    rw [Filter.eventually_all]
    intro k
    have hMass := tendsto_positive_endpointContinuumMass M hdelta W k
    have hMoment := tendsto_positive_endpointContinuumMoment M hdelta W k
    have hMassErr := tendsto_positive_endpointMassError_zero M hdelta Cmass W k
    have hMomentErr :=
      tendsto_positive_endpointMomentError_zero M hdelta Cmoment W k
    have hMassLimit : 0 < Real.log (M.upper k) - Real.log (M.lower k) :=
      sub_pos.mpr (Real.strictMonoOn_log (M.lower_pos hdelta k)
        ((M.lower_pos hdelta k).trans (M.lower_lt_upper hdelta k))
        (M.lower_lt_upper hdelta k))
    have hMomentLimit : 0 < M.width k := M.width_pos hdelta k
    have hMassPos := hMass.eventually (eventually_gt_nhds hMassLimit)
    have hMomentPos := hMoment.eventually
      (eventually_gt_nhds hMomentLimit)
    have hMassSmall : Tendsto (fun n : ℕ ↦
        endpointContinuumMass M n W (positiveBand M k) / 2 -
          endpointMassError M Cmass n W (positiveBand M k))
        atTop (nhds ((Real.log (M.upper k) - Real.log (M.lower k)) / 2)) := by
      simpa only [sub_zero] using hMass.div_const 2 |>.sub hMassErr
    have hMassSmallEvent := hMassSmall.eventually
      (eventually_ge_nhds (div_pos hMassLimit (by norm_num)))
    have hRel : Tendsto (fun n : ℕ ↦
        endpointRelativeCenterBound M Cmass Cmoment n W
          (positiveBand M k)) atTop (nhds 0) := by
      unfold endpointRelativeCenterBound
      have hTwo : Tendsto (fun _n : ℕ ↦ (2 : ℝ)) atTop (nhds 2) :=
        tendsto_const_nhds
      have hFirst := (hTwo.mul hMomentErr).div hMoment
        (ne_of_gt hMomentLimit)
      have hSecond := (hTwo.mul hMassErr).div hMass
        (ne_of_gt hMassLimit)
      simpa only [Pi.div_apply, mul_zero, zero_div, add_zero] using
        hFirst.add hSecond
    have hRelEvent := hRel.eventually (eventually_le_nhds he)
    filter_upwards [hMassPos, hMomentPos, hMassSmallEvent, hRelEvent] with
      n hm hmo hsmall hrel
    exact ⟨hm, hmo, by linarith, hrel⟩
  filter_upwards [hLowReady, hPositiveReady] with n hlow hpos
  intro j
  refine Fin.cases ?_ (fun k ↦ ?_) j
  · simpa only [lowBand] using hlow
  · simpa only [positiveBand] using hpos k





end Mesh
end Erdos390.Full.RegularMeshPrimeCutoffs

end

theorem solution :
∀ {delta eta : Real} (M : Erdos390.Full.RegularRelativeMesh.Mesh delta eta),
  LT.lt.{0} (0 : Real) delta →
    ∀ {W : Nat} (Cmass Cmoment : Real) {e : Real},
      LT.lt.{0} (0 : Real) e →
        ∀ᶠ (n : Nat) in Filter.atTop.{0},
          ∀ (j : Fin (HAdd.hAdd.{0, 0, 0} (Erdos390.Full.RegularRelativeMesh.Mesh.cellCount M) (1 : Nat))),
            And (LT.lt.{0} (0 : Real) (Erdos390.Full.RegularMeshPrimeCutoffs.Mesh.endpointContinuumMass M n W j))
              (And (LT.lt.{0} (0 : Real) (Erdos390.Full.RegularMeshPrimeCutoffs.Mesh.endpointContinuumMoment M n W j))
                (And
                  (LE.le.{0} (Erdos390.Full.RegularMeshPrimeCutoffs.Mesh.endpointMassError M Cmass n W j)
                    (HDiv.hDiv.{0, 0, 0} (Erdos390.Full.RegularMeshPrimeCutoffs.Mesh.endpointContinuumMass M n W j)
                      (2 : Real)))
                  (LE.le.{0}
                    (Erdos390.Full.RegularMeshPrimeCutoffs.Mesh.endpointRelativeCenterBound M Cmass Cmoment n W j) e))) := by
  exact @Erdos390.Full.RegularMeshPrimeCutoffs.Mesh.eventually_endpointRelativeCenterBound_le
