-- Prove2me | solution 1 for Erdos390.Full.RegularMeshPrimeCutoffs.Mesh.canonicalCenterEnvelopeCutoff_eventually_inverse
-- status  : ACCEPTED   (prove)
-- author  : @doctosil
-- created : 2026-09-17T16:17:19.020367+00:00
-- url     : https://prove2.me/submissions/ec7cf146-c70f-456a-9bfc-86d11f78056c

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
import Theorems.Thm_Erdos390_Full_RegularMeshPrimeCutoffs_Mesh_canonicalRelativeCenterCutoff_eventually

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









end

end Erdos390.Full.ArithmeticBandGeometry.Partition

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





















end Mesh
end Erdos390.Full.RegularMeshPrimeCutoffs

end

/- Source module: Erdos390.Full.CanonicalEndpointCenterEnvelopeEventually -/
section


/-!
# The canonical moving-low centre has the sharp reciprocal envelope

This file records the quantitative fact needed when an `o(1)` prime-profile
error is divided by the centre of the moving low cell.  The loss is exactly
`O(log log n)`: uniformly in every proof of scale separation and in every
canonical band,

`1 / center i <= C * log (log n)`.

The proof does not identify the low centre with a fixed continuum centre.
It uses the already proved *relative* endpoint-centre convergence, the
literal endpoint continuum first moment, and an elementary upper bound for
the literal endpoint continuum harmonic mass.  Thus it remains valid for the
moving low endpoint and has the quantifier order required in Sections 8.4--8.6.
-/

open Filter Topology

noncomputable section

namespace Erdos390.Full.RegularMeshPrimeCutoffs

open ArithmeticModel ArithmeticBandGeometry RegularRelativeMesh
open PositiveCellTransfer PrimeBandQuadrature MovingLowMomentQuadrature
open MovingLowGaugeTransfer KernelPrimeQuadrature

/- A mesh-independent cutoff for the sharp moving-low centre envelope. -/






namespace Mesh

variable {delta eta : ℝ} (M : Mesh delta eta)

/-- The literal continuum mass of the canonical low endpoint cell is positive
and is at most `log L`.  The proof uses the actual floored upper endpoint; no
replacement of that endpoint by `y` occurs in the definition. -/
theorem low_endpointContinuumMass_pos_le_logL
    {n W : ℕ} (hdelta : 0 < delta) (hW3 : 3 ≤ W)
    (hn : 1 < n) (hWne : W ≠ 0) (S : ScaleSeparation M n W) :
    0 < endpointContinuumMass M n W (lowBand M) ∧
      endpointContinuumMass M n W (lowBand M) ≤
        Real.log (Scale.L n) := by
  let A := fullCutoff M n W 1
  have hmono : Monotone (fullCutoff M n W) :=
    fullCutoff_monotone M hdelta hn (W_le_first_fullCutoff M S)
  obtain ⟨p, hpPrime, hpLower, hpUpper⟩ :=
    every_fullCutoff_cell_has_prime M hWne S (lowBand M)
  have hWA : W < A := by
    dsimp only [A]
    simpa only [lowBand, Fin.val_mk, Nat.zero_add] using
      hpLower.trans_le hpUpper
  have hWpos : (0 : ℝ) < (W : ℝ) := by positivity
  have hApos : (0 : ℝ) < (A : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by omega : 0 < W) hWA.le)
  have hWone : (1 : ℝ) < Real.log (W : ℝ) := by
    rw [Real.lt_log_iff_exp_lt hWpos]
    exact Real.exp_one_lt_three.trans_le (by exact_mod_cast hW3)
  have hLogWnonneg : 0 ≤ Real.log (Real.log (W : ℝ)) :=
    Real.log_nonneg hWone.le
  have hLogWltLogA : Real.log (W : ℝ) < Real.log (A : ℝ) :=
    Real.strictMonoOn_log hWpos hApos (by exact_mod_cast hWA)
  have hMassPos : 0 < endpointContinuumMass M n W (lowBand M) := by
    unfold endpointContinuumMass lowBand
    simp only [Nat.zero_add, fullCutoff_zero]
    change 0 < Real.log (Real.log (A : ℝ)) -
      Real.log (Real.log (W : ℝ))
    exact sub_pos.mpr
      (Real.strictMonoOn_log (zero_lt_one.trans hWone)
        (zero_lt_one.trans (hWone.trans hLogWltLogA)) hLogWltLogA)
  have hALast : A ≤ fullCutoff M n W (M.cellCount + 1) := by
    exact hmono (by omega)
  have hAyNat : A ≤ yNat n := by
    simpa only [fullCutoff_last M (Nat.zero_lt_of_lt hn)] using hALast
  have hyNatY : (yNat n : ℝ) ≤ y n :=
    Nat.floor_le (Scale.y_pos (Nat.zero_lt_of_lt hn)).le
  have hAY : (A : ℝ) ≤ y n :=
    (by exact_mod_cast hAyNat : (A : ℝ) ≤ (yNat n : ℝ)).trans hyNatY
  have hLogALeLogY : Real.log (A : ℝ) ≤ Real.log (y n) :=
    Real.log_le_log hApos hAY
  have hLpos : 0 < Scale.L n := Scale.L_pos hn
  have hLogALeL : Real.log (A : ℝ) ≤ Scale.L n := by
    calc
      Real.log (A : ℝ) ≤ Real.log (y n) := hLogALeLogY
      _ = (2 / 9 : ℝ) * Scale.L n :=
        Scale.log_y (Nat.zero_lt_of_lt hn)
      _ ≤ Scale.L n := by nlinarith
  have hLogLogALeLogL :
      Real.log (Real.log (A : ℝ)) ≤ Real.log (Scale.L n) :=
    Real.log_le_log
      (zero_lt_one.trans (hWone.trans hLogWltLogA)) hLogALeL
  constructor
  · exact hMassPos
  · unfold endpointContinuumMass lowBand
    simp only [Nat.zero_add, fullCutoff_zero]
    change Real.log (Real.log (A : ℝ)) -
      Real.log (Real.log (W : ℝ)) ≤ Real.log (Scale.L n)
    linarith

/-- Uniform sharp reciprocal-centre envelope for the literal canonical
partition, with its mesh-independent cutoff and explicit constant exposed.
Only the ambient `n` threshold may depend on the later mesh. -/
theorem canonicalCenterEnvelopeCutoff_eventually_inverse
    (hdelta : 0 < delta) (W : ℕ)
    (hW : canonicalCenterEnvelopeCutoff ≤ W) :
      ∀ᶠ n : ℕ in atTop, ∀ (hn : 1 < n) (hWne : W ≠ 0)
        (S : ScaleSeparation M n W) (i : Fin (M.cellCount + 1)),
        1 / (canonicalPartition M hdelta hn hWne S).center i ≤
          canonicalCenterEnvelopeConstant delta * Real.log (Scale.L n) := by
  have hW3 : 3 ≤ W := (le_max_left 3 canonicalRelativeCenterCutoff).trans hW
  have hWr : canonicalRelativeCenterCutoff ≤ W :=
    (le_max_right 3 canonicalRelativeCenterCutoff).trans hW
  have hRelative := canonicalRelativeCenterCutoff_eventually M hdelta W hWr
    (1 / 2 : ℝ) (by norm_num)
  have hLowMoment :=
    (tendsto_low_endpointContinuumMoment M hdelta W).eventually
      (eventually_ge_nhds (by linarith : delta / 2 < delta))
  have hLTop : Tendsto Scale.L atTop atTop := by
    simpa only [Scale.L] using
      Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hLogLTop : Tendsto (fun n : ℕ ↦ Real.log (Scale.L n))
      atTop atTop := Real.tendsto_log_atTop.comp hLTop
  have hLogL := hLogLTop.eventually (eventually_ge_atTop (1 : ℝ))
  filter_upwards [hRelative, hLowMoment, hLogL] with n hrel hmoment hlogL
  obtain ⟨hWne₀, hn₀, S₀, hratio⟩ := hrel
  intro hn hWne S i
  let P := canonicalPartition M hdelta hn hWne S
  let E := canonicalCertificate M hdelta hn hWne S
  have hLlogPos : 0 < Real.log (Scale.L n) := zero_lt_one.trans_le hlogL
  refine Fin.cases ?_ (fun k ↦ ?_) i
  · have hmass :=
      low_endpointContinuumMass_pos_le_logL M hdelta hW3 hn hWne S
    let c : ℝ := endpointContinuumCenter M n W (lowBand M)
    have hcId : c = E.continuumCenter (lowBand M) := by rfl
    have hcPos : 0 < c := by
      dsimp only [c, endpointContinuumCenter]
      exact div_pos ((div_pos hdelta (by norm_num)).trans_le hmoment) hmass.1
    have hcLower : delta / (2 * Real.log (Scale.L n)) ≤ c := by
      dsimp only [c, endpointContinuumCenter]
      calc
        delta / (2 * Real.log (Scale.L n)) =
            (delta / 2) / Real.log (Scale.L n) := by ring
        _ ≤ (delta / 2) /
              endpointContinuumMass M n W (lowBand M) :=
          div_le_div_of_nonneg_left (by positivity) hmass.1 hmass.2
        _ ≤ endpointContinuumMoment M n W (lowBand M) /
              endpointContinuumMass M n W (lowBand M) :=
          div_le_div_of_nonneg_right hmoment hmass.1.le
    have hratio' :
        |P.center (lowBand M) / c - 1| ≤ (1 / 2 : ℝ) := by
      simpa only [P, E, hcId] using hratio (lowBand M)
    have hhalfRatio : (1 / 2 : ℝ) ≤ P.center (lowBand M) / c := by
      have hleft := (abs_le.mp hratio').1
      linarith
    have hcenterLower :
        delta / (4 * Real.log (Scale.L n)) ≤ P.center (lowBand M) := by
      have hhalfCenter : (1 / 2 : ℝ) * c ≤ P.center (lowBand M) :=
        (le_div_iff₀ hcPos).mp hhalfRatio
      calc
        delta / (4 * Real.log (Scale.L n)) =
            (1 / 2 : ℝ) * (delta / (2 * Real.log (Scale.L n))) := by ring
        _ ≤ (1 / 2 : ℝ) * c :=
          mul_le_mul_of_nonneg_left hcLower (by norm_num)
        _ ≤ P.center (lowBand M) := hhalfCenter
    have hcenterPos : 0 < P.center (lowBand M) :=
      (div_pos hdelta (mul_pos (by norm_num) hLlogPos)).trans_le hcenterLower
    have hinv := one_div_le_one_div_of_le
      (div_pos hdelta (mul_pos (by norm_num) hLlogPos)) hcenterLower
    change 1 / P.center (lowBand M) ≤
      canonicalCenterEnvelopeConstant delta * Real.log (Scale.L n)
    calc
      1 / P.center (lowBand M) ≤
          1 / (delta / (4 * Real.log (Scale.L n))) := hinv
      _ = canonicalCenterEnvelopeConstant delta * Real.log (Scale.L n) := by
        unfold canonicalCenterEnvelopeConstant
        field_simp [hdelta.ne', hLlogPos.ne']
  · have hcoord (p : BandPrime n W)
        (hp : p ∈ P.data.fiber (positiveBand M k)) :
        tPrime n p.1 ∈ Set.Icc (M.lower k) (M.upper k) := by
      have hpBand : P.band p = positiveBand M k :=
        (Erdos390.Lemma84.WeightedBandData.mem_fiber_iff P.data).mp hp
      have hpInterval :=
        (PositiveCellTransfer.IntervalCertificate.band_eq_iff E p
          (positiveBand M k)).mp hpBand
      have hpLower := hpInterval.1
      have hpUpper := hpInterval.2
      change fullCutoff M n W (k.1 + 1) < p.1 at hpLower
      change p.1 ≤ fullCutoff M n W (k.1 + 1 + 1) at hpUpper
      simp only [fullCutoff] at hpLower hpUpper
      exact ⟨(realLogCoordinate_floorScale_lt_prime hn hpLower).le,
        prime_logCoordinate_le_of_le_floorScale hn
          (prime_of_mem_primeBand p.2).pos hpUpper⟩
    have hcenterLowerCell : M.lower k ≤ P.center (positiveBand M k) :=
      (P.center_mem_of_coord_bounds (positiveBand M k) hcoord).1
    have hdeltaLower : delta ≤ M.lower k := by
      unfold RegularRelativeMesh.Mesh.lower RegularRelativeMesh.Mesh.endpoint
      have hbase : 1 ≤ 1 + M.ratio := by linarith [M.ratio_pos]
      have hpow : 1 ≤ (1 + M.ratio) ^ k.1 := one_le_pow₀ hbase
      nlinarith
    have hdeltaCenter : delta ≤ P.center (positiveBand M k) :=
      hdeltaLower.trans hcenterLowerCell
    have hinv : 1 / P.center (positiveBand M k) ≤ 1 / delta :=
      one_div_le_one_div_of_le hdelta hdeltaCenter
    change 1 / P.center (positiveBand M k) ≤
      canonicalCenterEnvelopeConstant delta * Real.log (Scale.L n)
    calc
      1 / P.center (positiveBand M k) ≤ 1 / delta := hinv
      _ ≤ canonicalCenterEnvelopeConstant delta * Real.log (Scale.L n) := by
        unfold canonicalCenterEnvelopeConstant
        have hdeltaInvPos : 0 < 1 / delta := one_div_pos.mpr hdelta
        calc
          1 / delta ≤ 4 * (1 / delta) * Real.log (Scale.L n) := by
            nlinarith
          _ = (4 / delta) * Real.log (Scale.L n) := by ring









end Mesh
end Erdos390.Full.RegularMeshPrimeCutoffs

end

theorem solution :
∀ {delta eta : Real} (M : Erdos390.Full.RegularRelativeMesh.Mesh delta eta) (hdelta : LT.lt.{0} (0 : Real) delta)
  (W : Nat),
  LE.le.{0} Erdos390.Full.RegularMeshPrimeCutoffs.canonicalCenterEnvelopeCutoff W →
    ∀ᶠ (n : Nat) in Filter.atTop.{0},
      ∀ (hn : LT.lt.{0} (1 : Nat) n) (hWne : Ne.{1} W (0 : Nat))
        (S : Erdos390.Full.RegularMeshPrimeCutoffs.ScaleSeparation M n W)
        (i : Fin (HAdd.hAdd.{0, 0, 0} (Erdos390.Full.RegularRelativeMesh.Mesh.cellCount M) (1 : Nat))),
        LE.le.{0}
          (HDiv.hDiv.{0, 0, 0} (1 : Real)
            (Erdos390.Full.ArithmeticBandGeometry.Partition.center.{0}
              (Erdos390.Full.RegularMeshPrimeCutoffs.Mesh.canonicalPartition M hdelta hn hWne S) i))
          (HMul.hMul.{0, 0, 0} (Erdos390.Full.RegularMeshPrimeCutoffs.canonicalCenterEnvelopeConstant delta)
            (Real.log (Erdos390.Full.Scale.L n))) := by
  exact @Erdos390.Full.RegularMeshPrimeCutoffs.Mesh.canonicalCenterEnvelopeCutoff_eventually_inverse
