-- Prove2me | solution 1 for Erdos390.Full.RegularMeshPrimeCutoffs.Mesh.exists_global_cutoff_eventually_canonical_diagonalError
-- status  : ACCEPTED   (prove)
-- author  : @doctosil
-- created : 2026-09-17T15:29:40.28662+00:00
-- url     : https://prove2.me/submissions/b772f7c0-9fb2-49ba-8f88-346ff33e6957

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

/- Source module: Erdos390.Full.PositiveCellTransfer -/
section


/-!
# Actual positive-cell prime-band transfer

This file connects the exact arithmetic band geometry to the unconditional
two-endpoint PNT quadrature.  A certificate records that each finite band is
literally a prime interval `(A_j,Y_j]` inside the actual moving prime band.
From that elementary membership statement we derive, rather than assume,

* `H_j = sum_{A_j < p <= Y_j} 1/p`, and
* `H_j * alpha_j = (sum_{A_j < p <= Y_j} log p / p) / log y`.

The final theorems then import the uniform constants and threshold from
`PrimeBandQuadrature`; no Mertens constant or moving-cell asymptotic appears
as a structure field.
-/

open scoped BigOperators
open Set

noncomputable section

namespace Erdos390.Full.PositiveCellTransfer

open ArithmeticModel PrimeSums PrimeBandQuadrature
open ArithmeticBandGeometry

variable {n W : ℕ} {Band : Type*} [Fintype Band] [DecidableEq Band]

/-- Stability of a quotient under independent numerator and denominator
errors.  This elementary estimate is the deterministic ratio step used when
passing from convergence of `H` and `H alpha` to convergence of `alpha`. -/
lemma abs_div_sub_div_le {a b c d e₁ e₂ : ℝ}
    (hb : 0 < b) (hd : d ≠ 0)
    (hac : |a - c| ≤ e₁) (hbd : |b - d| ≤ e₂) :
    |a / b - c / d| ≤
      e₁ / b + |c| * e₂ / (b * |d|) := by
  have hb0 : b ≠ 0 := ne_of_gt hb
  have hidentity :
      a / b - c / d = (a - c) / b + c * (d - b) / (b * d) := by
    field_simp [hb0, hd]
    ring
  rw [hidentity]
  calc
    |(a - c) / b + c * (d - b) / (b * d)| ≤
        |(a - c) / b| + |c * (d - b) / (b * d)| :=
      abs_add_le _ _
    _ = |a - c| / b + |c| * |b - d| / (b * |d|) := by
      simp only [abs_div, abs_mul, abs_of_pos hb, abs_sub_comm]
    _ ≤ e₁ / b + |c| * e₂ / (b * |d|) := by
      apply add_le_add
      · exact div_le_div_of_nonneg_right hac (le_of_lt hb)
      · exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hbd (abs_nonneg c))
          (mul_nonneg (le_of_lt hb) (abs_nonneg d))





namespace IntervalCertificate

variable {P : Partition n W Band} (E : IntervalCertificate P)









omit [DecidableEq Band] in
lemma mem_cellPrimes_iff {j : Band} {p : ℕ} :
    p ∈ E.cellPrimes j ↔
      p.Prime ∧ E.lower j < p ∧ p ≤ E.upper j := by
  rw [cellPrimes, Finset.mem_sdiff]
  simp only [primesUpTo, Finset.mem_filter, Finset.mem_Icc]
  constructor
  · rintro ⟨⟨⟨_hzero, hpUpper⟩, hpPrime⟩, hpLower⟩
    refine ⟨hpPrime, ?_, hpUpper⟩
    by_contra hnot
    apply hpLower
    exact ⟨⟨Nat.zero_le p, Nat.le_of_not_gt hnot⟩, hpPrime⟩
  · rintro ⟨hpPrime, hpLower, hpUpper⟩
    refine ⟨⟨⟨Nat.zero_le p, hpUpper⟩, hpPrime⟩, ?_⟩
    rintro ⟨⟨_hzero, hpLower'⟩, _hpPrime⟩
    exact (Nat.not_lt_of_ge hpLower') hpLower

private lemma primesUpTo_mono {A Y : ℕ} (hAY : A ≤ Y) :
    primesUpTo A ⊆ primesUpTo Y := by
  intro p hp
  simp only [primesUpTo, Finset.mem_filter, Finset.mem_Icc] at hp ⊢
  exact ⟨⟨hp.1.1, hp.1.2.trans hAY⟩, hp.2⟩

omit [DecidableEq Band] in
lemma cellReciprocalSum_eq_sub (j : Band) :
    (∑ p ∈ E.cellPrimes j, 1 / (p : ℝ)) =
      fullReciprocalSum (E.upper j) - fullReciprocalSum (E.lower j) := by
  have hsub := primesUpTo_mono (E.lower_le_upper j)
  have hsum := Finset.sum_sdiff hsub (f := fun p : ℕ => 1 / (p : ℝ))
  change (∑ p ∈ primesUpTo (E.upper j) \ primesUpTo (E.lower j),
      1 / (p : ℝ)) =
    (∑ p ∈ primesUpTo (E.upper j), 1 / (p : ℝ)) -
      ∑ p ∈ primesUpTo (E.lower j), 1 / (p : ℝ)
  exact eq_sub_of_add_eq hsum



lemma fiber_reciprocalSum_eq_cell (j : Band) :
    (∑ p ∈ P.data.fiber j, 1 / (p.1 : ℝ)) =
      ∑ q ∈ E.cellPrimes j, 1 / (q : ℝ) := by
  apply Finset.sum_bij (fun p _hp => p.1)
  · intro p hp
    have hpBand : P.band p = j := by
      simpa only [Erdos390.Lemma84.WeightedBandData.mem_fiber_iff] using hp
    exact E.mem_cellPrimes_iff.mpr
      ⟨prime_of_mem_primeBand p.2, (E.band_eq_iff p j).mp hpBand⟩
  · intro p₁ hp₁ p₂ hp₂ heq
    exact Subtype.ext heq
  · intro q hq
    have hqData := E.mem_cellPrimes_iff.mp hq
    have hqBand : q ∈ primeBand n W := by
      exact mem_primeBand.mpr
        ⟨hqData.1,
          (E.cutoff_le_lower j).trans_lt hqData.2.1,
          hqData.2.2.trans (E.upper_le_yNat j)⟩
    let p : ArithmeticBandGeometry.BandPrime n W := ⟨q, hqBand⟩
    have hpFiber : p ∈ P.data.fiber j := by
      simp only [Erdos390.Lemma84.WeightedBandData.mem_fiber_iff]
      exact (E.band_eq_iff p j).mpr hqData.2
    exact ⟨p, hpFiber, rfl⟩
  · intro p hp
    rfl



/-- Exact arithmetic identification of the harmonic cell mass. -/
theorem mass_eq_fullReciprocalSum_sub (j : Band) :
    P.mass j = fullReciprocalSum (E.upper j) -
      fullReciprocalSum (E.lower j) := by
  change (∑ p ∈ P.data.fiber j, 1 / (p.1 : ℝ)) = _
  rw [E.fiber_reciprocalSum_eq_cell, E.cellReciprocalSum_eq_sub]













end IntervalCertificate

end Erdos390.Full.PositiveCellTransfer

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

/- Source module: Erdos390.Full.KernelPrimeQuadrature -/
section


/-!
# Weighted prime quadrature for the Poisson--Dickman kernel

This file generalizes the scalar Abel summation used for `H_j` to a smooth
test function on logarithmic prime coordinates.  The first layer is an exact
finite identity for the actual primes; later declarations specialize it to
the Poisson--Dickman covariance kernel and its compact derivative bounds.
-/

open scoped BigOperators
open Set

noncomputable section

namespace Erdos390.Full.KernelPrimeQuadrature

open MeasureTheory
open ArithmeticModel PrimeSums PrimeBandQuadrature
open DickmanBasic ConditionedPoissonLimit



















lemma realLogCoordinate_mem_unit {z x : ℝ}
    (hz : 1 < z) (hx : 1 ≤ x) (hxz : x ≤ z) :
    realLogCoordinate z x ∈ Icc (0 : ℝ) 1 := by
  have hlogzpos : 0 < Real.log z := Real.log_pos hz
  have hlogxnonneg : 0 ≤ Real.log x := Real.log_nonneg hx
  have hlogxz : Real.log x ≤ Real.log z :=
    Real.log_le_log (zero_lt_one.trans_le hx) hxz
  unfold realLogCoordinate
  constructor
  · exact div_nonneg hlogxnonneg hlogzpos.le
  · exact (div_le_one hlogzpos).2 hlogxz





































































end Erdos390.Full.KernelPrimeQuadrature

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

/- Source module: Erdos390.Full.DoubleKernelPrimeQuadrature -/
section


/-!
# Double-index prime quadrature for the Poisson--Dickman kernel

This module performs the two prime-index quadratures needed in the
positive-cell part of Lemma 8.4.  The constants are chosen once, before the
kernel coordinate, ambient scale, or moving endpoints.  The moving-low-cell
estimates are kept for the next layer; no lower endpoint tending to zero is
hidden in the positive-cell theorem below.
-/

open scoped BigOperators
open Set

noncomputable section

namespace Erdos390.Full.DoubleKernelPrimeQuadrature

open MeasureTheory
open ArithmeticModel PrimeSums PrimeBandQuadrature
open DickmanBasic ConditionedPoissonLimit
open KernelPrimeQuadrature
open PoissonDickmanKernelBounds
open PositiveCellTransfer

























/-- A pointwise bound on a continuum cell gives the exact harmonic-coordinate
length as its operator norm. -/
lemma abs_continuumCellOperator_le
    (z : ℝ) {A Y : ℕ} (hz : 1 < z) (hA : 2 ≤ A) (hAY : A ≤ Y)
    (f : ℝ → ℝ) {e : ℝ}
    (hint : IntervalIntegrable (fun t => f t / t) volume
      (realLogCoordinate z (A : ℝ)) (realLogCoordinate z (Y : ℝ)))
    (hbound : ∀ t ∈ Icc (realLogCoordinate z (A : ℝ))
      (realLogCoordinate z (Y : ℝ)), |f t| ≤ e) :
    |continuumCellOperator z A Y f| ≤
      e * (Real.log (realLogCoordinate z (Y : ℝ)) -
        Real.log (realLogCoordinate z (A : ℝ))) := by
  let a := realLogCoordinate z (A : ℝ)
  let b := realLogCoordinate z (Y : ℝ)
  have ha : 0 < a := realLogCoordinate_pos_nat hz hA
  have hb : 0 < b := realLogCoordinate_pos_nat hz (hA.trans hAY)
  have hab : a ≤ b := realLogCoordinate_mono_nat hz hA hAY
  have hmajorInt : IntervalIntegrable (fun t : ℝ => e / t) volume a b := by
    apply ContinuousOn.intervalIntegrable_of_Icc hab
    intro t ht
    exact continuousAt_const.div continuousAt_id
      (ne_of_gt (ha.trans_le ht.1)) |>.continuousWithinAt
  unfold continuumCellOperator
  change |∫ t in a..b, f t / t| ≤
    e * (Real.log b - Real.log a)
  calc
    |∫ t in a..b, f t / t| ≤ ∫ t in a..b, |f t / t| :=
      intervalIntegral.abs_integral_le_integral_abs hab
    _ ≤ ∫ t in a..b, e / t := by
      exact intervalIntegral.integral_mono_on hab hint.abs hmajorInt
        (fun t ht => by
          have htpos : 0 < t := ha.trans_le ht.1
          rw [abs_div, abs_of_pos htpos]
          exact div_le_div_of_nonneg_right (hbound t ht) htpos.le)
    _ = e * (Real.log b - Real.log a) := by
      have heq : (fun t : ℝ => e / t) = fun t => e * (1 / t) := by
        funext t
        ring
      rw [heq, intervalIntegral.integral_const_mul,
        integral_one_div_of_pos ha hb, Real.log_div hb.ne' ha.ne']







lemma coordinateCell_mem_unit {z : ℝ} (hz : 1 < z)
    {A Y : ℕ} (hA : 2 ≤ A) (hAY : A ≤ Y) (hYz : (Y : ℝ) ≤ z)
    {t : ℝ}
    (ht : t ∈ Icc (realLogCoordinate z (A : ℝ))
      (realLogCoordinate z (Y : ℝ))) :
    t ∈ Icc (0 : ℝ) 1 := by
  have hlow := realLogCoordinate_mem_unit hz
    (show (1 : ℝ) ≤ (A : ℝ) by exact_mod_cast (show 1 ≤ A by omega))
    ((show (A : ℝ) ≤ (Y : ℝ) by exact_mod_cast hAY).trans hYz)
  have hupp := realLogCoordinate_mem_unit hz
    (show (1 : ℝ) ≤ (Y : ℝ) by exact_mod_cast (show 1 ≤ Y by omega)) hYz
  exact ⟨hlow.1.trans ht.1, ht.2.trans hupp.2⟩









lemma intervalIntegrable_div_of_continuous
    {f : ℝ → ℝ} (hf : Continuous f) {a b : ℝ} (ha : 0 < a)
    (hab : a ≤ b) :
    IntervalIntegrable (fun t => f t / t) volume a b := by
  apply ContinuousOn.intervalIntegrable_of_Icc hab
  intro t ht
  exact hf.continuousAt.div continuousAt_id
    (ne_of_gt (ha.trans_le ht.1)) |>.continuousWithinAt







/-! ## Moving-low input cell -/































end Erdos390.Full.DoubleKernelPrimeQuadrature

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

/- Source module: Erdos390.Full.DiagonalPrimeQuadrature -/
section


/-!
# Prime quadrature for the Poisson--Dickman diagonal multiplier

The compressed operator in Lemma 8.4 contains the multiplier `F(t)` in
addition to the double kernel.  This file proves its actual prime-cell
quadrature independently, including the normalization used on the moving
low output row.
-/

open Set

noncomputable section

namespace Erdos390.Full.DiagonalPrimeQuadrature

open MeasureTheory
open PrimeSums PrimeBandQuadrature
open DickmanBasic ConditionedPoissonLimit
open KernelPrimeQuadrature DoubleKernelPrimeQuadrature
open PositiveCellTransfer







lemma hasDerivAt_diagonalWeightedAbelCoefficient
    {z x : ℝ} (hz : 1 < z) (hx : 1 < x) (hxz : x ≤ z) :
    HasDerivAt (weightedAbelCoefficient F z)
      (diagonalWeightedAbelDerivative z x) x := by
  have ht := realLogCoordinate_mem_unit hz hx.le hxz
  have ht₂ : realLogCoordinate z x ∈ Icc (0 : ℝ) 2 :=
    ⟨ht.1, ht.2.trans (by norm_num)⟩
  have hF : HasDerivAt F
      (derivFExtension (realLogCoordinate z x)) (realLogCoordinate z x) := by
    exact (differentiableAt_F ht₂).hasDerivAt.congr_deriv
      (derivFExtension_eq_deriv_of_mem ht₂).symm
  exact hasDerivAt_weightedAbelCoefficient F derivFExtension hz hx hF

lemma deriv_diagonalWeightedAbelCoefficient
    {z x : ℝ} (hz : 1 < z) (hx : 1 < x) (hxz : x ≤ z) :
    deriv (weightedAbelCoefficient F z) x =
      diagonalWeightedAbelDerivative z x :=
  (hasDerivAt_diagonalWeightedAbelCoefficient hz hx hxz).deriv

lemma continuousAt_diagonalWeightedAbelDerivative
    {z x : ℝ} (hz : 1 < z) (hx : 1 < x) :
    ContinuousAt (diagonalWeightedAbelDerivative z) x := by
  exact continuousAt_weightedAbelCoefficientDerivative F derivFExtension
    continuous_F continuous_derivFExtension hz hx

lemma continuousOn_diagonalWeightedAbelDerivative
    {z A Y : ℝ} (hz : 1 < z) (hA : 1 < A) :
    ContinuousOn (diagonalWeightedAbelDerivative z) (Icc A Y) := by
  intro x hx
  exact (continuousAt_diagonalWeightedAbelDerivative hz
    (hA.trans_le hx.1)).continuousWithinAt

/-- One compact constant bounds the diagonal and its first derivative. -/
theorem exists_diagonal_uniform_C1_bound :
    ∃ M : ℝ, 0 < M ∧ ∀ t ∈ Icc (0 : ℝ) 1,
      |F t| ≤ M ∧ |derivFExtension t| ≤ M := by
  obtain ⟨M₀, hM₀⟩ := isCompact_Icc.exists_bound_of_continuousOn
    continuous_F.continuousOn
  obtain ⟨M₁, hM₁⟩ := isCompact_Icc.exists_bound_of_continuousOn
    continuous_derivFExtension.continuousOn
  have hzero : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := by norm_num
  have hM₀nonneg : 0 ≤ M₀ :=
    (norm_nonneg (F 0)).trans (hM₀ 0 hzero)
  have hM₁nonneg : 0 ≤ M₁ :=
    (norm_nonneg (derivFExtension 0)).trans (hM₁ 0 hzero)
  refine ⟨1 + M₀ + M₁, by linarith, ?_⟩
  intro t ht
  constructor
  · have h := hM₀ t ht
    rw [Real.norm_eq_abs] at h
    linarith
  · have h := hM₁ t ht
    rw [Real.norm_eq_abs] at h
    linarith

lemma abs_diagonalWeightedAbelCoefficient_le
    {M z x : ℝ} (hz : 1 < z) (hx : 1 < x) (hxz : x ≤ z)
    (hF : ∀ t ∈ Icc (0 : ℝ) 1, |F t| ≤ M) :
    |weightedAbelCoefficient F z x| ≤ M / (x * Real.log x) := by
  have ht := realLogCoordinate_mem_unit hz hx.le hxz
  have hxpos : 0 < x := zero_lt_one.trans hx
  have hlogxpos : 0 < Real.log x := Real.log_pos hx
  have hdenpos : 0 < x * Real.log x := mul_pos hxpos hlogxpos
  unfold weightedAbelCoefficient
  rw [abs_div, abs_of_pos hdenpos]
  exact div_le_div_of_nonneg_right (hF _ ht) hdenpos.le

lemma abs_diagonalWeightedAbelDerivative_le
    {M z x : ℝ} (hz : 1 < z) (hx : 1 < x) (hxz : x ≤ z)
    (hF : ∀ t ∈ Icc (0 : ℝ) 1,
      |F t| ≤ M ∧ |derivFExtension t| ≤ M) :
    |diagonalWeightedAbelDerivative z x| ≤
      M / (x ^ 2 * Real.log x * Real.log z) +
        M * (Real.log x + 1) / (x ^ 2 * Real.log x ^ 2) := by
  have ht := realLogCoordinate_mem_unit hz hx.le hxz
  have hxpos : 0 < x := zero_lt_one.trans hx
  have hlogxpos : 0 < Real.log x := Real.log_pos hx
  have hlogzpos : 0 < Real.log z := Real.log_pos hz
  have hden₁ : 0 < x ^ 2 * Real.log x * Real.log z := by positivity
  have hden₂ : 0 < x ^ 2 * Real.log x ^ 2 := by positivity
  have hplus : 0 ≤ Real.log x + 1 := by linarith
  unfold diagonalWeightedAbelDerivative weightedAbelCoefficientDerivative
  calc
    |derivFExtension (realLogCoordinate z x) /
          (x ^ 2 * Real.log x * Real.log z) -
        F (realLogCoordinate z x) * (Real.log x + 1) /
          (x ^ 2 * Real.log x ^ 2)| ≤
      |derivFExtension (realLogCoordinate z x) /
          (x ^ 2 * Real.log x * Real.log z)| +
        |F (realLogCoordinate z x) * (Real.log x + 1) /
          (x ^ 2 * Real.log x ^ 2)| := abs_sub _ _
    _ = |derivFExtension (realLogCoordinate z x)| /
          (x ^ 2 * Real.log x * Real.log z) +
        |F (realLogCoordinate z x)| * (Real.log x + 1) /
          (x ^ 2 * Real.log x ^ 2) := by
      rw [abs_div, abs_div]
      simp only [abs_mul]
      rw [abs_of_nonneg (sq_nonneg x), abs_of_pos hlogxpos,
        abs_of_pos hlogzpos, abs_of_nonneg hplus,
        abs_of_nonneg (sq_nonneg (Real.log x))]
    _ ≤ M / (x ^ 2 * Real.log x * Real.log z) +
        M * (Real.log x + 1) / (x ^ 2 * Real.log x ^ 2) := by
      apply add_le_add
      · exact div_le_div_of_nonneg_right (hF _ ht).2 hden₁.le
      · exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_right (hF _ ht).1 hplus) hden₂.le

lemma abs_diagonalWeightedAbelCoefficient_mul_thetaError_le
    {C M z x : ℝ} (hM : 0 ≤ M) (hz : 1 < z)
    (hx : 2 ≤ x) (hxz : x ≤ z)
    (hF : ∀ t ∈ Icc (0 : ℝ) 1, |F t| ≤ M)
    (hTheta : |thetaError x| ≤ C * x / Real.log x ^ 3) :
    |weightedAbelCoefficient F z x * thetaError x| ≤
      C * M / Real.log x ^ 4 := by
  have hx1 : 1 < x := by linarith
  have hxpos : 0 < x := by linarith
  have hlogpos : 0 < Real.log x := Real.log_pos hx1
  have hcoeff := abs_diagonalWeightedAbelCoefficient_le hz hx1 hxz hF
  rw [abs_mul]
  calc
    |weightedAbelCoefficient F z x| * |thetaError x| ≤
        (M / (x * Real.log x)) * (C * x / Real.log x ^ 3) := by gcongr
    _ = C * M / Real.log x ^ 4 := by
      field_simp [ne_of_gt hxpos, ne_of_gt hlogpos]

lemma abs_diagonalWeightedAbelDerivative_mul_thetaError_le
    {C M z x : ℝ} (hC : 0 ≤ C) (hM : 0 ≤ M)
    (hz : 1 < z) (hx : 2 ≤ x) (hxz : x ≤ z)
    (hF : ∀ t ∈ Icc (0 : ℝ) 1,
      |F t| ≤ M ∧ |derivFExtension t| ≤ M)
    (hTheta : |thetaError x| ≤ C * x / Real.log x ^ 3) :
    |diagonalWeightedAbelDerivative z x * thetaError x| ≤
      mertensErrorMajorant (2 * C * M) x := by
  have hx1 : 1 < x := by linarith
  have hxpos : 0 < x := by linarith
  have hloghalf : (1 / 2 : ℝ) ≤ Real.log x := by
    have hmono : Real.log 2 ≤ Real.log x :=
      Real.log_le_log (by norm_num) hx
    nlinarith [Real.log_two_gt_d9]
  have hlogpos : 0 < Real.log x := by linarith
  have hlogzpos : 0 < Real.log z := Real.log_pos hz
  have hlogxz : Real.log x ≤ Real.log z := Real.log_le_log hxpos hxz
  have hplus : Real.log x + 1 ≤ 3 * Real.log x := by linarith
  have hderiv := abs_diagonalWeightedAbelDerivative_le hz hx1 hxz hF
  have hsimplified :
      M / (x ^ 2 * Real.log x * Real.log z) +
          M * (Real.log x + 1) / (x ^ 2 * Real.log x ^ 2) ≤
        5 * M / (x ^ 2 * Real.log x) := by
    have hdenx : 0 < x ^ 2 := sq_pos_of_pos hxpos
    have hden₁ : 0 < x ^ 2 * Real.log x * Real.log z := by positivity
    have hden₂ : 0 < x ^ 2 * Real.log x ^ 2 := by positivity
    have hden₃ : 0 < x ^ 2 * Real.log x := by positivity
    have hfirst :
        M / (x ^ 2 * Real.log x * Real.log z) ≤
          M / (x ^ 2 * Real.log x ^ 2) := by
      apply (div_le_div_iff₀ hden₁ hden₂).2
      apply mul_le_mul_of_nonneg_left _ hM
      nlinarith [mul_pos hdenx hlogpos]
    have hsecond :
        M * (Real.log x + 1) / (x ^ 2 * Real.log x ^ 2) ≤
          3 * M / (x ^ 2 * Real.log x) := by
      calc
        M * (Real.log x + 1) / (x ^ 2 * Real.log x ^ 2) ≤
            M * (3 * Real.log x) / (x ^ 2 * Real.log x ^ 2) := by gcongr
        _ = 3 * M / (x ^ 2 * Real.log x) := by
          field_simp [ne_of_gt hlogpos]
    have hfirst' :
        M / (x ^ 2 * Real.log x ^ 2) ≤
          2 * M / (x ^ 2 * Real.log x) := by
      have hone : 1 ≤ 2 * Real.log x := by linarith
      apply (div_le_div_iff₀ hden₂ hden₃).2
      calc
        M * (x ^ 2 * Real.log x) ≤
            M * (x ^ 2 * Real.log x) * (2 * Real.log x) := by
          simpa only [mul_one] using
            (mul_le_mul_of_nonneg_left hone (mul_nonneg hM hden₃.le))
        _ = 2 * M * (x ^ 2 * Real.log x ^ 2) := by ring
    calc
      _ ≤ M / (x ^ 2 * Real.log x ^ 2) +
          3 * M / (x ^ 2 * Real.log x) := add_le_add hfirst hsecond
      _ ≤ 2 * M / (x ^ 2 * Real.log x) +
          3 * M / (x ^ 2 * Real.log x) := add_le_add hfirst' (le_refl _)
      _ = 5 * M / (x ^ 2 * Real.log x) := by ring
  rw [abs_mul]
  calc
    |diagonalWeightedAbelDerivative z x| * |thetaError x| ≤
        (5 * M / (x ^ 2 * Real.log x)) *
          (C * x / Real.log x ^ 3) := by
      apply mul_le_mul
      · exact hderiv.trans hsimplified
      · exact hTheta
      · positivity
      · have := abs_nonneg (diagonalWeightedAbelDerivative z x)
        positivity
    _ ≤ mertensErrorMajorant (2 * C * M) x := by
      unfold mertensErrorMajorant
      have hCM : 0 ≤ C * M := mul_nonneg hC hM
      field_simp [ne_of_gt hxpos, ne_of_gt hlogpos]
      nlinarith

lemma integrableOn_deriv_diagonalWeightedAbelCoefficient
    {z : ℝ} (hz : 1 < z) {Y : ℕ} (hYz : (Y : ℝ) ≤ z) :
    IntegrableOn (deriv (weightedAbelCoefficient F z))
      (Icc (2 : ℝ) (Y : ℝ)) := by
  have hcont : ContinuousOn (diagonalWeightedAbelDerivative z)
      (Icc (2 : ℝ) (Y : ℝ)) :=
    continuousOn_diagonalWeightedAbelDerivative hz (by norm_num)
  apply (hcont.integrableOn_Icc).congr_fun
  · intro x hx
    symm
    exact deriv_diagonalWeightedAbelCoefficient hz
      (by linarith [hx.1]) (hx.2.trans hYz)
  · exact measurableSet_Icc

lemma intervalIntegrable_deriv_diagonal_mul_theta
    {z : ℝ} (hz : 1 < z) {Y : ℕ} (hY : 2 ≤ Y) (hYz : (Y : ℝ) ≤ z) :
    IntervalIntegrable
      (fun x : ℝ => deriv (weightedAbelCoefficient F z) x * Chebyshev.theta x)
      volume (2 : ℝ) (Y : ℝ) := by
  have h2Y : (2 : ℝ) ≤ (Y : ℝ) := by exact_mod_cast hY
  have hbase := intervalIntegrable_continuous_mul_theta
    (g := diagonalWeightedAbelDerivative z) (A := (2 : ℝ))
    (Y := (Y : ℝ)) (by norm_num) h2Y
    (continuousOn_diagonalWeightedAbelDerivative hz (by norm_num))
  apply hbase.congr
  intro x hx
  have hx' : x ∈ Ioc (2 : ℝ) (Y : ℝ) := by
    simpa only [uIoc_of_le h2Y] using hx
  change diagonalWeightedAbelDerivative z x * Chebyshev.theta x =
    deriv (weightedAbelCoefficient F z) x * Chebyshev.theta x
  congr 1
  exact (deriv_diagonalWeightedAbelCoefficient hz
    (by linarith [hx'.1]) (hx'.2.trans hYz)).symm

lemma intervalIntegrable_deriv_diagonal_mul_id
    {z : ℝ} (hz : 1 < z) {A Y : ℕ} (hA : 2 ≤ A) (hAY : A ≤ Y)
    (hYz : (Y : ℝ) ≤ z) :
    IntervalIntegrable
      (fun x : ℝ => deriv (weightedAbelCoefficient F z) x * x)
      volume (A : ℝ) (Y : ℝ) := by
  have hAR : (2 : ℝ) ≤ (A : ℝ) := by exact_mod_cast hA
  have hAYR : (A : ℝ) ≤ (Y : ℝ) := by exact_mod_cast hAY
  have hcont : ContinuousOn
      (fun x : ℝ => diagonalWeightedAbelDerivative z x * x)
      (Icc (A : ℝ) (Y : ℝ)) :=
    (continuousOn_diagonalWeightedAbelDerivative hz (by linarith [hAR])).mul
      continuousOn_id
  have hbase := hcont.intervalIntegrable_of_Icc (μ := volume) hAYR
  apply hbase.congr
  intro x hx
  have hx' : x ∈ Ioc (A : ℝ) (Y : ℝ) := by
    simpa only [uIoc_of_le hAYR] using hx
  change diagonalWeightedAbelDerivative z x * x =
    deriv (weightedAbelCoefficient F z) x * x
  congr 1
  exact (deriv_diagonalWeightedAbelCoefficient hz
    (by linarith [hAR, hx'.1]) (hx'.2.trans hYz)).symm

/-- Exact actual diagonal cell minus continuum cell equals its literal PNT
remainder. -/
theorem diagonalPrimeCell_sub_continuum_eq_remainder
    {z : ℝ} (hz : 1 < z) {A Y : ℕ}
    (hA : 2 ≤ A) (hAY : A ≤ Y) (hYz : (Y : ℝ) ≤ z) :
    diagonalPrimeCell z A Y - diagonalContinuumCell z A Y =
      weightedAbelRemainder F z (A : ℝ) (Y : ℝ) := by
  have hY : 2 ≤ Y := hA.trans hAY
  have hAR : (2 : ℝ) ≤ (A : ℝ) := by exact_mod_cast hA
  have hAYR : (A : ℝ) ≤ (Y : ℝ) := by exact_mod_cast hAY
  have h2Y : (2 : ℝ) ≤ (Y : ℝ) := by exact_mod_cast hY
  have hdiff : ∀ x ∈ Icc (2 : ℝ) (Y : ℝ),
      DifferentiableAt ℝ (weightedAbelCoefficient F z) x := by
    intro x hx
    exact (hasDerivAt_diagonalWeightedAbelCoefficient hz
      (by linarith [hx.1]) (hx.2.trans hYz)).differentiableAt
  have hint := integrableOn_deriv_diagonalWeightedAbelCoefficient hz hYz
  have hThetaInt := intervalIntegrable_deriv_diagonal_mul_theta hz hY hYz
  have hMainInt := intervalIntegrable_deriv_diagonal_mul_id hz hA hAY hYz
  have hErrorInt : IntervalIntegrable
      (fun x : ℝ => deriv (weightedAbelCoefficient F z) x * thetaError x)
      volume (A : ℝ) (Y : ℝ) := by
    have hThetaCell : IntervalIntegrable
        (fun x : ℝ => deriv (weightedAbelCoefficient F z) x * Chebyshev.theta x)
        volume (A : ℝ) (Y : ℝ) := by
      apply hThetaInt.mono_set
      rw [uIcc_of_le hAYR, uIcc_of_le h2Y]
      intro x hx
      exact ⟨hAR.trans hx.1, hx.2⟩
    have hsub := hThetaCell.sub hMainInt
    apply hsub.congr
    intro x hx
    unfold thetaError
    ring
  have hdecomp := fullWeightedReciprocalSum_interval_sub_main_eq_remainder
    F z hA hAY hdiff hint hThetaInt hMainInt hErrorInt
  rw [weightedAbelMain_eq_logCoordinateIntegral F continuous_F
    hz hA hAY hdiff hint] at hdecomp
  exact hdecomp

theorem abs_diagonalWeightedAbelRemainder_le
    {C M z : ℝ} (hC : 0 ≤ C) (hM : 0 ≤ M) (hz : 1 < z)
    {A Y : ℕ} (hA : 2 ≤ A) (hAY : A ≤ Y) (hYz : (Y : ℝ) ≤ z)
    (hF : ∀ t ∈ Icc (0 : ℝ) 1,
      |F t| ≤ M ∧ |derivFExtension t| ≤ M)
    (hTheta : ∀ x ∈ Icc (A : ℝ) (Y : ℝ),
      |thetaError x| ≤ C * x / Real.log x ^ 3) :
    |weightedAbelRemainder F z (A : ℝ) (Y : ℝ)| ≤
      6 * (C * M) / Real.log (A : ℝ) ^ 3 := by
  have hY : 2 ≤ Y := hA.trans hAY
  have hAR : (2 : ℝ) ≤ (A : ℝ) := by exact_mod_cast hA
  have hAYR : (A : ℝ) ≤ (Y : ℝ) := by exact_mod_cast hAY
  have hApos : (0 : ℝ) < A := by positivity
  have hlogAhalf : (1 / 2 : ℝ) ≤ Real.log (A : ℝ) := by
    have hmono : Real.log 2 ≤ Real.log (A : ℝ) :=
      Real.log_le_log (by norm_num) hAR
    nlinarith [Real.log_two_gt_d9]
  have hlogApos : 0 < Real.log (A : ℝ) := by linarith
  have hlogYpos : 0 < Real.log (Y : ℝ) := by
    apply Real.log_pos
    exact_mod_cast (show 1 < Y by omega)
  have hlogAY : Real.log (A : ℝ) ≤ Real.log (Y : ℝ) :=
    Real.log_le_log hApos (by exact_mod_cast hAY)
  have hCM : 0 ≤ C * M := mul_nonneg hC hM
  have hThetaCell : IntervalIntegrable
      (fun x : ℝ => deriv (weightedAbelCoefficient F z) x * Chebyshev.theta x)
      volume (A : ℝ) (Y : ℝ) := by
    have hfull := intervalIntegrable_deriv_diagonal_mul_theta hz hY hYz
    apply hfull.mono_set
    rw [uIcc_of_le hAYR]
    have h2Y : (2 : ℝ) ≤ (Y : ℝ) := by exact_mod_cast hY
    rw [uIcc_of_le h2Y]
    intro x hx
    exact ⟨hAR.trans hx.1, hx.2⟩
  have hMainInt := intervalIntegrable_deriv_diagonal_mul_id hz hA hAY hYz
  have hErrorInt : IntervalIntegrable
      (fun x : ℝ => deriv (weightedAbelCoefficient F z) x * thetaError x)
      volume (A : ℝ) (Y : ℝ) := by
    have hsub := hThetaCell.sub hMainInt
    apply hsub.congr
    intro x hx
    unfold thetaError
    ring
  have hmajorInt : IntervalIntegrable (mertensErrorMajorant (2 * C * M))
      volume (A : ℝ) (Y : ℝ) :=
    ContinuousOn.intervalIntegrable_of_Icc hAYR
      (continuousOn_mertensErrorMajorant (2 * C * M)
        (A := (A : ℝ)) (Y := (Y : ℝ)) (by linarith [hAR]))
  have hIntBound :
      (∫ x in (A : ℝ)..Y,
          |deriv (weightedAbelCoefficient F z) x * thetaError x|) ≤
        2 * (C * M) / Real.log (A : ℝ) ^ 3 := by
    calc
      (∫ x in (A : ℝ)..Y,
          |deriv (weightedAbelCoefficient F z) x * thetaError x|) ≤
          ∫ x in (A : ℝ)..Y, mertensErrorMajorant (2 * C * M) x := by
        exact intervalIntegral.integral_mono_on hAYR hErrorInt.abs hmajorInt
          (fun x hx => by
            have hx2 : 2 ≤ x := hAR.trans hx.1
            have hxz : x ≤ z := hx.2.trans hYz
            rw [deriv_diagonalWeightedAbelCoefficient hz (by linarith) hxz]
            exact abs_diagonalWeightedAbelDerivative_mul_thetaError_le
              hC hM hz hx2 hxz hF (hTheta x hx))
      _ = mertensErrorPrimitive (2 * C * M) (Y : ℝ) -
          mertensErrorPrimitive (2 * C * M) (A : ℝ) :=
        integral_mertensErrorMajorant (2 * C * M) hAR hAYR
      _ ≤ 2 * (C * M) / Real.log (A : ℝ) ^ 3 := by
        unfold mertensErrorPrimitive
        have hnonneg : 0 ≤ 2 * (C * M) / Real.log (Y : ℝ) ^ 3 := by positivity
        have heq :
            -(2 * C * M) / Real.log (Y : ℝ) ^ 3 -
                (-(2 * C * M) / Real.log (A : ℝ) ^ 3) =
              2 * (C * M) / Real.log (A : ℝ) ^ 3 -
                2 * (C * M) / Real.log (Y : ℝ) ^ 3 := by ring
        rw [heq]
        exact sub_le_self _ hnonneg
  have hAterm :
      |weightedAbelCoefficient F z (A : ℝ)| * |thetaError (A : ℝ)| ≤
        C * M / Real.log (A : ℝ) ^ 4 := by
    rw [← abs_mul]
    exact abs_diagonalWeightedAbelCoefficient_mul_thetaError_le hM hz hAR
      ((show (A : ℝ) ≤ (Y : ℝ) by exact_mod_cast hAY).trans hYz)
      (fun t ht => (hF t ht).1) (hTheta (A : ℝ) ⟨le_rfl, hAYR⟩)
  have hYterm :
      |weightedAbelCoefficient F z (Y : ℝ)| * |thetaError (Y : ℝ)| ≤
        C * M / Real.log (A : ℝ) ^ 4 := by
    rw [← abs_mul]
    calc
      |weightedAbelCoefficient F z (Y : ℝ) * thetaError (Y : ℝ)| ≤
          C * M / Real.log (Y : ℝ) ^ 4 := by
        exact abs_diagonalWeightedAbelCoefficient_mul_thetaError_le hM hz
          (by exact_mod_cast hY) hYz (fun t ht => (hF t ht).1)
          (hTheta (Y : ℝ) ⟨hAYR, le_rfl⟩)
      _ ≤ C * M / Real.log (A : ℝ) ^ 4 := by gcongr
  have hinv4 : C * M / Real.log (A : ℝ) ^ 4 ≤
      2 * (C * M) / Real.log (A : ℝ) ^ 3 := by
    have hone : 1 ≤ 2 * Real.log (A : ℝ) := by linarith
    have hmul := mul_le_mul_of_nonneg_right hone
      (pow_nonneg hlogApos.le 3)
    have hinv : 1 / Real.log (A : ℝ) ^ 4 ≤
        2 / Real.log (A : ℝ) ^ 3 := by
      apply (div_le_div_iff₀ (pow_pos hlogApos 4) (pow_pos hlogApos 3)).2
      calc
        1 * Real.log (A : ℝ) ^ 3 ≤
            (2 * Real.log (A : ℝ)) * Real.log (A : ℝ) ^ 3 := hmul
        _ = 2 * Real.log (A : ℝ) ^ 4 := by ring
    calc
      C * M / Real.log (A : ℝ) ^ 4 =
          (C * M) * (1 / Real.log (A : ℝ) ^ 4) := by ring
      _ ≤ (C * M) * (2 / Real.log (A : ℝ) ^ 3) :=
        mul_le_mul_of_nonneg_left hinv hCM
      _ = 2 * (C * M) / Real.log (A : ℝ) ^ 3 := by ring
  calc
    |weightedAbelRemainder F z (A : ℝ) (Y : ℝ)| ≤
        |weightedAbelCoefficient F z (Y : ℝ)| * |thetaError (Y : ℝ)| +
          |weightedAbelCoefficient F z (A : ℝ)| * |thetaError (A : ℝ)| +
          ∫ x in (A : ℝ)..Y,
            |deriv (weightedAbelCoefficient F z) x * thetaError x| :=
      abs_weightedAbelRemainder_le F z hAYR
    _ ≤ C * M / Real.log (A : ℝ) ^ 4 +
        C * M / Real.log (A : ℝ) ^ 4 +
        2 * (C * M) / Real.log (A : ℝ) ^ 3 := by linarith
    _ ≤ 6 * (C * M) / Real.log (A : ℝ) ^ 3 := by
      calc
        _ ≤ 2 * (C * M) / Real.log (A : ℝ) ^ 3 +
            2 * (C * M) / Real.log (A : ℝ) ^ 3 +
            2 * (C * M) / Real.log (A : ℝ) ^ 3 := by
          exact add_le_add (add_le_add hinv4 hinv4) (le_refl _)
        _ = 6 * (C * M) / Real.log (A : ℝ) ^ 3 := by ring

/-- Unconditional diagonal prime-cell quadrature, uniform in all moving
positive endpoints. -/
theorem exists_uniform_diagonalPrimeCell_error_bound :
    ∃ D : ℝ, 0 < D ∧ ∃ X₀ : ℕ,
      ∀ z : ℝ, 1 < z → ∀ A Y : ℕ,
        X₀ ≤ A → A ≤ Y → (Y : ℝ) ≤ z →
        |diagonalPrimeCell z A Y - diagonalContinuumCell z A Y| ≤
          D / Real.log (A : ℝ) ^ 3 := by
  obtain ⟨C, hC, X₀R, hTheta⟩ := exists_thetaError_log_cube_bound
  obtain ⟨M, hM, hF⟩ := exists_diagonal_uniform_C1_bound
  obtain ⟨N, hX₀N⟩ := exists_nat_gt X₀R
  refine ⟨6 * (C * M), by positivity, max N 2, ?_⟩
  intro z hz A Y hA hAY hYz
  have hA2 : 2 ≤ A := (le_max_right N 2).trans hA
  have hNA : N ≤ A := (le_max_left N 2).trans hA
  have hNAR : (N : ℝ) ≤ (A : ℝ) := by exact_mod_cast hNA
  rw [diagonalPrimeCell_sub_continuum_eq_remainder hz hA2 hAY hYz]
  apply abs_diagonalWeightedAbelRemainder_le hC.le hM.le hz hA2 hAY hYz hF
  intro x hx
  apply hTheta x
  exact (le_of_lt hX₀N).trans (hNAR.trans hx.1)





lemma abs_diagonalContinuumCell_le_mass
    {M z : ℝ} (hz : 1 < z) {A Y : ℕ}
    (hA : 2 ≤ A) (hAY : A ≤ Y) (hYz : (Y : ℝ) ≤ z)
    (hF : ∀ t ∈ Icc (0 : ℝ) 1, |F t| ≤ M) :
    |diagonalContinuumCell z A Y| ≤ M * continuumCellMass z A Y := by
  have hint : IntervalIntegrable (fun t => F t / t) volume
      (realLogCoordinate z (A : ℝ)) (realLogCoordinate z (Y : ℝ)) :=
    intervalIntegrable_div_of_continuous continuous_F
      (realLogCoordinate_pos_nat hz hA)
      (realLogCoordinate_mono_nat hz hA hAY)
  unfold diagonalContinuumCell
  apply abs_continuumCellOperator_le z hz hA hAY F hint
  intro t ht
  exact hF t (coordinateCell_mem_unit hz hA hAY hYz ht)

theorem normalizedDiagonalCell_error_le
    {z : ℝ} {A Y : ℕ} {eNumerator eMass : ℝ}
    (hActualMass : 0 < actualCellMass A Y)
    (hContinuumMass : continuumCellMass z A Y ≠ 0)
    (hNumerator : |diagonalPrimeCell z A Y - diagonalContinuumCell z A Y| ≤
      eNumerator)
    (hMass : |actualCellMass A Y - continuumCellMass z A Y| ≤ eMass) :
    |normalizedDiagonalPrimeCell z A Y - normalizedDiagonalContinuumCell z A Y| ≤
      eNumerator / actualCellMass A Y +
        |diagonalContinuumCell z A Y| * eMass /
          (actualCellMass A Y * |continuumCellMass z A Y|) := by
  unfold normalizedDiagonalPrimeCell normalizedDiagonalContinuumCell
  exact abs_div_sub_div_le hActualMass hContinuumMass hNumerator hMass

/-- Unconditional relative diagonal transfer on the moving low output row.
The actual and continuum masses remain explicit denominators; hence a fixed
lower-cutoff error is absorbed as those masses grow. -/
theorem exists_uniform_normalizedDiagonalCell_error_bound :
    ∃ M : ℝ, 0 < M ∧ ∃ DDiag : ℝ, 0 < DDiag ∧
    ∃ CMass : ℝ, 0 < CMass ∧ ∃ X₀ : ℕ,
      ∀ z : ℝ, 1 < z → ∀ A Y : ℕ,
        X₀ ≤ A → A ≤ Y → (Y : ℝ) ≤ z →
        0 < actualCellMass A Y → continuumCellMass z A Y ≠ 0 →
        |normalizedDiagonalPrimeCell z A Y -
            normalizedDiagonalContinuumCell z A Y| ≤
          (DDiag / Real.log (A : ℝ) ^ 3) / actualCellMass A Y +
            (M * continuumCellMass z A Y) *
              (5 * CMass / Real.log (A : ℝ) ^ 3) /
              (actualCellMass A Y * |continuumCellMass z A Y|) := by
  obtain ⟨M, hM, hF⟩ := exists_diagonal_uniform_C1_bound
  obtain ⟨DDiag, hDDiag, XDiag, hDiag⟩ :=
    exists_uniform_diagonalPrimeCell_error_bound
  obtain ⟨CMass, hCMass, XMass, hMass⟩ :=
    exists_fullReciprocalSum_interval_error_bound
  refine ⟨M, hM, DDiag, hDDiag, CMass, hCMass,
    max (max XDiag XMass) 2, ?_⟩
  intro z hz A Y hA hAY hYz hActualMass hContinuumMass
  have hADiag : XDiag ≤ A :=
    (le_max_left XDiag XMass).trans
      ((le_max_left (max XDiag XMass) 2).trans hA)
  have hAMass : XMass ≤ A :=
    (le_max_right XDiag XMass).trans
      ((le_max_left (max XDiag XMass) 2).trans hA)
  have hAtwo : 2 ≤ A := (le_max_right (max XDiag XMass) 2).trans hA
  have hNum := hDiag z hz A Y hADiag hAY hYz
  have hMassRaw := hMass A Y hAMass hAY
  have hMassCoord :
      |actualCellMass A Y - continuumCellMass z A Y| ≤
        5 * CMass / Real.log (A : ℝ) ^ 3 := by
    unfold actualCellMass continuumCellMass
    rw [show Real.log (realLogCoordinate z (Y : ℝ)) -
        Real.log (realLogCoordinate z (A : ℝ)) =
      Real.log (Real.log (Y : ℝ)) - Real.log (Real.log (A : ℝ)) by
        simpa only [realLogCoordinate, logCoordinate] using
          log_logCoordinate_sub hz hAtwo hAY]
    exact hMassRaw
  have hCont := abs_diagonalContinuumCell_le_mass hz hAtwo hAY hYz
    (fun t ht => (hF t ht).1)
  have hratio := normalizedDiagonalCell_error_le hActualMass hContinuumMass
    hNum hMassCoord
  exact hratio.trans (add_le_add le_rfl
    (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right hCont
        (by positivity : 0 ≤ 5 * CMass / Real.log (A : ℝ) ^ 3))
      (mul_nonneg hActualMass.le (abs_nonneg _))))

end Erdos390.Full.DiagonalPrimeQuadrature

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











end Mesh
end Erdos390.Full.RegularMeshPrimeCutoffs

end

/- Source module: Erdos390.Full.CanonicalEndpointDiagonalEventually -/
section


/-!
# Canonical endpoint convergence of the diagonal multiplier

The normalized diagonal PNT estimate contains the actual output-cell mass
in its denominator.  This file proves that the denominator has the required
limit on every literal canonical cell: it diverges on the moving low cell
and tends to a positive constant on every positive cell.  Thus no
``mass is large'' hypothesis remains in the final diagonal statement.
-/

open Filter Topology

noncomputable section

namespace Erdos390.Full.RegularMeshPrimeCutoffs

open ArithmeticModel RegularRelativeMesh PrimeBandQuadrature
open DiagonalPrimeQuadrature DoubleKernelPrimeQuadrature
open KernelPrimeQuadrature

namespace Mesh

variable {delta eta : ℝ} (M : Mesh delta eta)







theorem endpointContinuumMass_eq_doubleKernelMass
    {n W : ℕ} (hn : 1 < n) (j : Fin (M.cellCount + 1))
    (hLowerTwo : 2 ≤ fullCutoff M n W j.1)
    (hMono : fullCutoff M n W j.1 ≤
      fullCutoff M n W (j.1 + 1)) :
    endpointContinuumMass M n W j =
      continuumCellMass (y n) (fullCutoff M n W j.1)
        (fullCutoff M n W (j.1 + 1)) := by
  have hy : 1 < y n := by
    have hlog : 0 < Real.log (y n) := by
      rw [Scale.log_y (Nat.zero_lt_of_lt hn)]
      exact mul_pos (by norm_num) (Real.log_pos (by exact_mod_cast hn))
    exact (Real.log_pos_iff (Scale.y_pos
      (Nat.zero_lt_of_lt hn)).le).mp hlog
  unfold endpointContinuumMass continuumCellMass
  have h := log_logCoordinate_sub hy hLowerTwo hMono
  simpa only [PrimeBandQuadrature.logCoordinate,
    realLogCoordinate] using h.symm

theorem tendsto_positive_endpointActualMass
    (hdelta : 0 < delta) (W : ℕ) (C : ℝ) (X : ℕ)
    (hMass : ∀ A Y : ℕ, X ≤ A → A ≤ Y →
      |PrimeSums.fullReciprocalSum Y - PrimeSums.fullReciprocalSum A -
        (Real.log (Real.log (Y : ℝ)) -
          Real.log (Real.log (A : ℝ)))| ≤
        5 * C / Real.log (A : ℝ) ^ 3)
    (k : Fin M.cellCount) :
    Tendsto (fun n : ℕ ↦
      endpointActualMass M n W (positiveBand M k)) atTop
      (nhds (Real.log (M.upper k) - Real.log (M.lower k))) := by
  have hCont := tendsto_positive_endpointContinuumMass M hdelta W k
  have hErr := tendsto_positive_endpointMassError_zero M hdelta C W k
  have hThreshold := eventually_threshold_le_nonlow_fullCutoff M hdelta W X
    (positiveBand M k) (by
      intro h
      have hv := congrArg Fin.val h
      simp only [positiveBand, lowBand, Fin.val_mk] at hv
      omega)
  have hSep := eventually_scaleSeparation M hdelta W
  have hDiff : Tendsto (fun n : ℕ ↦
      endpointActualMass M n W (positiveBand M k) -
        endpointContinuumMass M n W (positiveBand M k))
      atTop (nhds 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have hAbs : ∀ᶠ n : ℕ in atTop,
        |endpointActualMass M n W (positiveBand M k) -
          endpointContinuumMass M n W (positiveBand M k)| ≤
            endpointMassError M C n W (positiveBand M k) := by
      filter_upwards [eventually_gt_atTop 1, hThreshold, hSep] with
        n hn hX S
      have hmono := fullCutoff_monotone M hdelta hn
        (W_le_first_fullCutoff M S) (by omega : k.1 + 1 ≤ k.1 + 2)
      have hq := hMass (fullCutoff M n W (k.1 + 1))
        (fullCutoff M n W (k.1 + 2)) hX hmono
      simpa only [endpointActualMass, endpointContinuumMass,
        endpointMassError, positiveBand] using hq
    have hsqueeze := squeeze_zero'
      (Filter.Eventually.of_forall (fun n : ℕ => abs_nonneg
        (endpointActualMass M n W (positiveBand M k) -
          endpointContinuumMass M n W (positiveBand M k))))
      hAbs hErr
    simpa only [Real.norm_eq_abs] using hsqueeze
  have hsum := hDiff.add hCont
  simpa only [sub_add_cancel, zero_add] using hsum

theorem tendsto_low_endpointActualMass_atTop
    (hdelta : 0 < delta) {W X : ℕ} (hXW : X ≤ W)
    (C : ℝ)
    (hMass : ∀ A Y : ℕ, X ≤ A → A ≤ Y →
      |PrimeSums.fullReciprocalSum Y - PrimeSums.fullReciprocalSum A -
        (Real.log (Real.log (Y : ℝ)) -
          Real.log (Real.log (A : ℝ)))| ≤
        5 * C / Real.log (A : ℝ) ^ 3) :
    Tendsto (fun n : ℕ ↦ endpointActualMass M n W (lowBand M))
      atTop atTop := by
  have hCont := tendsto_low_endpointContinuumMass_atTop M hdelta W
  rw [tendsto_atTop]
  intro b
  let E₀ := 5 * C / Real.log (W : ℝ) ^ 3
  have hLarge := hCont.eventually (eventually_ge_atTop (b + E₀))
  have hSep := eventually_scaleSeparation M hdelta W
  filter_upwards [eventually_gt_atTop 1, hLarge, hSep] with n hn hlarge S
  have hmono := fullCutoff_monotone M hdelta hn
    (W_le_first_fullCutoff M S) (by omega : 0 ≤ 1)
  have hq := hMass W (fullCutoff M n W 1) hXW (by
    simpa only [fullCutoff_zero] using hmono)
  have hleft := (abs_le.mp hq).1
  have hLower :
      endpointContinuumMass M n W (lowBand M) - E₀ ≤
        endpointActualMass M n W (lowBand M) := by
    change -(5 * C / Real.log (W : ℝ) ^ 3) ≤
      endpointActualMass M n W (lowBand M) -
        endpointContinuumMass M n W (lowBand M) at hleft
    linarith
  linarith

/-- The actual canonical normalized diagonal converges uniformly over the
finite band set.  The PNT constants and cutoff threshold are chosen before
the requested accuracy and before `n`. -/
theorem exists_global_cutoff_eventually_canonical_diagonalError :
    ∃ W₀ : ℕ,
      ∀ {delta eta : ℝ} (M : Mesh delta eta), 0 < delta →
      ∀ W : ℕ, W₀ ≤ W → ∀ e : ℝ, 0 < e →
        ∀ᶠ n : ℕ in atTop,
          ∀ j : Fin (M.cellCount + 1), endpointDiagonalError M n W j ≤ e := by
  obtain ⟨Mdiag, hMdiag, Ddiag, hDdiag, Cdiag, hCdiag,
    Xdiag, hDiag⟩ := exists_uniform_normalizedDiagonalCell_error_bound
  obtain ⟨Cmass, hCmass, Xmass, hMass⟩ :=
    exists_fullReciprocalSum_interval_error_bound
  let W₀ := max 2 (max Xdiag Xmass)
  refine ⟨W₀, ?_⟩
  intro delta eta M hdelta W hW e he
  have hW2 : 2 ≤ W := (le_max_left 2 (max Xdiag Xmass)).trans hW
  have hXdiag : Xdiag ≤ W :=
    ((le_max_left Xdiag Xmass).trans
      (le_max_right 2 (max Xdiag Xmass))).trans hW
  have hXmass : Xmass ≤ W :=
    ((le_max_right Xdiag Xmass).trans
      (le_max_right 2 (max Xdiag Xmass))).trans hW
  have hLowActual := tendsto_low_endpointActualMass_atTop M hdelta
    hXmass Cmass hMass
  have hLowCont := tendsto_low_endpointContinuumMass_atTop M hdelta W
  have hLowBound : Tendsto (fun n : ℕ ↦
      (Ddiag / Real.log (W : ℝ) ^ 3) /
          endpointActualMass M n W (lowBand M) +
        (Mdiag * endpointContinuumMass M n W (lowBand M)) *
          (5 * Cdiag / Real.log (W : ℝ) ^ 3) /
          (endpointActualMass M n W (lowBand M) *
            |endpointContinuumMass M n W (lowBand M)|))
      atTop (nhds 0) := by
    have hFirstNum : Tendsto (fun _n : ℕ ↦
        Ddiag / Real.log (W : ℝ) ^ 3) atTop
        (nhds (Ddiag / Real.log (W : ℝ) ^ 3)) := tendsto_const_nhds
    have hFirst := hFirstNum.div_atTop hLowActual
    have hSecondNum : Tendsto (fun _n : ℕ ↦
        Mdiag * (5 * Cdiag / Real.log (W : ℝ) ^ 3)) atTop
        (nhds (Mdiag * (5 * Cdiag / Real.log (W : ℝ) ^ 3))) :=
      tendsto_const_nhds
    have hSecondSimple := hSecondNum.div_atTop hLowActual
    have hContPos := hLowCont.eventually (eventually_gt_atTop 0)
    have hSecond : Tendsto (fun n : ℕ ↦
        (Mdiag * endpointContinuumMass M n W (lowBand M)) *
          (5 * Cdiag / Real.log (W : ℝ) ^ 3) /
          (endpointActualMass M n W (lowBand M) *
            |endpointContinuumMass M n W (lowBand M)|))
        atTop (nhds 0) := by
      have hSimple : Tendsto (fun n : ℕ ↦
          (Mdiag * (5 * Cdiag / Real.log (W : ℝ) ^ 3)) /
            endpointActualMass M n W (lowBand M)) atTop (nhds 0) := by
        simpa using hSecondSimple
      apply hSimple.congr'
      filter_upwards [hContPos] with n hc
      rw [abs_of_pos hc]
      field_simp [ne_of_gt hc]
    simpa only [zero_add] using hFirst.add hSecond
  have hLowSmall := hLowBound.eventually (eventually_le_nhds he)
  have hPositiveSmall : ∀ᶠ n : ℕ in atTop,
      ∀ k : Fin M.cellCount,
      let A := fullCutoff M n W (k.1 + 1)
      let Y := fullCutoff M n W (k.1 + 2)
      ((Ddiag / Real.log (A : ℝ) ^ 3) /
          endpointActualMass M n W (positiveBand M k) +
        (Mdiag * endpointContinuumMass M n W (positiveBand M k)) *
          (5 * Cdiag / Real.log (A : ℝ) ^ 3) /
          (endpointActualMass M n W (positiveBand M k) *
            |endpointContinuumMass M n W (positiveBand M k)|)) ≤ e := by
    rw [Filter.eventually_all]
    intro k
    have hActual := tendsto_positive_endpointActualMass M hdelta W
      Cmass Xmass hMass k
    have hCont := tendsto_positive_endpointContinuumMass M hdelta W k
    have hAReal : Tendsto (fun n : ℕ ↦
        (fullCutoff M n W (k.1 + 1) : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop.comp
        (tendsto_general_positive_lowerCutoff_atTop M hdelta W k)
    have hLog := Real.tendsto_log_atTop.comp hAReal
    have hInvCube := (tendsto_inv_atTop_zero.comp hLog).pow 3
    let Hk := Real.log (M.upper k) - Real.log (M.lower k)
    have hHk : 0 < Hk := sub_pos.mpr
      (Real.strictMonoOn_log (M.lower_pos hdelta k)
        ((M.lower_pos hdelta k).trans (M.lower_lt_upper hdelta k))
        (M.lower_lt_upper hdelta k))
    have hActual0 : Hk ≠ 0 := ne_of_gt hHk
    have hCont0 : Hk ≠ 0 := ne_of_gt hHk
    have hFirst : Tendsto (fun n : ℕ ↦
        (Ddiag / Real.log (fullCutoff M n W (k.1 + 1) : ℝ) ^ 3) /
          endpointActualMass M n W (positiveBand M k))
        atTop (nhds 0) := by
      have hD : Tendsto (fun _n : ℕ ↦ Ddiag) atTop (nhds Ddiag) :=
        tendsto_const_nhds
      have hNum := hD.mul hInvCube
      have hDiv := hNum.div hActual hActual0
      have hDivZero : Tendsto (fun n : ℕ ↦
          (Ddiag *
            (Real.log (fullCutoff M n W (k.1 + 1) : ℝ))⁻¹ ^ 3) /
              endpointActualMass M n W (positiveBand M k))
          atTop (nhds 0) := by simpa using hDiv
      apply hDivZero.congr'
      filter_upwards with n
      rw [inv_pow]
      ring
    have hSecond : Tendsto (fun n : ℕ ↦
        (Mdiag * endpointContinuumMass M n W (positiveBand M k)) *
          (5 * Cdiag /
            Real.log (fullCutoff M n W (k.1 + 1) : ℝ) ^ 3) /
          (endpointActualMass M n W (positiveBand M k) *
            |endpointContinuumMass M n W (positiveBand M k)|))
        atTop (nhds 0) := by
      have hM : Tendsto (fun _n : ℕ ↦ Mdiag) atTop (nhds Mdiag) :=
        tendsto_const_nhds
      have hFiveC : Tendsto (fun _n : ℕ ↦ 5 * Cdiag) atTop
          (nhds (5 * Cdiag)) := tendsto_const_nhds
      have hNum := (hM.mul hCont).mul (hFiveC.mul hInvCube)
      have hAbs := hCont.abs
      have hDen := hActual.mul hAbs
      have hDen0 : Hk * |Hk| ≠ 0 :=
        mul_ne_zero hActual0 (abs_ne_zero.mpr hCont0)
      have hDiv := hNum.div hDen hDen0
      have hDivZero : Tendsto (fun n : ℕ ↦
          (Mdiag * endpointContinuumMass M n W (positiveBand M k) *
            (5 * Cdiag *
              (Real.log (fullCutoff M n W (k.1 + 1) : ℝ))⁻¹ ^ 3)) /
            (endpointActualMass M n W (positiveBand M k) *
              |endpointContinuumMass M n W (positiveBand M k)|))
          atTop (nhds 0) := by simpa using hDiv
      apply hDivZero.congr'
      filter_upwards with n
      rw [inv_pow]
      ring
    have hSum := hFirst.add hSecond
    exact hSum.eventually (eventually_le_nhds (by simpa using he))
  have hSep := eventually_scaleSeparation M hdelta W
  have hThreshold : ∀ᶠ n : ℕ in atTop,
      ∀ j : Fin (M.cellCount + 1), Xdiag ≤ fullCutoff M n W j.1 := by
    rw [Filter.eventually_all]
    intro j
    by_cases hj : j = lowBand M
    · subst j
      exact Filter.Eventually.of_forall (fun _n ↦ by
        simpa only [lowBand, fullCutoff_zero] using hXdiag)
    · exact eventually_threshold_le_nonlow_fullCutoff M hdelta W Xdiag j hj
  filter_upwards [eventually_gt_atTop 1, hSep, hLowSmall,
    hPositiveSmall, hThreshold] with n hn S hLow hPos hX
  intro j
  have hmono := fullCutoff_monotone M hdelta hn
    (W_le_first_fullCutoff M S) (Nat.le_succ j.1)
  have hY : (fullCutoff M n W (j.1 + 1) : ℝ) ≤ y n := by
    have hNat : fullCutoff M n W (j.1 + 1) ≤ yNat n := by
      rw [← fullCutoff_last M (Nat.zero_lt_of_lt hn)]
      exact fullCutoff_monotone M hdelta hn (W_le_first_fullCutoff M S)
        (by omega)
    exact (by exact_mod_cast hNat :
      (fullCutoff M n W (j.1 + 1) : ℝ) ≤ (yNat n : ℝ)) |>.trans
        (Nat.floor_le (Scale.y_pos (Nat.zero_lt_of_lt hn)).le)
  have hActualPos : 0 < endpointActualMass M n W j := by
    let P := canonicalPartition M hdelta hn (by omega : W ≠ 0) S
    let E := canonicalCertificate M hdelta hn (by omega : W ≠ 0) S
    have hp := P.data.mass_pos j
    have hEq : P.mass j = endpointActualMass M n W j := by
      rw [E.mass_eq_fullReciprocalSum_sub]
      rfl
    rw [← hEq]
    exact hp
  have hContPos : 0 < endpointContinuumMass M n W j := by
    obtain ⟨p, hpPrime, hpLower, hpUpper⟩ :=
      every_fullCutoff_cell_has_prime M (by omega : W ≠ 0) S j
    have hCutLt : fullCutoff M n W j.1 <
        fullCutoff M n W (j.1 + 1) := hpLower.trans_le hpUpper
    have hLowerTwo : 2 ≤ fullCutoff M n W j.1 :=
      hW2.trans (fullCutoff_monotone M hdelta hn
        (W_le_first_fullCutoff M S) (Nat.zero_le j.1))
    have hLowerPos : (0 : ℝ) < (fullCutoff M n W j.1 : ℝ) := by
      positivity
    have hUpperPos : (0 : ℝ) <
        (fullCutoff M n W (j.1 + 1) : ℝ) :=
      hLowerPos.trans (by exact_mod_cast hCutLt)
    have hLogLowerPos : 0 < Real.log (fullCutoff M n W j.1 : ℝ) :=
      Real.log_pos (by exact_mod_cast (show 1 < fullCutoff M n W j.1 by
        omega))
    have hLogUpperPos : 0 <
        Real.log (fullCutoff M n W (j.1 + 1) : ℝ) :=
      hLogLowerPos.trans (Real.strictMonoOn_log hLowerPos hUpperPos
        (by exact_mod_cast hCutLt))
    unfold endpointContinuumMass
    exact sub_pos.mpr (Real.strictMonoOn_log hLogLowerPos hLogUpperPos
      (Real.strictMonoOn_log hLowerPos hUpperPos
        (by exact_mod_cast hCutLt)))
  have hraw := hDiag (y n) (by
      have hlog : 0 < Real.log (y n) := by
        rw [Scale.log_y (Nat.zero_lt_of_lt hn)]
        exact mul_pos (by norm_num) (Real.log_pos (by exact_mod_cast hn))
      exact (Real.log_pos_iff (Scale.y_pos
        (Nat.zero_lt_of_lt hn)).le).mp hlog)
    (fullCutoff M n W j.1) (fullCutoff M n W (j.1 + 1))
    (hX j) hmono hY hActualPos
    (by
      rw [← endpointContinuumMass_eq_doubleKernelMass M hn j
        (hW2.trans (fullCutoff_monotone M hdelta hn
          (W_le_first_fullCutoff M S) (Nat.zero_le j.1))) hmono]
      exact ne_of_gt hContPos)
  unfold endpointDiagonalError
  apply hraw.trans
  rw [← endpointContinuumMass_eq_doubleKernelMass M hn j
      (hW2.trans (fullCutoff_monotone M hdelta hn
        (W_le_first_fullCutoff M S) (Nat.zero_le j.1))) hmono]
  change _ ≤ e
  refine Fin.cases ?_ (fun k ↦ ?_) j
  · simpa only [lowBand, Fin.val_mk, fullCutoff_zero] using hLow
  · simpa only [positiveBand] using hPos k



end Mesh
end Erdos390.Full.RegularMeshPrimeCutoffs

end

theorem solution :
∃ W₀,
  ∀ {delta eta : Real} (M : Erdos390.Full.RegularRelativeMesh.Mesh delta eta),
    LT.lt.{0} (0 : Real) delta →
      ∀ (W : Nat),
        LE.le.{0} W₀ W →
          ∀ (e : Real),
            LT.lt.{0} (0 : Real) e →
              ∀ᶠ (n : Nat) in Filter.atTop.{0},
                ∀ (j : Fin (HAdd.hAdd.{0, 0, 0} (Erdos390.Full.RegularRelativeMesh.Mesh.cellCount M) (1 : Nat))),
                  LE.le.{0} (Erdos390.Full.RegularMeshPrimeCutoffs.Mesh.endpointDiagonalError M n W j) e := by
  exact @Erdos390.Full.RegularMeshPrimeCutoffs.Mesh.exists_global_cutoff_eventually_canonical_diagonalError
