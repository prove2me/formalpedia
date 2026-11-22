-- Prove2me | solution 1 for Erdos390.Full.RegularMeshPrimeCutoffs.Mesh.canonicalPaperGeometricCutoff_eventually
-- status  : ACCEPTED   (prove)
-- author  : @doctosil
-- created : 2026-09-17T16:13:13.6793+00:00
-- url     : https://prove2.me/submissions/1247dd13-8ece-44f1-b88c-fd843299285a

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
import Theorems.Thm_Erdos390_Full_RegularMeshPrimeCutoffs_Mesh_canonicalPrimeAnchorCutoff_eventually
import Theorems.Thm_Erdos390_Full_RegularMeshPrimeCutoffs_Mesh_momentReady_of_endpointMomentBounds

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

/- Source module: Erdos390.Full.PaperPrimePowerRow -/
section


/-!
# The paper prime-band row contraction

This module specializes the actual finite-law contraction to

* the literal band `primeBand n W`,
* `t_p = log p / log y`,
* reciprocal weight `u_p = 1 / p`,
* row normalization `p`, and
* `invW = 1 / W`.

Thus every elementary prime-coordinate and prime-sum input in the final row
step of paper Lemma 7.5 is discharged here.  The remaining hypotheses are
exactly the actual `JI`, `IJ`, `JJ`, diagonal, and endpoint estimates proved
by the marked four-chamber analysis.
-/

open scoped BigOperators

namespace Erdos390.Full.PaperPrimePowerRow

open ArithmeticModel Scale PrimeSums
open PrimePowerCovariance PrimePowerRowTransfer

noncomputable section

lemma tPrime_nonneg_of_mem_primeBand
    {n W p : Nat} (hn : 1 < n) (hp : p ∈ primeBand n W) :
    0 <= tPrime n p := by
  have hL : 0 < L n := L_pos hn
  have hlogy : 0 < Real.log (y n) := by
    rw [log_y (Nat.zero_lt_of_lt hn)]
    nlinarith
  have hlogp : 0 <= Real.log (p : Real) :=
    Real.log_nonneg (by exact_mod_cast (prime_of_mem_primeBand hp).one_le)
  exact div_nonneg hlogp hlogy.le

lemma tPrime_le_one_of_mem_primeBand
    {n W p : Nat} (hn : 1 < n) (hp : p ∈ primeBand n W) :
    tPrime n p <= 1 := by
  have hn0 : 0 < n := Nat.zero_lt_of_lt hn
  have hL : 0 < L n := L_pos hn
  have hlogy : 0 < Real.log (y n) := by
    rw [log_y hn0]
    nlinarith
  have hpPrime := prime_of_mem_primeBand hp
  have hp0 : 0 < (p : Real) := by exact_mod_cast hpPrime.pos
  have hyfloor : (yNat n : Real) <= y n :=
    Nat.floor_le (le_of_lt (y_pos hn0))
  have hpcast : (p : Real) <= y n := by
    exact (by exact_mod_cast le_yNat_of_mem_primeBand hp :
      (p : Real) <= (yNat n : Real)).trans hyfloor
  have hlog : Real.log (p : Real) <= Real.log (y n) :=
    Real.log_le_log hp0 hpcast
  unfold tPrime
  calc
    Real.log (p : Real) / Real.log (y n) <=
        Real.log (y n) / Real.log (y n) :=
      div_le_div_of_nonneg_right hlog hlogy.le
    _ = 1 := div_self hlogy.ne'





namespace BoundedValuationLaw

variable {Omega : Type*} [Fintype Omega] {M : Nat}
  (law : BoundedValuationLaw Omega M)

set_option maxHeartbeats 800000



end BoundedValuationLaw

end


end Erdos390.Full.PaperPrimePowerRow

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

omit [DecidableEq Band] in
lemma cellLogReciprocalSum_eq_sub (j : Band) :
    (∑ p ∈ E.cellPrimes j, Real.log (p : ℝ) / (p : ℝ)) =
      fullLogReciprocalSum (E.upper j) -
        fullLogReciprocalSum (E.lower j) := by
  have hsub := primesUpTo_mono (E.lower_le_upper j)
  have hsum := Finset.sum_sdiff hsub
    (f := fun p : ℕ => Real.log (p : ℝ) / (p : ℝ))
  change (∑ p ∈ primesUpTo (E.upper j) \ primesUpTo (E.lower j),
      Real.log (p : ℝ) / (p : ℝ)) =
    (∑ p ∈ primesUpTo (E.upper j),
      Real.log (p : ℝ) / (p : ℝ)) -
      ∑ p ∈ primesUpTo (E.lower j),
        Real.log (p : ℝ) / (p : ℝ)
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

lemma fiber_logReciprocalSum_eq_cell (j : Band) :
    (∑ p ∈ P.data.fiber j,
      Real.log (p.1 : ℝ) / (p.1 : ℝ)) =
      ∑ q ∈ E.cellPrimes j, Real.log (q : ℝ) / (q : ℝ) := by
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

private lemma mass_mul_center_eq_weightedCoordSum (j : Band) :
    P.mass j * P.center j =
      ∑ p ∈ P.data.fiber j,
        (1 / (p.1 : ℝ)) * tPrime n p.1 := by
  change P.data.mass j *
      ((∑ p ∈ P.data.fiber j,
        (1 / (p.1 : ℝ)) * tPrime n p.1) / P.data.mass j) = _
  field_simp [ne_of_gt (P.data.mass_pos j)]

/-- Exact arithmetic identification of the centered first cell moment. -/
theorem mass_mul_center_eq_fullLogReciprocalSum_sub (j : Band) :
    P.mass j * P.center j =
      (fullLogReciprocalSum (E.upper j) -
        fullLogReciprocalSum (E.lower j)) / Real.log (y n) := by
  rw [mass_mul_center_eq_weightedCoordSum (P := P)]
  change (∑ p ∈ P.data.fiber j,
      (1 / (p.1 : ℝ)) *
        (Real.log (p.1 : ℝ) / Real.log (y n))) = _
  calc
    (∑ p ∈ P.data.fiber j,
        (1 / (p.1 : ℝ)) *
          (Real.log (p.1 : ℝ) / Real.log (y n))) =
        (∑ p ∈ P.data.fiber j,
          Real.log (p.1 : ℝ) / (p.1 : ℝ)) /
            Real.log (y n) := by
              rw [Finset.sum_div]
              apply Finset.sum_congr rfl
              intro p hp
              ring
    _ = (∑ q ∈ E.cellPrimes j,
          Real.log (q : ℝ) / (q : ℝ)) /
            Real.log (y n) := by rw [E.fiber_logReciprocalSum_eq_cell]
    _ = _ := by rw [E.cellLogReciprocalSum_eq_sub]









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

theorem variance_eq_sum_bandVariance :
    P.variance = ∑ j : Band, P.bandVariance j := by
  change (∑ p : BandPrime n W,
      (1 / (p.1 : ℝ)) * P.data.cellDeviation p *
        P.data.cellDeviation p) = _
  rw [← Finset.sum_fiberwise Finset.univ P.band
    (fun p : BandPrime n W ↦
      (1 / (p.1 : ℝ)) * P.data.cellDeviation p *
        P.data.cellDeviation p)]
  apply Finset.sum_congr rfl
  intro j hj
  unfold bandVariance deviation
  apply Finset.sum_congr rfl
  intro p hp
  simp only [Erdos390.Lemma84.WeightedBandData.cellDeviation]
  change (1 / (p.1 : ℝ)) *
      (P.center (P.band p) - tPrime n p.1) *
        (P.center (P.band p) - tPrime n p.1) =
    (1 / (p.1 : ℝ)) * (P.center (P.band p) - tPrime n p.1) ^ 2
  rw [pow_two]
  ring

theorem bandVariance_eq_second_sub_mass_center_sq (j : Band) :
    P.bandVariance j =
      P.bandSecondMoment j - P.mass j * P.center j ^ 2 := by
  have hrewrite : P.bandVariance j =
      ∑ p ∈ P.data.fiber j, (1 / (p.1 : ℝ)) *
        (P.center j - tPrime n p.1) ^ 2 := by
    unfold bandVariance deviation
    apply Finset.sum_congr rfl
    intro p hp
    have hpj : P.band p = j :=
      (Erdos390.Lemma84.WeightedBandData.mem_fiber_iff P.data).mp hp
    rw [hpj]
  rw [hrewrite]
  have hmass : (∑ p ∈ P.data.fiber j, 1 / (p.1 : ℝ)) = P.mass j := rfl
  have hfirst :
      (∑ p ∈ P.data.fiber j,
        (1 / (p.1 : ℝ)) * tPrime n p.1) = P.mass j * P.center j := by
    change (∑ p ∈ P.data.fiber j,
        (1 / (p.1 : ℝ)) * tPrime n p.1) =
      P.data.mass j *
        ((∑ p ∈ P.data.fiber j,
          (1 / (p.1 : ℝ)) * tPrime n p.1) / P.data.mass j)
    field_simp [ne_of_gt (P.data.mass_pos j)]
  calc
    (∑ p ∈ P.data.fiber j,
        (1 / (p.1 : ℝ)) * (P.center j - tPrime n p.1) ^ 2) =
        ∑ p ∈ P.data.fiber j,
          ((1 / (p.1 : ℝ)) * P.center j ^ 2 -
            2 * P.center j * ((1 / (p.1 : ℝ)) * tPrime n p.1) +
            (1 / (p.1 : ℝ)) * tPrime n p.1 ^ 2) := by
      apply Finset.sum_congr rfl
      intro p hp
      ring
    _ = (∑ p ∈ P.data.fiber j, 1 / (p.1 : ℝ)) * P.center j ^ 2 -
        2 * P.center j *
          (∑ p ∈ P.data.fiber j, (1 / (p.1 : ℝ)) * tPrime n p.1) +
        ∑ p ∈ P.data.fiber j, (1 / (p.1 : ℝ)) * tPrime n p.1 ^ 2 := by
      rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
        ← Finset.sum_mul, ← Finset.mul_sum]
    _ = P.bandSecondMoment j - P.mass j * P.center j ^ 2 := by
      rw [hmass, hfirst]
      unfold bandSecondMoment
      ring

/-- Reindex the actual square-coordinate moment from a certified band to its
natural prime interval. -/
theorem bandSecondMoment_eq_cellPrimeSum
    (E : IntervalCertificate P) (j : Band) :
    P.bandSecondMoment j =
      ∑ q ∈ E.cellPrimes j,
        squareCoordinate (realLogCoordinate (y n) (q : ℝ)) / (q : ℝ) := by
  unfold bandSecondMoment
  apply Finset.sum_bij (fun p _hp ↦ p.1)
  · intro p hp
    have hpBand : P.band p = j := by
      simpa only [Erdos390.Lemma84.WeightedBandData.mem_fiber_iff] using hp
    exact E.mem_cellPrimes_iff.mpr
      ⟨prime_of_mem_primeBand p.2, (E.band_eq_iff p j).mp hpBand⟩
  · intro p₁ hp₁ p₂ hp₂ heq
    exact Subtype.ext heq
  · intro q hq
    have hqData := E.mem_cellPrimes_iff.mp hq
    have hqBand : q ∈ primeBand n W := mem_primeBand.mpr
      ⟨hqData.1, (E.cutoff_le_lower j).trans_lt hqData.2.1,
        hqData.2.2.trans (E.upper_le_yNat j)⟩
    let p : BandPrime n W := ⟨q, hqBand⟩
    have hpFiber : p ∈ P.data.fiber j := by
      simp only [Erdos390.Lemma84.WeightedBandData.mem_fiber_iff]
      exact (E.band_eq_iff p j).mpr hqData.2
    exact ⟨p, hpFiber, rfl⟩
  · intro p hp
    unfold squareCoordinate realLogCoordinate tPrime
    ring

theorem bandSecondMoment_eq_fullWeightedReciprocalSum_sub
    (E : IntervalCertificate P) (j : Band) :
    P.bandSecondMoment j =
      fullWeightedReciprocalSum squareCoordinate (y n) (E.upper j) -
        fullWeightedReciprocalSum squareCoordinate (y n) (E.lower j) := by
  rw [P.bandSecondMoment_eq_cellPrimeSum E j]
  have hsub : PrimeSums.primesUpTo (E.lower j) ⊆
      PrimeSums.primesUpTo (E.upper j) := by
    intro p hp
    simp only [PrimeSums.primesUpTo, Finset.mem_filter,
      Finset.mem_Icc] at hp ⊢
    exact ⟨⟨hp.1.1, hp.1.2.trans (E.lower_le_upper j)⟩, hp.2⟩
  have hsum := Finset.sum_sdiff hsub
    (f := fun q : ℕ ↦
      squareCoordinate (realLogCoordinate (y n) (q : ℝ)) / (q : ℝ))
  change (∑ q ∈ PrimeSums.primesUpTo (E.upper j) \
      PrimeSums.primesUpTo (E.lower j),
        squareCoordinate (realLogCoordinate (y n) (q : ℝ)) / (q : ℝ)) = _
  exact eq_sub_of_add_eq hsum



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

theorem bandVariance_le_width_sq_mul_mass_of_coord_bounds
    (j : Band) {a b : ℝ}
    (hcoord : ∀ p ∈ P.data.fiber j, tPrime n p.1 ∈ Set.Icc a b) :
    P.bandVariance j ≤ (b - a) ^ 2 * P.mass j := by
  unfold bandVariance
  change (∑ p ∈ P.data.fiber j,
      (1 / (p.1 : ℝ)) * P.deviation p ^ 2) ≤
    (b - a) ^ 2 * (∑ p ∈ P.data.fiber j, 1 / (p.1 : ℝ))
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro p hp
  have hdev := P.abs_deviation_le_width_of_coord_bounds j hcoord p hp
  have hwidth : 0 ≤ b - a := (abs_nonneg _).trans hdev
  have hsq : P.deviation p ^ 2 ≤ (b - a) ^ 2 :=
    sq_le_sq.mpr (by simpa [abs_of_nonneg hwidth] using hdev)
  calc
    (1 / (p.1 : ℝ)) * P.deviation p ^ 2 ≤
        (1 / (p.1 : ℝ)) * (b - a) ^ 2 :=
      mul_le_mul_of_nonneg_left hsq (by positivity)
    _ = (b - a) ^ 2 * (1 / (p.1 : ℝ)) := by ring

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

theorem cellHarmonicMass_pos
    (hdelta : 0 < delta) (k : Fin M.cellCount) :
    0 < M.cellHarmonicMass k := by
  rw [M.cellHarmonicMass_eq_log_one_add_ratio hdelta k]
  exact Real.log_pos (by linarith [M.ratio_pos])

theorem cellHarmonicMass_le_ratio
    (hdelta : 0 < delta) (k : Fin M.cellCount) :
    M.cellHarmonicMass k ≤ M.ratio := by
  rw [M.cellHarmonicMass_eq_log_one_add_ratio hdelta k]
  have h := Real.log_le_sub_one_of_pos (by linarith [M.ratio_pos] :
    0 < 1 + M.ratio)
  linarith

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

omit hLower in
/-- The moving low cell contributes a fixed multiple of `delta²` without
any comparison between the positive mesh ratio and `delta`. -/
theorem actual_low_bandVariance_lower_of_ready
    (hdelta : 0 < delta) (hn : 1 < n)
    (R : MomentReady M P) :
    delta ^ 2 / 4 ≤ P.bandVariance 0 := by
  have hlowCoord := low_coord_bounds M P E hUpper hn
  have hlowCenterNonneg : 0 ≤ P.center 0 :=
    (P.center_mem_of_coord_bounds 0 hlowCoord).1
  have hlowFirstNonneg : 0 ≤ P.mass 0 * P.center 0 :=
    mul_nonneg (P.data.mass_pos 0).le hlowCenterNonneg
  have hcenterTerm : P.mass 0 * P.center 0 ^ 2 ≤ delta ^ 2 / 12 := by
    have hmassPos := P.data.mass_pos 0
    have hidentity : P.mass 0 * P.center 0 ^ 2 =
        (P.mass 0 * P.center 0) ^ 2 / P.mass 0 := by
      field_simp [ne_of_gt hmassPos]
    rw [hidentity, div_le_iff₀ hmassPos]
    have hfirstSq : (P.mass 0 * P.center 0) ^ 2 ≤ (2 * delta) ^ 2 :=
      (sq_le_sq₀ hlowFirstNonneg (by positivity)).2 R.lowFirst
    have hright : (2 * delta) ^ 2 ≤ delta ^ 2 / 12 * P.mass 0 := by
      nlinarith [R.lowMass, sq_nonneg delta]
    exact hfirstSq.trans hright
  rw [P.bandVariance_eq_second_sub_mass_center_sq]
  linarith [R.lowSecondLower, hcenterTerm]

/-- The quadratic upper bound is uniform for independent mesh parameters;
it does not use `M.ratio ≤ delta`. -/
theorem actual_variance_upper_of_ready
    (hdelta : 0 < delta) (hn : 1 < n)
    (R : MomentReady M P) :
    P.variance ≤ 4 * (delta + M.ratio) ^ 2 := by
  have hposCoord := positive_coord_bounds M P E hLower hUpper hn
  have hlowVarUpper : P.bandVariance 0 ≤ delta ^ 2 := by
    rw [P.bandVariance_eq_second_sub_mass_center_sq]
    have hterm : 0 ≤ P.mass 0 * P.center 0 ^ 2 :=
      mul_nonneg (P.data.mass_pos 0).le (sq_nonneg _)
    linarith [R.lowSecondUpper]
  have hposVar (k : Fin M.cellCount) :
      P.bandVariance k.succ ≤ 3 * M.ratio * M.width k ^ 2 := by
    have hraw := P.bandVariance_le_width_sq_mul_mass_of_coord_bounds k.succ
      (hposCoord k)
    rw [show M.upper k - M.lower k = M.width k by rfl] at hraw
    calc
      P.bandVariance k.succ ≤ M.width k ^ 2 * P.mass k.succ := hraw
      _ ≤ M.width k ^ 2 * (3 * M.ratio) :=
        mul_le_mul_of_nonneg_left (R.positiveMass k) (sq_nonneg _)
      _ = 3 * M.ratio * M.width k ^ 2 := by ring
  have hsumWidthSq :
      (∑ k : Fin M.cellCount, M.width k ^ 2) ≤ M.ratio := by
    calc
      (∑ k : Fin M.cellCount, M.width k ^ 2) ≤
          ∑ k : Fin M.cellCount, M.ratio * M.width k := by
        apply Finset.sum_le_sum
        intro k hk
        have hw0 := (M.width_pos hdelta k).le
        have hwle := M.width_le_ratio hdelta k
        nlinarith
      _ = M.ratio * (1 - delta) := by
        rw [← Finset.mul_sum, M.sum_width_eq_one_sub_delta]
      _ ≤ M.ratio := by nlinarith [M.ratio_pos]
  rw [P.variance_eq_sum_bandVariance, Fin.sum_univ_succ]
  calc
    P.bandVariance 0 + ∑ k : Fin M.cellCount, P.bandVariance k.succ ≤
        delta ^ 2 + ∑ k : Fin M.cellCount,
          3 * M.ratio * M.width k ^ 2 := by
      exact add_le_add hlowVarUpper
        (Finset.sum_le_sum fun k hk ↦ hposVar k)
    _ = delta ^ 2 + 3 * M.ratio *
        (∑ k : Fin M.cellCount, M.width k ^ 2) := by
      rw [← Finset.mul_sum]
    _ ≤ delta ^ 2 + 3 * M.ratio ^ 2 := by
      have hmul := mul_le_mul_of_nonneg_left hsumWidthSq
        (show 0 ≤ 3 * M.ratio by
          exact mul_nonneg (by norm_num) M.ratio_pos.le)
      nlinarith
    _ ≤ 4 * (delta + M.ratio) ^ 2 := by
      nlinarith [M.ratio_pos, hdelta]



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



/-- The actual prime-deviation coefficient is uniformly of size at most
`w = delta + ratio`; this is the pointwise input to the compensated-score
regression ledger. -/
theorem actual_deviation_sup_le_scale
    (hdelta : 0 < delta) (hn : 1 < n)
    (p : BandPrime n W) :
    |P.deviation p| ≤ delta + M.ratio := by
  let motive := fun j : Fin (M.cellCount + 1) ↦
    P.band p = j → |P.deviation p| ≤ delta + M.ratio
  apply (Fin.cases (motive := motive) ?_ ?_
    (P.band p)) rfl
  · intro hpBand
    have hpFiber : p ∈ P.data.fiber (0 : Fin (M.cellCount + 1)) :=
      (Erdos390.Lemma84.WeightedBandData.mem_fiber_iff P.data).mpr hpBand
    have hdev := P.abs_deviation_le_width_of_coord_bounds 0
      (low_coord_bounds M P E hUpper hn) p hpFiber
    nlinarith [M.ratio_pos]
  · intro k hpBand
    have hpFiber : p ∈ P.data.fiber k.succ :=
      (Erdos390.Lemma84.WeightedBandData.mem_fiber_iff P.data).mpr hpBand
    have hdev := P.abs_deviation_le_width_of_coord_bounds k.succ
      (positive_coord_bounds M P E hLower hUpper hn k) p hpFiber
    rw [show M.upper k - M.lower k = M.width k by rfl] at hdev
    have hw := M.width_le_ratio hdelta k
    nlinarith







end Mesh

end

end Erdos390.Full.RegularMeshPrimeCutoffs

end

/- Source module: Erdos390.Full.PaperCompensatedCoefficientBounds -/
section


/-!
# Actual compensated-prime coefficient bounds for Lemma 8.6

This file specializes the elementary coefficient ledger to the literal
arithmetic prime partition.  The regression vector is an element of the
paper's exact arithmetic gauge

`sum_j H_j * alpha_j * q_j = 0`,

and the compensated coefficient is literally
`c_p = (alpha_{j(p)} - t_p) - q_{j(p)}`.  Thus none of the three norms below
is represented by an abstract array or stored in a certificate.

The sole regression input is the sharp norm estimate produced by the
weighted inverse and the row estimate.  All remaining estimates are derived
from the actual prime sums and the already proved canonical-mesh moment
bounds.
-/

open scoped BigOperators

namespace Erdos390.Full.ArithmeticBandGeometry.Partition

open ArithmeticModel ArithmeticBandGeometry
open PaperWeightedInverseExport PrimeSums

noncomputable section

variable {n W : ℕ} {Band : Type*} [Fintype Band] [DecidableEq Band]
  (P : Partition n W Band)













theorem center_mem_zero_one (hn : 1 < n) (j : Band) :
    P.center j ∈ Set.Icc (0 : ℝ) 1 := by
  apply P.center_mem_of_coord_bounds j
  intro p hp
  have hpBand : p.1 ∈ primeBand n W := p.2
  exact ⟨PaperPrimePowerRow.tPrime_nonneg_of_mem_primeBand hn hpBand,
    PaperPrimePowerRow.tPrime_le_one_of_mem_primeBand hn hpBand⟩

























end

end Erdos390.Full.ArithmeticBandGeometry.Partition

end

/- Source module: Erdos390.Full.PaperPermittedRegularMesh -/
section


/-!
# The paper's two-sided relative-mesh condition

`RegularRelativeMesh.Mesh delta eta` records an exact common relative width
`M.ratio` and the upper estimate `M.ratio ≤ eta`.  The permitted meshes in
Section 8.4 of the paper also satisfy the lower estimate

`cMesh * eta ≤ M.ratio`.

Keeping that second estimate as a named proposition prevents an arbitrary
upper-width parameter from being confused with the actual mesh scale.  The
elementary lemmas below convert estimates at the actual scale
`delta + M.ratio` to the paper scale `delta + eta`, with constants depending
only on the fixed structural regularity constant `cMesh`.
-/

namespace Erdos390.Full.PaperPermittedRegularMesh

open Erdos390.Full.RegularRelativeMesh

noncomputable section



namespace IsPermitted

variable {delta eta cMesh : ℝ} {M : Mesh delta eta}

theorem eta_pos (M : Mesh delta eta) : 0 < eta :=
  lt_of_lt_of_le M.ratio_pos M.ratio_le_eta



/-- The normalization `cMesh ≤ 1` is a consequence of the two-sided
mesh condition, not an additional paper hypothesis. -/
theorem cMesh_le_one (h : IsPermitted (cMesh := cMesh) M) : cMesh ≤ 1 := by
  change cMesh * eta ≤ M.ratio at h
  have heta : 0 < eta := eta_pos M
  have hupper : M.ratio ≤ eta := M.ratio_le_eta
  nlinarith

/-- For the usual normalization `cMesh ≤ 1`, the actual scale controls the
paper scale without any relation between `delta` and `eta`. -/
theorem cMesh_mul_paperScale_le_actualScale
    (hdelta : 0 ≤ delta) (hcOne : cMesh ≤ 1)
    (h : IsPermitted (cMesh := cMesh) M) :
    cMesh * (delta + eta) ≤ delta + M.ratio := by
  change cMesh * eta ≤ M.ratio at h
  have hcdelta : cMesh * delta ≤ delta := by
    nlinarith
  calc
    cMesh * (delta + eta) = cMesh * delta + cMesh * eta := by ring
    _ ≤ delta + M.ratio := add_le_add hcdelta h

theorem paperScale_le_inv_mul_actualScale
    (hdelta : 0 ≤ delta) (hc : 0 < cMesh) (hcOne : cMesh ≤ 1)
    (h : IsPermitted (cMesh := cMesh) M) :
    delta + eta ≤ (1 / cMesh) * (delta + M.ratio) := by
  have hscale := cMesh_mul_paperScale_le_actualScale
    hdelta hcOne h
  calc
    delta + eta ≤ (delta + M.ratio) / cMesh :=
      (le_div_iff₀ hc).2 (by simpa [mul_comm] using hscale)
    _ = (1 / cMesh) * (delta + M.ratio) := by
      field_simp [ne_of_gt hc]

theorem paperScale_sq_le_invSq_mul_actualScale_sq
    (hdelta : 0 ≤ delta) (hc : 0 < cMesh) (hcOne : cMesh ≤ 1)
    (h : IsPermitted (cMesh := cMesh) M) :
    (delta + eta) ^ 2 ≤
      (1 / cMesh ^ 2) * (delta + M.ratio) ^ 2 := by
  have hpaperNonneg : 0 ≤ delta + eta :=
    add_nonneg hdelta (eta_pos M).le
  have hactualNonneg : 0 ≤ delta + M.ratio :=
    add_nonneg hdelta M.ratio_pos.le
  have hscale := paperScale_le_inv_mul_actualScale
    hdelta hc hcOne h
  have hinvNonneg : 0 ≤ 1 / cMesh := by positivity
  have hsquare := (sq_le_sq₀ hpaperNonneg
    (mul_nonneg hinvNonneg hactualNonneg)).2 hscale
  calc
    (delta + eta) ^ 2 ≤ ((1 / cMesh) * (delta + M.ratio)) ^ 2 := hsquare
    _ = (1 / cMesh ^ 2) * (delta + M.ratio) ^ 2 := by
      field_simp [ne_of_gt hc]



/-- A lower quadratic estimate at the actual mesh scale implies the
corresponding paper-scale estimate. -/
theorem paperScale_sq_le_of_actualScale_sq_le
    (hdelta : 0 ≤ delta) (hc : 0 < cMesh) (hcOne : cMesh ≤ 1)
    (h : IsPermitted (cMesh := cMesh) M)
    {V K : ℝ}
    (hV : (delta + M.ratio) ^ 2 ≤ K * V) :
    (delta + eta) ^ 2 ≤ (K / cMesh ^ 2) * V := by
  have hscale := paperScale_sq_le_invSq_mul_actualScale_sq
    hdelta hc hcOne h
  calc
    (delta + eta) ^ 2 ≤
        (1 / cMesh ^ 2) * (delta + M.ratio) ^ 2 := hscale
    _ ≤ (1 / cMesh ^ 2) * (K * V) := by
      exact mul_le_mul_of_nonneg_left hV (by positivity)
    _ = (K / cMesh ^ 2) * V := by ring

/-- The preceding transfer without a separately supplied `cMesh ≤ 1`
premise. -/
theorem paperScale_sq_le_of_actualScale_sq_le_of_pos
    (hdelta : 0 ≤ delta) (hc : 0 < cMesh)
    (h : IsPermitted (cMesh := cMesh) M)
    {V K : ℝ}
    (hV : (delta + M.ratio) ^ 2 ≤ K * V) :
    (delta + eta) ^ 2 ≤ (K / cMesh ^ 2) * V :=
  paperScale_sq_le_of_actualScale_sq_le
    hdelta hc (cMesh_le_one h) h hV

/-- The actual scale is always bounded above by the paper scale. -/
theorem actualScale_le_paperScale :
    delta + M.ratio ≤ delta + eta := by
  linarith [M.ratio_le_eta]

/-- Coarse but uniform combination of the low-cell and positive-cell
quadratic lower bounds used in Lemma 8.6. -/
theorem actualScale_sq_le_456_mul_of_low_and_positive
    {V : ℝ}
    (hlow : delta ^ 2 / 4 ≤ V)
    (hpositive : M.ratio ^ 2 / 224 ≤ V) :
    (delta + M.ratio) ^ 2 ≤ 456 * V := by
  have hcross : (delta + M.ratio) ^ 2 ≤
      2 * delta ^ 2 + 2 * M.ratio ^ 2 := by
    nlinarith [sq_nonneg (delta - M.ratio)]
  have hdeltaV : delta ^ 2 ≤ 4 * V := by linarith
  have hratioV : M.ratio ^ 2 ≤ 224 * V := by linarith
  nlinarith

/-- The exact paper-scale consequence of the two complementary arithmetic
variance estimates.  Only the stated two-sided regularity and
`0 < cMesh` are required. -/
theorem paperScale_sq_le_of_low_and_positive
    (hdelta : 0 ≤ delta) (hc : 0 < cMesh)
    (h : IsPermitted (cMesh := cMesh) M) {V : ℝ}
    (hlow : delta ^ 2 / 4 ≤ V)
    (hpositive : M.ratio ^ 2 / 224 ≤ V) :
    (delta + eta) ^ 2 ≤ (456 / cMesh ^ 2) * V := by
  apply paperScale_sq_le_of_actualScale_sq_le_of_pos hdelta hc h
  exact actualScale_sq_le_456_mul_of_low_and_positive
    hlow hpositive

end IsPermitted

end

end Erdos390.Full.PaperPermittedRegularMesh

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



theorem tendsto_general_positive_lowerCutoff_atTop
    (hdelta : 0 < delta) (W : ℕ) (k : Fin M.cellCount) :
    Tendsto (fun n : ℕ ↦ fullCutoff M n W (k.1 + 1))
      atTop atTop := by
  simpa only [fullCutoff_succ, RegularRelativeMesh.Mesh.lower] using
    tendsto_nat_floor_atTop.comp
      (tendsto_scalePoint_atTop (M.lower_pos hdelta k))



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









end Mesh
end Erdos390.Full.RegularMeshPrimeCutoffs

end

/- Source module: Erdos390.Full.PaperCanonicalPrimeAnchorEventually -/
section


/-!
# Literal prime anchors for a fixed regular-mesh block

The continuum anchor used by the transferred inverse is not, by itself, the
prime anchor required by the finite Dirichlet argument.  This file constructs
the latter as the union of the literal prime fibers belonging to the selected
positive cells.  It proves both facts needed later:

* every selected prime stays in the prescribed compact subinterval of
  logarithmic coordinates; and
* its `t_p / p` mass is bounded below uniformly in the mesh, provided the
  selected ideal cells have a fixed total-width floor.

The mass comparison is an unconditional two-endpoint PNT estimate.  In
particular, no arithmetic centre is identified with a continuum centre.
-/

open Filter Set
open scoped BigOperators

noncomputable section

namespace Erdos390.Full.RegularMeshPrimeCutoffs

open ArithmeticModel ArithmeticBandGeometry RegularRelativeMesh
open PositiveCellTransfer MovingLowMomentQuadrature
open KernelPrimeQuadrature DoubleKernelPrimeQuadrature
open PrimeSquarefreeDirichletGeometry
open FiniteAnchoredDirichletQuadratic

namespace Mesh

variable {delta eta : ℝ} (M : Mesh delta eta)



theorem mem_canonicalPrimeAnchorSet_iff
    {n W : ℕ} {P : Partition n W (Fin (M.cellCount + 1))}
    {anchors : Finset (Fin M.cellCount)} {p : BandPrime n W} :
    p ∈ canonicalPrimeAnchorSet M P anchors ↔
      ∃ k ∈ anchors, P.band p = positiveBand M k := by
  classical
  simp only [canonicalPrimeAnchorSet, Finset.mem_filter, Finset.mem_univ,
    true_and, Finset.mem_map]
  constructor
  · rintro ⟨k, hk, hkp⟩
    exact ⟨k, hk, hkp.symm⟩
  · rintro ⟨k, hk, hpk⟩
    exact ⟨k, hk, hpk.symm⟩

/-- The `t_p/p` mass of one literal fiber is exactly `H_j alpha_j`.
This is finite arithmetic centering, with no limiting object involved. -/
theorem sum_primeWeight_fiber_eq_mass_mul_center
    {n W : ℕ} (P : Partition n W (Fin (M.cellCount + 1)))
    (j : Fin (M.cellCount + 1)) :
    (∑ p ∈ P.data.fiber j, primeWeight n p) =
      P.mass j * P.center j := by
  have hrewrite : (∑ p ∈ P.data.fiber j, primeWeight n p) =
      ∑ p ∈ P.data.fiber j,
        (1 / (p.1 : ℝ)) * tPrime n p.1 := by
    apply Finset.sum_congr rfl
    intro p hp
    unfold primeWeight
    ring
  rw [hrewrite]
  change (∑ p ∈ P.data.fiber j,
      (1 / (p.1 : ℝ)) * tPrime n p.1) =
    P.data.mass j *
      ((∑ p ∈ P.data.fiber j,
        (1 / (p.1 : ℝ)) * tPrime n p.1) / P.data.mass j)
  field_simp [ne_of_gt (P.data.mass_pos j)]

/-- Exact mass identity for the whole selected prime block. -/
theorem anchorMass_canonicalPrimeAnchorSet_eq
    {n W : ℕ} (P : Partition n W (Fin (M.cellCount + 1)))
    (anchors : Finset (Fin M.cellCount)) :
    anchorMass (primeWeight n) (canonicalPrimeAnchorSet M P anchors) =
      ∑ k ∈ anchors,
        P.mass (positiveBand M k) * P.center (positiveBand M k) := by
  classical
  unfold anchorMass canonicalPrimeAnchorSet
  rw [← Finset.sum_fiberwise_eq_sum_filter Finset.univ
    (anchors.map (positiveBandEmbedding M)) P.band (primeWeight n)]
  rw [Finset.sum_map]
  apply Finset.sum_congr rfl
  intro k hk
  exact sum_primeWeight_fiber_eq_mass_mul_center M P (positiveBand M k)

/-- The interior prime mass controls the literal arithmetic centre energy.
This is an exact finite inequality; it does not pass through continuum
centres. -/
theorem epsilon_mul_anchorMass_le_centerEnergy
    {n W : ℕ} (P : Partition n W (Fin (M.cellCount + 1)))
    (hn : 1 < n)
    {epsilon : ℝ} (hepsilon : 0 ≤ epsilon)
    (anchors : Finset (Fin M.cellCount))
    (hinterior : ∀ p ∈ canonicalPrimeAnchorSet M P anchors,
      tPrime n p.1 ∈ Icc epsilon (1 - epsilon)) :
    epsilon * anchorMass (primeWeight n)
        (canonicalPrimeAnchorSet M P anchors) ≤ P.centerEnergy := by
  classical
  have hCenterLower (k : Fin M.cellCount) (hk : k ∈ anchors) :
      epsilon ≤ P.center (positiveBand M k) := by
    exact (P.center_mem_of_coord_bounds (positiveBand M k) (fun p hp ↦ by
      apply hinterior p
      exact (mem_canonicalPrimeAnchorSet_iff M).mpr
        ⟨k, hk,
          (Erdos390.Lemma84.WeightedBandData.mem_fiber_iff P.data).mp hp⟩)).1
  rw [anchorMass_canonicalPrimeAnchorSet_eq M]
  have hSelected :
      epsilon * (∑ k ∈ anchors,
          P.mass (positiveBand M k) * P.center (positiveBand M k)) ≤
        ∑ k ∈ anchors,
          P.mass (positiveBand M k) * P.center (positiveBand M k) *
            P.center (positiveBand M k) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro k hk
    have hmass := (P.data.mass_pos (positiveBand M k)).le
    have hcenter : 0 ≤ P.center (positiveBand M k) :=
      hepsilon.trans (hCenterLower k hk)
    have hdiff : 0 ≤ P.center (positiveBand M k) - epsilon :=
      sub_nonneg.mpr (hCenterLower k hk)
    nlinarith [mul_nonneg (mul_nonneg hmass hcenter) hdiff]
  calc
    epsilon * (∑ k ∈ anchors,
        P.mass (positiveBand M k) * P.center (positiveBand M k)) ≤
        ∑ k ∈ anchors,
          P.mass (positiveBand M k) * P.center (positiveBand M k) *
            P.center (positiveBand M k) := hSelected
    _ = ∑ j ∈ anchors.map (positiveBandEmbedding M),
          P.mass j * P.center j * P.center j := by
      rw [Finset.sum_map]
      rfl
    _ ≤ ∑ j,
          P.mass j * P.center j * P.center j := by
      apply Finset.sum_le_univ_sum_of_nonneg
      intro j
      exact mul_nonneg
        (mul_nonneg (P.data.mass_pos j).le
          (P.center_mem_zero_one hn j).1)
        (P.center_mem_zero_one hn j).1
    _ = P.centerEnergy := by
      rfl



/-- First-moment quadrature for a canonical endpoint cell, stated as a
standalone reusable bound. -/
theorem abs_canonical_mass_mul_center_sub_endpointContinuumMoment_le
    {n W : ℕ} (hdelta : 0 < delta) (hn : 1 < n) (hW : W ≠ 0)
    (S : ScaleSeparation M n W)
    {Cmoment : ℝ} {Xmoment : ℕ}
    (hMoment : ∀ A Y : ℕ, Xmoment ≤ A → A ≤ Y →
      |PrimeSums.fullLogReciprocalSum Y -
        PrimeSums.fullLogReciprocalSum A -
        (Real.log (Y : ℝ) - Real.log (A : ℝ))| ≤
        2 * Cmoment / Real.log (A : ℝ) ^ 3 +
          Cmoment / (2 * Real.log (A : ℝ) ^ 2))
    (hXmoment : Xmoment ≤ W)
    (j : Fin (M.cellCount + 1)) :
    let P := canonicalPartition M hdelta hn hW S
    |P.mass j * P.center j - endpointContinuumMoment M n W j| ≤
      endpointMomentError M Cmoment n W j := by
  let P := canonicalPartition M hdelta hn hW S
  let E := canonicalCertificate M hdelta hn hW S
  dsimp only
  have hLowerThreshold : Xmoment ≤ E.lower j :=
    hXmoment.trans (E.cutoff_le_lower j)
  have h := hMoment (E.lower j) (E.upper j) hLowerThreshold
    (E.lower_le_upper j)
  rw [E.mass_mul_center_eq_fullLogReciprocalSum_sub]
  have hlog : 0 < Real.log (y n) := by
    rw [Scale.log_y (Nat.zero_lt_of_lt hn)]
    exact mul_pos (by norm_num) (Real.log_pos (by exact_mod_cast hn))
  have hNorm :
      |(PrimeSums.fullLogReciprocalSum (E.upper j) -
            PrimeSums.fullLogReciprocalSum (E.lower j)) /
            Real.log (y n) - E.continuumMoment j| ≤
        (2 * Cmoment / Real.log (E.lower j : ℝ) ^ 3 +
          Cmoment / (2 * Real.log (E.lower j : ℝ) ^ 2)) /
            Real.log (y n) := by
    unfold IntervalCertificate.continuumMoment
    rw [show
      (PrimeSums.fullLogReciprocalSum (E.upper j) -
            PrimeSums.fullLogReciprocalSum (E.lower j)) /
            Real.log (y n) -
          (Real.log (E.upper j : ℝ) - Real.log (E.lower j : ℝ)) /
            Real.log (y n) =
        ((PrimeSums.fullLogReciprocalSum (E.upper j) -
            PrimeSums.fullLogReciprocalSum (E.lower j)) -
          (Real.log (E.upper j : ℝ) - Real.log (E.lower j : ℝ))) /
            Real.log (y n) by ring]
    rw [abs_div, abs_of_pos hlog]
    exact div_le_div_of_nonneg_right h hlog.le
  simpa only [P, E, canonicalCertificate_lower,
    endpointMomentError] using hNorm







end Mesh
end Erdos390.Full.RegularMeshPrimeCutoffs

end

/- Source module: Erdos390.Full.RegularRelativeMeshInteriorAnchors -/
section


/-!
# A fixed-mass interior anchor block in every fine relative mesh

For the uniform moving-low inverse one cannot anchor on a single cell: its
width may tend to zero as the mesh is refined.  This file selects all cells
between the first crossings of `1/4` and `3/4`.  If every cell is shorter
than `1/16` and the low endpoint is below `1/16`, that block lies strictly
inside `[1/8,7/8]` and has total width at least `1/4` (in fact at least
`7/16`).
-/

open scoped BigOperators

namespace Erdos390.Full.RegularRelativeMesh

noncomputable section

namespace Mesh

variable {delta eta : ℝ} (M : Mesh delta eta)

theorem strictMono_endpoint (hdelta : 0 < delta) :
    StrictMono M.endpoint := by
  apply strictMono_nat_of_lt_succ
  intro k
  rw [M.endpoint_succ]
  have he := M.endpoint_pos hdelta k
  have hr := M.ratio_pos
  nlinarith [mul_pos he hr]





theorem firstEndpointAtLeast_spec (x : ℝ) (hx : x ≤ 1) :
    x ≤ M.endpoint (M.firstEndpointAtLeast x hx) := by
  exact Nat.find_spec (M.exists_endpoint_ge x hx)



theorem endpoint_lt_of_lt_firstEndpointAtLeast
    (x : ℝ) (hx : x ≤ 1) {k : ℕ}
    (hk : k < M.firstEndpointAtLeast x hx) :
    M.endpoint k < x := by
  exact lt_of_not_ge
    (Nat.find_min (M.exists_endpoint_ge x hx) hk)

theorem firstEndpointAtLeast_pos
    (x : ℝ) (hx : x ≤ 1)
    (hdeltax : delta < x) :
    0 < M.firstEndpointAtLeast x hx := by
  by_contra h
  have hzero : M.firstEndpointAtLeast x hx = 0 := by omega
  have hspec := M.firstEndpointAtLeast_spec x hx
  rw [hzero, M.endpoint_zero] at hspec
  linarith

theorem firstEndpointAtLeast_endpoint_lt_add
    (x tol : ℝ) (hx : x ≤ 1)
    (hdeltax : delta < x)
    (hwidth : ∀ k : Fin M.cellCount, M.width k < tol) :
    M.endpoint (M.firstEndpointAtLeast x hx) < x + tol := by
  let j := M.firstEndpointAtLeast x hx
  have hjpos : 0 < j := M.firstEndpointAtLeast_pos x hx hdeltax
  have hjle : j ≤ M.cellCount := M.firstEndpointAtLeast_le_cellCount x hx
  let k : Fin M.cellCount := ⟨j - 1, by omega⟩
  have hprev : M.endpoint (j - 1) < x := by
    apply M.endpoint_lt_of_lt_firstEndpointAtLeast x hx
    omega
  have hupper : M.upper k = M.endpoint j := by
    dsimp only [k, upper]
    rw [Nat.sub_add_cancel hjpos]
  have hstep : M.endpoint j = M.lower k + M.width k := by
    rw [← hupper]
    unfold width
    ring
  rw [hstep]
  have hw := hwidth k
  dsimp only [k, lower] at hprev ⊢
  linarith



theorem first_quarter_lt_first_threeQuarter
    (hdelta : 0 < delta) (hdeltaSmall : delta < 1 / 16)
    (hwidth : ∀ k : Fin M.cellCount, M.width k < (1 / 16 : ℝ)) :
    M.firstEndpointAtLeast (1 / 4 : ℝ) (by norm_num) <
      M.firstEndpointAtLeast (3 / 4 : ℝ) (by norm_num) := by
  let j := M.firstEndpointAtLeast (1 / 4 : ℝ) (by norm_num)
  let l := M.firstEndpointAtLeast (3 / 4 : ℝ) (by norm_num)
  have hjUpper : M.endpoint j < (1 / 4 : ℝ) + 1 / 16 := by
    exact M.firstEndpointAtLeast_endpoint_lt_add
      (1 / 4 : ℝ) (1 / 16 : ℝ) (by norm_num)
      (by linarith) hwidth
  have hlLower : (3 / 4 : ℝ) ≤ M.endpoint l :=
    M.firstEndpointAtLeast_spec _ _
  by_contra h
  have hlj : l ≤ j := Nat.le_of_not_gt h
  have hmono := (M.strictMono_endpoint hdelta).monotone hlj
  linarith

theorem interiorAnchors_nonempty
    (hdelta : 0 < delta) (hdeltaSmall : delta < 1 / 16)
    (hwidth : ∀ k : Fin M.cellCount, M.width k < (1 / 16 : ℝ)) :
    M.interiorAnchors.Nonempty := by
  let j := M.firstEndpointAtLeast (1 / 4 : ℝ) (by norm_num)
  let l := M.firstEndpointAtLeast (3 / 4 : ℝ) (by norm_num)
  have hjl : j < l :=
    M.first_quarter_lt_first_threeQuarter hdelta hdeltaSmall hwidth
  have hlcell : l ≤ M.cellCount :=
    M.firstEndpointAtLeast_le_cellCount _ _
  let k : Fin M.cellCount := ⟨j, by omega⟩
  refine ⟨k, ?_⟩
  simp only [interiorAnchors, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨le_rfl, hjl⟩

theorem interiorAnchors_idealLower
    (hdelta : 0 < delta) {k : Fin M.cellCount}
    (hk : k ∈ M.interiorAnchors) :
    (1 / 8 : ℝ) < M.lower k := by
  have hk' := (Finset.mem_filter.mp hk).2.1
  have hspec := M.firstEndpointAtLeast_spec (1 / 4 : ℝ) (by norm_num)
  have hmono := (M.strictMono_endpoint hdelta).monotone hk'
  dsimp only [lower]
  linarith

theorem interiorAnchors_idealUpper
    (hdelta : 0 < delta) (hdeltaSmall : delta < 1 / 16)
    (hwidth : ∀ k : Fin M.cellCount, M.width k < (1 / 16 : ℝ))
    {k : Fin M.cellCount} (hk : k ∈ M.interiorAnchors) :
    M.upper k ≤ 1 - (1 / 8 : ℝ) := by
  let l := M.firstEndpointAtLeast (3 / 4 : ℝ) (by norm_num)
  have hklt : k.1 < l := (Finset.mem_filter.mp hk).2.2
  have hlUpper : M.endpoint l < (3 / 4 : ℝ) + 1 / 16 := by
    exact M.firstEndpointAtLeast_endpoint_lt_add
      (3 / 4 : ℝ) (1 / 16 : ℝ) (by norm_num)
      (by linarith) hwidth
  have hsucc : k.1 + 1 ≤ l := by omega
  have hmono := (M.strictMono_endpoint hdelta).monotone hsucc
  dsimp only [upper]
  linarith

theorem sum_width_interiorAnchors_eq
    (hdelta : 0 < delta) (hdeltaSmall : delta < 1 / 16)
    (hwidth : ∀ k : Fin M.cellCount, M.width k < (1 / 16 : ℝ)) :
    (∑ k ∈ M.interiorAnchors, M.width k) =
      M.endpoint
          (M.firstEndpointAtLeast (3 / 4 : ℝ) (by norm_num)) -
      M.endpoint
          (M.firstEndpointAtLeast (1 / 4 : ℝ) (by norm_num)) := by
  let j := M.firstEndpointAtLeast (1 / 4 : ℝ) (by norm_num)
  let l := M.firstEndpointAtLeast (3 / 4 : ℝ) (by norm_num)
  simp only [interiorAnchors, Finset.sum_filter]
  change (∑ a : Fin M.cellCount,
    if j ≤ a.1 ∧ a.1 < l then M.width a else 0) =
      M.endpoint l - M.endpoint j
  simp only [width, upper, lower]
  change (∑ a : Fin M.cellCount,
    (fun i : ℕ ↦ if j ≤ i ∧ i < l then
      M.endpoint (i + 1) - M.endpoint i else 0) a.1) =
        M.endpoint l - M.endpoint j
  have hjl : j < l :=
    M.first_quarter_lt_first_threeQuarter hdelta hdeltaSmall hwidth
  have hlcell : l ≤ M.cellCount :=
    M.firstEndpointAtLeast_le_cellCount _ _
  calc
    _ = ∑ i ∈ Finset.range M.cellCount,
        if j ≤ i ∧ i < l then
          M.endpoint (i + 1) - M.endpoint i else 0 :=
      Fin.sum_univ_eq_sum_range
        (fun i : ℕ ↦ if j ≤ i ∧ i < l then
          M.endpoint (i + 1) - M.endpoint i else 0) M.cellCount
    _ = ∑ i ∈ Finset.Ico j l,
        (M.endpoint (i + 1) - M.endpoint i) := by
      rw [← Finset.sum_filter]
      apply Finset.sum_congr
      · ext i
        simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
        omega
      · intro i hi
        rfl
    _ = M.endpoint l - M.endpoint j := by
      rw [Finset.sum_Ico_eq_sub _ hjl.le,
        Finset.sum_range_sub, Finset.sum_range_sub]
      ring

theorem interiorAnchors_mass_lower
    (hdelta : 0 < delta) (hdeltaSmall : delta < 1 / 16)
    (hwidth : ∀ k : Fin M.cellCount, M.width k < (1 / 16 : ℝ)) :
    (1 / 8 : ℝ) ≤ (∑ k ∈ M.interiorAnchors, M.width k) / 2 := by
  have hsum := M.sum_width_interiorAnchors_eq hdelta hdeltaSmall hwidth
  have hlower : (3 / 4 : ℝ) ≤
      M.endpoint (M.firstEndpointAtLeast (3 / 4 : ℝ) (by norm_num)) :=
    M.firstEndpointAtLeast_spec _ _
  have hupper :
      M.endpoint (M.firstEndpointAtLeast (1 / 4 : ℝ) (by norm_num)) <
        (1 / 4 : ℝ) + 1 / 16 := by
    exact M.firstEndpointAtLeast_endpoint_lt_add
      (1 / 4 : ℝ) (1 / 16 : ℝ) (by norm_num)
      (by linarith) hwidth
  rw [hsum]
  linarith

/-- Every sufficiently fine relative mesh carries the fixed interior anchor
block needed by the mesh-uniform continuum and arithmetic inverse. -/
theorem exists_interiorAnchorBlock
    (hdelta : 0 < delta) (hdeltaSmall : delta < 1 / 16)
    (hwidth : ∀ k : Fin M.cellCount, M.width k < (1 / 16 : ℝ)) :
    ∃ anchors : Finset (Fin M.cellCount), ∃ anchor : Fin M.cellCount,
      anchor ∈ anchors ∧
      (∀ k ∈ anchors, (1 / 8 : ℝ) < M.lower k) ∧
      (∀ k ∈ anchors, M.upper k ≤ 1 - (1 / 8 : ℝ)) ∧
      (1 / 8 : ℝ) ≤ (∑ k ∈ anchors, M.width k) / 2 := by
  have hne := M.interiorAnchors_nonempty hdelta hdeltaSmall hwidth
  let anchor : Fin M.cellCount := hne.choose
  have hanchor : anchor ∈ M.interiorAnchors := hne.choose_spec
  refine ⟨M.interiorAnchors, anchor, hanchor, ?_, ?_, ?_⟩
  · intro k hk
    exact M.interiorAnchors_idealLower hdelta hk
  · intro k hk
    exact M.interiorAnchors_idealUpper hdelta hdeltaSmall hwidth hk
  · exact M.interiorAnchors_mass_lower hdelta hdeltaSmall hwidth

end Mesh

end

end Erdos390.Full.RegularRelativeMesh

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

/-- The deviation, first-moment, and variance-upper estimates are uniform
for independent mesh parameters `delta` and `eta`.  No variance lower bound,
and hence no comparison `M.ratio ≤ delta`, is used here. -/
theorem canonicalActualPreliminaryMomentCutoff_eventually
    (hdelta : 0 < delta) :
    ∀ W : ℕ, canonicalActualMomentCutoff ≤ W →
      ∀ᶠ n : ℕ in atTop,
        ∃ hWne : W ≠ 0, ∃ hn : 1 < n,
          ∀ S : ScaleSeparation M n W,
            let P := canonicalPartition M hdelta hn hWne S
            (∀ p : BandPrime n W,
              |P.deviation p| ≤ delta + M.ratio) ∧
            P.totalL1 ≤ 7 * (delta + M.ratio) ∧
            delta ^ 2 / 4 ≤ P.bandVariance 0 ∧
            P.variance ≤ 4 * (delta + M.ratio) ^ 2 := by
  let Cmass : ℝ := canonicalMassQuadratureConstant
  let Xmass : ℕ := canonicalMassQuadratureCutoff
  let Cfirst : ℝ :=
    MovingLowMomentQuadrature.fullLogReciprocalSumUniformConstant
  let Xfirst : ℕ :=
    MovingLowMomentQuadrature.fullLogReciprocalSumUniformCutoff
  let Csecond : ℝ := canonicalSecondMomentConstant
  let Xsecond : ℕ := canonicalSecondMomentCutoff
  have hMass : ∀ A Y : ℕ, Xmass ≤ A → A ≤ Y →
      |PrimeSums.fullReciprocalSum Y - PrimeSums.fullReciprocalSum A -
          (Real.log (Real.log (Y : ℝ)) -
            Real.log (Real.log (A : ℝ)))| ≤
        5 * Cmass / Real.log (A : ℝ) ^ 3 := by
    intro A Y hA hAY
    simpa only [Cmass, Xmass] using
      canonicalMassQuadratureBound A Y hA hAY
  have hFirst : ∀ A Y : ℕ, Xfirst ≤ A → A ≤ Y →
      |PrimeSums.fullLogReciprocalSum Y -
          PrimeSums.fullLogReciprocalSum A -
          (Real.log (Y : ℝ) - Real.log (A : ℝ))| ≤
        2 * Cfirst / Real.log (A : ℝ) ^ 3 +
          Cfirst / (2 * Real.log (A : ℝ) ^ 2) := by
    intro A Y hA hAY
    simpa only [Cfirst, Xfirst] using
      MovingLowMomentQuadrature.fullLogReciprocalSumUniform_bound A Y hA hAY
  have hSecond : ∀ z : ℝ, 1 < z → ∀ A Y : ℕ,
      Xsecond ≤ A → A ≤ Y →
      |KernelPrimeQuadrature.fullWeightedReciprocalSum
            PrimeCoordinateSecondMoment.squareCoordinate z Y -
          KernelPrimeQuadrature.fullWeightedReciprocalSum
            PrimeCoordinateSecondMoment.squareCoordinate z A -
          ((realLogCoordinate z (Y : ℝ) ^ 2 -
            realLogCoordinate z (A : ℝ) ^ 2) / 2)| ≤
        3 * Csecond / (Real.log z ^ 2 * Real.log (A : ℝ)) := by
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
  have hEndpoint := eventually_endpointMomentBounds M hdelta W
    Cmass Cfirst Csecond (by omega : 1 < W)
  filter_upwards [hEndpoint] with n R
  let hn : 1 < n := R.n_gt_one
  refine ⟨hWne, hn, ?_⟩
  intro S
  let P := canonicalPartition M hdelta hn hWne S
  let E := canonicalCertificate M hdelta hn hWne S
  have hReady := momentReady_of_endpointMomentBounds M P E
    (fun j ↦ rfl) (fun j ↦ rfl) hW8 hXmass hXfirst hXsecond
      hMass hFirst hSecond R
  have hL1 := actual_L1_bound_of_ready M P E
    (fun j ↦ rfl) (fun j ↦ rfl) hdelta hn hReady
  have hVarUpper := actual_variance_upper_of_ready M P E
    (fun j ↦ rfl) (fun j ↦ rfl) hdelta hn hReady
  have hLow := actual_low_bandVariance_lower_of_ready M P E
    (fun j ↦ rfl) hdelta hn hReady
  have hSup := actual_deviation_sup_le_scale M P E
    (fun j ↦ rfl) (fun j ↦ rfl) hdelta hn
  exact ⟨hSup, hL1, hLow, hVarUpper⟩









end GenericFirstMomentMesh

section DiagonalMesh

variable {delta : ℝ} (M : Mesh delta delta)





end DiagonalMesh

end Mesh
end Erdos390.Full.RegularMeshPrimeCutoffs

end

/- Source module: Erdos390.Full.PaperCanonicalPositiveCellVarianceEventually -/
section


/-!
# Positive-cell variance on an arbitrary regular relative mesh

The moving low cell alone controls the paper scale only when the positive
relative width is no larger than the low endpoint.  This file supplies the
missing complementary estimate: the sum of the literal within-cell prime
variances in the positive cells is bounded below by a fixed multiple of the
square of the actual common mesh ratio.  The proof first identifies the
finite prime moments with three unconditional PNT quadratures and then
passes to the exact continuum cell variance.
-/

open scoped BigOperators
open Filter Topology

noncomputable section

namespace Erdos390.Full.RegularMeshPrimeCutoffs

open ArithmeticModel ArithmeticBandGeometry RegularRelativeMesh
open PositiveCellTransfer KernelPrimeQuadrature PrimeBandQuadrature
open PrimeCoordinateSecondMoment MovingLowMomentQuadrature

namespace Mesh

variable {delta eta : ℝ} (M : Mesh delta eta)



/-- The first two positive terms of the symmetric power series for
`log (1+r)` already retain the cubic information needed for variance. -/
theorem twoTerm_log_one_add_lower :
    2 * (M.ratio / (M.ratio + 2)) +
        (2 / 3 : ℝ) * (M.ratio / (M.ratio + 2)) ^ 3 ≤
      Real.log (1 + M.ratio) := by
  let f : ℕ → ℝ := fun k ↦
    2 * (1 / (2 * (k : ℝ) + 1)) *
      (M.ratio / (M.ratio + 2)) ^ (2 * k + 1)
  have hs : HasSum f (Real.log (1 + M.ratio)) := by
    simpa only [f] using Real.hasSum_log_one_add M.ratio_pos.le
  have hsum := hs.summable.sum_le_tsum (Finset.range 2) (fun k hk ↦ by
    dsimp only [f]
    have hden : 0 ≤ 2 * (k : ℝ) + 1 := by positivity
    have hbase : 0 ≤ M.ratio / (M.ratio + 2) :=
      div_nonneg M.ratio_pos.le (by linarith [M.ratio_pos])
    exact mul_nonneg (mul_nonneg (by norm_num) (one_div_nonneg.mpr hden))
      (pow_nonneg hbase _))
  rw [hs.tsum_eq] at hsum
  norm_num [f, Finset.sum_range_succ] at hsum
  convert hsum using 1

/-- Cubic lower bound for the continuum variance in one geometric cell.
The numerical constant is deliberately coarse and uniform. -/
theorem lower_sq_mul_ratio_cube_div_le_idealPositiveBandVariance
    (hdelta : 0 < delta) (hratioOne : M.ratio ≤ 1)
    (k : Fin M.cellCount) :
    M.lower k ^ 2 * M.ratio ^ 3 / 28 ≤
      idealPositiveBandVariance M k := by
  let r : ℝ := M.ratio
  let a : ℝ := M.lower k
  let x : ℝ := r / (r + 2)
  let H₀ : ℝ := 2 * x + (2 / 3 : ℝ) * x ^ 3
  have hr : 0 < r := M.ratio_pos
  have hra : r ≤ 1 := hratioOne
  have ha : 0 < a := M.lower_pos hdelta k
  have hx : 0 < x := by
    dsimp only [x, r]
    exact div_pos M.ratio_pos (by linarith [M.ratio_pos])
  have hH₀ : 0 < H₀ := by
    dsimp only [H₀]
    positivity
  have hH₀le : H₀ ≤ Real.log (1 + r) := by
    simpa only [H₀, x, r] using twoTerm_log_one_add_lower M
  have hlog : 0 < Real.log (1 + r) :=
    Real.log_pos (by linarith [hr])
  have hquot : r ^ 2 / Real.log (1 + r) ≤ r ^ 2 / H₀ :=
    div_le_div_of_nonneg_left (sq_nonneg r) hH₀ hH₀le
  have hformula :
      r + r ^ 2 / 2 - r ^ 2 / H₀ =
        r ^ 3 * (r + 2) / (8 * (r ^ 2 + 3 * r + 3)) := by
    dsimp only [H₀, x]
    have hr2 : r + 2 ≠ 0 := by linarith
    have hpoly : r ^ 2 + 3 * r + 3 ≠ 0 := by nlinarith [sq_nonneg r]
    field_simp [hr2, hpoly]
    ring
  have hrsq : r ^ 2 ≤ r := by nlinarith [mul_nonneg hr.le (by linarith : 0 ≤ 1 - r)]
  have hpolyUpper : r ^ 2 + 3 * r + 3 ≤ 7 := by linarith
  have hdenPos : 0 < 8 * (r ^ 2 + 3 * r + 3) := by
    positivity
  have hcoarse : r ^ 3 / 28 ≤
      r ^ 3 * (r + 2) / (8 * (r ^ 2 + 3 * r + 3)) := by
    rw [le_div_iff₀ hdenPos]
    have hrCube : 0 ≤ r ^ 3 := by positivity
    nlinarith
  have hscalar : r ^ 3 / 28 ≤
      r + r ^ 2 / 2 - r ^ 2 / Real.log (1 + r) := by
    have hH₀scalar : r ^ 3 / 28 ≤
        r + r ^ 2 / 2 - r ^ 2 / H₀ := hcoarse.trans_eq hformula.symm
    linarith
  have hupper : M.upper k = a * (1 + r) := by
    dsimp only [a, r]
    unfold RegularRelativeMesh.Mesh.upper RegularRelativeMesh.Mesh.lower
    exact M.endpoint_succ k.1
  have hwidth : M.width k = r * a := by
    dsimp only [r, a]
    exact M.width_eq_ratio_mul_lower k
  have hmass : M.cellHarmonicMass k = Real.log (1 + r) := by
    simpa only [r] using M.cellHarmonicMass_eq_log_one_add_ratio hdelta k
  rw [idealPositiveBandVariance, hupper, hwidth, hmass]
  have haSq : 0 ≤ a ^ 2 := sq_nonneg a
  calc
    a ^ 2 * r ^ 3 / 28 = a ^ 2 * (r ^ 3 / 28) := by ring
    _ ≤ a ^ 2 *
        (r + r ^ 2 / 2 - r ^ 2 / Real.log (1 + r)) :=
      mul_le_mul_of_nonneg_left hscalar haSq
    _ = ((a * (1 + r)) ^ 2 - a ^ 2) / 2 -
        (r * a) ^ 2 / Real.log (1 + r) := by ring

/-- The squared endpoint increments telescope over the entire positive
mesh, just as the ordinary widths do. -/
theorem sum_upper_sq_sub_lower_sq :
    ∑ k : Fin M.cellCount, (M.upper k ^ 2 - M.lower k ^ 2) =
      1 - delta ^ 2 := by
  change (∑ k : Fin M.cellCount,
      (fun i : ℕ ↦ M.endpoint (i + 1) ^ 2 - M.endpoint i ^ 2) k.1) =
    1 - delta ^ 2
  calc
    (∑ k : Fin M.cellCount,
        (fun i : ℕ ↦ M.endpoint (i + 1) ^ 2 - M.endpoint i ^ 2) k.1) =
        ∑ k ∈ Finset.range M.cellCount,
          (M.endpoint (k + 1) ^ 2 - M.endpoint k ^ 2) :=
      Fin.sum_univ_eq_sum_range
        (fun i : ℕ ↦ M.endpoint (i + 1) ^ 2 - M.endpoint i ^ 2)
          M.cellCount
    _ = 1 - delta ^ 2 := by
      have htel := Finset.sum_range_sub
        (fun i : ℕ ↦ M.endpoint i ^ 2) M.cellCount
      rw [M.endpoint_cellCount, M.endpoint_zero] at htel
      norm_num at htel
      rw [Finset.sum_sub_distrib]
      exact htel

/-- Summing the one-cell cubic estimate gives a quadratic lower bound in
the actual common mesh ratio. -/
theorem ratio_sq_div_le_sum_idealPositiveBandVariance
    (hdelta : 0 < delta) (hdeltaHalf : delta ≤ (1 : ℝ) / 2)
    (hratioOne : M.ratio ≤ 1) :
    M.ratio ^ 2 / 112 ≤
      ∑ k : Fin M.cellCount, idealPositiveBandVariance M k := by
  have hcell (k : Fin M.cellCount) :
      M.lower k ^ 2 * M.ratio ^ 3 / 28 =
        (M.ratio ^ 2 / (28 * (M.ratio + 2))) *
          (M.upper k ^ 2 - M.lower k ^ 2) := by
    have hupper : M.upper k = M.lower k * (1 + M.ratio) := by
      unfold RegularRelativeMesh.Mesh.upper RegularRelativeMesh.Mesh.lower
      exact M.endpoint_succ k.1
    rw [hupper]
    have hden : M.ratio + 2 ≠ 0 := by linarith [M.ratio_pos]
    field_simp [hden]
    ring
  have hsumLower :
      (∑ k : Fin M.cellCount,
          M.lower k ^ 2 * M.ratio ^ 3 / 28) ≤
        ∑ k : Fin M.cellCount, idealPositiveBandVariance M k := by
    exact Finset.sum_le_sum fun k hk ↦
      lower_sq_mul_ratio_cube_div_le_idealPositiveBandVariance
        M hdelta hratioOne k
  have hsumIdentity :
      (∑ k : Fin M.cellCount,
          M.lower k ^ 2 * M.ratio ^ 3 / 28) =
        M.ratio ^ 2 * (1 - delta ^ 2) /
          (28 * (M.ratio + 2)) := by
    calc
      (∑ k : Fin M.cellCount,
          M.lower k ^ 2 * M.ratio ^ 3 / 28) =
          ∑ k : Fin M.cellCount,
            (M.ratio ^ 2 / (28 * (M.ratio + 2))) *
              (M.upper k ^ 2 - M.lower k ^ 2) := by
        apply Finset.sum_congr rfl
        intro k hk
        exact hcell k
      _ = (M.ratio ^ 2 / (28 * (M.ratio + 2))) *
          (∑ k : Fin M.cellCount,
            (M.upper k ^ 2 - M.lower k ^ 2)) := by
        rw [Finset.mul_sum]
      _ = M.ratio ^ 2 * (1 - delta ^ 2) /
          (28 * (M.ratio + 2)) := by
        rw [sum_upper_sq_sub_lower_sq M]
        ring
  have hdeltaSq : delta ^ 2 ≤ (1 : ℝ) / 4 := by
    nlinarith [sq_nonneg delta]
  have hdenPos : 0 < 28 * (M.ratio + 2) := by
    exact mul_pos (by norm_num) (by linarith [M.ratio_pos])
  have hcoarse : M.ratio ^ 2 / 112 ≤
      M.ratio ^ 2 * (1 - delta ^ 2) /
        (28 * (M.ratio + 2)) := by
    rw [le_div_iff₀ hdenPos]
    have hrSq : 0 ≤ M.ratio ^ 2 := sq_nonneg _
    nlinarith
  rw [← hsumIdentity] at hcoarse
  exact hcoarse.trans hsumLower











private theorem tendsto_of_abs_sub_le
    {f g e : ℕ → ℝ} {a : ℝ}
    (hg : Tendsto g atTop (nhds a)) (he : Tendsto e atTop (nhds 0))
    (hbound : ∀ᶠ n : ℕ in atTop, |f n - g n| ≤ e n) :
    Tendsto f atTop (nhds a) := by
  have habs : Tendsto (fun n ↦ |f n - g n|) atTop (nhds 0) :=
    squeeze_zero' (Filter.Eventually.of_forall (fun n ↦ abs_nonneg _))
      hbound he
  have hdiff : Tendsto (fun n ↦ f n - g n) atTop (nhds 0) :=
    tendsto_zero_iff_norm_tendsto_zero.mpr (by
      simpa only [Real.norm_eq_abs] using habs)
  have hadd := hdiff.add hg
  simpa only [sub_add_cancel, zero_add] using hadd

theorem tendsto_positiveContinuumSecond
    (hdelta : 0 < delta) (W : ℕ) (k : Fin M.cellCount) :
    Tendsto (fun n : ℕ ↦ positiveContinuumSecond M n W k) atTop
      (nhds ((M.upper k ^ 2 - M.lower k ^ 2) / 2)) := by
  have hLower := (tendsto_positive_lowerCoordinate M hdelta W k).pow 2
  have hUpper := (tendsto_positive_upperCoordinate M hdelta W k).pow 2
  simpa only [positiveContinuumSecond] using
    (hUpper.sub hLower).div_const (2 : ℝ)

theorem tendsto_positiveSecondError_zero
    (C : ℝ) (W : ℕ) (k : Fin M.cellCount) :
    Tendsto (fun n : ℕ ↦
      3 * C /
        (Real.log (y n) ^ 2 *
          Real.log (fullCutoff M n W (k.1 + 1) : ℝ)))
      atTop (nhds 0) := by
  have hInvY : Tendsto (fun n : ℕ ↦ (Real.log (y n))⁻¹)
      atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp tendsto_log_y_atTop
  have hLowerReal : Tendsto (fun n : ℕ ↦
      (fullCutoff M n W (k.1 + 1) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp
      (tendsto_positive_lowerCutoff_atTop M (by
        have hdelta : 0 < delta := by
          have hbase : 0 < (1 + M.ratio) ^ M.cellCount :=
            pow_pos (by linarith [M.ratio_pos]) M.cellCount
          nlinarith [M.lastEndpoint]
        exact hdelta) W k)
  have hInvA : Tendsto (fun n : ℕ ↦
      (Real.log (fullCutoff M n W (k.1 + 1) : ℝ))⁻¹)
      atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp (Real.tendsto_log_atTop.comp hLowerReal)
  have hMain :=
    ((tendsto_const_nhds : Tendsto (fun _n : ℕ ↦ 3 * C) atTop
      (nhds (3 * C))).mul (hInvY.pow 2)).mul hInvA
  convert hMain using 1 <;> ring

/-- Literal reciprocal mass in a fixed positive cell converges to its
harmonic continuum mass. -/
theorem tendsto_canonicalPositiveMassValue
    (hdelta : 0 < delta) {W : ℕ}
    (hW : canonicalMassQuadratureCutoff ≤ W)
    (k : Fin M.cellCount) :
    Tendsto (fun n : ℕ ↦ canonicalPositiveMassValue M n W k) atTop
      (nhds (M.cellHarmonicMass k)) := by
  have hMain : Tendsto (fun n : ℕ ↦
      endpointContinuumMass M n W (positiveBand M k)) atTop
      (nhds (M.cellHarmonicMass k)) := by
    have hEq : M.cellHarmonicMass k =
        Real.log (M.upper k) - Real.log (M.lower k) := by
      unfold RegularRelativeMesh.Mesh.cellHarmonicMass
      rw [Real.log_div
        (ne_of_gt ((M.lower_pos hdelta k).trans (M.lower_lt_upper hdelta k)))
        (ne_of_gt (M.lower_pos hdelta k))]
    rw [hEq]
    exact tendsto_positive_endpointContinuumMass M hdelta W k
  have hError := tendsto_positive_massError_zero M hdelta W
    canonicalMassQuadratureConstant k
  have hBound : ∀ᶠ n : ℕ in atTop,
      |canonicalPositiveMassValue M n W k -
        endpointContinuumMass M n W (positiveBand M k)| ≤
          5 * canonicalMassQuadratureConstant /
            Real.log (fullCutoff M n W (k.1 + 1) : ℝ) ^ 3 := by
    filter_upwards [eventually_gt_atTop 1,
      eventually_scaleSeparation M hdelta W] with n hn S
    have hmono := fullCutoff_monotone M hdelta hn
      (W_le_first_fullCutoff M S)
    have hA : canonicalMassQuadratureCutoff ≤
        fullCutoff M n W (k.1 + 1) :=
      hW.trans ((W_le_first_fullCutoff M S).trans
        (hmono (by omega : 1 ≤ k.1 + 1)))
    have hAY : fullCutoff M n W (k.1 + 1) ≤
        fullCutoff M n W (k.1 + 2) := hmono (by omega)
    have hq := canonicalMassQuadratureBound
      (fullCutoff M n W (k.1 + 1))
      (fullCutoff M n W (k.1 + 2)) hA hAY
    simpa only [canonicalPositiveMassValue, endpointContinuumMass,
      positiveBand, Fin.val_succ] using hq
  exact tendsto_of_abs_sub_le hMain hError hBound

/-- Literal first logarithmic prime moment in a fixed positive cell
converges to the cell width. -/
theorem tendsto_canonicalPositiveFirstValue
    (hdelta : 0 < delta) {W : ℕ}
    (hWtwo : 2 ≤ W)
    (hW : fullLogReciprocalSumUniformCutoff ≤ W)
    (k : Fin M.cellCount) :
    Tendsto (fun n : ℕ ↦ canonicalPositiveFirstValue M n W k) atTop
      (nhds (M.width k)) := by
  have hMain := tendsto_positive_endpointContinuumMoment M hdelta W k
  have hError := tendsto_positive_endpointMomentError_zero M hdelta
    fullLogReciprocalSumUniformConstant W k
  have hBound : ∀ᶠ n : ℕ in atTop,
      |canonicalPositiveFirstValue M n W k -
        endpointContinuumMoment M n W (positiveBand M k)| ≤
          endpointMomentError M fullLogReciprocalSumUniformConstant
            n W (positiveBand M k) := by
    filter_upwards [eventually_gt_atTop 1,
      eventually_scaleSeparation M hdelta W] with n hn S
    have hWne : W ≠ 0 := by omega
    have hq :=
      abs_canonical_mass_mul_center_sub_endpointContinuumMoment_le
        M hdelta hn hWne S fullLogReciprocalSumUniform_bound hW
          (positiveBand M k)
    let P := canonicalPartition M hdelta hn hWne S
    let E := canonicalCertificate M hdelta hn hWne S
    have hfirst : P.mass (positiveBand M k) *
        P.center (positiveBand M k) =
          canonicalPositiveFirstValue M n W k := by
      rw [E.mass_mul_center_eq_fullLogReciprocalSum_sub]
      rfl
    change |P.mass (positiveBand M k) * P.center (positiveBand M k) -
      endpointContinuumMoment M n W (positiveBand M k)| ≤
        endpointMomentError M fullLogReciprocalSumUniformConstant
          n W (positiveBand M k) at hq
    rw [hfirst] at hq
    exact hq
  exact tendsto_of_abs_sub_le hMain hError hBound

/-- Literal second logarithmic prime moment in a fixed positive cell
converges to the corresponding continuum second moment. -/
theorem tendsto_canonicalPositiveSecondValue
    (hdelta : 0 < delta) {W : ℕ}
    (hW : canonicalSecondMomentCutoff ≤ W)
    (k : Fin M.cellCount) :
    Tendsto (fun n : ℕ ↦ canonicalPositiveSecondValue M n W k) atTop
      (nhds ((M.upper k ^ 2 - M.lower k ^ 2) / 2)) := by
  have hMain := tendsto_positiveContinuumSecond M hdelta W k
  have hError := tendsto_positiveSecondError_zero M
    canonicalSecondMomentConstant W k
  have hBound : ∀ᶠ n : ℕ in atTop,
      |canonicalPositiveSecondValue M n W k -
        positiveContinuumSecond M n W k| ≤
          3 * canonicalSecondMomentConstant /
            (Real.log (y n) ^ 2 *
              Real.log (fullCutoff M n W (k.1 + 1) : ℝ)) := by
    filter_upwards [eventually_gt_atTop 1,
      eventually_scaleSeparation M hdelta W] with n hn S
    have hmono := fullCutoff_monotone M hdelta hn
      (W_le_first_fullCutoff M S)
    have hA : canonicalSecondMomentCutoff ≤
        fullCutoff M n W (k.1 + 1) :=
      hW.trans ((W_le_first_fullCutoff M S).trans
        (hmono (by omega : 1 ≤ k.1 + 1)))
    have hAY : fullCutoff M n W (k.1 + 1) ≤
        fullCutoff M n W (k.1 + 2) := hmono (by omega)
    have hq := canonicalSecondMomentBound (y n) (y_gt_one hn)
      (fullCutoff M n W (k.1 + 1))
      (fullCutoff M n W (k.1 + 2)) hA hAY
    simpa only [canonicalPositiveSecondValue, positiveContinuumSecond,
      cutoffCoordinate] using hq
  exact tendsto_of_abs_sub_le hMain hError hBound

/-- The exact prime-sum variance of a fixed positive cell converges to its
continuum harmonic variance. -/
theorem tendsto_canonicalPositiveVarianceValue
    (hdelta : 0 < delta) {W : ℕ}
    (hW : canonicalActualMomentCutoff ≤ W)
    (k : Fin M.cellCount) :
    Tendsto (fun n : ℕ ↦ canonicalPositiveVarianceValue M n W k) atTop
      (nhds (idealPositiveBandVariance M k)) := by
  have hW8 : 8 ≤ W :=
    (le_max_left 8 (max canonicalMassQuadratureCutoff
      (max fullLogReciprocalSumUniformCutoff
        canonicalSecondMomentCutoff))).trans hW
  have hMassCutoff : canonicalMassQuadratureCutoff ≤ W :=
    ((le_max_left canonicalMassQuadratureCutoff
      (max fullLogReciprocalSumUniformCutoff canonicalSecondMomentCutoff)).trans
      (le_max_right 8 (max canonicalMassQuadratureCutoff
        (max fullLogReciprocalSumUniformCutoff
          canonicalSecondMomentCutoff)))).trans hW
  have hFirstCutoff : fullLogReciprocalSumUniformCutoff ≤ W :=
    ((le_max_left fullLogReciprocalSumUniformCutoff
      canonicalSecondMomentCutoff).trans
      ((le_max_right canonicalMassQuadratureCutoff
        (max fullLogReciprocalSumUniformCutoff canonicalSecondMomentCutoff)).trans
        (le_max_right 8 (max canonicalMassQuadratureCutoff
          (max fullLogReciprocalSumUniformCutoff
            canonicalSecondMomentCutoff))))).trans hW
  have hSecondCutoff : canonicalSecondMomentCutoff ≤ W :=
    ((le_max_right fullLogReciprocalSumUniformCutoff
      canonicalSecondMomentCutoff).trans
      ((le_max_right canonicalMassQuadratureCutoff
        (max fullLogReciprocalSumUniformCutoff canonicalSecondMomentCutoff)).trans
        (le_max_right 8 (max canonicalMassQuadratureCutoff
          (max fullLogReciprocalSumUniformCutoff
            canonicalSecondMomentCutoff))))).trans hW
  have hMass := tendsto_canonicalPositiveMassValue M hdelta hMassCutoff k
  have hFirst := tendsto_canonicalPositiveFirstValue M hdelta
    (by omega : 2 ≤ W) hFirstCutoff k
  have hSecond := tendsto_canonicalPositiveSecondValue M hdelta
    hSecondCutoff k
  have hMassPos : 0 < M.cellHarmonicMass k :=
    M.cellHarmonicMass_pos hdelta k
  have hQuot := (hFirst.pow 2).div hMass (ne_of_gt hMassPos)
  simpa only [canonicalPositiveVarianceValue, idealPositiveBandVariance]
    using hSecond.sub hQuot

/-- Summed convergence over the finite positive mesh. -/
theorem tendsto_sum_canonicalPositiveVarianceValue
    (hdelta : 0 < delta) {W : ℕ}
    (hW : canonicalActualMomentCutoff ≤ W) :
    Tendsto (fun n : ℕ ↦
      ∑ k : Fin M.cellCount, canonicalPositiveVarianceValue M n W k)
      atTop (nhds (∑ k : Fin M.cellCount,
        idealPositiveBandVariance M k)) := by
  exact tendsto_finset_sum Finset.univ (fun k hk ↦
    tendsto_canonicalPositiveVarianceValue M hdelta hW k)

/-- The actual prime-sum positive variance eventually retains half of the
uniform continuum lower bound. -/
theorem eventually_ratio_sq_div_le_sum_canonicalPositiveVarianceValue
    (hdelta : 0 < delta) (hdeltaHalf : delta ≤ (1 : ℝ) / 2)
    (hratioOne : M.ratio ≤ 1) {W : ℕ}
    (hW : canonicalActualMomentCutoff ≤ W) :
    ∀ᶠ n : ℕ in atTop,
      M.ratio ^ 2 / 224 ≤
        ∑ k : Fin M.cellCount,
          canonicalPositiveVarianceValue M n W k := by
  have hLimit := tendsto_sum_canonicalPositiveVarianceValue M hdelta hW
  have hIdeal := ratio_sq_div_le_sum_idealPositiveBandVariance M hdelta
    hdeltaHalf hratioOne
  have hStrict : M.ratio ^ 2 / 224 <
      ∑ k : Fin M.cellCount, idealPositiveBandVariance M k := by
    have hrSqPos : 0 < M.ratio ^ 2 := sq_pos_of_pos M.ratio_pos
    exact (by nlinarith : M.ratio ^ 2 / 224 < M.ratio ^ 2 / 112).trans_le
      hIdeal
  exact hLimit.eventually (eventually_ge_nhds hStrict)

/-- Identification of the prime-sum proxy with the literal variance of a
canonical positive band. -/
theorem canonical_bandVariance_positive_eq_value
    {n W : ℕ} (hdelta : 0 < delta) (hn : 1 < n) (hWne : W ≠ 0)
    (S : ScaleSeparation M n W) (k : Fin M.cellCount) :
    let P := canonicalPartition M hdelta hn hWne S
    P.bandVariance (positiveBand M k) =
      canonicalPositiveVarianceValue M n W k := by
  let P := canonicalPartition M hdelta hn hWne S
  let E := canonicalCertificate M hdelta hn hWne S
  dsimp only
  have hMass : P.mass (positiveBand M k) =
      canonicalPositiveMassValue M n W k := by
    rw [E.mass_eq_fullReciprocalSum_sub]
    rfl
  have hFirst : P.mass (positiveBand M k) *
      P.center (positiveBand M k) =
        canonicalPositiveFirstValue M n W k := by
    rw [E.mass_mul_center_eq_fullLogReciprocalSum_sub]
    rfl
  have hSecond : P.bandSecondMoment (positiveBand M k) =
      canonicalPositiveSecondValue M n W k := by
    rw [P.bandSecondMoment_eq_fullWeightedReciprocalSum_sub E]
    rfl
  rw [P.bandVariance_eq_second_sub_mass_center_sq, hSecond]
  unfold canonicalPositiveVarianceValue
  rw [← hMass, ← hFirst]
  have hMassNe : P.mass (positiveBand M k) ≠ 0 :=
    ne_of_gt (P.data.mass_pos (positiveBand M k))
  field_simp [hMassNe]

/-- Paper-order eventual form of the literal positive-cell variance lower.
The global cutoff is fixed before the mesh; only the ambient threshold may
depend on the fixed mesh. -/
theorem canonicalPositiveVarianceCutoff_eventually
    (hdelta : 0 < delta) (hdeltaHalf : delta ≤ (1 : ℝ) / 2)
    (hratioOne : M.ratio ≤ 1) :
    ∀ W : ℕ, canonicalActualMomentCutoff ≤ W →
      ∀ᶠ n : ℕ in atTop,
        ∃ hWne : W ≠ 0, ∃ hn : 1 < n,
          ∀ S : ScaleSeparation M n W,
            let P := canonicalPartition M hdelta hn hWne S
            M.ratio ^ 2 / 224 ≤
              ∑ k : Fin M.cellCount,
                P.bandVariance (positiveBand M k) := by
  intro W hW
  have hValue :=
    eventually_ratio_sq_div_le_sum_canonicalPositiveVarianceValue
      M hdelta hdeltaHalf hratioOne hW
  have hWne : W ≠ 0 := by
    have hW8 : 8 ≤ W :=
      (le_max_left 8 (max canonicalMassQuadratureCutoff
        (max fullLogReciprocalSumUniformCutoff
          canonicalSecondMomentCutoff))).trans hW
    omega
  filter_upwards [hValue, eventually_gt_atTop 1] with n hValueN hn
  refine ⟨hWne, hn, ?_⟩
  intro S
  let P := canonicalPartition M hdelta hn hWne S
  calc
    M.ratio ^ 2 / 224 ≤
        ∑ k : Fin M.cellCount,
          canonicalPositiveVarianceValue M n W k := hValueN
    _ = ∑ k : Fin M.cellCount,
        P.bandVariance (positiveBand M k) := by
      apply Finset.sum_congr rfl
      intro k hk
      exact (canonical_bandVariance_positive_eq_value M hdelta hn hWne S k).symm

/-- The fixed interior prime mass gives a mesh-independent lower floor for
the literal arithmetic centre energy. -/
theorem one_div_64_le_centerEnergy_of_canonical_anchor
    {n W : ℕ} (hdelta : 0 < delta)
    (hn : 1 < n) (hWne : W ≠ 0) (S : ScaleSeparation M n W)
    (anchors : Finset (Fin M.cellCount))
    (hinterior : ∀ p ∈ canonicalPrimeAnchorSet M
        (canonicalPartition M hdelta hn hWne S) anchors,
      tPrime n p.1 ∈ Set.Icc ((1 : ℝ) / 8) (1 - (1 : ℝ) / 8))
    (hAnchorMass : (1 : ℝ) / 8 ≤
      FiniteAnchoredDirichletQuadratic.anchorMass
        (PrimeSquarefreeDirichletGeometry.primeWeight n)
        (canonicalPrimeAnchorSet M
          (canonicalPartition M hdelta hn hWne S) anchors)) :
    (1 : ℝ) / 64 ≤
      (canonicalPartition M hdelta hn hWne S).centerEnergy := by
  let P := canonicalPartition M hdelta hn hWne S
  have hEnergy := epsilon_mul_anchorMass_le_centerEnergy M P hn
    (by norm_num : (0 : ℝ) ≤ 1 / 8) anchors hinterior
  calc
    (1 : ℝ) / 64 = (1 / 8 : ℝ) * (1 / 8 : ℝ) := by norm_num
    _ ≤ (1 / 8 : ℝ) *
        FiniteAnchoredDirichletQuadratic.anchorMass
          (PrimeSquarefreeDirichletGeometry.primeWeight n)
          (canonicalPrimeAnchorSet M P anchors) := by
      exact mul_le_mul_of_nonneg_left hAnchorMass (by norm_num)
    _ ≤ P.centerEnergy := hEnergy

/-- Interior prime mass forces the center energy to dominate the within-cell
variance whenever the actual mesh scale is sufficiently small.  This form is
uniform for independent `delta` and `eta`. -/
theorem variance_le_centerEnergy_of_canonical_anchor_of_actualScale
    {n W : ℕ} (hdelta : 0 < delta)
    (hscaleSmall : delta + M.ratio ≤ (1 : ℝ) / 16)
    (hn : 1 < n) (hWne : W ≠ 0) (S : ScaleSeparation M n W)
    (anchors : Finset (Fin M.cellCount))
    (hinterior : ∀ p ∈ canonicalPrimeAnchorSet M
        (canonicalPartition M hdelta hn hWne S) anchors,
      tPrime n p.1 ∈ Set.Icc ((1 : ℝ) / 8) (1 - (1 : ℝ) / 8))
    (hAnchorMass : (1 : ℝ) / 8 ≤
      FiniteAnchoredDirichletQuadratic.anchorMass
        (PrimeSquarefreeDirichletGeometry.primeWeight n)
        (canonicalPrimeAnchorSet M
          (canonicalPartition M hdelta hn hWne S) anchors))
    (hVarUpper :
      (canonicalPartition M hdelta hn hWne S).variance ≤
        4 * (delta + M.ratio) ^ 2) :
    (canonicalPartition M hdelta hn hWne S).variance ≤
      (canonicalPartition M hdelta hn hWne S).centerEnergy := by
  let P := canonicalPartition M hdelta hn hWne S
  have hEnergyFloor : (1 : ℝ) / 64 ≤ P.centerEnergy := by
    exact one_div_64_le_centerEnergy_of_canonical_anchor M hdelta
      hn hWne S anchors hinterior hAnchorMass
  have hscaleNonneg : 0 ≤ delta + M.ratio :=
    (add_pos hdelta M.ratio_pos).le
  have hSmallVar : 4 * (delta + M.ratio) ^ 2 ≤ (1 : ℝ) / 64 := by
    nlinarith
  exact hVarUpper.trans (hSmallVar.trans hEnergyFloor)

end Mesh

end Erdos390.Full.RegularMeshPrimeCutoffs

end

/- Source module: Erdos390.Full.PaperCanonicalGeometricMomentFineMeshEventually -/
section


/-!
# Paper-scale geometric moment inputs on every permitted fine mesh

This file assembles the arithmetic estimates used after the continuum-to-band
transfer.  The structural prime cutoff and the numerical mesh tolerance are
chosen before the mesh.  The two mesh parameters remain independent: the
only comparison used is the two-sided regularity condition from the paper,
namely

`cMesh * eta ≤ M.ratio ≤ eta`.

The lower variance estimate deliberately combines two different arithmetic
sources.  The moving low cell controls `delta^2`, while the positive cells
control the square of the actual relative width `M.ratio`.  Thus no hidden
hypothesis such as `M.ratio ≤ delta` or `eta ≤ delta` is present.
-/

open scoped BigOperators
open Filter

noncomputable section

namespace Erdos390.Full.RegularMeshPrimeCutoffs

open ArithmeticModel ArithmeticBandGeometry RegularRelativeMesh
open PaperPermittedRegularMesh

namespace Mesh





/--
Uniform paper-scale geometric inputs for the literal canonical partition.

The order of the quantifiers is important.  After the fixed structural
constant `cMesh`, the cutoff `W` is selected before `delta`, `eta`, and the
mesh.  Only the eventual ambient threshold may depend on the fixed mesh.
-/
theorem canonicalPaperGeometricCutoff_eventually
    (cMesh : ℝ) (hcMesh : 0 < cMesh) :
    ∀ W : ℕ, canonicalPaperGeometricCutoff ≤ W →
      ∀ {delta eta : ℝ} (M : Mesh delta eta)
        (hdelta : 0 < delta)
        (_hPermitted : IsPermitted (cMesh := cMesh) M),
        delta + eta ≤ canonicalPaperGeometricMeshTolerance →
        ∀ᶠ n : ℕ in atTop,
          ∃ hWne : W ≠ 0, ∃ hn : 1 < n,
            ∀ S : ScaleSeparation M n W,
              let P := canonicalPartition M hdelta hn hWne S
              (∀ p : BandPrime n W,
                |P.deviation p| ≤ delta + eta) ∧
              P.totalL1 ≤ 7 * (delta + eta) ∧
              (delta + eta) ^ 2 ≤
                (456 / cMesh ^ 2) * P.variance ∧
              P.variance ≤ 4 * (delta + eta) ^ 2 ∧
              P.variance ≤ P.centerEnergy := by
  intro W hW delta eta M hdelta hPermitted hfine
  have hWmoment : canonicalActualMomentCutoff ≤ W :=
    (le_max_left canonicalActualMomentCutoff
      canonicalPrimeAnchorCutoff).trans hW
  have hWanchor : canonicalPrimeAnchorCutoff ≤ W :=
    (le_max_right canonicalActualMomentCutoff
      canonicalPrimeAnchorCutoff).trans hW
  have heta : 0 < eta := IsPermitted.eta_pos M
  have hdeltaSmall : delta < (1 : ℝ) / 16 := by
    dsimp only [canonicalPaperGeometricMeshTolerance] at hfine
    linarith
  have hratioSmall : M.ratio < (1 : ℝ) / 16 := by
    dsimp only [canonicalPaperGeometricMeshTolerance] at hfine
    linarith [M.ratio_le_eta]
  have hwidthSmall : ∀ k : Fin M.cellCount,
      M.width k < (1 : ℝ) / 16 := by
    intro k
    exact (M.width_le_ratio hdelta k).trans_lt hratioSmall
  have hdeltaHalf : delta ≤ (1 : ℝ) / 2 := by linarith
  have hratioOne : M.ratio ≤ 1 := by linarith
  have hActualPaper : delta + M.ratio ≤ delta + eta :=
    IsPermitted.actualScale_le_paperScale
  have hActualSmall : delta + M.ratio ≤ (1 : ℝ) / 16 := by
    dsimp only [canonicalPaperGeometricMeshTolerance] at hfine
    exact hActualPaper.trans hfine
  obtain ⟨anchors, anchor, hanchor, hIdealLower, hIdealUpper, hIdealMass⟩ :=
    M.exists_interiorAnchorBlock hdelta hdeltaSmall hwidthSmall
  have hAnchors : anchors.Nonempty := ⟨anchor, hanchor⟩
  have hMoment :=
    canonicalActualPreliminaryMomentCutoff_eventually M hdelta W hWmoment
  have hPositive := canonicalPositiveVarianceCutoff_eventually M hdelta
    hdeltaHalf hratioOne W hWmoment
  have hPrimeAnchor := canonicalPrimeAnchorCutoff_eventually M hdelta
    W hWanchor (epsilon := (1 / 8 : ℝ)) anchors hAnchors
      hIdealLower hIdealUpper hIdealMass
  filter_upwards [hMoment, hPositive, hPrimeAnchor] with
      n hMomentAt hPositiveAt hAnchorAt
  obtain ⟨hWm, hnm, hMomentAll⟩ := hMomentAt
  obtain ⟨hWp, hnp, hPositiveAll⟩ := hPositiveAt
  obtain ⟨hWa, hna, hAnchorAll⟩ := hAnchorAt
  refine ⟨hWm, hnm, ?_⟩
  intro S
  let P := canonicalPartition M hdelta hnm hWm S
  obtain ⟨hSupActual, hL1Actual, hLowBand, hVarUpperActual⟩ :=
    hMomentAll S
  have hPositiveRaw := hPositiveAll S
  have hPositiveCells : M.ratio ^ 2 / 224 ≤
      ∑ k : Fin M.cellCount,
        P.bandVariance (positiveBand M k) := by
    simpa only [P, Subsingleton.elim hnp hnm,
      Subsingleton.elim hWp hWm] using hPositiveRaw
  obtain ⟨hInteriorRaw, hAnchorMassRaw⟩ := hAnchorAll S
  have hInterior : ∀ p ∈ canonicalPrimeAnchorSet M P anchors,
      tPrime n p.1 ∈
        Set.Icc ((1 : ℝ) / 8) (1 - (1 : ℝ) / 8) := by
    simpa only [P, Subsingleton.elim hna hnm,
      Subsingleton.elim hWa hWm] using hInteriorRaw
  have hAnchorMass : (1 : ℝ) / 8 ≤
      FiniteAnchoredDirichletQuadratic.anchorMass
        (PrimeSquarefreeDirichletGeometry.primeWeight n)
        (canonicalPrimeAnchorSet M P anchors) := by
    simpa only [P, Subsingleton.elim hna hnm,
      Subsingleton.elim hWa hWm] using hAnchorMassRaw
  have hBandVarNonneg (j : Fin (M.cellCount + 1)) :
      0 ≤ P.bandVariance j := by
    unfold ArithmeticBandGeometry.Partition.bandVariance
    exact Finset.sum_nonneg fun p hp ↦
      mul_nonneg (by positivity) (sq_nonneg _)
  have hVarianceSplit : P.variance =
      P.bandVariance 0 +
        ∑ k : Fin M.cellCount, P.bandVariance k.succ := by
    rw [P.variance_eq_sum_bandVariance, Fin.sum_univ_succ]
  have hPositiveCells' : M.ratio ^ 2 / 224 ≤
      ∑ k : Fin M.cellCount, P.bandVariance k.succ := by
    simpa only [positiveBand] using hPositiveCells
  have hPositiveSumNonneg : 0 ≤
      ∑ k : Fin M.cellCount, P.bandVariance k.succ :=
    Finset.sum_nonneg fun k hk ↦ hBandVarNonneg k.succ
  have hLowTotal : delta ^ 2 / 4 ≤ P.variance := by
    rw [hVarianceSplit]
    linarith
  have hPositiveTotal : M.ratio ^ 2 / 224 ≤ P.variance := by
    rw [hVarianceSplit]
    exact hPositiveCells'.trans
      (le_add_of_nonneg_left (hBandVarNonneg 0))
  have hPaperLower : (delta + eta) ^ 2 ≤
      (456 / cMesh ^ 2) * P.variance :=
    IsPermitted.paperScale_sq_le_of_low_and_positive
      hdelta.le hcMesh hPermitted hLowTotal hPositiveTotal
  have hSupPaper : ∀ p : BandPrime n W,
      |P.deviation p| ≤ delta + eta := fun p ↦
    (hSupActual p).trans hActualPaper
  have hL1Paper : P.totalL1 ≤ 7 * (delta + eta) :=
    hL1Actual.trans
      (mul_le_mul_of_nonneg_left hActualPaper (by norm_num))
  have hActualNonneg : 0 ≤ delta + M.ratio :=
    (add_pos hdelta M.ratio_pos).le
  have hPaperNonneg : 0 ≤ delta + eta :=
    (add_pos hdelta heta).le
  have hScaleSq : (delta + M.ratio) ^ 2 ≤ (delta + eta) ^ 2 :=
    (sq_le_sq₀ hActualNonneg hPaperNonneg).2 hActualPaper
  have hVarUpperPaper : P.variance ≤ 4 * (delta + eta) ^ 2 :=
    hVarUpperActual.trans
      (mul_le_mul_of_nonneg_left hScaleSq (by norm_num))
  have hCenter : P.variance ≤ P.centerEnergy :=
    variance_le_centerEnergy_of_canonical_anchor_of_actualScale M hdelta
      hActualSmall hnm hWm S anchors hInterior hAnchorMass hVarUpperActual
  exact ⟨hSupPaper, hL1Paper, hPaperLower, hVarUpperPaper, hCenter⟩





end Mesh

end Erdos390.Full.RegularMeshPrimeCutoffs

end

theorem solution :
∀ (cMesh : Real),
  @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) cMesh →
    ∀ (W : Nat),
      @LE.le.{0} Nat instLENat Erdos390.Full.RegularMeshPrimeCutoffs.Mesh.canonicalPaperGeometricCutoff W →
        ∀ {delta eta : Real} (M : Erdos390.Full.RegularRelativeMesh.Mesh delta eta)
          (hdelta :
            @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
              delta),
          @Erdos390.Full.PaperPermittedRegularMesh.IsPermitted delta eta cMesh M →
            @LE.le.{0} Real Real.instLE
                (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) delta eta)
                Erdos390.Full.RegularMeshPrimeCutoffs.Mesh.canonicalPaperGeometricMeshTolerance →
              @Filter.Eventually.{0} Nat
                (fun (n : Nat) =>
                  @Exists.{0} (@Ne.{1} Nat W (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                    fun (hWne : @Ne.{1} Nat W (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) =>
                    @Exists.{0}
                      (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) n)
                      fun
                        (hn :
                          @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) n) =>
                      ∀ (S : @Erdos390.Full.RegularMeshPrimeCutoffs.ScaleSeparation delta eta M n W),
                        let P :=
                          @Erdos390.Full.RegularMeshPrimeCutoffs.Mesh.canonicalPartition delta eta M n W hdelta hn hWne
                            S;
                        And
                          (∀ (p : Erdos390.Full.ArithmeticBandGeometry.BandPrime n W),
                            @LE.le.{0} Real Real.instLE
                              (@abs.{0} Real Real.lattice Real.instAddGroup
                                (@Erdos390.Full.ArithmeticBandGeometry.Partition.deviation.{0} n W
                                  (Fin
                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                      (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                  (Fin.fintype
                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                      (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                  (instDecidableEqFin
                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                      (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                  P p))
                              (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) delta eta))
                          (And
                            (@LE.le.{0} Real Real.instLE
                              (@Erdos390.Full.ArithmeticBandGeometry.Partition.totalL1.{0} n W
                                (Fin
                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                    (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                (Fin.fintype
                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                    (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                (instDecidableEqFin
                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                    (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                P)
                              (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                                (@OfNat.ofNat.{0} Real (nat_lit 7)
                                  (@instOfNatAtLeastTwo.{0} Real (nat_lit 7) Real.instNatCast
                                    (@Nat.instAtLeastTwoHAddOfNat
                                      (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))
                                      (@Nat.instNeZeroSucc
                                        (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))))))
                                (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) delta eta)))
                            (And
                              (@LE.le.{0} Real Real.instLE
                                (@HPow.hPow.{0, 0, 0} Real Nat Real
                                  (@instHPow.{0, 0} Real Nat (@Monoid.toPow.{0} Real Real.instMonoid))
                                  (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) delta eta)
                                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                                  (@HDiv.hDiv.{0, 0, 0} Real Real Real
                                    (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                                    (@OfNat.ofNat.{0} Real (nat_lit 456)
                                      (@instOfNatAtLeastTwo.{0} Real (nat_lit 456) Real.instNatCast
                                        (@Nat.instAtLeastTwoHAddOfNat
                                          (@OfNat.ofNat.{0} Nat (nat_lit 455) (instOfNatNat (nat_lit 455)))
                                          (@Nat.instNeZeroSucc
                                            (@OfNat.ofNat.{0} Nat (nat_lit 454) (instOfNatNat (nat_lit 454)))))))
                                    (@HPow.hPow.{0, 0, 0} Real Nat Real
                                      (@instHPow.{0, 0} Real Nat (@Monoid.toPow.{0} Real Real.instMonoid)) cMesh
                                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                                  (@Erdos390.Full.ArithmeticBandGeometry.Partition.variance.{0} n W
                                    (Fin
                                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                        (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                    (Fin.fintype
                                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                        (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                    (instDecidableEqFin
                                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                        (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                    P)))
                              (And
                                (@LE.le.{0} Real Real.instLE
                                  (@Erdos390.Full.ArithmeticBandGeometry.Partition.variance.{0} n W
                                    (Fin
                                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                        (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                    (Fin.fintype
                                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                        (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                    (instDecidableEqFin
                                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                        (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                    P)
                                  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                                    (@OfNat.ofNat.{0} Real (nat_lit 4)
                                      (@instOfNatAtLeastTwo.{0} Real (nat_lit 4) Real.instNatCast
                                        (@Nat.instAtLeastTwoHAddOfNat
                                          (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                                          (@Nat.instNeZeroSucc
                                            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))
                                    (@HPow.hPow.{0, 0, 0} Real Nat Real
                                      (@instHPow.{0, 0} Real Nat (@Monoid.toPow.{0} Real Real.instMonoid))
                                      (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) delta eta)
                                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
                                (@LE.le.{0} Real Real.instLE
                                  (@Erdos390.Full.ArithmeticBandGeometry.Partition.variance.{0} n W
                                    (Fin
                                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                        (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                    (Fin.fintype
                                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                        (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                    (instDecidableEqFin
                                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                        (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                    P)
                                  (@Erdos390.Full.ArithmeticBandGeometry.Partition.centerEnergy.{0} n W
                                    (Fin
                                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                        (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                    (Fin.fintype
                                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                        (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                    (instDecidableEqFin
                                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                        (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                    P))))))
                (@Filter.atTop.{0} Nat Nat.instPreorder) := by
  exact @Erdos390.Full.RegularMeshPrimeCutoffs.Mesh.canonicalPaperGeometricCutoff_eventually
