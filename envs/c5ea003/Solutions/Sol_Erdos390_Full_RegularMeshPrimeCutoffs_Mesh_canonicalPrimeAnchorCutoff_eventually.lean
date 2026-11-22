-- Prove2me | solution 1 for Erdos390.Full.RegularMeshPrimeCutoffs.Mesh.canonicalPrimeAnchorCutoff_eventually
-- status  : ACCEPTED   (prove)
-- author  : @doctosil
-- created : 2026-09-17T15:27:43.465935+00:00
-- url     : https://prove2.me/submissions/e53470a3-562d-4f4c-976d-88940e4e8047

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























theorem fullLogReciprocalSumUniformConstant_pos :
    0 < fullLogReciprocalSumUniformConstant :=
  (Classical.choose_spec
    exists_fullLogReciprocalSum_interval_uniform_error_bound).1



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

theorem canonical_positiveBand_coordinate_bounds
    {n W : ℕ} (hdelta : 0 < delta) (hn : 1 < n)
    (hW : W ≠ 0) (S : ScaleSeparation M n W)
    (k : Fin M.cellCount)
    (hLowerTwo : 2 ≤ scalePoint n (M.lower k))
    (hUpperTwo : 2 ≤ scalePoint n (M.upper k)) :
    let E := canonicalCertificate M hdelta hn hW S
    M.lower k - Real.log 2 / Real.log (y n) ≤
        realLogCoordinate (y n) (E.lower (positiveBand M k) : ℝ) ∧
      realLogCoordinate (y n) (E.lower (positiveBand M k) : ℝ) ≤
        M.lower k ∧
      M.upper k - Real.log 2 / Real.log (y n) ≤
        realLogCoordinate (y n) (E.upper (positiveBand M k) : ℝ) ∧
      realLogCoordinate (y n) (E.upper (positiveBand M k) : ℝ) ≤
        M.upper k := by
  dsimp only
  have hlower := floor_scalePoint_coordinate_bounds hn hLowerTwo
  have hupper := floor_scalePoint_coordinate_bounds hn hUpperTwo
  simpa only [canonicalCertificate_lower, canonicalCertificate_upper,
    positiveBand, fullCutoff_succ, RegularRelativeMesh.Mesh.lower,
    RegularRelativeMesh.Mesh.upper] using ⟨hlower.1, hlower.2,
      hupper.1, hupper.2⟩

/-- Quantitative anchor statement at one `n`. -/
theorem canonical_anchor_interior_and_length
    {n W : ℕ} (hdelta : 0 < delta) (hn : 1 < n)
    (hW : W ≠ 0) (S : ScaleSeparation M n W)
    {epsilon : ℝ} (k : Fin M.cellCount)
    (hIdealUpper : M.upper k ≤ 1 - epsilon)
    (hLowerTwo : 2 ≤ scalePoint n (M.lower k))
    (hUpperTwo : 2 ≤ scalePoint n (M.upper k))
    (hLossLower : Real.log 2 / Real.log (y n) < M.lower k - epsilon)
    (hLossWidth : Real.log 2 / Real.log (y n) ≤ M.width k / 2) :
    let E := canonicalCertificate M hdelta hn hW S
    epsilon ≤ realLogCoordinate (y n) (E.lower (positiveBand M k) : ℝ) ∧
      realLogCoordinate (y n) (E.upper (positiveBand M k) : ℝ) ≤
        1 - epsilon ∧
      M.width k / 2 ≤
        realLogCoordinate (y n) (E.upper (positiveBand M k) : ℝ) -
          realLogCoordinate (y n) (E.lower (positiveBand M k) : ℝ) := by
  dsimp only
  obtain ⟨hlowerLo, hlowerHi, hupperLo, hupperHi⟩ :=
    canonical_positiveBand_coordinate_bounds M hdelta hn hW S k
      hLowerTwo hUpperTwo
  constructor
  · linarith
  constructor
  · exact hupperHi.trans hIdealUpper
  · unfold RegularRelativeMesh.Mesh.width at hLossWidth ⊢
    linarith

/-- The selected anchor cell is eventually interior and has a uniform
positive anchor mass. -/
theorem eventually_canonical_anchor_coverage
    (hdelta : 0 < delta) {W : ℕ} (hW : W ≠ 0)
    {epsilon : ℝ} (k : Fin M.cellCount)
    (hIdealLower : epsilon < M.lower k)
    (hIdealUpper : M.upper k ≤ 1 - epsilon) :
    ∀ᶠ n : ℕ in atTop,
      ∃ hn : 1 < n, ∀ S : ScaleSeparation M n W,
        let E := canonicalCertificate M hdelta hn hW S
        epsilon ≤
            realLogCoordinate (y n) (E.lower (positiveBand M k) : ℝ) ∧
          realLogCoordinate (y n) (E.upper (positiveBand M k) : ℝ) ≤
            1 - epsilon ∧
          M.width k / 2 ≤
            realLogCoordinate (y n) (E.upper (positiveBand M k) : ℝ) -
              realLogCoordinate (y n) (E.lower (positiveBand M k) : ℝ) := by
  have hlowerTop := tendsto_scalePoint_atTop (M.lower_pos hdelta k)
  have hupperTop := tendsto_scalePoint_atTop
    ((M.lower_pos hdelta k).trans (M.lower_lt_upper hdelta k))
  have hlogYTop : Tendsto (fun n : ℕ => Real.log (y n)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_y_atTop
  have hloss : Tendsto (fun n : ℕ => Real.log 2 / Real.log (y n))
      atTop (nhds 0) := by
    exact tendsto_const_nhds.div_atTop hlogYTop
  have hmargin : 0 < M.lower k - epsilon := sub_pos.mpr hIdealLower
  have hwidthHalf : 0 < M.width k / 2 :=
    div_pos (M.width_pos hdelta k) (by norm_num)
  have hlossLower := hloss.eventually (eventually_lt_nhds hmargin)
  have hlossWidth := hloss.eventually (eventually_le_nhds hwidthHalf)
  filter_upwards [eventually_gt_atTop 1,
    hlowerTop.eventually (eventually_ge_atTop (2 : ℝ)),
    hupperTop.eventually (eventually_ge_atTop (2 : ℝ)),
    hlossLower, hlossWidth] with n hn hLowerTwo hUpperTwo hLossLower hLossWidth
  refine ⟨hn, ?_⟩
  intro S
  exact canonical_anchor_interior_and_length M hdelta hn hW S k
    hIdealUpper hLowerTwo hUpperTwo hLossLower hLossWidth

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

/- Source module: Erdos390.Full.CanonicalEndpointMultiAnchorCoverage -/
section


/-!
# Eventual coverage of a fixed interior anchor block

All cells in a fixed finite ideal anchor block remain interior after the
literal floor operation.  Their total actual logarithmic length is at least
half of the total ideal length.  Unlike a singleton anchor, this lower bound
can stay positive while the mesh is refined.
-/

open Filter Set
open scoped BigOperators

noncomputable section

namespace Erdos390.Full.RegularMeshPrimeCutoffs

open ArithmeticModel RegularRelativeMesh KernelPrimeQuadrature
open ContinuumCellGraph

namespace Mesh

variable {delta eta : ℝ} (M : Mesh delta eta)

theorem eventually_canonical_anchorBlock_coverage
    (hdelta : 0 < delta) {W : ℕ} (hW : W ≠ 0) (hWTwo : 2 ≤ W)
    {epsilon anchorFloor : ℝ}
    (anchors : Finset (Fin M.cellCount)) (hAnchors : anchors.Nonempty)
    (hIdealLower : ∀ k ∈ anchors, epsilon < M.lower k)
    (hIdealUpper : ∀ k ∈ anchors, M.upper k ≤ 1 - epsilon)
    (hAnchorFloor : anchorFloor ≤
      (∑ k ∈ anchors, M.width k) / 2) :
    ∀ᶠ n : ℕ in atTop,
      ∃ hn : 1 < n, ∀ S : ScaleSeparation M n W,
        ∃ hInteriorLower : ∀ k ∈ anchors, epsilon ≤
          realLogCoordinate (y n)
            ((canonicalCertificate M hdelta hn hW S).lower
              (positiveBand M k) : ℝ),
        ∃ hInteriorUpper : ∀ k ∈ anchors,
          realLogCoordinate (y n)
            ((canonicalCertificate M hdelta hn hW S).upper
              (positiveBand M k) : ℝ) ≤ 1 - epsilon,
          let IM := canonicalIntervalMeshOfAnchors M hdelta hn hW
            hWTwo S epsilon anchors hAnchors
              hInteriorLower hInteriorUpper
          anchorFloor ≤ ∑ j, IM.anchor j := by
  have hEach : ∀ᶠ n : ℕ in atTop,
      ∀ k : Fin M.cellCount, k ∈ anchors →
        ∃ hnk : 1 < n, ∀ S : ScaleSeparation M n W,
          let E := canonicalCertificate M hdelta hnk hW S
          epsilon ≤ realLogCoordinate (y n)
              (E.lower (positiveBand M k) : ℝ) ∧
            realLogCoordinate (y n)
              (E.upper (positiveBand M k) : ℝ) ≤ 1 - epsilon ∧
            M.width k / 2 ≤
              realLogCoordinate (y n)
                  (E.upper (positiveBand M k) : ℝ) -
                realLogCoordinate (y n)
                  (E.lower (positiveBand M k) : ℝ) := by
    rw [Filter.eventually_all]
    intro k
    by_cases hk : k ∈ anchors
    · exact (eventually_canonical_anchor_coverage M hdelta hW k
        (hIdealLower k hk) (hIdealUpper k hk)).mono (fun n hn _ ↦ hn)
    · filter_upwards with n
      exact fun hfalse ↦ (hk hfalse).elim
  filter_upwards [eventually_gt_atTop 1, hEach] with n hn hAll
  have hCell (k : Fin M.cellCount) (hk : k ∈ anchors)
      (S : ScaleSeparation M n W) :
      epsilon ≤ realLogCoordinate (y n)
          ((canonicalCertificate M hdelta hn hW S).lower
            (positiveBand M k) : ℝ) ∧
        realLogCoordinate (y n)
          ((canonicalCertificate M hdelta hn hW S).upper
            (positiveBand M k) : ℝ) ≤ 1 - epsilon ∧
        M.width k / 2 ≤
          realLogCoordinate (y n)
              ((canonicalCertificate M hdelta hn hW S).upper
                (positiveBand M k) : ℝ) -
            realLogCoordinate (y n)
              ((canonicalCertificate M hdelta hn hW S).lower
                (positiveBand M k) : ℝ) := by
    obtain ⟨hnk, hkAll⟩ := hAll k hk
    simpa only [Subsingleton.elim hnk hn] using hkAll S
  refine ⟨hn, ?_⟩
  intro S
  let hLower : ∀ k ∈ anchors, epsilon ≤
      realLogCoordinate (y n)
        ((canonicalCertificate M hdelta hn hW S).lower
          (positiveBand M k) : ℝ) := fun k hk ↦ (hCell k hk S).1
  let hUpper : ∀ k ∈ anchors,
      realLogCoordinate (y n)
        ((canonicalCertificate M hdelta hn hW S).upper
          (positiveBand M k) : ℝ) ≤ 1 - epsilon :=
    fun k hk ↦ (hCell k hk S).2.1
  refine ⟨hLower, hUpper, ?_⟩
  let IM := canonicalIntervalMeshOfAnchors M hdelta hn hW hWTwo S epsilon
    anchors hAnchors hLower hUpper
  have hsum : (∑ j, IM.anchor j) =
      ∑ k ∈ anchors, IM.length (positiveBand M k) := by
    unfold ContinuumCellGraph.IntervalMesh.anchor
    rw [← Finset.sum_filter]
    calc
      (∑ x ∈ Finset.univ.filter
          (fun j ↦ j ∈ anchors.map (positiveBandEmbedding M)),
          IM.length x) =
          ∑ x ∈ anchors.map (positiveBandEmbedding M), IM.length x := by
        apply Finset.sum_congr
        · ext j
          simp
        · intro j hj
          rfl
      _ = ∑ k ∈ anchors, IM.length (positiveBand M k) := by
        rw [Finset.sum_map]
        rfl
  change anchorFloor ≤ ∑ j, IM.anchor j
  rw [hsum]
  calc
    anchorFloor ≤ (∑ k ∈ anchors, M.width k) / 2 := hAnchorFloor
    _ = ∑ k ∈ anchors, M.width k / 2 := by
      rw [Finset.sum_div]
    _ ≤ ∑ k ∈ anchors, IM.length (positiveBand M k) := by
      apply Finset.sum_le_sum
      intro k hk
      simpa only [IM, canonicalIntervalMeshOfAnchors,
        ContinuumCellGraph.IntervalMesh.length] using (hCell k hk S).2.2

end Mesh
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



/-- A selected literal prime lies between the actual endpoint coordinates
of its selected cell. -/
theorem canonicalPrimeAnchorSet_mem_Icc
    {n W : ℕ} {P : Partition n W (Fin (M.cellCount + 1))}
    (E : IntervalCertificate P) (hn : 1 < n) (hWTwo : 2 ≤ W)
    {epsilon : ℝ} (anchors : Finset (Fin M.cellCount))
    (hInteriorLower : ∀ k ∈ anchors, epsilon ≤
      realLogCoordinate (y n) (E.lower (positiveBand M k) : ℝ))
    (hInteriorUpper : ∀ k ∈ anchors,
      realLogCoordinate (y n) (E.upper (positiveBand M k) : ℝ) ≤
        1 - epsilon) :
    ∀ p ∈ canonicalPrimeAnchorSet M P anchors,
      tPrime n p.1 ∈ Icc epsilon (1 - epsilon) := by
  intro p hp
  obtain ⟨k, hk, hpk⟩ := (mem_canonicalPrimeAnchorSet_iff M).mp hp
  have hpInterval := (E.band_eq_iff p (positiveBand M k)).mp hpk
  have hy : 1 < y n := by
    rw [← Real.log_pos_iff (Scale.y_pos (Nat.zero_lt_of_lt hn)).le]
    rw [Scale.log_y (Nat.zero_lt_of_lt hn)]
    exact mul_pos (by norm_num) (Real.log_pos (by exact_mod_cast hn))
  have hLowerTwo : 2 ≤ E.lower (positiveBand M k) :=
    hWTwo.trans (E.cutoff_le_lower (positiveBand M k))
  have hLowerPrime : E.lower (positiveBand M k) ≤ p.1 :=
    hpInterval.1.le
  have hCoordLower := realLogCoordinate_mono_nat hy hLowerTwo hLowerPrime
  have hPrimeTwo : 2 ≤ p.1 := hLowerTwo.trans hLowerPrime
  have hCoordUpper := realLogCoordinate_mono_nat hy hPrimeTwo hpInterval.2
  change realLogCoordinate (y n) (p.1 : ℝ) ∈ Icc epsilon (1 - epsilon)
  exact ⟨(hInteriorLower k hk).trans hCoordLower,
    hCoordUpper.trans (hInteriorUpper k hk)⟩

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



/-- Uniform literal prime-anchor package for every fixed permitted mesh,
using the preceding named cutoff.  The order in the type is the order used
by the paper: the cutoff can be selected before `M`. -/
theorem canonicalPrimeAnchorCutoff_eventually
    (hdelta : 0 < delta) :
    ∀ W : ℕ, canonicalPrimeAnchorCutoff ≤ W →
      ∀ {epsilon : ℝ}
        (anchors : Finset (Fin M.cellCount)), anchors.Nonempty →
        (∀ k ∈ anchors, epsilon < M.lower k) →
        (∀ k ∈ anchors, M.upper k ≤ 1 - epsilon) →
        ((1 : ℝ) / 8 ≤ (∑ k ∈ anchors, M.width k) / 2) →
      ∀ᶠ n : ℕ in atTop,
        ∃ hWne : W ≠ 0, ∃ hn : 1 < n, ∀ S : ScaleSeparation M n W,
          let P := canonicalPartition M hdelta hn hWne S
          let anchor := canonicalPrimeAnchorSet M P anchors
          (∀ p ∈ anchor, tPrime n p.1 ∈ Icc epsilon (1 - epsilon)) ∧
            (1 : ℝ) / 8 ≤ anchorMass (primeWeight n) anchor := by
  let Cmoment : ℝ :=
    MovingLowMomentQuadrature.fullLogReciprocalSumUniformConstant
  let Xmoment : ℕ :=
    MovingLowMomentQuadrature.fullLogReciprocalSumUniformCutoff
  have hCmoment : 0 < Cmoment := by
    simpa only [Cmoment] using
      MovingLowMomentQuadrature.fullLogReciprocalSumUniformConstant_pos
  have hMoment : ∀ A Y : ℕ, Xmoment ≤ A → A ≤ Y →
      |PrimeSums.fullLogReciprocalSum Y -
          PrimeSums.fullLogReciprocalSum A -
          (Real.log (Y : ℝ) - Real.log (A : ℝ))| ≤
        2 * Cmoment / Real.log (A : ℝ) ^ 3 +
          Cmoment / (2 * Real.log (A : ℝ) ^ 2) := by
    intro A Y hA hAY
    simpa only [Cmoment, Xmoment] using
      MovingLowMomentQuadrature.fullLogReciprocalSumUniform_bound A Y hA hAY
  intro W hW epsilon anchors hAnchors hIdealLower hIdealUpper hIdealMass
  have hWTwo : 2 ≤ W := (le_max_left 2 Xmoment).trans hW
  have hWne : W ≠ 0 := by omega
  have hXmoment : Xmoment ≤ W := (le_max_right 2 Xmoment).trans hW
  have hCoverage := eventually_canonical_anchorBlock_coverage M hdelta
    hWne hWTwo anchors hAnchors hIdealLower hIdealUpper hIdealMass
  let e : ℝ := 1 / (32 * (anchors.card : ℝ))
  have hCardPosNat : 0 < anchors.card := Finset.card_pos.mpr hAnchors
  have hCardPos : (0 : ℝ) < anchors.card := by exact_mod_cast hCardPosNat
  have he : 0 < e := by
    dsimp only [e]
    positivity
  have hApprox : ∀ᶠ n : ℕ in atTop,
      ∀ k : Fin M.cellCount,
        |endpointContinuumMoment M n W (positiveBand M k) - M.width k| ≤ e ∧
          endpointMomentError M Cmoment n W (positiveBand M k) ≤ e := by
    rw [Filter.eventually_all]
    intro k
    have hMain := tendsto_positive_endpointContinuumMoment M hdelta W k
    have hMainSmall := hMain.eventually
      (Metric.eventually_nhds_iff.mpr ⟨e, he, fun x hx ↦ by
        simpa only [Real.dist_eq] using hx⟩)
    have hError := tendsto_positive_endpointMomentError_zero
      M hdelta Cmoment W k
    have hErrorSmall := hError.eventually (eventually_le_nhds he)
    filter_upwards [hMainSmall, hErrorSmall] with n hnMain hnError
    exact ⟨hnMain.le, hnError⟩
  filter_upwards [hCoverage, hApprox] with n hCoverageN hApproxN
  obtain ⟨hn, hCoverageAll⟩ := hCoverageN
  refine ⟨hWne, hn, ?_⟩
  intro S
  obtain ⟨hInteriorLower, hInteriorUpper, _hContinuumMass⟩ :=
    hCoverageAll S
  let P := canonicalPartition M hdelta hn hWne S
  let E := canonicalCertificate M hdelta hn hWne S
  let anchor := canonicalPrimeAnchorSet M P anchors
  have hInterior : ∀ p ∈ anchor,
      tPrime n p.1 ∈ Icc epsilon (1 - epsilon) := by
    exact canonicalPrimeAnchorSet_mem_Icc M E hn hWTwo anchors
      hInteriorLower hInteriorUpper
  have hCellApprox (k : Fin M.cellCount) :
      |P.mass (positiveBand M k) * P.center (positiveBand M k) -
          M.width k| ≤ 2 * e := by
    have hPNT := abs_canonical_mass_mul_center_sub_endpointContinuumMoment_le
      M hdelta hn hWne S hMoment hXmoment (positiveBand M k)
    calc
      |P.mass (positiveBand M k) * P.center (positiveBand M k) -
          M.width k| ≤
          |P.mass (positiveBand M k) * P.center (positiveBand M k) -
            endpointContinuumMoment M n W (positiveBand M k)| +
          |endpointContinuumMoment M n W (positiveBand M k) -
            M.width k| := abs_sub_le _ _ _
      _ ≤ e + e := add_le_add (hPNT.trans (hApproxN k).2)
        (hApproxN k).1
      _ = 2 * e := by ring
  have hSumLower :
      (∑ k ∈ anchors, M.width k) - (1 : ℝ) / 16 ≤
        ∑ k ∈ anchors,
          P.mass (positiveBand M k) * P.center (positiveBand M k) := by
    have hEach (k : Fin M.cellCount) (hk : k ∈ anchors) :
        M.width k - 2 * e ≤
          P.mass (positiveBand M k) * P.center (positiveBand M k) := by
      have hleft := neg_le_of_abs_le (hCellApprox k)
      linarith
    have hsum := Finset.sum_le_sum hEach
    calc
      (∑ k ∈ anchors, M.width k) - (1 : ℝ) / 16 =
          ∑ k ∈ anchors, (M.width k - 2 * e) := by
        rw [Finset.sum_sub_distrib, Finset.sum_const]
        dsimp only [e]
        have hcardInv : (anchors.card : ℝ) * (anchors.card : ℝ)⁻¹ = 1 :=
          mul_inv_cancel₀ (ne_of_gt hCardPos)
        have hconst : anchors.card •
            (2 * (1 / (32 * (anchors.card : ℝ)))) = (1 : ℝ) / 16 := by
          rw [nsmul_eq_mul]
          change (anchors.card : ℝ) *
            (2 * (1 / (32 * (anchors.card : ℝ)))) = 1 / 16
          calc
            (anchors.card : ℝ) *
                (2 * (1 / (32 * (anchors.card : ℝ)))) =
                ((anchors.card : ℝ) * (anchors.card : ℝ)⁻¹) *
                  (2 * 32⁻¹) := by ring
            _ = 1 / 16 := by rw [hcardInv]; norm_num
        rw [hconst]
      _ ≤ _ := hsum
  have hWidth : (1 : ℝ) / 4 ≤ ∑ k ∈ anchors, M.width k := by
    linarith
  have hMassLower : (1 : ℝ) / 8 ≤
      anchorMass (primeWeight n) anchor := by
    rw [anchorMass_canonicalPrimeAnchorSet_eq M]
    exact le_trans (by linarith : (1 : ℝ) / 8 ≤
      (∑ k ∈ anchors, M.width k) - (1 : ℝ) / 16) hSumLower
  exact ⟨hInterior, hMassLower⟩



end Mesh
end Erdos390.Full.RegularMeshPrimeCutoffs

end

theorem solution :
∀ {delta eta : Real} (M : Erdos390.Full.RegularRelativeMesh.Mesh delta eta) (hdelta : LT.lt.{0} (0 : Real) delta)
  (W : Nat),
  LE.le.{0} Erdos390.Full.RegularMeshPrimeCutoffs.Mesh.canonicalPrimeAnchorCutoff W →
    ∀ {epsilon : Real} (anchors : Finset.{0} (Fin (Erdos390.Full.RegularRelativeMesh.Mesh.cellCount M))),
      Finset.Nonempty.{0} anchors →
        (∀ (k : Fin (Erdos390.Full.RegularRelativeMesh.Mesh.cellCount M)),
            Membership.mem.{0, 0} anchors k → LT.lt.{0} epsilon (Erdos390.Full.RegularRelativeMesh.Mesh.lower M k)) →
          (∀ (k : Fin (Erdos390.Full.RegularRelativeMesh.Mesh.cellCount M)),
              Membership.mem.{0, 0} anchors k →
                LE.le.{0} (Erdos390.Full.RegularRelativeMesh.Mesh.upper M k) (HSub.hSub.{0, 0, 0} (1 : Real) epsilon)) →
            LE.le.{0} (1 / 8 : Real)
                (HDiv.hDiv.{0, 0, 0} (∑ k ∈ anchors, Erdos390.Full.RegularRelativeMesh.Mesh.width M k) (2 : Real)) →
              ∀ᶠ (n : Nat) in Filter.atTop.{0},
                ∃ (hWne : Ne.{1} W (0 : Nat)) (hn : LT.lt.{0} (1 : Nat) n),
                  ∀ (S : Erdos390.Full.RegularMeshPrimeCutoffs.ScaleSeparation M n W),
                    have P := Erdos390.Full.RegularMeshPrimeCutoffs.Mesh.canonicalPartition M hdelta hn hWne S;
                    have anchor := Erdos390.Full.RegularMeshPrimeCutoffs.Mesh.canonicalPrimeAnchorSet M P anchors;
                    And
                      (∀ (p : Erdos390.Full.ArithmeticBandGeometry.BandPrime n W),
                        Membership.mem.{0, 0} anchor p →
                          Membership.mem.{0, 0} (Set.Icc.{0} epsilon (HSub.hSub.{0, 0, 0} (1 : Real) epsilon))
                            (Erdos390.Full.ArithmeticModel.tPrime n ↑p))
                      (LE.le.{0} (1 / 8 : Real)
                        (Erdos390.Full.FiniteAnchoredDirichletQuadratic.anchorMass.{0}
                          (Erdos390.Full.PrimeSquarefreeDirichletGeometry.primeWeight n) anchor)) := by
  exact @Erdos390.Full.RegularMeshPrimeCutoffs.Mesh.canonicalPrimeAnchorCutoff_eventually
