-- Prove2me | solution 1 for Erdos390.Full.RegularMeshPrimeCutoffs.Mesh.canonicalRelativeCenterCutoff_eventually
-- status  : ACCEPTED   (prove)
-- author  : @doctosil
-- created : 2026-09-17T15:52:44.876092+00:00
-- url     : https://prove2.me/submissions/28157540-ad1b-4330-91ca-aca5b5a7ca0a

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
import Theorems.Thm_Erdos390_Full_RegularMeshPrimeCutoffs_Mesh_eventually_endpointRelativeCenterBound_le

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

/-- Relative form of a one-denominator error estimate. -/
lemma abs_div_sub_one_le {x y e : ℝ} (hy : y ≠ 0)
    (hxy : |x - y| ≤ e) :
    |x / y - 1| ≤ e / |y| := by
  have hidentity : x / y - 1 = (x - y) / y := by
    field_simp [hy]
  rw [hidentity, abs_div]
  exact div_le_div_of_nonneg_right hxy (abs_nonneg y)



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

/-- The exact deterministic ratio transfer.  Once the arithmetic mass and
first moment have been compared with their continuum counterparts, this
proves the corresponding center estimate without identifying arithmetic and
continuum centers. -/
theorem center_error_le_of_mass_moment_errors (j : Band)
    {eMass eMoment : ℝ}
    (hMass : |P.mass j - E.continuumMass j| ≤ eMass)
    (hMoment :
      |P.mass j * P.center j - E.continuumMoment j| ≤ eMoment)
    (hContinuumMass : E.continuumMass j ≠ 0) :
    |P.center j - E.continuumCenter j| ≤
      eMoment / P.mass j +
        |E.continuumMoment j| * eMass /
          (P.mass j * |E.continuumMass j|) := by
  have hmass : 0 < P.mass j := P.data.mass_pos j
  have hcenter :
      P.center j = (P.mass j * P.center j) / P.mass j := by
    rw [mul_div_cancel_left₀]
    exact ne_of_gt hmass
  rw [hcenter, continuumCenter]
  exact abs_div_sub_div_le hmass hContinuumMass hMoment hMass







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

/- Source module: Erdos390.Full.MovingLowGaugeTransfer -/
section


/-!
# Moving-low arithmetic/continuum gauge transfer

This file isolates the normalization which is delicate at the moving low
cell.  An additive estimate for the arithmetic center is not enough because
the center itself tends to zero.  We first prove a quantitative relative
center estimate from separate estimates for `H` and `H * alpha`.  We then
write the sharp conjugate of the weighted gauge projection exactly and
compare two such projections through their normalized weights
`omega_j = H_j * alpha_j^2`.

No limiting mesh, covariance gap, or inverse is assumed in this module.
-/

open scoped BigOperators

noncomputable section

namespace Erdos390.Full.MovingLowGaugeTransfer

open Erdos390.Lemma84
open PositiveCellTransfer
open PrimeSums
open PrimeBandQuadrature
open MovingLowMomentQuadrature

section RelativeCenter

variable {n W : ℕ} {Band : Type*} [Fintype Band] [DecidableEq Band]
variable {P : ArithmeticBandGeometry.Partition n W Band}

/-- Dividing the center estimate by the continuum center is legitimate and
keeps every denominator visible.  This is the exact `/ alpha_0` step which
cannot be replaced by an additive `o(1)` assertion. -/
theorem center_ratio_error_le_of_mass_moment_errors
    (E : PositiveCellTransfer.IntervalCertificate P) (j : Band)
    {eMass eMoment : ℝ}
    (hMass : |P.mass j - E.continuumMass j| ≤ eMass)
    (hMoment :
      |P.mass j * P.center j - E.continuumMoment j| ≤ eMoment)
    (hContinuumMass : E.continuumMass j ≠ 0)
    (hContinuumCenter : E.continuumCenter j ≠ 0) :
    |P.center j / E.continuumCenter j - 1| ≤
      (eMoment / P.mass j +
        |E.continuumMoment j| * eMass /
          (P.mass j * |E.continuumMass j|)) /
        |E.continuumCenter j| := by
  apply abs_div_sub_one_le hContinuumCenter
  exact E.center_error_le_of_mass_moment_errors j
    hMass hMoment hContinuumMass

/-- If the mass error is at most half of the positive continuum mass, the
preceding exact bound simplifies to the scale-transparent estimate

`relative center error <= 2 eMoment / M_c + 2 eMass / H_c`.

At the moving low cell `M_c` stays bounded away from zero, while `H_c`
grows; hence an ambient-logarithm error for the first moment and a bounded
mass error both become small after division by `alpha_0 = M_c / H_c`. -/
theorem center_ratio_error_le_two_errors
    (E : PositiveCellTransfer.IntervalCertificate P) (j : Band)
    {eMass eMoment : ℝ}
    (hMass : |P.mass j - E.continuumMass j| ≤ eMass)
    (hMoment :
      |P.mass j * P.center j - E.continuumMoment j| ≤ eMoment)
    (hContinuumMass : 0 < E.continuumMass j)
    (hContinuumMoment : 0 < E.continuumMoment j)
    (hMassSmall : eMass ≤ E.continuumMass j / 2) :
    |P.center j / E.continuumCenter j - 1| ≤
      2 * eMoment / E.continuumMoment j +
        2 * eMass / E.continuumMass j := by
  have heMass : 0 ≤ eMass := (abs_nonneg _).trans hMass
  have heMoment : 0 ≤ eMoment := (abs_nonneg _).trans hMoment
  have hmassLower : E.continuumMass j / 2 ≤ P.mass j := by
    have hleft : -eMass ≤ P.mass j - E.continuumMass j :=
      (abs_le.mp hMass).1
    linarith
  have hmass : 0 < P.mass j := P.data.mass_pos j
  have htwoMass : E.continuumMass j ≤ 2 * P.mass j := by linarith
  have hcenter : 0 < E.continuumCenter j := by
    unfold PositiveCellTransfer.IntervalCertificate.continuumCenter
    exact div_pos hContinuumMoment hContinuumMass
  have hraw := center_ratio_error_le_of_mass_moment_errors E j
    hMass hMoment (ne_of_gt hContinuumMass) (ne_of_gt hcenter)
  have hsimplify :
      (eMoment / P.mass j +
          |E.continuumMoment j| * eMass /
            (P.mass j * |E.continuumMass j|)) /
          |E.continuumCenter j| =
        eMoment * E.continuumMass j /
            (P.mass j * E.continuumMoment j) +
          eMass / P.mass j := by
    rw [abs_of_pos hContinuumMoment, abs_of_pos hContinuumMass,
      abs_of_pos hcenter]
    unfold PositiveCellTransfer.IntervalCertificate.continuumCenter
    field_simp [ne_of_gt hmass, ne_of_gt hContinuumMass,
      ne_of_gt hContinuumMoment]
  rw [hsimplify] at hraw
  have hfirst :
      eMoment * E.continuumMass j /
          (P.mass j * E.continuumMoment j) ≤
        2 * eMoment / E.continuumMoment j := by
    have hnum :
        eMoment * E.continuumMass j ≤
          eMoment * (2 * P.mass j) :=
      mul_le_mul_of_nonneg_left htwoMass heMoment
    calc
      eMoment * E.continuumMass j /
          (P.mass j * E.continuumMoment j) ≤
        (eMoment * (2 * P.mass j)) /
          (P.mass j * E.continuumMoment j) :=
        div_le_div_of_nonneg_right hnum
          (mul_pos hmass hContinuumMoment).le
      _ = 2 * eMoment / E.continuumMoment j := by
        field_simp [ne_of_gt hmass, ne_of_gt hContinuumMoment]
  have hsecond :
      eMass / P.mass j ≤ 2 * eMass / E.continuumMass j := by
    apply (div_le_div_iff₀ hmass hContinuumMass).2
    have hscaled := mul_le_mul_of_nonneg_left htwoMass heMass
    nlinarith
  exact hraw.trans (add_le_add hfirst hsecond)





end RelativeCenter

section SharpProjection

variable {Band : Type*} [Fintype Band] [DecidableEq Band]

































end SharpProjection

end Erdos390.Full.MovingLowGaugeTransfer

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































/-- Relative-centre convergence with the *global* arithmetic cutoff exposed.
The cutoff is selected before, and is independent of, `M`; only the eventual
ambient threshold may depend on the mesh. -/
theorem canonicalRelativeCenterCutoff_eventually
    (hdelta : 0 < delta) (W : ℕ)
    (hW : canonicalRelativeCenterCutoff ≤ W) (e : ℝ) (he : 0 < e) :
      ∀ᶠ n : ℕ in atTop, ∃ hWne : W ≠ 0, ∃ hn : 1 < n,
        ∃ S : ScaleSeparation M n W,
          let P := canonicalPartition M hdelta hn hWne S
          let E := canonicalCertificate M hdelta hn hWne S
          ∀ j : Fin (M.cellCount + 1),
            |P.center j / E.continuumCenter j - 1| ≤ e := by
  let Cmass := PrimeBandQuadrature.fullReciprocalSumUniformConstant
  let Cmoment := MovingLowMomentQuadrature.fullLogReciprocalSumUniformConstant
  have hW2 : 2 ≤ W := (le_max_left 2
    (max PrimeBandQuadrature.fullReciprocalSumUniformCutoff
      MovingLowMomentQuadrature.fullLogReciprocalSumUniformCutoff)).trans hW
  have hXmass : PrimeBandQuadrature.fullReciprocalSumUniformCutoff ≤ W :=
    ((le_max_left PrimeBandQuadrature.fullReciprocalSumUniformCutoff
      MovingLowMomentQuadrature.fullLogReciprocalSumUniformCutoff).trans
      (le_max_right 2
        (max PrimeBandQuadrature.fullReciprocalSumUniformCutoff
          MovingLowMomentQuadrature.fullLogReciprocalSumUniformCutoff))).trans hW
  have hXmoment : MovingLowMomentQuadrature.fullLogReciprocalSumUniformCutoff ≤ W :=
    ((le_max_right PrimeBandQuadrature.fullReciprocalSumUniformCutoff
      MovingLowMomentQuadrature.fullLogReciprocalSumUniformCutoff).trans
      (le_max_right 2
        (max PrimeBandQuadrature.fullReciprocalSumUniformCutoff
          MovingLowMomentQuadrature.fullLogReciprocalSumUniformCutoff))).trans hW
  have hReady := eventually_endpointRelativeCenterBound_le M hdelta
    (W := W) Cmass Cmoment he
  have hSep := eventually_scaleSeparation M hdelta W
  filter_upwards [eventually_gt_atTop 1, hSep, hReady] with n hn S hR
  have hWne : W ≠ 0 := by omega
  let P := canonicalPartition M hdelta hn hWne S
  let E := canonicalCertificate M hdelta hn hWne S
  refine ⟨hWne, hn, S, ?_⟩
  dsimp only
  intro j
  have hLowerThresholdMass :
      PrimeBandQuadrature.fullReciprocalSumUniformCutoff ≤ E.lower j :=
    hXmass.trans (E.cutoff_le_lower j)
  have hLowerThresholdMoment :
      MovingLowMomentQuadrature.fullLogReciprocalSumUniformCutoff ≤ E.lower j :=
    hXmoment.trans (E.cutoff_le_lower j)
  have hMassQ : |P.mass j - E.continuumMass j| ≤
      endpointMassError M Cmass n W j := by
    have h := PrimeBandQuadrature.fullReciprocalSumUniform_bound
      (E.lower j) (E.upper j)
      hLowerThresholdMass (E.lower_le_upper j)
    rw [E.mass_eq_fullReciprocalSum_sub]
    simpa only [P, E, canonicalCertificate_lower,
      canonicalCertificate_upper, endpointMassError] using h
  have hMomentQ : |P.mass j * P.center j - E.continuumMoment j| ≤
      endpointMomentError M Cmoment n W j := by
    have h := MovingLowMomentQuadrature.fullLogReciprocalSumUniform_bound
      (E.lower j) (E.upper j)
      hLowerThresholdMoment (E.lower_le_upper j)
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
  have hMassId : E.continuumMass j = endpointContinuumMass M n W j := by
    rfl
  have hMomentId : E.continuumMoment j =
      endpointContinuumMoment M n W j := by rfl
  have hBound := center_ratio_error_le_two_errors E j hMassQ hMomentQ
    (by rw [hMassId]; exact (hR j).1)
    (by rw [hMomentId]; exact (hR j).2.1)
    (by rw [hMassId]; exact (hR j).2.2.1)
  exact hBound.trans (by
    simpa only [hMassId, hMomentId, endpointRelativeCenterBound] using
      (hR j).2.2.2)



end Mesh
end Erdos390.Full.RegularMeshPrimeCutoffs

end

theorem solution :
∀ {delta eta : Real} (M : Erdos390.Full.RegularRelativeMesh.Mesh delta eta) (hdelta : LT.lt.{0} (0 : Real) delta)
  (W : Nat),
  LE.le.{0} Erdos390.Full.RegularMeshPrimeCutoffs.canonicalRelativeCenterCutoff W →
    ∀ (e : Real),
      LT.lt.{0} (0 : Real) e →
        ∀ᶠ (n : Nat) in Filter.atTop.{0},
          ∃ (hWne : Ne.{1} W (0 : Nat)) (hn : LT.lt.{0} (1 : Nat) n) (S :
            Erdos390.Full.RegularMeshPrimeCutoffs.ScaleSeparation M n W),
            have P := Erdos390.Full.RegularMeshPrimeCutoffs.Mesh.canonicalPartition M hdelta hn hWne S;
            have E := Erdos390.Full.RegularMeshPrimeCutoffs.Mesh.canonicalCertificate M hdelta hn hWne S;
            ∀ (j : Fin (HAdd.hAdd.{0, 0, 0} (Erdos390.Full.RegularRelativeMesh.Mesh.cellCount M) (1 : Nat))),
              LE.le.{0}
                (abs.{0}
                  (HSub.hSub.{0, 0, 0}
                    (HDiv.hDiv.{0, 0, 0} (Erdos390.Full.ArithmeticBandGeometry.Partition.center.{0} P j)
                      (Erdos390.Full.PositiveCellTransfer.IntervalCertificate.continuumCenter.{0} E j))
                    (1 : Real)))
                e := by
  exact @Erdos390.Full.RegularMeshPrimeCutoffs.Mesh.canonicalRelativeCenterCutoff_eventually
