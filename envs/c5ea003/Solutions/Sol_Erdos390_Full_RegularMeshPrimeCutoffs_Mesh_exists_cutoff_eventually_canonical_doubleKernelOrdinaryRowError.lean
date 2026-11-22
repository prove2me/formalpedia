-- Prove2me | solution 1 for Erdos390.Full.RegularMeshPrimeCutoffs.Mesh.exists_cutoff_eventually_canonical_doubleKernelOrdinaryRowError
-- status  : ACCEPTED   (prove)
-- author  : @doctosil
-- created : 2026-09-17T16:02:24.786548+00:00
-- url     : https://prove2.me/submissions/1d6e60df-bdf1-48a3-8b14-4406eb439e12

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
import Theorems.Thm_Erdos390_Full_DoubleKernelPrimeQuadrature_doubleKernelCell_error_le_of_oneIndex
import Theorems.Thm_Erdos390_Full_KernelPrimeQuadrature_abs_kernelWeightedAbelRemainder_le
import Theorems.Thm_Erdos390_Full_RegularMeshPrimeCutoffs_Mesh_eventually_endpointRelativeCenterBound_le
import Theorems.Thm_Erdos390_Full_RegularMeshPrimeCutoffs_Mesh_tendsto_low_endpointContinuumMass_div_log_y_cube_zero

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

/- Source module: Erdos390.Full.ConditionedPoissonLimit -/
section


/-!
# Exact analytic identities for the Poisson--Dickman bridge

This file continues the explicit finite-cutoff construction in
`ConditionedPoisson`.  The first layer below isolates the identities which
are needed by the covariance operator and proves them directly from the
method-of-steps Dickman equation.  In particular, the fact that the scale
function `t` is a null direction is not postulated.

The probability-theoretic exact-total projective limit is kept separate from
these analytic identities: this prevents a choice of a regular conditional
law on a null fibre from silently entering the operator calculation.
-/

open Filter Set
open scoped Interval BigOperators ENNReal NNReal

noncomputable section

namespace Erdos390.Full.ConditionedPoissonLimit

open MeasureTheory ProbabilityTheory Real
open DickmanBasic

/-! ## A global method-of-steps Dickman function -/































































































/-! ## Density-weighted Palm moments and covariance -/



lemma continuous_covarianceKernel :
    Continuous (Function.uncurry covarianceKernel) := by
  unfold covarianceKernel Function.uncurry
  exact (continuous_F.comp (continuous_fst.add continuous_snd)).sub
    ((continuous_F.comp continuous_fst).mul (continuous_F.comp continuous_snd))

/-! ## The removable axis singularity and a continuous kernel representative -/

















































/-! ## The measurable Cauchy endpoint of the kernel argument -/





/-! The Palm argument produces additivity first on the positive triangle.
The following deterministic lemma records that no global Cauchy equation is
needed: continuity on the closed unit interval and local additivity already
force one common slope. -/







end Erdos390.Full.ConditionedPoissonLimit

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





lemma continuous_covarianceKernelDerivativeSecondExtension_left (s : ℝ) :
    Continuous (covarianceKernelDerivativeSecondExtension s) := by
  unfold covarianceKernelDerivativeSecondExtension
  exact (continuous_derivFExtension.comp
      (continuous_const.add continuous_id)).sub
    (continuous_const.mul continuous_derivFExtension)

lemma continuous_uncurry_covarianceKernelDerivativeSecondExtension :
    Continuous (Function.uncurry covarianceKernelDerivativeSecondExtension) := by
  unfold covarianceKernelDerivativeSecondExtension Function.uncurry
  exact (continuous_derivFExtension.comp
      (continuous_fst.add continuous_snd)).sub
    ((continuous_F.comp continuous_fst).mul
      (continuous_derivFExtension.comp continuous_snd))

/-- Uniform `C¹` bound for the actual kernel family on the unit square. -/
theorem exists_covarianceKernel_uniform_C1_bound :
    ∃ M : ℝ, 0 < M ∧
      ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
        |covarianceKernel s t| ≤ M ∧
        |covarianceKernelDerivativeSecondExtension s t| ≤ M := by
  let S : Set (ℝ × ℝ) := Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1
  have hScompact : IsCompact S := isCompact_Icc.prod isCompact_Icc
  obtain ⟨C₀, hC₀⟩ := hScompact.exists_bound_of_continuousOn
    continuous_covarianceKernel.continuousOn
  obtain ⟨C₁, hC₁⟩ := hScompact.exists_bound_of_continuousOn
    continuous_uncurry_covarianceKernelDerivativeSecondExtension.continuousOn
  have hmem : ((0 : ℝ), (0 : ℝ)) ∈ S := ⟨by norm_num, by norm_num⟩
  have hC₀nonneg : 0 ≤ C₀ :=
    (norm_nonneg (covarianceKernel 0 0)).trans (hC₀ (0, 0) hmem)
  have hC₁nonneg : 0 ≤ C₁ :=
    (norm_nonneg (covarianceKernelDerivativeSecondExtension 0 0)).trans
      (hC₁ (0, 0) hmem)
  refine ⟨1 + C₀ + C₁, by linarith, ?_⟩
  intro s hs t ht
  constructor
  · have h := hC₀ (s, t) ⟨hs, ht⟩
    rw [Real.norm_eq_abs] at h
    change |covarianceKernel s t| ≤ C₀ at h
    linarith
  · have h := hC₁ (s, t) ⟨hs, ht⟩
    rw [Real.norm_eq_abs] at h
    change |covarianceKernelDerivativeSecondExtension s t| ≤ C₁ at h
    linarith

lemma covarianceKernelDerivativeSecondExtension_eq {s t : ℝ}
    (hs : s ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1) :
    covarianceKernelDerivativeSecondExtension s t =
      covarianceKernelDerivativeSecond s t := by
  have hst : s + t ∈ Icc (0 : ℝ) 2 := by
    constructor <;> linarith [hs.1, hs.2, ht.1, ht.2]
  unfold covarianceKernelDerivativeSecondExtension
  unfold covarianceKernelDerivativeSecond
  rw [derivFExtension_eq_deriv_of_mem hst,
    derivFExtension_eq_deriv_of_mem
      ⟨ht.1, ht.2.trans (by norm_num)⟩]

lemma continuous_covarianceKernel_left (s : ℝ) :
    Continuous (covarianceKernel s) := by
  exact continuous_covarianceKernel.comp
    (continuous_const.prodMk continuous_id)

lemma hasDerivAt_covarianceKernel_second {s t : ℝ}
    (hs : s ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1) :
    HasDerivAt (covarianceKernel s)
      (covarianceKernelDerivativeSecond s t) t := by
  have ht₂ : t ∈ Icc (0 : ℝ) 2 :=
    ⟨ht.1, ht.2.trans (by norm_num)⟩
  have hst₂ : s + t ∈ Icc (0 : ℝ) 2 := by
    constructor <;> linarith [hs.1, hs.2, ht.1, ht.2]
  have hshift : HasDerivAt (fun u : ℝ => s + u) 1 t := by
    simpa only [zero_add] using
      (hasDerivAt_const t s).add (hasDerivAt_id t)
  have hfirst := (differentiableAt_F hst₂).hasDerivAt.comp t hshift
  have hsecond := (differentiableAt_F ht₂).hasDerivAt.const_mul (F s)
  convert hfirst.sub hsecond using 1
  unfold covarianceKernelDerivativeSecond
  ring



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















lemma hasDerivAt_kernelWeightedAbelCoefficient {s z x : ℝ}
    (hs : s ∈ Icc (0 : ℝ) 1) (hz : 1 < z)
    (hx : 1 < x) (hxz : x ≤ z) :
    HasDerivAt (kernelWeightedAbelCoefficient s z)
      (kernelWeightedAbelDerivative s z x) x := by
  have ht := realLogCoordinate_mem_unit hz hx.le hxz
  have hkernel := hasDerivAt_covarianceKernel_second hs ht
  have hext := covarianceKernelDerivativeSecondExtension_eq hs ht
  have hkernel' : HasDerivAt (covarianceKernel s)
      (covarianceKernelDerivativeSecondExtension s
        (realLogCoordinate z x)) (realLogCoordinate z x) :=
    hkernel.congr_deriv hext.symm
  exact hasDerivAt_weightedAbelCoefficient
    (covarianceKernel s) (covarianceKernelDerivativeSecondExtension s)
    hz hx hkernel'

lemma deriv_kernelWeightedAbelCoefficient {s z x : ℝ}
    (hs : s ∈ Icc (0 : ℝ) 1) (hz : 1 < z)
    (hx : 1 < x) (hxz : x ≤ z) :
    deriv (kernelWeightedAbelCoefficient s z) x =
      kernelWeightedAbelDerivative s z x :=
  (hasDerivAt_kernelWeightedAbelCoefficient hs hz hx hxz).deriv

lemma continuousAt_kernelWeightedAbelDerivative (s : ℝ)
    {z x : ℝ} (hz : 1 < z) (hx : 1 < x) :
    ContinuousAt (kernelWeightedAbelDerivative s z) x := by
  exact continuousAt_weightedAbelCoefficientDerivative
    (covarianceKernel s) (covarianceKernelDerivativeSecondExtension s)
    (continuous_covarianceKernel_left s)
    (continuous_covarianceKernelDerivativeSecondExtension_left s) hz hx

lemma continuousOn_kernelWeightedAbelDerivative (s : ℝ)
    {z A Y : ℝ} (hz : 1 < z) (hA : 1 < A) :
    ContinuousOn (kernelWeightedAbelDerivative s z) (Icc A Y) := by
  intro x hx
  exact (continuousAt_kernelWeightedAbelDerivative s hz
    (hA.trans_le hx.1)).continuousWithinAt









/-- On an actual prime range below `z`, the ordinary derivative is the
explicit continuous kernel derivative. -/
theorem integrableOn_deriv_kernelWeightedAbelCoefficient
    {s z : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) (hz : 1 < z)
    {Y : ℕ} (hYz : (Y : ℝ) ≤ z) :
    IntegrableOn (deriv (kernelWeightedAbelCoefficient s z))
      (Icc (2 : ℝ) (Y : ℝ)) := by
  have hcont : ContinuousOn (kernelWeightedAbelDerivative s z)
      (Icc (2 : ℝ) (Y : ℝ)) :=
    continuousOn_kernelWeightedAbelDerivative s hz (by norm_num)
  apply (hcont.integrableOn_Icc).congr_fun
  · intro x hx
    symm
    apply deriv_kernelWeightedAbelCoefficient hs hz
    · linarith [hx.1]
    · exact hx.2.trans hYz
  · exact measurableSet_Icc



lemma intervalIntegrable_deriv_kernelWeighted_mul_theta
    {s z : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) (hz : 1 < z)
    {Y : ℕ} (hY : 2 ≤ Y) (hYz : (Y : ℝ) ≤ z) :
    IntervalIntegrable
      (fun x : ℝ => deriv (kernelWeightedAbelCoefficient s z) x *
        Chebyshev.theta x) volume (2 : ℝ) (Y : ℝ) := by
  have h2Y : (2 : ℝ) ≤ (Y : ℝ) := by exact_mod_cast hY
  have hbase := intervalIntegrable_continuous_mul_theta
    (g := kernelWeightedAbelDerivative s z) (A := (2 : ℝ))
    (Y := (Y : ℝ)) (by norm_num) h2Y
    (continuousOn_kernelWeightedAbelDerivative s hz (by norm_num))
  apply hbase.congr
  intro x hx
  have hx' : x ∈ Ioc (2 : ℝ) (Y : ℝ) := by
    simpa only [uIoc_of_le h2Y] using hx
  change kernelWeightedAbelDerivative s z x * Chebyshev.theta x =
    deriv (kernelWeightedAbelCoefficient s z) x * Chebyshev.theta x
  congr 1
  exact (deriv_kernelWeightedAbelCoefficient hs hz
    (by linarith [hx'.1]) (hx'.2.trans hYz)).symm

lemma intervalIntegrable_deriv_kernelWeighted_mul_id
    {s z : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) (hz : 1 < z)
    {A Y : ℕ} (hA : 2 ≤ A) (hAY : A ≤ Y)
    (hYz : (Y : ℝ) ≤ z) :
    IntervalIntegrable
      (fun x : ℝ => deriv (kernelWeightedAbelCoefficient s z) x * x)
      volume (A : ℝ) (Y : ℝ) := by
  have hAR : (2 : ℝ) ≤ (A : ℝ) := by exact_mod_cast hA
  have hAYR : (A : ℝ) ≤ (Y : ℝ) := by exact_mod_cast hAY
  have hcont : ContinuousOn
      (fun x : ℝ => kernelWeightedAbelDerivative s z x * x)
      (Icc (A : ℝ) (Y : ℝ)) :=
    (continuousOn_kernelWeightedAbelDerivative s hz (by linarith [hAR])).mul
      continuousOn_id
  have hbase : IntervalIntegrable
      (fun x : ℝ => kernelWeightedAbelDerivative s z x * x)
      volume (A : ℝ) (Y : ℝ) :=
    hcont.intervalIntegrable_of_Icc (μ := volume) hAYR
  apply hbase.congr
  intro x hx
  have hx' : x ∈ Ioc (A : ℝ) (Y : ℝ) := by
    simpa only [uIoc_of_le hAYR] using hx
  change kernelWeightedAbelDerivative s z x * x =
    deriv (kernelWeightedAbelCoefficient s z) x * x
  congr 1
  exact (deriv_kernelWeightedAbelCoefficient hs hz
    (by linarith [hAR, hx'.1]) (hx'.2.trans hYz)).symm

























/-- Exact one-index prime-cell quadrature for the actual
Poisson--Dickman kernel.  The right side is the literal PNT remainder; no
asymptotic estimate or probability input is assumed. -/
theorem kernel_primeCell_sub_continuum_eq_remainder
    {s z : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) (hz : 1 < z)
    {A Y : ℕ} (hA : 2 ≤ A) (hAY : A ≤ Y)
    (hYz : (Y : ℝ) ≤ z) :
    fullWeightedReciprocalSum (covarianceKernel s) z Y -
        fullWeightedReciprocalSum (covarianceKernel s) z A -
        (∫ t in realLogCoordinate z (A : ℝ)..
          realLogCoordinate z (Y : ℝ), covarianceKernel s t / t) =
      weightedAbelRemainder (covarianceKernel s) z (A : ℝ) (Y : ℝ) := by
  have hY : 2 ≤ Y := hA.trans hAY
  have hAR : (2 : ℝ) ≤ (A : ℝ) := by exact_mod_cast hA
  have hAYR : (A : ℝ) ≤ (Y : ℝ) := by exact_mod_cast hAY
  have h2Y : (2 : ℝ) ≤ (Y : ℝ) := hAR.trans hAYR
  have hdiff : ∀ x ∈ Icc (2 : ℝ) (Y : ℝ),
      DifferentiableAt ℝ
        (weightedAbelCoefficient (covarianceKernel s) z) x := by
    intro x hx
    change DifferentiableAt ℝ (kernelWeightedAbelCoefficient s z) x
    exact (hasDerivAt_kernelWeightedAbelCoefficient hs hz
      (by linarith [hx.1]) (hx.2.trans hYz)).differentiableAt
  have hint : IntegrableOn
      (deriv (weightedAbelCoefficient (covarianceKernel s) z))
      (Icc (2 : ℝ) (Y : ℝ)) := by
    simpa only [kernelWeightedAbelCoefficient] using
      integrableOn_deriv_kernelWeightedAbelCoefficient hs hz hYz
  have hThetaInt : IntervalIntegrable
      (fun x : ℝ =>
        deriv (weightedAbelCoefficient (covarianceKernel s) z) x *
          Chebyshev.theta x) volume (2 : ℝ) (Y : ℝ) := by
    simpa only [kernelWeightedAbelCoefficient] using
      intervalIntegrable_deriv_kernelWeighted_mul_theta hs hz hY hYz
  have hMainInt : IntervalIntegrable
      (fun x : ℝ =>
        deriv (weightedAbelCoefficient (covarianceKernel s) z) x * x)
      volume (A : ℝ) (Y : ℝ) := by
    simpa only [kernelWeightedAbelCoefficient] using
      intervalIntegrable_deriv_kernelWeighted_mul_id hs hz hA hAY hYz
  have hErrorInt : IntervalIntegrable
      (fun x : ℝ =>
        deriv (weightedAbelCoefficient (covarianceKernel s) z) x * thetaError x)
      volume (A : ℝ) (Y : ℝ) := by
    have hThetaCell : IntervalIntegrable
        (fun x : ℝ =>
          deriv (weightedAbelCoefficient (covarianceKernel s) z) x *
            Chebyshev.theta x) volume (A : ℝ) (Y : ℝ) := by
      apply hThetaInt.mono_set
      rw [uIcc_of_le hAYR, uIcc_of_le h2Y]
      intro x hx
      exact ⟨hAR.trans hx.1, hx.2⟩
    have hsub := hThetaCell.sub hMainInt
    apply hsub.congr
    intro x hx
    unfold thetaError
    ring
  have hdecomp :=
    fullWeightedReciprocalSum_interval_sub_main_eq_remainder
      (covarianceKernel s) z hA hAY hdiff hint hThetaInt hMainInt hErrorInt
  rw [weightedAbelMain_eq_logCoordinateIntegral
    (covarianceKernel s) (continuous_covarianceKernel_left s)
    hz hA hAY hdiff hint] at hdecomp
  exact hdecomp



/-- Unconditional one-index kernel quadrature on every positive moving
prime cell.  A single constant and threshold work simultaneously for all
kernel coordinates, all later cell endpoints, and all ambient scales `z`.
This is the quantitative positive-cell input needed by the two-index
operator transfer. -/
theorem exists_uniform_kernel_primeCell_error_bound :
    ∃ D : ℝ, 0 < D ∧ ∃ X₀ : ℕ,
      ∀ s ∈ Icc (0 : ℝ) 1, ∀ z : ℝ, 1 < z →
      ∀ A Y : ℕ, X₀ ≤ A → A ≤ Y → (Y : ℝ) ≤ z →
        |fullWeightedReciprocalSum (covarianceKernel s) z Y -
            fullWeightedReciprocalSum (covarianceKernel s) z A -
            (∫ t in realLogCoordinate z (A : ℝ)..
              realLogCoordinate z (Y : ℝ), covarianceKernel s t / t)| ≤
          D / Real.log (A : ℝ) ^ 3 := by
  obtain ⟨C, hC, X₀R, hTheta⟩ := exists_thetaError_log_cube_bound
  obtain ⟨M, hM, hK⟩ := exists_covarianceKernel_uniform_C1_bound
  obtain ⟨N, hX₀N⟩ := exists_nat_gt X₀R
  refine ⟨6 * (C * M), by positivity, max N 2, ?_⟩
  intro s hs z hz A Y hA hAY hYz
  have hA2 : 2 ≤ A := (le_max_right N 2).trans hA
  have hNA : N ≤ A := (le_max_left N 2).trans hA
  have hNAR : (N : ℝ) ≤ (A : ℝ) := by exact_mod_cast hNA
  rw [kernel_primeCell_sub_continuum_eq_remainder hs hz hA2 hAY hYz]
  apply abs_kernelWeightedAbelRemainder_le hC.le hM.le hs hz hA2 hAY hYz hK
  intro x hx
  apply hTheta x
  exact le_trans (le_of_lt hX₀N) (hNAR.trans hx.1)

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















/-- Unconditional two-index positive-cell quadrature.  The PNT constant and
threshold are selected before the ambient scale and both moving cells.  The
two terms display the input and output quadrature losses separately. -/
theorem exists_uniform_doubleKernelCell_error_bound :
    ∃ D : ℝ, 0 < D ∧ ∃ X₀ : ℕ,
      ∀ z : ℝ, 1 < z →
      ∀ A₁ Y₁ A₂ Y₂ : ℕ,
        X₀ ≤ A₁ → A₁ ≤ Y₁ → (Y₁ : ℝ) ≤ z →
        X₀ ≤ A₂ → A₂ ≤ Y₂ → (Y₂ : ℝ) ≤ z →
        |doublePrimeKernelCell z A₁ Y₁ A₂ Y₂ -
            doubleContinuumKernelCell z A₁ Y₁ A₂ Y₂| ≤
          (D / Real.log (A₂ : ℝ) ^ 3) *
              (fullReciprocalSum Y₁ - fullReciprocalSum A₁) +
            (D / Real.log (A₁ : ℝ) ^ 3) *
              (Real.log (realLogCoordinate z (Y₂ : ℝ)) -
                Real.log (realLogCoordinate z (A₂ : ℝ))) := by
  obtain ⟨D, hD, X₀, hquad⟩ :=
    exists_uniform_kernel_primeCell_error_bound
  refine ⟨D, hD, max X₀ 2, ?_⟩
  intro z hz A₁ Y₁ A₂ Y₂ hA₁ hA₁Y₁ hY₁z
    hA₂ hA₂Y₂ hY₂z
  have hA₁base : X₀ ≤ A₁ := (le_max_left X₀ 2).trans hA₁
  have hA₂base : X₀ ≤ A₂ := (le_max_left X₀ 2).trans hA₂
  have hA₁two : 2 ≤ A₁ := (le_max_right X₀ 2).trans hA₁
  have hA₂two : 2 ≤ A₂ := (le_max_right X₀ 2).trans hA₂
  apply doubleKernelCell_error_le_of_oneIndex hz
    hA₁two hA₁Y₁ hY₁z hA₂two hA₂Y₂ hY₂z
  · intro t ht
    change |fullWeightedReciprocalSum (covarianceKernel t) z Y₁ -
        fullWeightedReciprocalSum (covarianceKernel t) z A₁ -
        (∫ u in realLogCoordinate z (A₁ : ℝ)..
          realLogCoordinate z (Y₁ : ℝ), covarianceKernel t u / u)| ≤
      D / Real.log (A₁ : ℝ) ^ 3
    exact hquad t ht z hz A₁ Y₁ hA₁base hA₁Y₁ hY₁z
  · intro s hs
    change |fullWeightedReciprocalSum (covarianceKernel s) z Y₂ -
        fullWeightedReciprocalSum (covarianceKernel s) z A₂ -
        (∫ u in realLogCoordinate z (A₂ : ℝ)..
          realLogCoordinate z (Y₂ : ℝ), covarianceKernel s u / u)| ≤
      D / Real.log (A₂ : ℝ) ^ 3
    exact hquad s hs z hz A₂ Y₂ hA₂base hA₂Y₂ hY₂z

/-! ## Moving-low input cell -/















/-- Product-kernel version of the continuum cell estimate, retaining the
first coordinate. -/
lemma abs_continuumCellKernel_le_productLength
    {C s z : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) (hz : 1 < z)
    {A Y : ℕ} (hA : 2 ≤ A) (hAY : A ≤ Y) (hYz : (Y : ℝ) ≤ z)
    (hK : ∀ u ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
      |covarianceKernel u t| ≤ C * u * t) :
    |continuumCellOperator z A Y (covarianceKernel s)| ≤
      (C * s) *
        (realLogCoordinate z (Y : ℝ) - realLogCoordinate z (A : ℝ)) := by
  let a := realLogCoordinate z (A : ℝ)
  let b := realLogCoordinate z (Y : ℝ)
  have ha : 0 < a := realLogCoordinate_pos_nat hz hA
  have hab : a ≤ b := realLogCoordinate_mono_nat hz hA hAY
  unfold continuumCellOperator
  change |∫ t in a..b, covarianceKernel s t / t| ≤ (C * s) * (b - a)
  have hnorm := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := a) (b := b) (C := C * s)
    (f := fun t : ℝ => covarianceKernel s t / t) (fun t ht => by
      have ht' : t ∈ uIcc a b := uIoc_subset_uIcc ht
      have htIcc : t ∈ Icc a b := by simpa only [uIcc_of_le hab] using ht'
      have htUnit := coordinateCell_mem_unit hz hA hAY hYz htIcc
      have htpos : 0 < t := ha.trans_le htIcc.1
      rw [Real.norm_eq_abs, abs_div, abs_of_pos htpos]
      exact (div_le_iff₀ htpos).2 (hK s hs t htUnit))
  rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hab)] at hnorm
  exact hnorm

/-- The iterated continuum kernel numerator is bounded by the product of
the two ordinary logarithmic-coordinate lengths. -/
lemma abs_doubleContinuumKernelCell_le_productLengths
    {C z : ℝ} (hz : 1 < z)
    {A₁ Y₁ A₂ Y₂ : ℕ}
    (hA₁ : 2 ≤ A₁) (hA₁Y₁ : A₁ ≤ Y₁) (hY₁z : (Y₁ : ℝ) ≤ z)
    (hA₂ : 2 ≤ A₂) (hA₂Y₂ : A₂ ≤ Y₂) (hY₂z : (Y₂ : ℝ) ≤ z)
    (hK : ∀ u ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
      |covarianceKernel u t| ≤ C * u * t) :
    |doubleContinuumKernelCell z A₁ Y₁ A₂ Y₂| ≤
      C * (realLogCoordinate z (Y₁ : ℝ) -
          realLogCoordinate z (A₁ : ℝ)) *
        (realLogCoordinate z (Y₂ : ℝ) -
          realLogCoordinate z (A₂ : ℝ)) := by
  let a₂ := realLogCoordinate z (A₂ : ℝ)
  let b₂ := realLogCoordinate z (Y₂ : ℝ)
  let ell₁ := realLogCoordinate z (Y₁ : ℝ) -
    realLogCoordinate z (A₁ : ℝ)
  have ha₂ : 0 < a₂ := realLogCoordinate_pos_nat hz hA₂
  have hab₂ : a₂ ≤ b₂ := realLogCoordinate_mono_nat hz hA₂ hA₂Y₂
  unfold doubleContinuumKernelCell continuumCellOperator
  change |∫ t in a₂..b₂,
      continuumCellOperator z A₁ Y₁ (covarianceKernel t) / t| ≤
    C * ell₁ * (b₂ - a₂)
  have hnorm := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := a₂) (b := b₂) (C := C * ell₁)
    (f := fun t : ℝ =>
      continuumCellOperator z A₁ Y₁ (covarianceKernel t) / t)
    (fun t ht => by
      have ht' : t ∈ uIcc a₂ b₂ := uIoc_subset_uIcc ht
      have htIcc : t ∈ Icc a₂ b₂ := by
        simpa only [uIcc_of_le hab₂] using ht'
      have htUnit := coordinateCell_mem_unit hz hA₂ hA₂Y₂ hY₂z htIcc
      have htpos : 0 < t := ha₂.trans_le htIcc.1
      rw [Real.norm_eq_abs, abs_div, abs_of_pos htpos]
      have hinner := abs_continuumCellKernel_le_productLength
        htUnit hz hA₁ hA₁Y₁ hY₁z hK
      exact (div_le_iff₀ htpos).2 (by
        calc
          |continuumCellOperator z A₁ Y₁ (covarianceKernel t)| ≤
              (C * t) * ell₁ := hinner
          _ = (C * ell₁) * t := by ring))
  rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hab₂)] at hnorm
  simpa [ell₁] using hnorm









/-- Exact relative output transfer.  This is the normalization mechanism
which absorbs a bounded fixed-cutoff error on the moving low output row. -/
theorem normalizedDoubleKernelCell_error_le
    {z : ℝ} {A₁ Y₁ A₂ Y₂ : ℕ} {eNumerator eMass : ℝ}
    (hActualMass : 0 < actualCellMass A₁ Y₁)
    (hContinuumMass : continuumCellMass z A₁ Y₁ ≠ 0)
    (hNumerator :
      |doublePrimeKernelCell z A₁ Y₁ A₂ Y₂ -
        doubleContinuumKernelCell z A₁ Y₁ A₂ Y₂| ≤ eNumerator)
    (hMass : |actualCellMass A₁ Y₁ -
      continuumCellMass z A₁ Y₁| ≤ eMass) :
    |normalizedDoublePrimeKernelCell z A₁ Y₁ A₂ Y₂ -
        normalizedDoubleContinuumKernelCell z A₁ Y₁ A₂ Y₂| ≤
      eNumerator / actualCellMass A₁ Y₁ +
        |doubleContinuumKernelCell z A₁ Y₁ A₂ Y₂| * eMass /
          (actualCellMass A₁ Y₁ *
            |continuumCellMass z A₁ Y₁|) := by
  unfold normalizedDoublePrimeKernelCell normalizedDoubleContinuumKernelCell
  exact abs_div_sub_div_le hActualMass hContinuumMass hNumerator hMass

/-- Fully explicit normalized output-row bound obtained by combining double
quadrature, moving-cell mass quadrature, and the product-kernel numerator
bound.  All global constants and thresholds precede the moving cells. -/
theorem exists_uniform_normalizedDoubleKernelCell_error_bound :
    ∃ CKernel : ℝ, 0 < CKernel ∧
    ∃ DKernel : ℝ, 0 < DKernel ∧
    ∃ CMass : ℝ, 0 < CMass ∧
    ∃ X₀ : ℕ,
      ∀ z : ℝ, 1 < z →
      ∀ A₁ Y₁ A₂ Y₂ : ℕ,
        X₀ ≤ A₁ → A₁ ≤ Y₁ → (Y₁ : ℝ) ≤ z →
        X₀ ≤ A₂ → A₂ ≤ Y₂ → (Y₂ : ℝ) ≤ z →
        0 < actualCellMass A₁ Y₁ →
        continuumCellMass z A₁ Y₁ ≠ 0 →
        |normalizedDoublePrimeKernelCell z A₁ Y₁ A₂ Y₂ -
            normalizedDoubleContinuumKernelCell z A₁ Y₁ A₂ Y₂| ≤
          (((DKernel / Real.log (A₂ : ℝ) ^ 3) * actualCellMass A₁ Y₁ +
              (DKernel / Real.log (A₁ : ℝ) ^ 3) *
                continuumCellMass z A₂ Y₂) /
              actualCellMass A₁ Y₁) +
            ((CKernel *
                (realLogCoordinate z (Y₁ : ℝ) - realLogCoordinate z (A₁ : ℝ)) *
                (realLogCoordinate z (Y₂ : ℝ) - realLogCoordinate z (A₂ : ℝ))) *
              (5 * CMass / Real.log (A₁ : ℝ) ^ 3) /
              (actualCellMass A₁ Y₁ *
                |continuumCellMass z A₁ Y₁|)) := by
  obtain ⟨CKernel, hCKernel, hProduct⟩ := kernel_product_bound
  obtain ⟨DKernel, hDKernel, XKernel, hDouble⟩ :=
    exists_uniform_doubleKernelCell_error_bound
  obtain ⟨CMass, hCMass, XMass, hMass⟩ :=
    exists_fullReciprocalSum_interval_error_bound
  refine ⟨CKernel, hCKernel, DKernel, hDKernel, CMass, hCMass,
    max (max XKernel XMass) 2, ?_⟩
  intro z hz A₁ Y₁ A₂ Y₂ hA₁ hA₁Y₁ hY₁z
    hA₂ hA₂Y₂ hY₂z hActualMass hContinuumMass
  have hA₁Kernel : XKernel ≤ A₁ :=
    (le_max_left XKernel XMass).trans
      ((le_max_left (max XKernel XMass) 2).trans hA₁)
  have hA₂Kernel : XKernel ≤ A₂ :=
    (le_max_left XKernel XMass).trans
      ((le_max_left (max XKernel XMass) 2).trans hA₂)
  have hA₁Mass : XMass ≤ A₁ :=
    (le_max_right XKernel XMass).trans
      ((le_max_left (max XKernel XMass) 2).trans hA₁)
  have hA₁two : 2 ≤ A₁ :=
    (le_max_right (max XKernel XMass) 2).trans hA₁
  have hA₂two : 2 ≤ A₂ :=
    (le_max_right (max XKernel XMass) 2).trans hA₂
  have hNum := hDouble z hz A₁ Y₁ A₂ Y₂
    hA₁Kernel hA₁Y₁ hY₁z hA₂Kernel hA₂Y₂ hY₂z
  have hMassRaw := hMass A₁ Y₁ hA₁Mass hA₁Y₁
  have hMassCoord :
      |actualCellMass A₁ Y₁ - continuumCellMass z A₁ Y₁| ≤
        5 * CMass / Real.log (A₁ : ℝ) ^ 3 := by
    unfold actualCellMass continuumCellMass
    rw [show Real.log (realLogCoordinate z (Y₁ : ℝ)) -
        Real.log (realLogCoordinate z (A₁ : ℝ)) =
      Real.log (Real.log (Y₁ : ℝ)) - Real.log (Real.log (A₁ : ℝ)) by
        simpa only [realLogCoordinate, logCoordinate] using
          log_logCoordinate_sub hz hA₁two hA₁Y₁]
    exact hMassRaw
  have hCont := abs_doubleContinuumKernelCell_le_productLengths hz
    hA₁two hA₁Y₁ hY₁z hA₂two hA₂Y₂ hY₂z
    (by
      intro u hu t ht
      simpa only [covarianceKernel] using hProduct u hu t ht)
  have hratio := normalizedDoubleKernelCell_error_le hActualMass hContinuumMass
    hNum hMassCoord
  exact hratio.trans (by
    apply add_le_add
    · exact le_rfl
    · exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right hCont
          (by positivity : 0 ≤ 5 * CMass / Real.log (A₁ : ℝ) ^ 3))
        (mul_nonneg hActualMass.le (abs_nonneg _)))

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









end Mesh
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



















theorem tendsto_positive_endpointInvLogCube_zero
    (hdelta : 0 < delta) (W : ℕ) (k : Fin M.cellCount) :
    Tendsto (fun n : ℕ ↦
      endpointInvLogCube M n W (positiveBand M k))
      atTop (nhds 0) := by
  have hAReal : Tendsto (fun n : ℕ ↦
      (fullCutoff M n W (k.1 + 1) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp
      (tendsto_general_positive_lowerCutoff_atTop M hdelta W k)
  have hLog := Real.tendsto_log_atTop.comp hAReal
  have hInv := tendsto_inv_atTop_zero.comp hLog
  have h := hInv.pow 3
  have h0 : Tendsto (fun n : ℕ ↦
      (Real.log (fullCutoff M n W (k.1 + 1) : ℝ))⁻¹ ^ 3)
      atTop (nhds 0) := by
    simpa only [Function.comp_apply,
      zero_pow (by norm_num : 3 ≠ 0)] using h
  apply h0.congr'
  filter_upwards with n
  unfold endpointInvLogCube positiveBand
  rw [one_div, inv_pow]











/-- The positive-cell cubic cutoff beats the reciprocal moving-low centre.
This is the quantitative low-output/positive-input orientation. -/
theorem tendsto_positive_invLogCube_mul_lowMass_zero
    (hdelta : 0 < delta) {W : ℕ} (hWTwo : 2 ≤ W)
    (k : Fin M.cellCount) :
    Tendsto (fun n : ℕ ↦
      endpointInvLogCube M n W (positiveBand M k) *
        endpointContinuumMass M n W (lowBand M))
      atTop (nhds 0) := by
  have hRate :=
    tendsto_low_endpointContinuumMass_div_log_y_cube_zero M hdelta hWTwo
  have hCoord : Tendsto (fun n : ℕ ↦
      actualCutoffCoordinate M n W (k.1 + 1)) atTop
      (nhds (M.lower k)) := by
    simpa only [actualCutoffCoordinate, fullCutoff_succ,
      RegularRelativeMesh.Mesh.lower] using
        tendsto_floor_scalePoint_coordinate (M.lower_pos hdelta k)
  have hCoordCube := hCoord.pow 3
  have hLowerCube : M.lower k ^ 3 ≠ 0 :=
    pow_ne_zero 3 (ne_of_gt (M.lower_pos hdelta k))
  have hQuot := hRate.div hCoordCube hLowerCube
  have hQuot0 : Tendsto (fun n : ℕ ↦
      (endpointContinuumMass M n W (lowBand M) /
          Real.log (y n) ^ 3) /
        actualCutoffCoordinate M n W (k.1 + 1) ^ 3)
      atTop (nhds 0) := by simpa using hQuot
  apply hQuot0.congr'
  have hCoordNe := hCoord.eventually
    (eventually_ne_nhds (ne_of_gt (M.lower_pos hdelta k)))
  have hLogNe := tendsto_log_y_atTop.eventually (eventually_ne_atTop 0)
  filter_upwards [hCoordNe, hLogNe] with n hcn hln
  have hLogCutoff :
      Real.log (fullCutoff M n W (k.1 + 1) : ℝ) =
        actualCutoffCoordinate M n W (k.1 + 1) * Real.log (y n) := by
    unfold actualCutoffCoordinate realLogCoordinate
    field_simp [hln]
  unfold endpointInvLogCube positiveBand
  rw [hLogCutoff]
  field_simp [hcn, hln]





/-- Endpoint notation is literally the abstract cell-bound notation. -/
theorem normalizedDoubleKernelCellBound_eq_endpointAbstract
    {n W : ℕ} (hn : 1 < n)
    (hmono : Monotone (fullCutoff M n W))
    (hLowerTwo : ∀ j : Fin (M.cellCount + 1),
      2 ≤ fullCutoff M n W j.1)
    (hMassPos : ∀ j : Fin (M.cellCount + 1),
      0 < endpointContinuumMass M n W j)
    (CKernel DKernel CMass : ℝ)
    (i j : Fin (M.cellCount + 1)) :
    normalizedDoubleKernelCellBound CKernel DKernel CMass (y n)
        (fullCutoff M n W i.1) (fullCutoff M n W (i.1 + 1))
        (fullCutoff M n W j.1) (fullCutoff M n W (j.1 + 1)) =
      abstractNormalizedCellBound CKernel DKernel CMass
        (endpointInvLogCube M n W i) (endpointInvLogCube M n W j)
        (endpointActualMass M n W i)
        (endpointContinuumMass M n W i)
        (endpointContinuumMass M n W j)
        (endpointContinuumMoment M n W i)
        (endpointContinuumMoment M n W j) := by
  have hMassI := endpointContinuumMass_eq_doubleKernelMass M hn i
    (hLowerTwo i) (hmono (Nat.le_succ i.1))
  have hMassJ := endpointContinuumMass_eq_doubleKernelMass M hn j
    (hLowerTwo j) (hmono (Nat.le_succ j.1))
  have hLengthI := endpointContinuumMoment_eq_coordinateLength
    M (W := W) hn i
  have hLengthJ := endpointContinuumMoment_eq_coordinateLength
    M (W := W) hn j
  unfold normalizedDoubleKernelCellBound abstractNormalizedCellBound
    endpointInvLogCube endpointActualMass
  rw [← hMassI, ← hMassJ, abs_of_pos (hMassPos i)]
  rw [hLengthI, hLengthJ]
  unfold actualCutoffCoordinate
  ring





end Mesh
end Erdos390.Full.RegularMeshPrimeCutoffs

end

/- Source module: Erdos390.Full.CanonicalEndpointDoubleKernelOrdinaryRowEventually -/
section


/-!
# Canonical endpoint double-kernel quadrature in ordinary raw norm

The sharp row estimate weights an input cell by a ratio of arithmetic
centres.  That is the correct estimate after sharp conjugation, but its
fixed-cutoff constant contains the reciprocal of the moving low centre.
For the ordinary raw norm no centre ratio occurs.  This file repeats only
the final finite summation in that norm and obtains a fixed-cutoff constant
which is independent of the later regular mesh.
-/

open scoped BigOperators
open Filter Topology

noncomputable section

namespace Erdos390.Full.RegularMeshPrimeCutoffs

open ArithmeticModel RegularRelativeMesh
open PrimeBandQuadrature KernelPrimeQuadrature DoubleKernelPrimeQuadrature

namespace Mesh

variable {delta eta : ℝ} (M : Mesh delta eta)





/-- Removing the sharp centre ratio from the abstract cell estimate removes
the dangerous reciprocal low-centre factor as well. -/
theorem abstractNormalizedCellBound_le_ordinaryCoarse
    {CKernel DKernel CMass rOut rIn actualOutMass
      continuumOutMass continuumInMass outLength inLength : ℝ}
    (hC : 0 ≤ CKernel) (hD : 0 ≤ DKernel) (hCMass : 0 ≤ CMass)
    (hrOut : 0 ≤ rOut)
    (hActual : 0 < actualOutMass)
    (hOutMass : 0 < continuumOutMass)
    (hInMass : 0 < continuumInMass)
    (hOutLength : 0 ≤ outLength) (hInLength : 0 ≤ inLength)
    (hMassLower : continuumOutMass / 2 ≤ actualOutMass) :
    abstractNormalizedCellBound CKernel DKernel CMass rOut rIn
        actualOutMass continuumOutMass continuumInMass outLength inLength ≤
      DKernel * rIn +
        2 * DKernel * rOut * (continuumInMass / continuumOutMass) +
        10 * CKernel * CMass * rOut *
          (outLength * inLength / continuumOutMass ^ 2) := by
  have hInv : 1 / actualOutMass ≤ 2 / continuumOutMass := by
    rw [div_le_div_iff₀ hActual hOutMass]
    linarith
  have hFirst :
      (DKernel * rIn * actualOutMass +
          DKernel * rOut * continuumInMass) / actualOutMass =
        DKernel * rIn +
          (DKernel * rOut * continuumInMass) * (1 / actualOutMass) := by
    field_simp [ne_of_gt hActual]
  have hSecond :
      (DKernel * rOut * continuumInMass) * (1 / actualOutMass) ≤
        2 * DKernel * rOut * (continuumInMass / continuumOutMass) := by
    calc
      (DKernel * rOut * continuumInMass) * (1 / actualOutMass) ≤
          (DKernel * rOut * continuumInMass) *
            (2 / continuumOutMass) := by gcongr
      _ = 2 * DKernel * rOut *
          (continuumInMass / continuumOutMass) := by ring
  have hThird :
      CKernel * outLength * inLength * (5 * CMass * rOut) /
          (actualOutMass * continuumOutMass) ≤
        10 * CKernel * CMass * rOut *
          (outLength * inLength / continuumOutMass ^ 2) := by
    have hDenInv : 1 / (actualOutMass * continuumOutMass) ≤
        2 / continuumOutMass ^ 2 := by
      have hmul := mul_le_mul_of_nonneg_right hInv
        (one_div_nonneg.mpr hOutMass.le)
      have hrewriteLeft :
          (1 / actualOutMass) * (1 / continuumOutMass) =
            1 / (actualOutMass * continuumOutMass) := by ring
      have hrewriteRight :
          (2 / continuumOutMass) * (1 / continuumOutMass) =
            2 / continuumOutMass ^ 2 := by ring
      simpa only [hrewriteLeft, hrewriteRight] using hmul
    calc
      CKernel * outLength * inLength * (5 * CMass * rOut) /
          (actualOutMass * continuumOutMass) =
        (5 * CKernel * CMass * rOut * outLength * inLength) *
          (1 / (actualOutMass * continuumOutMass)) := by ring
      _ ≤ (5 * CKernel * CMass * rOut * outLength * inLength) *
          (2 / continuumOutMass ^ 2) := by gcongr
      _ = 10 * CKernel * CMass * rOut *
          (outLength * inLength / continuumOutMass ^ 2) := by ring
  unfold abstractNormalizedCellBound
  rw [hFirst]
  exact add_le_add (add_le_add le_rfl hSecond) hThird

theorem endpointDoubleKernelOrdinaryCoarseRow_eq
    (CKernel DKernel CMass : ℝ) (n W : ℕ)
    (i : Fin (M.cellCount + 1)) :
    endpointDoubleKernelOrdinaryCoarseRow
        M CKernel DKernel CMass n W i =
      DKernel * (∑ j, endpointInvLogCube M n W j) +
        2 * DKernel * endpointInvLogCube M n W i *
          ((∑ j, endpointContinuumMass M n W j) /
            endpointContinuumMass M n W i) +
        10 * CKernel * CMass * endpointInvLogCube M n W i *
          (endpointContinuumMoment M n W i *
            (∑ j, endpointContinuumMoment M n W j) /
              endpointContinuumMass M n W i ^ 2) := by
  unfold endpointDoubleKernelOrdinaryCoarseRow
    endpointDoubleKernelOrdinaryCoarseEntry
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  rw [← Finset.mul_sum]
  rw [show (∑ x : Fin (M.cellCount + 1),
      2 * DKernel * endpointInvLogCube M n W i *
        (endpointContinuumMass M n W x /
          endpointContinuumMass M n W i)) =
      2 * DKernel * endpointInvLogCube M n W i *
        ((∑ x, endpointContinuumMass M n W x) /
          endpointContinuumMass M n W i) by
    rw [Finset.sum_div, Finset.mul_sum] ]
  rw [show (∑ x : Fin (M.cellCount + 1),
      10 * CKernel * CMass * endpointInvLogCube M n W i *
        (endpointContinuumMoment M n W i *
          endpointContinuumMoment M n W x /
            endpointContinuumMass M n W i ^ 2)) =
      10 * CKernel * CMass * endpointInvLogCube M n W i *
        (endpointContinuumMoment M n W i *
          (∑ x, endpointContinuumMoment M n W x) /
            endpointContinuumMass M n W i ^ 2) by
    calc
      _ = ∑ x : Fin (M.cellCount + 1),
          (10 * CKernel * CMass * endpointInvLogCube M n W i *
            endpointContinuumMoment M n W i /
              endpointContinuumMass M n W i ^ 2) *
                endpointContinuumMoment M n W x := by
          apply Finset.sum_congr rfl
          intro x hx
          ring
      _ = (10 * CKernel * CMass * endpointInvLogCube M n W i *
            endpointContinuumMoment M n W i /
              endpointContinuumMass M n W i ^ 2) *
            (∑ x, endpointContinuumMoment M n W x) := by
          rw [Finset.mul_sum]
      _ = _ := by ring]

theorem tendsto_sum_endpointInvLogCube
    (hdelta : 0 < delta) (W : ℕ) :
    Tendsto (fun n : ℕ ↦
      ∑ j : Fin (M.cellCount + 1), endpointInvLogCube M n W j)
      atTop (nhds (1 / Real.log (W : ℝ) ^ 3)) := by
  have hEach : ∀ j : Fin (M.cellCount + 1), Tendsto (fun n : ℕ ↦
      endpointInvLogCube M n W j) atTop
      (nhds (Fin.cases (1 / Real.log (W : ℝ) ^ 3)
        (fun _ : Fin M.cellCount ↦ 0) j)) := by
    intro j
    refine Fin.cases ?_ (fun k ↦ ?_) j
    · simpa only [Fin.cases_zero, lowBand, endpointInvLogCube_low] using
        (tendsto_const_nhds : Tendsto
          (fun _n : ℕ ↦ 1 / Real.log (W : ℝ) ^ 3) atTop
            (nhds (1 / Real.log (W : ℝ) ^ 3)))
    · simpa only [Fin.cases_succ] using
        tendsto_positive_endpointInvLogCube_zero M hdelta W k
  have hSum := tendsto_finset_sum Finset.univ (fun j _hj ↦ hEach j)
  have hLimit : (∑ j : Fin (M.cellCount + 1),
      Fin.cases (1 / Real.log (W : ℝ) ^ 3)
        (fun _ : Fin M.cellCount ↦ 0) j) =
      1 / Real.log (W : ℝ) ^ 3 := by
    rw [Fin.sum_univ_succ]
    simp
  simpa only [hLimit] using hSum

theorem tendsto_sum_endpointContinuumMoment_one
    (hdelta : 0 < delta) (W : ℕ) :
    Tendsto (fun n : ℕ ↦
      ∑ j : Fin (M.cellCount + 1), endpointContinuumMoment M n W j)
      atTop (nhds 1) := by
  have hEach : ∀ j : Fin (M.cellCount + 1), Tendsto (fun n : ℕ ↦
      endpointContinuumMoment M n W j) atTop
      (nhds (Fin.cases (motive := fun _ ↦ ℝ) delta
        (fun k : Fin M.cellCount ↦ M.width k) j)) := by
    intro j
    refine Fin.cases ?_ (fun k ↦ ?_) j
    · simpa only [Fin.cases_zero] using
        tendsto_low_endpointContinuumMoment M hdelta W
    · simpa only [Fin.cases_succ] using
        tendsto_positive_endpointContinuumMoment M hdelta W k
  have hSum := tendsto_finset_sum Finset.univ (fun j _hj ↦ hEach j)
  have hLimit : (∑ j : Fin (M.cellCount + 1),
      Fin.cases (motive := fun _ ↦ ℝ) delta
        (fun k : Fin M.cellCount ↦ M.width k) j) = (1 : ℝ) := by
    rw [Fin.sum_univ_succ]
    simp only [Fin.cases_zero, Fin.cases_succ]
    rw [M.sum_width_eq_one_sub_delta]
    ring
  simpa only [hLimit] using hSum

theorem tendsto_positive_endpointContinuumMass_sum
    (hdelta : 0 < delta) (W : ℕ) :
    Tendsto (fun n : ℕ ↦
      ∑ k : Fin M.cellCount,
        endpointContinuumMass M n W (positiveBand M k)) atTop
      (nhds (∑ k : Fin M.cellCount,
        (Real.log (M.upper k) - Real.log (M.lower k)))) := by
  exact tendsto_finset_sum Finset.univ (fun k _hk ↦
    tendsto_positive_endpointContinuumMass M hdelta W k)

/-- In the moving low row the total continuum harmonic mass is asymptotic
to the low-cell harmonic mass. -/
theorem tendsto_sum_endpointContinuumMass_div_low_one
    (hdelta : 0 < delta) (W : ℕ) :
    Tendsto (fun n : ℕ ↦
      (∑ j : Fin (M.cellCount + 1), endpointContinuumMass M n W j) /
        endpointContinuumMass M n W (lowBand M)) atTop (nhds 1) := by
  have hLow := tendsto_low_endpointContinuumMass_atTop M hdelta W
  have hPos := tendsto_positive_endpointContinuumMass_sum M hdelta W
  have hPosDiv := hPos.div_atTop hLow
  have hLowNe : ∀ᶠ n : ℕ in atTop,
      endpointContinuumMass M n W (lowBand M) ≠ 0 :=
    hLow.eventually (eventually_ne_atTop 0)
  have hRewrite : ∀ᶠ n : ℕ in atTop,
      (∑ j : Fin (M.cellCount + 1), endpointContinuumMass M n W j) /
          endpointContinuumMass M n W (lowBand M) =
        1 +
          (∑ k : Fin M.cellCount,
            endpointContinuumMass M n W (positiveBand M k)) /
              endpointContinuumMass M n W (lowBand M) := by
    filter_upwards [hLowNe] with n hzero
    rw [Fin.sum_univ_succ]
    change (endpointContinuumMass M n W (lowBand M) +
        ∑ k : Fin M.cellCount,
          endpointContinuumMass M n W (positiveBand M k)) /
          endpointContinuumMass M n W (lowBand M) = _
    field_simp [hzero]
  have hAdd : Tendsto (fun n : ℕ ↦
      (1 : ℝ) +
        (∑ k : Fin M.cellCount,
          endpointContinuumMass M n W (positiveBand M k)) /
            endpointContinuumMass M n W (lowBand M)) atTop (nhds 1) := by
    simpa only [add_zero] using
      (tendsto_const_nhds.add hPosDiv : Tendsto (fun n : ℕ ↦
        (1 : ℝ) +
          (∑ k : Fin M.cellCount,
            endpointContinuumMass M n W (positiveBand M k)) /
              endpointContinuumMass M n W (lowBand M)) atTop
        (nhds ((1 : ℝ) + 0)))
  exact hAdd.congr' (hRewrite.mono fun n hn ↦ hn.symm)

theorem tendsto_positive_invLogCube_mul_sumContinuumMass_zero
    (hdelta : 0 < delta) {W : ℕ} (hWTwo : 2 ≤ W)
    (k : Fin M.cellCount) :
    Tendsto (fun n : ℕ ↦
      endpointInvLogCube M n W (positiveBand M k) *
        (∑ j : Fin (M.cellCount + 1), endpointContinuumMass M n W j))
      atTop (nhds 0) := by
  have hLow := tendsto_positive_invLogCube_mul_lowMass_zero
    M hdelta hWTwo k
  have hInv := tendsto_positive_endpointInvLogCube_zero M hdelta W k
  have hPos := tendsto_positive_endpointContinuumMass_sum M hdelta W
  have hPosPart := hInv.mul hPos
  have hSplit : ∀ n : ℕ,
      endpointInvLogCube M n W (positiveBand M k) *
          (∑ j : Fin (M.cellCount + 1), endpointContinuumMass M n W j) =
        endpointInvLogCube M n W (positiveBand M k) *
            endpointContinuumMass M n W (lowBand M) +
          endpointInvLogCube M n W (positiveBand M k) *
            (∑ j : Fin M.cellCount,
              endpointContinuumMass M n W (positiveBand M j)) := by
    intro n
    rw [Fin.sum_univ_succ]
    change _ * (endpointContinuumMass M n W (lowBand M) +
      ∑ j : Fin M.cellCount,
        endpointContinuumMass M n W (positiveBand M j)) = _
    ring
  have hSum : Tendsto (fun n : ℕ ↦
      endpointInvLogCube M n W (positiveBand M k) *
          endpointContinuumMass M n W (lowBand M) +
        endpointInvLogCube M n W (positiveBand M k) *
          (∑ j : Fin M.cellCount,
            endpointContinuumMass M n W (positiveBand M j)))
      atTop (nhds 0) := by
    have hAdd := hLow.add hPosPart
    simpa only [zero_add, zero_mul, add_zero] using hAdd
  exact hSum.congr' (Filter.Eventually.of_forall fun n ↦ (hSplit n).symm)

theorem tendsto_low_endpointDoubleKernelOrdinaryCoarseRow
    (hdelta : 0 < delta) (W : ℕ)
    (CKernel DKernel CMass : ℝ) :
    Tendsto (fun n : ℕ ↦
      endpointDoubleKernelOrdinaryCoarseRow
        M CKernel DKernel CMass n W (lowBand M)) atTop
      (nhds (3 * DKernel / Real.log (W : ℝ) ^ 3)) := by
  have hInv := tendsto_sum_endpointInvLogCube M hdelta W
  have hMassRatio :=
    tendsto_sum_endpointContinuumMass_div_low_one M hdelta W
  have hLowMoment := tendsto_low_endpointContinuumMoment M hdelta W
  have hMomentSum := tendsto_sum_endpointContinuumMoment_one M hdelta W
  have hLowMass := tendsto_low_endpointContinuumMass_atTop M hdelta W
  have hMomentDiv := hLowMoment.div_atTop hLowMass
  have hSumDiv := hMomentSum.div_atTop hLowMass
  have hThirdCore : Tendsto (fun n : ℕ ↦
      endpointContinuumMoment M n W (lowBand M) *
          (∑ j : Fin (M.cellCount + 1),
            endpointContinuumMoment M n W j) /
        endpointContinuumMass M n W (lowBand M) ^ 2) atTop (nhds 0) := by
    have hprod := hMomentDiv.mul hSumDiv
    have hprodZero : Tendsto (fun n : ℕ ↦
        (endpointContinuumMoment M n W (lowBand M) /
            endpointContinuumMass M n W (lowBand M)) *
          ((∑ j : Fin (M.cellCount + 1),
              endpointContinuumMoment M n W j) /
            endpointContinuumMass M n W (lowBand M))) atTop (nhds 0) := by
      simpa only [zero_mul] using hprod
    apply hprodZero.congr'
    have hMassPos := hLowMass.eventually (eventually_gt_atTop 0)
    filter_upwards [hMassPos] with n hn
    field_simp [ne_of_gt hn]
  have hFirst : Tendsto (fun n : ℕ ↦
      DKernel * (∑ j : Fin (M.cellCount + 1),
        endpointInvLogCube M n W j)) atTop
      (nhds (DKernel * (1 / Real.log (W : ℝ) ^ 3))) :=
    tendsto_const_nhds.mul hInv
  have hSecond : Tendsto (fun n : ℕ ↦
      2 * DKernel * endpointInvLogCube M n W (lowBand M) *
        ((∑ j : Fin (M.cellCount + 1),
          endpointContinuumMass M n W j) /
            endpointContinuumMass M n W (lowBand M))) atTop
      (nhds (2 * DKernel * (1 / Real.log (W : ℝ) ^ 3))) := by
    have hconst : Tendsto (fun _n : ℕ ↦
        2 * DKernel * (1 / Real.log (W : ℝ) ^ 3)) atTop
        (nhds (2 * DKernel * (1 / Real.log (W : ℝ) ^ 3))) :=
      tendsto_const_nhds
    have hmul := hconst.mul hMassRatio
    have hmulLimit : Tendsto (fun n : ℕ ↦
        (2 * DKernel * (1 / Real.log (W : ℝ) ^ 3)) *
          ((∑ j : Fin (M.cellCount + 1),
            endpointContinuumMass M n W j) /
              endpointContinuumMass M n W (lowBand M))) atTop
        (nhds (2 * DKernel * (1 / Real.log (W : ℝ) ^ 3))) := by
      simpa only [mul_one] using hmul
    apply hmulLimit.congr'
    filter_upwards with n
    rw [endpointInvLogCube_low]
  have hThird : Tendsto (fun n : ℕ ↦
      10 * CKernel * CMass * endpointInvLogCube M n W (lowBand M) *
        (endpointContinuumMoment M n W (lowBand M) *
          (∑ j : Fin (M.cellCount + 1),
            endpointContinuumMoment M n W j) /
              endpointContinuumMass M n W (lowBand M) ^ 2))
      atTop (nhds 0) := by
    have hconst : Tendsto (fun _n : ℕ ↦
        10 * CKernel * CMass *
          (1 / Real.log (W : ℝ) ^ 3)) atTop
        (nhds (10 * CKernel * CMass *
          (1 / Real.log (W : ℝ) ^ 3))) := tendsto_const_nhds
    have hmul := hconst.mul hThirdCore
    have hmulZero : Tendsto (fun n : ℕ ↦
        (10 * CKernel * CMass * (1 / Real.log (W : ℝ) ^ 3)) *
          (endpointContinuumMoment M n W (lowBand M) *
            (∑ j : Fin (M.cellCount + 1),
              endpointContinuumMoment M n W j) /
                endpointContinuumMass M n W (lowBand M) ^ 2))
        atTop (nhds 0) := by
      simpa only [mul_zero] using hmul
    apply hmulZero.congr'
    filter_upwards with n
    rw [endpointInvLogCube_low]
  rw [show 3 * DKernel / Real.log (W : ℝ) ^ 3 =
      DKernel * (1 / Real.log (W : ℝ) ^ 3) +
        2 * DKernel * (1 / Real.log (W : ℝ) ^ 3) + 0 by ring]
  apply ((hFirst.add hSecond).add hThird).congr'
  filter_upwards with n
  rw [endpointDoubleKernelOrdinaryCoarseRow_eq]

theorem tendsto_positive_endpointDoubleKernelOrdinaryCoarseRow
    (hdelta : 0 < delta) {W : ℕ} (hWTwo : 2 ≤ W)
    (CKernel DKernel CMass : ℝ) (k : Fin M.cellCount) :
    Tendsto (fun n : ℕ ↦
      endpointDoubleKernelOrdinaryCoarseRow M CKernel DKernel CMass n W
        (positiveBand M k)) atTop
      (nhds (DKernel / Real.log (W : ℝ) ^ 3)) := by
  have hInvSum := tendsto_sum_endpointInvLogCube M hdelta W
  have hInv := tendsto_positive_endpointInvLogCube_zero M hdelta W k
  have hMassSum := tendsto_positive_invLogCube_mul_sumContinuumMass_zero M
    hdelta hWTwo k
  have hMass := tendsto_positive_endpointContinuumMass M hdelta W k
  have hMoment := tendsto_positive_endpointContinuumMoment M hdelta W k
  have hMomentSum := tendsto_sum_endpointContinuumMoment_one M hdelta W
  let Hk : ℝ := Real.log (M.upper k) - Real.log (M.lower k)
  have hHk : 0 < Hk := by
    dsimp only [Hk]
    exact sub_pos.mpr (Real.strictMonoOn_log (M.lower_pos hdelta k)
      ((M.lower_pos hdelta k).trans (M.lower_lt_upper hdelta k))
      (M.lower_lt_upper hdelta k))
  have hSecondCore := hMassSum.div hMass (ne_of_gt hHk)
  have hThirdCore : Tendsto (fun n : ℕ ↦
      endpointInvLogCube M n W (positiveBand M k) *
        (endpointContinuumMoment M n W (positiveBand M k) *
          (∑ j : Fin (M.cellCount + 1),
            endpointContinuumMoment M n W j) /
              endpointContinuumMass M n W (positiveBand M k) ^ 2))
      atTop (nhds 0) := by
    have hnum := (hInv.mul hMoment).mul hMomentSum
    have hden := hMass.pow 2
    have hquot := hnum.div hden (pow_ne_zero 2 (ne_of_gt hHk))
    have hquotZero : Tendsto (fun n : ℕ ↦
        (endpointInvLogCube M n W (positiveBand M k) *
            endpointContinuumMoment M n W (positiveBand M k) *
              (∑ j : Fin (M.cellCount + 1),
                endpointContinuumMoment M n W j)) /
          endpointContinuumMass M n W (positiveBand M k) ^ 2)
        atTop (nhds 0) := by
      simpa only [zero_mul, mul_zero, zero_div] using hquot
    apply hquotZero.congr'
    filter_upwards with n
    ring
  have hFirst : Tendsto (fun n : ℕ ↦
      DKernel * (∑ j : Fin (M.cellCount + 1),
        endpointInvLogCube M n W j)) atTop
      (nhds (DKernel / Real.log (W : ℝ) ^ 3)) := by
    have hmul : Tendsto (fun n : ℕ ↦
        DKernel * (∑ j : Fin (M.cellCount + 1),
          endpointInvLogCube M n W j)) atTop
        (nhds (DKernel * (1 / Real.log (W : ℝ) ^ 3))) :=
      tendsto_const_nhds.mul hInvSum
    simpa [div_eq_mul_inv] using hmul
  have hSecond : Tendsto (fun n : ℕ ↦
      2 * DKernel * endpointInvLogCube M n W (positiveBand M k) *
        ((∑ j : Fin (M.cellCount + 1),
          endpointContinuumMass M n W j) /
            endpointContinuumMass M n W (positiveBand M k)))
      atTop (nhds 0) := by
    have hSecondCoreZero : Tendsto (fun n : ℕ ↦
        (endpointInvLogCube M n W (positiveBand M k) *
          (∑ j : Fin (M.cellCount + 1),
            endpointContinuumMass M n W j)) /
              endpointContinuumMass M n W (positiveBand M k))
        atTop (nhds 0) := by
      simpa only [zero_div] using hSecondCore
    have hmul : Tendsto (fun n : ℕ ↦
        (2 * DKernel) *
          (endpointInvLogCube M n W (positiveBand M k) *
            (∑ j : Fin (M.cellCount + 1),
              endpointContinuumMass M n W j) /
                endpointContinuumMass M n W (positiveBand M k)))
        atTop (nhds 0) := by
      simpa only [mul_zero] using tendsto_const_nhds.mul hSecondCoreZero
    apply hmul.congr'
    filter_upwards with n
    ring
  have hThird : Tendsto (fun n : ℕ ↦
      10 * CKernel * CMass * endpointInvLogCube M n W (positiveBand M k) *
        (endpointContinuumMoment M n W (positiveBand M k) *
          (∑ j : Fin (M.cellCount + 1),
            endpointContinuumMoment M n W j) /
              endpointContinuumMass M n W (positiveBand M k) ^ 2))
      atTop (nhds 0) := by
    have hmul : Tendsto (fun n : ℕ ↦
        (10 * CKernel * CMass) *
          (endpointInvLogCube M n W (positiveBand M k) *
            (endpointContinuumMoment M n W (positiveBand M k) *
              (∑ j : Fin (M.cellCount + 1),
                endpointContinuumMoment M n W j) /
                  endpointContinuumMass M n W (positiveBand M k) ^ 2)))
        atTop (nhds 0) := by
      simpa only [mul_zero] using tendsto_const_nhds.mul hThirdCore
    apply hmul.congr'
    filter_upwards with n
    ring
  have hTotal : Tendsto (fun n : ℕ ↦
      DKernel * (∑ j : Fin (M.cellCount + 1),
        endpointInvLogCube M n W j) +
      2 * DKernel * endpointInvLogCube M n W (positiveBand M k) *
        ((∑ j : Fin (M.cellCount + 1),
          endpointContinuumMass M n W j) /
            endpointContinuumMass M n W (positiveBand M k)) +
      10 * CKernel * CMass * endpointInvLogCube M n W (positiveBand M k) *
        (endpointContinuumMoment M n W (positiveBand M k) *
          (∑ j : Fin (M.cellCount + 1),
            endpointContinuumMoment M n W j) /
              endpointContinuumMass M n W (positiveBand M k) ^ 2))
      atTop (nhds (DKernel / Real.log (W : ℝ) ^ 3)) := by
    simpa only [add_zero] using (hFirst.add hSecond).add hThird
  apply hTotal.congr'
  filter_upwards with n
  rw [endpointDoubleKernelOrdinaryCoarseRow_eq]

/-- A literal normalized double-kernel cell estimate implies the
centre-free coarse entry used by the ordinary raw norm.  No comparison of
arithmetic centres is needed here. -/
theorem endpointDoubleKernelError_le_ordinaryCoarse
    {n W : ℕ} (hdelta : 0 < delta) (hn : 1 < n)
    (hW : W ≠ 0) (hWTwo : 2 ≤ W) (S : ScaleSeparation M n W)
    (CKernel DKernel CMass : ℝ)
    (hC : 0 ≤ CKernel) (hD : 0 ≤ DKernel) (hCMass : 0 ≤ CMass)
    (hMassPos : ∀ r : Fin (M.cellCount + 1),
      0 < endpointContinuumMass M n W r)
    (hMomentPos : ∀ r : Fin (M.cellCount + 1),
      0 < endpointContinuumMoment M n W r)
    (hMassLower : ∀ r : Fin (M.cellCount + 1),
      endpointContinuumMass M n W r / 2 ≤ endpointActualMass M n W r)
    (i j : Fin (M.cellCount + 1))
    (hError : endpointDoubleKernelError M n W i j ≤
      normalizedDoubleKernelCellBound CKernel DKernel CMass (y n)
        (fullCutoff M n W i.1) (fullCutoff M n W (i.1 + 1))
        (fullCutoff M n W j.1) (fullCutoff M n W (j.1 + 1))) :
    endpointDoubleKernelError M n W i j ≤
      endpointDoubleKernelOrdinaryCoarseEntry
        M CKernel DKernel CMass n W i j := by
  let P := canonicalPartition M hdelta hn hW S
  let E := canonicalCertificate M hdelta hn hW S
  have hmono : Monotone (fullCutoff M n W) :=
    fullCutoff_monotone M hdelta hn (W_le_first_fullCutoff M S)
  have hLowerTwo (r : Fin (M.cellCount + 1)) :
      2 ≤ fullCutoff M n W r.1 :=
    hWTwo.trans (hmono (Nat.zero_le r.1))
  have hActualEq (r : Fin (M.cellCount + 1)) :
      endpointActualMass M n W r = P.mass r := by
    rw [E.mass_eq_fullReciprocalSum_sub]
    rfl
  have hActualPos (r : Fin (M.cellCount + 1)) :
      0 < endpointActualMass M n W r := by
    rw [hActualEq]
    exact P.data.mass_pos r
  have hAbstract := abstractNormalizedCellBound_le_ordinaryCoarse
    (CKernel := CKernel) (DKernel := DKernel) (CMass := CMass)
    (rOut := endpointInvLogCube M n W i)
    (rIn := endpointInvLogCube M n W j)
    (actualOutMass := endpointActualMass M n W i)
    (continuumOutMass := endpointContinuumMass M n W i)
    (continuumInMass := endpointContinuumMass M n W j)
    (outLength := endpointContinuumMoment M n W i)
    (inLength := endpointContinuumMoment M n W j)
    hC hD hCMass
    (by unfold endpointInvLogCube; positivity)
    (hActualPos i) (hMassPos i) (hMassPos j)
    (hMomentPos i).le (hMomentPos j).le (hMassLower i)
  have hIdentification := normalizedDoubleKernelCellBound_eq_endpointAbstract
    M hn hmono hLowerTwo hMassPos CKernel DKernel CMass i j
  calc
    endpointDoubleKernelError M n W i j ≤
        normalizedDoubleKernelCellBound CKernel DKernel CMass (y n)
          (fullCutoff M n W i.1) (fullCutoff M n W (i.1 + 1))
          (fullCutoff M n W j.1) (fullCutoff M n W (j.1 + 1)) := hError
    _ = abstractNormalizedCellBound CKernel DKernel CMass
          (endpointInvLogCube M n W i) (endpointInvLogCube M n W j)
          (endpointActualMass M n W i)
          (endpointContinuumMass M n W i)
          (endpointContinuumMass M n W j)
          (endpointContinuumMoment M n W i)
          (endpointContinuumMoment M n W j) := hIdentification
    _ ≤ endpointDoubleKernelOrdinaryCoarseEntry
          M CKernel DKernel CMass n W i j := by
      simpa only [endpointDoubleKernelOrdinaryCoarseEntry] using hAbstract

/-- Canonical double-kernel quadrature in ordinary raw row norm.  The
constant and cutoff are selected before `delta`, `eta`, and the mesh.  For
each fixed permitted mesh, only the eventual threshold in `n` may depend on
that mesh. -/
theorem exists_cutoff_eventually_canonical_doubleKernelOrdinaryRowError :
    ∃ CRow : ℝ, 0 < CRow ∧ ∃ W₀ : ℕ,
      ∀ {δ ε : ℝ} (N : Mesh δ ε), 0 < δ →
        ∀ W : ℕ, W₀ ≤ W → ∀ e : ℝ, 0 < e →
          ∀ᶠ n : ℕ in atTop,
            ∃ _hW : W ≠ 0, ∃ _hn : 1 < n,
              ∃ _S : ScaleSeparation N n W,
                ∀ i : Fin (N.cellCount + 1),
                  (∑ j : Fin (N.cellCount + 1),
                      endpointDoubleKernelError N n W i j) ≤
                    CRow / Real.log (W : ℝ) ^ 3 + e := by
  obtain ⟨CKernel, hCKernel, DKernel, hDKernel, CMass, hCMass,
    XKernel, hKernel⟩ := exists_uniform_normalizedDoubleKernelCell_error_bound
  obtain ⟨Cmass, hCmass, Xmass, hMass⟩ :=
    exists_fullReciprocalSum_interval_error_bound
  let CRow : ℝ := 3 * DKernel + 1
  let W₀ : ℕ := max 2 (max XKernel Xmass)
  have hCRow : 0 < CRow := by
    dsimp only [CRow]
    positivity
  refine ⟨CRow, hCRow, W₀, ?_⟩
  intro δ ε N hδ
  let M := N
  have hdelta : 0 < δ := hδ
  intro W hW e he
  have hWTwo : 2 ≤ W :=
    (le_max_left 2 (max XKernel Xmass)).trans hW
  have hWne : W ≠ 0 := by omega
  have hXKernel : XKernel ≤ W :=
    ((le_max_left XKernel Xmass).trans
      (le_max_right 2 (max XKernel Xmass))).trans hW
  have hXmass : Xmass ≤ W :=
    ((le_max_right XKernel Xmass).trans
      (le_max_right 2 (max XKernel Xmass))).trans hW
  have hReady := eventually_endpointRelativeCenterBound_le M
    hdelta (W := W) Cmass 0
      (by norm_num : (0 : ℝ) < 1 / 2)
  have hLowCoarse :=
    (tendsto_low_endpointDoubleKernelOrdinaryCoarseRow M
      hdelta W CKernel DKernel CMass).eventually
        (eventually_le_nhds (show
          3 * DKernel / Real.log (W : ℝ) ^ 3 <
            3 * DKernel / Real.log (W : ℝ) ^ 3 + e / 2 by
          linarith))
  have hPositiveCoarse : ∀ᶠ n : ℕ in atTop,
      ∀ k : Fin M.cellCount,
        endpointDoubleKernelOrdinaryCoarseRow
            M CKernel DKernel CMass n W (positiveBand M k) ≤
          DKernel / Real.log (W : ℝ) ^ 3 + e / 2 := by
    rw [Filter.eventually_all]
    intro k
    exact (tendsto_positive_endpointDoubleKernelOrdinaryCoarseRow
      M hdelta hWTwo CKernel DKernel CMass k).eventually
        (eventually_le_nhds (show
          DKernel / Real.log (W : ℝ) ^ 3 <
            DKernel / Real.log (W : ℝ) ^ 3 + e / 2 by
          linarith))
  have hNgt : ∀ᶠ n : ℕ in atTop, 1 < n := eventually_gt_atTop 1
  have hSep := eventually_scaleSeparation M hdelta W
  filter_upwards [hReady, hLowCoarse, hPositiveCoarse, hNgt, hSep] with
    n hReadyN hLowN hPositiveN hn S
  let P := canonicalPartition M hdelta hn hWne S
  let E := canonicalCertificate M hdelta hn hWne S
  have hmono : Monotone (fullCutoff M n W) :=
    fullCutoff_monotone M hdelta hn
      (W_le_first_fullCutoff M S)
  have hy : 1 < y n := by
    have hlog : 0 < Real.log (y n) := by
      rw [Scale.log_y (Nat.zero_lt_of_lt hn)]
      exact mul_pos (by norm_num) (Real.log_pos (by exact_mod_cast hn))
    exact (Real.log_pos_iff (Scale.y_pos (Nat.zero_lt_of_lt hn)).le).mp hlog
  have hMassPos (r : Fin (M.cellCount + 1)) :
      0 < endpointContinuumMass M n W r := (hReadyN r).1
  have hMomentPos (r : Fin (M.cellCount + 1)) :
      0 < endpointContinuumMoment M n W r := (hReadyN r).2.1
  have hMassError (r : Fin (M.cellCount + 1)) :
      |endpointActualMass M n W r - endpointContinuumMass M n W r| ≤
        endpointMassError M Cmass n W r := by
    have hq := hMass (fullCutoff M n W r.1)
      (fullCutoff M n W (r.1 + 1))
      (hXmass.trans (hmono (Nat.zero_le r.1)))
      (hmono (Nat.le_succ r.1))
    simpa only [endpointActualMass, endpointContinuumMass,
      endpointMassError] using hq
  have hMassLower (r : Fin (M.cellCount + 1)) :
      endpointContinuumMass M n W r / 2 ≤ endpointActualMass M n W r := by
    have hleft := (abs_le.mp (hMassError r)).1
    have hsmall := (hReadyN r).2.2.1
    linarith
  have hActualMassPos (r : Fin (M.cellCount + 1)) :
      0 < endpointActualMass M n W r := by
    have hEq : endpointActualMass M n W r = P.mass r := by
      rw [E.mass_eq_fullReciprocalSum_sub]
      rfl
    rw [hEq]
    exact P.data.mass_pos r
  have hY (r : Fin (M.cellCount + 1)) :
      (fullCutoff M n W (r.1 + 1) : ℝ) ≤ y n := by
    have hNat : fullCutoff M n W (r.1 + 1) ≤ yNat n := by
      rw [← fullCutoff_last M (Nat.zero_lt_of_lt hn)]
      exact hmono (by omega)
    exact (by exact_mod_cast hNat :
      (fullCutoff M n W (r.1 + 1) : ℝ) ≤ (yNat n : ℝ)) |>.trans
        (Nat.floor_le (Scale.y_pos (Nat.zero_lt_of_lt hn)).le)
  have hCellError (i j : Fin (M.cellCount + 1)) :
      endpointDoubleKernelError M n W i j ≤
        normalizedDoubleKernelCellBound CKernel DKernel CMass (y n)
          (fullCutoff M n W i.1) (fullCutoff M n W (i.1 + 1))
          (fullCutoff M n W j.1) (fullCutoff M n W (j.1 + 1)) := by
    have hq := hKernel (y n) hy
      (fullCutoff M n W i.1) (fullCutoff M n W (i.1 + 1))
      (fullCutoff M n W j.1) (fullCutoff M n W (j.1 + 1))
      (hXKernel.trans (hmono (Nat.zero_le i.1)))
      (hmono (Nat.le_succ i.1)) (hY i)
      (hXKernel.trans (hmono (Nat.zero_le j.1)))
      (hmono (Nat.le_succ j.1)) (hY j)
      (hActualMassPos i)
      (by
        have hEq := endpointContinuumMass_eq_doubleKernelMass M hn i
          (hWTwo.trans (hmono (Nat.zero_le i.1)))
          (hmono (Nat.le_succ i.1))
        rw [← hEq]
        exact ne_of_gt (hMassPos i))
    simpa only [endpointDoubleKernelError,
      normalizedDoubleKernelCellBound] using hq
  have hPoint (i j : Fin (M.cellCount + 1)) :
      endpointDoubleKernelError M n W i j ≤
        endpointDoubleKernelOrdinaryCoarseEntry
          M CKernel DKernel CMass n W i j :=
    endpointDoubleKernelError_le_ordinaryCoarse
      M hdelta hn hWne hWTwo S
      CKernel DKernel CMass hCKernel.le hDKernel.le hCMass.le
      hMassPos hMomentPos hMassLower i j (hCellError i j)
  have hRow (i : Fin (M.cellCount + 1)) :
      (∑ j : Fin (M.cellCount + 1),
          endpointDoubleKernelError M n W i j) ≤
        endpointDoubleKernelOrdinaryCoarseRow
          M CKernel DKernel CMass n W i := by
    unfold endpointDoubleKernelOrdinaryCoarseRow
    exact Finset.sum_le_sum (fun j _hj ↦ hPoint i j)
  refine ⟨hWne, hn, S, ?_⟩
  intro i
  have hlogW : 0 < Real.log (W : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < W by omega))
  have hInvNonneg : 0 ≤ 1 / Real.log (W : ℝ) ^ 3 := by positivity
  have hCRowIdentity :
      CRow / Real.log (W : ℝ) ^ 3 =
        3 * DKernel / Real.log (W : ℝ) ^ 3 +
          1 / Real.log (W : ℝ) ^ 3 := by
    dsimp only [CRow]
    ring
  refine Fin.cases ?_ (fun k ↦ ?_) i
  · calc
      (∑ j : Fin (M.cellCount + 1),
          endpointDoubleKernelError M n W (lowBand M) j) ≤
        endpointDoubleKernelOrdinaryCoarseRow
          M CKernel DKernel CMass n W (lowBand M) := hRow (lowBand M)
      _ ≤ 3 * DKernel / Real.log (W : ℝ) ^ 3 + e / 2 := hLowN
      _ ≤ CRow / Real.log (W : ℝ) ^ 3 + e := by
        rw [hCRowIdentity]
        nlinarith
  · calc
      (∑ j : Fin (M.cellCount + 1),
          endpointDoubleKernelError M n W (positiveBand M k) j) ≤
        endpointDoubleKernelOrdinaryCoarseRow
          M CKernel DKernel CMass n W (positiveBand M k) :=
            hRow (positiveBand M k)
      _ ≤ DKernel / Real.log (W : ℝ) ^ 3 + e / 2 := hPositiveN k
      _ ≤ CRow / Real.log (W : ℝ) ^ 3 + e := by
        rw [hCRowIdentity]
        have hDNonneg : 0 ≤ DKernel := hDKernel.le
        have hScale :
            DKernel / Real.log (W : ℝ) ^ 3 ≤
              3 * DKernel / Real.log (W : ℝ) ^ 3 := by
          rw [div_eq_mul_inv, div_eq_mul_inv]
          nlinarith [mul_nonneg hDNonneg
            (inv_nonneg.mpr (pow_nonneg hlogW.le 3))]
        linarith


end Mesh
end Erdos390.Full.RegularMeshPrimeCutoffs

end

theorem solution :
∃ CRow,
  And (LT.lt.{0} (0 : Real) CRow)
    (∃ W₀,
      ∀ {δ ε : Real} (N : Erdos390.Full.RegularRelativeMesh.Mesh δ ε),
        LT.lt.{0} (0 : Real) δ →
          ∀ (W : Nat),
            LE.le.{0} W₀ W →
              ∀ (e : Real),
                LT.lt.{0} (0 : Real) e →
                  ∀ᶠ (n : Nat) in Filter.atTop.{0},
                    ∃ (_ : Ne.{1} W (0 : Nat)) (_ : LT.lt.{0} (1 : Nat) n) (_ :
                      Erdos390.Full.RegularMeshPrimeCutoffs.ScaleSeparation N n W),
                      ∀ (i : Fin (HAdd.hAdd.{0, 0, 0} (Erdos390.Full.RegularRelativeMesh.Mesh.cellCount N) (1 : Nat))),
                        LE.le.{0} (∑ j, Erdos390.Full.RegularMeshPrimeCutoffs.Mesh.endpointDoubleKernelError N n W i j)
                          (HAdd.hAdd.{0, 0, 0} (HDiv.hDiv.{0, 0, 0} CRow (HPow.hPow.{0, 0, 0} (Real.log ↑W) (3 : Nat)))
                            e)) := by
  exact @Erdos390.Full.RegularMeshPrimeCutoffs.Mesh.exists_cutoff_eventually_canonical_doubleKernelOrdinaryRowError
