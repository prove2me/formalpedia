-- Prove2me | solution 1 for Erdos390.Full.RegularMeshPrimeCutoffs.Mesh.exists_fineMesh_cutoff_eventually_canonical_ordinaryProjectedRaw_inverse_compact
-- status  : ACCEPTED   (prove)
-- author  : @doctosil
-- created : 2026-09-17T17:40:41.985392+00:00
-- url     : https://prove2.me/submissions/d581a468-a9b3-49bc-9809-67f46983b2c1

import Definitions.Def_erdos390_analytic_compact_goals_006
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
import Theorems.Thm_Erdos390_Full_ContinuumCellGraph_ArithmeticGaugeOrdinary_IntervalMesh_ordinary_split_arithmetic_projected_raw_bound_compact
import Theorems.Thm_Erdos390_Full_ContinuumCellGraph_IntervalMesh_abs_center_mul_integral_div_sub_integral_le
import Theorems.Thm_Erdos390_Full_RegularMeshPrimeCutoffs_Mesh_canonicalPrimeAnchorCutoff_eventually
import Theorems.Thm_Erdos390_Full_RegularMeshPrimeCutoffs_Mesh_exists_cutoff_eventually_canonical_doubleKernelOrdinaryRowError
import Theorems.Thm_Erdos390_Full_RegularMeshPrimeCutoffs_Mesh_exists_global_cutoff_eventually_canonical_diagonalError


section
universe u_1 u_2 u_3
theorem Erdos390.Full.ContinuumCellGraph.ArithmeticGaugeOrdinary.IntervalMesh.ordinary_split_arithmetic_projected_raw_bound : Erdos390.AnalyticCompactGoal001.{u_1, u_2, u_3} := @Erdos390.Full.ContinuumCellGraph.ArithmeticGaugeOrdinary.IntervalMesh.ordinary_split_arithmetic_projected_raw_bound_compact
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





end Mesh



end

end Erdos390.Full.RegularRelativeMesh

end

/- Source module: Erdos390.Full.PrimeSums -/
section


/-!
# Prime sums on the actual moving band

This file derives the finite prime-sum estimates needed in Lemma 7.5 from
Mathlib's Chebyshev bound.  No prime-sum estimate is introduced as a contract.
-/

open scoped BigOperators Nat.Prime
open Filter Topology

namespace Erdos390.Full.PrimeSums

open ArithmeticModel Scale



















private theorem primeBand_subset_primesUpTo (n W : ℕ) :
    primeBand n W ⊆ primesUpTo (yNat n) := by
  intro p hp
  have h := mem_primeBand.mp hp
  simp [primesUpTo, h.1, h.2.2]





















/-- A global Chebyshev bound for the logarithmically weighted reciprocal
prime sum.  The deliberately simple constant is uniform in the endpoint. -/
theorem fullLogReciprocalSum_le (Y : ℕ) (hY : 2 ≤ Y) :
    fullLogReciprocalSum Y ≤ Real.log 4 * (1 + Real.log (Y : ℝ)) := by
  rw [fullLogReciprocalSum_eq Y hY]
  have hYR : (2 : ℝ) ≤ (Y : ℝ) := by exact_mod_cast hY
  have hY0 : (0 : ℝ) < (Y : ℝ) := by linarith
  have hlog4 : (0 : ℝ) ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have htheta : Chebyshev.theta (Y : ℝ) / (Y : ℝ) ≤ Real.log 4 := by
    calc
      Chebyshev.theta (Y : ℝ) / (Y : ℝ) ≤
          (Real.log 4 * (Y : ℝ)) / (Y : ℝ) := by
        gcongr
        exact Chebyshev.theta_le_log4_mul_x (by positivity)
      _ = Real.log 4 := by field_simp
  have hint :
      (∫ t in (2 : ℝ)..Y, Chebyshev.theta t / t ^ 2) ≤
        Real.log 4 * Real.log (Y : ℝ) := by
    calc
      (∫ t in (2 : ℝ)..Y, Chebyshev.theta t / t ^ 2) ≤
          ∫ t in (2 : ℝ)..Y, Real.log 4 * (1 / t) := by
        refine intervalIntegral.integral_mono_on hYR
          (intervalIntegrable_theta_div_sq hYR) ?_ ?_
        · apply ContinuousOn.intervalIntegrable
          intro t ht
          rw [Set.uIcc_of_le hYR] at ht
          have ht0 : t ≠ 0 := by linarith [ht.1]
          exact ContinuousAt.continuousWithinAt
            (continuousAt_const.mul (continuousAt_const.div continuousAt_id ht0))
        · intro t ht
          calc
            Chebyshev.theta t / t ^ 2 ≤ (Real.log 4 * t) / t ^ 2 := by
              gcongr
              exact Chebyshev.theta_le_log4_mul_x (by linarith [ht.1])
            _ = Real.log 4 * (1 / t) := by
              have ht0 : t ≠ 0 := by linarith [ht.1]
              field_simp
      _ = Real.log 4 * Real.log ((Y : ℝ) / 2) := by
        rw [intervalIntegral.integral_const_mul,
          integral_one_div_of_pos (by norm_num) hY0]
      _ ≤ Real.log 4 * Real.log (Y : ℝ) := by
        apply mul_le_mul_of_nonneg_left _ hlog4
        apply Real.log_le_log (div_pos hY0 (by norm_num))
        linarith
  nlinarith

theorem bandLogReciprocalSum_le_full (n W : ℕ) :
    bandLogReciprocalSum n W ≤ fullLogReciprocalSum (yNat n) := by
  apply Finset.sum_le_sum_of_subset_of_nonneg (primeBand_subset_primesUpTo n W)
  intro p hp hnot
  have hp' : p ≤ yNat n ∧ p.Prime := by
    simpa [primesUpTo] using hp
  exact div_nonneg (Real.log_nonneg (by exact_mod_cast hp'.2.one_le)) (by positivity)





private theorem bandTReciprocalSum_eq (n W : ℕ) :
    bandTReciprocalSum n W =
      bandLogReciprocalSum n W / Real.log (y n) := by
  rw [bandTReciprocalSum, bandLogReciprocalSum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro p hp
  simp only [tPrime]
  ring

/-- The `t_p/p` mass of the moving prime band is uniformly bounded.  This is
the first-moment estimate used in the weighted covariance-row contraction. -/
theorem eventually_bandTReciprocalSum_le (W : ℕ) :
    ∀ᶠ n in atTop, bandTReciprocalSum n W ≤ 2 * Real.log 4 := by
  have hyTop : Tendsto (fun n : ℕ => y n) atTop atTop := by
    simpa [y] using
      ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 2 / 9)).comp
        tendsto_natCast_atTop_atTop)
  have hLTop : Tendsto L atTop atTop := by
    simpa [L] using Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_gt_atTop 0,
    hyTop.eventually (eventually_ge_atTop (2 : ℝ)),
    hLTop.eventually (eventually_ge_atTop (9 / 2 : ℝ))] with n hn hyn hLn
  have hyNat : 2 ≤ yNat n := by
    exact Nat.le_floor hyn
  have hlogy : 1 ≤ Real.log (y n) := by
    rw [log_y hn]
    nlinarith
  have hlogy0 : 0 < Real.log (y n) := lt_of_lt_of_le (by norm_num) hlogy
  have hyNatPos : (0 : ℝ) < (yNat n : ℝ) := by positivity
  have hyFloor : (yNat n : ℝ) ≤ y n :=
    Nat.floor_le (le_of_lt (y_pos hn))
  have hlogFloor : Real.log (yNat n : ℝ) ≤ Real.log (y n) :=
    Real.log_le_log hyNatPos hyFloor
  have hnum :
      Real.log 4 * (1 + Real.log (yNat n : ℝ)) ≤
        Real.log 4 * (2 * Real.log (y n)) := by
    apply mul_le_mul_of_nonneg_left _ (Real.log_nonneg (by norm_num))
    nlinarith
  calc
    bandTReciprocalSum n W =
        bandLogReciprocalSum n W / Real.log (y n) := bandTReciprocalSum_eq n W
    _ ≤ fullLogReciprocalSum (yNat n) / Real.log (y n) := by
      exact div_le_div_of_nonneg_right (bandLogReciprocalSum_le_full n W)
        (le_of_lt hlogy0)
    _ ≤ (Real.log 4 * (1 + Real.log (yNat n : ℝ))) /
          Real.log (y n) := by
      exact div_le_div_of_nonneg_right (fullLogReciprocalSum_le (yNat n) hyNat)
        (le_of_lt hlogy0)
    _ ≤ (Real.log 4 * (2 * Real.log (y n))) / Real.log (y n) := by
      exact div_le_div_of_nonneg_right hnum (le_of_lt hlogy0)
    _ = 2 * Real.log 4 := by field_simp

end Erdos390.Full.PrimeSums

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













































































lemma covarianceKernel_comm (s t : ℝ) :
    covarianceKernel s t = covarianceKernel t s := by
  unfold covarianceKernel
  rw [add_comm]
  ring

/-- The Dickman averaging identity after translating the unit interval.
This is the analytic content of the total-mass constraint. -/
lemma integral_rho_U_sub_shift (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
    (∫ t in (0 : ℝ)..1, rho (U - s - t)) = (U - s) * rho (U - s) := by
  have hx1 : 1 ≤ U - s := by
    norm_num [U] at hs ⊢
    linarith [hs.2]
  have hx5 : U - s ≤ 5 := by
    norm_num [U] at hs ⊢
    linarith [hs.1]
  have havg := rho_average_eq (x := U - s) hx1 hx5
  have hcomp := intervalIntegral.integral_comp_sub_left
    (a := (0 : ℝ)) (b := 1) rho (U - s)
  rw [show U - s - 1 = (U - s) - 1 by ring] at havg
  rw [hcomp]
  simpa [sub_eq_add_neg, add_assoc] using havg.symm

/-- At zero shift the preceding formula gives the first Palm mass identity. -/
lemma integral_rho_U_sub :
    (∫ t in (0 : ℝ)..1, rho (U - t)) = U * rho U := by
  simpa using integral_rho_U_sub_shift 0 (by norm_num)

/-- The normalized one-point Dickman weight integrates to the conditioned
total `U`. -/
lemma integral_F : (∫ t in (0 : ℝ)..1, F t) = U := by
  unfold F
  have hconst :
      (∫ t in (0 : ℝ)..1, rho (U - t) / rho U) =
        (∫ t in (0 : ℝ)..1, rho (U - t)) / rho U := by
    exact intervalIntegral.integral_div (f := fun t : ℝ => rho (U - t))
      (a := (0 : ℝ)) (b := 1) (rho U)
  rw [hconst, integral_rho_U_sub]
  field_simp [rho_U_ne_zero]

/-- The shifted one-point Palm weight has the exact residual-mass moment. -/
lemma integral_F_shift (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
    (∫ t in (0 : ℝ)..1, F (s + t)) = (U - s) * F s := by
  unfold F
  simp_rw [show ∀ t : ℝ, U - (s + t) = U - s - t by intro t; ring]
  have hconst :
      (∫ t in (0 : ℝ)..1, rho (U - s - t) / rho U) =
        (∫ t in (0 : ℝ)..1, rho (U - s - t)) / rho U := by
    exact intervalIntegral.integral_div
      (f := fun t : ℝ => rho (U - s - t))
      (a := (0 : ℝ)) (b := 1) (rho U)
  rw [hconst, integral_rho_U_sub_shift s hs]
  ring

/-- Integrating one variable of the covariance kernel yields exactly the
negative diagonal term required by the deterministic total constraint. -/
lemma integral_covarianceKernel (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
    (∫ t in (0 : ℝ)..1, covarianceKernel s t) = -s * F s := by
  have hFint : IntervalIntegrable F volume 0 1 := by
    have hcont : Continuous F := by
      unfold F
      exact (continuous_rho.comp
        (continuous_const.sub continuous_id)).div_const (rho U)
    exact hcont.intervalIntegrable 0 1
  have hshift : IntervalIntegrable (fun t : ℝ => F (s + t)) volume 0 1 := by
    have hcont : Continuous (fun t : ℝ => F (s + t)) := by
      have hF : Continuous F := by
        unfold F
        exact (continuous_rho.comp
          (continuous_const.sub continuous_id)).div_const (rho U)
      exact hF.comp (continuous_const.add continuous_id)
    exact hcont.intervalIntegrable 0 1
  change (∫ t in (0 : ℝ)..1, F (s + t) - F s * F t) = -s * F s
  rw [intervalIntegral.integral_sub hshift (hFint.const_mul (F s))]
  rw [integral_F_shift s hs, intervalIntegral.integral_const_mul, integral_F]
  ring







/-! ## Density-weighted Palm moments and covariance -/



lemma continuous_covarianceKernel :
    Continuous (Function.uncurry covarianceKernel) := by
  unfold covarianceKernel Function.uncurry
  exact (continuous_F.comp (continuous_fst.add continuous_snd)).sub
    ((continuous_F.comp continuous_fst).mul (continuous_F.comp continuous_snd))

/-! ## The removable axis singularity and a continuous kernel representative -/



















lemma covarianceKernelQuotient_eq_div {s t : ℝ}
    (hs : s ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1)
    (ht0 : t ≠ 0) :
    covarianceKernelQuotient s t = covarianceKernel s t / t := by
  apply (eq_div_iff ht0).2
  rw [mul_comm]
  exact mul_covarianceKernelQuotient_eq_kernel hs ht





























/-! ## The measurable Cauchy endpoint of the kernel argument -/





/-! The Palm argument produces additivity first on the positive triangle.
The following deterministic lemma records that no global Cauchy equation is
needed: continuity on the closed unit interval and local additivity already
force one common slope. -/







end Erdos390.Full.ConditionedPoissonLimit

end

/- Source module: Erdos390.Full.PoissonDickmanKernelBounds -/
section


/-!
# Uniform bounds for the removable Poisson--Dickman kernel

The moving-low-cell transfer needs a bound which remains valid as either
prime coordinate approaches zero.  The continuous quotient constructed in
`ConditionedPoissonLimit` gives such a bound on the compact unit square.  This
file exports the compactness consequence and converts it back to literal
bounds for the covariance kernel.  No conditioned-law or Palm identity is
used here.
-/

open Set

noncomputable section

namespace Erdos390.Full.PoissonDickmanKernelBounds

open ConditionedPoissonLimit

/-- The removable quotient `K(s,t)/t` is uniformly bounded on the closed unit
square. -/
theorem exists_covarianceKernelQuotient_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
      |covarianceKernelQuotient s t| ≤ C := by
  let S : Set (ℝ × ℝ) := Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1
  have hScompact : IsCompact S := isCompact_Icc.prod isCompact_Icc
  obtain ⟨C, hC⟩ := hScompact.exists_bound_of_continuousOn
    continuous_uncurry_covarianceKernelQuotient.continuousOn
  have hzeroMem : ((0 : ℝ), (0 : ℝ)) ∈ S := by
    exact ⟨by norm_num, by norm_num⟩
  have hCnonneg : 0 ≤ C :=
    (norm_nonneg (covarianceKernelQuotient 0 0)).trans
      (hC (0, 0) hzeroMem)
  refine ⟨C, hCnonneg, ?_⟩
  intro s hs t ht
  simpa only [Real.norm_eq_abs] using hC (s, t) ⟨hs, ht⟩





end Erdos390.Full.PoissonDickmanKernelBounds

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

/- Source module: Erdos390.Full.PoissonDickmanWeightedInverse -/
section


/-!
# A deterministic weighted `L∞` quotient inverse

After writing the Poisson--Dickman test as `f(t)=t q(t)`, the covariance
operator is a nonlocal graph Laplacian with continuous edge kernel
`-K(s,t)/s`.  Strict Dickman log-concavity makes this edge kernel uniformly
positive when the second endpoint ranges in one fixed interior interval,
including at the removable axis `s=0`.  A maximum/minimum argument then
controls the oscillation of `q` directly.  This gives the weighted quotient
inverse without assuming Fredholm theory or an inverse theorem.
-/

open Set

noncomputable section

set_option maxHeartbeats 800000

namespace Erdos390.Full.PoissonDickmanWeightedInverse

open MeasureTheory
open DickmanBasic ConditionedPoissonLimit PoissonDickmanDirichlet









/-! The strict four-point inequality with one endpoint allowed to equal one.
The proof repeats the already audited shifted-slope integral argument, but
uses only positivity (not strict upper bounds) for the endpoints. -/













/-! ## The weighted operator as a graph Laplacian -/









/-- The removable row-sum identity, including the axis by continuity. -/
theorem weightedKernel_rowSum (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
    F s + (∫ t in (0 : ℝ)..1, covarianceKernelQuotient t s) = 0 := by
  let R : ℝ → ℝ := fun u =>
    F u + ∫ t in (0 : ℝ)..1, covarianceKernelQuotient t u
  have hRcont : Continuous R := by
    dsimp only [R]
    apply continuous_F.add
    apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (a₀ := (0 : ℝ)) (b₀ := 1)
    exact continuous_uncurry_covarianceKernelQuotient.comp
      (continuous_snd.prodMk continuous_fst)
  have hzero : Ioc (0 : ℝ) 1 ⊆ R ⁻¹' ({0} : Set ℝ) := by
    intro u hu
    have hucc : u ∈ Icc (0 : ℝ) 1 := ⟨hu.1.le, hu.2⟩
    have hu0 : u ≠ 0 := ne_of_gt hu.1
    change R u = 0
    dsimp only [R]
    have hInt :
        (∫ t in (0 : ℝ)..1, covarianceKernelQuotient t u) =
          (∫ t in (0 : ℝ)..1, covarianceKernel u t) / u := by
      calc
        (∫ t in (0 : ℝ)..1, covarianceKernelQuotient t u) =
            ∫ t in (0 : ℝ)..1, covarianceKernel u t / u := by
          apply intervalIntegral.integral_congr
          intro t ht
          have htcc : t ∈ Icc (0 : ℝ) 1 := by
            simpa [uIcc_of_le (show (0 : ℝ) ≤ 1 by norm_num)] using ht
          change covarianceKernelQuotient t u = covarianceKernel u t / u
          rw [covarianceKernelQuotient_eq_div htcc hucc hu0,
            covarianceKernel_comm]
        _ = (∫ t in (0 : ℝ)..1, covarianceKernel u t) / u := by
          rw [intervalIntegral.integral_div]
    rw [hInt, integral_covarianceKernel u hucc]
    field_simp [hu0]
    ring
  have hclosed : IsClosed (R ⁻¹' ({0} : Set ℝ)) :=
    isClosed_singleton.preimage hRcont
  have hclosure := closure_minimal hzero hclosed
  rw [closure_Ioc (by norm_num : (0 : ℝ) ≠ 1)] at hclosure
  exact hclosure hs









end Erdos390.Full.PoissonDickmanWeightedInverse

end

/- Source module: Erdos390.Full.ContinuumCellGraph -/
section


/-!
# Continuum cell compression as a finite graph

This is the mesh-uniform bridge from the weighted Poisson--Dickman operator
to a finite matrix.  Every row is the ordinary-cell average of the graph
kernel `-K(t,s)/s`.  A fixed collection of cells lying in one interior
interval supplies a common anchor measure.  The positive edge constant is
derived from the Dickman kernel theorem; it is not mesh data.
-/

open scoped BigOperators
open Set

noncomputable section

namespace Erdos390.Full.ContinuumCellGraph

open MeasureTheory
open ConditionedPoissonLimit
open PoissonDickmanWeightedInverse

variable {Band : Type*} [Fintype Band] [DecidableEq Band]



namespace IntervalMesh

variable {epsilon : ℝ} (M : IntervalMesh epsilon Band)



omit [DecidableEq Band] in
theorem length_pos (i : Band) : 0 < M.length i :=
  sub_pos.mpr (M.lower_lt_upper i)







omit [DecidableEq Band] in
theorem cell_mem_unit {i : Band} {s : ℝ}
    (hs : s ∈ Icc (M.lower i) (M.upper i)) :
    s ∈ Icc (0 : ℝ) 1 :=
  ⟨(M.lower_pos i).le.trans hs.1, hs.2.trans (M.upper_le_one i)⟩













/-! ## The exact edge matrix of the sharp continuum kernel block -/



omit [DecidableEq Band] in
theorem harmonicMass_pos (i : Band) : 0 < M.harmonicMass i := by
  unfold harmonicMass
  rw [integral_one_div_of_pos
    (M.lower_pos i) ((M.lower_pos i).trans (M.lower_lt_upper i))]
  apply Real.log_pos
  exact (one_lt_div (M.lower_pos i)).2 (M.lower_lt_upper i)



omit [DecidableEq Band] in
theorem center_pos (i : Band) : 0 < M.center i :=
  div_pos (M.length_pos i) (M.harmonicMass_pos i)















end IntervalMesh

end Erdos390.Full.ContinuumCellGraph

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











/-- Exact first-moment identity for the arithmetic centers. -/
theorem sum_mass_mul_center_eq_bandTReciprocalSum :
    (∑ j : Band, P.mass j * P.center j) =
      bandTReciprocalSum n W := by
  have hcenter (j : Band) :
      P.mass j * P.center j =
        ∑ p ∈ P.data.fiber j,
          (1 / (p.1 : ℝ)) * tPrime n p.1 := by
    change P.data.mass j *
        ((∑ p ∈ P.data.fiber j,
          (1 / (p.1 : ℝ)) * tPrime n p.1) / P.data.mass j) = _
    field_simp [ne_of_gt (P.data.mass_pos j)]
  calc
    (∑ j : Band, P.mass j * P.center j) =
        ∑ j : Band, ∑ p ∈ P.data.fiber j,
          (1 / (p.1 : ℝ)) * tPrime n p.1 := by
            apply Finset.sum_congr rfl
            intro j hj
            exact hcenter j
    _ = ∑ p : BandPrime n W,
          (1 / (p.1 : ℝ)) * tPrime n p.1 := by
            rw [← Finset.sum_fiberwise Finset.univ P.band
              (fun p : BandPrime n W ↦
                (1 / (p.1 : ℝ)) * tPrime n p.1)]
            apply Finset.sum_congr rfl
            intro j hj
            rfl
    _ = bandTReciprocalSum n W := by
          unfold bandTReciprocalSum
          have hattach := Finset.sum_attach (primeBand n W)
            (fun p ↦ tPrime n p / (p : ℝ))
          rw [← hattach]
          apply Finset.sum_congr rfl
          intro p hp
          ring













end

end Erdos390.Full.ArithmeticBandGeometry.Partition

end

/- Source module: Erdos390.Full.ContinuumRowResidualBound -/
section


/-!
# An explicit moving-low bound for the continuum row residual

Harmonic cell centers need not be close pointwise to the coordinate in the
moving low cell.  The correct cancellation is instead
`center * ∫ dt/t = ∫ dt`.  This file exploits that exact identity before
taking absolute values.  Consequently the residual is controlled by the
ordinary modulus of continuity of `F` and of the removable kernel on the
closed physical square, together with the omitted initial tail.
-/

open scoped BigOperators
open Set

noncomputable section

namespace Erdos390.Full
namespace ContinuumCellGraph
namespace IntervalMesh

open MeasureTheory
open ConditionedPoissonLimit
open DickmanBasic
open PoissonDickmanWeightedInverse

variable {Band : Type*} [Fintype Band]
variable {epsilon : ℝ} (M : IntervalMesh epsilon Band)

theorem center_mul_harmonicMass (i : Band) :
    M.center i * M.harmonicMass i = M.length i := by
  unfold center
  field_simp [ne_of_gt (M.harmonicMass_pos i)]





private theorem continuous_innerKernel (a b : ℝ) :
    Continuous (fun s : ℝ =>
      ∫ t in a..b, covarianceKernelQuotient t s) := by
  apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (a₀ := a) (b₀ := b)
  exact continuous_uncurry_covarianceKernelQuotient.comp
    (continuous_snd.prodMk continuous_fst)

private theorem continuous_innerKernelDiv (j : Band) :
    Continuous (fun s : ℝ =>
      ∫ t in M.lower j..M.upper j,
        covarianceKernelQuotient t s / t) := by
  let d : ℝ → ℝ := fun t => max t (M.lower j / 2)
  have hdcont : Continuous d :=
    continuous_id.max
      (continuous_const : Continuous fun _ : ℝ => M.lower j / 2)
  have hd0 (t : ℝ) : d t ≠ 0 := by
    have hdpos : 0 < d t := by
      dsimp only [d]
      exact (half_pos (M.lower_pos j)).trans_le (le_max_right _ _)
    exact ne_of_gt hdpos
  have hsurrogate : Continuous (fun s : ℝ =>
      ∫ t in M.lower j..M.upper j,
        covarianceKernelQuotient t s / d t) := by
    apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (a₀ := M.lower j) (b₀ := M.upper j)
    exact (continuous_uncurry_covarianceKernelQuotient.comp
      (continuous_snd.prodMk continuous_fst)).div
        (hdcont.comp continuous_snd) (fun z => hd0 z.2)
  have heq : (fun s : ℝ =>
      ∫ t in M.lower j..M.upper j,
        covarianceKernelQuotient t s / t) =
      (fun s : ℝ =>
        ∫ t in M.lower j..M.upper j,
          covarianceKernelQuotient t s / d t) := by
    funext s
    apply intervalIntegral.integral_congr
    intro t ht
    have htcc : t ∈ Icc (M.lower j) (M.upper j) := by
      simpa [uIcc_of_le (le_of_lt (M.lower_lt_upper j))] using ht
    have hhalf : M.lower j / 2 ≤ t := by
      linarith [M.lower_pos j, htcc.1]
    change covarianceKernelQuotient t s / t =
      covarianceKernelQuotient t s / d t
    rw [show d t = t by simp [d, max_eq_left hhalf] ]
  rw [heq]
  exact hsurrogate



theorem abs_inputCellResidual_le
    (i j : Band) {rhoKernel : ℝ}
    (hosc : ∀ s ∈ Icc (0 : ℝ) 1,
      ∀ t ∈ Icc (M.lower j) (M.upper j),
        |covarianceKernelQuotient t s -
          covarianceKernelQuotient (M.lower j) s| ≤ rhoKernel) :
    |M.inputCellResidual i j| ≤
      (2 * rhoKernel * M.length j) * M.length i := by
  unfold inputCellResidual
  have hpoint (s : ℝ) (hs : s ∈ Icc (M.lower i) (M.upper i)) :
      |M.center j *
          (∫ t in M.lower j..M.upper j,
            covarianceKernelQuotient t s / t) -
        ∫ t in M.lower j..M.upper j,
          covarianceKernelQuotient t s| ≤
        2 * rhoKernel * M.length j := by
    apply M.abs_center_mul_integral_div_sub_integral_le
      (fun t => covarianceKernelQuotient t s)
      (continuous_uncurry_covarianceKernelQuotient.comp
        (continuous_id.prodMk continuous_const)) j
    intro t ht
    exact hosc s (M.cell_mem_unit hs) t ht
  have hnorm := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := M.lower i) (b := M.upper i)
    (C := 2 * rhoKernel * M.length j)
    (f := fun s : ℝ =>
      M.center j *
          (∫ t in M.lower j..M.upper j,
            covarianceKernelQuotient t s / t) -
        ∫ t in M.lower j..M.upper j,
          covarianceKernelQuotient t s)
    (fun s hs => by
      have hscc : s ∈ Icc (M.lower i) (M.upper i) := by
        have hs' : s ∈ uIcc (M.lower i) (M.upper i) :=
          uIoc_subset_uIcc hs
        simpa only [uIcc_of_le (le_of_lt (M.lower_lt_upper i))] using hs'
      simpa only [Real.norm_eq_abs] using hpoint s hscc)
  simpa only [Real.norm_eq_abs, length,
    abs_of_pos (sub_pos.mpr (M.lower_lt_upper i))] using hnorm



theorem abs_kernelTailResidual_le
    (i : Band) {base C : ℝ}
    (hbase : 0 ≤ base) (hbaseOne : base ≤ 1)
    (hKernel : ∀ s ∈ Icc (0 : ℝ) 1,
      ∀ t ∈ Icc (0 : ℝ) 1,
        |covarianceKernelQuotient t s| ≤ C) :
    |M.kernelTailResidual base i| ≤
      (C * base) * M.length i := by
  have hinner (s : ℝ) (hs : s ∈ Icc (M.lower i) (M.upper i)) :
      |∫ t in (0 : ℝ)..base, covarianceKernelQuotient t s| ≤
        C * base := by
    have hnorm := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := (0 : ℝ)) (b := base) (C := C)
      (f := fun t : ℝ => covarianceKernelQuotient t s)
      (fun t ht => by
        have htcc : t ∈ Icc (0 : ℝ) base := by
          have ht' : t ∈ uIcc (0 : ℝ) base := uIoc_subset_uIcc ht
          simpa only [uIcc_of_le hbase] using ht'
        rw [Real.norm_eq_abs]
        exact hKernel s (M.cell_mem_unit hs) t
          ⟨htcc.1, htcc.2.trans hbaseOne⟩)
    simpa only [Real.norm_eq_abs, sub_zero, abs_of_nonneg hbase] using hnorm
  unfold kernelTailResidual
  have hnorm := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := M.lower i) (b := M.upper i) (C := C * base)
    (f := fun s : ℝ =>
      ∫ t in (0 : ℝ)..base, covarianceKernelQuotient t s)
    (fun s hs => by
      have hscc : s ∈ Icc (M.lower i) (M.upper i) := by
        have hs' : s ∈ uIcc (M.lower i) (M.upper i) :=
          uIoc_subset_uIcc hs
        simpa only [uIcc_of_le (le_of_lt (M.lower_lt_upper i))] using hs'
      simpa only [Real.norm_eq_abs] using hinner s hscc)
  simpa only [Real.norm_eq_abs, length,
    abs_of_pos (sub_pos.mpr (M.lower_lt_upper i))] using hnorm

theorem inputCellResidual_eq (i j : Band) :
    M.inputCellResidual i j =
      M.center j *
          (∫ s in M.lower i..M.upper i,
            ∫ t in M.lower j..M.upper j,
              covarianceKernelQuotient t s / t) -
        ∫ s in M.lower i..M.upper i,
          ∫ t in M.lower j..M.upper j,
            covarianceKernelQuotient t s := by
  unfold inputCellResidual
  have hleft : IntervalIntegrable (fun s : ℝ =>
      M.center j *
        (∫ t in M.lower j..M.upper j,
          covarianceKernelQuotient t s / t)) volume
      (M.lower i) (M.upper i) :=
    (continuous_const.mul (M.continuous_innerKernelDiv j)).intervalIntegrable _ _
  have hright : IntervalIntegrable (fun s : ℝ =>
      ∫ t in M.lower j..M.upper j,
        covarianceKernelQuotient t s) volume
      (M.lower i) (M.upper i) :=
    (continuous_innerKernel (M.lower j) (M.upper j)).intervalIntegrable _ _
  rw [intervalIntegral.integral_sub hleft hright,
    intervalIntegral.integral_const_mul]

theorem length_mul_normalizedDiagonalCell (i : Band) :
    M.length i * M.normalizedDiagonalCell i =
      M.center i *
        (∫ s in M.lower i..M.upper i, F s / s) := by
  unfold normalizedDiagonalCell
  rw [← M.center_mul_harmonicMass i]
  field_simp [ne_of_gt (M.harmonicMass_pos i)]

theorem length_mul_normalizedKernel_ratio (i j : Band) :
    M.length i *
        (M.normalizedKernelCell i j * (M.center j / M.center i)) =
      M.center j *
        (∫ s in M.lower i..M.upper i,
          ∫ t in M.lower j..M.upper j,
            covarianceKernelQuotient t s / t) := by
  unfold normalizedKernelCell
  rw [← M.center_mul_harmonicMass i]
  field_simp [ne_of_gt (M.harmonicMass_pos i),
    ne_of_gt (M.center_pos i)]







/-- Joint modulus of continuity in exactly the orientation used by the
cell residual.  Compactness is invoked on the closed physical interval and
square, so the constants do not depend on the moving low endpoint. -/
theorem exists_uniform_cell_oscillation_modulus
    {rhoF rhoKernel : ℝ} (hrhoF : 0 < rhoF)
    (hrhoKernel : 0 < rhoKernel) :
    ∃ eta : ℝ, 0 < eta ∧
      (∀ x ∈ Icc (0 : ℝ) 1, ∀ y ∈ Icc (0 : ℝ) 1,
        |x - y| < eta → |F x - F y| < rhoF) ∧
      (∀ s ∈ Icc (0 : ℝ) 1,
        ∀ t ∈ Icc (0 : ℝ) 1, ∀ u ∈ Icc (0 : ℝ) 1,
          |t - u| < eta →
            |covarianceKernelQuotient t s -
              covarianceKernelQuotient u s| < rhoKernel) := by
  have hFu : UniformContinuousOn F (Icc (0 : ℝ) 1) :=
    isCompact_Icc.uniformContinuousOn_of_continuous continuous_F.continuousOn
  obtain ⟨etaF, hetaF, hFmod⟩ :=
    Metric.uniformContinuousOn_iff.mp hFu rhoF hrhoF
  let square : Set (ℝ × ℝ) := Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1
  have hKu : UniformContinuousOn
      (Function.uncurry covarianceKernelQuotient) square :=
    (isCompact_Icc.prod isCompact_Icc).uniformContinuousOn_of_continuous
      continuous_uncurry_covarianceKernelQuotient.continuousOn
  obtain ⟨etaK, hetaK, hKmod⟩ :=
    Metric.uniformContinuousOn_iff.mp hKu rhoKernel hrhoKernel
  refine ⟨min etaF etaK, lt_min hetaF hetaK, ?_, ?_⟩
  · intro x hx y hy hxy
    rw [← Real.dist_eq] at hxy ⊢
    exact hFmod x hx y hy (hxy.trans_le (min_le_left _ _))
  · intro s hs t ht u hu htu
    have hdist : dist (t, s) (u, s) < etaK := by
      simpa only [Prod.dist_eq, dist_self, Real.dist_eq,
        max_eq_left (abs_nonneg (t - u))] using
        htu.trans_le (min_le_right etaF etaK)
    have h := hKmod (t, s) ⟨ht, hs⟩ (u, s) ⟨hu, hs⟩ hdist
    simpa only [Function.uncurry_apply_pair, Real.dist_eq] using h



end IntervalMesh
end ContinuumCellGraph
end Erdos390.Full

end

/- Source module: Erdos390.Full.ContinuumTwoTailResidualBound -/
section


/-!
# Continuum row residual with both endpoint tails

For the literal arithmetic endpoint mesh the last endpoint is
`log(floor y)/log y`, not exactly `1`.  This file keeps both omitted tails
explicit.  It closes the top-endpoint gap without changing the continuum
operator or pretending that `floor y = y`.
-/

open scoped BigOperators
open Set

noncomputable section

namespace Erdos390.Full
namespace ContinuumCellGraph
namespace IntervalMesh

open MeasureTheory
open ConditionedPoissonLimit
open DickmanBasic
open PoissonDickmanWeightedInverse

variable {Band : Type*} [Fintype Band]
variable {epsilon : ℝ} (M : IntervalMesh epsilon Band)





theorem abs_kernelUpperTailResidual_le
    (i : Band) {top C : ℝ}
    (htop : 0 ≤ top) (htopOne : top ≤ 1)
    (hKernel : ∀ s ∈ Icc (0 : ℝ) 1,
      ∀ t ∈ Icc (0 : ℝ) 1,
        |covarianceKernelQuotient t s| ≤ C) :
    |M.kernelUpperTailResidual top i| ≤
      (C * (1 - top)) * M.length i := by
  have hinner (s : ℝ) (hs : s ∈ Icc (M.lower i) (M.upper i)) :
      |∫ t in top..1, covarianceKernelQuotient t s| ≤
        C * (1 - top) := by
    have hnorm := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := top) (b := (1 : ℝ)) (C := C)
      (f := fun t : ℝ => covarianceKernelQuotient t s)
      (fun t ht => by
        have htcc : t ∈ Icc top (1 : ℝ) := by
          have ht' : t ∈ uIcc top (1 : ℝ) := uIoc_subset_uIcc ht
          simpa only [uIcc_of_le htopOne] using ht'
        rw [Real.norm_eq_abs]
        exact hKernel s (M.cell_mem_unit hs) t
          ⟨htop.trans htcc.1, htcc.2⟩)
    simpa only [Real.norm_eq_abs,
      abs_of_nonneg (sub_nonneg.mpr htopOne)] using hnorm
  unfold kernelUpperTailResidual
  have hnorm := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := M.lower i) (b := M.upper i) (C := C * (1 - top))
    (f := fun s : ℝ =>
      ∫ t in top..1, covarianceKernelQuotient t s)
    (fun s hs => by
      have hscc : s ∈ Icc (M.lower i) (M.upper i) := by
        have hs' : s ∈ uIcc (M.lower i) (M.upper i) :=
          uIoc_subset_uIcc hs
        simpa only [uIcc_of_le (le_of_lt (M.lower_lt_upper i))] using hs'
      simpa only [Real.norm_eq_abs] using hinner s hscc)
  simpa only [Real.norm_eq_abs, length,
    abs_of_pos (sub_pos.mpr (M.lower_lt_upper i))] using hnorm

private theorem continuous_middleKernel (a b : ℝ) :
    Continuous (fun s : ℝ =>
      ∫ t in a..b, covarianceKernelQuotient t s) := by
  apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (a₀ := a) (b₀ := b)
  exact continuous_uncurry_covarianceKernelQuotient.comp
    (continuous_snd.prodMk continuous_fst)

theorem diagonal_add_middleKernel_eq_neg_tails
    (P : M.TwoTailPartitionCertificate) (i : Band) :
    (∫ s in M.lower i..M.upper i, F s) +
        (∫ s in M.lower i..M.upper i,
          ∫ t in P.base..P.upperEnd, covarianceKernelQuotient t s) =
      -M.kernelTailResidual P.base i -
        M.kernelUpperTailResidual P.upperEnd i := by
  have hpoint (s : ℝ) (hs : s ∈ Icc (M.lower i) (M.upper i)) :
      F s + (∫ t in P.base..P.upperEnd, covarianceKernelQuotient t s) =
        -(∫ t in (0 : ℝ)..P.base, covarianceKernelQuotient t s) -
          (∫ t in P.upperEnd..1, covarianceKernelQuotient t s) := by
    have hrow := weightedKernel_rowSum s (M.cell_mem_unit hs)
    let f : ℝ → ℝ := fun t => covarianceKernelQuotient t s
    have hleft : IntervalIntegrable f volume 0 P.base :=
      (continuous_uncurry_covarianceKernelQuotient.comp
        (continuous_id.prodMk continuous_const)).intervalIntegrable _ _
    have hmid : IntervalIntegrable f volume P.base P.upperEnd :=
      (continuous_uncurry_covarianceKernelQuotient.comp
        (continuous_id.prodMk continuous_const)).intervalIntegrable _ _
    have hzeroTop : IntervalIntegrable f volume 0 P.upperEnd :=
      (continuous_uncurry_covarianceKernelQuotient.comp
        (continuous_id.prodMk continuous_const)).intervalIntegrable _ _
    have hright : IntervalIntegrable f volume P.upperEnd 1 :=
      (continuous_uncurry_covarianceKernelQuotient.comp
        (continuous_id.prodMk continuous_const)).intervalIntegrable _ _
    have haddLeft := intervalIntegral.integral_add_adjacent_intervals hleft hmid
    have haddRight := intervalIntegral.integral_add_adjacent_intervals
      hzeroTop hright
    dsimp only [f] at haddLeft haddRight
    linarith
  have hFint : IntervalIntegrable F volume (M.lower i) (M.upper i) :=
    continuous_F.intervalIntegrable _ _
  have hmidInt : IntervalIntegrable (fun s : ℝ =>
      ∫ t in P.base..P.upperEnd, covarianceKernelQuotient t s) volume
      (M.lower i) (M.upper i) :=
    (continuous_middleKernel P.base P.upperEnd).intervalIntegrable _ _
  have hlowInt : IntervalIntegrable (fun s : ℝ =>
      ∫ t in (0 : ℝ)..P.base, covarianceKernelQuotient t s) volume
      (M.lower i) (M.upper i) :=
    (continuous_middleKernel 0 P.base).intervalIntegrable _ _
  have hnegLowInt : IntervalIntegrable (fun s : ℝ =>
      -(∫ t in (0 : ℝ)..P.base, covarianceKernelQuotient t s)) volume
      (M.lower i) (M.upper i) := hlowInt.neg
  have hhighInt : IntervalIntegrable (fun s : ℝ =>
      ∫ t in P.upperEnd..1, covarianceKernelQuotient t s) volume
      (M.lower i) (M.upper i) :=
    (continuous_middleKernel P.upperEnd 1).intervalIntegrable _ _
  unfold kernelTailResidual kernelUpperTailResidual
  rw [← intervalIntegral.integral_add hFint hmidInt,
    ← intervalIntegral.integral_neg,
    ← intervalIntegral.integral_sub hnegLowInt hhighInt]
  apply intervalIntegral.integral_congr
  intro s hs
  have hscc : s ∈ Icc (M.lower i) (M.upper i) := by
    simpa [uIcc_of_le (le_of_lt (M.lower_lt_upper i))] using hs
  exact hpoint s hscc

/-- Exact two-tail decomposition of the continuum null-vector defect. -/
theorem length_mul_rowResidual_eq_twoTails
    (P : M.TwoTailPartitionCertificate) (i : Band) :
    M.length i * M.rowResidual i =
      (M.center i *
          (∫ s in M.lower i..M.upper i, F s / s) -
        ∫ s in M.lower i..M.upper i, F s) +
      (∑ j, M.inputCellResidual i j) -
        M.kernelTailResidual P.base i -
        M.kernelUpperTailResidual P.upperEnd i := by
  have hscaled : M.length i * M.rowResidual i =
      M.center i *
          (∫ s in M.lower i..M.upper i, F s / s) +
        ∑ j, M.center j *
          (∫ s in M.lower i..M.upper i,
            ∫ t in M.lower j..M.upper j,
              covarianceKernelQuotient t s / t) := by
    unfold rowResidual
    rw [mul_add, Finset.mul_sum, M.length_mul_normalizedDiagonalCell]
    apply congrArg
      (fun x : ℝ =>
        M.center i * (∫ s in M.lower i..M.upper i, F s / s) + x)
    apply Finset.sum_congr rfl
    intro j hj
    exact M.length_mul_normalizedKernel_ratio i j
  have hinput : (∑ j, M.inputCellResidual i j) =
      (∑ j, M.center j *
        (∫ s in M.lower i..M.upper i,
          ∫ t in M.lower j..M.upper j,
            covarianceKernelQuotient t s / t)) -
      (∫ s in M.lower i..M.upper i,
        ∫ t in P.base..P.upperEnd, covarianceKernelQuotient t s) := by
    simp_rw [M.inputCellResidual_eq i]
    rw [Finset.sum_sub_distrib, P.kernelDoubleIntegral_split]
  have hrow := M.diagonal_add_middleKernel_eq_neg_tails P i
  rw [hscaled, hinput]
  linarith

/-- Quantitative two-tail residual bound. -/
theorem abs_rowResidual_le_twoTails
    (P : M.TwoTailPartitionCertificate)
    {rhoF rhoKernel C : ℝ}
    (hFosc : ∀ j, ∀ s ∈ Icc (M.lower j) (M.upper j),
      |F s - F (M.lower j)| ≤ rhoF)
    (hKernelOsc : ∀ j, ∀ s ∈ Icc (0 : ℝ) 1,
      ∀ t ∈ Icc (M.lower j) (M.upper j),
        |covarianceKernelQuotient t s -
          covarianceKernelQuotient (M.lower j) s| ≤ rhoKernel)
    (hKernel : ∀ s ∈ Icc (0 : ℝ) 1,
      ∀ t ∈ Icc (0 : ℝ) 1,
        |covarianceKernelQuotient t s| ≤ C)
    (i : Band) :
    |M.rowResidual i| ≤
      2 * rhoF + 2 * rhoKernel * (P.upperEnd - P.base) +
        C * P.base + C * (1 - P.upperEnd) := by
  have hdiag := M.abs_center_mul_integral_div_sub_integral_le
    F continuous_F i (hFosc i)
  have hinputEach (j : Band) :=
    M.abs_inputCellResidual_le i j (hKernelOsc j)
  have hinput : |∑ j, M.inputCellResidual i j| ≤
      (2 * rhoKernel * (P.upperEnd - P.base)) * M.length i := by
    calc
      |∑ j, M.inputCellResidual i j| ≤
          ∑ j, |M.inputCellResidual i j| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j, (2 * rhoKernel * M.length j) * M.length i := by
        apply Finset.sum_le_sum
        intro j hj
        exact hinputEach j
      _ = (2 * rhoKernel * (∑ j, M.length j)) * M.length i := by
        rw [Finset.mul_sum, Finset.sum_mul]
      _ = (2 * rhoKernel * (P.upperEnd - P.base)) * M.length i := by
        rw [P.totalLength]
  have hlow := M.abs_kernelTailResidual_le i P.base_nonneg
    (P.base_le_upperEnd.trans P.upperEnd_le_one) hKernel
  have hhigh := M.abs_kernelUpperTailResidual_le i
    (P.base_nonneg.trans P.base_le_upperEnd) P.upperEnd_le_one hKernel
  have hscaled : |M.length i * M.rowResidual i| ≤
      (2 * rhoF + 2 * rhoKernel * (P.upperEnd - P.base) +
        C * P.base + C * (1 - P.upperEnd)) * M.length i := by
    rw [M.length_mul_rowResidual_eq_twoTails P i]
    calc
      |_ + (∑ j, M.inputCellResidual i j) -
          M.kernelTailResidual P.base i -
          M.kernelUpperTailResidual P.upperEnd i| ≤
        |M.center i * (∫ s in M.lower i..M.upper i, F s / s) -
            ∫ s in M.lower i..M.upper i, F s| +
          |∑ j, M.inputCellResidual i j| +
          |M.kernelTailResidual P.base i| +
          |M.kernelUpperTailResidual P.upperEnd i| := by
        calc
          |_ - M.kernelUpperTailResidual P.upperEnd i| ≤
              |_ - M.kernelTailResidual P.base i| +
                |M.kernelUpperTailResidual P.upperEnd i| := abs_sub _ _
          _ ≤ (|_ + (∑ j, M.inputCellResidual i j)| +
                |M.kernelTailResidual P.base i|) +
                |M.kernelUpperTailResidual P.upperEnd i| := by
            gcongr
            exact abs_sub _ _
          _ ≤ _ := by
            gcongr
            exact abs_add_le _ _
      _ ≤ (2 * rhoF * M.length i) +
          ((2 * rhoKernel * (P.upperEnd - P.base)) * M.length i) +
          ((C * P.base) * M.length i) +
          ((C * (1 - P.upperEnd)) * M.length i) := by
        gcongr
      _ = _ := by ring
  have hlength : 0 < M.length i := M.length_pos i
  apply le_of_mul_le_mul_left _ hlength
  calc
    M.length i * |M.rowResidual i| =
        |M.length i * M.rowResidual i| := by
      rw [abs_mul, abs_of_pos hlength]
    _ ≤ _ := hscaled
    _ = M.length i *
        (2 * rhoF + 2 * rhoKernel * (P.upperEnd - P.base) +
          C * P.base + C * (1 - P.upperEnd)) := by ring



end IntervalMesh
end ContinuumCellGraph
end Erdos390.Full

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

/-- If the ideal low cell and every ideal positive cell have length
strictly below `rho`, then all literal floored cells eventually do too,
simultaneously. -/
theorem eventually_all_actualCoordinateLengths_lt
    (hdelta : 0 < delta) {rho : ℝ}
    (hLow : delta < rho)
    (hPositive : ∀ k : Fin M.cellCount, M.width k < rho)
    (W : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ j : Fin (M.cellCount + 1),
      actualCutoffCoordinate M n W (j.1 + 1) -
        actualCutoffCoordinate M n W j.1 < rho := by
  have hLowEvent : ∀ᶠ n : ℕ in atTop,
      actualCutoffCoordinate M n W 1 - actualCutoffCoordinate M n W 0 < rho :=
    (tendsto_low_actualCoordinateLength M hdelta W).eventually
      (eventually_lt_nhds hLow)
  have hPositiveEvent : ∀ᶠ n : ℕ in atTop,
      ∀ k : Fin M.cellCount,
        actualCutoffCoordinate M n W (k.1 + 2) -
          actualCutoffCoordinate M n W (k.1 + 1) < rho := by
    rw [Filter.eventually_all]
    intro k
    exact (tendsto_positive_actualCoordinateLength M hdelta W k).eventually
      (eventually_lt_nhds (hPositive k))
  filter_upwards [hLowEvent, hPositiveEvent] with n hnLow hnPositive
  intro j
  refine Fin.cases ?_ (fun k ↦ ?_) j
  · simpa using hnLow
  · simpa using hnPositive k

theorem tendsto_canonical_upperEnd_one (W : ℕ) :
    Tendsto (fun n : ℕ ↦
      actualCutoffCoordinate M n W (M.cellCount + 1))
      atTop (nhds 1) := by
  have hT := tendsto_floor_scalePoint_coordinate (t := (1 : ℝ)) (by norm_num)
  apply hT.congr'
  filter_upwards [eventually_gt_atTop 0] with n hn
  simp only [actualCutoffCoordinate, fullCutoff_last M hn, yNat, scalePoint,
    one_mul, Real.exp_log (Scale.y_pos hn)]

/-- Both literal endpoint omissions tend to zero. -/
theorem eventually_canonical_twoTails_lt
    (W : ℕ) {beta : ℝ} (hbeta : 0 < beta) :
    ∀ᶠ n : ℕ in atTop,
      actualCutoffCoordinate M n W 0 < beta ∧
        1 - actualCutoffCoordinate M n W (M.cellCount + 1) < beta := by
  have hBase : Tendsto (fun n : ℕ ↦ actualCutoffCoordinate M n W 0)
      atTop (nhds 0) := by
    have h := tendsto_fixed_cutoffCoordinate_zero W
    simpa only [actualCutoffCoordinate, fullCutoff_zero] using h
  have hTop := tendsto_canonical_upperEnd_one M W
  have hTopTail : Tendsto (fun n : ℕ ↦
      1 - actualCutoffCoordinate M n W (M.cellCount + 1))
      atTop (nhds 0) := by
    have hOne : Tendsto (fun _n : ℕ ↦ (1 : ℝ)) atTop (nhds 1) :=
      tendsto_const_nhds
    simpa only [sub_self] using hOne.sub hTop
  exact (hBase.eventually (eventually_lt_nhds hbeta)).and
    (hTopTail.eventually (eventually_lt_nhds hbeta))

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

/- Source module: Erdos390.Full.EndpointContinuumMeshIdentification -/
section


/-!
# Exact identification of endpoint continuum cells with an interval mesh

The prime-quadrature modules use natural endpoints and logarithmic
coordinates, whereas the continuum graph is phrased directly in physical
intervals.  This file proves that the two diagonal and double-kernel
matrices are literally the same after identifying endpoints.  The kernel
proof includes the required Fubini swap on positive rectangles.
-/

open scoped BigOperators
open Set

noncomputable section

namespace Erdos390.Full
namespace ContinuumCellGraph
namespace IntervalMesh

open MeasureTheory
open ConditionedPoissonLimit
open KernelPrimeQuadrature
open DoubleKernelPrimeQuadrature
open DiagonalPrimeQuadrature
open CompressedArithmeticOperator

variable {Band : Type*} [Fintype Band]
variable {epsilon : ℝ} (M : IntervalMesh epsilon Band)

private theorem double_intervalIntegral_swap_of_continuous
    {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d)
    {g : ℝ → ℝ → ℝ} (hg : Continuous (Function.uncurry g)) :
    (∫ s in a..b, ∫ t in c..d, g s t) =
      ∫ t in c..d, ∫ s in a..b, g s t := by
  have hIntegrableOn : IntegrableOn (Function.uncurry g)
      (Ioc a b ×ˢ Ioc c d) := by
    apply (hg.continuousOn.integrableOn_compact
      (isCompact_Icc.prod isCompact_Icc)).mono_set
    exact prod_mono Ioc_subset_Icc_self Ioc_subset_Icc_self
  have hIntegrable : Integrable (Function.uncurry g)
      ((volume.restrict (Ioc a b)).prod
        (volume.restrict (Ioc c d))) := by
    rw [Measure.prod_restrict]
    exact hIntegrableOn
  simp_rw [intervalIntegral.integral_of_le hab,
    intervalIntegral.integral_of_le hcd]
  exact integral_integral_swap hIntegrable

theorem harmonicMass_eq_continuumCellMass
    (z : ℝ) (lower upper : Band → ℕ)
    (hLower : ∀ i, M.lower i = realLogCoordinate z (lower i : ℝ))
    (hUpper : ∀ i, M.upper i = realLogCoordinate z (upper i : ℝ))
    (i : Band) :
    M.harmonicMass i = continuumCellMass z (lower i) (upper i) := by
  have hlo : 0 < realLogCoordinate z (lower i : ℝ) := by
    rw [← hLower]
    exact M.lower_pos i
  have hup : 0 < realLogCoordinate z (upper i : ℝ) := by
    rw [← hUpper]
    exact (M.lower_pos i).trans (M.lower_lt_upper i)
  unfold harmonicMass continuumCellMass
  rw [hLower, hUpper, integral_one_div_of_pos hlo hup,
    Real.log_div hup.ne' hlo.ne']

theorem normalizedDiagonalCell_eq_endpointContinuum
    (z : ℝ) (lower upper : Band → ℕ)
    (hLower : ∀ i, M.lower i = realLogCoordinate z (lower i : ℝ))
    (hUpper : ∀ i, M.upper i = realLogCoordinate z (upper i : ℝ))
    (i : Band) :
    M.normalizedDiagonalCell i = continuumDiagonal z lower upper i := by
  unfold normalizedDiagonalCell continuumDiagonal
  unfold normalizedDiagonalContinuumCell diagonalContinuumCell
    continuumCellOperator
  rw [hLower, hUpper, M.harmonicMass_eq_continuumCellMass
    z lower upper hLower hUpper i]

private theorem doubleKernelNumerator_eq_endpointContinuum
    (z : ℝ) (lower upper : Band → ℕ)
    (hLower : ∀ i, M.lower i = realLogCoordinate z (lower i : ℝ))
    (hUpper : ∀ i, M.upper i = realLogCoordinate z (upper i : ℝ))
    (i j : Band) :
    (∫ s in M.lower i..M.upper i,
      ∫ t in M.lower j..M.upper j,
        covarianceKernelQuotient t s / t) =
      doubleContinuumKernelCell z
        (lower i) (upper i) (lower j) (upper j) := by
  let di : ℝ → ℝ := fun s => max s (M.lower i / 2)
  let dj : ℝ → ℝ := fun t => max t (M.lower j / 2)
  let g : ℝ → ℝ → ℝ := fun s t =>
    covarianceKernel t s / di s / dj t
  have hdiCont : Continuous di :=
    continuous_id.max
      (continuous_const : Continuous fun _ : ℝ => M.lower i / 2)
  have hdjCont : Continuous dj :=
    continuous_id.max
      (continuous_const : Continuous fun _ : ℝ => M.lower j / 2)
  have hdi0 (s : ℝ) : di s ≠ 0 := by
    apply ne_of_gt
    exact (half_pos (M.lower_pos i)).trans_le (le_max_right _ _)
  have hdj0 (t : ℝ) : dj t ≠ 0 := by
    apply ne_of_gt
    exact (half_pos (M.lower_pos j)).trans_le (le_max_right _ _)
  have hg : Continuous (Function.uncurry g) := by
    dsimp only [g, Function.uncurry]
    exact (continuous_covarianceKernel.comp
      (continuous_snd.prodMk continuous_fst)).div
        (hdiCont.comp continuous_fst) (fun x => hdi0 x.1) |>.div
        (hdjCont.comp continuous_snd) (fun x => hdj0 x.2)
  have hdiCell {s : ℝ} (hs : s ∈ Icc (M.lower i) (M.upper i)) :
      di s = s := by
    have hhalf : M.lower i / 2 ≤ s := by
      linarith [M.lower_pos i, hs.1]
    simp [di, max_eq_left hhalf]
  have hdjCell {t : ℝ} (ht : t ∈ Icc (M.lower j) (M.upper j)) :
      dj t = t := by
    have hhalf : M.lower j / 2 ≤ t := by
      linarith [M.lower_pos j, ht.1]
    simp [dj, max_eq_left hhalf]
  have hleft :
      (∫ s in M.lower i..M.upper i,
        ∫ t in M.lower j..M.upper j,
          covarianceKernelQuotient t s / t) =
        ∫ s in M.lower i..M.upper i,
          ∫ t in M.lower j..M.upper j, g s t := by
    apply intervalIntegral.integral_congr
    intro s hs
    have hscc : s ∈ Icc (M.lower i) (M.upper i) := by
      simpa [uIcc_of_le (le_of_lt (M.lower_lt_upper i))] using hs
    apply intervalIntegral.integral_congr
    intro t ht
    have htcc : t ∈ Icc (M.lower j) (M.upper j) := by
      simpa [uIcc_of_le (le_of_lt (M.lower_lt_upper j))] using ht
    have hsUnit := M.cell_mem_unit hscc
    have htUnit := M.cell_mem_unit htcc
    have hs0 : s ≠ 0 := ne_of_gt ((M.lower_pos i).trans_le hscc.1)
    unfold g
    rw [hdiCell hscc, hdjCell htcc]
    change covarianceKernelQuotient t s / t =
      covarianceKernel t s / s / t
    rw [covarianceKernelQuotient_eq_div htUnit hsUnit hs0]
  have hright :
      (∫ t in M.lower j..M.upper j,
        ∫ s in M.lower i..M.upper i, g s t) =
      doubleContinuumKernelCell z
        (lower i) (upper i) (lower j) (upper j) := by
    unfold doubleContinuumKernelCell continuumCellOperator
    rw [← hLower i, ← hUpper i, ← hLower j, ← hUpper j]
    apply intervalIntegral.integral_congr
    intro t ht
    have htcc : t ∈ Icc (M.lower j) (M.upper j) := by
      simpa [uIcc_of_le (le_of_lt (M.lower_lt_upper j))] using ht
    change (∫ s in M.lower i..M.upper i, g s t) =
      (∫ s in M.lower i..M.upper i,
        covarianceKernel t s / s) / t
    rw [← intervalIntegral.integral_div]
    apply intervalIntegral.integral_congr
    intro s hs
    have hscc : s ∈ Icc (M.lower i) (M.upper i) := by
      simpa [uIcc_of_le (le_of_lt (M.lower_lt_upper i))] using hs
    unfold g
    change covarianceKernel t s / di s / dj t =
      covarianceKernel t s / s / t
    rw [hdiCell hscc, hdjCell htcc]
  rw [hleft,
    double_intervalIntegral_swap_of_continuous
      (le_of_lt (M.lower_lt_upper i))
      (le_of_lt (M.lower_lt_upper j)) hg,
    hright]

theorem normalizedKernelCell_eq_endpointContinuum
    (z : ℝ) (lower upper : Band → ℕ)
    (hLower : ∀ i, M.lower i = realLogCoordinate z (lower i : ℝ))
    (hUpper : ∀ i, M.upper i = realLogCoordinate z (upper i : ℝ))
    (i j : Band) :
    M.normalizedKernelCell i j = continuumKernel z lower upper i j := by
  unfold normalizedKernelCell continuumKernel
  unfold normalizedDoubleContinuumKernelCell
  rw [M.doubleKernelNumerator_eq_endpointContinuum
      z lower upper hLower hUpper i j,
    M.harmonicMass_eq_continuumCellMass
      z lower upper hLower hUpper i]

end IntervalMesh
end ContinuumCellGraph
end Erdos390.Full

end

/- Source module: Erdos390.Full.CanonicalEndpointWeightedInverseEventually -/
section


/-!
# Eventual weighted inverse for the literal canonical endpoint family

This file combines the unconditional endpoint estimates with the deterministic
attachment theorem.  The order of choices is explicit: the Dickman gap and a
mesh tolerance are selected first, the fixed cutoff is selected next, and the
ambient integer is taken sufficiently large last.
-/

open scoped BigOperators
open Filter Topology Set

noncomputable section

namespace Erdos390.Full.RegularMeshPrimeCutoffs

open ArithmeticModel ArithmeticBandGeometry RegularRelativeMesh
open KernelPrimeQuadrature DoubleKernelPrimeQuadrature
open ContinuumCellGraph ContinuumCellGraph.IntervalMesh
open CompressedArithmeticOperator PositiveCellTransfer
open MovingLowGaugeTransfer
open PaperWeightedInverseExport
open PoissonDickmanWeightedInverse PoissonDickmanKernelBounds

namespace Mesh

variable {delta eta : ℝ} (M : Mesh delta eta)

/-- A single global modulus and the two literal endpoint tails imply the
two-tail row-residual estimate for every finite interval mesh.  The constants
do not depend on the number of cells. -/
theorem rowResidual_lt_of_global_modulus
    {Band : Type*} [Fintype Band] [DecidableEq Band]
    {epsilon target meshTol beta C : ℝ}
    (IM : IntervalMesh epsilon Band)
    (T : IM.TwoTailPartitionCertificate)
    (htarget : 0 < target)
    (hC : 0 ≤ C)
    (hKernel : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
      |ConditionedPoissonLimit.covarianceKernelQuotient t s| ≤ C)
    (hFmod : ∀ x ∈ Icc (0 : ℝ) 1, ∀ y ∈ Icc (0 : ℝ) 1,
      |x - y| < meshTol → |DickmanBasic.F x - DickmanBasic.F y| < target / 10)
    (hKmod : ∀ s ∈ Icc (0 : ℝ) 1,
      ∀ t ∈ Icc (0 : ℝ) 1, ∀ u ∈ Icc (0 : ℝ) 1,
        |t - u| < meshTol →
          |ConditionedPoissonLimit.covarianceKernelQuotient t s -
            ConditionedPoissonLimit.covarianceKernelQuotient u s| < target / 10)
    (hbeta : beta = target / (5 * (C + 1)))
    (hBase : T.base < beta) (hTop : 1 - T.upperEnd < beta)
    (hLength : ∀ j, IM.length j < meshTol)
    (i : Band) :
    |IM.rowResidual i| < target := by
  have hCplus : 0 < C + 1 := by linarith
  have hFosc (j : Band) (s : ℝ)
      (hs : s ∈ Icc (IM.lower j) (IM.upper j)) :
      |DickmanBasic.F s - DickmanBasic.F (IM.lower j)| ≤ target / 10 := by
    apply (hFmod s (IM.cell_mem_unit hs) (IM.lower j)
      ⟨(IM.lower_pos j).le,
        (IM.lower_lt_upper j).le.trans (IM.upper_le_one j)⟩ ?_).le
    rw [abs_of_nonneg (sub_nonneg.mpr hs.1)]
    have : s - IM.lower j ≤ IM.length j := by
      unfold IntervalMesh.length
      linarith [hs.2]
    exact this.trans_lt (hLength j)
  have hKosc (j : Band) (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1)
      (t : ℝ) (ht : t ∈ Icc (IM.lower j) (IM.upper j)) :
      |ConditionedPoissonLimit.covarianceKernelQuotient t s -
        ConditionedPoissonLimit.covarianceKernelQuotient (IM.lower j) s| ≤
          target / 10 := by
    apply (hKmod s hs t (IM.cell_mem_unit ht) (IM.lower j)
      ⟨(IM.lower_pos j).le,
        (IM.lower_lt_upper j).le.trans (IM.upper_le_one j)⟩ ?_).le
    rw [abs_of_nonneg (sub_nonneg.mpr ht.1)]
    have : t - IM.lower j ≤ IM.length j := by
      unfold IntervalMesh.length
      linarith [ht.2]
    exact this.trans_lt (hLength j)
  have hraw := IM.abs_rowResidual_le_twoTails T hFosc hKosc hKernel i
  have hmiddle : T.upperEnd - T.base ≤ 1 := by
    linarith [T.base_nonneg, T.upperEnd_le_one]
  have hkernelTerm :
      2 * (target / 10) * (T.upperEnd - T.base) ≤ target / 5 := by
    have hcoef : 0 ≤ 2 * (target / 10) := by positivity
    calc
      2 * (target / 10) * (T.upperEnd - T.base) ≤
          2 * (target / 10) * 1 :=
        mul_le_mul_of_nonneg_left hmiddle hcoef
      _ = target / 5 := by ring
  have hlow : C * T.base < target / 5 := by
    have hfirst : C * T.base ≤ (C + 1) * T.base :=
      mul_le_mul_of_nonneg_right (by linarith) T.base_nonneg
    have hsecond : (C + 1) * T.base < (C + 1) * beta :=
      mul_lt_mul_of_pos_left hBase hCplus
    have heq : (C + 1) * beta = target / 5 := by
      rw [hbeta]
      field_simp [ne_of_gt hCplus]
    exact hfirst.trans_lt (hsecond.trans_eq heq)
  have hhigh : C * (1 - T.upperEnd) < target / 5 := by
    have hnonneg : 0 ≤ 1 - T.upperEnd := sub_nonneg.mpr T.upperEnd_le_one
    have hfirst : C * (1 - T.upperEnd) ≤
        (C + 1) * (1 - T.upperEnd) :=
      mul_le_mul_of_nonneg_right (by linarith) hnonneg
    have hsecond : (C + 1) * (1 - T.upperEnd) < (C + 1) * beta :=
      mul_lt_mul_of_pos_left hTop hCplus
    have heq : (C + 1) * beta = target / 5 := by
      rw [hbeta]
      field_simp [ne_of_gt hCplus]
    exact hfirst.trans_lt (hsecond.trans_eq heq)
  calc
    |IM.rowResidual i| ≤
        2 * (target / 10) +
          2 * (target / 10) * (T.upperEnd - T.base) +
          C * T.base + C * (1 - T.upperEnd) := hraw
    _ < target := by
      have hdiag : 2 * (target / 10) = target / 5 := by ring
      rw [hdiag]
      linarith



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

/- Source module: Erdos390.Full.PaperActualSlowRightRowFinite -/
section


/-!
# Exact finite reference estimate for the slow right row

This file isolates the moving-low-cell estimate which is easy to lose if
one bounds the Dickman diagonal by an absolute constant.  The arithmetic
deviation is centred on every actual prime fiber.  We therefore subtract
`F (alpha_i)` in the diagonal term before estimating it.  The resulting
bound retains the factor `alpha_i`, including on the low cell where
`alpha_i` tends to zero.
-/

open scoped BigOperators

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

open ArithmeticModel ArithmeticBandGeometry
open SquarefreeSharpBandTransfer SquarefreeCovarianceReference
open SquarefreeReferenceOperatorIdentification
open PrimeSquarefreeDirichletGeometry
open FiniteAnchoredDirichletQuadratic
open ConditionedPoissonLimit DickmanBasic

namespace PaperActualSlowRightRowFinite

/-- A uniform Lipschitz constant for the Dickman diagonal profile on the
closed unit interval.  This is extracted from the already proved
differentiability and continuity of `F`; it is independent of every mesh,
cutoff, ambient integer, and tilt box. -/
theorem exists_F_lipschitz_unit :
    ∃ CF : ℝ, 0 < CF ∧ ∀ s ∈ Set.Icc (0 : ℝ) 1,
      ∀ t ∈ Set.Icc (0 : ℝ) 1,
        |F s - F t| ≤ CF * |s - t| := by
  have hcontinuous : ContinuousOn (fun x : ℝ => ‖deriv F x‖)
      (Set.Icc (0 : ℝ) 1) := by
    exact (continuousOn_deriv_F.mono (Set.Icc_subset_Icc_right
      (by norm_num : (1 : ℝ) ≤ 2))).norm
  obtain ⟨x, hx, hmax⟩ := isCompact_Icc.exists_isMaxOn
    (Set.nonempty_Icc.mpr (by norm_num : (0 : ℝ) ≤ 1)) hcontinuous
  let CF : ℝ := 1 + ‖deriv F x‖
  have hCF : 0 < CF := by
    dsimp only [CF]
    positivity
  refine ⟨CF, hCF, ?_⟩
  intro s hs t ht
  have hderiv (u : ℝ) (hu : u ∈ Set.Icc (0 : ℝ) 1) :
      ‖deriv F u‖ ≤ CF := by
    dsimp only [CF]
    exact (hmax hu).trans (le_add_of_nonneg_left (by norm_num))
  have hbound := Convex.norm_image_sub_le_of_norm_deriv_le
    (f := F) (C := CF)
    (fun u hu => differentiableAt_F
      ⟨hu.1, hu.2.trans (by norm_num)⟩)
    hderiv (convex_Icc (0 : ℝ) 1) ht hs
  simpa only [Real.norm_eq_abs] using hbound

end PaperActualSlowRightRowFinite

namespace BridgeData

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]
  (B : BridgeData Head Band)



end BridgeData

end

end Erdos390.Full.PaperBridgeFit

end

/- Source module: Erdos390.Full.ContinuumCellGraphReversible -/
section


/-!
# Reversibility of the continuum cell graph

After the centre conjugation, the cell edge is reversible for the exact
sharp gauge weight `H_i alpha_i^2`.  The proof below keeps the moving low
cell: all divisions occur on its positive interval `[t₀,δ]`, and no lower
bound independent of `t₀` is used.
-/

open scoped BigOperators
open Set

noncomputable section

namespace Erdos390.Full.ContinuumCellGraph
namespace IntervalMesh

open MeasureTheory
open ConditionedPoissonLimit
open FiniteGraphQuotientInverse
open FiniteReversibleGraph

variable {Band : Type*} [Fintype Band] [DecidableEq Band]
variable {epsilon : ℝ} (M : IntervalMesh epsilon Band)





omit [DecidableEq Band] in
/-- The exact harmonic-centre gauge weight equals `length * center`. -/
theorem harmonicMass_mul_center_sq_eq (i : Band) :
    M.harmonicMass i * M.center i ^ 2 = M.length i * M.center i := by
  unfold center
  field_simp [ne_of_gt (M.harmonicMass_pos i)]







end IntervalMesh
end Erdos390.Full.ContinuumCellGraph

end

/- Source module: Erdos390.Full.ContinuumRawLowRow -/
section


/-!
# Ordinary low-row bounds for the continuum cell compression

The product estimate `|K(s,t)| ≤ C s t` cancels both harmonic variables in
the compressed kernel.  Consequently the entire raw kernel row of a cell is
bounded by its harmonic centre, even when the mesh contains many cells below
a fixed cutoff.  This is the estimate that prevents the growing low harmonic
mass from entering the ordinary inverse.
-/

open scoped BigOperators
open Set

noncomputable section

namespace Erdos390.Full.ContinuumCellGraph
namespace IntervalMesh

open MeasureTheory
open ConditionedPoissonLimit
open DickmanBasic
open PaperWeightedInverseExport

variable {Band : Type*} [Fintype Band]
variable {epsilon : ℝ} (M : IntervalMesh epsilon Band)





/-- Harmonic averaging preserves a pointwise modulus from the value
`F(0)=1`; this is the exact diagonal estimate used on every low cell. -/
theorem abs_normalizedDiagonalCell_sub_one_le
    {d : ℝ} (i : Band)
    (hF : ∀ s ∈ Icc (M.lower i) (M.upper i), |F s - 1| ≤ d) :
    |M.normalizedDiagonalCell i - 1| ≤ d := by
  have hab : M.lower i ≤ M.upper i := (M.lower_lt_upper i).le
  have hdiffInt : IntervalIntegrable (fun s : ℝ ↦ (F s - 1) / s)
      volume (M.lower i) (M.upper i) := by
    apply ContinuousOn.intervalIntegrable_of_Icc hab
    intro s hs
    exact ((continuous_F.sub continuous_const).continuousAt.div
      continuousAt_id
      (ne_of_gt ((M.lower_pos i).trans_le hs.1))).continuousWithinAt
  have hmajorInt : IntervalIntegrable (fun s : ℝ ↦ d * (1 / s))
      volume (M.lower i) (M.upper i) := by
    apply ContinuousOn.intervalIntegrable_of_Icc hab
    intro s hs
    exact (continuousAt_const.mul (continuousAt_const.div continuousAt_id
      (ne_of_gt ((M.lower_pos i).trans_le hs.1)))).continuousWithinAt
  have hnorm := intervalIntegral.norm_integral_le_of_norm_le hab
    (f := fun s : ℝ ↦ (F s - 1) / s)
    (g := fun s : ℝ ↦ d * (1 / s)) (by
      filter_upwards with s hs
      have hscc : s ∈ Icc (M.lower i) (M.upper i) :=
        ⟨hs.1.le, hs.2⟩
      rw [Real.norm_eq_abs, abs_div,
        abs_of_pos ((M.lower_pos i).trans_le hscc.1)]
      calc
        |F s - 1| / s ≤ d / s :=
          div_le_div_of_nonneg_right (hF s hscc)
            ((M.lower_pos i).trans_le hscc.1).le
        _ = d * (1 / s) := by ring) hmajorInt
  have hmass : 0 < M.harmonicMass i := M.harmonicMass_pos i
  have hnorm' : |∫ s in M.lower i..M.upper i, (F s - 1) / s| ≤
      d * M.harmonicMass i := by
    rw [intervalIntegral.integral_const_mul] at hnorm
    simpa only [Real.norm_eq_abs, harmonicMass] using hnorm
  unfold normalizedDiagonalCell
  have hFInt : IntervalIntegrable (fun s : ℝ ↦ F s / s)
      volume (M.lower i) (M.upper i) := by
    apply ContinuousOn.intervalIntegrable_of_Icc hab
    intro s hs
    exact (continuous_F.continuousAt.div continuousAt_id
      (ne_of_gt ((M.lower_pos i).trans_le hs.1))).continuousWithinAt
  have hOneInt : IntervalIntegrable (fun s : ℝ ↦ 1 / s)
      volume (M.lower i) (M.upper i) := by
    apply ContinuousOn.intervalIntegrable_of_Icc hab
    intro s hs
    exact (continuousAt_const.div continuousAt_id
      (ne_of_gt ((M.lower_pos i).trans_le hs.1))).continuousWithinAt
  have hid : (∫ s in M.lower i..M.upper i, (F s - 1) / s) =
      (∫ s in M.lower i..M.upper i, F s / s) - M.harmonicMass i := by
    rw [show (fun s : ℝ ↦ (F s - 1) / s) =
        fun s : ℝ ↦ F s / s - 1 / s by
      funext s
      ring]
    rw [intervalIntegral.integral_sub hFInt hOneInt]
    unfold harmonicMass
    rfl
  rw [show (∫ s in M.lower i..M.upper i, F s / s) /
      M.harmonicMass i - 1 =
      ((∫ s in M.lower i..M.upper i, F s / s) -
        M.harmonicMass i) / M.harmonicMass i by
      field_simp [ne_of_gt hmass] ]
  rw [← hid, abs_div, abs_of_pos hmass]
  exact (div_le_iff₀ hmass).2 (by
    simpa only [mul_comm] using hnorm')



end IntervalMesh
end Erdos390.Full.ContinuumCellGraph

end

/- Source module: Erdos390.Full.ContinuumManyLowHighGeometry -/
section


/-!
# Low--high geometry for the ordinary continuum inverse

The ordinary inverse cannot be obtained from the sharp inverse by dividing
by the least cell centre: the centre of the moving low cell tends to zero.
This file instead records the exact estimates used after splitting a finite
continuum mesh into an arbitrary low block and a high block.  The product
kernel bound makes every edge entering a low cell proportional to both the
ordinary length and the centre of that cell.  Consequently all constants
below depend on the total low length, not on the number of low cells or on
their least endpoint.

No inverse, coercivity, or convergence statement is assumed here.
-/

open scoped BigOperators
open Set

noncomputable section

namespace Erdos390.Full.ContinuumCellGraph
namespace IntervalMesh

open ConditionedPoissonLimit
open FiniteGraphQuotientInverse

variable {Band Low High : Type*}
  [Fintype Band] [Fintype Low]
variable {epsilon : ℝ} (M : IntervalMesh epsilon Band)







section Anchor

variable [DecidableEq Band]





omit [Fintype Low] in
/-- The sharp gauge weight of the high block is bounded below by its anchor
length times the least high centre.  This estimate is independent of the
number of low cells. -/
theorem amin_mul_highAnchor_le_highSharpWeight
    [Fintype High]
    (e : Sum Low High ≃ Band) {amin : ℝ}
    (hAmin : 0 ≤ amin)
    (hHighCenter : ∀ i : High, amin ≤ M.center (e (.inr i))) :
    amin * (∑ i : High, splitHighAnchor M e i) ≤
      ∑ i : High,
        M.harmonicMass (e (.inr i)) * M.center (e (.inr i)) ^ 2 := by
  have hAnchorLe (i : High) :
      splitHighAnchor M e i ≤ M.length (e (.inr i)) := by
    unfold splitHighAnchor anchor
    split_ifs
    · exact le_rfl
    · exact (M.length_pos _).le
  calc
    amin * (∑ i : High, splitHighAnchor M e i) =
        ∑ i : High, amin * splitHighAnchor M e i := by
      rw [Finset.mul_sum]
    _ ≤ ∑ i : High, amin * M.length (e (.inr i)) := by
      apply Finset.sum_le_sum
      intro i hi
      exact mul_le_mul_of_nonneg_left (hAnchorLe i) hAmin
    _ ≤ ∑ i : High,
        M.length (e (.inr i)) * M.center (e (.inr i)) := by
      apply Finset.sum_le_sum
      intro i hi
      calc
        amin * M.length (e (.inr i)) =
            M.length (e (.inr i)) * amin := by ring
        _ ≤ M.length (e (.inr i)) * M.center (e (.inr i)) :=
          mul_le_mul_of_nonneg_left (hHighCenter i) (M.length_pos _).le
    _ = ∑ i : High,
        M.harmonicMass (e (.inr i)) * M.center (e (.inr i)) ^ 2 := by
      apply Finset.sum_congr rfl
      intro i hi
      exact (M.harmonicMass_mul_center_sq_eq (e (.inr i))).symm





end Anchor









end IntervalMesh
end Erdos390.Full.ContinuumCellGraph

end

/- Source module: Erdos390.Full.RegularRelativeMeshPrefixSplit -/
section


/-!
# Prefix split at a fixed logarithmic threshold

The moving low cell and all positive cells before the first ideal endpoint
crossing `tau` form the low block.  The remaining positive cells form the
high block.  The construction is purely ideal-mesh geometry and therefore
does not depend on the later arithmetic cutoff or ambient integer.
-/

namespace Erdos390.Full.RegularRelativeMesh

noncomputable section

namespace Mesh

variable {delta eta : ℝ} (M : Mesh delta eta)













theorem width_lt_ratio (hdelta : 0 < delta) (k : Fin M.cellCount) :
    M.width k < M.ratio := by
  rw [M.width_eq_ratio_mul_lower]
  have hlowerOne : M.lower k < 1 :=
    (M.lower_lt_upper hdelta k).trans_le (M.upper_le_one hdelta k)
  nlinarith [M.ratio_pos]

theorem prefix_endpoint_lt_tau_add_ratio
    (hdelta : 0 < delta) {tau : ℝ} (htau : tau ≤ 1)
    (hdeltatau : delta < tau) :
    M.endpoint (M.prefixIndex tau htau) < tau + M.ratio := by
  exact M.firstEndpointAtLeast_endpoint_lt_add tau M.ratio htau
    hdeltatau (M.width_lt_ratio hdelta)

theorem prefix_endpoint_ge_tau (tau : ℝ) (htau : tau ≤ 1) :
    tau ≤ M.endpoint (M.prefixIndex tau htau) :=
  M.firstEndpointAtLeast_spec tau htau

/-- A small relative ratio ensures a nonempty high suffix. -/
theorem prefixIndex_lt_cellCount
    (hdelta : 0 < delta) {tau : ℝ} (htau : tau ≤ 1)
    (htauSmall : tau + M.ratio < 1) :
    M.prefixIndex tau htau < M.cellCount := by
  let last : Fin M.cellCount :=
    ⟨M.cellCount - 1, Nat.sub_lt M.cellCount_pos (by omega)⟩
  have hlastUpper : M.upper last = 1 := by
    dsimp only [last, upper]
    rw [Nat.sub_add_cancel M.cellCount_pos]
    exact M.endpoint_cellCount
  have hlastLower : tau < M.lower last := by
    have hwidth := M.width_lt_ratio hdelta last
    unfold width at hwidth
    rw [hlastUpper] at hwidth
    linarith
  have hWitness : tau ≤ M.endpoint (M.cellCount - 1) := by
    simpa only [last, lower] using hlastLower.le
  have hle : M.prefixIndex tau htau ≤ M.cellCount - 1 := by
    exact Nat.find_min' (M.exists_endpoint_ge tau htau) hWitness
  exact hle.trans_lt (Nat.sub_lt M.cellCount_pos (by omega))

instance prefixHigh_nonempty
    (hdelta : 0 < delta) {tau : ℝ} (htau : tau ≤ 1)
    (htauSmall : tau + M.ratio < 1) :
    Nonempty (M.prefixHigh tau htau) := by
  have hj := M.prefixIndex_lt_cellCount hdelta htau htauSmall
  exact Fin.pos_iff_nonempty.mp (Nat.sub_pos_of_lt hj)





/-- Every ideal anchor cell lying above `tau` belongs to the high suffix. -/
theorem prefixIndex_le_of_tau_lt_lower
    {tau : ℝ} (htau : tau ≤ 1)
    {k : Fin M.cellCount} (hk : tau < M.lower k) :
    M.prefixIndex tau htau ≤ k.1 := by
  by_contra hnot
  have hlt : k.1 < M.prefixIndex tau htau := by omega
  have hbelow := M.endpoint_lt_of_lt_firstEndpointAtLeast tau htau hlt
  exact (not_lt_of_ge hk.le) (by simpa only [lower] using hbelow)

end Mesh
end
end Erdos390.Full.RegularRelativeMesh

end

/- Source module: Erdos390.Full.ContinuumIntervalCenterBounds -/
section


/-!
# Endpoint bounds for the logarithmic mean

The continuum cell centre is the logarithmic mean of its endpoints.  These
elementary endpoint bounds are used by the moving-prefix ordinary inverse.
-/

open Set

noncomputable section

namespace Erdos390.Full.ContinuumCellGraph
namespace IntervalMesh

variable {epsilon : ℝ} {Band : Type*} [Fintype Band]
  (M : IntervalMesh epsilon Band)

theorem harmonicMass_eq_log_div (i : Band) :
    M.harmonicMass i = Real.log (M.upper i / M.lower i) := by
  unfold harmonicMass
  rw [integral_one_div_of_pos (M.lower_pos i)
    ((M.lower_pos i).trans (M.lower_lt_upper i))]

/-- The logarithmic mean lies between the two cell endpoints. -/
theorem lower_le_center (i : Band) : M.lower i ≤ M.center i := by
  have ha : 0 < M.lower i := M.lower_pos i
  have hb : 0 < M.upper i := ha.trans (M.lower_lt_upper i)
  have hratio : 0 < M.upper i / M.lower i := div_pos hb ha
  have hlog := Real.log_le_sub_one_of_pos hratio
  have hmass : M.harmonicMass i ≤ M.length i / M.lower i := by
    rw [M.harmonicMass_eq_log_div]
    calc
      Real.log (M.upper i / M.lower i) ≤
          M.upper i / M.lower i - 1 := hlog
      _ = M.length i / M.lower i := by
        unfold length
        field_simp [ne_of_gt ha]
  have hmul : M.lower i * M.harmonicMass i ≤ M.length i := by
    calc
      M.lower i * M.harmonicMass i ≤
          M.lower i * (M.length i / M.lower i) :=
        mul_le_mul_of_nonneg_left hmass ha.le
      _ = M.length i := by field_simp [ne_of_gt ha]
  rw [center]
  exact (le_div_iff₀ (M.harmonicMass_pos i)).2 (by
    simpa only [mul_comm] using hmul)

theorem center_le_upper (i : Band) : M.center i ≤ M.upper i := by
  have ha : 0 < M.lower i := M.lower_pos i
  have hb : 0 < M.upper i := ha.trans (M.lower_lt_upper i)
  have hratio : 0 < M.upper i / M.lower i := div_pos hb ha
  have hlog := Real.one_sub_inv_le_log_of_pos hratio
  have hmass : M.length i / M.upper i ≤ M.harmonicMass i := by
    rw [M.harmonicMass_eq_log_div]
    have hid : 1 - (M.upper i / M.lower i)⁻¹ =
        M.length i / M.upper i := by
      unfold length
      field_simp [ne_of_gt ha, ne_of_gt hb]
    simpa only [hid] using hlog
  rw [center]
  exact (div_le_iff₀ (M.harmonicMass_pos i)).2 (by
    have hmul := mul_le_mul_of_nonneg_left hmass hb.le
    have hcancel :
        M.upper i * (M.length i / M.upper i) = M.length i := by
      field_simp [ne_of_gt hb]
    nlinarith)

/-- Harmonic mass times the logarithmic mean is exactly the ordinary cell
length.  This identity is the arithmetic/continuum raw-gauge comparison;
it does not replace an arithmetic centre by a continuum centre. -/
theorem harmonicMass_mul_center_eq_length (i : Band) :
    M.harmonicMass i * M.center i = M.length i := by
  unfold center
  field_simp [ne_of_gt (M.harmonicMass_pos i)]

end IntervalMesh
end Erdos390.Full.ContinuumCellGraph

end

/- Source module: Erdos390.Full.CanonicalEndpointPrefixGeometry -/
section


/-!
# Canonical endpoint geometry for the moving prefix split

One literal boundary separates the low prefix from the high suffix.  Its
coordinate converges to the corresponding ideal endpoint.  Consequently,
ordinary centre and length estimates do not divide by the moving low-cell
centre and are uniform in the number of cells.
-/

open scoped BigOperators
open Filter

noncomputable section

namespace Erdos390.Full.RegularMeshPrimeCutoffs

open ArithmeticModel RegularRelativeMesh KernelPrimeQuadrature
  DoubleKernelPrimeQuadrature
  ContinuumCellGraph

namespace Mesh

variable {delta eta : ℝ} (M : Mesh delta eta)



theorem tendsto_canonicalPrefixBoundary
    (hdelta : 0 < delta) (W : ℕ) (tau : ℝ) (htau : tau ≤ 1) :
    Tendsto (fun n : ℕ ↦ canonicalPrefixBoundary M n W tau htau)
      atTop (nhds (M.endpoint (M.prefixIndex tau htau))) := by
  simpa only [canonicalPrefixBoundary, actualCutoffCoordinate,
    fullCutoff_succ, RegularRelativeMesh.Mesh.prefixIndex] using
      tendsto_floor_scalePoint_coordinate
        (M.endpoint_pos hdelta (M.firstEndpointAtLeast tau htau))

/-- If the ideal mesh scale is small relative to `tau`, the actual prefix
boundary eventually stays between `tau/2` and `2*tau`. -/
theorem eventually_canonicalPrefixBoundary_between
    (hdelta : 0 < delta) {tau : ℝ} (htau : tau ≤ 1)
    (hdeltatau : delta < tau)
    (hratio : M.ratio ≤ tau / 2) (W : ℕ) :
    ∀ᶠ n : ℕ in atTop,
      tau / 2 ≤ canonicalPrefixBoundary M n W tau htau ∧
        canonicalPrefixBoundary M n W tau htau ≤ 2 * tau := by
  let a := M.endpoint (M.prefixIndex tau htau)
  have haLower : tau / 2 < a := by
    have hspec := M.prefix_endpoint_ge_tau tau htau
    dsimp only [a]
    linarith
  have haUpper : a < 2 * tau := by
    have hcross := M.prefix_endpoint_lt_tau_add_ratio hdelta htau hdeltatau
    dsimp only [a]
    linarith
  have hlim := tendsto_canonicalPrefixBoundary M hdelta W tau htau
  have hlower := hlim.eventually (eventually_ge_nhds haLower)
  have hupper := hlim.eventually (eventually_le_nhds haUpper)
  filter_upwards [hlower, hupper] with n hnLower hnUpper
  exact ⟨hnLower, hnUpper⟩

section LiteralGeometry

variable {n W : ℕ} (hdelta : 0 < delta) (hn : 1 < n)
  (hW : W ≠ 0) (hWTwo : 2 ≤ W) (S : ScaleSeparation M n W)
  {tau epsilon : ℝ} (htau : tau ≤ 1)
  (anchors : Finset (Fin M.cellCount)) (hAnchors : anchors.Nonempty)
  (hIdealAnchorLower : ∀ k ∈ anchors, tau < M.lower k)
  (hInteriorLower : ∀ k ∈ anchors, epsilon ≤
    realLogCoordinate (y n)
      ((canonicalCertificate M hdelta hn hW S).lower
        (positiveBand M k) : ℝ))
  (hInteriorUpper : ∀ k ∈ anchors,
    realLogCoordinate (y n)
      ((canonicalCertificate M hdelta hn hW S).upper
        (positiveBand M k) : ℝ) ≤ 1 - epsilon)

theorem canonicalPrefix_low_center_le_boundary
    (l : M.prefixLow tau htau) :
    let IM := canonicalIntervalMeshOfAnchors M hdelta hn hW hWTwo S epsilon
      anchors hAnchors hInteriorLower hInteriorUpper
    let split := M.prefixSplitEquiv tau htau
    IM.center (split (.inl l)) ≤
      canonicalPrefixBoundary M n W tau htau := by
  dsimp only
  let IM := canonicalIntervalMeshOfAnchors M hdelta hn hW hWTwo S epsilon
    anchors hAnchors hInteriorLower hInteriorUpper
  let split := M.prefixSplitEquiv tau htau
  change IM.center (split (.inl l)) ≤
    canonicalPrefixBoundary M n W tau htau
  have hcenter := IM.center_le_upper (split (.inl l))
  have hmono : Monotone (fullCutoff M n W) :=
    fullCutoff_monotone M hdelta hn (W_le_first_fullCutoff M S)
  have hidx : (split (.inl l)).1 + 1 ≤ M.prefixIndex tau htau + 1 := by
    change l.1 + 1 ≤ M.prefixIndex tau htau + 1
    have hl : l.1 < M.prefixIndex tau htau + 1 := l.2
    omega
  have hcut := hmono hidx
  have hy : 1 < y n := by
    rw [← Real.log_pos_iff (Scale.y_pos (Nat.zero_lt_of_lt hn)).le]
    rw [Scale.log_y (Nat.zero_lt_of_lt hn)]
    exact mul_pos (by norm_num) (Real.log_pos (by exact_mod_cast hn))
  have hlowerTwo : 2 ≤ fullCutoff M n W ((split (.inl l)).1 + 1) :=
    hWTwo.trans (hmono (Nat.zero_le _))
  have hcoord := realLogCoordinate_mono_nat hy hlowerTwo hcut
  exact hcenter.trans (by
    simpa only [canonicalIntervalMeshOfAnchors_upper,
      canonicalCertificate_upper, canonicalPrefixBoundary,
      actualCutoffCoordinate] using hcoord)

theorem canonicalPrefix_boundary_le_high_center
    (k : M.prefixHigh tau htau) :
    let IM := canonicalIntervalMeshOfAnchors M hdelta hn hW hWTwo S epsilon
      anchors hAnchors hInteriorLower hInteriorUpper
    let split := M.prefixSplitEquiv tau htau
    canonicalPrefixBoundary M n W tau htau ≤
      IM.center (split (.inr k)) := by
  dsimp only
  let IM := canonicalIntervalMeshOfAnchors M hdelta hn hW hWTwo S epsilon
    anchors hAnchors hInteriorLower hInteriorUpper
  let split := M.prefixSplitEquiv tau htau
  change canonicalPrefixBoundary M n W tau htau ≤
    IM.center (split (.inr k))
  have hcenter := IM.lower_le_center (split (.inr k))
  have hmono : Monotone (fullCutoff M n W) :=
    fullCutoff_monotone M hdelta hn (W_le_first_fullCutoff M S)
  have hidx : M.prefixIndex tau htau + 1 ≤ (split (.inr k)).1 := by
    change M.prefixIndex tau htau + 1 ≤
      M.prefixIndex tau htau + 1 + k.1
    omega
  have hcut := hmono hidx
  have hy : 1 < y n := by
    rw [← Real.log_pos_iff (Scale.y_pos (Nat.zero_lt_of_lt hn)).le]
    rw [Scale.log_y (Nat.zero_lt_of_lt hn)]
    exact mul_pos (by norm_num) (Real.log_pos (by exact_mod_cast hn))
  have hlowerTwo : 2 ≤ fullCutoff M n W (M.prefixIndex tau htau + 1) :=
    hWTwo.trans (hmono (Nat.zero_le _))
  have hcoord := realLogCoordinate_mono_nat hy hlowerTwo hcut
  have hcoord' : canonicalPrefixBoundary M n W tau htau ≤
      IM.lower (split (.inr k)) := by
    simpa only [canonicalIntervalMeshOfAnchors_lower,
      canonicalCertificate_lower, canonicalPrefixBoundary,
      actualCutoffCoordinate] using hcoord
  exact hcoord'.trans hcenter

theorem sum_canonicalPrefix_low_length_eq :
    let IM := canonicalIntervalMeshOfAnchors M hdelta hn hW hWTwo S epsilon
      anchors hAnchors hInteriorLower hInteriorUpper
    let split := M.prefixSplitEquiv tau htau
    (∑ l : M.prefixLow tau htau, IM.length (split (.inl l))) =
      canonicalPrefixBoundary M n W tau htau -
        actualCutoffCoordinate M n W 0 := by
  dsimp only
  let j := M.prefixIndex tau htau
  change (∑ l : Fin (j + 1),
      (fun r : ℕ ↦ actualCutoffCoordinate M n W (r + 1) -
        actualCutoffCoordinate M n W r) l.1) =
      actualCutoffCoordinate M n W (j + 1) -
        actualCutoffCoordinate M n W 0
  calc
    _ = ∑ r ∈ Finset.range (j + 1),
        (actualCutoffCoordinate M n W (r + 1) -
          actualCutoffCoordinate M n W r) :=
      Fin.sum_univ_eq_sum_range _ (j + 1)
    _ = _ := by rw [Finset.sum_range_sub]

theorem sum_canonicalPrefix_low_length_le_boundary :
    let IM := canonicalIntervalMeshOfAnchors M hdelta hn hW hWTwo S epsilon
      anchors hAnchors hInteriorLower hInteriorUpper
    let split := M.prefixSplitEquiv tau htau
    (∑ l : M.prefixLow tau htau, IM.length (split (.inl l))) ≤
      canonicalPrefixBoundary M n W tau htau := by
  dsimp only
  rw [sum_canonicalPrefix_low_length_eq M hdelta hn hW hWTwo S htau
    anchors hAnchors hInteriorLower hInteriorUpper]
  have hbase : 0 ≤ actualCutoffCoordinate M n W 0 := by
    simp only [actualCutoffCoordinate, fullCutoff_zero, realLogCoordinate]
    exact div_nonneg (Real.log_nonneg (by exact_mod_cast
      (show 1 ≤ W by omega)))
      (Real.log_nonneg (by
        have hy : 1 < y n := by
          rw [← Real.log_pos_iff (Scale.y_pos
            (Nat.zero_lt_of_lt hn)).le]
          rw [Scale.log_y (Nat.zero_lt_of_lt hn)]
          exact mul_pos (by norm_num)
            (Real.log_pos (by exact_mod_cast hn))
        exact hy.le))
  linarith

theorem sum_canonical_all_length_le_one :
    let IM := canonicalIntervalMeshOfAnchors M hdelta hn hW hWTwo S epsilon
      anchors hAnchors hInteriorLower hInteriorUpper
    (∑ i : Fin (M.cellCount + 1), IM.length i) ≤ 1 := by
  dsimp only
  let m := M.cellCount + 1
  change (∑ i : Fin m,
      (fun r : ℕ ↦ actualCutoffCoordinate M n W (r + 1) -
        actualCutoffCoordinate M n W r) i.1) ≤ 1
  have hsum : (∑ i : Fin m,
      (fun r : ℕ ↦ actualCutoffCoordinate M n W (r + 1) -
        actualCutoffCoordinate M n W r) i.1) =
      ∑ r ∈ Finset.range m,
        (actualCutoffCoordinate M n W (r + 1) -
          actualCutoffCoordinate M n W r) :=
    Fin.sum_univ_eq_sum_range
      (fun r : ℕ ↦ actualCutoffCoordinate M n W (r + 1) -
        actualCutoffCoordinate M n W r) m
  rw [hsum, Finset.sum_range_sub]
  have htop : actualCutoffCoordinate M n W m ≤ 1 := by
    have hfloor : (yNat n : ℝ) ≤ y n :=
      Nat.floor_le (Scale.y_pos (Nat.zero_lt_of_lt hn)).le
    have hy : 1 < y n := by
      rw [← Real.log_pos_iff (Scale.y_pos (Nat.zero_lt_of_lt hn)).le]
      rw [Scale.log_y (Nat.zero_lt_of_lt hn)]
      exact mul_pos (by norm_num) (Real.log_pos (by exact_mod_cast hn))
    have hmono := fullCutoff_monotone M hdelta hn
      (W_le_first_fullCutoff M S)
    have hFullTwo : 2 ≤ fullCutoff M n W m :=
      hWTwo.trans (hmono (Nat.zero_le m))
    have hFullY : (fullCutoff M n W m : ℝ) ≤ y n := by
      have hFullNat : fullCutoff M n W m ≤ yNat n := by
        rw [show m = M.cellCount + 1 by rfl, fullCutoff_last M
          (Nat.zero_lt_of_lt hn)]
      exact (by exact_mod_cast hFullNat :
        (fullCutoff M n W m : ℝ) ≤ (yNat n : ℝ)) |>.trans hfloor
    simp only [actualCutoffCoordinate, realLogCoordinate]
    exact (div_le_one (Real.log_pos hy)).2
      (Real.log_le_log (by exact_mod_cast
        (show 0 < fullCutoff M n W m by omega)) hFullY)
  have hbase : 0 ≤ actualCutoffCoordinate M n W 0 := by
    simp only [actualCutoffCoordinate, fullCutoff_zero, realLogCoordinate]
    exact div_nonneg (Real.log_nonneg (by exact_mod_cast
      (show 1 ≤ W by omega)))
      (Real.log_pos (by
        rw [← Real.log_pos_iff (Scale.y_pos
          (Nat.zero_lt_of_lt hn)).le]
        rw [Scale.log_y (Nat.zero_lt_of_lt hn)]
        exact mul_pos (by norm_num)
          (Real.log_pos (by exact_mod_cast hn)))).le
  linarith

include hIdealAnchorLower in
theorem canonicalPrefix_low_anchor_zero
    (l : M.prefixLow tau htau) :
    let IM := canonicalIntervalMeshOfAnchors M hdelta hn hW hWTwo S epsilon
      anchors hAnchors hInteriorLower hInteriorUpper
    let split := M.prefixSplitEquiv tau htau
    IM.anchor (split (.inl l)) = 0 := by
  dsimp only
  let IM := canonicalIntervalMeshOfAnchors M hdelta hn hW hWTwo S epsilon
    anchors hAnchors hInteriorLower hInteriorUpper
  let split := M.prefixSplitEquiv tau htau
  change IM.anchor (split (.inl l)) = 0
  unfold IntervalMesh.anchor
  rw [if_neg]
  intro hmem
  change (split (.inl l)) ∈
    anchors.map (positiveBandEmbedding M) at hmem
  rw [Finset.mem_map] at hmem
  obtain ⟨k, hk, heq⟩ := hmem
  have hjk := M.prefixIndex_le_of_tau_lt_lower htau
    (hIdealAnchorLower k hk)
  have hval := congrArg Fin.val heq
  change k.1 + 1 = l.1 at hval
  have hl : l.1 < M.prefixIndex tau htau + 1 := l.2
  omega

include hIdealAnchorLower in
theorem sum_canonicalPrefix_high_anchor_eq_all :
    let IM := canonicalIntervalMeshOfAnchors M hdelta hn hW hWTwo S epsilon
      anchors hAnchors hInteriorLower hInteriorUpper
    let split := M.prefixSplitEquiv tau htau
    (∑ k : M.prefixHigh tau htau, IM.splitHighAnchor split k) =
      ∑ i : Fin (M.cellCount + 1), IM.anchor i := by
  dsimp only
  let IM := canonicalIntervalMeshOfAnchors M hdelta hn hW hWTwo S epsilon
    anchors hAnchors hInteriorLower hInteriorUpper
  let split := M.prefixSplitEquiv tau htau
  change (∑ k : M.prefixHigh tau htau, IM.splitHighAnchor split k) =
    ∑ i : Fin (M.cellCount + 1), IM.anchor i
  have hsum := Equiv.sum_comp split IM.anchor
  rw [Fintype.sum_sum_type] at hsum
  have hlow : (∑ l : M.prefixLow tau htau,
      IM.anchor (split (.inl l))) = 0 := by
    apply Finset.sum_eq_zero
    intro l _hl
    exact canonicalPrefix_low_anchor_zero M hdelta hn hW hWTwo S htau
      anchors hAnchors hIdealAnchorLower hInteriorLower hInteriorUpper l
  unfold IntervalMesh.splitHighAnchor
  linarith

end LiteralGeometry

end Mesh
end Erdos390.Full.RegularMeshPrimeCutoffs

end

/- Source module: Erdos390.Full.CanonicalEndpointRawWeightDefectEventually -/
section


/-!
# Ordinary raw-weight convergence for canonical endpoint bands

The arithmetic raw gauge uses the exact finite weights `H_j alpha_j`.
The continuum gauge uses `harmonicMass_j * center_j`, which is exactly the
ordinary coordinate length of the endpoint cell.  This file compares those
two quantities without identifying either arithmetic factor separately with
its continuum analogue.
-/

open scoped BigOperators
open Filter Topology

noncomputable section

namespace Erdos390.Full.RegularMeshPrimeCutoffs

open ArithmeticModel ArithmeticBandGeometry RegularRelativeMesh
open KernelPrimeQuadrature MovingLowMomentQuadrature



namespace Mesh

/-- The total raw-weight defect tends to zero for every fixed permitted
mesh.  The cutoff is selected before both mesh parameters and the mesh; only
the eventual ambient threshold may depend on them.  The conclusion is
uniform in the proof objects defining the literal canonical partition. -/
theorem canonicalRawWeightDefectCutoff_eventually
    (W : ℕ) (hWcut : canonicalRawWeightDefectCutoff ≤ W)
    {delta eta : ℝ} (M : Mesh delta eta) (hdelta : 0 < delta)
    {e : ℝ} (he : 0 < e) :
    ∀ᶠ n : ℕ in atTop, ∀ (hn : 1 < n) (hWne : W ≠ 0)
      (S : ScaleSeparation M n W),
      let P := canonicalPartition M hdelta hn hWne S
      (∑ j : Fin (M.cellCount + 1),
        |P.mass j * P.center j - endpointContinuumMoment M n W j|) ≤ e := by
  let Cmoment : ℝ :=
    MovingLowMomentQuadrature.fullLogReciprocalSumUniformConstant
  let Xmoment : ℕ :=
    MovingLowMomentQuadrature.fullLogReciprocalSumUniformCutoff
  have hXmoment : Xmoment ≤ W :=
    (le_max_right 2 Xmoment).trans hWcut
  have hMoment : ∀ A Y : ℕ, Xmoment ≤ A → A ≤ Y →
      |PrimeSums.fullLogReciprocalSum Y -
        PrimeSums.fullLogReciprocalSum A -
        (Real.log (Y : ℝ) - Real.log (A : ℝ))| ≤
      2 * Cmoment / Real.log (A : ℝ) ^ 3 +
        Cmoment / (2 * Real.log (A : ℝ) ^ 2) := by
    intro A Y hA hAY
    simpa only [Cmoment, Xmoment] using
      MovingLowMomentQuadrature.fullLogReciprocalSumUniform_bound
        A Y hA hAY
  have hEach : ∀ j : Fin (M.cellCount + 1),
      Tendsto (fun n : ℕ ↦ endpointMomentError M Cmoment n W j)
        atTop (nhds 0) := by
    intro j
    refine Fin.cases ?_ (fun k ↦ ?_) j
    · simpa only [lowBand] using
        tendsto_low_endpointMomentError_zero M Cmoment W
    · simpa only [positiveBand] using
        tendsto_positive_endpointMomentError_zero M hdelta Cmoment W k
  have hSumT : Tendsto (fun n : ℕ ↦
      ∑ j : Fin (M.cellCount + 1), endpointMomentError M Cmoment n W j)
      atTop (nhds 0) := by
    have hsum := tendsto_finset_sum Finset.univ (fun j _hj ↦ hEach j)
    simpa only [Finset.sum_const_zero] using hsum
  have hSumSmall := hSumT.eventually (eventually_le_nhds he)
  filter_upwards [hSumSmall] with n hnSmall
  intro hn hWne S
  let P := canonicalPartition M hdelta hn hWne S
  calc
    (∑ j : Fin (M.cellCount + 1),
        |P.mass j * P.center j - endpointContinuumMoment M n W j|) ≤
        ∑ j : Fin (M.cellCount + 1), endpointMomentError M Cmoment n W j := by
      apply Finset.sum_le_sum
      intro j _hj
      exact abs_canonical_mass_mul_center_sub_endpointContinuumMoment_le
        M hdelta hn hWne S hMoment hXmoment j
    _ ≤ e := hnSmall



end Mesh
end Erdos390.Full.RegularMeshPrimeCutoffs

end

/- Source module: Erdos390.Full.OrdinaryRawOperatorRowTransfer -/
section


/-!
# Entrywise transfer in ordinary raw row norm

This is the centre-free analogue of the sharp row aggregation lemma.  It
is deliberately stated for arbitrary finite matrices, so every later
endpoint attachment uses the same auditable deterministic estimate.
-/

open scoped BigOperators

noncomputable section

namespace Erdos390.Full.PaperWeightedInverseExport

variable {Band : Type*} [Fintype Band]

lemma rawOperator_sub
    (diagonalA diagonalC : Band → ℝ)
    (kernelA kernelC : Band → Band → ℝ)
    (b : Band → ℝ) (i : Band) :
    rawOperator diagonalA kernelA b i -
        rawOperator diagonalC kernelC b i =
      (diagonalA i - diagonalC i) * b i +
        ∑ j, (kernelA i j - kernelC i j) * b j := by
  unfold rawOperator
  rw [show diagonalA i * b i + (∑ j, kernelA i j * b j) -
      (diagonalC i * b i + ∑ j, kernelC i j * b j) =
    (diagonalA i - diagonalC i) * b i +
      ((∑ j, kernelA i j * b j) - ∑ j, kernelC i j * b j) by ring]
  rw [← Finset.sum_sub_distrib]
  apply congrArg (fun x : ℝ ↦ (diagonalA i - diagonalC i) * b i + x)
  apply Finset.sum_congr rfl
  intro j _hj
  ring

/-- Entrywise diagonal and kernel errors aggregate in raw sup norm with no
centre ratio and no factor depending on the number of cells. -/
theorem abs_rawOperator_sub_le
    (diagonalA diagonalC diagonalError : Band → ℝ)
    (kernelA kernelC kernelError : Band → Band → ℝ)
    (b : Band → ℝ)
    (hDiagonal : ∀ i,
      |diagonalA i - diagonalC i| ≤ diagonalError i)
    (hKernel : ∀ i j,
      |kernelA i j - kernelC i j| ≤ kernelError i j)
    (i : Band) :
    |rawOperator diagonalA kernelA b i -
        rawOperator diagonalC kernelC b i| ≤
      (diagonalError i + ∑ j, kernelError i j) * ‖b‖ := by
  rw [rawOperator_sub]
  calc
    |(diagonalA i - diagonalC i) * b i +
        ∑ j, (kernelA i j - kernelC i j) * b j| ≤
      |(diagonalA i - diagonalC i) * b i| +
        ∑ j, |(kernelA i j - kernelC i j) * b j| := by
          exact (abs_add_le _ _).trans
            (add_le_add le_rfl (Finset.abs_sum_le_sum_abs _ _))
    _ ≤ diagonalError i * ‖b‖ +
        ∑ j, kernelError i j * ‖b‖ := by
      apply add_le_add
      · rw [abs_mul]
        exact mul_le_mul (hDiagonal i)
          (by simpa only [Real.norm_eq_abs] using norm_le_pi_norm b i)
          (abs_nonneg _) ((abs_nonneg _).trans (hDiagonal i))
      · apply Finset.sum_le_sum
        intro j _hj
        rw [abs_mul]
        exact mul_le_mul (hKernel i j)
          (by simpa only [Real.norm_eq_abs] using norm_le_pi_norm b j)
          (abs_nonneg _) ((abs_nonneg _).trans (hKernel i j))
    _ = (diagonalError i + ∑ j, kernelError i j) * ‖b‖ := by
      rw [← Finset.sum_mul]
      ring

end Erdos390.Full.PaperWeightedInverseExport

end

/- Source module: Erdos390.Full.CanonicalEndpointOrdinaryRawRowEventually -/
section


/-!
# Canonical arithmetic/continuum transfer in ordinary raw row norm

The global PNT cutoff is chosen before both mesh parameters and before the
mesh.  The only fixed-cutoff remainder is `CRow / log(W)^3`; all other row
errors are absorbed by the later eventual threshold in `n`.
-/

open scoped BigOperators
open Filter

noncomputable section

namespace Erdos390.Full.RegularMeshPrimeCutoffs

open ArithmeticModel RegularRelativeMesh
open CompressedArithmeticOperator PaperWeightedInverseExport

namespace Mesh

/-- Literal paper-order ordinary raw row transfer for the canonical endpoint
matrix.  The estimate applies to every coefficient vector, not merely to a
gauge subspace. -/
theorem exists_cutoff_before_mesh_eventually_canonical_ordinaryRawRowError :
    ∃ CRow : ℝ, 0 < CRow ∧ ∃ W₀ : ℕ,
      ∀ {delta eta : ℝ} (M : Mesh delta eta), 0 < delta →
      ∀ W : ℕ, W₀ ≤ W → ∀ e : ℝ, 0 < e →
        ∀ᶠ n : ℕ in atTop,
          ∃ _hW : W ≠ 0, ∃ _hn : 1 < n,
            ∃ _S : ScaleSeparation M n W,
              ∀ b : Fin (M.cellCount + 1) → ℝ,
              ∀ i : Fin (M.cellCount + 1),
                |rawOperator
                    (arithmeticDiagonal (y n)
                      (fun j ↦ fullCutoff M n W j.1)
                      (fun j ↦ fullCutoff M n W (j.1 + 1)))
                    (arithmeticKernel (y n)
                      (fun j ↦ fullCutoff M n W j.1)
                      (fun j ↦ fullCutoff M n W (j.1 + 1))) b i -
                  rawOperator
                    (continuumDiagonal (y n)
                      (fun j ↦ fullCutoff M n W j.1)
                      (fun j ↦ fullCutoff M n W (j.1 + 1)))
                    (continuumKernel (y n)
                      (fun j ↦ fullCutoff M n W j.1)
                      (fun j ↦ fullCutoff M n W (j.1 + 1))) b i| ≤
                    (CRow / Real.log (W : ℝ) ^ 3 + e) * ‖b‖ := by
  obtain ⟨CRow, hCRow, WKernel, hKernel⟩ :=
    exists_cutoff_eventually_canonical_doubleKernelOrdinaryRowError
  obtain ⟨WDiagonal, hDiagonal⟩ :=
    exists_global_cutoff_eventually_canonical_diagonalError
  let W₀ : ℕ := max WKernel WDiagonal
  refine ⟨CRow, hCRow, W₀, ?_⟩
  intro delta eta M hdelta W hW e he
  have hWKernel : WKernel ≤ W :=
    (le_max_left WKernel WDiagonal).trans hW
  have hWDiagonal : WDiagonal ≤ W :=
    (le_max_right WKernel WDiagonal).trans hW
  have hKernelN := hKernel M hdelta W hWKernel (e / 2) (half_pos he)
  have hDiagonalN := hDiagonal M hdelta W hWDiagonal (e / 2) (half_pos he)
  filter_upwards [hKernelN, hDiagonalN] with n hKernelAt hDiagonalAt
  obtain ⟨hWne, hn, S, hKernelRows⟩ := hKernelAt
  refine ⟨hWne, hn, S, ?_⟩
  intro b i
  have hDiagonalEntry (r : Fin (M.cellCount + 1)) :
      |arithmeticDiagonal (y n)
          (fun j ↦ fullCutoff M n W j.1)
          (fun j ↦ fullCutoff M n W (j.1 + 1)) r -
        continuumDiagonal (y n)
          (fun j ↦ fullCutoff M n W j.1)
          (fun j ↦ fullCutoff M n W (j.1 + 1)) r| ≤
        endpointDiagonalError M n W r := le_rfl
  have hKernelEntry (r s : Fin (M.cellCount + 1)) :
      |arithmeticKernel (y n)
          (fun j ↦ fullCutoff M n W j.1)
          (fun j ↦ fullCutoff M n W (j.1 + 1)) r s -
        continuumKernel (y n)
          (fun j ↦ fullCutoff M n W j.1)
          (fun j ↦ fullCutoff M n W (j.1 + 1)) r s| ≤
        endpointDoubleKernelError M n W r s := le_rfl
  have hRaw := abs_rawOperator_sub_le
    (arithmeticDiagonal (y n)
      (fun j ↦ fullCutoff M n W j.1)
      (fun j ↦ fullCutoff M n W (j.1 + 1)))
    (continuumDiagonal (y n)
      (fun j ↦ fullCutoff M n W j.1)
      (fun j ↦ fullCutoff M n W (j.1 + 1)))
    (endpointDiagonalError M n W)
    (arithmeticKernel (y n)
      (fun j ↦ fullCutoff M n W j.1)
      (fun j ↦ fullCutoff M n W (j.1 + 1)))
    (continuumKernel (y n)
      (fun j ↦ fullCutoff M n W j.1)
      (fun j ↦ fullCutoff M n W (j.1 + 1)))
    (endpointDoubleKernelError M n W) b
    hDiagonalEntry hKernelEntry i
  calc
    |rawOperator
          (arithmeticDiagonal (y n)
            (fun j ↦ fullCutoff M n W j.1)
            (fun j ↦ fullCutoff M n W (j.1 + 1)))
          (arithmeticKernel (y n)
            (fun j ↦ fullCutoff M n W j.1)
            (fun j ↦ fullCutoff M n W (j.1 + 1))) b i -
        rawOperator
          (continuumDiagonal (y n)
            (fun j ↦ fullCutoff M n W j.1)
            (fun j ↦ fullCutoff M n W (j.1 + 1)))
          (continuumKernel (y n)
            (fun j ↦ fullCutoff M n W j.1)
            (fun j ↦ fullCutoff M n W (j.1 + 1))) b i| ≤
      (endpointDiagonalError M n W i +
        ∑ j, endpointDoubleKernelError M n W i j) * ‖b‖ := hRaw
    _ ≤ (CRow / Real.log (W : ℝ) ^ 3 + e) * ‖b‖ := by
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg b)
      have hDiag := hDiagonalAt i
      have hKer := hKernelRows i
      linarith

end Mesh
end Erdos390.Full.RegularMeshPrimeCutoffs

end

/- Source module: Erdos390.Full.CanonicalEndpointOrdinaryProjectedRawInverseEventually -/
section


/-!
# Mesh-uniform ordinary inverse for the canonical endpoint operator

This is the arithmetic conclusion of the moving-low-cell transfer.  All
structural constants, the mesh tolerance, and the prime cutoff are selected
before the two independent mesh parameters.  For each permitted mesh only
the eventual ambient threshold is allowed to vary.
-/

open scoped BigOperators NNReal
open Filter Topology Set

noncomputable section

namespace Erdos390.Full.RegularMeshPrimeCutoffs

open ArithmeticModel ArithmeticBandGeometry RegularRelativeMesh
open KernelPrimeQuadrature DoubleKernelPrimeQuadrature
open ContinuumCellGraph ContinuumCellGraph.IntervalMesh
open ContinuumCellGraph.ArithmeticGaugeOrdinary
open CompressedArithmeticOperator MovingLowGaugeTransfer
open PaperWeightedInverseExport PoissonDickmanWeightedInverse
open PoissonDickmanKernelBounds PrimeSums
open PaperBridgeFit.PaperActualSlowRightRowFinite

namespace Mesh



set_option maxHeartbeats 4000000 in
/-- Canonical endpoint arithmetic operator, inverted in the ordinary raw
sup norm.  The hypothesis uses the actual relative-mesh scale
`delta + M.ratio`; a paper-facing `delta + eta` wrapper follows by
`M.ratio_le_eta`. -/
theorem exists_fineMesh_cutoff_eventually_canonical_ordinaryProjectedRaw_inverse :
    ∃ Cref : ℝ, 0 < Cref ∧
      ∃ meshTol : ℝ, 0 < meshTol ∧
      ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W →
      ∀ {delta eta : ℝ} (M : Mesh delta eta) (hdelta : 0 < delta),
      delta + M.ratio ≤ meshTol →
      ∀ᶠ n : ℕ in atTop,
        ∃ hWne : W ≠ 0, ∃ hn : 1 < n,
          ∃ S : ScaleSeparation M n W,
            let P := canonicalPartition M hdelta hn hWne S
            let E := canonicalCertificate M hdelta hn hWne S
            ∀ q : RawGaugeSpace P.mass P.center,
              ‖q‖ ≤ Cref *
                ‖projectedRawLinearMap
                  (arithmeticDiagonal (y n) E.lower E.upper)
                  (arithmeticKernel (y n) E.lower E.upper)
                  P.mass P.center
                  (by
                    rw [sharpWeightTotal_partition_eq_centerEnergy P]
                    exact (P.centerEnergy_pos hn).ne') q‖ := by
  obtain ⟨kappa, hkappa, hgap⟩ :=
    exists_transposeQuotient_uniform_gap
      (by norm_num : (0 : ℝ) < 1 / 8)
      (by norm_num : (1 : ℝ) / 8 < 1 / 2)
  obtain ⟨C, hCpos, hKernelProduct⟩ := DickmanBasic.kernel_product_bound
  obtain ⟨CF, hCFpos, hFLipschitz⟩ := exists_F_lipschitz_unit
  obtain ⟨Cquot, hCquot, hQuotient⟩ :=
    exists_covarianceKernelQuotient_bound
  let R : ℝ := 128 * Real.log 4
  have hR : 0 ≤ R := by dsimp only [R]; positivity
  let Kabs : ℝ := 144 * C / kappa + 384 * C + 192
  have hKabs : 0 < Kabs := by
    dsimp only [Kabs]
    positivity
  let tau : ℝ := min (1 / 64)
    (min (1 / (16 * (CF + 1))) (1 / (8 * (Kabs + 1))))
  have htau : 0 < tau := by
    dsimp only [tau]
    positivity
  have htauOne : tau ≤ 1 := by
    exact (min_le_left _ _).trans (by norm_num)
  have htau64 : tau ≤ 1 / 64 := min_le_left _ _
  have htauCF : tau ≤ 1 / (16 * (CF + 1)) :=
    (min_le_right _ _).trans (min_le_left _ _)
  have htauAbs : tau ≤ 1 / (8 * (Kabs + 1)) :=
    (min_le_right _ _).trans (min_le_right _ _)
  have hKabsTau : Kabs * tau ≤ 1 / 8 := by
    have hKplus : 0 < Kabs + 1 := by linarith
    calc
      Kabs * tau ≤ Kabs * (1 / (8 * (Kabs + 1))) :=
        mul_le_mul_of_nonneg_left htauAbs hKabs.le
      _ = (1 / 8) * (Kabs / (Kabs + 1)) := by
        field_simp [ne_of_gt hKplus]
      _ ≤ (1 / 8) * 1 := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        exact (div_le_one hKplus).2 (by linarith)
      _ = 1 / 8 := by ring
  let gaugeRatio : ℝ := 96
  let CmainBound : ℝ := max 2
    (16 / kappa * (2 / tau + 4 * C * tau) + gaugeRatio * 2)
  have hCmainBound : 0 < CmainBound :=
    (by norm_num : (0 : ℝ) < 2) |>.trans_le (le_max_left _ _)
  have hOneR : 0 < 1 + R := by linarith
  let errorTarget : ℝ := 1 / (32 * CmainBound * (1 + R))
  have hErrorTarget : 0 < errorTarget := by
    dsimp only [errorTarget]
    positivity
  let residualTarget : ℝ := min tau errorTarget
  have hResidualTarget : 0 < residualTarget :=
    lt_min htau hErrorTarget
  have hResidualTau : residualTarget ≤ tau := min_le_left _ _
  have hResidualError : residualTarget ≤ errorTarget := min_le_right _ _
  let weightTarget : ℝ := min (1 / 256) (tau / 32)
  have hWeightTarget : 0 < weightTarget := by
    dsimp only [weightTarget]
    positivity
  have hWeight256 : weightTarget ≤ 1 / 256 := min_le_left _ _
  have hWeightTau : weightTarget ≤ tau / 32 := min_le_right _ _
  obtain ⟨continuumMeshTol, hContinuumMeshTol, hFmod, hKmod⟩ :=
    exists_uniform_cell_oscillation_modulus
      (div_pos hResidualTarget (by norm_num : (0 : ℝ) < 10))
      (div_pos hResidualTarget (by norm_num : (0 : ℝ) < 10))
  let meshTol : ℝ := min (tau / 2)
    (min (1 / 16) continuumMeshTol)
  have hmeshTol : 0 < meshTol := by
    dsimp only [meshTol]
    positivity
  obtain ⟨CRow, hCRow, Wrow, hRowEvent⟩ :=
    exists_cutoff_before_mesh_eventually_canonical_ordinaryRawRowError
  have hFixedTerm : Tendsto (fun W : ℕ ↦
      CRow / Real.log (W : ℝ) ^ 3) atTop (nhds 0) := by
    have hLog : Tendsto (fun W : ℕ ↦ Real.log (W : ℝ)) atTop atTop :=
      Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
    have hInv := tendsto_inv_atTop_zero.comp hLog
    have h := (tendsto_const_nhds : Tendsto (fun _W : ℕ ↦ CRow)
      atTop (nhds CRow)).mul (hInv.pow 3)
    simpa only [Function.comp_apply, mul_zero,
      zero_pow (by norm_num : 3 ≠ 0), div_eq_mul_inv, inv_pow] using h
  obtain ⟨Wfixed, hWfixed⟩ := eventually_atTop.1
    (hFixedTerm.eventually
      (eventually_le_nhds (half_pos hErrorTarget)))
  let W₀ : ℕ := max 2 (max Wrow (max Wfixed
    (max canonicalRawWeightDefectCutoff canonicalPrimeAnchorCutoff)))
  let Cref : ℝ := 8 * CmainBound
  have hCref : 0 < Cref := by dsimp only [Cref]; positivity
  refine ⟨Cref, hCref, meshTol, hmeshTol, W₀, ?_⟩
  intro W hW delta eta M hdelta hfine
  have hWTwo : 2 ≤ W := (le_max_left 2 _).trans hW
  have hWne : W ≠ 0 := by omega
  have hWrow : Wrow ≤ W := by
    exact ((le_max_left Wrow _).trans (le_max_right 2 _)).trans hW
  have hWfixed' : Wfixed ≤ W := by
    exact ((le_max_left Wfixed _).trans (le_max_right Wrow _)).trans
      ((le_max_right 2 _).trans hW)
  have hWweight : canonicalRawWeightDefectCutoff ≤ W := by
    exact ((le_max_left canonicalRawWeightDefectCutoff
      canonicalPrimeAnchorCutoff).trans (le_max_right Wfixed _)).trans
        ((le_max_right Wrow _).trans ((le_max_right 2 _).trans hW))
  have hWanchor : canonicalPrimeAnchorCutoff ≤ W := by
    exact ((le_max_right canonicalRawWeightDefectCutoff
      canonicalPrimeAnchorCutoff).trans (le_max_right Wfixed _)).trans
        ((le_max_right Wrow _).trans ((le_max_right 2 _).trans hW))
  have hdeltaMesh : delta < meshTol := by
    linarith [M.ratio_pos]
  have hratioMesh : M.ratio < meshTol := by
    linarith [hdelta]
  have hdeltaTau : delta < tau :=
    hdeltaMesh.trans_le ((min_le_left _ _).trans (by linarith))
  have hratioTau : M.ratio ≤ tau / 2 :=
    hratioMesh.le.trans (min_le_left _ _)
  have hdeltaSmall : delta < (1 / 16 : ℝ) :=
    hdeltaMesh.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hwidthSmall : ∀ k : Fin M.cellCount,
      M.width k < (1 / 16 : ℝ) := by
    intro k
    exact (M.width_le_ratio hdelta k).trans_lt
      (hratioMesh.trans_le ((min_le_right _ _).trans (min_le_left _ _)))
  have hLengthFineLow : delta < continuumMeshTol :=
    hdeltaMesh.trans_le
      ((min_le_right _ _).trans (min_le_right _ _))
  have hLengthFinePositive : ∀ k : Fin M.cellCount,
      M.width k < continuumMeshTol := by
    intro k
    exact (M.width_le_ratio hdelta k).trans_lt
      (hratioMesh.trans_le
        ((min_le_right _ _).trans (min_le_right _ _)))
  obtain ⟨anchors, anchor, hAnchor, hIdealLower,
      hIdealUpper, hIdealMass⟩ :=
    M.exists_interiorAnchorBlock hdelta hdeltaSmall hwidthSmall
  have hAnchors : anchors.Nonempty := ⟨anchor, hAnchor⟩
  have hIdealAboveTau : ∀ k ∈ anchors, tau < M.lower k := by
    intro k hk
    exact htau64.trans_lt (by
      have hkLower := hIdealLower k hk
      norm_num at hkLower ⊢
      linarith)
  have hTauRatioSmall : tau + M.ratio < 1 := by
    calc
      tau + M.ratio ≤ tau + tau / 2 := add_le_add le_rfl hratioTau
      _ ≤ (1 / 64 : ℝ) + 1 / 128 := by linarith
      _ < 1 := by norm_num
  letI : Nonempty (M.prefixHigh tau htauOne) :=
    M.prefixHigh_nonempty hdelta htauOne hTauRatioSmall
  have hFixedSmall : CRow / Real.log (W : ℝ) ^ 3 ≤ errorTarget / 2 :=
    hWfixed W hWfixed'
  have hRowN := hRowEvent M hdelta W hWrow
    (errorTarget / 2) (half_pos hErrorTarget)
  have hWeightN := canonicalRawWeightDefectCutoff_eventually
    W hWweight M hdelta hWeightTarget
  have hCoverageN := eventually_canonical_anchorBlock_coverage M hdelta
    hWne hWTwo anchors hAnchors hIdealLower hIdealUpper hIdealMass
  have hPrimeAnchorN := canonicalPrimeAnchorCutoff_eventually M hdelta
    W hWanchor anchors hAnchors hIdealLower hIdealUpper hIdealMass
  have hBoundaryN := eventually_canonicalPrefixBoundary_between M hdelta
    htauOne hdeltaTau hratioTau W
  have hLengthN := eventually_all_actualCoordinateLengths_lt M hdelta
    hLengthFineLow hLengthFinePositive W
  let beta : ℝ := residualTarget / (5 * (Cquot + 1))
  have hbeta : 0 < beta := by
    dsimp only [beta]
    positivity
  have hTailN := eventually_canonical_twoTails_lt M W hbeta
  have hBandTN := eventually_bandTReciprocalSum_le W
  filter_upwards [hRowN, hWeightN, hCoverageN, hPrimeAnchorN,
    hBoundaryN, hLengthN, hTailN, hBandTN] with n hRowAt hWeightAt
      hCoverageAt hPrimeAnchorAt hBoundaryAt hLengthAt hTailAt hBandTAt
  obtain ⟨hWr, hnr, S, hRows⟩ := hRowAt
  obtain ⟨hnc, hCoverageAll⟩ := hCoverageAt
  obtain ⟨hWa, hna, hPrimeAnchorAll⟩ := hPrimeAnchorAt
  obtain ⟨hInteriorLowerRaw, hInteriorUpperRaw, hAnchorMassRaw⟩ :=
    hCoverageAll S
  let hInteriorLower : ∀ k ∈ anchors, (1 / 8 : ℝ) ≤
      realLogCoordinate (y n)
        ((canonicalCertificate M hdelta hnr hWr S).lower
          (positiveBand M k) : ℝ) := hInteriorLowerRaw
  let hInteriorUpper : ∀ k ∈ anchors,
      realLogCoordinate (y n)
        ((canonicalCertificate M hdelta hnr hWr S).upper
          (positiveBand M k) : ℝ) ≤ 1 - (1 / 8 : ℝ) :=
    hInteriorUpperRaw
  let P := canonicalPartition M hdelta hnr hWr S
  let E := canonicalCertificate M hdelta hnr hWr S
  let IM := canonicalIntervalMeshOfAnchors M hdelta hnr hWr hWTwo S
    (1 / 8) anchors hAnchors hInteriorLower hInteriorUpper
  let split := M.prefixSplitEquiv tau htauOne
  let T := canonicalTwoTailCertificateOfAnchors M hdelta hnr hWr hWTwo S
    (1 / 8) anchors hAnchors anchor hAnchor hInteriorLower hInteriorUpper
  have hAnchorMass : (1 / 8 : ℝ) ≤ ∑ j, IM.anchor j := by
    simpa only [IM, Subsingleton.elim hnc hnr,
      Subsingleton.elim hWTwo hWTwo] using hAnchorMassRaw
  have hPrimeAnchor :
      let A := canonicalPrimeAnchorSet M P anchors
      (∀ p ∈ A, tPrime n p.1 ∈ Icc (1 / 8 : ℝ) (1 - 1 / 8)) ∧
        (1 / 8 : ℝ) ≤
          FiniteAnchoredDirichletQuadratic.anchorMass
            (PrimeSquarefreeDirichletGeometry.primeWeight n) A := by
    simpa only [P, Subsingleton.elim hna hnr,
      Subsingleton.elim hWa hWr] using hPrimeAnchorAll S
  have hRawDefect :
      (∑ j : Fin (M.cellCount + 1),
        |P.mass j * P.center j - endpointContinuumMoment M n W j|) ≤
          weightTarget := by
    simpa only [P, Subsingleton.elim hWr hWne] using
      hWeightAt hnr hWr S
  have hBoundaryLower : tau / 2 ≤
      canonicalPrefixBoundary M n W tau htauOne := hBoundaryAt.1
  have hBoundaryUpper :
      canonicalPrefixBoundary M n W tau htauOne ≤ 2 * tau :=
    hBoundaryAt.2
  have hLengths (j : Fin (M.cellCount + 1)) :
      IM.length j < continuumMeshTol := by
    simpa only [IM, canonicalIntervalMeshOfAnchors, IntervalMesh.length,
      actualCutoffCoordinate] using hLengthAt j
  have hBase : T.base < beta := by
    simpa only [T, canonicalTwoTailCertificateOfAnchors,
      canonicalTwoTailCertificate, actualCutoffCoordinate,
      fullCutoff_zero] using hTailAt.1
  have hTop : 1 - T.upperEnd < beta := by
    simpa only [T, canonicalTwoTailCertificateOfAnchors,
      canonicalTwoTailCertificate, actualCutoffCoordinate] using hTailAt.2
  have hResidual (i : Fin (M.cellCount + 1)) :
      |IM.rowResidual i| ≤ residualTarget := by
    exact (rowResidual_lt_of_global_modulus IM T hResidualTarget hCquot
      (fun s hs t ht ↦ hQuotient t ht s hs) hFmod hKmod rfl
      hBase hTop hLengths i).le
  have hContinuumWeight (j : Fin (M.cellCount + 1)) :
      IM.harmonicMass j * IM.center j =
        endpointContinuumMoment M n W j := by
    rw [IM.harmonicMass_mul_center_eq_length]
    simpa only [IM, canonicalIntervalMeshOfAnchors, IntervalMesh.length]
      using (endpointContinuumMoment_eq_coordinateLength
        (W := W) M hnr j).symm
  have hRawWeightDefect :
      (∑ j : Fin (M.cellCount + 1),
        |P.mass j * P.center j - IM.harmonicMass j * IM.center j|) ≤
          weightTarget := by
    simpa only [hContinuumWeight] using hRawDefect
  have hEnergy : (1 / 64 : ℝ) ≤ P.centerEnergy := by
    let A := canonicalPrimeAnchorSet M P anchors
    have hE := epsilon_mul_anchorMass_le_centerEnergy M P hnr
      (by norm_num : (0 : ℝ) ≤ 1 / 8) anchors hPrimeAnchor.1
    calc
      (1 / 64 : ℝ) = (1 / 8 : ℝ) * (1 / 8 : ℝ) := by norm_num
      _ ≤ (1 / 8 : ℝ) *
          FiniteAnchoredDirichletQuadratic.anchorMass
            (PrimeSquarefreeDirichletGeometry.primeWeight n) A := by
        exact mul_le_mul_of_nonneg_left hPrimeAnchor.2 (by norm_num)
      _ ≤ P.centerEnergy := hE
  have hMomentRatio :
      (1 : ℝ) * (∑ i, P.mass i * P.center i) ≤
        R * sharpWeightTotal P.mass P.center := by
    have htotal : (∑ i, P.mass i * P.center i) =
        bandTReciprocalSum n W := P.sum_mass_mul_center_eq_bandTReciprocalSum
    have henergyId : sharpWeightTotal P.mass P.center = P.centerEnergy := by
      exact sharpWeightTotal_partition_eq_centerEnergy P
    rw [one_mul, htotal, henergyId]
    calc
      bandTReciprocalSum n W ≤ 2 * Real.log 4 := hBandTAt
      _ = R * (1 / 64) := by dsimp only [R]; ring
      _ ≤ R * P.centerEnergy :=
        mul_le_mul_of_nonneg_left hEnergy hR
  have hLowCenter (l : M.prefixLow tau htauOne) :
      IM.center (split (.inl l)) ≤ 2 * tau := by
    exact (canonicalPrefix_low_center_le_boundary M hdelta hnr hWr
      hWTwo S htauOne anchors hAnchors hInteriorLower hInteriorUpper l).trans
        hBoundaryUpper
  have hHighCenterLower (k : M.prefixHigh tau htauOne) :
      tau / 2 ≤ IM.center (split (.inr k)) := by
    exact hBoundaryLower.trans
      (canonicalPrefix_boundary_le_high_center M hdelta hnr hWr
        hWTwo S htauOne anchors hAnchors hInteriorLower hInteriorUpper k)
  have hHighCenterUpper (k : M.prefixHigh tau htauOne) :
      IM.center (split (.inr k)) ≤ 1 :=
    (IM.center_le_upper _).trans (IM.upper_le_one _)
  have hLowLength :
      (∑ l : M.prefixLow tau htauOne, IM.length (split (.inl l))) ≤
        2 * tau := by
    exact (sum_canonicalPrefix_low_length_le_boundary M hdelta hnr hWr
      hWTwo S htauOne anchors hAnchors hInteriorLower hInteriorUpper).trans
        hBoundaryUpper
  have hTotalLength : (∑ i, IM.length i) ≤ 1 :=
    sum_canonical_all_length_le_one M hdelta hnr hWr hWTwo S
      anchors hAnchors hInteriorLower hInteriorUpper
  have hHighAnchor : (1 / 8 : ℝ) ≤
      ∑ k : M.prefixHigh tau htauOne, IM.splitHighAnchor split k := by
    rw [sum_canonicalPrefix_high_anchor_eq_all M hdelta hnr hWr hWTwo S
      htauOne anchors hAnchors hIdealAboveTau hInteriorLower hInteriorUpper]
    exact hAnchorMass
  have hDiagonalLow (l : M.prefixLow tau htauOne) :
      |IM.normalizedDiagonalCell (split (.inl l)) - 1| ≤ 1 / 4 := by
    apply IM.abs_normalizedDiagonalCell_sub_one_le
    intro s hs
    have hsUnit := IM.cell_mem_unit hs
    have hUpperBoundary : IM.upper (split (.inl l)) ≤
        canonicalPrefixBoundary M n W tau htauOne := by
      have hmono : Monotone (fullCutoff M n W) :=
        fullCutoff_monotone M hdelta hnr (W_le_first_fullCutoff M S)
      have hidx : (split (.inl l)).1 + 1 ≤
          M.prefixIndex tau htauOne + 1 := by
        change l.1 + 1 ≤ M.prefixIndex tau htauOne + 1
        have hl : l.1 < M.prefixIndex tau htauOne + 1 := l.2
        omega
      have hcut := hmono hidx
      have hy : 1 < y n := by
        rw [← Real.log_pos_iff (Scale.y_pos
          (Nat.zero_lt_of_lt hnr)).le]
        rw [Scale.log_y (Nat.zero_lt_of_lt hnr)]
        exact mul_pos (by norm_num)
          (Real.log_pos (by exact_mod_cast hnr))
      have hlowerTwo : 2 ≤ fullCutoff M n W ((split (.inl l)).1 + 1) :=
        hWTwo.trans (hmono (Nat.zero_le _))
      have hcoord := realLogCoordinate_mono_nat hy hlowerTwo hcut
      simpa only [IM, canonicalIntervalMeshOfAnchors_upper,
        canonicalCertificate_upper, canonicalPrefixBoundary,
        actualCutoffCoordinate] using hcoord
    have hsUpper' : s ≤ 2 * tau :=
      hs.2.trans (hUpperBoundary.trans hBoundaryUpper)
    have hLip := hFLipschitz s hsUnit 0 (by norm_num)
    simp only [DickmanBasic.F_zero] at hLip
    calc
      |DickmanBasic.F s - 1| ≤ CF * |s - 0| := hLip
      _ = CF * s := by rw [sub_zero, abs_of_nonneg hsUnit.1]
      _ ≤ CF * (2 * tau) :=
        mul_le_mul_of_nonneg_left hsUpper' hCFpos.le
      _ ≤ 1 / 4 := by
        have hCFtau : CF * tau ≤ 1 / 16 := by
          have hCFplus : 0 < CF + 1 := by linarith
          calc
            CF * tau ≤ CF * (1 / (16 * (CF + 1))) :=
              mul_le_mul_of_nonneg_left htauCF hCFpos.le
            _ = (1 / 16) * (CF / (CF + 1)) := by
              field_simp [ne_of_gt hCFplus]
            _ ≤ (1 / 16) * 1 := by
              apply mul_le_mul_of_nonneg_left _ (by norm_num)
              exact (div_le_one hCFplus).2 (by linarith)
            _ = 1 / 16 := by ring
        nlinarith only [hCFtau]
  have hRowError (q : RawGaugeSpace P.mass P.center)
      (i : Fin (M.cellCount + 1)) :
      |rawOperator (arithmeticDiagonal (y n) E.lower E.upper)
          (arithmeticKernel (y n) E.lower E.upper) q.1 i -
        rawOperator IM.normalizedDiagonalCell IM.normalizedKernelCell
          q.1 i| ≤ errorTarget * ‖q‖ := by
    have hraw := hRows q.1 i
    have hDiagId (j : Fin (M.cellCount + 1)) :
        IM.normalizedDiagonalCell j =
          continuumDiagonal (y n) E.lower E.upper j := by
      exact IM.normalizedDiagonalCell_eq_endpointContinuum
        (y n) E.lower E.upper (fun _ ↦ rfl) (fun _ ↦ rfl) j
    have hKernelId (j k : Fin (M.cellCount + 1)) :
        IM.normalizedKernelCell j k =
          continuumKernel (y n) E.lower E.upper j k := by
      exact IM.normalizedKernelCell_eq_endpointContinuum
        (y n) E.lower E.upper (fun _ ↦ rfl) (fun _ ↦ rfl) j k
    have hcoeff : CRow / Real.log (W : ℝ) ^ 3 + errorTarget / 2 ≤
        errorTarget := by linarith
    have hDiagFun : IM.normalizedDiagonalCell =
        continuumDiagonal (y n) E.lower E.upper := funext hDiagId
    have hKernelFun : IM.normalizedKernelCell =
        continuumKernel (y n) E.lower E.upper := by
      funext j k
      exact hKernelId j k
    rw [hDiagFun, hKernelFun]
    simpa only [E, canonicalCertificate_lower, canonicalCertificate_upper]
      using hraw.trans
        (mul_le_mul_of_nonneg_right hcoeff (norm_nonneg q.1))
  -- The remaining inequalities are finite arithmetic consequences of the
  -- preceding literal bounds.
  have hAlphaUpper (i : Fin (M.cellCount + 1)) : P.center i ≤ 1 :=
    (P.center_mem_zero_one hnr i).2
  have hLowArithmetic :
      (∑ l : M.prefixLow tau htauOne,
        P.mass (split (.inl l)) * P.center (split (.inl l))) ≤
        3 * tau := by
    have hdefLow :
        (∑ l : M.prefixLow tau htauOne,
          |P.mass (split (.inl l)) * P.center (split (.inl l)) -
            IM.length (split (.inl l))|) ≤ weightTarget := by
      calc
        _ ≤ ∑ j : Fin (M.cellCount + 1),
            |P.mass j * P.center j - IM.length j| := by
          rw [← Equiv.sum_comp split]
          rw [Fintype.sum_sum_type]
          exact le_add_of_nonneg_right
            (Finset.sum_nonneg fun _ _ ↦ abs_nonneg _)
        _ = ∑ j : Fin (M.cellCount + 1),
            |P.mass j * P.center j -
              IM.harmonicMass j * IM.center j| := by
          apply Finset.sum_congr rfl
          intro j _hj
          rw [IM.harmonicMass_mul_center_eq_length]
        _ ≤ weightTarget := hRawWeightDefect
    have hsum :
        (∑ l : M.prefixLow tau htauOne,
          P.mass (split (.inl l)) * P.center (split (.inl l))) ≤
          (∑ l : M.prefixLow tau htauOne,
            IM.length (split (.inl l))) + weightTarget := by
      calc
        _ ≤ ∑ l : M.prefixLow tau htauOne,
            (IM.length (split (.inl l)) +
              |P.mass (split (.inl l)) * P.center (split (.inl l)) -
                IM.length (split (.inl l))|) := by
          apply Finset.sum_le_sum
          intro l _hl
          linarith [le_abs_self
            (P.mass (split (.inl l)) * P.center (split (.inl l)) -
              IM.length (split (.inl l)))]
        _ = (∑ l : M.prefixLow tau htauOne,
              IM.length (split (.inl l))) +
            ∑ l : M.prefixLow tau htauOne,
              |P.mass (split (.inl l)) * P.center (split (.inl l)) -
                IM.length (split (.inl l))| := Finset.sum_add_distrib
        _ ≤ (∑ l : M.prefixLow tau htauOne,
              IM.length (split (.inl l))) + weightTarget :=
          add_le_add le_rfl hdefLow
    exact hsum.trans (by linarith [hLowLength, hWeightTau, htau])
  have hHighMixed : tau / 32 ≤
      ∑ k : M.prefixHigh tau htauOne,
        P.mass (split (.inr k)) * P.center (split (.inr k)) *
          IM.center (split (.inr k)) := by
    have hContinuumHigh : tau / 16 ≤
        ∑ k : M.prefixHigh tau htauOne,
          IM.length (split (.inr k)) * IM.center (split (.inr k)) := by
      have hsharp := IM.amin_mul_highAnchor_le_highSharpWeight split
        (show 0 ≤ tau / 2 by positivity) hHighCenterLower
      calc
        tau / 16 = (tau / 2) * (1 / 8) := by ring
        _ ≤ (tau / 2) *
            (∑ k : M.prefixHigh tau htauOne,
              IM.splitHighAnchor split k) :=
          mul_le_mul_of_nonneg_left hHighAnchor (by positivity)
        _ ≤ ∑ k : M.prefixHigh tau htauOne,
            IM.harmonicMass (split (.inr k)) *
              IM.center (split (.inr k)) ^ 2 := hsharp
        _ = ∑ k : M.prefixHigh tau htauOne,
            IM.length (split (.inr k)) * IM.center (split (.inr k)) := by
          apply Finset.sum_congr rfl
          intro k _hk
          exact IM.harmonicMass_mul_center_sq_eq (split (.inr k))
    have hdefHigh :
        |(∑ k : M.prefixHigh tau htauOne,
            P.mass (split (.inr k)) * P.center (split (.inr k)) *
              IM.center (split (.inr k))) -
          ∑ k : M.prefixHigh tau htauOne,
            IM.length (split (.inr k)) * IM.center (split (.inr k))| ≤
          weightTarget := by
      rw [← Finset.sum_sub_distrib]
      calc
        |∑ k : M.prefixHigh tau htauOne,
            (P.mass (split (.inr k)) * P.center (split (.inr k)) *
                IM.center (split (.inr k)) -
              IM.length (split (.inr k)) * IM.center (split (.inr k)))| ≤
            ∑ k : M.prefixHigh tau htauOne,
              |P.mass (split (.inr k)) * P.center (split (.inr k)) -
                IM.length (split (.inr k))| := by
          calc
            _ ≤ ∑ k : M.prefixHigh tau htauOne,
                |P.mass (split (.inr k)) * P.center (split (.inr k)) -
                  IM.length (split (.inr k))| *
                    |IM.center (split (.inr k))| := by
              calc
                _ ≤ ∑ k : M.prefixHigh tau htauOne,
                    |P.mass (split (.inr k)) * P.center (split (.inr k)) *
                        IM.center (split (.inr k)) -
                      IM.length (split (.inr k)) *
                        IM.center (split (.inr k))| :=
                  Finset.abs_sum_le_sum_abs _ _
                _ = _ := by
                  apply Finset.sum_congr rfl
                  intro k _hk
                  rw [show
                    P.mass (split (.inr k)) * P.center (split (.inr k)) *
                        IM.center (split (.inr k)) -
                      IM.length (split (.inr k)) * IM.center (split (.inr k)) =
                        (P.mass (split (.inr k)) *
                          P.center (split (.inr k)) -
                          IM.length (split (.inr k))) *
                            IM.center (split (.inr k)) by ring,
                    abs_mul]
            _ ≤ _ := by
              apply Finset.sum_le_sum
              intro k _hk
              rw [abs_of_pos (IM.center_pos _)]
              simpa only [mul_one] using
                (mul_le_mul_of_nonneg_left (hHighCenterUpper k)
                  (abs_nonneg
                    (P.mass (split (.inr k)) * P.center (split (.inr k)) -
                      IM.length (split (.inr k)))))
        _ ≤ ∑ j : Fin (M.cellCount + 1),
            |P.mass j * P.center j - IM.length j| := by
          rw [← Equiv.sum_comp split, Fintype.sum_sum_type]
          exact le_add_of_nonneg_left
            (Finset.sum_nonneg fun _ _ ↦ abs_nonneg _)
        _ = ∑ j : Fin (M.cellCount + 1),
            |P.mass j * P.center j -
              IM.harmonicMass j * IM.center j| := by
          apply Finset.sum_congr rfl
          intro j _hj
          rw [IM.harmonicMass_mul_center_eq_length]
        _ ≤ weightTarget := hRawWeightDefect
    have hleft := neg_le_of_abs_le hdefHigh
    linarith [hContinuumHigh, hWeightTau]
  have hMixedGauge :
      (∑ l : M.prefixLow tau htauOne,
        P.mass (split (.inl l)) * P.center (split (.inl l))) ≤
        gaugeRatio *
          (∑ k : M.prefixHigh tau htauOne,
            P.mass (split (.inr k)) * P.center (split (.inr k)) *
              IM.center (split (.inr k))) := by
    dsimp only [gaugeRatio]
    nlinarith only [hLowArithmetic, hHighMixed]
  have hEpsLowBound :
      (residualTarget + C * (2 * tau) * 1) / (1 - (1 / 4 : ℝ)) ≤
        (4 * C + 2) * tau := by
    have hres := hResidualTau
    have hnonneg : 0 ≤ C * tau := mul_nonneg hCpos.le htau.le
    field_simp
    nlinarith only [hres, hnonneg, htau]
  have hEpsSmall :
      (residualTarget + C * (2 * tau) * 1) / (1 - (1 / 4 : ℝ)) ≤
        1 / 8 := by
    have hCoeff : 4 * C + 2 ≤ Kabs := by
      dsimp only [Kabs]
      have hdiv : 0 ≤ 144 * C / kappa := by positivity
      nlinarith only [hdiv, hCpos]
    exact hEpsLowBound.trans
      ((mul_le_mul_of_nonneg_right hCoeff htau.le).trans hKabsTau)
  have hInvAnchor : 1 / (kappa * ∑ k : M.prefixHigh tau htauOne,
      IM.splitHighAnchor split k) ≤ 8 / kappa := by
    have hsumPos : 0 < ∑ k : M.prefixHigh tau htauOne,
        IM.splitHighAnchor split k := (by norm_num : (0 : ℝ) < 1 / 8)
          |>.trans_le hHighAnchor
    apply (div_le_div_iff₀ (mul_pos hkappa hsumPos) hkappa).2
    have hmul := mul_le_mul_of_nonneg_left hHighAnchor hkappa.le
    nlinarith only [hmul]
  have hAbsorbLow :
      let epsLow :=
        (residualTarget + C * (2 * tau) * 1) / (1 - (1 / 4 : ℝ))
      max epsLow
        (1 *
          (2 * (1 / (kappa *
              ∑ k : M.prefixHigh tau htauOne,
                IM.splitHighAnchor split k)) *
              ((C * (2 * tau) * (2 * tau)) / (tau / 2) +
                (C * (2 * tau)) * epsLow) +
            gaugeRatio * epsLow)) ≤ 1 / 2 := by
    dsimp only
    apply max_le
    · exact hEpsSmall.trans (by norm_num)
    · have htauNe : tau ≠ 0 := ne_of_gt htau
      have hfirst : (C * (2 * tau) * (2 * tau)) / (tau / 2) =
          8 * C * tau := by field_simp [htauNe]; ring
      rw [hfirst]
      have hInsideNonneg : 0 ≤
          8 * C * tau +
            C * (2 * tau) *
              ((residualTarget + C * (2 * tau) * 1) /
                (1 - (1 / 4 : ℝ))) := by positivity
      have hInside :
          8 * C * tau + C * (2 * tau) *
              ((residualTarget + C * (2 * tau) * 1) /
                (1 - (1 / 4 : ℝ))) ≤ 9 * C * tau := by
        have hmul :
            C * (2 * tau) *
                ((residualTarget + C * (2 * tau) * 1) /
                  (1 - (1 / 4 : ℝ))) ≤
              C * (2 * tau) * (1 / 8 : ℝ) := by
          exact mul_le_mul_of_nonneg_left hEpsSmall
            (mul_nonneg hCpos.le
              (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) htau.le))
        nlinarith only [hmul, mul_nonneg hCpos.le htau.le]
      have hinvMul :
          2 * (1 / (kappa *
              ∑ k : M.prefixHigh tau htauOne,
                IM.splitHighAnchor split k)) ≤ 16 / kappa := by
        calc
          _ ≤ 2 * (8 / kappa) :=
            mul_le_mul_of_nonneg_left hInvAnchor (by norm_num)
          _ = 16 / kappa := by ring
      have hfirstTerm :
          2 * (1 / (kappa *
              ∑ k : M.prefixHigh tau htauOne,
                IM.splitHighAnchor split k)) *
            (8 * C * tau + C * (2 * tau) *
              ((residualTarget + C * (2 * tau) * 1) /
                (1 - (1 / 4 : ℝ)))) ≤
          (144 * C / kappa) * tau := by
        calc
          _ ≤ (16 / kappa) * (9 * C * tau) :=
            mul_le_mul hinvMul hInside hInsideNonneg
              (by positivity)
          _ = (144 * C / kappa) * tau := by ring
      have hsecondTerm : gaugeRatio *
          ((residualTarget + C * (2 * tau) * 1) /
            (1 - (1 / 4 : ℝ))) ≤
          (384 * C + 192) * tau := by
        dsimp only [gaugeRatio]
        nlinarith only [hEpsLowBound]
      have htotal :
          2 * (1 / (kappa *
              ∑ k : M.prefixHigh tau htauOne,
                IM.splitHighAnchor split k)) *
              (8 * C * tau + C * (2 * tau) *
                ((residualTarget + C * (2 * tau) * 1) /
                  (1 - (1 / 4 : ℝ)))) +
            gaugeRatio *
              ((residualTarget + C * (2 * tau) * 1) /
                (1 - (1 / 4 : ℝ))) ≤ Kabs * tau := by
        dsimp only [Kabs]
        linarith
      norm_num only [gaugeRatio, one_mul] at htotal ⊢
      exact htotal.trans
        (hKabsTau.trans (by norm_num : (1 / 8 : ℝ) ≤ 1 / 2))
  have hClow : (1 / (1 - (1 / 4 : ℝ))) ≤ 2 := by norm_num
  have hCmainActual :
      max (1 / (1 - (1 / 4 : ℝ)))
        (1 *
          (2 * (1 / (kappa *
              ∑ k : M.prefixHigh tau htauOne,
                IM.splitHighAnchor split k)) *
              (1 / (tau / 2) +
                (C * (2 * tau)) * (1 / (1 - (1 / 4 : ℝ)))) +
            gaugeRatio * (1 / (1 - (1 / 4 : ℝ))))) ≤
        CmainBound := by
    apply max_le
    · exact hClow.trans (le_max_left _ _)
    · have htauNe : tau ≠ 0 := ne_of_gt htau
      have hInvTau : 1 / (tau / 2) = 2 / tau := by
        field_simp [htauNe]
      rw [hInvTau]
      have hInside :
          2 / tau + C * (2 * tau) * (1 / (1 - (1 / 4 : ℝ))) ≤
            2 / tau + 4 * C * tau := by
        norm_num at hClow
        nlinarith only [mul_nonneg hCpos.le htau.le]
      have hInsideNonneg : 0 ≤
          2 / tau + C * (2 * tau) * (1 / (1 - (1 / 4 : ℝ))) := by
        positivity
      have hfirst :
          2 * (1 / (kappa *
              ∑ k : M.prefixHigh tau htauOne,
                IM.splitHighAnchor split k)) *
            (2 / tau + C * (2 * tau) *
              (1 / (1 - (1 / 4 : ℝ)))) ≤
          16 / kappa * (2 / tau + 4 * C * tau) := by
        have hinvMul : 2 * (1 / (kappa *
            ∑ k : M.prefixHigh tau htauOne,
              IM.splitHighAnchor split k)) ≤ 16 / kappa := by
          calc
            _ ≤ 2 * (8 / kappa) :=
              mul_le_mul_of_nonneg_left hInvAnchor (by norm_num)
            _ = 16 / kappa := by ring
        exact mul_le_mul hinvMul hInside hInsideNonneg (by positivity)
      have hgauge : gaugeRatio * (1 / (1 - (1 / 4 : ℝ))) ≤
          gaugeRatio * 2 :=
        mul_le_mul_of_nonneg_left hClow (by dsimp only [gaugeRatio]; norm_num)
      calc
        1 *
            (2 * (1 / (kappa *
                ∑ k : M.prefixHigh tau htauOne,
                  IM.splitHighAnchor split k)) *
                (2 / tau + C * (2 * tau) *
                  (1 / (1 - (1 / 4 : ℝ)))) +
              gaugeRatio * (1 / (1 - (1 / 4 : ℝ)))) =
            2 * (1 / (kappa *
                ∑ k : M.prefixHigh tau htauOne,
                  IM.splitHighAnchor split k)) *
                (2 / tau + C * (2 * tau) *
                  (1 / (1 - (1 / 4 : ℝ)))) +
              gaugeRatio * (1 / (1 - (1 / 4 : ℝ))) := one_mul _
        _ ≤ 16 / kappa * (2 / tau + 4 * C * tau) +
            gaugeRatio * 2 := add_le_add hfirst hgauge
        _ ≤ CmainBound := by
          dsimp only [CmainBound]
          exact le_max_right _ _
  have hAbsorbArithmetic :
      let Clow := 1 / (1 - (1 / 4 : ℝ))
      let Cmain :=
        max Clow
          (1 *
            (2 * (1 / (kappa *
                ∑ k : M.prefixHigh tau htauOne,
                  IM.splitHighAnchor split k)) *
                (1 / (tau / 2) + (C * (2 * tau)) * Clow) +
              gaugeRatio * Clow))
      4 * Cmain * ((1 + R) * (errorTarget + residualTarget)) ≤ 1 / 2 := by
    dsimp only
    have hErrSum : errorTarget + residualTarget ≤ 2 * errorTarget := by
      linarith [hResidualError]
    have hnonneg : 0 ≤ (1 + R) * (errorTarget + residualTarget) := by
      positivity
    calc
      4 *
          max (1 / (1 - (1 / 4 : ℝ)))
            (1 *
              (2 * (1 / (kappa *
                  ∑ k : M.prefixHigh tau htauOne,
                    IM.splitHighAnchor split k)) *
                  (1 / (tau / 2) +
                    C * (2 * tau) * (1 / (1 - (1 / 4 : ℝ)))) +
                gaugeRatio * (1 / (1 - (1 / 4 : ℝ))))) *
            ((1 + R) * (errorTarget + residualTarget)) ≤
          4 * CmainBound * ((1 + R) * (2 * errorTarget)) := by
        gcongr
      _ = 1 / 4 := by
        dsimp only [errorTarget]
        field_simp [ne_of_gt hCmainBound, ne_of_gt hOneR]
        ring
      _ ≤ 1 / 2 := by norm_num
  have hRawDefectScaled :
      (1 : ℝ) *
          (∑ i, |P.mass i * P.center i -
            IM.harmonicMass i * IM.center i|) ≤
        (1 / 4 : ℝ) * sharpWeightTotal P.mass P.center := by
    rw [one_mul]
    have hweight :
        (∑ i, |P.mass i * P.center i -
          IM.harmonicMass i * IM.center i|) ≤ 1 / 256 :=
      hRawWeightDefect.trans hWeight256
    have henergyId : sharpWeightTotal P.mass P.center = P.centerEnergy := by
      exact sharpWeightTotal_partition_eq_centerEnergy P
    rw [henergyId]
    nlinarith only [hweight, hEnergy]
  have hBound :=
    ContinuumCellGraph.ArithmeticGaugeOrdinary.IntervalMesh.ordinary_split_arithmetic_projected_raw_bound
    IM split
    (arithmeticDiagonal (y n) E.lower E.upper)
    (arithmeticKernel (y n) E.lower E.upper)
    P.mass P.center
    hCpos.le hKernelProduct hkappa hgap
    ((by norm_num : (0 : ℝ) < 1 / 8).trans_le hHighAnchor)
    (div_pos htau (by norm_num)) hHighCenterLower hHighCenterUpper
    (by norm_num) (by positivity) hLowCenter (by positivity) hLowLength
    (by norm_num) hTotalLength P.data.mass_pos (P.center_pos hnr)
    hAlphaUpper hMixedGauge (by norm_num : (1 / 4 : ℝ) < 1)
    hDiagonalLow hResidualTarget.le hResidual hErrorTarget.le hRowError
    hR hMomentRatio (by norm_num : (1 / 4 : ℝ) ≤ 1 / 2)
    hRawDefectScaled hAbsorbLow hAbsorbArithmetic
  refine ⟨hWr, hnr, S, ?_⟩
  dsimp only
  intro q
  have hq := hBound q
  have hconstant :
      8 *
        max (1 / (1 - (1 / 4 : ℝ)))
          (1 *
            (2 * (1 / (kappa *
                ∑ k : M.prefixHigh tau htauOne,
                  IM.splitHighAnchor split k)) *
                (1 / (tau / 2) +
                  (C * (2 * tau)) * (1 / (1 - (1 / 4 : ℝ)))) +
              gaugeRatio * (1 / (1 - (1 / 4 : ℝ))))) ≤ Cref := by
    dsimp only [Cref]
    exact mul_le_mul_of_nonneg_left hCmainActual (by norm_num)
  exact hq.trans (mul_le_mul_of_nonneg_right hconstant (norm_nonneg _))



end Mesh
end Erdos390.Full.RegularMeshPrimeCutoffs

end

theorem solution : Erdos390.AnalyticCompactBatch006Goal001 := by
  exact @Erdos390.Full.RegularMeshPrimeCutoffs.Mesh.exists_fineMesh_cutoff_eventually_canonical_ordinaryProjectedRaw_inverse
