-- Prove2me | solution 1 for Erdos390.Full.RegularMeshPrimeCutoffs.Mesh.canonicalNonstepLocalDiagonalCutoff_eventually
-- status  : ACCEPTED   (prove)
-- author  : @doctosil
-- created : 2026-09-17T15:27:20.196178+00:00
-- url     : https://prove2.me/submissions/6076a80f-1a36-47b7-aff7-f7ddb2a6e176

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
import Theorems.Thm_Erdos390_Full_ArithmeticBandGeometry_Partition_normalizedDeviationReciprocalSquare_le_global_moments

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

private theorem inv_sq_le_telescope {k : ℕ} (hk : 2 ≤ k) :
    1 / (k : ℝ) ^ 2 ≤
      1 / ((k - 1 : ℕ) : ℝ) - 1 / (k : ℝ) := by
  have hkR : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hk0 : (0 : ℝ) < (k : ℝ) := by linarith
  have hk10 : (0 : ℝ) < ((k - 1 : ℕ) : ℝ) := by
    exact_mod_cast (by omega : 0 < k - 1)
  have hcast : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
    rw [Nat.cast_sub (show 1 ≤ k by omega)]
    norm_num
  have hrhs :
      1 / ((k - 1 : ℕ) : ℝ) - 1 / (k : ℝ) =
        1 / ((k : ℝ) * ((k - 1 : ℕ) : ℝ)) := by
    field_simp [hk0.ne', hk10.ne']
    nlinarith [hcast]
  rw [hrhs]
  gcongr
  nlinarith

private theorem telescope_Icc_le_inv (W Y : ℕ) (hW : 1 ≤ W) :
    (∑ k ∈ Finset.Icc (W + 1) Y,
      (1 / ((k - 1 : ℕ) : ℝ) - 1 / (k : ℝ))) ≤ 1 / (W : ℝ) := by
  by_cases hWY : W ≤ Y
  · have hset : Finset.Icc (W + 1) Y = Finset.Ico (W + 1) (Y + 1) := by
      ext k
      simp
    rw [hset, Finset.sum_Ico_eq_sum_range]
    have hterm : ∀ i ∈ Finset.range ((Y + 1) - (W + 1)),
        1 / ((((W + 1) + i) - 1 : ℕ) : ℝ) - 1 / ((W + 1 + i : ℕ) : ℝ) =
          1 / ((W + i : ℕ) : ℝ) - 1 / ((W + i + 1 : ℕ) : ℝ) := by
      intro i hi
      congr 2 <;> norm_cast <;> omega
    rw [Finset.sum_congr rfl hterm]
    have htel := Finset.sum_range_sub' (fun i : ℕ => 1 / ((W + i : ℕ) : ℝ)) (Y - W)
    rw [show (Y + 1) - (W + 1) = Y - W by omega]
    have htel' :
        (∑ i ∈ Finset.range (Y - W),
          (1 / ((W + i : ℕ) : ℝ) - 1 / ((W + i + 1 : ℕ) : ℝ))) =
            1 / ((W + 0 : ℕ) : ℝ) - 1 / ((W + (Y - W) : ℕ) : ℝ) := by
      simpa only [Nat.add_assoc] using htel
    rw [htel']
    exact sub_le_self _ (by positivity)
  · have hempty : Finset.Icc (W + 1) Y = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro k hk
      simp only [Finset.mem_Icc] at hk
      omega
    rw [hempty]
    simp

/-- The square-reciprocal tail needed in every `IJ/JJ` row contraction. -/
theorem bandReciprocalSquareSum_le (n W : ℕ) (hW : 1 ≤ W) :
    bandReciprocalSquareSum n W ≤ 1 / (W : ℝ) := by
  calc
    bandReciprocalSquareSum n W ≤
        ∑ p ∈ primeBand n W,
          (1 / ((p - 1 : ℕ) : ℝ) - 1 / (p : ℝ)) := by
      apply Finset.sum_le_sum
      intro p hp
      exact inv_sq_le_telescope (by
        have := cutoff_lt_of_mem_primeBand hp
        omega)
    _ ≤ ∑ k ∈ Finset.Icc (W + 1) (yNat n),
          (1 / ((k - 1 : ℕ) : ℝ) - 1 / (k : ℝ)) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro p hp
        have h := mem_primeBand.mp hp
        simp [h.2.1, h.2.2]
      · intro k hk hnot
        have hk' := Finset.mem_Icc.mp hk
        have hk2 : 2 ≤ k := by omega
        exact le_trans (by positivity : (0 : ℝ) ≤ 1 / (k : ℝ) ^ 2)
          (inv_sq_le_telescope hk2)
    _ ≤ 1 / (W : ℝ) := telescope_Icc_le_inv W (yNat n) hW











private theorem integral_one_div_mul_log {Y : ℝ} (hY : 2 ≤ Y) :
    (∫ t in (2 : ℝ)..Y, 1 / (t * Real.log t)) =
      Real.log (Real.log Y) - Real.log (Real.log 2) := by
  have hint : IntervalIntegrable (fun t : ℝ => 1 / (t * Real.log t))
      MeasureTheory.volume 2 Y := by
    apply ContinuousOn.intervalIntegrable
    intro t ht
    rw [Set.uIcc_of_le hY] at ht
    have ht0 : t ≠ 0 := by linarith [ht.1]
    have hlog0 : Real.log t ≠ 0 :=
      Real.log_ne_zero_of_pos_of_ne_one (by linarith [ht.1]) (by linarith [ht.1])
    exact ContinuousAt.continuousWithinAt
      (continuousAt_const.div (continuousAt_id.mul (Real.continuousAt_log ht0))
        (mul_ne_zero ht0 hlog0))
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt _ hint
  intro t ht
  rw [Set.uIcc_of_le hY] at ht
  have ht0 : t ≠ 0 := by linarith [ht.1]
  have hlog0 : Real.log t ≠ 0 :=
    Real.log_ne_zero_of_pos_of_ne_one (by linarith [ht.1]) (by linarith [ht.1])
  have hd := (Real.hasDerivAt_log ht0).log hlog0
  convert hd using 1
  field_simp

/-- An explicit Mertens-type upper bound, obtained from the global Chebyshev
bound by Abel summation.  It is sufficient for every harmonic loss in
Lemma 7.5 and does not invoke the prime number theorem as an assumption. -/
theorem fullReciprocalSum_le (Y : ℕ) (hY : 2 ≤ Y) :
    fullReciprocalSum Y ≤
      2 * Real.log 4 + 3 * Real.log 4 *
        (Real.log (Real.log (Y : ℝ)) - Real.log (Real.log 2)) := by
  rw [fullReciprocalSum_eq Y hY]
  have hYR : (2 : ℝ) ≤ (Y : ℝ) := by exact_mod_cast hY
  have hY0 : (0 : ℝ) < (Y : ℝ) := by linarith
  have hlogYhalf : (1 / 2 : ℝ) ≤ Real.log (Y : ℝ) := by
    have hmono : Real.log 2 ≤ Real.log (Y : ℝ) :=
      Real.log_le_log (by norm_num) hYR
    nlinarith [Real.log_two_gt_d9]
  have hlogY0 : 0 < Real.log (Y : ℝ) := by linarith
  have hlog4 : (0 : ℝ) ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hboundary :
      Chebyshev.theta (Y : ℝ) / ((Y : ℝ) * Real.log (Y : ℝ)) ≤
        2 * Real.log 4 := by
    calc
      Chebyshev.theta (Y : ℝ) / ((Y : ℝ) * Real.log (Y : ℝ)) ≤
          (Real.log 4 * (Y : ℝ)) /
            ((Y : ℝ) * Real.log (Y : ℝ)) := by
        gcongr
        exact Chebyshev.theta_le_log4_mul_x (by positivity)
      _ ≤ 2 * Real.log 4 := by
        field_simp [hY0.ne', hlogY0.ne']
        nlinarith
  have hint :
      (∫ t in (2 : ℝ)..Y,
        Chebyshev.theta t * (Real.log t + 1) /
          (t ^ 2 * Real.log t ^ 2)) ≤
        3 * Real.log 4 *
          (Real.log (Real.log (Y : ℝ)) - Real.log (Real.log 2)) := by
    calc
      (∫ t in (2 : ℝ)..Y,
        Chebyshev.theta t * (Real.log t + 1) /
          (t ^ 2 * Real.log t ^ 2)) ≤
          ∫ t in (2 : ℝ)..Y,
            3 * Real.log 4 * (1 / (t * Real.log t)) := by
        refine intervalIntegral.integral_mono_on hYR
          (intervalIntegrable_mertensIntegrand hYR) ?_ ?_
        · apply ContinuousOn.intervalIntegrable
          intro t ht
          rw [Set.uIcc_of_le hYR] at ht
          have ht0 : t ≠ 0 := by linarith [ht.1]
          have hlog0 : Real.log t ≠ 0 :=
            Real.log_ne_zero_of_pos_of_ne_one
              (by linarith [ht.1]) (by linarith [ht.1])
          exact ContinuousAt.continuousWithinAt
            (continuousAt_const.mul
              (continuousAt_const.div
                (continuousAt_id.mul (Real.continuousAt_log ht0))
                (mul_ne_zero ht0 hlog0)))
        · intro t ht
          have ht0 : 0 < t := by linarith [ht.1]
          have hloghalf : (1 / 2 : ℝ) ≤ Real.log t := by
            have hmono : Real.log 2 ≤ Real.log t :=
              Real.log_le_log (by norm_num) ht.1
            nlinarith [Real.log_two_gt_d9]
          calc
            Chebyshev.theta t * (Real.log t + 1) /
                (t ^ 2 * Real.log t ^ 2) ≤
                (Real.log 4 * t) * (Real.log t + 1) /
                  (t ^ 2 * Real.log t ^ 2) := by
              gcongr
              exact Chebyshev.theta_le_log4_mul_x (le_of_lt ht0)
            _ ≤ 3 * Real.log 4 * (1 / (t * Real.log t)) := by
              field_simp [ht0.ne', (show Real.log t ≠ 0 by linarith)]
              nlinarith
      _ = 3 * Real.log 4 *
          (Real.log (Real.log (Y : ℝ)) - Real.log (Real.log 2)) := by
        rw [intervalIntegral.integral_const_mul, integral_one_div_mul_log hYR]
  linarith





theorem bandReciprocalSum_le_full (n W : ℕ) :
    bandReciprocalSum n W ≤ fullReciprocalSum (yNat n) := by
  apply Finset.sum_le_sum_of_subset_of_nonneg (primeBand_subset_primesUpTo n W)
  intro p hp hnot
  positivity

/-- The unweighted prime harmonic mass has precisely the `O(log L)` loss
allowed in Lemma 7.5.  The constant is explicit and independent of `W` and of
every later tilt box. -/
theorem eventually_bandReciprocalSum_le_logL (W : ℕ) :
    ∀ᶠ n in atTop,
      bandReciprocalSum n W ≤ 12 * Real.log (L n) := by
  have hyTop : Tendsto (fun n : ℕ => y n) atTop atTop := by
    simpa [y] using
      ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 2 / 9)).comp
        tendsto_natCast_atTop_atTop)
  have hLTop : Tendsto L atTop atTop := by
    simpa [L] using Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hlogLTop : Tendsto (fun n : ℕ => Real.log (L n)) atTop atTop :=
    Real.tendsto_log_atTop.comp hLTop
  have hlog4nonneg : (0 : ℝ) ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hlog4upper : Real.log 4 ≤ 3 := by
    have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 4 by norm_num)
    norm_num at h ⊢
    exact h
  have hlog2pos : (0 : ℝ) < Real.log 2 := by
    linarith [Real.log_two_gt_d9]
  have hinvLog2 : (Real.log 2)⁻¹ ≤ 2 := by
    rw [← one_div, one_div_le hlog2pos (by norm_num)]
    nlinarith [Real.log_two_gt_d9]
  have hloglog2 : (-1 : ℝ) ≤ Real.log (Real.log 2) := by
    calc
      (-1 : ℝ) ≤ 1 - (Real.log 2)⁻¹ := by linarith
      _ ≤ Real.log (Real.log 2) := Real.one_sub_inv_le_log_of_pos hlog2pos
  filter_upwards [eventually_gt_atTop 0,
    hyTop.eventually (eventually_ge_atTop (2 : ℝ)),
    hLTop.eventually (eventually_ge_atTop (1 : ℝ)),
    hlogLTop.eventually (eventually_ge_atTop (5 : ℝ))] with n hn hyn hLn hlogLn
  have hyNat : 2 ≤ yNat n := Nat.le_floor hyn
  have hyNatPos : (0 : ℝ) < (yNat n : ℝ) := by positivity
  have hlogNatPos : 0 < Real.log (yNat n : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < yNat n by omega))
  have hyFloor : (yNat n : ℝ) ≤ y n :=
    Nat.floor_le (le_of_lt (y_pos hn))
  have hlogNatLeY : Real.log (yNat n : ℝ) ≤ Real.log (y n) :=
    Real.log_le_log hyNatPos hyFloor
  have hlogNatLeL : Real.log (yNat n : ℝ) ≤ L n := by
    calc
      Real.log (yNat n : ℝ) ≤ Real.log (y n) := hlogNatLeY
      _ = (2 / 9 : ℝ) * L n := log_y hn
      _ ≤ L n := by nlinarith
  have hloglogNatLeL :
      Real.log (Real.log (yNat n : ℝ)) ≤ Real.log (L n) :=
    Real.log_le_log hlogNatPos hlogNatLeL
  have hraw :
      bandReciprocalSum n W ≤
        2 * Real.log 4 + 3 * Real.log 4 *
          (Real.log (L n) - Real.log (Real.log 2)) := by
    calc
      bandReciprocalSum n W ≤ fullReciprocalSum (yNat n) :=
        bandReciprocalSum_le_full n W
      _ ≤ 2 * Real.log 4 + 3 * Real.log 4 *
          (Real.log (Real.log (yNat n : ℝ)) - Real.log (Real.log 2)) :=
        fullReciprocalSum_le (yNat n) hyNat
      _ ≤ 2 * Real.log 4 + 3 * Real.log 4 *
          (Real.log (L n) - Real.log (Real.log 2)) := by
        gcongr
  calc
    bandReciprocalSum n W ≤
        2 * Real.log 4 + 3 * Real.log 4 *
          (Real.log (L n) - Real.log (Real.log 2)) := hraw
    _ = Real.log 4 *
        (2 + 3 * Real.log (L n) - 3 * Real.log (Real.log 2)) := by ring
    _ ≤ Real.log 4 * (5 + 3 * Real.log (L n)) := by
      apply mul_le_mul_of_nonneg_left _ hlog4nonneg
      nlinarith
    _ ≤ 3 * (5 + 3 * Real.log (L n)) := by
      apply mul_le_mul_of_nonneg_right hlog4upper
      nlinarith
    _ ≤ 12 * Real.log (L n) := by nlinarith





end Erdos390.Full.PrimeSums

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





theorem endpointActualMass_eq_fullReciprocalSum_sub
    (n W : ℕ) (j : Fin (M.cellCount + 1)) :
    endpointActualMass M n W j =
      PrimeSums.fullReciprocalSum (fullCutoff M n W (j.1 + 1)) -
        PrimeSums.fullReciprocalSum (fullCutoff M n W j.1) := by
  rfl





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





end Mesh
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

/- Source module: Erdos390.Full.PaperNonstepPrimeMomentRate -/
section


/-!
# Vanishing reciprocal-square logarithmic moment

The moving-low non-step ledger needs the literal quantity
`sum t_p / p^2`, not a step-function surrogate.  This file proves directly
that it tends to zero for every fixed cutoff.  The proof uses only the
already-audited harmonic prime bound and `log p ≤ p`; no PNT asymptotic is
introduced.
-/

open scoped BigOperators
open Filter Topology

namespace Erdos390.Full.PrimeSums

open ArithmeticModel Scale

noncomputable section



theorem bandTReciprocalSquareSum_nonneg
    {n W : ℕ} (hn : 1 < n) :
    0 ≤ bandTReciprocalSquareSum n W := by
  unfold bandTReciprocalSquareSum
  exact Finset.sum_nonneg fun p hp ↦
    mul_nonneg
      (by
        unfold tPrime
        apply div_nonneg
        · exact Real.log_nonneg
            (by exact_mod_cast (prime_of_mem_primeBand hp).one_le)
        · rw [log_y (Nat.zero_lt_of_lt hn)]
          exact (mul_pos (by norm_num)
            (Real.log_pos (by exact_mod_cast hn))).le)
      (sq_nonneg _)

/-- Elementary domination by the harmonic mass divided by `log y`. -/
theorem bandTReciprocalSquareSum_le
    {n W : ℕ} (hn : 1 < n) :
    bandTReciprocalSquareSum n W ≤
      bandReciprocalSum n W / Real.log (y n) := by
  have hlogy : 0 < Real.log (y n) := by
    rw [log_y (Nat.zero_lt_of_lt hn)]
    exact mul_pos (by norm_num) (Real.log_pos (by exact_mod_cast hn))
  unfold bandTReciprocalSquareSum bandReciprocalSum
  rw [Finset.sum_div]
  apply Finset.sum_le_sum
  intro p hp
  have hpPrime := prime_of_mem_primeBand hp
  have hpR : (0 : ℝ) < p := by exact_mod_cast hpPrime.pos
  have hlogp : Real.log (p : ℝ) ≤ (p : ℝ) := by
    have h := Real.log_le_sub_one_of_pos hpR
    linarith
  unfold tPrime
  rw [show (Real.log (p : ℝ) / Real.log (y n)) *
      (1 / (p : ℝ)) ^ 2 =
        (Real.log (p : ℝ) / (p : ℝ)) *
          (1 / (p : ℝ)) / Real.log (y n) by ring]
  apply div_le_div_of_nonneg_right _ hlogy.le
  have hinv : 0 ≤ (1 / (p : ℝ)) := by positivity
  calc
    (Real.log (p : ℝ) / (p : ℝ)) * (1 / (p : ℝ)) ≤
        1 * (1 / (p : ℝ)) := by
      apply mul_le_mul_of_nonneg_right _ hinv
      exact (div_le_one hpR).2 hlogp
    _ = 1 / (p : ℝ) := one_mul _

/-- For every fixed cutoff, the literal global `sum t_p/p²` tends to zero.
This rate is independent of every later mesh and tilt box. -/
theorem tendsto_bandTReciprocalSquareSum_zero (W : ℕ) :
    Tendsto (fun n : ℕ ↦ bandTReciprocalSquareSum n W)
      atTop (nhds 0) := by
  have hLTop : Tendsto L atTop atTop := by
    simpa only [L] using
      Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hlogLdivL : Tendsto (fun n : ℕ ↦ Real.log (L n) / L n)
      atTop (nhds 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp hLTop
  have hmajorant : Tendsto (fun n : ℕ ↦
      54 * (Real.log (L n) / L n)) atTop (nhds 0) := by
    simpa only [mul_zero] using tendsto_const_nhds.mul hlogLdivL
  have hnonneg : ∀ᶠ n : ℕ in atTop,
      0 ≤ bandTReciprocalSquareSum n W := by
    filter_upwards [eventually_gt_atTop 1] with n hn
    exact bandTReciprocalSquareSum_nonneg hn
  have hupper : ∀ᶠ n : ℕ in atTop,
      bandTReciprocalSquareSum n W ≤
        54 * (Real.log (L n) / L n) := by
    filter_upwards [eventually_gt_atTop 1,
      eventually_bandReciprocalSum_le_logL W] with n hn hmass
    have hlogyN : 0 < Real.log (y n) := by
      rw [log_y (Nat.zero_lt_of_lt hn)]
      exact mul_pos (by norm_num) (Real.log_pos (by exact_mod_cast hn))
    have hraw := (bandTReciprocalSquareSum_le hn).trans
      (div_le_div_of_nonneg_right hmass hlogyN.le)
    calc
      bandTReciprocalSquareSum n W ≤
          (12 * Real.log (L n)) / Real.log (y n) := hraw
      _ = 54 * (Real.log (L n) / L n) := by
        rw [log_y (Nat.zero_lt_of_lt hn)]
        ring
  exact squeeze_zero' hnonneg hupper hmajorant

end

end Erdos390.Full.PrimeSums

end

/- Source module: Erdos390.Full.PaperNonstepLocalDiagonal -/
section


/-!
# Exact local diagonal estimates for the non-step slow row

The prime-power slow-row ledger leaves the literal cell quantity

`H_i^{-1} sum_{p in cell i} |alpha_i-t_p|/p^2`.

This file bounds that quantity without replacing `t_p` by a step value.
The low-cell estimate retains the two global reciprocal-square moments;
the positive-cell estimate exploits the moving lower endpoint.  Both are
finite identities/inequalities, independent of any tilt box.
-/

open scoped BigOperators

namespace Erdos390.Full.ArithmeticBandGeometry.Partition

noncomputable section

open ArithmeticModel ArithmeticBandGeometry PrimeSums
open PositiveCellTransfer

variable {n W : ℕ} {Band : Type*} [Fintype Band] [DecidableEq Band]
  (P : Partition n W Band)











/-- A cell whose primes all lie strictly above `A` has local diagonal at
most `w/A`, provided the literal deviations are at most `w`. -/
theorem normalizedDeviationReciprocalSquare_le_scale_div_lower
    {i : Band} {A w : ℝ}
    (hA : 0 < A)
    (hlower : ∀ p ∈ P.data.fiber i, A < (p.1 : ℝ))
    (hdev : ∀ p ∈ P.data.fiber i, |P.deviation p| ≤ w)
    (hw : 0 ≤ w) :
    P.normalizedDeviationReciprocalSquare i ≤ w / A := by
  have hH : 0 < P.mass i := P.data.mass_pos i
  have hsum :
      (∑ p ∈ P.data.fiber i,
          |P.deviation p| * (1 / (p.1 : ℝ)) ^ 2) ≤
        (w / A) * P.mass i := by
    change (∑ p ∈ P.data.fiber i,
        |P.deviation p| * (1 / (p.1 : ℝ)) ^ 2) ≤
      (w / A) * ∑ p ∈ P.data.fiber i, 1 / (p.1 : ℝ)
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro p hp
    have hp0 : (0 : ℝ) < p.1 := hA.trans (hlower p hp)
    have hinvA : 1 / (p.1 : ℝ) ≤ 1 / A :=
      one_div_le_one_div_of_le hA (hlower p hp).le
    calc
      |P.deviation p| * (1 / (p.1 : ℝ)) ^ 2 ≤
          w * (1 / (p.1 : ℝ)) ^ 2 :=
        mul_le_mul_of_nonneg_right (hdev p hp) (sq_nonneg _)
      _ ≤ w * ((1 / A) * (1 / (p.1 : ℝ))) := by
        apply mul_le_mul_of_nonneg_left _ hw
        calc
          (1 / (p.1 : ℝ)) ^ 2 =
              (1 / (p.1 : ℝ)) * (1 / (p.1 : ℝ)) := by ring
          _ ≤ (1 / A) * (1 / (p.1 : ℝ)) :=
            mul_le_mul_of_nonneg_right hinvA (by positivity)
      _ = (w / A) * (1 / (p.1 : ℝ)) := by ring
  unfold normalizedDeviationReciprocalSquare
  calc
    (1 / P.mass i) *
        (∑ p ∈ P.data.fiber i,
          |P.deviation p| * (1 / (p.1 : ℝ)) ^ 2) ≤
      (1 / P.mass i) * ((w / A) * P.mass i) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = w / A := by field_simp [hH.ne']

end

end Erdos390.Full.ArithmeticBandGeometry.Partition

end

/- Source module: Erdos390.Full.PaperCanonicalNonstepLocalDiagonalEventually -/
section


/-!
# Canonical relative decay of the literal non-step local diagonal

For the moving low cell one must not replace the local `p^{-2}` term by an
additive `O(1/W)`: its centre tends to zero.  We instead retain the exact
decomposition into `alpha_0 * sum p^{-2}` and `sum t_p p^{-2}`.  The first
term is divided by the diverging low-cell mass, while the second vanishes
and is divided only by `H_0 alpha_0 -> delta`.

For every positive cell the lower endpoint tends to infinity, giving the
direct estimate `D_i <= w/A_i`.  The result is uniform over the finite band
set and uses the actual scale `w = delta + M.ratio`; `eta` is independent.
-/

open scoped BigOperators
open Filter Topology

noncomputable section

namespace Erdos390.Full.RegularMeshPrimeCutoffs

open ArithmeticModel ArithmeticBandGeometry RegularRelativeMesh
open PositiveCellTransfer PrimeSums MovingLowMomentQuadrature
open KernelPrimeQuadrature



namespace Mesh

variable {delta eta : ℝ} (M : Mesh delta eta)

set_option maxHeartbeats 2000000 in
/-- The literal reciprocal-square deviation diagonal is `o(w alpha_i)` in
every canonical arithmetic band.  The quantification over `hn`, `hWne`,
and `S` makes proof irrelevance unnecessary at the statement boundary. -/
theorem canonicalNonstepLocalDiagonalCutoff_eventually
    (hdelta : 0 < delta) (W : ℕ)
    (hWcut : canonicalNonstepLocalDiagonalCutoff ≤ W)
    {r : ℝ} (hr : 0 < r) :
    ∀ᶠ n : ℕ in atTop, ∀ (hn : 1 < n) (hWne : W ≠ 0)
      (S : ScaleSeparation M n W) (i : Fin (M.cellCount + 1)),
      let P := canonicalPartition M hdelta hn hWne S
      P.normalizedDeviationReciprocalSquare i ≤
        r * (delta + M.ratio) * P.center i := by
  let w : ℝ := delta + M.ratio
  have hw : 0 < w := add_pos hdelta M.ratio_pos
  have hW2 : 2 ≤ W :=
    (le_max_left 2 (max canonicalMassQuadratureCutoff
      MovingLowMomentQuadrature.fullLogReciprocalSumUniformCutoff)).trans hWcut
  have hXmass : canonicalMassQuadratureCutoff ≤ W :=
    ((le_max_left canonicalMassQuadratureCutoff
      MovingLowMomentQuadrature.fullLogReciprocalSumUniformCutoff).trans
      (le_max_right 2 (max canonicalMassQuadratureCutoff
        MovingLowMomentQuadrature.fullLogReciprocalSumUniformCutoff))).trans hWcut
  have hXmoment :
      MovingLowMomentQuadrature.fullLogReciprocalSumUniformCutoff ≤ W :=
    ((le_max_right canonicalMassQuadratureCutoff
      MovingLowMomentQuadrature.fullLogReciprocalSumUniformCutoff).trans
      (le_max_right 2 (max canonicalMassQuadratureCutoff
        MovingLowMomentQuadrature.fullLogReciprocalSumUniformCutoff))).trans hWcut
  let Cmass : ℝ := canonicalMassQuadratureConstant
  let Cmoment : ℝ :=
    MovingLowMomentQuadrature.fullLogReciprocalSumUniformConstant
  have hMassQ : ∀ A Y : ℕ, canonicalMassQuadratureCutoff ≤ A → A ≤ Y →
      |fullReciprocalSum Y - fullReciprocalSum A -
        (Real.log (Real.log (Y : ℝ)) -
          Real.log (Real.log (A : ℝ)))| ≤
        5 * Cmass / Real.log (A : ℝ) ^ 3 := by
    intro A Y hA hAY
    simpa only [Cmass] using canonicalMassQuadratureBound A Y hA hAY
  have hMomentQ : ∀ A Y : ℕ,
      MovingLowMomentQuadrature.fullLogReciprocalSumUniformCutoff ≤ A →
      A ≤ Y →
      |fullLogReciprocalSum Y - fullLogReciprocalSum A -
        (Real.log (Y : ℝ) - Real.log (A : ℝ))| ≤
        2 * Cmoment / Real.log (A : ℝ) ^ 3 +
          Cmoment / (2 * Real.log (A : ℝ) ^ 2) := by
    intro A Y hA hAY
    simpa only [Cmoment] using
      MovingLowMomentQuadrature.fullLogReciprocalSumUniform_bound
        A Y hA hAY
  have hLowMassTop := tendsto_low_endpointActualMass_atTop M hdelta
    hXmass Cmass hMassQ
  have hLowSquareMajorant : Tendsto (fun n : ℕ ↦
      (1 / (W : ℝ)) / endpointActualMass M n W (lowBand M))
      atTop (nhds 0) := by
    simpa only [zero_div] using
      (tendsto_const_nhds : Tendsto (fun _n : ℕ ↦ 1 / (W : ℝ))
        atTop (nhds (1 / (W : ℝ)))).div_atTop hLowMassTop
  have hLowSquareSmall : ∀ᶠ n : ℕ in atTop,
      (1 / (W : ℝ)) / endpointActualMass M n W (lowBand M) <
        r * w / 2 :=
    hLowSquareMajorant.eventually
      (eventually_lt_nhds (div_pos (mul_pos hr hw) (by norm_num)))
  have hLowMomentMain : ∀ᶠ n : ℕ in atTop,
      3 * delta / 4 ≤ endpointContinuumMoment M n W (lowBand M) :=
    (tendsto_low_endpointContinuumMoment M hdelta W).eventually
      (eventually_ge_nhds (by linarith : 3 * delta / 4 < delta))
  have hLowMomentError : ∀ᶠ n : ℕ in atTop,
      endpointMomentError M Cmoment n W (lowBand M) ≤ delta / 4 :=
    (tendsto_low_endpointMomentError_zero M Cmoment W).eventually
      (eventually_le_nhds (by linarith : 0 < delta / 4))
  have hT2Small : ∀ᶠ n : ℕ in atTop,
      bandTReciprocalSquareSum n W < r * w * delta / 4 :=
    (tendsto_bandTReciprocalSquareSum_zero W).eventually
      (eventually_lt_nhds (by positivity : 0 < r * w * delta / 4))
  have hPositiveInv : ∀ᶠ n : ℕ in atTop,
      ∀ k : Fin M.cellCount,
        1 / (fullCutoff M n W (k.1 + 1) : ℝ) < r * delta := by
    rw [Filter.eventually_all]
    intro k
    have hAReal : Tendsto (fun n : ℕ ↦
        (fullCutoff M n W (k.1 + 1) : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop.comp
        (tendsto_general_positive_lowerCutoff_atTop M hdelta W k)
    have hInv := tendsto_inv_atTop_zero.comp hAReal
    simpa only [one_div] using
      hInv.eventually (eventually_lt_nhds (mul_pos hr hdelta))
  filter_upwards [hLowSquareSmall, hLowMomentMain, hLowMomentError,
    hT2Small, hPositiveInv] with n hSqSmall hMomentMain hMomentErr
      hT2 hPosInv
  intro hn hWne S i
  let P := canonicalPartition M hdelta hn hWne S
  let E := canonicalCertificate M hdelta hn hWne S
  have hMassEq (j : Fin (M.cellCount + 1)) :
      P.mass j = endpointActualMass M n W j := by
    rw [endpointActualMass_eq_fullReciprocalSum_sub]
    simpa only [P, E, canonicalCertificate_lower,
      canonicalCertificate_upper] using E.mass_eq_fullReciprocalSum_sub j
  let motive := fun j : Fin (M.cellCount + 1) ↦
    P.normalizedDeviationReciprocalSquare j ≤
      r * w * P.center j
  apply (Fin.cases (motive := motive) ?_ ?_ i)
  · have hH : 0 < P.mass (lowBand M) := P.data.mass_pos (lowBand M)
    have halpha : 0 < P.center (lowBand M) :=
      P.center_pos hn (lowBand M)
    have hS2 := bandReciprocalSquareSum_le n W (by omega : 1 ≤ W)
    have hSratio :
        (1 / P.mass (lowBand M)) * bandReciprocalSquareSum n W ≤
          r * w / 2 := by
      calc
        (1 / P.mass (lowBand M)) * bandReciprocalSquareSum n W =
            bandReciprocalSquareSum n W / P.mass (lowBand M) := by ring
        _ ≤ (1 / (W : ℝ)) / P.mass (lowBand M) :=
          div_le_div_of_nonneg_right hS2 hH.le
        _ = (1 / (W : ℝ)) /
            endpointActualMass M n W (lowBand M) := by rw [← hMassEq]
        _ ≤ r * w / 2 := hSqSmall.le
    have hPNT :=
      abs_canonical_mass_mul_center_sub_endpointContinuumMoment_le
        M hdelta hn hWne S hMomentQ hXmoment (lowBand M)
    have hHalpha : delta / 2 ≤
        P.mass (lowBand M) * P.center (lowBand M) := by
      have hleft := (abs_le.mp hPNT).1
      linarith
    have hT2nonneg : 0 ≤ bandTReciprocalSquareSum n W :=
      bandTReciprocalSquareSum_nonneg hn
    have hTtarget : bandTReciprocalSquareSum n W ≤
        (r * w / 2) *
          (P.mass (lowBand M) * P.center (lowBand M)) := by
      have hsmall : bandTReciprocalSquareSum n W ≤ r * w * delta / 4 :=
        hT2.le
      have hcoef : 0 ≤ r * w / 2 := (div_pos (mul_pos hr hw) (by norm_num)).le
      calc
        bandTReciprocalSquareSum n W ≤ r * w * delta / 4 := hsmall
        _ = (r * w / 2) * (delta / 2) := by ring
        _ ≤ (r * w / 2) *
            (P.mass (lowBand M) * P.center (lowBand M)) :=
          mul_le_mul_of_nonneg_left hHalpha hcoef
    have hTterm :
        (1 / P.mass (lowBand M)) * bandTReciprocalSquareSum n W ≤
          (r * w / 2) * P.center (lowBand M) := by
      rw [one_div_mul_eq_div]
      apply (div_le_iff₀ hH).2
      nlinarith
    have hraw :=
      P.normalizedDeviationReciprocalSquare_le_global_moments hn (lowBand M)
    calc
      P.normalizedDeviationReciprocalSquare (lowBand M) ≤
          (1 / P.mass (lowBand M)) *
            (P.center (lowBand M) * bandReciprocalSquareSum n W +
              bandTReciprocalSquareSum n W) := hraw
      _ = P.center (lowBand M) *
            ((1 / P.mass (lowBand M)) * bandReciprocalSquareSum n W) +
          (1 / P.mass (lowBand M)) * bandTReciprocalSquareSum n W := by ring
      _ ≤ P.center (lowBand M) * (r * w / 2) +
          (r * w / 2) * P.center (lowBand M) :=
        add_le_add (mul_le_mul_of_nonneg_left hSratio halpha.le) hTterm
      _ = r * w * P.center (lowBand M) := by ring
  · intro k
    let j : Fin (M.cellCount + 1) := k.succ
    let A : ℝ := fullCutoff M n W (k.1 + 1)
    have hANat : 0 < fullCutoff M n W (k.1 + 1) := by
      have hcut : W ≤ E.lower j := E.cutoff_le_lower j
      have hident : E.lower j = fullCutoff M n W (k.1 + 1) := by rfl
      rw [hident] at hcut
      omega
    have hA : 0 < A := by
      dsimp only [A]
      exact_mod_cast hANat
    have hlower : ∀ p ∈ P.data.fiber j, A < (p.1 : ℝ) := by
      intro p hp
      have hpBand : P.band p = j :=
        (Erdos390.Lemma84.WeightedBandData.mem_fiber_iff P.data).mp hp
      have hpInterval := (E.band_eq_iff p j).mp hpBand
      dsimp only [A]
      have hpNat : fullCutoff M n W (k.1 + 1) < p.1 := by
        simpa only [E, j, canonicalCertificate_lower] using hpInterval.1
      exact_mod_cast hpNat
    have hdevAll : ∀ p : BandPrime n W,
        |P.deviation p| ≤ w := by
      intro p
      simpa only [w] using actual_deviation_sup_le_scale M P E
        (fun j ↦ rfl) (fun j ↦ rfl) hdelta hn p
    have hdiag := P.normalizedDeviationReciprocalSquare_le_scale_div_lower
      hA (fun p hp ↦ hlower p hp) (fun p _hp ↦ hdevAll p) hw.le
    have hInv : 1 / A ≤ r * delta := by
      exact (hPosInv k).le
    have hcoord : ∀ p ∈ P.data.fiber j,
        tPrime n p.1 ∈ Set.Icc (M.lower k) (M.upper k) := by
      simpa only [j] using positive_coord_bounds M P E
        (fun j ↦ rfl) (fun j ↦ rfl) hn k
    have hcenterLower : M.lower k ≤ P.center j :=
      (P.center_mem_of_coord_bounds j hcoord).1
    have hdeltaLower : delta ≤ M.lower k := by
      unfold RegularRelativeMesh.Mesh.lower RegularRelativeMesh.Mesh.endpoint
      have hbase : 1 ≤ 1 + M.ratio := by linarith [M.ratio_pos]
      have hpow : 1 ≤ (1 + M.ratio) ^ k.1 := one_le_pow₀ hbase
      nlinarith
    have hdeltaCenter : delta ≤ P.center j :=
      hdeltaLower.trans hcenterLower
    calc
      P.normalizedDeviationReciprocalSquare j ≤ w / A := hdiag
      _ = w * (1 / A) := by ring
      _ ≤ w * (r * delta) := mul_le_mul_of_nonneg_left hInv hw.le
      _ ≤ w * (r * P.center j) := by
        apply mul_le_mul_of_nonneg_left _ hw.le
        exact mul_le_mul_of_nonneg_left hdeltaCenter hr.le
      _ = r * w * P.center j := by ring





end Mesh

end Erdos390.Full.RegularMeshPrimeCutoffs

end

theorem solution :
∀ {delta eta : Real} (M : Erdos390.Full.RegularRelativeMesh.Mesh delta eta) (hdelta : LT.lt.{0} (0 : Real) delta)
  (W : Nat),
  LE.le.{0} Erdos390.Full.RegularMeshPrimeCutoffs.canonicalNonstepLocalDiagonalCutoff W →
    ∀ {r : Real},
      LT.lt.{0} (0 : Real) r →
        ∀ᶠ (n : Nat) in Filter.atTop.{0},
          ∀ (hn : LT.lt.{0} (1 : Nat) n) (hWne : Ne.{1} W (0 : Nat))
            (S : Erdos390.Full.RegularMeshPrimeCutoffs.ScaleSeparation M n W)
            (i : Fin (HAdd.hAdd.{0, 0, 0} (Erdos390.Full.RegularRelativeMesh.Mesh.cellCount M) (1 : Nat))),
            have P := Erdos390.Full.RegularMeshPrimeCutoffs.Mesh.canonicalPartition M hdelta hn hWne S;
            LE.le.{0} (Erdos390.Full.ArithmeticBandGeometry.Partition.normalizedDeviationReciprocalSquare.{0} P i)
              (HMul.hMul.{0, 0, 0}
                (HMul.hMul.{0, 0, 0} r (HAdd.hAdd.{0, 0, 0} delta (Erdos390.Full.RegularRelativeMesh.Mesh.ratio M)))
                (Erdos390.Full.ArithmeticBandGeometry.Partition.center.{0} P i)) := by
  exact @Erdos390.Full.RegularMeshPrimeCutoffs.Mesh.canonicalNonstepLocalDiagonalCutoff_eventually
