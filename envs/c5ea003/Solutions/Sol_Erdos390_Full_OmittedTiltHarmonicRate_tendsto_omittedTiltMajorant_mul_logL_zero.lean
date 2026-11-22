-- Prove2me | solution 1 for Erdos390.Full.OmittedTiltHarmonicRate.tendsto_omittedTiltMajorant_mul_logL_zero
-- status  : ACCEPTED   (prove)
-- author  : @doctosil
-- created : 2026-09-17T15:03:37.903177+00:00
-- url     : https://prove2.me/submissions/7f4a9f0c-e2e2-4c62-9442-9ef0e342ffd4

import Mathlib
import Definitions.Def_erdos390_source_bank_interface
import Definitions.Def_erdos390_dickman_step_function
import Theorems.Thm_MediumPNT
import Definitions.Def_erdos390_analytic_foundations_001
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_product_bound
import Theorems.Thm_Erdos390_Full_DickmanBasic_rho_pos_on_zero_five
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_secondDerivative_first_bound

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

/- Source module: Erdos390.Full.OmittedTiltMarkedProbability -/
section


/-!
# Actual omitted-score marked probabilities

This module joins the paper-scale structured-cell count to the genuine
finite valuation tilt.  The local forced primes are omitted from the score,
so their marked modulus is coprime to every score prime.  No marked-number
asymptotic or normalization estimate remains as an input.
-/

open Filter Topology
open scoped BigOperators

namespace Erdos390.Full.OmittedTiltMarkedProbability

open ArithmeticModel Scale PrimeSums
open StructuredCells HeadPattern
open DivisibilityMomentBounds FiniteProbability
open PaperScaleMarkedCell PaperTiltSmallness ValuationScoreDomination
open DickmanBasic

noncomputable section



theorem eventually_omittedTiltMajorant_nonneg
    (B C c : ℝ) (W : ℕ) (hB : 0 ≤ B) (hc : 0 < c) :
    ∀ᶠ n : ℕ in atTop, 0 ≤ omittedTiltMajorant B C c W n := by
  filter_upwards [Filter.eventually_gt_atTop 1] with n hn
  have hL : 0 < L n := L_pos hn
  have hband : 0 ≤ bandReciprocalSum n W := by
    unfold bandReciprocalSum
    positivity
  unfold omittedTiltMajorant
  exact mul_nonneg
    (mul_nonneg (Real.exp_pos _).le (div_nonneg hB hL.le))
    (mul_nonneg (div_nonneg (by norm_num) hc.le) hband)









/-! ## The actual omitted-score marked law -/



end

end Erdos390.Full.OmittedTiltMarkedProbability

end

/- Source module: Erdos390.Full.OmittedTiltHarmonicRate -/
section


/-!
# Harmonic-rate control for the omitted-score remainder

The band-row aggregation in Lemma 7.5 can lose one harmonic factor of order
`log L`.  This file proves directly from the explicit paper remainder that
this loss is harmless: the remainder multiplied by `log L` still tends to
zero.  In particular, the statement does not infer the stronger rate from a
bare `o(1)` estimate.
-/

open Filter Topology

namespace Erdos390.Full.OmittedTiltHarmonicRate

open ArithmeticModel Scale PrimeSums DickmanBasic
open OmittedTiltMarkedProbability
open StructuredCells HeadPattern
open DivisibilityMomentBounds FiniteProbability
open PaperScaleMarkedCell PaperTiltSmallness ValuationScoreDomination

noncomputable section

private theorem tendsto_L_atTop : Tendsto L atTop atTop := by
  simpa [L] using
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop

/-- The normalizer perturbation retains a vanishing rate after the full
harmonic band loss. -/
theorem tendsto_omittedTiltMajorant_mul_logL_zero
    (B C c : ℝ) (W : ℕ) (hB : 0 ≤ B) (hC : 0 < C)
    (hc : 0 < c) (hW : 1 < W) :
    Tendsto
      (fun n : ℕ ↦ omittedTiltMajorant B C c W n * Real.log (L n))
      atTop (𝓝 0) := by
  let Kbound : ℝ := 2 * B / Real.log (W : ℝ)
  let small : ℕ → ℝ := fun n ↦
    (B / L n) * ((2 / c) * bandReciprocalSum n W)
  have hLTop : Tendsto L atTop atTop := tendsto_L_atTop
  have hlogSqRatio : Tendsto
      (fun n : ℕ ↦ Real.log (L n) ^ 2 / L n) atTop (𝓝 0) := by
    exact Real.isLittleO_pow_log_id_atTop.tendsto_div_nhds_zero.comp hLTop
  have hsmallNonneg : ∀ᶠ n : ℕ in atTop, 0 ≤ small n := by
    filter_upwards [Filter.eventually_gt_atTop 1] with n hn
    have hL : 0 < L n := L_pos hn
    have hband : 0 ≤ bandReciprocalSum n W := by
      unfold bandReciprocalSum
      positivity
    dsimp only [small]
    exact mul_nonneg (div_nonneg hB hL.le)
      (mul_nonneg (div_nonneg (by norm_num) hc.le) hband)
  have hsmallMajor : ∀ᶠ n : ℕ in atTop,
      small n ≤ (24 * B / c) * (Real.log (L n) / L n) := by
    filter_upwards [eventually_bandReciprocalSum_le_logL W,
      Filter.eventually_gt_atTop 1] with n hband hn
    have hL : 0 < L n := L_pos hn
    have hcoef : 0 ≤ (B / L n) * (2 / c) := by positivity
    dsimp only [small]
    calc
      (B / L n) * ((2 / c) * bandReciprocalSum n W) =
          ((B / L n) * (2 / c)) * bandReciprocalSum n W := by ring
      _ ≤ ((B / L n) * (2 / c)) * (12 * Real.log (L n)) :=
        mul_le_mul_of_nonneg_left hband hcoef
      _ = (24 * B / c) * (Real.log (L n) / L n) := by ring
  have hcastTop : Tendsto (fun n : ℕ ↦ (n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hCevent : ∀ᶠ n : ℕ in atTop, C ≤ (n : ℝ) :=
    hcastTop.eventually (eventually_ge_atTop C)
  have hInvCevent : ∀ᶠ n : ℕ in atTop, 1 / C ≤ (n : ℝ) :=
    hcastTop.eventually (eventually_ge_atTop (1 / C))
  have hexpBound : ∀ᶠ n : ℕ in atTop,
      Real.exp
          ((B / L n) *
            (Real.log (physicalBound C n : ℝ) / Real.log (W : ℝ))) ≤
        Real.exp Kbound := by
    filter_upwards [hCevent, hInvCevent, Filter.eventually_gt_atTop 1]
      with n hCn hInvCn hn
    have hnpos : 0 < n := Nat.zero_lt_of_lt hn
    have hL : 0 < L n := L_pos hn
    have hlogW : 0 < Real.log (W : ℝ) :=
      Real.log_pos (by exact_mod_cast hW)
    have hphysLower : 1 ≤ physicalBound C n := by
      unfold physicalBound
      apply Nat.le_floor
      have hOne : (1 : ℝ) ≤ C * (n : ℝ) := by
        have := (div_le_iff₀ hC).mp hInvCn
        simpa [mul_comm] using this
      exact_mod_cast hOne
    have hphysPos : 0 < physicalBound C n :=
      lt_of_lt_of_le Nat.zero_lt_one hphysLower
    have hphysCast : (physicalBound C n : ℝ) ≤ C * (n : ℝ) := by
      unfold physicalBound
      exact Nat.floor_le (mul_nonneg hC.le (by positivity))
    have hCnSq : C * (n : ℝ) ≤ (n : ℝ) ^ 2 := by
      nlinarith [show (0 : ℝ) ≤ n by positivity]
    have hlogPhys : Real.log (physicalBound C n : ℝ) ≤ 2 * L n := by
      have hleSq : (physicalBound C n : ℝ) ≤ (n : ℝ) ^ 2 :=
        hphysCast.trans hCnSq
      have hlog := Real.log_le_log (by exact_mod_cast hphysPos) hleSq
      rw [Real.log_pow] at hlog
      simpa [L] using hlog
    apply Real.exp_le_exp.mpr
    calc
      (B / L n) *
          (Real.log (physicalBound C n : ℝ) / Real.log (W : ℝ)) ≤
        (B / L n) * ((2 * L n) / Real.log (W : ℝ)) := by gcongr
      _ = Kbound := by
        dsimp only [Kbound]
        field_simp [hL.ne', hlogW.ne']
  have hmajorLe : ∀ᶠ n : ℕ in atTop,
      omittedTiltMajorant B C c W n ≤ Real.exp Kbound * small n := by
    filter_upwards [hexpBound, hsmallNonneg] with n hexp hsmall
    calc
      omittedTiltMajorant B C c W n =
          Real.exp
              ((B / L n) *
                (Real.log (physicalBound C n : ℝ) /
                  Real.log (W : ℝ))) * small n := by
        unfold omittedTiltMajorant
        dsimp only [small]
        ring
      _ ≤ Real.exp Kbound * small n :=
        mul_le_mul_of_nonneg_right hexp hsmall
  have hlogLNonneg : ∀ᶠ n : ℕ in atTop, 0 ≤ Real.log (L n) := by
    filter_upwards [hLTop.eventually (eventually_ge_atTop (1 : ℝ))]
      with n hn
    exact Real.log_nonneg hn
  have hmajorNonneg :=
    eventually_omittedTiltMajorant_nonneg B C c W hB hc
  have hprodNonneg : ∀ᶠ n : ℕ in atTop,
      0 ≤ omittedTiltMajorant B C c W n * Real.log (L n) := by
    filter_upwards [hmajorNonneg, hlogLNonneg] with n hmaj hlog
    exact mul_nonneg hmaj hlog
  let upperConstant : ℝ := Real.exp Kbound * (24 * B / c)
  have hupperT : Tendsto
      (fun n : ℕ ↦ upperConstant *
        (Real.log (L n) ^ 2 / L n)) atTop (𝓝 0) := by
    simpa using tendsto_const_nhds.mul hlogSqRatio
  have hprodLe : ∀ᶠ n : ℕ in atTop,
      omittedTiltMajorant B C c W n * Real.log (L n) ≤
        upperConstant * (Real.log (L n) ^ 2 / L n) := by
    filter_upwards [hmajorLe, hsmallMajor, hlogLNonneg,
      hsmallNonneg] with n hmajor hsmall hlog hsmall0
    have hexp0 : 0 ≤ Real.exp Kbound := (Real.exp_pos _).le
    calc
      omittedTiltMajorant B C c W n * Real.log (L n) ≤
          (Real.exp Kbound * small n) * Real.log (L n) :=
        mul_le_mul_of_nonneg_right hmajor hlog
      _ ≤ (Real.exp Kbound *
            ((24 * B / c) * (Real.log (L n) / L n))) *
            Real.log (L n) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hsmall hexp0) hlog
      _ = upperConstant * (Real.log (L n) ^ 2 / L n) := by
        dsimp only [upperConstant]
        ring
  exact squeeze_zero' hprodNonneg hprodLe hupperT







/-! ## Definitional witness for row aggregation -/



end

end Erdos390.Full.OmittedTiltHarmonicRate

end

theorem solution :
∀ (B C c : Real) (W : Nat),
  LE.le.{0} (0 : Real) B →
    LT.lt.{0} (0 : Real) C →
      LT.lt.{0} (0 : Real) c →
        LT.lt.{0} (1 : Nat) W →
          Filter.Tendsto.{0, 0}
            (fun n =>
              HMul.hMul.{0, 0, 0} (Erdos390.Full.OmittedTiltMarkedProbability.omittedTiltMajorant B C c W n)
                (Real.log (Erdos390.Full.Scale.L n)))
            Filter.atTop.{0} (nhds.{0} (0 : Real)) := by
  exact @Erdos390.Full.OmittedTiltHarmonicRate.tendsto_omittedTiltMajorant_mul_logL_zero
