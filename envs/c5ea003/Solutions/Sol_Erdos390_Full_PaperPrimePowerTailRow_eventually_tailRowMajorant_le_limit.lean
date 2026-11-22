-- Prove2me | solution 1 for Erdos390.Full.PaperPrimePowerTailRow.eventually_tailRowMajorant_le_limit
-- status  : ACCEPTED   (prove)
-- author  : @doctosil
-- created : 2026-09-17T15:24:43.175029+00:00
-- url     : https://prove2.me/submissions/afb831c7-e03a-4f4f-bfda-7df2808e2a44

import Mathlib
import Definitions.Def_erdos390_source_bank_interface
import Definitions.Def_erdos390_dickman_step_function
import Theorems.Thm_MediumPNT
import Definitions.Def_erdos390_analytic_foundations_001
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_product_bound
import Theorems.Thm_Erdos390_Full_DickmanBasic_rho_pos_on_zero_five
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_secondDerivative_first_bound
import Definitions.Def_erdos390_analytic_foundations_004

/- Source module: Erdos390.Full.FriableAsymptotic -/
section


/-!
# Friable counts on the Erdős 390 scale

This file develops the arithmetic side of the uniform Dickman estimate from
Mathlib's actual finite set `Nat.smoothNumbersUpTo`.  In particular, the
statements below are exact finite identities: no asymptotic count is exposed
as a hypothesis or a contract.

Our second parameter `y` is inclusive: `friableCount X y` counts positive
integers at most `X` all of whose prime factors are at most `y`.  Thus the
underlying Mathlib smoothness threshold is `y + 1`.
-/

open scoped BigOperators
open Filter Topology Asymptotics

namespace Erdos390.Full.FriableAsymptotic

open ArithmeticModel DickmanBasic Scale

/-! ## Quantitative prime-number input

The finite de Bruijn induction below needs a power-saving prime Stieltjes
estimate.  We derive it here from the audited medium-strength PNT, rather than
postulating a prime-distribution contract.  The exponential PNT remainder is
stronger than every fixed power of `1 / log x`.
-/



















































/-! ## Explicit regularity of the finite Dickman kernel -/









/-! ## The Dickman test weight in the prime recurrence -/



















































/-! ## Explicit oscillation and Riemann error for the Dickman weight -/


open DickmanBasic






























/-! ## Quantitative PNT transfer for the Dickman prime weight

The following estimates combine the preceding Chebyshev--Stieltjes identity,
the audited medium PNT, and the explicit Dickman-weight oscillation bound.
They are the one-prime analytic input for the finite de Bruijn induction.
-/


















/-! ## Uniform floor stability for the recursive Dickman kernel -/






















































/-- The integral cutoff `floor(n^(2/9))` retains enough logarithmic size
for the complete four-mark coordinate range. -/
theorem eventually_one_fifth_L_le_log_yNat :
    ∀ᶠ n : ℕ in Filter.atTop,
      (1 / 5 : ℝ) * L n ≤ Real.log (yNat n : ℝ) := by
  have hyTop : Filter.Tendsto (fun n : ℕ => y n)
      Filter.atTop Filter.atTop := by
    simpa [y] using
      ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 2 / 9)).comp
        tendsto_natCast_atTop_atTop)
  have hLTop : Filter.Tendsto L Filter.atTop Filter.atTop := by
    simpa [L] using
      Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [Filter.eventually_gt_atTop 0,
    hyTop.eventually (Filter.eventually_ge_atTop (2 : ℝ)),
    hLTop.eventually
      (Filter.eventually_ge_atTop (45 * Real.log 2))] with n hn hyn hLn
  have hypos : 0 < y n := y_pos hn
  have hyNatLower : y n / 2 ≤ (yNat n : ℝ) := by
    have hfloor : y n < (yNat n : ℝ) + 1 := Nat.lt_floor_add_one _
    linarith
  have hyNatPos : (0 : ℝ) < (yNat n : ℝ) :=
    (div_pos hypos (by norm_num)).trans_le hyNatLower
  have hlogLower : Real.log (y n / 2) ≤ Real.log (yNat n : ℝ) :=
    Real.log_le_log (div_pos hypos (by norm_num)) hyNatLower
  have hlogDiv : Real.log (y n / 2) = Real.log (y n) - Real.log 2 := by
    rw [Real.log_div hypos.ne' (by norm_num : (2 : ℝ) ≠ 0)]
  calc
    (1 / 5 : ℝ) * L n ≤ Real.log (y n / 2) := by
      rw [hlogDiv, log_y hn]
      linarith
    _ ≤ Real.log (yNat n : ℝ) := hlogLower






end Erdos390.Full.FriableAsymptotic

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

/- Source module: Erdos390.Full.PaperPrimePowerTailLedger -/
section


/-!
# Actual prime-power tail and endpoint ledgers

This module closes the finite arithmetic part of the beyond-four-mark
argument in paper Lemma 7.5.  The exponent sets are the actual logarithmic
valuation cutoffs, the primes belong to the actual finite band cut off by
`yNat`, and the four-mark boundary is the literal integer inequality
`yNat n ^ 4 < D`.  No asymptotic `O` notation is used in the statements.
-/

open Filter
open scoped BigOperators

namespace Erdos390.Full.PaperPrimePowerTailLedger

open ArithmeticModel Scale ValuationCutoff PaperValuationCutoff

noncomputable section













































/-! ## Literal endpoint multiplicities -/







/-! ## Actual logarithmic cutoffs and paper-scale ledgers -/





lemma cutoffScale_pos {W : ℕ} (hW : 1 < W) : 0 < cutoffScale W := by
  unfold cutoffScale
  exact div_pos (by norm_num) (Real.log_pos (by exact_mod_cast hW))



















end

end Erdos390.Full.PaperPrimePowerTailLedger

end

/- Source module: Erdos390.Full.PaperPrimePowerTailRow -/
section


/-!
# The literal beyond-four residual row

The residual functions of the four pointwise displays are exactly supported
on the finite beyond-four exponent sets.  This file identifies those sums
and applies the previously proved actual-cutoff tail ledgers.
-/

open Filter
open scoped BigOperators

namespace Erdos390.Full.PaperPrimePowerTailRow

open ArithmeticModel Scale ValuationCutoff
open OmittedTiltPairChamber
open PaperPrimePowerTailLedger PaperPrimePowerPointwise
open PaperPrimePowerFourDisplays
open PrimeSums

noncomputable section

















/-! ## One row majorant -/









/-! ## Vanishing of the row majorant -/







theorem eventually_tailRowMajorant_le_limit
    (G : ℝ) (W : ℕ) (hG : 0 ≤ G) (hW : 1 < W) :
    ∀ᶠ n : ℕ in atTop,
      tailRowMajorant G W n ≤ tailRowLimitMajorant G W n := by
  filter_upwards [FriableAsymptotic.eventually_one_fifth_L_le_log_yNat,
    eventually_bandReciprocalSum_le_logL W,
    (show Tendsto L atTop atTop by
      simpa [L] using
        Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
          (eventually_ge_atTop (1 : ℝ)),
    Filter.eventually_gt_atTop 1] with n hlogY hband hL1 hn
  let T : ℝ := G + G ^ 2
  let c : ℝ := cutoffScale W
  let Y : ℝ := yNat n
  have hL : 0 < L n := L_pos hn
  have hT : 0 ≤ T := by
    dsimp only [T]
    nlinarith [sq_nonneg G]
  have hc : 0 ≤ c := (cutoffScale_pos hW).le
  have hYnonneg : 0 ≤ Y := by dsimp only [Y]; positivity
  have hlogYpos : 0 < Real.log Y := by
    have : 0 < (1 / 5 : ℝ) * L n := by positivity
    exact this.trans_le (by simpa only [Y] using hlogY)
  have hYone : 1 < Y := (Real.log_pos_iff hYnonneg).mp hlogYpos
  have hYpos : 0 < Y := zero_lt_one.trans hYone
  have hnRpos : (0 : ℝ) < n := by exact_mod_cast (Nat.zero_lt_of_lt hn)
  have hnPow : (n : ℝ) ^ (1 / 5 : ℝ) ≤ Y := by
    calc
      (n : ℝ) ^ (1 / 5 : ℝ) =
          Real.exp ((1 / 5 : ℝ) * L n) := by
        rw [Real.rpow_def_of_pos hnRpos]
        congr 1
        unfold L
        ring
      _ ≤ Real.exp (Real.log Y) := Real.exp_le_exp.mpr
        (by simpa only [Y] using hlogY)
      _ = Y := Real.exp_log hYpos
  have hnPowPos : 0 < (n : ℝ) ^ (1 / 5 : ℝ) :=
    Real.rpow_pos_of_pos hnRpos _
  have hnPow23 : (n : ℝ) ^ (2 / 15 : ℝ) ≤
      Y ^ (2 / 3 : ℝ) := by
    have hmono := Real.rpow_le_rpow
      (Real.rpow_nonneg (Nat.cast_nonneg n) (1 / 5 : ℝ))
      hnPow (show (0 : ℝ) ≤ 2 / 3 by norm_num)
    calc
      (n : ℝ) ^ (2 / 15 : ℝ) =
          ((n : ℝ) ^ (1 / 5 : ℝ)) ^ (2 / 3 : ℝ) := by
        convert Real.rpow_mul (Nat.cast_nonneg n) (1 / 5 : ℝ) (2 / 3 : ℝ)
          using 1
        all_goals norm_num
      _ ≤ Y ^ (2 / 3 : ℝ) := hmono
  have hnPow23Pos : 0 < (n : ℝ) ^ (2 / 15 : ℝ) :=
    Real.rpow_pos_of_pos hnRpos _
  have hnPow2 : (n : ℝ) ^ (2 / 5 : ℝ) ≤ Y ^ 2 := by
    have hmono := Real.rpow_le_rpow
      (Real.rpow_nonneg (Nat.cast_nonneg n) (1 / 5 : ℝ))
      hnPow (show (0 : ℝ) ≤ 2 by norm_num)
    calc
      (n : ℝ) ^ (2 / 5 : ℝ) =
          ((n : ℝ) ^ (1 / 5 : ℝ)) ^ (2 : ℝ) := by
        convert Real.rpow_mul (Nat.cast_nonneg n) (1 / 5 : ℝ) (2 : ℝ)
          using 1
        all_goals norm_num
      _ ≤ Y ^ (2 : ℝ) := hmono
      _ = Y ^ 2 := by norm_num [Real.rpow_two]
  have hnPow2Pos : 0 < (n : ℝ) ^ (2 / 5 : ℝ) :=
    Real.rpow_pos_of_pos hnRpos _
  have hlogL : Real.log (L n) ≤ L n - 1 :=
    Real.log_le_sub_one_of_pos hL
  have hband' : bandReciprocalSum n W + 1 ≤ 13 * L n := by
    linarith
  have hH0 : 0 ≤ bandReciprocalSum n W := by
    unfold bandReciprocalSum
    positivity
  have hK0 : 0 ≤ c * L n := mul_nonneg hc hL.le
  have hdiv1 : (c * L n) / Y ≤
      (c * L n) / (n : ℝ) ^ (1 / 5 : ℝ) :=
    div_le_div_of_nonneg_left hK0 hnPowPos hnPow
  have hinner1 : ((c * L n) / Y) * (bandReciprocalSum n W + 1) ≤
      ((c * L n) / (n : ℝ) ^ (1 / 5 : ℝ)) * (13 * L n) :=
    mul_le_mul hdiv1 hband' (add_nonneg hH0 zero_le_one)
      (div_nonneg hK0 hnPowPos.le)
  have hterm1 : T * (((c * L n) / Y) *
      (bandReciprocalSum n W + 1)) ≤
      (13 * T * c) * (L n ^ 2 / (n : ℝ) ^ (1 / 5 : ℝ)) := by
    calc
      _ ≤ T * (((c * L n) / (n : ℝ) ^ (1 / 5 : ℝ)) *
          (13 * L n)) := mul_le_mul_of_nonneg_left hinner1 hT
      _ = _ := by ring
  have hnum2 : 0 ≤ (c * L n) ^ 2 := sq_nonneg _
  have hdiv2 : (c * L n) ^ 2 / Y ^ (2 / 3 : ℝ) ≤
      (c * L n) ^ 2 / (n : ℝ) ^ (2 / 15 : ℝ) :=
    div_le_div_of_nonneg_left hnum2 hnPow23Pos hnPow23
  have hterm2 : T * ((c * L n) ^ 2 / Y ^ (2 / 3 : ℝ)) ≤
      (T * c ^ 2) * (L n ^ 2 / (n : ℝ) ^ (2 / 15 : ℝ)) := by
    calc
      _ ≤ T * ((c * L n) ^ 2 /
          (n : ℝ) ^ (2 / 15 : ℝ)) :=
        mul_le_mul_of_nonneg_left hdiv2 hT
      _ = _ := by ring
  have hdiv3 : (c * L n) ^ 2 / Y ^ 2 ≤
      (c * L n) ^ 2 / (n : ℝ) ^ (2 / 5 : ℝ) :=
    div_le_div_of_nonneg_left hnum2 hnPow2Pos hnPow2
  have hterm3 : 6 * G * ((c * L n) ^ 2 / Y ^ 2) ≤
      (6 * G * c ^ 2) * (L n ^ 2 / (n : ℝ) ^ (2 / 5 : ℝ)) := by
    calc
      _ ≤ 6 * G * ((c * L n) ^ 2 /
          (n : ℝ) ^ (2 / 5 : ℝ)) :=
        mul_le_mul_of_nonneg_left hdiv3 (mul_nonneg (by norm_num) hG)
      _ = _ := by ring
  unfold tailRowMajorant tailRowLimitMajorant
  dsimp only [T, c, Y]
  exact add_le_add (add_le_add hterm1 hterm2) hterm3







end

end Erdos390.Full.PaperPrimePowerTailRow

end

theorem solution :
∀ (G : Real) (W : Nat),
  LE.le.{0} (0 : Real) G →
    LT.lt.{0} (1 : Nat) W →
      ∀ᶠ (n : Nat) in Filter.atTop.{0},
        LE.le.{0} (Erdos390.Full.PaperPrimePowerTailRow.tailRowMajorant G W n)
          (Erdos390.Full.PaperPrimePowerTailRow.tailRowLimitMajorant G W n) := by
  exact @Erdos390.Full.PaperPrimePowerTailRow.eventually_tailRowMajorant_le_limit
