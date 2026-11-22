-- Prove2me | solution 1 for Erdos390.Full.PaperPrimePowerRemainderRate.tendsto_primePowerRowRemainder_mul_logL_zero
-- status  : ACCEPTED   (prove)
-- author  : @doctosil
-- created : 2026-09-17T15:30:43.00678+00:00
-- url     : https://prove2.me/submissions/fcef2d7f-1ee7-4449-8c63-3cecf5f84999

import Mathlib
import Definitions.Def_erdos390_source_bank_interface
import Definitions.Def_erdos390_dickman_step_function
import Theorems.Thm_MediumPNT
import Definitions.Def_erdos390_analytic_foundations_001
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_product_bound
import Theorems.Thm_Erdos390_Full_DickmanBasic_rho_pos_on_zero_five
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_secondDerivative_first_bound
import Definitions.Def_erdos390_analytic_foundations_004
import Theorems.Thm_Erdos390_Full_PaperPrimePowerRemainderRate_tendsto_primePowerChamberRemainder_mul_logL_sq_zero
import Theorems.Thm_Erdos390_Full_PaperPrimePowerRemainderRate_tendsto_primePowerChamberRemainder_zero_and_rate
import Theorems.Thm_Erdos390_Full_PaperPrimePowerTailRow_eventually_tailRowMajorant_le_limit

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

/- Source module: Erdos390.Full.LocalFugacityBounds -/
section


/-!
# Uniform bounds for restored local fugacity coefficients

The local restoration in Lemma 7.5 must retain both the factor `1 / L`
and the geometric factor `p^{-r}`.  Cardinality bounds on the exponent set
are too crude for that purpose.  This module proves the required shifted
geometric estimates directly for the actual coefficients
`exp (eta/L)^a - exp (eta/L)^(a-1)`.
-/

open scoped BigOperators

namespace Erdos390.Full.LocalFugacityBounds

open LocalFugacity

noncomputable section























theorem quadraticHalfMass_nonneg : 0 ≤ quadraticHalfMass := by
  unfold quadraticHalfMass
  exact tsum_nonneg fun i ↦ by
    unfold quadraticHalfTerm
    positivity



















end

end Erdos390.Full.LocalFugacityBounds

end

/- Source module: Erdos390.Full.PaperPrimePowerChamberError -/
section


/-!
# Explicit chamber-error majorants for prime-power aggregation

This file replaces the nested restoration ledger by one scalar remainder at
the natural product-reciprocal scale.  The scalar is explicit, uniform over
all moving primes and exponents, and retains the vanishing omitted-score and
`1 / log n` factors needed before the harmonic prime sum is taken.
-/

namespace Erdos390.Full.PaperPrimePowerChamberError

open ArithmeticModel Scale HeadPattern
open OmittedTiltPairChamber FullTiltPairChamber
open LocalFugacityBounds TwoLocalRestorationBound
open PaperTwoLocalRestorationBound PaperScaleMarkedCell
open FullTiltPrimePowerCovariance

noncomputable section





















theorem localRestorationScale_nonneg {G k : ℝ}
    (hG : 0 ≤ G) (hk : 0 ≤ k) :
    0 ≤ localRestorationScale G k := by
  unfold localRestorationScale
  positivity

theorem pairProbabilityScale_nonneg {epsilon G k : ℝ}
    (hepsilon : 0 ≤ epsilon) (hG : 0 ≤ G) (hk : 0 ≤ k) :
    0 ≤ pairProbabilityScale epsilon G k := by
  unfold pairProbabilityScale
  have hlocal := localRestorationScale_nonneg hG hk
  have hrho : 0 ≤ 1 / DickmanBasic.rho DickmanBasic.U := by
    exact one_div_nonneg.mpr DickmanBasic.rho_U_pos.le
  positivity

theorem pairCovarianceScale_nonneg {E : ℝ} (hE : 0 ≤ E) :
    0 ≤ pairCovarianceScale E := by
  unfold pairCovarianceScale
  have hrho : 0 ≤ 1 / DickmanBasic.rho DickmanBasic.U := by
    exact one_div_nonneg.mpr DickmanBasic.rho_U_pos.le
  positivity

theorem aggregateChamberScale_nonneg {epsilon G k : ℝ}
    (hepsilon : 0 ≤ epsilon) (hG : 0 ≤ G) (hk : 0 ≤ k) :
    0 ≤ aggregateChamberScale epsilon G k := by
  unfold aggregateChamberScale
  have hE := pairProbabilityScale_nonneg hepsilon hG hk
  exact add_nonneg (mul_nonneg (by norm_num) (pairCovarianceScale_nonneg hE)) hE













end

end Erdos390.Full.PaperPrimePowerChamberError

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

/- Source module: Erdos390.Full.PaperPrimePowerPairAggregation -/
section


/-!
# From actual prime-power pairs to a paper prime row

This file performs the finite aggregation that follows the pointwise
two-local estimates in Lemma 7.5.  Its inputs are covariances and moments of
the genuine divisor-indicator columns of an actual `BoundedValuationLaw`.
The preceding logarithmic-cutoff module makes every exponent range literal.

The factors `8`, `64`, and `quadraticHalfMass` are obtained from the proved
geometric series, rather than hidden in an `O`-constant.  A single universal
aggregation constant then feeds the already formalized paper-band row
contraction.
-/

open scoped BigOperators

namespace Erdos390.Full.PaperPrimePowerPairAggregation

open ArithmeticModel Scale
open FiniteProbability PrimePowerCovariance
open PrimePowerCutoffCovariance LocalFugacityBounds
open ValuationCutoff
open PrimeSums
open PaperPrimePowerRow

noncomputable section



lemma pairAggregationConstant_nonneg : 0 ≤ pairAggregationConstant := by
  unfold pairAggregationConstant
  exact add_nonneg (by norm_num) quadraticHalfMass_nonneg







namespace BoundedValuationLaw

variable {Omega : Type*} [Fintype Omega] {M : ℕ}
  (law : BoundedValuationLaw Omega M)











end BoundedValuationLaw

end


end Erdos390.Full.PaperPrimePowerPairAggregation

end

/- Source module: Erdos390.Full.PaperPrimePowerFourDisplays -/
section


/-!
# The four pointwise displays of Lemma 7.5

This file is the exact algebraic specialization of the generic actual-law
splice to `JI`, `IJ`, `JJ`, and the diagonal second-moment input.  One main
constant and one chamber remainder dominate all four orientations.
-/

namespace Erdos390.Full.PaperPrimePowerFourDisplays

open ArithmeticModel Scale
open FiniteProbability PrimePowerCovariance
open PaperPrimePowerChamberError PaperPrimePowerPointwise

noncomputable section















theorem primePowerChamberRemainder_nonneg
    {epsilon G₀ k : ℝ} (hepsilon : 0 ≤ epsilon)
    (hG₀ : 0 ≤ G₀) (hk : 0 ≤ k) :
    0 ≤ primePowerChamberRemainder epsilon G₀ k :=
  aggregateChamberScale_nonneg hepsilon hG₀ hk









end

end Erdos390.Full.PaperPrimePowerFourDisplays

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



theorem tailRowMajorant_nonneg {G : ℝ} (hG : 0 ≤ G) {W n : ℕ}
    (hW : 1 < W) (hn : 1 < n) :
    0 ≤ tailRowMajorant G W n := by
  unfold tailRowMajorant
  dsimp only
  have hT : 0 ≤ G + G ^ 2 := by nlinarith [sq_nonneg G]
  have hband : 0 ≤ bandReciprocalSum n W := by
    unfold bandReciprocalSum
    positivity
  have hK : 0 ≤ cutoffScale W * L n :=
    mul_nonneg (cutoffScale_pos hW).le (L_pos hn).le
  have hY : 0 ≤ (yNat n : ℝ) := by positivity
  have hYpow : 0 ≤ (yNat n : ℝ) ^ (2 / 3 : ℝ) :=
    Real.rpow_nonneg hY _
  exact add_nonneg
    (add_nonneg
      (mul_nonneg hT (mul_nonneg (div_nonneg hK hY)
        (by linarith)))
      (mul_nonneg hT (div_nonneg (sq_nonneg _) hYpow)))
    (mul_nonneg (mul_nonneg (by norm_num) hG)
      (div_nonneg (sq_nonneg _) (sq_nonneg _)))





/-! ## Vanishing of the row majorant -/











/-- The polynomial tail remains negligible after the one harmonic
`log (L n)` loss used by the moving low band. -/
private theorem tendsto_L_sq_div_nat_rpow_mul_logL_zero
    {a : ℝ} (ha : 0 < a) :
    Tendsto (fun n : ℕ ↦
      (L n ^ 2 / (n : ℝ) ^ a) * Real.log (L n)) atTop (nhds 0) := by
  have hcube : Tendsto (fun n : ℕ ↦
      L n ^ 3 / (n : ℝ) ^ a) atTop (nhds 0) := by
    have hreal : Tendsto
        (fun x : ℝ ↦ Real.log x ^ (3 : ℝ) / x ^ a)
        atTop (nhds 0) :=
      (isLittleO_log_rpow_rpow_atTop (3 : ℝ) ha).tendsto_div_nhds_zero
    have hnat := hreal.comp tendsto_natCast_atTop_atTop
    change Tendsto
      (fun n : ℕ ↦ Real.log (n : ℝ) ^ (3 : ℝ) / (n : ℝ) ^ a)
        atTop (nhds 0) at hnat
    simpa [L, Real.rpow_natCast] using hnat
  have hLTop : Tendsto L atTop atTop := by
    simpa [L] using
      Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hlower : ∀ᶠ n : ℕ in atTop,
      0 ≤ (L n ^ 2 / (n : ℝ) ^ a) * Real.log (L n) := by
    filter_upwards [hLTop.eventually (eventually_ge_atTop (1 : ℝ))]
      with n hL1
    exact mul_nonneg (div_nonneg (sq_nonneg _) (Real.rpow_nonneg (by positivity) _))
      (Real.log_nonneg hL1)
  have hupper : ∀ᶠ n : ℕ in atTop,
      (L n ^ 2 / (n : ℝ) ^ a) * Real.log (L n) ≤
        L n ^ 3 / (n : ℝ) ^ a := by
    filter_upwards [hLTop.eventually (eventually_ge_atTop (1 : ℝ))]
      with n hL1
    have hL0 : 0 ≤ L n := zero_le_one.trans hL1
    have hlog0 : 0 ≤ Real.log (L n) := Real.log_nonneg hL1
    have hlogLe : Real.log (L n) ≤ L n :=
      (Real.log_le_sub_one_of_pos (zero_lt_one.trans_le hL1)).trans (by linarith)
    have hden : 0 ≤ (n : ℝ) ^ a := Real.rpow_nonneg (by positivity) _
    calc
      (L n ^ 2 / (n : ℝ) ^ a) * Real.log (L n) =
          (L n ^ 2 * Real.log (L n)) / (n : ℝ) ^ a := by ring
      _ ≤ (L n ^ 2 * L n) / (n : ℝ) ^ a :=
        div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hlogLe (sq_nonneg _)) hden
      _ = L n ^ 3 / (n : ℝ) ^ a := by ring
  exact squeeze_zero' hlower hupper hcube

/-- `tailRowMajorant` has the sharp rate required to divide by the moving
low-cell scale `alpha_0 \asymp 1 / log L`. -/
theorem tendsto_tailRowMajorant_mul_logL_zero
    (G : ℝ) (W : ℕ) (hG : 0 ≤ G) (hW : 1 < W) :
    Tendsto (fun n : ℕ ↦
      tailRowMajorant G W n * Real.log (L n)) atTop (nhds 0) := by
  have h1 := tendsto_L_sq_div_nat_rpow_mul_logL_zero
    (show (0 : ℝ) < 1 / 5 by norm_num)
  have h2 := tendsto_L_sq_div_nat_rpow_mul_logL_zero
    (show (0 : ℝ) < 2 / 15 by norm_num)
  have h3 := tendsto_L_sq_div_nat_rpow_mul_logL_zero
    (show (0 : ℝ) < 2 / 5 by norm_num)
  have hlimitRate : Tendsto (fun n : ℕ ↦
      tailRowLimitMajorant G W n * Real.log (L n)) atTop (nhds 0) := by
    have ht1 := (tendsto_const_nhds : Tendsto
      (fun _n : ℕ ↦ 13 * (G + G ^ 2) * cutoffScale W) atTop
      (nhds (13 * (G + G ^ 2) * cutoffScale W))).mul h1
    have ht2 := (tendsto_const_nhds : Tendsto
      (fun _n : ℕ ↦ (G + G ^ 2) * cutoffScale W ^ 2) atTop
      (nhds ((G + G ^ 2) * cutoffScale W ^ 2))).mul h2
    have ht3 := (tendsto_const_nhds : Tendsto
      (fun _n : ℕ ↦ 6 * G * cutoffScale W ^ 2) atTop
      (nhds (6 * G * cutoffScale W ^ 2))).mul h3
    have hsum := (ht1.add ht2).add ht3
    have hsum0 : Tendsto (fun n : ℕ ↦
        (13 * (G + G ^ 2) * cutoffScale W) *
            ((L n ^ 2 / (n : ℝ) ^ (1 / 5 : ℝ)) * Real.log (L n)) +
        ((G + G ^ 2) * cutoffScale W ^ 2) *
            ((L n ^ 2 / (n : ℝ) ^ (2 / 15 : ℝ)) * Real.log (L n)) +
        (6 * G * cutoffScale W ^ 2) *
            ((L n ^ 2 / (n : ℝ) ^ (2 / 5 : ℝ)) * Real.log (L n)))
        atTop (nhds 0) := by simpa only [mul_zero, add_zero] using hsum
    apply hsum0.congr'
    filter_upwards with n
    unfold tailRowLimitMajorant
    ring
  have hLTop : Tendsto L atTop atTop := by
    simpa [L] using
      Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hlower : ∀ᶠ n : ℕ in atTop,
      0 ≤ tailRowMajorant G W n * Real.log (L n) := by
    filter_upwards [Filter.eventually_gt_atTop 1,
      hLTop.eventually (eventually_ge_atTop (1 : ℝ))] with n hn hL1
    exact mul_nonneg (tailRowMajorant_nonneg hG hW hn)
      (Real.log_nonneg hL1)
  have hupper : ∀ᶠ n : ℕ in atTop,
      tailRowMajorant G W n * Real.log (L n) ≤
        tailRowLimitMajorant G W n * Real.log (L n) := by
    filter_upwards [eventually_tailRowMajorant_le_limit G W hG hW,
      hLTop.eventually (eventually_ge_atTop (1 : ℝ))] with n hrow hL1
    exact mul_le_mul_of_nonneg_right hrow (Real.log_nonneg hL1)
  exact squeeze_zero' hlower hupper hlimitRate

end

end Erdos390.Full.PaperPrimePowerTailRow

end

/- Source module: Erdos390.Full.PaperPrimePowerRemainderRate -/
section


/-!
# Common vanishing remainder for Lemma 7.5

The omitted-score error must survive one complete harmonic prime sum.  This
file propagates the strengthened `epsilon * log L -> 0` estimate through the
local restoration and covariance polynomials, and then combines it with the
literal beyond-four row.
-/

open Filter Topology

namespace Erdos390.Full.PaperPrimePowerRemainderRate

open ArithmeticModel Scale PrimeSums
open PaperPrimePowerChamberError PaperPrimePowerFourDisplays
open PaperPrimePowerPairAggregation PaperPrimePowerTailRow

noncomputable section

private theorem tendsto_const_mul_zero
    (a : ℝ) {f : ℕ → ℝ} (hf : Tendsto f atTop (nhds 0)) :
    Tendsto (fun n : ℕ ↦ a * f n) atTop (nhds 0) := by
  have ha : Tendsto (fun _n : ℕ ↦ a) atTop (nhds a) :=
    tendsto_const_nhds
  simpa only [mul_zero] using ha.mul hf















/-- After the two-harmonic pointwise rate, the fully aggregated row still
has one harmonic rate left.  This is the exact `o(alpha_0)` input required
by the sharp moving-low-cell transfer. -/
theorem tendsto_primePowerRowRemainder_mul_logL_zero
    (epsilon : ℕ → ℝ) (G₀ B Gf : ℝ) (W : ℕ)
    (hepsilon : Tendsto epsilon atTop (nhds 0))
    (hepsilonRate : Tendsto
      (fun n : ℕ ↦ epsilon n * Real.log (L n)) atTop (nhds 0))
    (hepsilonRateSq : Tendsto
      (fun n : ℕ ↦ epsilon n * Real.log (L n) ^ 2) atTop (nhds 0))
    (hepsilon0 : ∀ n, 0 ≤ epsilon n) (hG₀ : 0 ≤ G₀)
    (hB : 0 ≤ B) (hGf : 0 ≤ Gf) (hW : 1 < W) :
    Tendsto (fun n : ℕ ↦
      primePowerRowRemainder epsilon G₀ B Gf W n * Real.log (L n))
      atTop (nhds 0) := by
  obtain ⟨hchamber, hchamberRate⟩ :=
    tendsto_primePowerChamberRemainder_zero_and_rate
      epsilon G₀ B W hepsilon hepsilonRate
  have hchamberRateSq :=
    tendsto_primePowerChamberRemainder_mul_logL_sq_zero
      epsilon G₀ B W hepsilon hepsilonRateSq
  let R : ℕ → ℝ := fun n ↦
    primePowerChamberRemainder (epsilon n) G₀ (coefficientScale B W n)
  let upper : ℕ → ℝ := fun n ↦
    pairAggregationConstant *
      (12 * (R n * Real.log (L n) ^ 2) +
        5 * (R n * Real.log (L n))) * (1 / (W : ℝ))
  have hupperT : Tendsto upper atTop (nhds 0) := by
    have hscaledSq := tendsto_const_mul_zero 12 hchamberRateSq
    have hscaled := tendsto_const_mul_zero 5 hchamberRate
    have hsum := hscaledSq.add hscaled
    have hsum0 : Tendsto (fun n : ℕ ↦
        12 * (primePowerChamberRemainder (epsilon n) G₀
          (coefficientScale B W n) * Real.log (L n) ^ 2) +
        5 * (primePowerChamberRemainder (epsilon n) G₀
          (coefficientScale B W n) * Real.log (L n)))
        atTop (nhds 0) := by simpa only [add_zero] using hsum
    have hleft := tendsto_const_mul_zero pairAggregationConstant hsum0
    have hout := tendsto_const_mul_zero (1 / (W : ℝ)) hleft
    apply hout.congr'
    filter_upwards with n
    unfold upper
    dsimp only [R]
    ring
  have hchamberNonneg : ∀ᶠ n : ℕ in atTop, 0 ≤ R n := by
    filter_upwards [Filter.eventually_gt_atTop 1] with n hn
    unfold R
    exact primePowerChamberRemainder_nonneg
      (hepsilon0 n) hG₀ (by
        unfold coefficientScale
        have hL := L_pos hn
        positivity)
  have hLTop : Tendsto L atTop atTop := by
    simpa [L] using Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hbandUpper : ∀ᶠ n : ℕ in atTop,
      (pairAggregationConstant * R n * (bandReciprocalSum n W + 5) *
          (1 / (W : ℝ))) * Real.log (L n) ≤ upper n := by
    filter_upwards [eventually_bandReciprocalSum_le_logL W,
      hchamberNonneg, hLTop.eventually (eventually_ge_atTop (1 : ℝ))]
      with n hband hR hL1
    have hlog : 0 ≤ Real.log (L n) := Real.log_nonneg hL1
    have hAgg : 0 ≤ pairAggregationConstant := pairAggregationConstant_nonneg
    have hWinv : 0 ≤ 1 / (W : ℝ) := by positivity
    have hinside : R n * (bandReciprocalSum n W + 5) * Real.log (L n) ≤
        12 * (R n * Real.log (L n) ^ 2) +
          5 * (R n * Real.log (L n)) := by
      have := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hband hR) hlog
      nlinarith
    calc
      (pairAggregationConstant * R n * (bandReciprocalSum n W + 5) *
          (1 / (W : ℝ))) * Real.log (L n) =
        (pairAggregationConstant *
          (R n * (bandReciprocalSum n W + 5) * Real.log (L n))) *
            (1 / (W : ℝ)) := by ring
      _ ≤ (pairAggregationConstant *
          (12 * (R n * Real.log (L n) ^ 2) +
            5 * (R n * Real.log (L n)))) * (1 / (W : ℝ)) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hinside hAgg) hWinv
      _ = upper n := by rfl
  have hbandNonneg : ∀ᶠ n : ℕ in atTop,
      0 ≤ (pairAggregationConstant * R n * (bandReciprocalSum n W + 5) *
        (1 / (W : ℝ))) * Real.log (L n) := by
    filter_upwards [hchamberNonneg,
      hLTop.eventually (eventually_ge_atTop (1 : ℝ))] with n hR hL1
    have hband : 0 ≤ bandReciprocalSum n W := by
      unfold bandReciprocalSum
      positivity
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg
          (mul_nonneg pairAggregationConstant_nonneg hR) (by linarith))
        (by positivity)) (Real.log_nonneg hL1)
  have hbandT := squeeze_zero' hbandNonneg hbandUpper hupperT
  have htail := tendsto_tailRowMajorant_mul_logL_zero Gf W hGf hW
  change Tendsto (fun n : ℕ ↦
    (pairAggregationConstant *
      primePowerChamberRemainder (epsilon n) G₀ (coefficientScale B W n) *
      (bandReciprocalSum n W + 5) * (1 / (W : ℝ)) +
      tailRowMajorant Gf W n) * Real.log (L n)) atTop (nhds 0)
  have hsum := hbandT.add htail
  have hsum0 : Tendsto (fun n : ℕ ↦
      pairAggregationConstant * R n * (bandReciprocalSum n W + 5) *
          (1 / (W : ℝ)) * Real.log (L n) +
        tailRowMajorant Gf W n * Real.log (L n))
      atTop (nhds 0) := by simpa only [add_zero] using hsum
  apply hsum0.congr'
  filter_upwards with n
  dsimp only [R]
  ring

end

end Erdos390.Full.PaperPrimePowerRemainderRate

end

theorem solution :
∀ (epsilon : Nat → Real) (G₀ B Gf : Real) (W : Nat),
  Filter.Tendsto.{0, 0} epsilon Filter.atTop.{0} (nhds.{0} (0 : Real)) →
    Filter.Tendsto.{0, 0} (fun n => HMul.hMul.{0, 0, 0} (epsilon n) (Real.log (Erdos390.Full.Scale.L n)))
        Filter.atTop.{0} (nhds.{0} (0 : Real)) →
      Filter.Tendsto.{0, 0}
          (fun n =>
            HMul.hMul.{0, 0, 0} (epsilon n) (HPow.hPow.{0, 0, 0} (Real.log (Erdos390.Full.Scale.L n)) (2 : Nat)))
          Filter.atTop.{0} (nhds.{0} (0 : Real)) →
        (∀ (n : Nat), LE.le.{0} (0 : Real) (epsilon n)) →
          LE.le.{0} (0 : Real) G₀ →
            LE.le.{0} (0 : Real) B →
              LE.le.{0} (0 : Real) Gf →
                LT.lt.{0} (1 : Nat) W →
                  Filter.Tendsto.{0, 0}
                    (fun n =>
                      HMul.hMul.{0, 0, 0}
                        (Erdos390.Full.PaperPrimePowerRemainderRate.primePowerRowRemainder epsilon G₀ B Gf W n)
                        (Real.log (Erdos390.Full.Scale.L n)))
                    Filter.atTop.{0} (nhds.{0} (0 : Real)) := by
  exact @Erdos390.Full.PaperPrimePowerRemainderRate.tendsto_primePowerRowRemainder_mul_logL_zero
