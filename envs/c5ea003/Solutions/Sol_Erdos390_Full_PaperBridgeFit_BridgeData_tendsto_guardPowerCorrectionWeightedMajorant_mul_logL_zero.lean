-- Prove2me | solution 1 for Erdos390.Full.PaperBridgeFit.BridgeData.tendsto_guardPowerCorrectionWeightedMajorant_mul_logL_zero
-- status  : ACCEPTED   (prove)
-- author  : @doctosil
-- created : 2026-09-17T15:21:24.541899+00:00
-- url     : https://prove2.me/submissions/edca0b73-082f-4a44-a59d-743561cc1c2c

import Mathlib
import Definitions.Def_erdos390_source_bank_interface
import Definitions.Def_erdos390_dickman_step_function
import Theorems.Thm_MediumPNT
import Definitions.Def_erdos390_analytic_foundations_001
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_product_bound
import Theorems.Thm_Erdos390_Full_DickmanBasic_rho_pos_on_zero_five
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_secondDerivative_first_bound
import Definitions.Def_erdos390_analytic_foundations_002
import Definitions.Def_erdos390_analytic_foundations_005

/- Source module: Erdos390.Full.GuardSquarefreeErrorRate -/
section


/-!
# Vanishing rate of the squarefree guard error

The reciprocal guard conversion costs `y²`.  Since the concrete ledger has
`O(y log n)` guards and each raw cell has positive linear density, the final
cost is `O((log n)/n^(1/3))`; it still vanishes after multiplication by
`log log n`.  This file proves that rate with the literal scales.
-/

open Filter Topology

namespace Erdos390.Full.GuardSquarefreeErrorRate

open ArithmeticModel Scale PaperGuardCensus
open GuardDeletionSquarefreeProfiles

noncomputable section

private theorem tendsto_inv_nat_rpow_zero (a : ℝ) (ha : 0 < a) :
    Tendsto (fun n : ℕ ↦ 1 / (n : ℝ) ^ a) atTop (nhds 0) := by
  have hreal : Tendsto
      (fun x : ℝ ↦ Real.log x ^ (0 : ℝ) / x ^ a) atTop (nhds 0) :=
    (isLittleO_log_rpow_rpow_atTop (0 : ℝ) ha).tendsto_div_nhds_zero
  have hnat := hreal.comp tendsto_natCast_atTop_atTop
  apply hnat.congr'
  filter_upwards [eventually_gt_atTop 1] with n hn
  simp only [Function.comp_apply, Real.rpow_zero]

private theorem tendsto_L_div_nat_rpow_zero (a : ℝ) (ha : 0 < a) :
    Tendsto (fun n : ℕ ↦ L n / (n : ℝ) ^ a) atTop (nhds 0) := by
  have hreal : Tendsto
      (fun x : ℝ ↦ Real.log x ^ (1 : ℝ) / x ^ a) atTop (nhds 0) :=
    (isLittleO_log_rpow_rpow_atTop (1 : ℝ) ha).tendsto_div_nhds_zero
  have hnat := hreal.comp tendsto_natCast_atTop_atTop
  apply hnat.congr'
  filter_upwards [eventually_gt_atTop 1] with n hn
  simp only [Function.comp_apply, L, Real.rpow_one]

private theorem tendsto_L_sq_div_nat_rpow_zero (a : ℝ) (ha : 0 < a) :
    Tendsto (fun n : ℕ ↦ L n ^ 2 / (n : ℝ) ^ a) atTop (nhds 0) := by
  have hreal : Tendsto
      (fun x : ℝ ↦ Real.log x ^ (2 : ℝ) / x ^ a) atTop (nhds 0) :=
    (isLittleO_log_rpow_rpow_atTop (2 : ℝ) ha).tendsto_div_nhds_zero
  have hnat := hreal.comp tendsto_natCast_atTop_atTop
  change Tendsto
    (fun n : ℕ ↦ Real.log (n : ℝ) ^ (2 : ℝ) / (n : ℝ) ^ a)
      atTop (nhds 0) at hnat
  simpa [L, Real.rpow_natCast] using hnat

private theorem y_cube_div_nat_eq_inv_rpow {n : ℕ} (hn : 0 < n) :
    y n ^ 3 / (n : ℝ) = 1 / (n : ℝ) ^ (1 / 3 : ℝ) := by
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hpow :
      ((n : ℝ) ^ (2 / 9 : ℝ)) ^ 3 *
          (n : ℝ) ^ (1 / 3 : ℝ) = (n : ℝ) := by
    calc
      ((n : ℝ) ^ (2 / 9 : ℝ)) ^ 3 *
          (n : ℝ) ^ (1 / 3 : ℝ) =
        (((n : ℝ) ^ (2 / 9 : ℝ) *
            (n : ℝ) ^ (2 / 9 : ℝ)) *
          ((n : ℝ) ^ (2 / 9 : ℝ) *
            (n : ℝ) ^ (1 / 3 : ℝ))) := by ring
      _ = (n : ℝ) ^ ((2 / 9 : ℝ) + 2 / 9) *
          (n : ℝ) ^ ((2 / 9 : ℝ) + 1 / 3) := by
        rw [Real.rpow_add hnR, Real.rpow_add hnR]
      _ = (n : ℝ) ^ (((2 / 9 : ℝ) + 2 / 9) +
          ((2 / 9 : ℝ) + 1 / 3)) := by
        rw [← Real.rpow_add hnR]
      _ = (n : ℝ) := by norm_num [Real.rpow_one]
  unfold y
  field_simp [(Real.rpow_pos_of_pos hnR (1 / 3 : ℝ)).ne', hnR.ne']
  nlinarith

private theorem census_mul_y_sq_expansion
    (Cprom Cbank n : ℕ) (hn : 0 < n) :
    censusRatioMajorant Cprom Cbank n * y n ^ 2 =
      (Cprom : ℝ) * (1 / (n : ℝ) ^ (1 / 3 : ℝ)) +
        3 * (Cbank : ℝ) *
          (L n / (n : ℝ) ^ (1 / 3 : ℝ) +
            2 * (1 / (n : ℝ) ^ (1 / 3 : ℝ))) := by
  rw [censusRatioMajorant]
  rw [show
    (((Cprom : ℝ) + 3 * (Cbank : ℝ) * (L n + 2)) * y n /
        (n : ℝ)) * y n ^ 2 =
      ((Cprom : ℝ) + 3 * (Cbank : ℝ) * (L n + 2)) *
        (y n ^ 3 / (n : ℝ)) by ring]
  rw [y_cube_div_nat_eq_inv_rpow hn]
  ring

/-- The concrete census still vanishes after the reciprocal `y²` conversion. -/
theorem tendsto_censusRatioMajorant_mul_y_sq_zero (Cprom Cbank : ℕ) :
    Tendsto (fun n : ℕ ↦ censusRatioMajorant Cprom Cbank n * y n ^ 2)
      atTop (nhds 0) := by
  let a : ℝ := 1 / 3
  have ha : 0 < a := by norm_num [a]
  have hzero := tendsto_inv_nat_rpow_zero a ha
  have hlog := tendsto_L_div_nat_rpow_zero a ha
  have hsum : Tendsto
      (fun n : ℕ ↦
        (Cprom : ℝ) * (1 / (n : ℝ) ^ a) +
          3 * (Cbank : ℝ) *
            (L n / (n : ℝ) ^ a + 2 * (1 / (n : ℝ) ^ a)))
      atTop (nhds 0) := by
    simpa only [mul_zero, add_zero] using
      (hzero.const_mul (Cprom : ℝ)).add
        ((hlog.add (hzero.const_mul 2)).const_mul (3 * (Cbank : ℝ)))
  apply hsum.congr'
  filter_upwards [eventually_gt_atTop 0] with n hn
  simpa only [a] using (census_mul_y_sq_expansion Cprom Cbank n hn).symm

/-- The unweighted census ratio itself tends to zero.  This follows from
the stronger `y²`-weighted estimate because `1 ≤ y²` eventually. -/
theorem tendsto_censusRatioMajorant_zero (Cprom Cbank : ℕ) :
    Tendsto (censusRatioMajorant Cprom Cbank) atTop (nhds 0) := by
  refine squeeze_zero' ?_ ?_
    (tendsto_censusRatioMajorant_mul_y_sq_zero Cprom Cbank)
  · filter_upwards [eventually_gt_atTop 0] with n hn
    unfold censusRatioMajorant
    have hL : 0 ≤ L n := Real.log_nonneg (by exact_mod_cast hn)
    have hcoef : 0 ≤
        (Cprom : ℝ) + 3 * (Cbank : ℝ) * (L n + 2) := by positivity
    exact div_nonneg
      (mul_nonneg hcoef (Scale.y_pos hn).le) (by positivity)
  · filter_upwards [eventually_gt_atTop 0] with n hn
    have hyOne : (1 : ℝ) ≤ y n := by
      unfold y
      exact Real.one_le_rpow (by exact_mod_cast hn) (by norm_num)
    have hySq : (1 : ℝ) ≤ y n ^ 2 := by nlinarith
    have hcensus0 : 0 ≤ censusRatioMajorant Cprom Cbank n := by
      unfold censusRatioMajorant
      have hL : 0 ≤ L n := Real.log_nonneg (by exact_mod_cast hn)
      have hcoef : 0 ≤
          (Cprom : ℝ) + 3 * (Cbank : ℝ) * (L n + 2) := by positivity
      exact div_nonneg
        (mul_nonneg hcoef (Scale.y_pos hn).le) (by positivity)
    calc
      censusRatioMajorant Cprom Cbank n =
          censusRatioMajorant Cprom Cbank n * 1 := by ring
      _ ≤ censusRatioMajorant Cprom Cbank n * y n ^ 2 :=
        mul_le_mul_of_nonneg_left hySq hcensus0

/-- The same error survives the extra moving-low harmonic loss
`log (L n)`. -/
theorem tendsto_censusRatioMajorant_mul_y_sq_mul_logL_zero
    (Cprom Cbank : ℕ) :
    Tendsto (fun n : ℕ ↦
      censusRatioMajorant Cprom Cbank n * y n ^ 2 * Real.log (L n))
      atTop (nhds 0) := by
  let a : ℝ := 1 / 3
  have ha : 0 < a := by norm_num [a]
  have hlog := tendsto_L_div_nat_rpow_zero a ha
  have hlogSq := tendsto_L_sq_div_nat_rpow_zero a ha
  let upper : ℕ → ℝ := fun n ↦
    (Cprom : ℝ) * (L n / (n : ℝ) ^ a) +
      3 * (Cbank : ℝ) *
        (L n ^ 2 / (n : ℝ) ^ a +
          2 * (L n / (n : ℝ) ^ a))
  have hupper : Tendsto upper atTop (nhds 0) := by
    dsimp only [upper]
    simpa only [mul_zero, add_zero] using
      (hlog.const_mul (Cprom : ℝ)).add
        ((hlogSq.add (hlog.const_mul 2)).const_mul (3 * (Cbank : ℝ)))
  have hLTop : Tendsto L atTop atTop := by
    simpa only [L] using
      Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hLge : ∀ᶠ n : ℕ in atTop, (1 : ℝ) ≤ L n :=
    hLTop.eventually (eventually_ge_atTop 1)
  refine squeeze_zero' ?_ ?_ hupper
  · filter_upwards [eventually_gt_atTop 0, hLge] with n hn hLn
    rw [census_mul_y_sq_expansion Cprom Cbank n hn]
    exact mul_nonneg (by positivity) (Real.log_nonneg hLn)
  · filter_upwards [eventually_gt_atTop 0, hLge] with n hn hLn
    have hlogL : Real.log (L n) ≤ L n :=
      (Real.log_le_sub_one_of_pos (zero_lt_one.trans_le hLn)).trans (by linarith)
    rw [census_mul_y_sq_expansion Cprom Cbank n hn]
    dsimp only [upper, a]
    have hbase0 : 0 ≤
        (Cprom : ℝ) * (1 / (n : ℝ) ^ (1 / 3 : ℝ)) +
          3 * (Cbank : ℝ) *
            (L n / (n : ℝ) ^ (1 / 3 : ℝ) +
              2 * (1 / (n : ℝ) ^ (1 / 3 : ℝ))) := by
      positivity
    calc
      ((Cprom : ℝ) * (1 / (n : ℝ) ^ (1 / 3 : ℝ)) +
            3 * (Cbank : ℝ) *
              (L n / (n : ℝ) ^ (1 / 3 : ℝ) +
                2 * (1 / (n : ℝ) ^ (1 / 3 : ℝ)))) * Real.log (L n) ≤
          ((Cprom : ℝ) * (1 / (n : ℝ) ^ (1 / 3 : ℝ)) +
            3 * (Cbank : ℝ) *
              (L n / (n : ℝ) ^ (1 / 3 : ℝ) +
                2 * (1 / (n : ℝ) ^ (1 / 3 : ℝ)))) * L n :=
        mul_le_mul_of_nonneg_left hlogL hbase0
      _ = (Cprom : ℝ) * (L n / (n : ℝ) ^ (1 / 3 : ℝ)) +
          3 * (Cbank : ℝ) *
            (L n ^ 2 / (n : ℝ) ^ (1 / 3 : ℝ) +
              2 * (L n / (n : ℝ) ^ (1 / 3 : ℝ))) := by ring



theorem tendsto_guardRateMajorant_mul_logL_zero
    (Cprom Cbank : ℕ) (constant : ℝ) :
    Tendsto (fun n : ℕ ↦ constant *
      (censusRatioMajorant Cprom Cbank n * y n ^ 2) * Real.log (L n))
      atTop (nhds 0) := by
  have hc : Tendsto (fun _n : ℕ ↦ constant) atTop (nhds constant) :=
    tendsto_const_nhds
  have h := hc.mul
    (tendsto_censusRatioMajorant_mul_y_sq_mul_logL_zero Cprom Cbank)
  simpa only [mul_zero, mul_assoc] using h

















end

end Erdos390.Full.GuardSquarefreeErrorRate

end

/- Source module: Erdos390.Full.PaperGuardPowerCorrectionMixture -/
section


/-!
# Guard deletion for the global prime-power correction row

The useful object in Lemma 7.5 is not the full valuation covariance by
itself, but its difference from the squarefree covariance.  This file applies
the family-summed tagged-mixture perturbation theorem separately to the `VV`
and `II` rows and then subtracts them.  The estimate is global: arbitrary
common component weights and every between-cell covariance term are included.
-/

open scoped BigOperators

namespace Erdos390.Full.PaperGuardCensus

open ArithmeticModel ArithmeticBandGeometry FiniteProbability PaperBridgeFit

noncomputable section





theorem guardPowerCorrectionRowError_nonneg {K d : ℝ}
    (hK : 0 ≤ K) (hd : 0 ≤ d) :
    0 ≤ guardPowerCorrectionRowError K d := by
  unfold guardPowerCorrectionRowError
  positivity

variable {Head : Type*} [Fintype Head]



end

end Erdos390.Full.PaperGuardCensus

end

/- Source module: Erdos390.Full.PaperBridgeCanonicalGuardPowerCorrection -/
section


/-!
# The canonical guard contribution to the prime-power correction row

The prime-power reference law in Lemma 8.4 lives on the unguarded raw
structured cells, whereas the medium-only bridge law lives on the literal
guard-deleted cells.  This file compares the two tagged mixtures without
changing their (post-tilt) component weights.  The comparison includes all
between-component covariance terms.

No arbitrary `BridgeData` is declared canonical.  The finite comparison is
stated under the exact equality between its `sampleData` field and the
canonical constructor from `PaperGuardedStructuredSample`; all dependent
sample-space identifications are then obtained from
`canonicalSampleData_cellFinset`.
-/

open scoped BigOperators
open Filter Topology

set_option maxRecDepth 5000

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

open ArithmeticModel ArithmeticBandGeometry FiniteProbability
open PrimePowerCovariance PrimePowerCovariance.BoundedValuationLaw
open StructuredCellValuationLaw StructuredCells
open PaperGuardCensus GuardedUniformCell
open ValuationScoreDomination

namespace BridgeData



variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]
  (B : BridgeData Head Band)



























private theorem guardPowerCorrectionRowError_eq (K d : ℝ) :
    PaperGuardCensus.guardPowerCorrectionRowError K d =
      (K ^ 2 + K) * (7 * d + 2 * d ^ 2) := by
  unfold PaperGuardCensus.guardPowerCorrectionRowError
  ring

private theorem tendsto_L_sq_div_y_zero :
    Tendsto (fun n : ℕ ↦ Scale.L n ^ 2 / ArithmeticModel.y n)
      atTop (nhds 0) := by
  have hreal : Tendsto
      (fun x : ℝ ↦ Real.log x ^ (2 : ℝ) / x ^ (2 / 9 : ℝ))
        atTop (nhds 0) :=
    (isLittleO_log_rpow_rpow_atTop (2 : ℝ) (by norm_num : (0 : ℝ) < 2 / 9))
      |>.tendsto_div_nhds_zero
  have hnat := hreal.comp tendsto_natCast_atTop_atTop
  change Tendsto
    (fun n : ℕ ↦ Real.log (n : ℝ) ^ (2 : ℝ) /
      (n : ℝ) ^ (2 / 9 : ℝ)) atTop (nhds 0) at hnat
  simpa [Scale.L, ArithmeticModel.y, Real.rpow_natCast] using hnat

private theorem eventually_L_sq_le_y :
    ∀ᶠ n : ℕ in atTop, Scale.L n ^ 2 ≤ ArithmeticModel.y n := by
  have hratio := tendsto_L_sq_div_y_zero.eventually
    (eventually_le_nhds (by norm_num : (0 : ℝ) < 1))
  filter_upwards [hratio, eventually_gt_atTop 0] with n hratio hn
  have hy : 0 < ArithmeticModel.y n := Scale.y_pos hn
  exact (div_le_iff₀ hy).mp hratio |>.trans_eq (one_mul _)

/-- The `p ≤ y` guard loss is still negligible after the moving-low
factor `log L`; equivalently it is `o(1 / log L)`, the scale of the low
arithmetic center. -/
theorem tendsto_guardPowerCorrectionWeightedMajorant_mul_logL_zero
    (Cprom Cbank : ℕ) {Cenv D : ℝ}
    (hCenv : 0 ≤ Cenv) (hD : 0 ≤ D) :
    Tendsto (fun n : ℕ ↦
      guardPowerCorrectionWeightedMajorant Cprom Cbank Cenv D n *
        Real.log (Scale.L n)) atTop (nhds 0) := by
  let constant := 9 * D * (Cenv ^ 2 + Cenv)
  have hconstant : 0 ≤ constant := by
    dsimp only [constant]
    positivity
  have hdT : Tendsto (fun n : ℕ ↦
      D * PaperGuardCensus.censusRatioMajorant Cprom Cbank n)
      atTop (nhds 0) := by
    simpa only [mul_zero] using tendsto_const_nhds.mul
      (GuardSquarefreeErrorRate.tendsto_censusRatioMajorant_zero
        Cprom Cbank)
  have hdle : ∀ᶠ n : ℕ in atTop,
      D * PaperGuardCensus.censusRatioMajorant Cprom Cbank n ≤ 1 :=
    hdT.eventually (eventually_le_nhds (by norm_num))
  have hLTop : Tendsto Scale.L atTop atTop := by
    simpa only [Scale.L] using
      Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hLge : ∀ᶠ n : ℕ in atTop, (1 : ℝ) ≤ Scale.L n :=
    hLTop.eventually (eventually_ge_atTop 1)
  have hlog0 : ∀ᶠ n : ℕ in atTop, 0 ≤ Real.log (Scale.L n) :=
    hLge.mono fun n hn ↦ Real.log_nonneg hn
  have hupper :=
    GuardSquarefreeErrorRate.tendsto_guardRateMajorant_mul_logL_zero
      Cprom Cbank constant
  refine squeeze_zero' ?_ ?_ hupper
  · filter_upwards [eventually_gt_atTop 0, hlog0] with n hn hlog
    have hLn : 0 ≤ Scale.L n := Real.log_nonneg (by exact_mod_cast hn)
    have hcensus : 0 ≤
        PaperGuardCensus.censusRatioMajorant Cprom Cbank n := by
      unfold PaperGuardCensus.censusRatioMajorant
      have hcoef : 0 ≤ (Cprom : ℝ) +
          3 * (Cbank : ℝ) * (Scale.L n + 2) := by positivity
      exact div_nonneg
        (mul_nonneg hcoef (Scale.y_pos hn).le) (by positivity)
    exact mul_nonneg
      (mul_nonneg (by positivity)
        (PaperGuardCensus.guardPowerCorrectionRowError_nonneg
          (mul_nonneg hCenv hLn)
          (mul_nonneg hD hcensus))) hlog
  · filter_upwards [eventually_gt_atTop 0, hdle, hLge,
      eventually_L_sq_le_y, hlog0] with n hn hdOne hLn hLsq hlog
    let census := PaperGuardCensus.censusRatioMajorant Cprom Cbank n
    let d := D * census
    let K := Cenv * Scale.L n
    have hcensus : 0 ≤ census := by
      dsimp only [census]
      unfold PaperGuardCensus.censusRatioMajorant
      have hL0 : 0 ≤ Scale.L n := Real.log_nonneg (by exact_mod_cast hn)
      have hcoef : 0 ≤ (Cprom : ℝ) +
          3 * (Cbank : ℝ) * (Scale.L n + 2) := by positivity
      exact div_nonneg
        (mul_nonneg hcoef (Scale.y_pos hn).le) (by positivity)
    have hd0 : 0 ≤ d := mul_nonneg hD hcensus
    have hK0 : 0 ≤ K := mul_nonneg hCenv (zero_le_one.trans hLn)
    have hdpoly : 7 * d + 2 * d ^ 2 ≤ 9 * d := by
      nlinarith [mul_nonneg hd0 (sub_nonneg.mpr hdOne)]
    have hKpoly : K ^ 2 + K ≤
        (Cenv ^ 2 + Cenv) * Scale.L n ^ 2 := by
      dsimp only [K]
      have haux : 0 ≤ Cenv * Scale.L n * (Scale.L n - 1) :=
        mul_nonneg (mul_nonneg hCenv (zero_le_one.trans hLn))
          (sub_nonneg.mpr hLn)
      nlinarith
    have herror :
        PaperGuardCensus.guardPowerCorrectionRowError K d ≤
          constant * census * Scale.L n ^ 2 := by
      rw [guardPowerCorrectionRowError_eq]
      calc
        (K ^ 2 + K) * (7 * d + 2 * d ^ 2) ≤
            (K ^ 2 + K) * (9 * d) :=
          mul_le_mul_of_nonneg_left hdpoly (add_nonneg (sq_nonneg K) hK0)
        _ ≤ ((Cenv ^ 2 + Cenv) * Scale.L n ^ 2) * (9 * d) :=
          mul_le_mul_of_nonneg_right hKpoly (mul_nonneg (by norm_num) hd0)
        _ = constant * census * Scale.L n ^ 2 := by
          dsimp only [constant, d, census]
          ring
    have hyNat : (yNat n : ℝ) ≤ ArithmeticModel.y n :=
      Nat.floor_le (Scale.y_pos hn).le
    have herror0 : 0 ≤
        PaperGuardCensus.guardPowerCorrectionRowError K d :=
      PaperGuardCensus.guardPowerCorrectionRowError_nonneg hK0 hd0
    have hbase :
        (yNat n : ℝ) *
            PaperGuardCensus.guardPowerCorrectionRowError K d ≤
          constant * (census * ArithmeticModel.y n ^ 2) := by
      calc
        (yNat n : ℝ) *
            PaperGuardCensus.guardPowerCorrectionRowError K d ≤
          ArithmeticModel.y n *
            PaperGuardCensus.guardPowerCorrectionRowError K d :=
          mul_le_mul_of_nonneg_right hyNat herror0
        _ ≤ ArithmeticModel.y n *
            (constant * census * Scale.L n ^ 2) :=
          mul_le_mul_of_nonneg_left herror (Scale.y_pos hn).le
        _ ≤ ArithmeticModel.y n *
            (constant * census * ArithmeticModel.y n) := by
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hLsq
              (mul_nonneg hconstant hcensus))
            (Scale.y_pos hn).le
        _ = constant * (census * ArithmeticModel.y n ^ 2) := by ring
    have hbaseLog := mul_le_mul_of_nonneg_right hbase hlog
    simpa only [guardPowerCorrectionWeightedMajorant, K, d, census,
      constant, mul_assoc] using hbaseLog



end BridgeData

end

end Erdos390.Full.PaperBridgeFit

end

theorem solution :
∀ (Cprom Cbank : Nat) {Cenv D : Real},
  LE.le.{0} (0 : Real) Cenv →
    LE.le.{0} (0 : Real) D →
      Filter.Tendsto.{0, 0}
        (fun n =>
          HMul.hMul.{0, 0, 0}
            (Erdos390.Full.PaperBridgeFit.BridgeData.guardPowerCorrectionWeightedMajorant Cprom Cbank Cenv D n)
            (Real.log (Erdos390.Full.Scale.L n)))
        Filter.atTop.{0} (nhds.{0} (0 : Real)) := by
  exact @Erdos390.Full.PaperBridgeFit.BridgeData.tendsto_guardPowerCorrectionWeightedMajorant_mul_logL_zero
