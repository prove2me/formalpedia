-- Prove2me | solution 1 for Erdos390.Full.PaperPrimePowerRemainderRate.tendsto_primePowerChamberRemainder_zero_and_rate
-- status  : ACCEPTED   (prove)
-- author  : @doctosil
-- created : 2026-09-17T15:24:30.846032+00:00
-- url     : https://prove2.me/submissions/8e549c3c-1a4e-4362-b8ec-d0c531b6a99e

import Mathlib
import Definitions.Def_erdos390_source_bank_interface
import Definitions.Def_erdos390_dickman_step_function
import Theorems.Thm_MediumPNT
import Definitions.Def_erdos390_analytic_foundations_001
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_product_bound
import Theorems.Thm_Erdos390_Full_DickmanBasic_rho_pos_on_zero_five
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_secondDerivative_first_bound
import Definitions.Def_erdos390_analytic_foundations_004

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

theorem tendsto_coefficientScale_zero
    (B : ℝ) (W : ℕ) :
    Tendsto (fun n : ℕ ↦ coefficientScale B W n) atTop (nhds 0) := by
  have hLTop : Tendsto L atTop atTop := by
    simpa [L] using Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hInv : Tendsto (fun n : ℕ ↦ (L n)⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp hLTop
  have hconst : Tendsto
      (fun _n : ℕ ↦ (2 * B) * Real.exp (2 * B / Real.log (W : ℝ)))
      atTop (nhds ((2 * B) * Real.exp (2 * B / Real.log (W : ℝ)))) :=
    tendsto_const_nhds
  have hmul := hconst.mul hInv
  have hmul0 : Tendsto
      (fun n : ℕ ↦ (2 * B) * Real.exp (2 * B / Real.log (W : ℝ)) *
        (L n)⁻¹) atTop (nhds 0) := by
    simpa only [mul_zero] using hmul
  apply hmul0.congr'
  filter_upwards with n
  unfold coefficientScale
  ring

theorem tendsto_coefficientScale_mul_logL_zero
    (B : ℝ) (W : ℕ) :
    Tendsto (fun n : ℕ ↦
      coefficientScale B W n * Real.log (L n)) atTop (nhds 0) := by
  have hLTop : Tendsto L atTop atTop := by
    simpa [L] using Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hratioReal : Tendsto (fun x : ℝ ↦ Real.log x / x)
      atTop (nhds 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
  have hratio := hratioReal.comp hLTop
  have hconst : Tendsto
      (fun _n : ℕ ↦ (2 * B) * Real.exp (2 * B / Real.log (W : ℝ)))
      atTop (nhds ((2 * B) * Real.exp (2 * B / Real.log (W : ℝ)))) :=
    tendsto_const_nhds
  have hmul := hconst.mul hratio
  have hmul0 : Tendsto
      (fun n : ℕ ↦ (2 * B) * Real.exp (2 * B / Real.log (W : ℝ)) *
        (Real.log (L n) / L n)) atTop (nhds 0) := by
    simpa only [Function.comp_apply, mul_zero] using hmul
  apply hmul0.congr'
  filter_upwards with n
  unfold coefficientScale
  ring



/-- The common chamber remainder tends to zero and remains vanishing after
one harmonic loss. -/
theorem tendsto_primePowerChamberRemainder_zero_and_rate
    (epsilon : ℕ → ℝ) (G₀ B : ℝ) (W : ℕ)
    (hepsilon : Tendsto epsilon atTop (nhds 0))
    (hepsilonRate : Tendsto
      (fun n : ℕ ↦ epsilon n * Real.log (L n)) atTop (nhds 0)) :
    Tendsto (fun n : ℕ ↦
      primePowerChamberRemainder (epsilon n) G₀ (coefficientScale B W n))
        atTop (nhds 0) ∧
    Tendsto (fun n : ℕ ↦
      primePowerChamberRemainder (epsilon n) G₀ (coefficientScale B W n) *
        Real.log (L n)) atTop (nhds 0) := by
  let k : ℕ → ℝ := fun n ↦ coefficientScale B W n
  have hk := tendsto_coefficientScale_zero B W
  have hkRate := tendsto_coefficientScale_mul_logL_zero B W
  have hkSq : Tendsto (fun n : ℕ ↦ k n ^ 2) atTop (nhds 0) := by
    simpa only [zero_pow (by norm_num : (2 : ℕ) ≠ 0)] using hk.pow 2
  have hkSqRate : Tendsto
      (fun n : ℕ ↦ k n ^ 2 * Real.log (L n)) atTop (nhds 0) := by
    have hprod := hk.mul hkRate
    have hprod0 : Tendsto
        (fun n : ℕ ↦ k n * (k n * Real.log (L n)))
          atTop (nhds 0) := by
      simpa only [k, mul_zero] using hprod
    apply hprod0.congr'
    filter_upwards with n
    ring

  let loc : ℕ → ℝ := fun n ↦ localRestorationScale G₀ (k n)
  have hloc : Tendsto loc atTop (nhds 0) := by
    have hpoly : Tendsto (fun n : ℕ ↦ 2 * k n + k n ^ 2)
        atTop (nhds 0) := by
      simpa only [add_zero] using (tendsto_const_mul_zero 2 hk).add hkSq
    simpa only [loc, localRestorationScale] using
      tendsto_const_mul_zero G₀ hpoly
  have hlocRate : Tendsto
      (fun n : ℕ ↦ loc n * Real.log (L n)) atTop (nhds 0) := by
    have hpolyRate : Tendsto (fun n : ℕ ↦
        (2 * k n + k n ^ 2) * Real.log (L n)) atTop (nhds 0) := by
      have htwo := tendsto_const_mul_zero 2 hkRate
      have hadd := htwo.add hkSqRate
      have hadd0 : Tendsto (fun n : ℕ ↦
          2 * (coefficientScale B W n * Real.log (L n)) +
            k n ^ 2 * Real.log (L n)) atTop (nhds 0) := by
        simpa only [add_zero] using hadd
      apply hadd0.congr'
      filter_upwards with n
      ring
    have hbase := tendsto_const_mul_zero G₀ hpolyRate
    apply hbase.congr'
    filter_upwards with n
    unfold loc localRestorationScale
    ring
  let E : ℕ → ℝ := fun n ↦
    pairProbabilityScale (epsilon n) G₀ (k n)
  have hE : Tendsto E atTop (nhds 0) := by
    have hRloc := tendsto_const_mul_zero
      (1 / DickmanBasic.rho DickmanBasic.U) hloc
    have hsum := (hloc.add hepsilon).add hRloc
    have hsum0 : Tendsto (fun n : ℕ ↦
        loc n + epsilon n +
          (1 / DickmanBasic.rho DickmanBasic.U) * loc n)
        atTop (nhds 0) := by
      simpa only [add_zero] using hsum
    have htwo := tendsto_const_mul_zero 2 hsum0
    apply htwo.congr'
    filter_upwards with n
    unfold E pairProbabilityScale
    dsimp only [loc]
  have hERate : Tendsto (fun n : ℕ ↦ E n * Real.log (L n))
      atTop (nhds 0) := by
    have hRloc := tendsto_const_mul_zero
      (1 / DickmanBasic.rho DickmanBasic.U) hlocRate
    have hsum := (hlocRate.add hepsilonRate).add hRloc
    have hsum0 : Tendsto (fun n : ℕ ↦
        loc n * Real.log (L n) + epsilon n * Real.log (L n) +
          (1 / DickmanBasic.rho DickmanBasic.U) *
            (loc n * Real.log (L n))) atTop (nhds 0) := by
      simpa only [add_zero] using hsum
    have htwo := tendsto_const_mul_zero 2 hsum0
    apply htwo.congr'
    filter_upwards with n
    unfold E pairProbabilityScale
    dsimp only [loc]
    ring
  let ECov : ℕ → ℝ := fun n ↦ pairCovarianceScale (E n)
  have hESq : Tendsto (fun n : ℕ ↦ E n ^ 2) atTop (nhds 0) := by
    simpa only [zero_pow (by norm_num : (2 : ℕ) ≠ 0)] using hE.pow 2
  have hESqRate : Tendsto (fun n : ℕ ↦
      E n ^ 2 * Real.log (L n)) atTop (nhds 0) := by
    have hprod := hE.mul hERate
    have hprod0 : Tendsto
        (fun n : ℕ ↦ E n * (E n * Real.log (L n)))
          atTop (nhds 0) := by
      simpa only [mul_zero] using hprod
    apply hprod0.congr'
    filter_upwards with n
    ring
  have hECov : Tendsto ECov atTop (nhds 0) := by
    have hlin := tendsto_const_mul_zero
      (1 + 2 * (1 / DickmanBasic.rho DickmanBasic.U)) hE
    have hadd := hlin.add hESq
    have hadd0 : Tendsto (fun n : ℕ ↦
        (1 + 2 * (1 / DickmanBasic.rho DickmanBasic.U)) * E n + E n ^ 2)
        atTop (nhds 0) := by
      simpa only [add_zero] using hadd
    apply hadd0.congr'
    filter_upwards with n
    unfold ECov pairCovarianceScale
    ring
  have hECovRate : Tendsto
      (fun n : ℕ ↦ ECov n * Real.log (L n)) atTop (nhds 0) := by
    have hlin := tendsto_const_mul_zero
      (1 + 2 * (1 / DickmanBasic.rho DickmanBasic.U)) hERate
    have hadd := hlin.add hESqRate
    have hadd0 : Tendsto (fun n : ℕ ↦
        (1 + 2 * (1 / DickmanBasic.rho DickmanBasic.U)) *
            (E n * Real.log (L n)) +
          E n ^ 2 * Real.log (L n)) atTop (nhds 0) := by
      simpa only [add_zero] using hadd
    apply hadd0.congr'
    filter_upwards with n
    unfold ECov pairCovarianceScale
    ring
  constructor
  · have hagg := (tendsto_const_mul_zero 2 hECov).add hE
    have hagg0 : Tendsto (fun n : ℕ ↦ 2 * ECov n + E n)
        atTop (nhds 0) := by simpa only [add_zero] using hagg
    apply hagg0.congr'
    filter_upwards with n
    unfold primePowerChamberRemainder aggregateChamberScale
    dsimp only [ECov, E, k]
  · have hagg := (tendsto_const_mul_zero 2 hECovRate).add hERate
    have hagg0 : Tendsto (fun n : ℕ ↦
        2 * (ECov n * Real.log (L n)) + E n * Real.log (L n))
        atTop (nhds 0) := by simpa only [add_zero] using hagg
    apply hagg0.congr'
    filter_upwards with n
    unfold primePowerChamberRemainder aggregateChamberScale
    dsimp only [ECov, E, k]
    ring









end

end Erdos390.Full.PaperPrimePowerRemainderRate

end

theorem solution :
∀ (epsilon : Nat → Real) (G₀ B : Real) (W : Nat),
  Filter.Tendsto.{0, 0} epsilon Filter.atTop.{0} (nhds.{0} (0 : Real)) →
    Filter.Tendsto.{0, 0} (fun n => HMul.hMul.{0, 0, 0} (epsilon n) (Real.log (Erdos390.Full.Scale.L n)))
        Filter.atTop.{0} (nhds.{0} (0 : Real)) →
      And
        (Filter.Tendsto.{0, 0}
          (fun n =>
            Erdos390.Full.PaperPrimePowerFourDisplays.primePowerChamberRemainder (epsilon n) G₀
              (Erdos390.Full.PaperPrimePowerChamberError.coefficientScale B W n))
          Filter.atTop.{0} (nhds.{0} (0 : Real)))
        (Filter.Tendsto.{0, 0}
          (fun n =>
            HMul.hMul.{0, 0, 0}
              (Erdos390.Full.PaperPrimePowerFourDisplays.primePowerChamberRemainder (epsilon n) G₀
                (Erdos390.Full.PaperPrimePowerChamberError.coefficientScale B W n))
              (Real.log (Erdos390.Full.Scale.L n)))
          Filter.atTop.{0} (nhds.{0} (0 : Real))) := by
  exact @Erdos390.Full.PaperPrimePowerRemainderRate.tendsto_primePowerChamberRemainder_zero_and_rate
