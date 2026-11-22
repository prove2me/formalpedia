-- Prove2me | solution 1 for Erdos390.Full.PaperBridgeFit.BridgeData.vectorFieldProfilesMarkedConstant_le_majorant
-- status  : ACCEPTED   (prove)
-- author  : @doctosil
-- created : 2026-09-17T15:21:36.560015+00:00
-- url     : https://prove2.me/submissions/8a045eee-83d5-4e9c-8f1c-ec0da45d686f

import Mathlib
import Definitions.Def_erdos390_source_bank_interface
import Definitions.Def_erdos390_dickman_step_function
import Theorems.Thm_MediumPNT
import Definitions.Def_erdos390_analytic_foundations_001
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_product_bound
import Theorems.Thm_Erdos390_Full_DickmanBasic_rho_pos_on_zero_five
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_secondDerivative_first_bound
import Definitions.Def_erdos390_analytic_foundations_002
import Definitions.Def_erdos390_analytic_foundations_004
import Definitions.Def_erdos390_analytic_foundations_005

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

























theorem pairCovarianceScale_nonneg {E : ℝ} (hE : 0 ≤ E) :
    0 ≤ pairCovarianceScale E := by
  unfold pairCovarianceScale
  have hrho : 0 ≤ 1 / DickmanBasic.rho DickmanBasic.U := by
    exact one_div_nonneg.mpr DickmanBasic.rho_U_pos.le
  positivity















end

end Erdos390.Full.PaperPrimePowerChamberError

end

/- Source module: Erdos390.Full.PaperProposition87MarkedProfilesMajorant -/
section


/-!
# An ambient-independent majorant for the Proposition 8.7 marked row

The signed-profile and nuisance errors are `o(1 / log L)`, while the total
harmonic mass is `O(log L)`.  This file records the exact finite inequality
which converts those rates into one constant independent of the ambient
integer.
-/

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

set_option maxHeartbeats 1200000

namespace BridgeData

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]
  (B : BridgeData Head Band)



/-- Deterministic majorization.  No limit, filter, or unspecified `O(1)`
constant occurs in this statement. -/
theorem vectorFieldProfilesMarkedConstant_le_majorant
    {H K Eprofile CF Cprod CKernel R Rmax Cmarked gammaNuisance
      gammaFloor CinvOrd Tband Tslow Vlower Creg : ℝ}
    (hH : 0 ≤ H) (hK : 0 ≤ K)
    (hE : 0 ≤ Eprofile) (hEone : Eprofile ≤ 1)
    (hEH : Eprofile * H ≤ 1)
    (hCF : 0 ≤ CF) (hCprod : 0 ≤ Cprod)
    (hCKernel : 0 ≤ CKernel)
    (hR : 0 ≤ R) (hRRmax : R ≤ Rmax)
    (hM : 0 ≤ Cmarked) (hMone : Cmarked ≤ 1)
    (hMH : Cmarked * H ≤ 1)
    (hgammaFloor : 0 < gammaFloor)
    (hgamma : 0 < gammaNuisance)
    (hgammaCompare : gammaFloor ≤ gammaNuisance)
    (hCinvOrd : 0 ≤ CinvOrd) (hTband : 0 ≤ Tband)
    (hTslow : 0 ≤ Tslow) (hVlower : 0 < Vlower)
    (hCreg : 0 ≤ Creg) (hW : 1 < B.sampleData.W) :
    B.vectorFieldProfilesMarkedConstant H K Eprofile CF Cprod CKernel R
        Cmarked gammaNuisance CinvOrd Tband Tslow Vlower Creg ≤
      B.vectorFieldProfilesMarkedMajorant K CF Cprod CKernel Rmax
        gammaFloor CinvOrd Tband Tslow Vlower Creg := by
  let A : ℝ := 1 / DickmanBasic.rho DickmanBasic.U
  let d : ℝ :=
    Real.sqrt (Fintype.card (NuisanceCoord B.HeadIndex) : ℝ)
  let S : ℝ := 7 + Creg * K
  have hA : 0 ≤ A := by
    dsimp only [A]
    exact one_div_nonneg.mpr DickmanBasic.rho_U_pos.le
  have hd : 0 ≤ d := by dsimp only [d]; positivity
  have hS : 0 ≤ S := by dsimp only [S]; positivity
  have hRmax : 0 ≤ Rmax := hR.trans hRRmax
  have hWinv0 : 0 ≤ 1 / (B.sampleData.W : ℝ) := by positivity
  have hWinv1 : 1 / (B.sampleData.W : ℝ) ≤ 1 := by
    have hcast : (1 : ℝ) ≤ B.sampleData.W := by
      exact_mod_cast hW.le
    simpa only [one_div_one] using
      one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hcast
  have hInvGamma : 1 / gammaNuisance ≤ 1 / gammaFloor :=
    one_div_le_one_div_of_le hgammaFloor hgammaCompare
  have hE2 : Eprofile ^ 2 ≤ Eprofile := by
    nlinarith [mul_nonneg hE (sub_nonneg.mpr hEone)]
  have hM2 : Cmarked ^ 2 ≤ 1 := by
    nlinarith [mul_nonneg hM (sub_nonneg.mpr hMone)]
  have hpairOne :
      PaperPrimePowerChamberError.pairCovarianceScale Eprofile ≤
        2 + 2 * A := by
    unfold PaperPrimePowerChamberError.pairCovarianceScale
    dsimp only [A]
    have hcoef : 0 ≤
        1 + 2 * (1 / DickmanBasic.rho DickmanBasic.U) := by positivity
    calc
      Eprofile * (1 + 2 * (1 / DickmanBasic.rho DickmanBasic.U)) +
          Eprofile ^ 2 ≤
        1 * (1 + 2 * (1 / DickmanBasic.rho DickmanBasic.U)) + 1 :=
          add_le_add (mul_le_mul_of_nonneg_right hEone hcoef)
            (hE2.trans hEone)
      _ = 2 + 2 * A := by dsimp only [A]; ring
  have hpairH :
      PaperPrimePowerChamberError.pairCovarianceScale Eprofile * H ≤
        2 + 2 * A := by
    unfold PaperPrimePowerChamberError.pairCovarianceScale
    dsimp only [A]
    have hcoef : 0 ≤
        1 + 2 * (1 / DickmanBasic.rho DickmanBasic.U) := by positivity
    calc
      (Eprofile * (1 + 2 * (1 / DickmanBasic.rho DickmanBasic.U)) +
          Eprofile ^ 2) * H =
        (Eprofile * H) *
            (1 + 2 * (1 / DickmanBasic.rho DickmanBasic.U)) +
          Eprofile * (Eprofile * H) := by ring
      _ ≤ 1 * (1 + 2 * (1 / DickmanBasic.rho DickmanBasic.U)) +
          1 * 1 := by
        exact add_le_add
          (mul_le_mul_of_nonneg_right hEH hcoef)
          (mul_le_mul hEone hEH (mul_nonneg hE hH) (by norm_num))
      _ = 2 + 2 * A := by dsimp only [A]; ring
  have hSquare :
      (A + 2 * Eprofile) ^ 2 ≤ (A + 2) ^ 2 := by
    have hbase : A + 2 * Eprofile ≤ A + 2 := by linarith
    exact (sq_le_sq₀ (by positivity) (by positivity)).2 hbase
  have hTailFast :
      ((A + 2 * Eprofile) ^ 2 + Cprod) *
          (1 / (B.sampleData.W : ℝ)) ≤
        (A + 2) ^ 2 + Cprod := by
    calc
      ((A + 2 * Eprofile) ^ 2 + Cprod) *
          (1 / (B.sampleData.W : ℝ)) ≤
        ((A + 2) ^ 2 + Cprod) * 1 := by
          exact mul_le_mul (add_le_add hSquare le_rfl) hWinv1
            hWinv0 (add_nonneg (sq_nonneg _) hCprod)
      _ = _ := by ring
  have hTailSlow :
      (((A + 2 * Eprofile) ^ 2 + CKernel) * (1 + Creg)) *
          (1 / (B.sampleData.W : ℝ)) ≤
        ((A + 2) ^ 2 + CKernel) * (1 + Creg) := by
    have hbase :
        ((A + 2 * Eprofile) ^ 2 + CKernel) * (1 + Creg) ≤
          ((A + 2) ^ 2 + CKernel) * (1 + Creg) :=
      mul_le_mul_of_nonneg_right (add_le_add hSquare le_rfl)
        (by positivity)
    calc
      (((A + 2 * Eprofile) ^ 2 + CKernel) * (1 + Creg)) *
          (1 / (B.sampleData.W : ℝ)) ≤
        (((A + 2) ^ 2 + CKernel) * (1 + Creg)) * 1 := by
          exact mul_le_mul hbase hWinv1 hWinv0 (by positivity)
      _ = _ := by ring
  have hFastNuisance :
      ((d * (Cmarked * H)) / gammaNuisance) * (d * Cmarked) ≤
        d ^ 2 / gammaFloor := by
    have hMH_M : (Cmarked * H) * Cmarked ≤ 1 := by
      exact (mul_le_mul hMH hMone hM (by norm_num)).trans_eq
        (one_mul 1)
    rw [div_eq_mul_inv, div_eq_mul_inv]
    calc
      (d * (Cmarked * H) * gammaNuisance⁻¹) * (d * Cmarked) =
          d ^ 2 * ((Cmarked * H) * Cmarked) * gammaNuisance⁻¹ := by ring
      _ ≤ d ^ 2 * 1 * gammaFloor⁻¹ := by
        exact mul_le_mul
          (mul_le_mul_of_nonneg_left hMH_M (sq_nonneg d))
          (by simpa only [one_div] using hInvGamma)
          (inv_nonneg.mpr hgamma.le) (mul_nonneg (sq_nonneg d) (by norm_num))
      _ = d ^ 2 * gammaFloor⁻¹ := by ring
  have hSlowNuisance :
      ((d * (Cmarked * S)) / gammaNuisance) * (d * Cmarked) ≤
        d ^ 2 * S / gammaFloor := by
    rw [div_eq_mul_inv, div_eq_mul_inv]
    calc
      (d * (Cmarked * S) * gammaNuisance⁻¹) * (d * Cmarked) =
          (d ^ 2 * S) * (Cmarked ^ 2) * gammaNuisance⁻¹ := by ring
      _ ≤ (d ^ 2 * S) * 1 * gammaFloor⁻¹ := by
        exact mul_le_mul
          (mul_le_mul_of_nonneg_left hM2
            (mul_nonneg (sq_nonneg d) hS))
          (by simpa only [one_div] using hInvGamma)
          (inv_nonneg.mpr hgamma.le)
          (mul_nonneg (mul_nonneg (sq_nonneg d) hS) (by norm_num))
      _ = d ^ 2 * S * gammaFloor⁻¹ := by ring
  let fastActual := fastProfilesMarkedConstant d H K Eprofile CF Cprod R
    Cmarked gammaNuisance (1 / (B.sampleData.W : ℝ))
  let fastBound := Cprod * K + CF + 4 * (2 + 2 * A) + 2 +
    ((A + 2) ^ 2 + Cprod) + Rmax + d ^ 2 / gammaFloor
  have hfast : fastActual ≤ fastBound := by
    dsimp only [fastActual, fastBound, fastProfilesMarkedConstant]
    dsimp only [A, d] at hpairH hTailFast hFastNuisance ⊢
    nlinarith
  let slowActual := slowProfilesMarkedConstant d Creg K R Eprofile CF
    CKernel Cmarked gammaNuisance (1 / (B.sampleData.W : ℝ))
  let slowBound := CKernel * S + CF * (1 + Creg) +
    4 * (2 + 2 * A) * S + 2 * (1 + Creg) +
    ((A + 2) ^ 2 + CKernel) * (1 + Creg) +
    (1 + Creg) * Rmax + d ^ 2 * S / gammaFloor
  have hslow : slowActual ≤ slowBound := by
    dsimp only [slowActual, slowBound, slowProfilesMarkedConstant,
      actualSquarefreeMarkedConstant]
    dsimp only [S, A, d] at hpairOne hTailSlow hSlowNuisance ⊢
    have hpairScaled := mul_le_mul_of_nonneg_right hpairOne
      (by positivity : 0 ≤ 7 + Creg * K)
    have hRscaled := mul_le_mul_of_nonneg_left hRRmax (by positivity)
    nlinarith
  have hfast0 : 0 ≤ fastActual := by
    dsimp only [fastActual, fastProfilesMarkedConstant]
    have hpair0 :=
      PaperPrimePowerChamberError.pairCovarianceScale_nonneg hE
    positivity
  have hslow0 : 0 ≤ slowActual := by
    dsimp only [slowActual, slowProfilesMarkedConstant,
      actualSquarefreeMarkedConstant]
    have hpair0 :=
      PaperPrimePowerChamberError.pairCovarianceScale_nonneg hE
    positivity
  unfold vectorFieldProfilesMarkedConstant
    vectorFieldProfilesMarkedMajorant
  dsimp only [A, d, S, fastActual, fastBound, slowActual, slowBound]
  exact add_le_add
    (mul_le_mul_of_nonneg_right hfast (mul_nonneg hCinvOrd hTband))
    (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right hslow B.w_pos.le)
      (div_nonneg hTslow hVlower.le))









end BridgeData

end

end Erdos390.Full.PaperBridgeFit

end

universe u_1 u_2
theorem solution :
∀ {Head : Type u_1} {Band : Type u_2} [inst : Fintype.{u_1} Head] [inst_1 : DecidableEq.{u_1 + 1} Head]
  [inst_2 : Fintype.{u_2} Band] [inst_3 : DecidableEq.{u_2 + 1} Band]
  (B : Erdos390.Full.PaperBridgeFit.BridgeData.{u_1, u_2} Head Band)
  {H K Eprofile CF Cprod CKernel R Rmax Cmarked gammaNuisance gammaFloor CinvOrd Tband Tslow Vlower Creg : Real},
  LE.le.{0} (0 : Real) H →
    LE.le.{0} (0 : Real) K →
      LE.le.{0} (0 : Real) Eprofile →
        LE.le.{0} Eprofile (1 : Real) →
          LE.le.{0} (HMul.hMul.{0, 0, 0} Eprofile H) (1 : Real) →
            LE.le.{0} (0 : Real) CF →
              LE.le.{0} (0 : Real) Cprod →
                LE.le.{0} (0 : Real) CKernel →
                  LE.le.{0} (0 : Real) R →
                    LE.le.{0} R Rmax →
                      LE.le.{0} (0 : Real) Cmarked →
                        LE.le.{0} Cmarked (1 : Real) →
                          LE.le.{0} (HMul.hMul.{0, 0, 0} Cmarked H) (1 : Real) →
                            LT.lt.{0} (0 : Real) gammaFloor →
                              LT.lt.{0} (0 : Real) gammaNuisance →
                                LE.le.{0} gammaFloor gammaNuisance →
                                  LE.le.{0} (0 : Real) CinvOrd →
                                    LE.le.{0} (0 : Real) Tband →
                                      LE.le.{0} (0 : Real) Tslow →
                                        LT.lt.{0} (0 : Real) Vlower →
                                          LE.le.{0} (0 : Real) Creg →
                                            LT.lt.{0} (1 : Nat)
                                                (Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1}
                                                  (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B)) →
                                              LE.le.{0}
                                                (Erdos390.Full.PaperBridgeFit.BridgeData.vectorFieldProfilesMarkedConstant.{u_1,
                                                    u_2}
                                                  B H K Eprofile CF Cprod CKernel R Cmarked gammaNuisance CinvOrd Tband
                                                  Tslow Vlower Creg)
                                                (Erdos390.Full.PaperBridgeFit.BridgeData.vectorFieldProfilesMarkedMajorant.{u_1,
                                                    u_2}
                                                  B K CF Cprod CKernel Rmax gammaFloor CinvOrd Tband Tslow Vlower Creg) := by
  exact @Erdos390.Full.PaperBridgeFit.BridgeData.vectorFieldProfilesMarkedConstant_le_majorant
