-- Prove2me | solution 1 for Erdos390.Full.PaperBridgeFit.BridgeData.physicalPowerCorrectionMixtureBudget_le_inv_mul_rowError
-- status  : ACCEPTED   (prove)
-- author  : @doctosil
-- created : 2026-09-17T15:20:30.853207+00:00
-- url     : https://prove2.me/submissions/5c0e3d2a-b69c-4acc-ab82-884eaa65d96b

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

/- Source module: Erdos390.Full.PaperBridgePhysicalPowerCorrectionRow -/
section


/-!
# The prime-power correction row through the residual physical tilt

This file keeps the actual partition-function-reweighted component weights
fixed and compares the residual physical tilt component by component.  The
high prime-power columns are summed geometrically before the tagged-mixture
covariance algebra is applied.  Consequently the final comparison is for the
literal `VV-II` row, including all between-component covariance terms.
-/

open scoped BigOperators
open Filter Topology

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

open ArithmeticModel ArithmeticBandGeometry FiniteProbability
open PrimePowerCovariance PrimePowerCovariance.BoundedValuationLaw
open PrimePowerCutoffCovariance ValuationCutoff LocalFugacityBounds
open PrimeSums
open PrimePowerLcmGeometry

namespace BridgeData

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]
  (B : BridgeData Head Band)













set_option maxHeartbeats 2000000 in
/-- The exact tagged-mixture budget is one marked-prime factor smaller than
the public weighted-row error.  All estimates are finite and pointwise; in
particular, no asymptotic `O`-constant or change of mixture weights is hidden
in this contraction. -/
theorem physicalPowerCorrectionMixtureBudget_le_inv_mul_rowError
    {epsilon G : ℝ} {n W p : ℕ}
    (hepsilon : 0 ≤ epsilon) (hsmall : 8 * epsilon ≤ 1)
    (hG : 0 ≤ G) (hW : 1 < W) (hp : p ∈ primeBand n W) :
    physicalPowerCorrectionMixtureBudget epsilon G n W p ≤
      (1 / (p : ℝ)) * physicalPowerCorrectionRowError epsilon G n W := by
  let e : ℝ := 8 * epsilon
  let H : ℝ := bandReciprocalSum n W
  let S : ℝ := bandReciprocalSquareSum n W
  let w : ℝ := 1 / (W : ℝ)
  let x : ℝ := 1 / (p : ℝ)
  let Q : ℝ := quadraticHalfMass
  let R : ℝ := (1 + Q) * (1 + G) ^ 2
  let F : ℝ := e * R * (H + 1) * w
  have he0 : 0 ≤ e := by dsimp only [e]; positivity
  have he1 : e ≤ 1 := by simpa only [e] using hsmall
  have hH0 : 0 ≤ H := by
    dsimp only [H, bandReciprocalSum]
    positivity
  have hS0 : 0 ≤ S := by
    dsimp only [S, bandReciprocalSquareSum]
    positivity
  have hW0 : 0 < (W : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt hW)
  have hw0 : 0 ≤ w := by dsimp only [w]; positivity
  have hw1 : w ≤ 1 := by
    dsimp only [w]
    exact (div_le_one hW0).2 (by exact_mod_cast hW.le)
  have hpPrime := prime_of_mem_primeBand hp
  have hp0 : 0 < (p : ℝ) := by exact_mod_cast hpPrime.pos
  have hx0 : 0 ≤ x := by dsimp only [x]; positivity
  have hxp : x ≤ w := by
    dsimp only [x, w]
    exact one_div_le_one_div_of_le hW0
      (by exact_mod_cast (cutoff_lt_of_mem_primeBand hp).le)
  have hx1 : x ≤ 1 := hxp.trans hw1
  have hSle : S ≤ w := by
    dsimp only [S, w]
    exact bandReciprocalSquareSum_le n W hW.le
  have hQ0 : 0 ≤ Q := by
    dsimp only [Q]
    exact quadraticHalfMass_nonneg
  have hR0 : 0 ≤ R := by dsimp only [R]; positivity
  have hF0 : 0 ≤ F := by dsimp only [F]; positivity
  have hGone : G ≤ (1 + G) ^ 2 := by nlinarith [sq_nonneg G]
  have hGtwo : G ^ 2 ≤ (1 + G) ^ 2 := by nlinarith
  have hGle : G ≤ R := by
    dsimp only [R]
    calc
      G ≤ (1 + G) ^ 2 := hGone
      _ ≤ (1 + Q) * (1 + G) ^ 2 := by
        nlinarith [mul_nonneg hQ0 (sq_nonneg (1 + G))]
  have hGtwoLe : G ^ 2 ≤ R := by
    dsimp only [R]
    calc
      G ^ 2 ≤ (1 + G) ^ 2 := hGtwo
      _ ≤ (1 + Q) * (1 + G) ^ 2 := by
        nlinarith [mul_nonneg hQ0 (sq_nonneg (1 + G))]
  have hGQLe : G * Q ≤ R := by
    dsimp only [R]
    have hprod := mul_le_mul hGone (show Q ≤ 1 + Q by linarith)
      hQ0 (sq_nonneg (1 + G))
    nlinarith
  have hHle : H ≤ H + 1 := by linarith
  have honeH : (1 : ℝ) ≤ H + 1 := by linarith
  have hxSqW : x ^ 2 ≤ w := by
    have hxx : x * x ≤ x * 1 := mul_le_mul_of_nonneg_left hx1 hx0
    nlinarith [hxp]
  have hxCubeW : x ^ 3 ≤ w := by
    have hmul := mul_le_mul hx1 hxSqW (sq_nonneg x)
      (by norm_num : (0 : ℝ) ≤ 1)
    nlinarith
  have hxwW : x * w ≤ w := by nlinarith [mul_le_mul_of_nonneg_right hx1 hw0]
  have hexe : e * x ≤ w := by
    have hex : e * x ≤ 1 * x := mul_le_mul_of_nonneg_right he1 hx0
    nlinarith [hxp]
  have hexw : e * (x * w) ≤ w := by
    calc
      e * (x * w) ≤ 1 * (x * w) :=
        mul_le_mul_of_nonneg_right he1 (mul_nonneg hx0 hw0)
      _ = x * w := one_mul _
      _ ≤ w := hxwW
  have hmono (a b c : ℝ) (ha0 : 0 ≤ a) (ha : a ≤ R)
      (hb0 : 0 ≤ b) (hb : b ≤ H + 1)
      (hc0 : 0 ≤ c) (hc : c ≤ w) :
      x * e * a * b * c ≤ x * F := by
    dsimp only [F]
    have hxe : 0 ≤ x * e := mul_nonneg hx0 he0
    calc
      x * e * a * b * c ≤ x * e * R * b * c := by gcongr
      _ ≤ x * e * R * (H + 1) * c := by gcongr
      _ ≤ x * e * R * (H + 1) * w := by gcongr
      _ = x * (e * R * (H + 1) * w) := by ring
  have mGHx : e * G * x ^ 2 * H ≤ x * F := by
    (convert hmono G H x hG hGle hH0 hHle hx0 hxp using 1; ring_nf)
  have mGtwoHx : e * G ^ 2 * x ^ 2 * H ≤ x * F := by
    (convert hmono (G ^ 2) H x (sq_nonneg G) hGtwoLe hH0 hHle hx0 hxp
      using 1; ring_nf)
  have meGtwoHx : e ^ 2 * G ^ 2 * x ^ 2 * H ≤ x * F := by
    (convert hmono (G ^ 2) H (e * x) (sq_nonneg G) hGtwoLe hH0 hHle
      (mul_nonneg he0 hx0) hexe using 1; ring_nf)
  have mGx : e * G * x ^ 2 ≤ x * F := by
    (convert hmono G 1 x hG hGle (by norm_num) honeH hx0 hxp using 1; ring_nf)
  have mGtwoXsq : e * G ^ 2 * x ^ 3 ≤ x * F := by
    (convert hmono (G ^ 2) 1 (x ^ 2) (sq_nonneg G) hGtwoLe
      (by norm_num) honeH (sq_nonneg x) hxSqW using 1; ring_nf)
  have mGS : e * G * x * S ≤ x * F := by
    (convert hmono G 1 S hG hGle (by norm_num) honeH hS0 hSle using 1; ring_nf)
  have mGtwoS : e * G ^ 2 * x * S ≤ x * F := by
    (convert hmono (G ^ 2) 1 S (sq_nonneg G) hGtwoLe
      (by norm_num) honeH hS0 hSle using 1; ring_nf)
  have mGxS : e * G * x ^ 2 * S ≤ x * F := by
    have hxs0 : 0 ≤ x * S := mul_nonneg hx0 hS0
    have hxsW : x * S ≤ w := by
      have := mul_le_mul hx1 hSle hS0 (by norm_num : (0 : ℝ) ≤ 1)
      nlinarith
    (convert hmono G 1 (x * S) hG hGle (by norm_num) honeH hxs0 hxsW
      using 1; ring_nf)
  have mGtwoXS : e * G ^ 2 * x ^ 2 * S ≤ x * F := by
    have hxs0 : 0 ≤ x * S := mul_nonneg hx0 hS0
    have hxsW : x * S ≤ w := by
      have := mul_le_mul hx1 hSle hS0 (by norm_num : (0 : ℝ) ≤ 1)
      nlinarith
    (convert hmono (G ^ 2) 1 (x * S) (sq_nonneg G) hGtwoLe
      (by norm_num) honeH hxs0 hxsW using 1; ring_nf)
  have mGQx : e * (G * Q) * x ^ 2 ≤ x * F := by
    (convert hmono (G * Q) 1 x (mul_nonneg hG hQ0) hGQLe
      (by norm_num) honeH hx0 hxp using 1; ring_nf)
  have mGtwoXcube : e * G ^ 2 * x ^ 4 ≤ x * F := by
    (convert hmono (G ^ 2) 1 (x ^ 3) (sq_nonneg G) hGtwoLe
      (by norm_num) honeH (by positivity) hxCubeW using 1; ring_nf)
  have mGtwoW : e * G ^ 2 * x * w ≤ x * F := by
    (convert hmono (G ^ 2) 1 w (sq_nonneg G) hGtwoLe
      (by norm_num) honeH hw0 le_rfl using 1; ring_nf)
  have meGtwoW : e ^ 2 * G ^ 2 * x * w ≤ x * F := by
    (convert hmono (G ^ 2) 1 (e * w) (sq_nonneg G) hGtwoLe
      (by norm_num) honeH (mul_nonneg he0 hw0)
      (by nlinarith [mul_le_mul_of_nonneg_right he1 hw0]) using 1; ring_nf)
  have mGtwoXW : e * G ^ 2 * x ^ 2 * w ≤ x * F := by
    (convert hmono (G ^ 2) 1 (x * w) (sq_nonneg G) hGtwoLe
      (by norm_num) honeH (mul_nonneg hx0 hw0) hxwW using 1; ring_nf)
  have meGtwoXW : e ^ 2 * G ^ 2 * x ^ 2 * w ≤ x * F := by
    (convert hmono (G ^ 2) 1 (e * (x * w)) (sq_nonneg G) hGtwoLe
      (by norm_num) honeH (by positivity) hexw using 1; ring_nf)
  change
    physicalPowerCorrectionMixtureBudget epsilon G n W p ≤
      (1 / (p : ℝ)) * physicalPowerCorrectionRowError epsilon G n W
  unfold physicalPowerCorrectionMixtureBudget physicalPowerCorrectionRowError
  dsimp only
  change _ ≤ x * (200 * e * (1 + Q) * (1 + G) ^ 2 * (H + 1) * w)
  have htarget : x * (200 * e * (1 + Q) * (1 + G) ^ 2 *
      (H + 1) * w) = 200 * (x * F) := by
    dsimp only [F, R]
    ring
  rw [htarget]
  nlinarith [mGHx, mGtwoHx, meGtwoHx, mGx, mGtwoXsq,
    mGS, mGtwoS, mGxS, mGtwoXS, mGQx, mGtwoXcube,
    mGtwoW, meGtwoW, mGtwoXW, meGtwoXW]









































end BridgeData

end

end Erdos390.Full.PaperBridgeFit

end

theorem solution :
∀ {epsilon G : Real} {n W p : Nat},
  LE.le.{0} (0 : Real) epsilon →
    LE.le.{0} (HMul.hMul.{0, 0, 0} (8 : Real) epsilon) (1 : Real) →
      LE.le.{0} (0 : Real) G →
        LT.lt.{0} (1 : Nat) W →
          Membership.mem.{0, 0} (Erdos390.Full.ArithmeticModel.primeBand n W) p →
            LE.le.{0} (Erdos390.Full.PaperBridgeFit.BridgeData.physicalPowerCorrectionMixtureBudget epsilon G n W p)
              (HMul.hMul.{0, 0, 0} (HDiv.hDiv.{0, 0, 0} (1 : Real) ↑p)
                (Erdos390.Full.PaperBridgeFit.BridgeData.physicalPowerCorrectionRowError epsilon G n W)) := by
  exact @Erdos390.Full.PaperBridgeFit.BridgeData.physicalPowerCorrectionMixtureBudget_le_inv_mul_rowError
