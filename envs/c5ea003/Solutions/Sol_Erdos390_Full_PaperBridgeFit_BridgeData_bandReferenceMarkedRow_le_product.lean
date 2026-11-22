-- Prove2me | solution 1 for Erdos390.Full.PaperBridgeFit.BridgeData.bandReferenceMarkedRow_le_product
-- status  : ACCEPTED   (prove)
-- author  : @doctosil
-- created : 2026-09-17T15:15:31.4853+00:00
-- url     : https://prove2.me/submissions/3b20fcd9-75ed-4594-97f8-8fdfa288edbc

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

/- Source module: Erdos390.Full.PaperActualFastMarkedRowProfiles -/
section


/-!
# Ordinary-fast marked rows from the literal analytic inputs

The fast solve is bounded in the ordinary raw-band norm.  Its reference
kernel row is nevertheless `O(1/p)`: the product bound for the Dickman
kernel supplies the missing factor `t_r`, whose prime sum is bounded.  Only
the signed profile error pays the full harmonic mass, exactly as in the
paper's `epsilon(n) log L -> 0` bookkeeping.
-/

open scoped BigOperators

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

open ArithmeticModel ArithmeticBandGeometry FiniteProbability
open PrimePowerCovariance PaperWeightedInverseExport
open SquarefreeCovarianceReference

namespace BridgeData

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]
  (B : BridgeData Head Band)









/-- The product Dickman-kernel bound gives an `O(1/p)` reference row even
for an ordinary, rather than sharp, raw-band coefficient. -/
theorem bandReferenceMarkedRow_le_product
    (q : B.RawBandGauge) {CF Cprod K : ℝ}
    (hCprod : 0 ≤ Cprod)
    (hbandT : PrimeSums.bandTReciprocalSum
      B.sampleData.n B.sampleData.W ≤ K)
    (hF : ∀ r : BandPrime B.sampleData.n B.sampleData.W,
      |DickmanBasic.F (tPrime B.sampleData.n r.1)| ≤ CF)
    (hKernel : ∀ r s : BandPrime B.sampleData.n B.sampleData.W,
      |ConditionedPoissonLimit.covarianceKernel
          (tPrime B.sampleData.n r.1)
          (tPrime B.sampleData.n s.1)| ≤
        Cprod * tPrime B.sampleData.n r.1 * tPrime B.sampleData.n s.1)
    {p : ℕ} (hp : p ∈ primeBand B.sampleData.n B.sampleData.W) :
    |∑ r : BandPrime B.sampleData.n B.sampleData.W,
        q.1 (B.partition.band r) *
          squarefreeReferenceEntry B.sampleData.n p r.1| ≤
      ‖q‖ * (Cprod * K + CF) * (1 / (p : ℝ)) := by
  let pp : BandPrime B.sampleData.n B.sampleData.W := ⟨p, hp⟩
  have hpR : (0 : ℝ) < p := by
    exact_mod_cast (prime_of_mem_primeBand hp).pos
  have htp : 0 ≤ tPrime B.sampleData.n p :=
    PaperPrimePowerRow.tPrime_nonneg_of_mem_primeBand B.n_gt_one hp
  have htp1 : tPrime B.sampleData.n p ≤ 1 :=
    PaperPrimePowerRow.tPrime_le_one_of_mem_primeBand B.n_gt_one hp
  have hq (r : BandPrime B.sampleData.n B.sampleData.W) :
      |q.1 (B.partition.band r)| ≤ ‖q‖ := by
    simpa only [Real.norm_eq_abs] using norm_le_pi_norm q.1
      (B.partition.band r)
  have hentry (r : BandPrime B.sampleData.n B.sampleData.W) :
      |squarefreeReferenceEntry B.sampleData.n p r.1| ≤
        Cprod * (1 / (p : ℝ)) *
            (tPrime B.sampleData.n r.1 / (r.1 : ℝ)) +
          if p = r.1 then CF * (1 / (p : ℝ)) else 0 := by
    have hrR : (0 : ℝ) < r.1 := by
      exact_mod_cast (prime_of_mem_primeBand r.2).pos
    by_cases hpr : p = r.1
    · subst p
      unfold squarefreeReferenceEntry squarefreeKernelEntry
      rw [if_pos rfl, if_pos rfl]
      calc
        |DickmanBasic.F (tPrime B.sampleData.n r.1) / (r.1 : ℝ) +
            ConditionedPoissonLimit.covarianceKernel
              (tPrime B.sampleData.n r.1) (tPrime B.sampleData.n r.1) /
                ((r.1 : ℝ) * (r.1 : ℝ))| ≤
          |DickmanBasic.F (tPrime B.sampleData.n r.1) / (r.1 : ℝ)| +
            |ConditionedPoissonLimit.covarianceKernel
              (tPrime B.sampleData.n r.1) (tPrime B.sampleData.n r.1) /
                ((r.1 : ℝ) * (r.1 : ℝ))| := abs_add_le _ _
        _ ≤ CF * (1 / (r.1 : ℝ)) +
            Cprod * (1 / (r.1 : ℝ)) *
              (tPrime B.sampleData.n r.1 / (r.1 : ℝ)) := by
          rw [abs_div, abs_of_pos hrR, abs_div,
            abs_of_pos (mul_pos hrR hrR)]
          have hK := hKernel r r
          calc
            _ ≤ CF / (r.1 : ℝ) +
                (Cprod * tPrime B.sampleData.n r.1 *
                  tPrime B.sampleData.n r.1) /
                    ((r.1 : ℝ) * (r.1 : ℝ)) :=
              add_le_add
                (div_le_div_of_nonneg_right (hF r) hrR.le)
                (div_le_div_of_nonneg_right hK
                  (mul_nonneg hrR.le hrR.le))
            _ ≤ CF * (1 / (r.1 : ℝ)) +
                Cprod * (1 / (r.1 : ℝ)) *
                  (tPrime B.sampleData.n r.1 / (r.1 : ℝ)) := by
              have ht1 := PaperPrimePowerRow.tPrime_le_one_of_mem_primeBand
                B.n_gt_one r.2
              have ht0 := PaperPrimePowerRow.tPrime_nonneg_of_mem_primeBand
                B.n_gt_one r.2
              field_simp [hrR.ne']
              nlinarith [mul_nonneg ht0 (sub_nonneg.mpr ht1)]
        _ = Cprod * (1 / (r.1 : ℝ)) *
              (tPrime B.sampleData.n r.1 / (r.1 : ℝ)) +
            CF * (1 / (r.1 : ℝ)) := by ring
    · unfold squarefreeReferenceEntry squarefreeKernelEntry
      rw [if_neg hpr, if_neg hpr, abs_div,
        abs_of_pos (mul_pos hpR hrR)]
      have hK := hKernel pp r
      calc
        _ ≤ (Cprod * tPrime B.sampleData.n p *
              tPrime B.sampleData.n r.1) / ((p : ℝ) * (r.1 : ℝ)) :=
          div_le_div_of_nonneg_right hK (mul_nonneg hpR.le hrR.le)
        _ ≤ Cprod * (1 / (p : ℝ)) *
              (tPrime B.sampleData.n r.1 / (r.1 : ℝ)) := by
          field_simp [hpR.ne', hrR.ne']
          exact mul_le_mul_of_nonneg_right
            (by simpa only [mul_one] using
              (mul_le_mul_of_nonneg_left htp1 hCprod))
            (PaperPrimePowerRow.tPrime_nonneg_of_mem_primeBand
              B.n_gt_one r.2)
        _ = _ := by ring
  calc
    |∑ r : BandPrime B.sampleData.n B.sampleData.W,
        q.1 (B.partition.band r) *
          squarefreeReferenceEntry B.sampleData.n p r.1| ≤
      ∑ r : BandPrime B.sampleData.n B.sampleData.W,
        |q.1 (B.partition.band r)| *
          |squarefreeReferenceEntry B.sampleData.n p r.1| := by
        calc
          _ ≤ ∑ r : BandPrime B.sampleData.n B.sampleData.W,
              |q.1 (B.partition.band r) *
                squarefreeReferenceEntry B.sampleData.n p r.1| :=
            Finset.abs_sum_le_sum_abs _ _
          _ = _ := by simp only [abs_mul]
    _ ≤ ∑ r : BandPrime B.sampleData.n B.sampleData.W,
        ‖q‖ * (Cprod * (1 / (p : ℝ)) *
            (tPrime B.sampleData.n r.1 / (r.1 : ℝ)) +
          if p = r.1 then CF * (1 / (p : ℝ)) else 0) := by
      apply Finset.sum_le_sum
      intro r hr
      exact mul_le_mul (hq r) (hentry r) (abs_nonneg _) (norm_nonneg q)
    _ = ‖q‖ * (Cprod * (1 / (p : ℝ)) *
          PrimeSums.bandTReciprocalSum B.sampleData.n B.sampleData.W +
        CF * (1 / (p : ℝ))) := by
      rw [← Finset.mul_sum]
      congr 1
      rw [Finset.sum_add_distrib]
      have hk :
          (∑ r : BandPrime B.sampleData.n B.sampleData.W,
            Cprod * (1 / (p : ℝ)) *
              (tPrime B.sampleData.n r.1 / (r.1 : ℝ))) =
          Cprod * (1 / (p : ℝ)) *
            PrimeSums.bandTReciprocalSum
              B.sampleData.n B.sampleData.W := by
        rw [← Finset.mul_sum]
        unfold PrimeSums.bandTReciprocalSum
        congr 1
        exact (Finset.sum_subtype
          (primeBand B.sampleData.n B.sampleData.W)
          (fun _ ↦ Iff.rfl)
          (fun r ↦ tPrime B.sampleData.n r / (r : ℝ))).symm
      have hdiag :
          (∑ r : BandPrime B.sampleData.n B.sampleData.W,
            if p = r.1 then CF * (1 / (p : ℝ)) else 0) =
          CF * (1 / (p : ℝ)) := by
        rw [Finset.sum_eq_single ⟨p, hp⟩]
        · simp
        · intro r hr hne
          have hval : p ≠ r.1 := by
            intro heq
            exact hne (Subtype.ext heq.symm)
          simp only [if_neg hval]
        · exact fun hnot ↦ (hnot (Finset.mem_univ _)).elim
      rw [hk, hdiag]
    _ ≤ ‖q‖ * (Cprod * (1 / (p : ℝ)) * K +
        CF * (1 / (p : ℝ))) := by
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg q)
      exact add_le_add_left
        (mul_le_mul_of_nonneg_left hbandT
          (mul_nonneg hCprod (one_div_nonneg.mpr hpR.le))) _
    _ = ‖q‖ * (Cprod * K + CF) * (1 / (p : ℝ)) := by ring



end BridgeData

end

end Erdos390.Full.PaperBridgeFit

end

universe u_1 u_2
theorem solution :
∀ {Head : Type u_1} {Band : Type u_2} [inst : Fintype.{u_1} Head] [inst_1 : DecidableEq.{u_1 + 1} Head]
  [inst_2 : Fintype.{u_2} Band] [inst_3 : DecidableEq.{u_2 + 1} Band]
  (B : Erdos390.Full.PaperBridgeFit.BridgeData.{u_1, u_2} Head Band)
  (q : ↥(Erdos390.Full.PaperBridgeFit.BridgeData.RawBandGauge.{u_1, u_2} B)) {CF Cprod K : Real},
  LE.le.{0} (0 : Real) Cprod →
    LE.le.{0}
        (Erdos390.Full.PrimeSums.bandTReciprocalSum
          (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
            (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B))
          (Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1}
            (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B)))
        K →
      (∀
          (r :
            Erdos390.Full.ArithmeticBandGeometry.BandPrime
              (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B))
              (Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1}
                (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B))),
          LE.le.{0}
            (abs.{0}
              (Erdos390.Full.DickmanBasic.F
                (Erdos390.Full.ArithmeticModel.tPrime
                  (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                    (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B))
                  (↑r : Nat))))
            CF) →
        (∀
            (r s :
              Erdos390.Full.ArithmeticBandGeometry.BandPrime
                (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                  (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B))
                (Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1}
                  (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B))),
            LE.le.{0}
              (abs.{0}
                (Erdos390.Full.ConditionedPoissonLimit.covarianceKernel
                  (Erdos390.Full.ArithmeticModel.tPrime
                    (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                      (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B))
                    (↑r : Nat))
                  (Erdos390.Full.ArithmeticModel.tPrime
                    (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                      (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B))
                    (↑s : Nat))))
              (HMul.hMul.{0, 0, 0}
                (HMul.hMul.{0, 0, 0} Cprod
                  (Erdos390.Full.ArithmeticModel.tPrime
                    (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                      (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B))
                    (↑r : Nat)))
                (Erdos390.Full.ArithmeticModel.tPrime
                  (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                    (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B))
                  (↑s : Nat)))) →
          ∀ {p : Nat},
            Membership.mem.{0, 0}
                (Erdos390.Full.ArithmeticModel.primeBand
                  (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                    (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B))
                  (Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1}
                    (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B)))
                p →
              LE.le.{0}
                (abs.{0}
                  (∑ r :
                    Erdos390.Full.ArithmeticBandGeometry.BandPrime
                      (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                        (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B))
                      (Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1}
                        (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B)),
                    HMul.hMul.{0, 0, 0}
                      ((↑q : Band → Real)
                        (Erdos390.Full.ArithmeticBandGeometry.Partition.band.{u_2}
                          (Erdos390.Full.PaperBridgeFit.BridgeData.partition.{u_1, u_2} B) r))
                      (Erdos390.Full.SquarefreeCovarianceReference.squarefreeReferenceEntry
                        (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                          (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B))
                        p (↑r : Nat))))
                (HMul.hMul.{0, 0, 0}
                  (HMul.hMul.{0, 0, 0} (Norm.norm.{u_2} q) (HAdd.hAdd.{0, 0, 0} (HMul.hMul.{0, 0, 0} Cprod K) CF))
                  (HDiv.hDiv.{0, 0, 0} (1 : Real) (↑p : Real))) := by
  exact @Erdos390.Full.PaperBridgeFit.BridgeData.bandReferenceMarkedRow_le_product
