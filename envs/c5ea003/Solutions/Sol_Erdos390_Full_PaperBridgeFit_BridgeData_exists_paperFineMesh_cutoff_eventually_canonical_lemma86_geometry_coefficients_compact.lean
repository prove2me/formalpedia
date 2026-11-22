-- Prove2me | solution 1 for Erdos390.Full.PaperBridgeFit.BridgeData.exists_paperFineMesh_cutoff_eventually_canonical_lemma86_geometry_coefficients_compact
-- status  : ACCEPTED   (prove)
-- author  : @doctosil
-- created : 2026-09-17T17:21:34.608575+00:00
-- url     : https://prove2.me/submissions/1feefdea-2531-44e9-8cc4-4ec56c22c5fa

import Definitions.Def_erdos390_remaining_analytic_propositions_002
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
import Theorems.Thm_Erdos390_Full_PaperBridgeFit_BridgeData_exists_cutoff_before_mesh_eventually_actualBandSchur_primeGraph_inverse_compact
import Theorems.Thm_Erdos390_Full_PaperBridgeFit_BridgeData_exists_cutoff_eventually_canonical_ordinary_perturbation_rows_compact
import Theorems.Thm_Erdos390_Full_PaperBridgeFit_BridgeData_exists_global_cutoff_eventually_canonical_nonstepSlowResidualRow_le_compact
import Theorems.Thm_Erdos390_Full_PaperBridgeFit_BridgeData_exists_structural_cutoff_eventually_canonical_actualFullQuotient_compact
import Theorems.Thm_Erdos390_Full_RegularMeshPrimeCutoffs_Mesh_canonicalPaperGeometricCutoff_eventually
import Theorems.Thm_Erdos390_Full_RegularMeshPrimeCutoffs_Mesh_canonicalPrimeAnchorCutoff_eventually
import Theorems.Thm_Erdos390_Full_RegularMeshPrimeCutoffs_Mesh_exists_fineMesh_cutoff_eventually_canonical_ordinaryProjectedRaw_inverse
import Theorems.Thm_Erdos390_Full_SquarefreeReferenceOperatorIdentification_referenceBandRow_eq_rawOperator





section
universe u_1
theorem Erdos390.Full.PaperBridgeFit.BridgeData.exists_structural_cutoff_eventually_canonical_actualFullQuotient : Erdos390.RemainingAnalyticGoal003_003.{u_1} := @Erdos390.Full.PaperBridgeFit.BridgeData.exists_structural_cutoff_eventually_canonical_actualFullQuotient_compact
end
section
universe u_1
theorem Erdos390.Full.PaperBridgeFit.BridgeData.exists_global_cutoff_eventually_canonical_nonstepSlowResidualRow_le : Erdos390.RemainingAnalyticGoal002_002.{u_1} := @Erdos390.Full.PaperBridgeFit.BridgeData.exists_global_cutoff_eventually_canonical_nonstepSlowResidualRow_le_compact
end
section
universe u_1 u_2
theorem Erdos390.Full.PaperBridgeFit.BridgeData.exists_cutoff_eventually_canonical_ordinary_perturbation_rows : Erdos390.RemainingAnalyticGoal001_015.{u_1, u_2} := @Erdos390.Full.PaperBridgeFit.BridgeData.exists_cutoff_eventually_canonical_ordinary_perturbation_rows_compact
end
section
universe u_1
theorem Erdos390.Full.PaperBridgeFit.BridgeData.exists_cutoff_before_mesh_eventually_actualBandSchur_primeGraph_inverse : Erdos390.RemainingAnalyticGoal001_012.{u_1} := @Erdos390.Full.PaperBridgeFit.BridgeData.exists_cutoff_before_mesh_eventually_actualBandSchur_primeGraph_inverse_compact
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

/- Source module: Erdos390.Full.PrimePowerCovariance -/
section


/-!
# Exact prime-power covariance expansion

This file replaces the algebraic part of the prime-power transfer by proofs
for the actual valuation and divisor indicators under an actual finite
probability law.  In particular, `V = I + J` and all `JI`, `IJ`, and `JJ`
covariances are finite sums of genuine prime-power indicator covariances.
-/

open scoped BigOperators

namespace Erdos390.Full

noncomputable section

namespace FiniteProbability

variable {Omega Iota : Type*} [Fintype Omega]













theorem covariance_zero_left (mu : FiniteProbability Omega) (G : Omega → ℝ) :
    mu.covariance (fun _ ↦ 0) G = 0 := by
  simp [covariance, expect]

theorem covariance_zero_right (mu : FiniteProbability Omega) (F : Omega → ℝ) :
    mu.covariance F (fun _ ↦ 0) = 0 := by
  simp [covariance, expect]

theorem covariance_add_left (mu : FiniteProbability Omega)
    (F G H : Omega → ℝ) :
    mu.covariance (fun omega ↦ F omega + G omega) H =
      mu.covariance F H + mu.covariance G H := by
  unfold covariance
  rw [mu.expect_add F G]
  rw [show (fun omega ↦ (F omega + G omega) * H omega) =
      fun omega ↦ F omega * H omega + G omega * H omega by
    funext omega
    ring]
  rw [mu.expect_add]
  ring







theorem covariance_sum_left (mu : FiniteProbability Omega)
    (s : Finset Iota) (F : Iota → Omega → ℝ) (G : Omega → ℝ) :
    mu.covariance (fun omega ↦ ∑ i ∈ s, F i omega) G =
      ∑ i ∈ s, mu.covariance (F i) G := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [mu.covariance_zero_left]
  | @insert i s hi ih =>
      simp only [Finset.sum_insert hi]
      rw [mu.covariance_add_left, ih]

theorem covariance_sum_right (mu : FiniteProbability Omega)
    (F : Omega → ℝ) (s : Finset Iota) (G : Iota → Omega → ℝ) :
    mu.covariance F (fun omega ↦ ∑ i ∈ s, G i omega) =
      ∑ i ∈ s, mu.covariance F (G i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [mu.covariance_zero_right]
  | @insert i s hi ih =>
      simp only [Finset.sum_insert hi]
      rw [mu.covariance_add_right, ih]



end FiniteProbability

namespace PrimePowerCovariance

open ArithmeticModel



namespace BoundedValuationLaw

variable {Omega : Type*} [Fintype Omega] {M : ℕ}













































end BoundedValuationLaw

end PrimePowerCovariance

end

end Erdos390.Full

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

/- Source module: Erdos390.Lemma84 -/
section


/-!
# The finite-dimensional core of Lemma 8.4

This file formalizes only the algebraic part of the moving-low-cell
arithmetic quotient argument.  The Poisson--Dickman gap, prime
quadrature, and marked covariance estimates occur below as fields of an
explicit input structure.  Thus this file contains no postulate claiming
those analytic results.
-/

namespace Erdos390.Lemma84

open scoped BigOperators

noncomputable section

section WeightedBands

variable {Prime Band : Type*}
variable [Fintype Prime] [Fintype Band]
variable [DecidableEq Prime] [DecidableEq Band]



namespace WeightedBandData

variable (d : WeightedBandData Prime Band)























































theorem bandNormSq_nonneg (x : Band → ℝ) : 0 ≤ d.bandNormSq x := by
  unfold bandNormSq bandInner
  apply Finset.sum_nonneg
  intro j hj
  have hH : 0 ≤ d.mass j := by
    unfold mass
    apply Finset.sum_nonneg
    intro p hp
    exact le_of_lt (d.weight_pos p)
  nlinarith [sq_nonneg (x j)]















theorem bandInner_comm (x y : Band → ℝ) :
    d.bandInner x y = d.bandInner y x := by
  apply Finset.sum_congr rfl
  intro j hj
  ring

theorem bandInner_add_right (x y z : Band → ℝ) :
    d.bandInner x (fun j => y j + z j) =
      d.bandInner x y + d.bandInner x z := by
  unfold bandInner
  calc
    (∑ j, d.mass j * x j * (y j + z j)) =
        ∑ j, (d.mass j * x j * y j + d.mass j * x j * z j) := by
          apply Finset.sum_congr rfl
          intro j hj
          ring
    _ = _ := Finset.sum_add_distrib

theorem bandInner_smul_right (a : ℝ) (x y : Band → ℝ) :
    d.bandInner x (fun j => a * y j) = a * d.bandInner x y := by
  unfold bandInner
  calc
    (∑ j, d.mass j * x j * (a * y j)) =
        ∑ j, a * (d.mass j * x j * y j) := by
          apply Finset.sum_congr rfl
          intro j hj
          ring
    _ = _ := (Finset.mul_sum Finset.univ _ a).symm

theorem bandNormSq_add (x y : Band → ℝ) :
    d.bandNormSq (fun j => x j + y j) =
      d.bandNormSq x + d.bandNormSq y + 2 * d.bandInner x y := by
  unfold bandNormSq
  rw [d.bandInner_add_right]
  have haddLeft :
      d.bandInner (fun j => x j + y j) x =
        d.bandInner x x + d.bandInner y x := by
    rw [d.bandInner_comm, d.bandInner_add_right]
    rw [d.bandInner_comm x x, d.bandInner_comm x y]
  have haddRight :
      d.bandInner (fun j => x j + y j) y =
        d.bandInner x y + d.bandInner y y := by
    rw [d.bandInner_comm, d.bandInner_add_right]
    rw [d.bandInner_comm y x, d.bandInner_comm y y]
  rw [haddLeft, haddRight, d.bandInner_comm y x]
  ring

theorem bandNormSq_smul (a : ℝ) (x : Band → ℝ) :
    d.bandNormSq (fun j => a * x j) = a ^ 2 * d.bandNormSq x := by
  unfold bandNormSq
  rw [d.bandInner_smul_right]
  rw [d.bandInner_comm, d.bandInner_smul_right]
  rw [d.bandInner_comm]
  ring













theorem gaugePart_inGauge (b : Band → ℝ) (hA : d.centerEnergy ≠ 0) :
    d.inGauge (d.gaugePart b) := by
  have hE : d.bandInner d.center d.center ≠ 0 := by
    simpa [centerEnergy, bandNormSq] using hA
  have hfun : d.gaugePart b = fun j =>
      b j + (-d.gaugeCoefficient b) * d.center j := by
    funext j
    simp only [gaugePart]
    ring
  unfold inGauge
  rw [hfun, d.bandInner_add_right, d.bandInner_smul_right]
  unfold gaugeCoefficient centerEnergy bandNormSq
  field_simp [hE]
  ring

theorem gauge_decomposition (b : Band → ℝ) (j : Band) :
    d.gaugePart b j + d.gaugeCoefficient b * d.center j = b j := by
  simp only [gaugePart]
  ring

theorem band_distance_expansion (q : Band → ℝ) (lambda mu : ℝ)
    (hq : d.inGauge q) :
    d.bandNormSq (fun j => q j + (lambda - mu) * d.center j) =
      d.bandNormSq q + (lambda - mu) ^ 2 * d.centerEnergy := by
  rw [d.bandNormSq_add, d.bandNormSq_smul,
    d.bandInner_smul_right]
  have hcross : d.bandInner q d.center = 0 := by
    rw [d.bandInner_comm]
    exact hq
  rw [hcross]
  unfold centerEnergy
  ring

/-- The gauge part is the exact best weighted approximation modulo the
center direction. -/
theorem gaugePart_best_distance (b : Band → ℝ) (mu : ℝ)
    (hA : d.centerEnergy ≠ 0) :
    d.bandNormSq (d.gaugePart b) ≤
      d.bandNormSq (fun j => b j - mu * d.center j) := by
  let q : Band → ℝ := d.gaugePart b
  let lambda : ℝ := d.gaugeCoefficient b
  have hq : d.inGauge q := by
    simpa [q] using d.gaugePart_inGauge b hA
  have hrewrite : (fun j => b j - mu * d.center j) =
      fun j => q j + (lambda - mu) * d.center j := by
    funext j
    have hd := d.gauge_decomposition b j
    dsimp only [q, lambda]
    linarith
  rw [hrewrite, d.band_distance_expansion q lambda mu hq]
  have hcenter : 0 ≤ d.centerEnergy := d.bandNormSq_nonneg d.center
  have hterm : 0 ≤ (lambda - mu) ^ 2 * d.centerEnergy :=
    mul_nonneg (sq_nonneg _) hcenter
  linarith

/-!
## Conditional bridge

The next structure is the exact boundary between the finite argument and
the presently external analytic work.  Its fields are a leading
Poisson--Dickman/quadrature form, an actual marked covariance form, the
nuisance loss, and quantitative comparisons between them.  No field is
the desired quotient conclusion.
-/













end WeightedBandData

end WeightedBands

end

end Erdos390.Lemma84

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

/- Source module: Erdos390.Full.MovingLowGaugeTransfer -/
section


/-!
# Moving-low arithmetic/continuum gauge transfer

This file isolates the normalization which is delicate at the moving low
cell.  An additive estimate for the arithmetic center is not enough because
the center itself tends to zero.  We first prove a quantitative relative
center estimate from separate estimates for `H` and `H * alpha`.  We then
write the sharp conjugate of the weighted gauge projection exactly and
compare two such projections through their normalized weights
`omega_j = H_j * alpha_j^2`.

No limiting mesh, covariance gap, or inverse is assumed in this module.
-/

open scoped BigOperators

noncomputable section

namespace Erdos390.Full.MovingLowGaugeTransfer

open Erdos390.Lemma84
open PositiveCellTransfer
open PrimeSums
open PrimeBandQuadrature
open MovingLowMomentQuadrature

section RelativeCenter

variable {n W : ℕ} {Band : Type*} [Fintype Band] [DecidableEq Band]
variable {P : ArithmeticBandGeometry.Partition n W Band}









end RelativeCenter

section SharpProjection

variable {Band : Type*} [Fintype Band] [DecidableEq Band]











omit [DecidableEq Band] in
/-- The sharp conjugate is just subtraction of the `omega`-weighted mean.
This is the finite arithmetic identity
`S^{-1} P_{alpha,H} S = I - 1 omega^T/(1^T omega)`. -/
theorem unscale_weightedGaugeProjection_scale_eq
    (H alpha x : Band → ℝ)
    (hAlpha : ∀ j, alpha j ≠ 0)
    (hTotal : sharpWeightTotal H alpha ≠ 0) :
    unscaleByCenter alpha
        (weightedGaugeProjection H alpha (scaleByCenter alpha x)) =
      fun j => x j -
        (∑ k, sharpWeight H alpha k * x k) /
          sharpWeightTotal H alpha := by
  funext j
  have hsum :
      (∑ k, H k * alpha k * (alpha k * x k)) =
        ∑ k, sharpWeight H alpha k * x k := by
    apply Finset.sum_congr rfl
    intro k hk
    unfold sharpWeight
    ring
  unfold unscaleByCenter weightedGaugeProjection scaleByCenter
  rw [hsum]
  field_simp [hAlpha j, hTotal]





omit [Fintype Band] [DecidableEq Band] in
theorem sharpWeight_nonneg_of_mass_nonneg
    (H alpha : Band → ℝ) (hH : ∀ j, 0 ≤ H j) (j : Band) :
    0 ≤ sharpWeight H alpha j := by
  exact mul_nonneg (hH j) (sq_nonneg (alpha j))















end SharpProjection

end Erdos390.Full.MovingLowGaugeTransfer

end

/- Source module: Erdos390.Full.PaperWeightedInverseExport -/
section


/-!
# Export of the sharp inverse in the paper's weighted band norm

The finite graph argument is naturally written after the diagonal change of
variables `b j = alpha j * q j`.  This file records the change of variables
as an exact linear equivalence between the two arithmetic gauges.  It also
proves that the projected raw row-normalized matrix is conjugate to
`projectedSharpLinearMap`.  Consequently an inverse estimate in the ordinary
supremum norm of `q` is literally the paper estimate
`max_j |b_j| / |alpha_j|` for the unscaled band coefficient `b`.

There is no limiting centre and no continuum gauge in this algebraic export.
-/

open scoped BigOperators

noncomputable section

namespace Erdos390.Full.PaperWeightedInverseExport

open ArithmeticGaugeStableInverse
open CompressedArithmeticOperator
open FiniteGraphQuotientInverse
open FiniteGraphStableInverse
open MovingLowGaugeTransfer

variable {Band : Type*} [Fintype Band]















theorem paperSharpNorm_eq_piNorm
    (H alpha : Band → ℝ) (hAlpha : ∀ j, alpha j ≠ 0)
    (b : RawGaugeSpace H alpha) :
    paperSharpNorm H alpha hAlpha b =
      ‖fun j ↦ b.1 j / alpha j‖ := by
  rfl























/-- Coordinate form of the preceding weighted bound. -/
theorem abs_raw_coordinate_le_paperSharpNorm
    (H alpha : Band → ℝ) (hAlpha : ∀ j, alpha j ≠ 0)
    (b : RawGaugeSpace H alpha) (j : Band) :
    |b.1 j| ≤ |alpha j| * paperSharpNorm H alpha hAlpha b := by
  have hcoord : |b.1 j / alpha j| ≤
      paperSharpNorm H alpha hAlpha b := by
    rw [paperSharpNorm_eq_piNorm]
    rw [← Real.norm_eq_abs]
    exact norm_le_pi_norm (fun k ↦ b.1 k / alpha k) j
  have hrewrite : |b.1 j| = |alpha j| * |b.1 j / alpha j| := by
    rw [abs_div]
    field_simp [abs_ne_zero.mpr (hAlpha j)]
  rw [hrewrite]
  exact mul_le_mul_of_nonneg_left hcoord (abs_nonneg (alpha j))

end Erdos390.Full.PaperWeightedInverseExport

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

/-- Exact reindexing of a bandwise coefficient through the actual partition. -/
theorem sum_regressionCoefficient_eq_sum_band
    (q : RawGaugeSpace P.mass P.center)
    (F : ℝ → ℝ) :
    (∑ p : BandPrime n W,
      (1 / (p.1 : ℝ)) * F (P.regressionCoefficient q p)) =
      ∑ j : Band, P.mass j * F (q.1 j) := by
  unfold regressionCoefficient
  rw [← Finset.sum_fiberwise Finset.univ P.band
    (fun p : BandPrime n W ↦ (1 / (p.1 : ℝ)) * F (q.1 (P.band p)))]
  apply Finset.sum_congr rfl
  intro j hj
  change (∑ p ∈ P.data.fiber j,
      (1 / (p.1 : ℝ)) * F (q.1 (P.band p))) =
    P.mass j * F (q.1 j)
  calc
    _ = ∑ p ∈ P.data.fiber j,
        (1 / (p.1 : ℝ)) * F (q.1 j) := by
          apply Finset.sum_congr rfl
          intro p hp
          have hpj : P.band p = j :=
            (Erdos390.Lemma84.WeightedBandData.mem_fiber_iff P.data).mp hp
          rw [hpj]
    _ = P.mass j * F (q.1 j) := by
          rw [← Finset.sum_mul]
          rfl

/-- The literal weighted square of the actual deviation is definitionally
the arithmetic partition variance. -/
theorem deviationL2Sq_eq_variance :
    (∑ p : BandPrime n W,
      (1 / (p.1 : ℝ)) * (P.deviation p) ^ 2) = P.variance := by
  change (∑ p : BandPrime n W,
      (1 / (p.1 : ℝ)) * (P.deviation p) ^ 2) =
    ∑ p : BandPrime n W,
      (1 / (p.1 : ℝ)) * P.data.cellDeviation p *
        P.data.cellDeviation p
  apply Finset.sum_congr rfl
  intro p hp
  change (1 / (p.1 : ℝ)) *
      (P.center (P.band p) - tPrime n p.1) ^ 2 =
    (1 / (p.1 : ℝ)) *
      (P.center (P.band p) - tPrime n p.1) *
        (P.center (P.band p) - tPrime n p.1)
  rw [pow_two]
  ring

/-- A sharp regression bound gives the literal pointwise band bound. -/
theorem abs_regressionCoefficient_le
    (hn : 1 < n) (q : RawGaugeSpace P.mass P.center)
    {C w : ℝ}
    (hsharp : paperSharpNorm P.mass P.center (P.center_ne_zero hn) q ≤ C * w)
    (p : BandPrime n W) :
    |P.regressionCoefficient q p| ≤ C * w := by
  have hcoord := abs_raw_coordinate_le_paperSharpNorm
    P.mass P.center (P.center_ne_zero hn) q (P.band p)
  have hcenter := (P.center_mem_zero_one hn (P.band p)).2
  have hcenter0 := (P.center_mem_zero_one hn (P.band p)).1
  have habsCenter : |P.center (P.band p)| ≤ 1 := by
    rw [abs_of_nonneg hcenter0]
    exact hcenter
  calc
    |P.regressionCoefficient q p| = |q.1 (P.band p)| := rfl
    _ ≤ |P.center (P.band p)| *
        paperSharpNorm P.mass P.center (P.center_ne_zero hn) q := hcoord
    _ ≤ 1 * paperSharpNorm P.mass P.center (P.center_ne_zero hn) q :=
      mul_le_mul_of_nonneg_right habsCenter (norm_nonneg _)
    _ ≤ C * w := by simpa using hsharp

/-- The actual weighted `L¹` norm of the regression vector. -/
theorem regressionL1_le
    (hn : 1 < n) (q : RawGaugeSpace P.mass P.center)
    {C w K : ℝ} (hC : 0 ≤ C) (hw : 0 ≤ w)
    (hsharp : paperSharpNorm P.mass P.center (P.center_ne_zero hn) q ≤ C * w)
    (hbandT : bandTReciprocalSum n W ≤ K) :
    P.regressionL1 q ≤ C * K * w := by
  have hcw : 0 ≤ C * w := mul_nonneg hC hw
  have hsum : P.regressionL1 q ≤
      (C * w) * ∑ j : Band, P.mass j * P.center j := by
    rw [regressionL1, P.sum_regressionCoefficient_eq_sum_band q abs]
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j hj
    have hcoord := abs_raw_coordinate_le_paperSharpNorm
      P.mass P.center (P.center_ne_zero hn) q j
    have hcenter0 := (P.center_mem_zero_one hn j).1
    have hq : |q.1 j| ≤ P.center j * (C * w) := by
      calc
        |q.1 j| ≤ |P.center j| *
            paperSharpNorm P.mass P.center (P.center_ne_zero hn) q := hcoord
        _ ≤ |P.center j| * (C * w) :=
          mul_le_mul_of_nonneg_left hsharp (abs_nonneg _)
        _ = P.center j * (C * w) := by rw [abs_of_nonneg hcenter0]
    calc
      P.mass j * |q.1 j| ≤ P.mass j * (P.center j * (C * w)) :=
        mul_le_mul_of_nonneg_left hq (P.data.mass_pos j).le
      _ = (C * w) * (P.mass j * P.center j) := by ring
  rw [P.sum_mass_mul_center_eq_bandTReciprocalSum] at hsum
  calc
    P.regressionL1 q ≤ (C * w) * bandTReciprocalSum n W := hsum
    _ ≤ (C * w) * K := mul_le_mul_of_nonneg_left hbandT hcw
    _ = C * K * w := by ring

/-- The actual weighted quadratic norm of the regression vector. -/
theorem regressionL2Sq_le
    (hn : 1 < n) (q : RawGaugeSpace P.mass P.center)
    {C w K : ℝ} (hC : 0 ≤ C) (hw : 0 ≤ w)
    (hsharp : paperSharpNorm P.mass P.center (P.center_ne_zero hn) q ≤ C * w)
    (hbandT : bandTReciprocalSum n W ≤ K) :
    P.regressionL2Sq q ≤ C ^ 2 * K * w ^ 2 := by
  have hcw : 0 ≤ C * w := mul_nonneg hC hw
  have hsum : P.regressionL2Sq q ≤
      (C * w) ^ 2 * ∑ j : Band, P.mass j * P.center j := by
    rw [regressionL2Sq, P.sum_regressionCoefficient_eq_sum_band q
      (fun x ↦ x ^ 2)]
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j hj
    have hcoord := abs_raw_coordinate_le_paperSharpNorm
      P.mass P.center (P.center_ne_zero hn) q j
    have hcenter := P.center_mem_zero_one hn j
    have hqabs : |q.1 j| ≤ P.center j * (C * w) := by
      calc
        |q.1 j| ≤ |P.center j| *
            paperSharpNorm P.mass P.center (P.center_ne_zero hn) q := hcoord
        _ ≤ |P.center j| * (C * w) :=
          mul_le_mul_of_nonneg_left hsharp (abs_nonneg _)
        _ = P.center j * (C * w) := by rw [abs_of_nonneg hcenter.1]
    have hqsq : (q.1 j) ^ 2 ≤ P.center j * (C * w) ^ 2 := by
      have hsq : (q.1 j) ^ 2 ≤ (P.center j * (C * w)) ^ 2 := by
        have hright0 : 0 ≤ P.center j * (C * w) :=
          mul_nonneg hcenter.1 hcw
        have hprod := mul_nonneg (sub_nonneg.mpr hqabs)
          (add_nonneg (abs_nonneg (q.1 j)) hright0)
        rw [← sq_abs (q.1 j)]
        nlinarith
      have hcenterSq : P.center j ^ 2 ≤ P.center j := by
        have hprod := mul_nonneg hcenter.1 (sub_nonneg.mpr hcenter.2)
        nlinarith
      calc
        (q.1 j) ^ 2 ≤ (P.center j * (C * w)) ^ 2 := hsq
        _ = P.center j ^ 2 * (C * w) ^ 2 := by ring
        _ ≤ P.center j * (C * w) ^ 2 :=
          mul_le_mul_of_nonneg_right hcenterSq (sq_nonneg _)
    calc
      P.mass j * (q.1 j) ^ 2 ≤
          P.mass j * (P.center j * (C * w) ^ 2) :=
        mul_le_mul_of_nonneg_left hqsq (P.data.mass_pos j).le
      _ = (C * w) ^ 2 * (P.mass j * P.center j) := by ring
  rw [P.sum_mass_mul_center_eq_bandTReciprocalSum] at hsum
  calc
    P.regressionL2Sq q ≤ (C * w) ^ 2 * bandTReciprocalSum n W := hsum
    _ ≤ (C * w) ^ 2 * K :=
      mul_le_mul_of_nonneg_left hbandT (sq_nonneg _)
    _ = C ^ 2 * K * w ^ 2 := by ring

/-- All three paper coefficient bounds for the literal compensated vector.
The constants are explicit and independent of the number of bands. -/
theorem compensatedCoefficient_three_bounds
    (hn : 1 < n) (q : RawGaugeSpace P.mass P.center)
    {C w K : ℝ} (hC : 0 ≤ C) (hw : 0 ≤ w)
    (hsharp : paperSharpNorm P.mass P.center (P.center_ne_zero hn) q ≤ C * w)
    (hbandT : bandTReciprocalSum n W ≤ K)
    (hdevSup : ∀ p : BandPrime n W, |P.deviation p| ≤ w)
    (hdevL1 : P.totalL1 ≤ 7 * w)
    (hdevL2 : P.variance ≤ 4 * w ^ 2) :
    (∀ p : BandPrime n W,
        |P.compensatedCoefficient q p| ≤ (1 + C) * w) ∧
      P.compensatedL1 q ≤ (7 + C * K) * w ∧
      P.compensatedL2Sq q ≤
        2 * (4 + C ^ 2 * K) * w ^ 2 := by
  have hqSup : ∀ p : BandPrime n W,
      |P.regressionCoefficient q p| ≤ C * w :=
    P.abs_regressionCoefficient_le hn q hsharp
  have hqL1 : P.regressionL1 q ≤ C * K * w :=
    P.regressionL1_le hn q hC hw hsharp hbandT
  have hqL2 : P.regressionL2Sq q ≤ C ^ 2 * K * w ^ 2 :=
    P.regressionL2Sq_le hn q hC hw hsharp hbandT
  constructor
  · intro p
    unfold compensatedCoefficient
    calc
      |P.deviation p - P.regressionCoefficient q p| ≤
          |P.deviation p| + |P.regressionCoefficient q p| := abs_sub _ _
      _ ≤ w + C * w := add_le_add (hdevSup p) (hqSup p)
      _ = (1 + C) * w := by ring
  constructor
  · unfold compensatedL1
    calc
      (∑ p : BandPrime n W,
          (1 / (p.1 : ℝ)) * |P.compensatedCoefficient q p|) ≤
          ∑ p : BandPrime n W,
            ((1 / (p.1 : ℝ)) * |P.deviation p| +
              (1 / (p.1 : ℝ)) * |P.regressionCoefficient q p|) := by
        apply Finset.sum_le_sum
        intro p hp
        unfold compensatedCoefficient
        simpa only [mul_add] using
          (mul_le_mul_of_nonneg_left (abs_sub
              (P.deviation p) (P.regressionCoefficient q p))
            (one_div_nonneg.mpr
              (show (0 : ℝ) ≤ (p.1 : ℝ) by positivity)))
      _ = (∑ p : BandPrime n W,
          (1 / (p.1 : ℝ)) * |P.deviation p|) +
          ∑ p : BandPrime n W,
            (1 / (p.1 : ℝ)) * |P.regressionCoefficient q p| :=
        Finset.sum_add_distrib
      _ ≤ 7 * w + C * K * w := add_le_add hdevL1 hqL1
      _ = (7 + C * K) * w := by ring
  · unfold compensatedL2Sq
    calc
      (∑ p : BandPrime n W,
          (1 / (p.1 : ℝ)) * (P.compensatedCoefficient q p) ^ 2) ≤
          ∑ p : BandPrime n W,
            (2 * ((1 / (p.1 : ℝ)) * P.deviation p ^ 2) +
              2 * ((1 / (p.1 : ℝ)) *
                (P.regressionCoefficient q p) ^ 2)) := by
        apply Finset.sum_le_sum
        intro p hp
        have hsquare : (P.deviation p - P.regressionCoefficient q p) ^ 2 ≤
            2 * P.deviation p ^ 2 +
              2 * (P.regressionCoefficient q p) ^ 2 := by
          nlinarith [sq_nonneg (P.deviation p + P.regressionCoefficient q p)]
        unfold compensatedCoefficient
        calc
          (1 / (p.1 : ℝ)) *
              (P.deviation p - P.regressionCoefficient q p) ^ 2 ≤
            (1 / (p.1 : ℝ)) *
              (2 * P.deviation p ^ 2 +
                2 * (P.regressionCoefficient q p) ^ 2) :=
              mul_le_mul_of_nonneg_left hsquare
                (one_div_nonneg.mpr
                  (show (0 : ℝ) ≤ (p.1 : ℝ) by positivity))
          _ = 2 * ((1 / (p.1 : ℝ)) * P.deviation p ^ 2) +
              2 * ((1 / (p.1 : ℝ)) *
                (P.regressionCoefficient q p) ^ 2) := by ring
      _ = 2 * (∑ p : BandPrime n W,
            (1 / (p.1 : ℝ)) * P.deviation p ^ 2) +
          2 * (∑ p : BandPrime n W,
            (1 / (p.1 : ℝ)) * (P.regressionCoefficient q p) ^ 2) := by
        simp only [Finset.sum_add_distrib, Finset.mul_sum]
      _ = 2 * P.variance + 2 * P.regressionL2Sq q := by
        rw [P.deviationL2Sq_eq_variance]
        rfl
      _ ≤ 2 * (4 * w ^ 2) + 2 * (C ^ 2 * K * w ^ 2) := by
        linarith
      _ = 2 * (4 + C ^ 2 * K) * w ^ 2 := by ring

end

end Erdos390.Full.ArithmeticBandGeometry.Partition

end

/- Source module: Erdos390.Full.PaperActualCompensatedRegression -/
section


/-!
# The actual two-stage compensated regression in Lemma 8.6

The objects in this file live on the genuine guard-deleted, tilted finite
probability space from `PaperBridgeFit`.  In particular, the nuisance
coefficient is not an abstract vector satisfying a normal equation: it is
defined by applying the inverse of the proved actual nuisance covariance
operator to the literal covariance vector of the post-band-regression score.

This file proves the exact finite identities used before the analytic
`w^2` comparison: the prime-coefficient expansion, nuisance normal equation,
orthogonality, Schur variance identity, and marked-row decomposition.
-/

open scoped BigOperators

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

open ArithmeticModel ArithmeticBandGeometry
open PaperWeightedInverseExport
open PrimePowerCovariance

namespace BridgeData

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]
  (B : BridgeData Head Band)















theorem partition_compensatedCoefficient_eq
    (q : B.RawBandGauge)
    (p : BandPrime B.sampleData.n B.sampleData.W) :
    B.partition.compensatedCoefficient q p =
      B.actualCompensatedCoefficient q p := rfl

/-- Reindexing over the actual partition identifies the raw band score with
the corresponding primewise coefficient sum. -/
theorem bandRegressionScore_eq_primeSum
    (q : B.RawBandGauge) (m : B.sampleData.Sample) :
    B.bandRegressionScore q m =
      ∑ p : BandPrime B.sampleData.n B.sampleData.W,
        B.bandRegressionCoefficient q p *
          valuation p.1 (B.sampleData.value m) := by
  unfold bandRegressionScore bandScore bandRegressionCoefficient
  rw [← Finset.sum_fiberwise Finset.univ B.partition.band
    (fun p : BandPrime B.sampleData.n B.sampleData.W ↦
      q.1 (B.partition.band p) *
        valuation p.1 (B.sampleData.value m))]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  have hpj : B.partition.band p = j :=
    (Erdos390.Lemma84.WeightedBandData.mem_fiber_iff
      B.partition.data).mp hp
  rw [hpj]

















































end BridgeData

end

end Erdos390.Full.PaperBridgeFit

end

/- Source module: Erdos390.Full.PaperActualTwoStageRegression -/
section


/-!
# The literal two-stage band/nuisance solve of Lemma 8.6

This file defines the actual Schur-projected band operator on the exact raw
arithmetic gauge.  The first regression vector is obtained by inverting this
literal operator on the literal Schur-projected raw slow-score column.  The
second regression is then the actual nuisance inverse already constructed in
`PaperActualCompensatedRegression`.

No covariance matrix, inverse, or regression conclusion is stored in bridge
data.  The equivalence argument of the first-stage constructor is intended to
be supplied by the actual projected inverse conclusion of Lemma 8.4.
-/

open scoped BigOperators

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

open ArithmeticModel ArithmeticBandGeometry
open PaperWeightedInverseExport
open CompressedArithmeticOperator
open MovingLowGaugeTransfer

namespace BridgeData

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]
  (B : BridgeData Head Band)









theorem projectRawBandVector_sub [Nonempty Band]
    (x y : Band → ℝ) :
    B.projectRawBandVector (x - y) =
      B.projectRawBandVector x - B.projectRawBandVector y := by
  apply Subtype.ext
  funext j
  change weightedGaugeProjection B.harmonicMass B.bandCenter (x - y) j =
    weightedGaugeProjection B.harmonicMass B.bandCenter x j -
      weightedGaugeProjection B.harmonicMass B.bandCenter y j
  have hsum :
      (∑ k : Band,
        B.harmonicMass k * B.bandCenter k * (x k - y k)) =
      (∑ k : Band, B.harmonicMass k * B.bandCenter k * x k) -
        ∑ k : Band, B.harmonicMass k * B.bandCenter k * y k := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    ring
  unfold weightedGaugeProjection
  simp only [Pi.sub_apply, hsum]
  ring











































theorem actualBandRegression_normalEquation [Nonempty Head] [Nonempty Band]
    (xi : B.ParamSpace) {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (e : B.RawBandGauge ≃ₗ[ℝ] B.RawBandGauge)
    (he : ∀ q, e q = B.actualBandSchurLinearMap xi hgamma hgap q) :
    B.actualBandSchurLinearMap xi hgamma hgap
        (B.actualBandRegression xi hgamma hgap e) =
      B.actualBandRegressionTarget xi hgamma hgap := by
  rw [← he]
  exact e.apply_symm_apply _







/-- Arithmetic gauge projection costs at most a factor two in the paper's
sharp norm.  This is the exact finite form of the rowwise step used on the
right side of the regression equation: a bound
`|x_j| <= C * alpha_j` remains a sharp bound after applying
`P_{alpha,n}`.  Positivity of the actual harmonic masses and centers proves
the weighted-mean estimate; no operator bound is assumed. -/
theorem projectRawBandVector_paperSharpNorm_le_two
    [Nonempty Band]
    (x : Band → ℝ) {C : ℝ} (hC : 0 ≤ C)
    (hx : ∀ j, |x j| ≤ C * B.bandCenter j) :
    paperSharpNorm B.harmonicMass B.bandCenter
        (B.partition.center_ne_zero B.n_gt_one)
        (B.projectRawBandVector x) ≤ 2 * C := by
  let u : Band → ℝ := fun j ↦ x j / B.bandCenter j
  let omega : Band → ℝ :=
    sharpWeight B.harmonicMass B.bandCenter
  let total : ℝ := sharpWeightTotal B.harmonicMass B.bandCenter
  have hAlpha (j : Band) : B.bandCenter j ≠ 0 :=
    B.partition.center_ne_zero B.n_gt_one j
  have hAlphaPos (j : Band) : 0 < B.bandCenter j :=
    B.bandCenter_pos j
  have hTotal : 0 < total := by
    simpa only [total] using B.sharpBandWeightTotal_pos
  have hu (j : Band) : |u j| ≤ C := by
    dsimp only [u]
    rw [abs_div, abs_of_pos (hAlphaPos j)]
    exact (div_le_iff₀ (hAlphaPos j)).2 (by
      simpa only [mul_comm] using hx j)
  have hOmega (j : Band) : 0 ≤ omega j := by
    dsimp only [omega]
    exact sharpWeight_nonneg_of_mass_nonneg
      B.harmonicMass B.bandCenter
      (fun k ↦ (B.harmonicMass_pos k).le) j
  have hMean :
      |(∑ j, omega j * u j) / total| ≤ C := by
    rw [abs_div, abs_of_pos hTotal]
    calc
      |∑ j, omega j * u j| / total ≤
          (∑ j, |omega j * u j|) / total :=
        div_le_div_of_nonneg_right
          (Finset.abs_sum_le_sum_abs _ _) hTotal.le
      _ ≤ (∑ j, omega j * C) / total := by
        apply div_le_div_of_nonneg_right _ hTotal.le
        apply Finset.sum_le_sum
        intro j hj
        rw [abs_mul, abs_of_nonneg (hOmega j)]
        exact mul_le_mul_of_nonneg_left (hu j) (hOmega j)
      _ = C := by
        rw [← Finset.sum_mul]
        change total * C / total = C
        field_simp [ne_of_gt hTotal]
  have hScale : scaleByCenter B.bandCenter u = x := by
    funext j
    unfold scaleByCenter u
    field_simp [hAlpha j]
  have hProjected (j : Band) :
      (B.projectRawBandVector x).1 j / B.bandCenter j =
        u j - (∑ k, omega k * u k) / total := by
    have hconj := congrFun
      (unscale_weightedGaugeProjection_scale_eq
        B.harmonicMass B.bandCenter u hAlpha (ne_of_gt hTotal)) j
    change weightedGaugeProjection B.harmonicMass B.bandCenter
        (scaleByCenter B.bandCenter u) j / B.bandCenter j = _ at hconj
    rw [hScale] at hconj
    simpa only [BridgeData.projectRawBandVector, omega, total] using hconj
  rw [paperSharpNorm_eq_piNorm]
  have hTwoC : 0 ≤ 2 * C := mul_nonneg (by norm_num) hC
  rw [pi_norm_le_iff_of_nonneg hTwoC]
  intro j
  rw [Real.norm_eq_abs, hProjected]
  exact (abs_sub _ _).trans (by linarith [hu j, hMean])

/-- A literal row-relative estimate for the Schur-projected slow-score
column implies the sharp bound on the actual regression target.  This removes
the target-norm contract from later Lemma 8.6 assembly: applications need
only prove the paper's natural row estimate before arithmetic gauge
projection. -/
theorem actualBandRegressionTarget_sharpNorm_le_of_row
    [Nonempty Head] [Nonempty Band]
    (xi : B.ParamSpace) {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    {C w : ℝ} (hC : 0 ≤ C) (hw : 0 ≤ w)
    (hrow : ∀ j,
      |B.normalizedBandCovarianceRow xi
          (B.nuisanceResidualScore xi hgamma hgap B.slowScore) j| ≤
        (C * w) * B.bandCenter j) :
    paperSharpNorm B.harmonicMass B.bandCenter
        (B.partition.center_ne_zero B.n_gt_one)
        (B.actualBandRegressionTarget xi hgamma hgap) ≤
      (2 * C) * w := by
  have hproject := B.projectRawBandVector_paperSharpNorm_le_two
    (B.normalizedBandCovarianceRow xi
      (B.nuisanceResidualScore xi hgamma hgap B.slowScore))
    (mul_nonneg hC hw) hrow
  simpa only [actualBandRegressionTarget, mul_assoc] using hproject

/-- The inverse bound and actual target bound imply the sharp estimate for
the constructed first-stage regression; it is not an independent input. -/
theorem actualBandRegression_sharpNorm_le [Nonempty Head] [Nonempty Band]
    (xi : B.ParamSpace) {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (e : B.RawBandGauge ≃ₗ[ℝ] B.RawBandGauge)
    {Cinv Cright w : ℝ}
    (hCinv : 0 ≤ Cinv)
    (hinv : ∀ v,
      paperSharpNorm B.harmonicMass B.bandCenter
          (B.partition.center_ne_zero B.n_gt_one) (e.symm v) ≤
        Cinv * paperSharpNorm B.harmonicMass B.bandCenter
          (B.partition.center_ne_zero B.n_gt_one) v)
    (hright : paperSharpNorm B.harmonicMass B.bandCenter
        (B.partition.center_ne_zero B.n_gt_one)
        (B.actualBandRegressionTarget xi hgamma hgap) ≤ Cright * w) :
    paperSharpNorm B.harmonicMass B.bandCenter
        (B.partition.center_ne_zero B.n_gt_one)
        (B.actualBandRegression xi hgamma hgap e) ≤
      (Cinv * Cright) * w := by
  calc
    paperSharpNorm B.harmonicMass B.bandCenter
        (B.partition.center_ne_zero B.n_gt_one)
        (B.actualBandRegression xi hgamma hgap e) ≤
      Cinv * paperSharpNorm B.harmonicMass B.bandCenter
        (B.partition.center_ne_zero B.n_gt_one)
        (B.actualBandRegressionTarget xi hgamma hgap) :=
      hinv _
    _ ≤ Cinv * (Cright * w) :=
      mul_le_mul_of_nonneg_left hright hCinv
    _ = (Cinv * Cright) * w := by ring

/-- The three displayed coefficient bounds of Lemma 8.6 for the regression
vector constructed above.  They are derived from the actual inverse/target
outputs and the actual canonical-mesh moment bounds. -/
theorem actualBandRegression_compensatedCoefficient_three_bounds
    [Nonempty Head] [Nonempty Band]
    (xi : B.ParamSpace) {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (e : B.RawBandGauge ≃ₗ[ℝ] B.RawBandGauge)
    {Cinv Cright K w : ℝ}
    (hCinv : 0 ≤ Cinv) (hCright : 0 ≤ Cright)
    (hw : 0 ≤ w)
    (hinv : ∀ v,
      paperSharpNorm B.harmonicMass B.bandCenter
          (B.partition.center_ne_zero B.n_gt_one) (e.symm v) ≤
        Cinv * paperSharpNorm B.harmonicMass B.bandCenter
          (B.partition.center_ne_zero B.n_gt_one) v)
    (hright : paperSharpNorm B.harmonicMass B.bandCenter
        (B.partition.center_ne_zero B.n_gt_one)
        (B.actualBandRegressionTarget xi hgamma hgap) ≤ Cright * w)
    (hbandT : PrimeSums.bandTReciprocalSum
      B.sampleData.n B.sampleData.W ≤ K)
    (hdevSup : ∀ p : BandPrime B.sampleData.n B.sampleData.W,
      |B.partition.deviation p| ≤ w)
    (hdevL1 : B.partition.totalL1 ≤ 7 * w)
    (hdevL2 : B.partition.variance ≤ 4 * w ^ 2) :
    (∀ p : BandPrime B.sampleData.n B.sampleData.W,
      |B.actualCompensatedCoefficient
        (B.actualBandRegression xi hgamma hgap e) p| ≤
          (1 + Cinv * Cright) * w) ∧
    B.partition.compensatedL1
        (B.actualBandRegression xi hgamma hgap e) ≤
      (7 + (Cinv * Cright) * K) * w ∧
    B.partition.compensatedL2Sq
        (B.actualBandRegression xi hgamma hgap e) ≤
      2 * (4 + (Cinv * Cright) ^ 2 * K) * w ^ 2 := by
  have hsharp := B.actualBandRegression_sharpNorm_le
    xi hgamma hgap e hCinv hinv hright
  have hC : 0 ≤ Cinv * Cright := mul_nonneg hCinv hCright
  obtain ⟨hsup, hL1, hL2⟩ :=
    B.partition.compensatedCoefficient_three_bounds B.n_gt_one
      (B.actualBandRegression xi hgamma hgap e)
      hC hw hsharp hbandT hdevSup hdevL1 hdevL2
  refine ⟨?_, hL1, hL2⟩
  intro p
  rw [← B.partition_compensatedCoefficient_eq
    (B.actualBandRegression xi hgamma hgap e) p]
  exact hsup p











end BridgeData

end

end Erdos390.Full.PaperBridgeFit

end

/- Source module: Erdos390.Full.PaperActualFullBandIdentification -/
section


/-!
# Exact identification of the actual full-valuation band operator

The full-valuation sharp operator produced by Lemmas 7.5 and 8.4 is defined
through the bounded valuation law.  The nonlinear bridge is written through
covariance rows of the actual tilted sample.  This file proves that these
are the same finite operator before nuisance regression, and records the
exact sharp/raw gauge conjugacy.  No asymptotic estimate is used.
-/

open scoped BigOperators

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

open ArithmeticBandGeometry PaperWeightedInverseExport

namespace BridgeData

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]
  (B : BridgeData Head Band)

/-- The bounded-law full band row is literally the normalized covariance row
of the actual tilted bridge law. -/
theorem fullBandRow_actualValuationLaw_eq_normalizedBandCovarianceRow
    [Nonempty Head]
    (xi : B.ParamSpace) (q : B.RawBandGauge) (i : Band) :
    PrimePowerSharpBandTransfer.fullBandRow
        (B.actualValuationLaw xi) B.partition q.1 i =
      B.normalizedBandCovarianceRow xi
        (B.bandRegressionScore q) i := by
  have hscore : B.bandRegressionScore q =
      fun m ↦ ∑ p : BandPrime B.sampleData.n B.sampleData.W,
        B.bandRegressionCoefficient q p *
          ArithmeticModel.valuation p.1 (B.sampleData.value m) := by
    funext m
    exact B.bandRegressionScore_eq_primeSum q m
  rw [hscore]
  unfold PrimePowerSharpBandTransfer.fullBandRow
    normalizedBandCovarianceRow bandScore
    PrimePowerCovariance.BoundedValuationLaw.covVV
    PrimePowerCovariance.BoundedValuationLaw.V
    actualValuationLaw
  rw [FiniteProbability.covariance_sum_left]
  simp_rw [FiniteProbability.covariance_sum_right,
    FiniteProbability.covariance_smul_right]
  simp only [bandRegressionCoefficient]
  change (1 / B.harmonicMass i) * _ = _ / B.harmonicMass i
  ring

























end BridgeData

end

end Erdos390.Full.PaperBridgeFit

end

/- Source module: Erdos390.Full.PaperExactTwoStageOrdinaryFast -/
section


/-!
# Ordinary-fast / sharp-slow form of the exact two-stage solve

The fast target in Proposition 8.7 is bounded in the ordinary raw-band
supremum norm: its unprojected coordinates are
`(L / q) * Delta_j / H_j = O(1)`.  They are not, in general, bounded after
division by the moving centre `alpha_j`; in particular `alpha_0 -> 0`.

The slow regression is different.  Lemma 8.5 supplies a sharp inverse for
that right-hand side and hence a regression vector of size `O(w alpha_j)`.
This file records the exact finite algebra with those two norms kept
separate.  It is the norm-correct form of the block calculation in the
proof of Proposition 8.7.
-/

open scoped BigOperators

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

open ArithmeticBandGeometry PaperWeightedInverseExport
  MovingLowGaugeTransfer

namespace BridgeData

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]
  (B : BridgeData Head Band)









/-- Exact ordinary projection estimate.  The sole geometric input is the
displayed ratio between the first band moment and
`sum_j H_j alpha_j^2`.  On a permitted regular mesh Lemma 8.4 bounds that
ratio uniformly by the fixed positive interior anchor block. -/
theorem projectRawBandVector_norm_le_of_moment_ratio
    [Nonempty Band]
    (x : Band → ℝ) {C R : ℝ}
    (hC : 0 ≤ C) (hR : 0 ≤ R)
    (hx : ∀ j, |x j| ≤ C)
    (hRatio : (∑ j : Band,
        B.harmonicMass j * B.bandCenter j) ≤
      R * sharpWeightTotal B.harmonicMass B.bandCenter) :
    ‖B.projectRawBandVector x‖ ≤ (1 + R) * C := by
  let total : ℝ := sharpWeightTotal B.harmonicMass B.bandCenter
  let numerator : ℝ := ∑ j : Band,
    B.harmonicMass j * B.bandCenter j * x j
  have htotal : 0 < total := by
    simpa only [total] using B.sharpBandWeightTotal_pos
  have hmoment : 0 ≤ ∑ j : Band,
      B.harmonicMass j * B.bandCenter j := by
    apply Finset.sum_nonneg
    intro j hj
    exact mul_nonneg (B.harmonicMass_pos j).le (B.bandCenter_pos j).le
  have hnum : |numerator| ≤
      C * ∑ j : Band, B.harmonicMass j * B.bandCenter j := by
    dsimp only [numerator]
    calc
      |∑ j : Band, B.harmonicMass j * B.bandCenter j * x j| ≤
          ∑ j : Band,
            |B.harmonicMass j * B.bandCenter j * x j| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j : Band,
          C * (B.harmonicMass j * B.bandCenter j) := by
        apply Finset.sum_le_sum
        intro j hj
        rw [abs_mul, abs_mul, abs_of_pos (B.harmonicMass_pos j),
          abs_of_pos (B.bandCenter_pos j)]
        calc
          B.harmonicMass j * B.bandCenter j * |x j| ≤
              (B.harmonicMass j * B.bandCenter j) * C :=
            mul_le_mul_of_nonneg_left (hx j)
              (mul_nonneg (B.harmonicMass_pos j).le
                (B.bandCenter_pos j).le)
          _ = C * (B.harmonicMass j * B.bandCenter j) := by ring
      _ = C * ∑ j : Band,
          B.harmonicMass j * B.bandCenter j := by
        rw [Finset.mul_sum]
  have hmean : |numerator / total| ≤ C * R := by
    rw [abs_div, abs_of_pos htotal]
    calc
      |numerator| / total ≤
          (C * ∑ j : Band,
            B.harmonicMass j * B.bandCenter j) / total :=
        div_le_div_of_nonneg_right hnum htotal.le
      _ ≤ (C * (R * total)) / total := by
        exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hRatio hC) htotal.le
      _ = C * R := by field_simp [htotal.ne']
  have hbound : 0 ≤ (1 + R) * C :=
    mul_nonneg (by linarith) hC
  change ‖(B.projectRawBandVector x).1‖ ≤ (1 + R) * C
  rw [pi_norm_le_iff_of_nonneg hbound]
  intro j
  rw [Real.norm_eq_abs]
  change |weightedGaugeProjection B.harmonicMass B.bandCenter x j| ≤ _
  unfold weightedGaugeProjection
  change |x j - B.bandCenter j * (numerator / total)| ≤ _
  calc
    |x j - B.bandCenter j * (numerator / total)| ≤
        |x j| + |B.bandCenter j| * |numerator / total| := by
      simpa only [abs_mul] using abs_sub (x j)
        (B.bandCenter j * (numerator / total))
    _ ≤ C + 1 * (C * R) := by
      have hcenter := (B.partition.center_mem_zero_one B.n_gt_one j).2
      rw [abs_of_pos (B.bandCenter_pos j)]
      exact add_le_add (hx j)
        (mul_le_mul hcenter hmean (abs_nonneg _) (by positivity))
    _ = (1 + R) * C := by ring

























end BridgeData

end

end Erdos390.Full.PaperBridgeFit

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

/- Source module: Erdos390.Full.PaperCanonicalFullQuotientFineMeshEventually -/
section


/-!
# Anchor-free, two-parameter full quotient gap

This file removes the explicit interior-anchor input from the canonical
full-valuation quotient theorem.  Unlike older selected-mesh wrappers, the
statement keeps the paper's two independent mesh parameters `delta` and
`eta`.  The structural cutoff is chosen before both of them.
-/

open scoped BigOperators
open Filter Metric Set

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

open ArithmeticModel ArithmeticBandGeometry FiniteProbability
open PaperGuardCensus RegularMeshPrimeCutoffs

namespace BridgeData

set_option maxHeartbeats 1200000 in
/-- Paper-order, every-fine-mesh form of the literal full quotient gap.
There are no caller-supplied anchors or analytic error estimates. -/
theorem exists_fineMesh_cutoff_eventually_canonical_actualFullQuotient :
    ∃ kappa : ℝ, 0 < kappa ∧
      ∃ meshTol : ℝ, 0 < meshTol ∧
      ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W →
      ∀ {delta eta : ℝ} (M : RegularRelativeMesh.Mesh delta eta)
        (hdelta : 0 < delta),
      delta + M.ratio ≤ meshTol →
      ∀ {Head : Type*} [Fintype Head] [DecidableEq Head] [Nonempty Head],
      ∀ (Phead : Head → HeadPattern.Pattern),
        (∀ h : Head, ∀ p : ℕ,
          p ∈ (Phead h).primes ↔ p.Prime ∧ p ≤ W) →
      ∀ (I : PhysicalIntervals) (U : ℝ) (hU : 1 ≤ U)
        (hlowerOne : ∀ sigma, 1 ≤ I.lower sigma)
        (hupperU : ∀ sigma, I.upper sigma ≤ U),
      ∀ (Cprom Cbank : ℕ) (ledger : ∀ n, Ledger n Cprom Cbank),
      ∀ (a : NNReal) (marginFloor : ℝ), 0 < marginFloor →
      ∀ᶠ n : ℕ in atTop,
        ∀ (B : BridgeData Head (Fin (M.cellCount + 1))),
          B.sampleData.n = n → B.sampleData.W = W →
          ∀ (hBWlarge : 1 < B.sampleData.W),
          ∀ (hsep : physicalBound (I.upper .minus) B.sampleData.n <
              physicalBound (I.lower .plus) B.sampleData.n)
            (hremaining : ∀ c : Cell Head,
              (rawCell Phead I B.sampleData.n c \
                (ledger B.sampleData.n).guards).Nonempty),
          (hcanonical : B.sampleData = canonicalSampleData
            (W := B.sampleData.W) Phead I (ledger B.sampleData.n)
              hsep hremaining) →
          (∃ (hWne : B.sampleData.W ≠ 0)
              (S : ScaleSeparation M B.sampleData.n B.sampleData.W),
            B.partition = RegularMeshPrimeCutoffs.Mesh.canonicalPartition
              M hdelta B.n_gt_one hWne S) →
          ∀ (T : BarycentricTarget B.sampleData),
            marginFloor ≤ T.cellMassMargin →
            ∀ (hbaseline : B.baseline = T.baseline),
          ∀ (z : B.EffectiveParamSpace)
            (hz : z ∈ closedBall (0 : B.EffectiveParamSpace) (a : ℝ)),
          let xi : B.ParamSpace := B.effectiveParamEquiv z
          let gamma : ℝ :=
            B.canonicalEffectiveNuisanceGamma I U (3 * (a : ℝ)) T
          let hgamma : 0 < gamma :=
            B.canonicalEffectiveNuisanceGamma_pos I U (3 * (a : ℝ)) T
          let hgap : ∀ v, gamma * ‖v‖ ^ 2 ≤
              inner ℝ v (B.nuisanceCovarianceOperator xi v) := by
            intro v
            simpa only [gamma, xi] using
              B.canonicalEffectiveNuisanceGap_on_closedBall I a hU
                hlowerOne hupperU
                (by intro sigma; rw [hcanonical]; rfl)
                (by intro sigma; rw [hcanonical]; rfl)
                T hbaseline hBWlarge z hz v
          ∀ (b : Fin (M.cellCount + 1) → ℝ) (mu : ℝ),
            kappa * B.partition.data.bandNormSq
                (B.partition.data.gaugePart b) ≤
              (B.tiltedLaw xi).covariance
                (B.nuisanceResidualScore xi hgamma hgap
                  (B.primeValuationScore
                    (B.partition.data.residual b mu)))
                (B.nuisanceResidualScore xi hgamma hgap
                  (B.primeValuationScore
                    (B.partition.data.residual b mu))) := by
  obtain ⟨kappa, hkappa, W₀, hmain⟩ :=
    exists_structural_cutoff_eventually_canonical_actualFullQuotient
  let meshTol : ℝ := 1 / 16
  have hmeshTol : 0 < meshTol := by
    dsimp only [meshTol]
    norm_num
  refine ⟨kappa, hkappa, meshTol, hmeshTol, W₀, ?_⟩
  intro W hW delta eta M hdelta hfine
  have hdeltaSmall : delta < (1 / 16 : ℝ) := by
    dsimp only [meshTol] at hfine
    linarith [M.ratio_pos]
  have hratioSmall : M.ratio < (1 / 16 : ℝ) := by
    dsimp only [meshTol] at hfine
    linarith [hdelta]
  have hwidthSmall : ∀ k : Fin M.cellCount,
      M.width k < (1 / 16 : ℝ) := by
    intro k
    exact (M.width_le_ratio hdelta k).trans_lt hratioSmall
  obtain ⟨anchors, anchor, hanchor, hLower, hUpper, hMass⟩ :=
    M.exists_interiorAnchorBlock hdelta hdeltaSmall hwidthSmall
  have hAnchors : anchors.Nonempty := ⟨anchor, hanchor⟩
  intro Head _instFintype _instDecidable _instNonempty
  exact hmain W hW M hdelta anchors hAnchors hLower hUpper hMass
    (Head := Head)

end BridgeData

end

end Erdos390.Full.PaperBridgeFit

end

/- Source module: Erdos390.Full.PaperBandBestDistance -/
section


/-!
# Exact weighted distance to the logarithmic null direction

The paper states the quotient gap using an infimum over the scalar multiple
of the band-centre vector.  The finite Lean development uses the explicit
weighted orthogonal projection `gaugePart`.  This file proves that the two
forms are literally equal, so a paper-facing terminal can use the displayed
infimum without changing the result.
-/

namespace Erdos390.Lemma84

noncomputable section

open Set

variable {Prime Band : Type*}
variable [Fintype Prime] [Fintype Band]
variable [DecidableEq Prime] [DecidableEq Band]

namespace WeightedBandData

variable (d : WeightedBandData Prime Band)



/-- The explicit gauge projection attains the literal infimum. -/
theorem bestBandDistance_eq_bandNormSq_gaugePart
    (b : Band → ℝ) (hA : d.centerEnergy ≠ 0) :
    d.bestBandDistance b = d.bandNormSq (d.gaugePart b) := by
  unfold bestBandDistance
  apply le_antisymm
  · have hBdd : BddBelow (range
        (fun mu : ℝ ↦ d.bandNormSq
          (fun j ↦ b j - mu * d.center j))) := by
      refine ⟨0, ?_⟩
      rintro x ⟨mu, rfl⟩
      exact d.bandNormSq_nonneg _
    have h := ciInf_le hBdd (d.gaugeCoefficient b)
    simpa only [gaugePart] using h
  · exact le_ciInf fun mu ↦ d.gaugePart_best_distance b mu hA

/-- Paper-display form of the same identity. -/
theorem bestBandDistance_eq_iInf
    (b : Band → ℝ) :
    d.bestBandDistance b =
      ⨅ mu : ℝ, ∑ j : Band,
        d.mass j * |b j - mu * d.center j| ^ 2 := by
  unfold bestBandDistance
  congr 1
  funext mu
  unfold bandNormSq bandInner
  apply Finset.sum_congr rfl
  intro j _hj
  rw [sq_abs]
  ring

end WeightedBandData

end


end Erdos390.Lemma84

end

/- Source module: Erdos390.Full.PaperCanonicalFullQuotientPaperDistanceEventually -/
section


/-!
# Literal paper-distance form of the canonical full quotient gap

The canonical arithmetic theorem is proved using the explicit weighted
gauge projection.  This paper-facing wrapper keeps the two mesh parameters
independent, uses the displayed paper scale `delta + eta`, and rewrites the
conclusion as the literal infimum over the logarithmic null direction.
-/

open scoped BigOperators
open Filter Metric Set

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

open ArithmeticModel ArithmeticBandGeometry FiniteProbability
open PaperGuardCensus RegularMeshPrimeCutoffs
open Erdos390.Lemma84

namespace BridgeData

/-- Anchor-free, paper-scale, literal-infimum quotient gap. -/
theorem exists_paperFineMesh_cutoff_eventually_canonical_actualFullQuotientDistance :
    ∃ kappa : ℝ, 0 < kappa ∧
      ∃ w₀ : ℝ, 0 < w₀ ∧
      ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W →
      ∀ {delta eta : ℝ} (M : RegularRelativeMesh.Mesh delta eta)
        (hdelta : 0 < delta),
      delta + eta ≤ w₀ →
      ∀ {Head : Type*} [Fintype Head] [DecidableEq Head] [Nonempty Head],
      ∀ (Phead : Head → HeadPattern.Pattern),
        (∀ h : Head, ∀ p : ℕ,
          p ∈ (Phead h).primes ↔ p.Prime ∧ p ≤ W) →
      ∀ (I : PhysicalIntervals) (U : ℝ) (hU : 1 ≤ U)
        (hlowerOne : ∀ sigma, 1 ≤ I.lower sigma)
        (hupperU : ∀ sigma, I.upper sigma ≤ U),
      ∀ (Cprom Cbank : ℕ) (ledger : ∀ n, Ledger n Cprom Cbank),
      ∀ (a : NNReal) (marginFloor : ℝ), 0 < marginFloor →
      ∀ᶠ n : ℕ in atTop,
        ∀ (B : BridgeData Head (Fin (M.cellCount + 1))),
          B.sampleData.n = n → B.sampleData.W = W →
          ∀ (hBWlarge : 1 < B.sampleData.W),
          ∀ (hsep : physicalBound (I.upper .minus) B.sampleData.n <
              physicalBound (I.lower .plus) B.sampleData.n)
            (hremaining : ∀ c : Cell Head,
              (rawCell Phead I B.sampleData.n c \
                (ledger B.sampleData.n).guards).Nonempty),
          (hcanonical : B.sampleData = canonicalSampleData
            (W := B.sampleData.W) Phead I (ledger B.sampleData.n)
              hsep hremaining) →
          (∃ (hWne : B.sampleData.W ≠ 0)
              (S : ScaleSeparation M B.sampleData.n B.sampleData.W),
            B.partition = RegularMeshPrimeCutoffs.Mesh.canonicalPartition
              M hdelta B.n_gt_one hWne S) →
          ∀ (T : BarycentricTarget B.sampleData),
            marginFloor ≤ T.cellMassMargin →
            ∀ (hbaseline : B.baseline = T.baseline),
          ∀ (z : B.EffectiveParamSpace)
            (hz : z ∈ closedBall (0 : B.EffectiveParamSpace) (a : ℝ)),
          let xi : B.ParamSpace := B.effectiveParamEquiv z
          let gamma : ℝ :=
            B.canonicalEffectiveNuisanceGamma I U (3 * (a : ℝ)) T
          let hgamma : 0 < gamma :=
            B.canonicalEffectiveNuisanceGamma_pos I U (3 * (a : ℝ)) T
          let hgap : ∀ v, gamma * ‖v‖ ^ 2 ≤
              inner ℝ v (B.nuisanceCovarianceOperator xi v) := by
            intro v
            simpa only [gamma, xi] using
              B.canonicalEffectiveNuisanceGap_on_closedBall I a hU
                hlowerOne hupperU
                (by intro sigma; rw [hcanonical]; rfl)
                (by intro sigma; rw [hcanonical]; rfl)
                T hbaseline hBWlarge z hz v
          ∀ (b : Fin (M.cellCount + 1) → ℝ) (mu : ℝ),
            kappa *
                (⨅ lambda : ℝ, ∑ j : Fin (M.cellCount + 1),
                  B.harmonicMass j *
                    |b j - lambda * B.bandCenter j| ^ 2) ≤
              (B.tiltedLaw xi).covariance
                (B.nuisanceResidualScore xi hgamma hgap
                  (B.primeValuationScore
                    (B.partition.data.residual b mu)))
                (B.nuisanceResidualScore xi hgamma hgap
                  (B.primeValuationScore
                    (B.partition.data.residual b mu))) := by
  obtain ⟨kappa, hkappa, meshTol, hmeshTol, W₀, hmain⟩ :=
    exists_fineMesh_cutoff_eventually_canonical_actualFullQuotient
  refine ⟨kappa, hkappa, meshTol, hmeshTol, W₀, ?_⟩
  intro W hW delta eta M hdelta hfine
  have hactualFine : delta + M.ratio ≤ meshTol :=
    (add_le_add_right M.ratio_le_eta delta).trans hfine
  intro Head _instFintype _instDecidable _instNonempty Phead hhead I U hU
    hlowerOne hupperU Cprom Cbank ledger a marginFloor hmargin
  have hevent := hmain W hW M hdelta hactualFine Phead hhead I U hU
    hlowerOne hupperU Cprom Cbank ledger a marginFloor hmargin
  filter_upwards [hevent] with n hn
  intro B hBn hBW hBWlarge hsep hremaining hcanonical hpartition
    T hTmargin hbaseline z hz
  have hraw := hn B hBn hBW hBWlarge hsep hremaining hcanonical
    hpartition T hTmargin hbaseline z hz
  dsimp only at hraw ⊢
  intro b mu
  have hbound := hraw b mu
  have hcenter : B.partition.data.centerEnergy ≠ 0 :=
    ne_of_gt (B.partition.centerEnergy_pos B.n_gt_one)
  rw [← B.partition.data.bestBandDistance_eq_bandNormSq_gaugePart
    b hcenter] at hbound
  rw [B.partition.data.bestBandDistance_eq_iInf b] at hbound
  simpa only [BridgeData.harmonicMass, BridgeData.bandCenter,
    ArithmeticBandGeometry.Partition.mass,
    ArithmeticBandGeometry.Partition.center] using hbound

end BridgeData

end

end Erdos390.Full.PaperBridgeFit

end

/- Source module: Erdos390.Full.PaperCanonicalFullQuotientQScaledEventually -/
section


/-!
# Literal `q_n`-scaled paper form of the canonical full quotient gap

The probability law in the bridge is normalized, whereas the matrix
`\mathcal C^Z_\xi` in the paper carries the active-mass factor `q_n`.
This wrapper records that factor explicitly.  Thus its displayed conclusion
is the literal normalized version of (8.54), multiplied by `q_n` on both
sides; no rescaling is left to a downstream application.
-/

open scoped BigOperators
open Filter Metric Set

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

open ArithmeticModel ArithmeticBandGeometry FiniteProbability
open PaperGuardCensus RegularMeshPrimeCutoffs

namespace BridgeData

/-- Anchor-free, paper-scale, literal-infimum quotient gap with the paper's
active-mass factor `q_n` displayed on both sides. -/
theorem exists_paperFineMesh_cutoff_eventually_canonical_actualFullQuotient_qScaled :
    ∃ kappa : ℝ, 0 < kappa ∧
      ∃ w₀ : ℝ, 0 < w₀ ∧
      ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W →
      ∀ {delta eta : ℝ} (M : RegularRelativeMesh.Mesh delta eta)
        (hdelta : 0 < delta),
      delta + eta ≤ w₀ →
      ∀ {Head : Type*} [Fintype Head] [DecidableEq Head] [Nonempty Head],
      ∀ (Phead : Head → HeadPattern.Pattern),
        (∀ h : Head, ∀ p : ℕ,
          p ∈ (Phead h).primes ↔ p.Prime ∧ p ≤ W) →
      ∀ (I : PhysicalIntervals) (U : ℝ) (hU : 1 ≤ U)
        (hlowerOne : ∀ sigma, 1 ≤ I.lower sigma)
        (hupperU : ∀ sigma, I.upper sigma ≤ U),
      ∀ (Cprom Cbank : ℕ) (ledger : ∀ n, Ledger n Cprom Cbank),
      ∀ (a : NNReal) (marginFloor : ℝ), 0 < marginFloor →
      ∀ᶠ n : ℕ in atTop,
        ∀ (B : BridgeData Head (Fin (M.cellCount + 1))),
          B.sampleData.n = n → B.sampleData.W = W →
          ∀ (hBWlarge : 1 < B.sampleData.W),
          ∀ (hsep : physicalBound (I.upper .minus) B.sampleData.n <
              physicalBound (I.lower .plus) B.sampleData.n)
            (hremaining : ∀ c : Cell Head,
              (rawCell Phead I B.sampleData.n c \
                (ledger B.sampleData.n).guards).Nonempty),
          (hcanonical : B.sampleData = canonicalSampleData
            (W := B.sampleData.W) Phead I (ledger B.sampleData.n)
              hsep hremaining) →
          (∃ (hWne : B.sampleData.W ≠ 0)
              (S : ScaleSeparation M B.sampleData.n B.sampleData.W),
            B.partition = RegularMeshPrimeCutoffs.Mesh.canonicalPartition
              M hdelta B.n_gt_one hWne S) →
          ∀ (T : BarycentricTarget B.sampleData),
            marginFloor ≤ T.cellMassMargin →
            ∀ (hbaseline : B.baseline = T.baseline),
          ∀ (z : B.EffectiveParamSpace)
            (hz : z ∈ closedBall (0 : B.EffectiveParamSpace) (a : ℝ)),
          let xi : B.ParamSpace := B.effectiveParamEquiv z
          let gamma : ℝ :=
            B.canonicalEffectiveNuisanceGamma I U (3 * (a : ℝ)) T
          let hgamma : 0 < gamma :=
            B.canonicalEffectiveNuisanceGamma_pos I U (3 * (a : ℝ)) T
          let hgap : ∀ v, gamma * ‖v‖ ^ 2 ≤
              inner ℝ v (B.nuisanceCovarianceOperator xi v) := by
            intro v
            simpa only [gamma, xi] using
              B.canonicalEffectiveNuisanceGap_on_closedBall I a hU
                hlowerOne hupperU
                (by intro sigma; rw [hcanonical]; rfl)
                (by intro sigma; rw [hcanonical]; rfl)
                T hbaseline hBWlarge z hz v
          ∀ (b : Fin (M.cellCount + 1) → ℝ) (mu : ℝ),
            kappa * B.q *
                (⨅ lambda : ℝ, ∑ j : Fin (M.cellCount + 1),
                  B.harmonicMass j *
                    |b j - lambda * B.bandCenter j| ^ 2) ≤
              B.q * (B.tiltedLaw xi).covariance
                (B.nuisanceResidualScore xi hgamma hgap
                  (B.primeValuationScore
                    (B.partition.data.residual b mu)))
                (B.nuisanceResidualScore xi hgamma hgap
                  (B.primeValuationScore
                    (B.partition.data.residual b mu))) := by
  obtain ⟨kappa, hkappa, w₀, hw₀, W₀, hmain⟩ :=
    exists_paperFineMesh_cutoff_eventually_canonical_actualFullQuotientDistance
  refine ⟨kappa, hkappa, w₀, hw₀, W₀, ?_⟩
  intro W hW delta eta M hdelta hfine Head _instFintype
    _instDecidableEq _instNonempty Phead hhead I U hU hlowerOne hupperU
    Cprom Cbank ledger a marginFloor hmargin
  have hevent := hmain W hW M hdelta hfine Phead hhead I U hU
    hlowerOne hupperU Cprom Cbank ledger a marginFloor hmargin
  filter_upwards [hevent] with n hn
  intro B hBn hBW hBWlarge hsep hremaining hcanonical hpartition T
    hTmargin hbaseline z hz
  have h := hn B hBn hBW hBWlarge hsep hremaining hcanonical hpartition
    T hTmargin hbaseline z hz
  dsimp only at h ⊢
  intro b mu
  have hraw := h b mu
  have hq : 0 ≤ B.q := B.q_pos.le
  calc
    kappa * B.q *
          (⨅ lambda : ℝ, ∑ j : Fin (M.cellCount + 1),
            B.harmonicMass j * |b j - lambda * B.bandCenter j| ^ 2) =
        B.q * (kappa *
          (⨅ lambda : ℝ, ∑ j : Fin (M.cellCount + 1),
            B.harmonicMass j * |b j - lambda * B.bandCenter j| ^ 2)) := by
      ring
    _ ≤ B.q * (B.tiltedLaw (B.effectiveParamEquiv z)).covariance
          (B.nuisanceResidualScore (B.effectiveParamEquiv z)
            (B.canonicalEffectiveNuisanceGamma_pos
              I U (3 * (a : ℝ)) T)
            (by
              intro v
              simpa only using
                B.canonicalEffectiveNuisanceGap_on_closedBall I a hU
                  hlowerOne hupperU
                  (by intro sigma; rw [hcanonical]; rfl)
                  (by intro sigma; rw [hcanonical]; rfl)
                  T hbaseline hBWlarge z hz v)
            (B.primeValuationScore (B.partition.data.residual b mu)))
          (B.nuisanceResidualScore (B.effectiveParamEquiv z)
            (B.canonicalEffectiveNuisanceGamma_pos
              I U (3 * (a : ℝ)) T)
            (by
              intro v
              simpa only using
                B.canonicalEffectiveNuisanceGap_on_closedBall I a hU
                  hlowerOne hupperU
                  (by intro sigma; rw [hcanonical]; rfl)
                  (by intro sigma; rw [hcanonical]; rfl)
                  T hbaseline hBWlarge z hz v)
            (B.primeValuationScore (B.partition.data.residual b mu))) :=
      mul_le_mul_of_nonneg_left hraw hq

end BridgeData

end

end Erdos390.Full.PaperBridgeFit

end

/- Source module: Erdos390.Full.PaperCanonicalLemma84GapNuisanceEventually -/
section


/-!
# Assumption-free gap and nuisance half of paper Lemma 8.4

This wrapper records together the two lower bounds occurring in the paper's
Lemma 8.4: strict positivity/coercivity of the actual finite nuisance block,
and the literal `q_n`-scaled quotient gap after nuisance regression.  It
contains no caller-supplied convergence, row, anchor, or inverse hypothesis.
-/

open scoped BigOperators
open Filter Topology Metric Set

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

open ArithmeticModel ArithmeticBandGeometry FiniteProbability
open PaperGuardCensus RegularMeshPrimeCutoffs

namespace BridgeData

/-- Paper-scale canonical nuisance positivity and literal quotient gap. -/
theorem exists_paperFineMesh_cutoff_eventually_canonical_lemma84_gap_nuisance :
    ∃ kappa : ℝ, 0 < kappa ∧
      ∃ w₀ : ℝ, 0 < w₀ ∧
      ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W →
      ∀ {delta eta : ℝ} (M : RegularRelativeMesh.Mesh delta eta)
        (hdelta : 0 < delta),
      delta + eta ≤ w₀ →
      ∀ {Head : Type*} [Fintype Head] [DecidableEq Head] [Nonempty Head],
      ∀ (Phead : Head → HeadPattern.Pattern),
        (∀ h : Head, ∀ p : ℕ,
          p ∈ (Phead h).primes ↔ p.Prime ∧ p ≤ W) →
      ∀ (I : PhysicalIntervals) (U : ℝ) (hU : 1 ≤ U)
        (hlowerOne : ∀ sigma, 1 ≤ I.lower sigma)
        (hupperU : ∀ sigma, I.upper sigma ≤ U),
      ∀ (Cprom Cbank : ℕ) (ledger : ∀ n, Ledger n Cprom Cbank),
      ∀ (a : NNReal) (marginFloor : ℝ), 0 < marginFloor →
      ∀ᶠ n : ℕ in atTop,
        ∀ (B : BridgeData Head (Fin (M.cellCount + 1))),
          B.sampleData.n = n → B.sampleData.W = W →
          ∀ (hBWlarge : 1 < B.sampleData.W),
          ∀ (hsep : physicalBound (I.upper .minus) B.sampleData.n <
              physicalBound (I.lower .plus) B.sampleData.n)
            (hremaining : ∀ c : Cell Head,
              (rawCell Phead I B.sampleData.n c \
                (ledger B.sampleData.n).guards).Nonempty),
          (hcanonical : B.sampleData = canonicalSampleData
            (W := B.sampleData.W) Phead I (ledger B.sampleData.n)
              hsep hremaining) →
          (∃ (hWne : B.sampleData.W ≠ 0)
              (S : ScaleSeparation M B.sampleData.n B.sampleData.W),
            B.partition = RegularMeshPrimeCutoffs.Mesh.canonicalPartition
              M hdelta B.n_gt_one hWne S) →
          ∀ (T : BarycentricTarget B.sampleData),
            marginFloor ≤ T.cellMassMargin →
            ∀ (hbaseline : B.baseline = T.baseline),
          ∀ (z : B.EffectiveParamSpace)
            (hz : z ∈ closedBall (0 : B.EffectiveParamSpace) (a : ℝ)),
            let xi : B.ParamSpace := B.effectiveParamEquiv z
            let gamma : ℝ :=
              B.canonicalEffectiveNuisanceGamma I U (3 * (a : ℝ)) T
            let hgamma : 0 < gamma :=
              B.canonicalEffectiveNuisanceGamma_pos I U (3 * (a : ℝ)) T
            let hgap : ∀ v, gamma * ‖v‖ ^ 2 ≤
                inner ℝ v (B.nuisanceCovarianceOperator xi v) := by
              intro v
              simpa only [gamma, xi] using
                B.canonicalEffectiveNuisanceGap_on_closedBall I a hU
                  hlowerOne hupperU
                  (by intro sigma; rw [hcanonical]; rfl)
                  (by intro sigma; rw [hcanonical]; rfl)
                  T hbaseline hBWlarge z hz v
            (0 < gamma) ∧
            (∀ v, gamma * ‖v‖ ^ 2 ≤
              inner ℝ v (B.nuisanceCovarianceOperator xi v)) ∧
            ∀ (b : Fin (M.cellCount + 1) → ℝ) (mu : ℝ),
              kappa * B.q *
                  (⨅ lambda : ℝ, ∑ j : Fin (M.cellCount + 1),
                    B.harmonicMass j *
                      |b j - lambda * B.bandCenter j| ^ 2) ≤
                B.q * (B.tiltedLaw xi).covariance
                  (B.nuisanceResidualScore xi hgamma hgap
                    (B.primeValuationScore
                      (B.partition.data.residual b mu)))
                  (B.nuisanceResidualScore xi hgamma hgap
                    (B.primeValuationScore
                      (B.partition.data.residual b mu))) := by
  obtain ⟨kappa, hkappa, w₀, hw₀, W₀, hmain⟩ :=
    exists_paperFineMesh_cutoff_eventually_canonical_actualFullQuotient_qScaled
  refine ⟨kappa, hkappa, w₀, hw₀, W₀, ?_⟩
  intro W hW delta eta M hdelta hfine Head _instFintype
    _instDecidable _instNonempty Phead hhead I U hU hlowerOne hupperU
    Cprom Cbank ledger a marginFloor hmargin
  have hevent := hmain W hW M hdelta hfine Phead hhead I U hU
    hlowerOne hupperU Cprom Cbank ledger a marginFloor hmargin
  filter_upwards [hevent] with n hn
  intro B hBn hBW hBWlarge hsep hremaining hcanonical hpartition
    T hTmargin hbaseline z hz
  have hquotient := hn B hBn hBW hBWlarge hsep hremaining hcanonical
    hpartition T hTmargin hbaseline z hz
  dsimp only at hquotient ⊢
  refine ⟨B.canonicalEffectiveNuisanceGamma_pos
      I U (3 * (a : ℝ)) T, ?_, hquotient⟩
  intro v
  exact B.canonicalEffectiveNuisanceGap_on_closedBall I a hU
    hlowerOne hupperU
    (by intro sigma; rw [hcanonical]; rfl)
    (by intro sigma; rw [hcanonical]; rfl)
    T hbaseline hBWlarge z hz v

end BridgeData

end

end Erdos390.Full.PaperBridgeFit

end

/- Source module: Erdos390.Full.PaperActualFullOrdinaryRowTransfer -/
section


/-!
# Ordinary raw-row transfer to the actual full band operator

The sharp transfer divides an output row by its band centre.  The fast
solve instead uses an ordinary raw coefficient, so the prime rows are first
averaged with their exact harmonic mass.  The factor `1/p` then cancels that
mass and no moving-centre loss occurs.
-/

open scoped BigOperators

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

open ArithmeticModel ArithmeticBandGeometry
open PaperWeightedInverseExport
open PrimePowerSharpBandTransfer
open SquarefreeSharpBandTransfer
open SquarefreeCovarianceReference

namespace BridgeData

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]
  (B : BridgeData Head Band)







/-- Triangle from the literal actual full row to the signed Dickman
reference row in the ordinary raw norm. -/
theorem fullBandRow_sub_referenceBandRow_le_ordinary
    [Nonempty Head]
    (xi : B.ParamSpace) (q : B.RawBandGauge)
    {Esquare R : ℝ}
    (hsquare : ∀ i : Band,
      |squarefreeBandRow (B.actualValuationLaw xi) B.partition q.1 i -
        referenceBandRow B.partition q.1 i| ≤ ‖q‖ * Esquare)
    (hfull : ∀ i : Band,
      |fullBandRow (B.actualValuationLaw xi) B.partition q.1 i -
        squarefreeBandRow (B.actualValuationLaw xi) B.partition q.1 i| ≤
          ‖q‖ * R)
    (i : Band) :
    |fullBandRow (B.actualValuationLaw xi) B.partition q.1 i -
        referenceBandRow B.partition q.1 i| ≤
      ‖q‖ * (R + Esquare) := by
  calc
    |fullBandRow (B.actualValuationLaw xi) B.partition q.1 i -
        referenceBandRow B.partition q.1 i| ≤
      |fullBandRow (B.actualValuationLaw xi) B.partition q.1 i -
        squarefreeBandRow (B.actualValuationLaw xi) B.partition q.1 i| +
      |squarefreeBandRow (B.actualValuationLaw xi) B.partition q.1 i -
        referenceBandRow B.partition q.1 i| := by
      have := abs_add_le
        (fullBandRow (B.actualValuationLaw xi) B.partition q.1 i -
          squarefreeBandRow (B.actualValuationLaw xi) B.partition q.1 i)
        (squarefreeBandRow (B.actualValuationLaw xi) B.partition q.1 i -
          referenceBandRow B.partition q.1 i)
      simpa only [sub_add_sub_cancel] using this
    _ ≤ ‖q‖ * R + ‖q‖ * Esquare := add_le_add (hfull i) (hsquare i)
    _ = ‖q‖ * (R + Esquare) := by ring

end BridgeData
end
end Erdos390.Full.PaperBridgeFit

end

/- Source module: Erdos390.Full.PaperActualFullOrdinaryProjectionConnector -/
section


/-!
# Ordinary projected transfer from the Dickman reference to the actual full row

The row estimates are first established before gauge projection.  This file
performs the exact finite projection and identifies the projected Dickman
reference with the literal endpoint arithmetic raw operator.  The only
projection loss is the displayed first-moment/centre-energy ratio; there is
no division by the moving low-band centre.
-/

open scoped BigOperators

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

open ArithmeticBandGeometry
open PaperWeightedInverseExport
open PrimePowerSharpBandTransfer
open SquarefreeSharpBandTransfer
open SquarefreeCovarianceReference
open SquarefreeReferenceOperatorIdentification
open PositiveCellTransfer

namespace BridgeData

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]
  (B : BridgeData Head Band)

/-- The actual full band map is exactly the projection of its literal full
valuation row. -/
theorem actualBandFullLinearMap_eq_projectedFullBandRow
    [Nonempty Head] [Nonempty Band]
    (xi : B.ParamSpace) (q : B.RawBandGauge) :
    B.actualBandFullLinearMap xi q =
      B.projectRawBandVector (fun i ↦
        fullBandRow (B.actualValuationLaw xi) B.partition q.1 i) := by
  change B.projectRawBandVector
      (B.normalizedBandCovarianceRow xi (B.bandRegressionScore q)) = _
  congr 1
  funext i
  exact (B.fullBandRow_actualValuationLaw_eq_normalizedBandCovarianceRow
    xi q i).symm

/-- Coordinatewise ordinary full-to-reference control survives the exact
arithmetic gauge projection with only the first-moment ratio loss. -/
theorem actualBandFull_sub_projectedReference_norm_le_ordinary
    [Nonempty Head] [Nonempty Band]
    (xi : B.ParamSpace) (q : B.RawBandGauge)
    {E Rproj : ℝ}
    (hE : 0 ≤ E) (hRproj : 0 ≤ Rproj)
    (hRatio : (∑ j : Band,
        B.harmonicMass j * B.bandCenter j) ≤
      Rproj * MovingLowGaugeTransfer.sharpWeightTotal
        B.harmonicMass B.bandCenter)
    (hrow : ∀ i : Band,
      |fullBandRow (B.actualValuationLaw xi) B.partition q.1 i -
          referenceBandRow B.partition q.1 i| ≤ ‖q‖ * E) :
    ‖B.actualBandFullLinearMap xi q -
        B.projectRawBandVector
          (fun i ↦ referenceBandRow B.partition q.1 i)‖ ≤
      (1 + Rproj) * E * ‖q‖ := by
  let full : Band → ℝ := fun i ↦
    fullBandRow (B.actualValuationLaw xi) B.partition q.1 i
  let reference : Band → ℝ := fun i ↦
    referenceBandRow B.partition q.1 i
  have hC : 0 ≤ ‖q‖ * E := mul_nonneg (norm_nonneg q) hE
  have hproject :
      ‖B.projectRawBandVector (full - reference)‖ ≤
        (1 + Rproj) * (‖q‖ * E) := by
    exact B.projectRawBandVector_norm_le_of_moment_ratio
      (full - reference) hC hRproj (by
        intro i
        simpa only [full, reference, Pi.sub_apply] using hrow i) hRatio
  rw [B.actualBandFullLinearMap_eq_projectedFullBandRow xi q]
  rw [← B.projectRawBandVector_sub]
  simpa only [full, reference, mul_assoc, mul_left_comm, mul_comm] using
    hproject

/-- Direct form using the squarefree-profile error and Lemma 7.5's weighted
full-versus-squarefree row. -/
theorem actualBandFull_sub_projectedReference_norm_le_of_rows_ordinary
    [Nonempty Head] [Nonempty Band]
    (xi : B.ParamSpace) (q : B.RawBandGauge)
    {Esquare Rpow Rproj : ℝ}
    (hEsquare : 0 ≤ Esquare) (hRpow : 0 ≤ Rpow)
    (hRproj : 0 ≤ Rproj)
    (hRatio : (∑ j : Band,
        B.harmonicMass j * B.bandCenter j) ≤
      Rproj * MovingLowGaugeTransfer.sharpWeightTotal
        B.harmonicMass B.bandCenter)
    (hsquare : ∀ i : Band,
      |SquarefreeSharpBandTransfer.squarefreeBandRow
          (B.actualValuationLaw xi) B.partition q.1 i -
        referenceBandRow B.partition q.1 i| ≤ ‖q‖ * Esquare)
    (hfull : ∀ i : Band,
      |fullBandRow (B.actualValuationLaw xi) B.partition q.1 i -
        SquarefreeSharpBandTransfer.squarefreeBandRow
          (B.actualValuationLaw xi) B.partition q.1 i| ≤
          ‖q‖ * Rpow) :
    ‖B.actualBandFullLinearMap xi q -
        B.projectRawBandVector
          (fun i ↦ referenceBandRow B.partition q.1 i)‖ ≤
      (1 + Rproj) * (Rpow + Esquare) * ‖q‖ := by
  have hrow : ∀ i : Band,
      |fullBandRow (B.actualValuationLaw xi) B.partition q.1 i -
          referenceBandRow B.partition q.1 i| ≤
        ‖q‖ * (Rpow + Esquare) := by
    intro i
    exact B.fullBandRow_sub_referenceBandRow_le_ordinary
      xi q hsquare hfull i
  exact B.actualBandFull_sub_projectedReference_norm_le_ordinary
    xi q (add_nonneg hRpow hEsquare) hRproj hRatio hrow

/-- The projected reference in the preceding theorems is literally the
paper's endpoint arithmetic raw linear map. -/
theorem projectRawBandVector_referenceBandRow_eq_projectedRawLinearMap
    [Nonempty Band]
    (Ecert : IntervalCertificate B.partition)
    (q : B.RawBandGauge) :
    B.projectRawBandVector
        (fun i ↦ referenceBandRow B.partition q.1 i) =
      projectedRawLinearMap
        (CompressedArithmeticOperator.arithmeticDiagonal
          (ArithmeticModel.y B.sampleData.n) Ecert.lower Ecert.upper)
        (CompressedArithmeticOperator.arithmeticKernel
          (ArithmeticModel.y B.sampleData.n) Ecert.lower Ecert.upper)
        B.harmonicMass B.bandCenter
        (ne_of_gt B.sharpBandWeightTotal_pos) q := by
  apply Subtype.ext
  change MovingLowGaugeTransfer.weightedGaugeProjection
      B.harmonicMass B.bandCenter
        (fun i ↦ referenceBandRow B.partition q.1 i) =
    MovingLowGaugeTransfer.weightedGaugeProjection
      B.harmonicMass B.bandCenter
        (rawOperator
          (CompressedArithmeticOperator.arithmeticDiagonal
            (ArithmeticModel.y B.sampleData.n) Ecert.lower Ecert.upper)
          (CompressedArithmeticOperator.arithmeticKernel
            (ArithmeticModel.y B.sampleData.n) Ecert.lower Ecert.upper)
          q.1)
  congr 1
  funext i
  exact referenceBandRow_eq_rawOperator Ecert q.1 i

/-- Final finite ordinary perturbation estimate with the endpoint arithmetic
reference displayed as a linear map. -/
theorem actualBandFull_sub_projectedArithmeticRaw_norm_le_of_rows_ordinary
    [Nonempty Head] [Nonempty Band]
    (xi : B.ParamSpace) (Ecert : IntervalCertificate B.partition)
    (q : B.RawBandGauge)
    {Esquare Rpow Rproj : ℝ}
    (hEsquare : 0 ≤ Esquare) (hRpow : 0 ≤ Rpow)
    (hRproj : 0 ≤ Rproj)
    (hRatio : (∑ j : Band,
        B.harmonicMass j * B.bandCenter j) ≤
      Rproj * MovingLowGaugeTransfer.sharpWeightTotal
        B.harmonicMass B.bandCenter)
    (hsquare : ∀ i : Band,
      |SquarefreeSharpBandTransfer.squarefreeBandRow
          (B.actualValuationLaw xi) B.partition q.1 i -
        referenceBandRow B.partition q.1 i| ≤ ‖q‖ * Esquare)
    (hfull : ∀ i : Band,
      |fullBandRow (B.actualValuationLaw xi) B.partition q.1 i -
        SquarefreeSharpBandTransfer.squarefreeBandRow
          (B.actualValuationLaw xi) B.partition q.1 i| ≤
          ‖q‖ * Rpow) :
    ‖B.actualBandFullLinearMap xi q -
        projectedRawLinearMap
          (CompressedArithmeticOperator.arithmeticDiagonal
            (ArithmeticModel.y B.sampleData.n) Ecert.lower Ecert.upper)
          (CompressedArithmeticOperator.arithmeticKernel
            (ArithmeticModel.y B.sampleData.n) Ecert.lower Ecert.upper)
          B.harmonicMass B.bandCenter
          (ne_of_gt B.sharpBandWeightTotal_pos) q‖ ≤
      (1 + Rproj) * (Rpow + Esquare) * ‖q‖ := by
  rw [← B.projectRawBandVector_referenceBandRow_eq_projectedRawLinearMap
    Ecert q]
  exact B.actualBandFull_sub_projectedReference_norm_le_of_rows_ordinary
    xi q hEsquare hRpow hRproj hRatio hsquare hfull

end BridgeData

end

end Erdos390.Full.PaperBridgeFit

end

/- Source module: Erdos390.Full.OrdinaryRawInverseTransfer -/
section


/-!
# Stable inversion in the literal ordinary raw supremum norm

This elementary connector is deliberately stated in the ambient norm of a
finite raw gauge space.  In the applications that norm is the ordinary
coordinate supremum norm, not the sharp norm obtained after division by a
moving band centre.

The theorem is useful when invertibility has already been obtained (for
example from the independently proved sharp estimate), while a separate
maximum-principle or continuum argument supplies an ordinary inverse estimate
for a reference operator.  It transfers that estimate without changing the
map and without assuming an ordinary inverse as a structure field.
-/

noncomputable section

namespace Erdos390.Full.OrdinaryRawInverseTransfer

variable {V : Type*} [NormedAddCommGroup V] [Module ℝ V]

/-- Absorption of an ordinary-norm operator perturbation.  The equivalence
`e` is retained literally; no replacement operator is constructed. -/
theorem inverse_norm_le_of_reference
    (e : V ≃ₗ[ℝ] V) (reference : V →ₗ[ℝ] V)
    {C delta : ℝ}
    (hC : 0 ≤ C)
    (hsmall : C * delta ≤ 1 / 2)
    (href : ∀ q, ‖q‖ ≤ C * ‖reference q‖)
    (herror : ∀ q, ‖reference q - e q‖ ≤ delta * ‖q‖) :
    ∀ v, ‖e.symm v‖ ≤ (2 * C) * ‖v‖ := by
  intro v
  let q : V := e.symm v
  have heq : e q = v := e.apply_symm_apply v
  have htriangle : ‖reference q‖ ≤
      ‖e q‖ + ‖reference q - e q‖ := by
    calc
      ‖reference q‖ = ‖e q + (reference q - e q)‖ := by
        congr 1
        abel
      _ ≤ ‖e q‖ + ‖reference q - e q‖ :=
        norm_add_le (e q) (reference q - e q)
  have hpert : C * ‖reference q - e q‖ ≤
      (C * delta) * ‖q‖ := by
    calc
      C * ‖reference q - e q‖ ≤ C * (delta * ‖q‖) :=
        mul_le_mul_of_nonneg_left (herror q) hC
      _ = (C * delta) * ‖q‖ := by ring
  have habsorb : (C * delta) * ‖q‖ ≤ (1 / 2) * ‖q‖ :=
    mul_le_mul_of_nonneg_right hsmall (norm_nonneg q)
  have hq : ‖q‖ ≤ C * ‖v‖ + (1 / 2) * ‖q‖ := by
    calc
      ‖q‖ ≤ C * ‖reference q‖ := href q
      _ ≤ C * (‖e q‖ + ‖reference q - e q‖) :=
        mul_le_mul_of_nonneg_left htriangle hC
      _ = C * ‖e q‖ + C * ‖reference q - e q‖ := by ring
      _ ≤ C * ‖e q‖ + (C * delta) * ‖q‖ :=
        add_le_add le_rfl hpert
      _ = C * ‖v‖ + (C * delta) * ‖q‖ := by rw [heq]
      _ ≤ C * ‖v‖ + (1 / 2) * ‖q‖ :=
        add_le_add le_rfl habsorb
  change ‖q‖ ≤ (2 * C) * ‖v‖
  linarith

end Erdos390.Full.OrdinaryRawInverseTransfer

end

/- Source module: Erdos390.Full.PaperActualSchurOrdinaryRow -/
section


/-!
# Ordinary raw-norm nuisance--Schur transfer

The sharp Schur estimate divides by the least band centre.  That loss is
appropriate for a sharp input, but it is spurious for the ordinary raw
supremum norm required by the fast solve.  Here both prime-band summations
are performed before projection.  The result depends on the total harmonic
mass, which is later paired with the genuinely vanishing marked rate; it has
no factor `1 / min alpha`.
-/

open scoped BigOperators

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

open ArithmeticBandGeometry
open OrdinaryRawInverseTransfer

namespace BridgeData

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]
  (B : BridgeData Head Band)







/-- Once a literal Schur equivalence is known from the sharp argument, an
ordinary inverse estimate for the full raw operator and the just-proved raw
nuisance estimate give the ordinary inverse for the *same* equivalence. -/
theorem actualBandSchur_inverse_norm_le_of_full_ordinary
    [Nonempty Head] [Nonempty Band]
    (xi : B.ParamSpace) {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (e : B.RawBandGauge ≃ₗ[ℝ] B.RawBandGauge)
    (he : ∀ q, e q = B.actualBandSchurLinearMap xi hgamma hgap q)
    {C delta : ℝ} (hC : 0 ≤ C)
    (hsmall : C * delta ≤ 1 / 2)
    (hfull : ∀ q : B.RawBandGauge,
      ‖q‖ ≤ C * ‖B.actualBandFullLinearMap xi q‖)
    (herror : ∀ q : B.RawBandGauge,
      ‖B.actualBandSchurLinearMap xi hgamma hgap q -
          B.actualBandFullLinearMap xi q‖ ≤ delta * ‖q‖) :
    ∀ v, ‖e.symm v‖ ≤ (2 * C) * ‖v‖ := by
  apply inverse_norm_le_of_reference e
    (B.actualBandFullLinearMap xi) hC hsmall hfull
  intro q
  rw [he q, norm_sub_rev]
  exact herror q

end BridgeData

end

end Erdos390.Full.PaperBridgeFit

end

/- Source module: Erdos390.Full.PaperActualSchurOrdinaryEndpointConnector -/
section


/-!
# Same-map ordinary inverse from the endpoint reference

This file performs the last two deterministic perturbations in ordinary raw
norm.  The reference is the literal endpoint arithmetic operator, the first
perturbation is the actual full-valuation row, and the second is the literal
nuisance Schur correction.  The equivalence in the conclusion is the same
equivalence supplied by the sharp existence argument.
-/

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

open ArithmeticBandGeometry
open PaperWeightedInverseExport
open SquarefreeReferenceOperatorIdentification
open PositiveCellTransfer

namespace BridgeData

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]
  (B : BridgeData Head Band)

/-- A reference ordinary inverse and an actual-full row perturbation give
an ordinary inverse for the literal actual-full map. -/
theorem actualBandFull_ordinary_inverse_of_endpoint_reference
    [Nonempty Head] [Nonempty Band]
    (xi : B.ParamSpace) (Ecert : IntervalCertificate B.partition)
    {Cref Esquare Rpow Rproj : ℝ}
    (hCref : 0 ≤ Cref)
    (hEsquare : 0 ≤ Esquare) (hRpow : 0 ≤ Rpow)
    (hRproj : 0 ≤ Rproj)
    (hRatio : (∑ j : Band,
        B.harmonicMass j * B.bandCenter j) ≤
      Rproj * MovingLowGaugeTransfer.sharpWeightTotal
        B.harmonicMass B.bandCenter)
    (hReference : ∀ q : B.RawBandGauge,
      ‖q‖ ≤ Cref *
        ‖projectedRawLinearMap
          (CompressedArithmeticOperator.arithmeticDiagonal
            (ArithmeticModel.y B.sampleData.n) Ecert.lower Ecert.upper)
          (CompressedArithmeticOperator.arithmeticKernel
            (ArithmeticModel.y B.sampleData.n) Ecert.lower Ecert.upper)
          B.harmonicMass B.bandCenter
          (ne_of_gt B.sharpBandWeightTotal_pos) q‖)
    (hsquare : ∀ q : B.RawBandGauge, ∀ i : Band,
      |SquarefreeSharpBandTransfer.squarefreeBandRow
          (B.actualValuationLaw xi) B.partition q.1 i -
        SquarefreeSharpBandTransfer.referenceBandRow
          B.partition q.1 i| ≤ ‖q‖ * Esquare)
    (hfull : ∀ q : B.RawBandGauge, ∀ i : Band,
      |PrimePowerSharpBandTransfer.fullBandRow
          (B.actualValuationLaw xi) B.partition q.1 i -
        SquarefreeSharpBandTransfer.squarefreeBandRow
          (B.actualValuationLaw xi) B.partition q.1 i| ≤
          ‖q‖ * Rpow)
    (hSmallFull :
      Cref * ((1 + Rproj) * (Rpow + Esquare)) ≤ 1 / 2) :
    ∀ q : B.RawBandGauge,
      ‖q‖ ≤ (2 * Cref) * ‖B.actualBandFullLinearMap xi q‖ := by
  let deltaFull : ℝ := (1 + Rproj) * (Rpow + Esquare)
  have herror (q : B.RawBandGauge) :
      ‖B.actualBandFullLinearMap xi q -
          projectedRawLinearMap
            (CompressedArithmeticOperator.arithmeticDiagonal
              (ArithmeticModel.y B.sampleData.n) Ecert.lower Ecert.upper)
            (CompressedArithmeticOperator.arithmeticKernel
              (ArithmeticModel.y B.sampleData.n) Ecert.lower Ecert.upper)
            B.harmonicMass B.bandCenter
            (ne_of_gt B.sharpBandWeightTotal_pos) q‖ ≤
        deltaFull * ‖q‖ := by
    simpa only [deltaFull] using
      B.actualBandFull_sub_projectedArithmeticRaw_norm_le_of_rows_ordinary
        xi Ecert q hEsquare hRpow hRproj hRatio
          (hsquare q) (hfull q)
  intro q
  let Aref := projectedRawLinearMap
    (CompressedArithmeticOperator.arithmeticDiagonal
      (ArithmeticModel.y B.sampleData.n) Ecert.lower Ecert.upper)
    (CompressedArithmeticOperator.arithmeticKernel
      (ArithmeticModel.y B.sampleData.n) Ecert.lower Ecert.upper)
    B.harmonicMass B.bandCenter
    (ne_of_gt B.sharpBandWeightTotal_pos)
  have href := hReference q
  have htri : ‖Aref q‖ ≤
      ‖B.actualBandFullLinearMap xi q‖ + deltaFull * ‖q‖ := by
    have hid : Aref q = B.actualBandFullLinearMap xi q -
        (B.actualBandFullLinearMap xi q - Aref q) := by abel
    calc
      ‖Aref q‖ = ‖B.actualBandFullLinearMap xi q -
          (B.actualBandFullLinearMap xi q - Aref q)‖ := congrArg norm hid
      _ ≤ ‖B.actualBandFullLinearMap xi q‖ +
          ‖B.actualBandFullLinearMap xi q - Aref q‖ := norm_sub_le _ _
      _ ≤ ‖B.actualBandFullLinearMap xi q‖ + deltaFull * ‖q‖ :=
        add_le_add le_rfl (by simpa only [Aref] using herror q)
  have hraw : ‖q‖ ≤ Cref * ‖B.actualBandFullLinearMap xi q‖ +
      (Cref * deltaFull) * ‖q‖ := by
    calc
      ‖q‖ ≤ Cref * ‖Aref q‖ := by simpa only [Aref] using href
      _ ≤ Cref *
          (‖B.actualBandFullLinearMap xi q‖ + deltaFull * ‖q‖) :=
        mul_le_mul_of_nonneg_left htri hCref
      _ = Cref * ‖B.actualBandFullLinearMap xi q‖ +
          (Cref * deltaFull) * ‖q‖ := by ring
  have habsorb : (Cref * deltaFull) * ‖q‖ ≤
      (1 / 2) * ‖q‖ :=
    mul_le_mul_of_nonneg_right (by
      simpa only [deltaFull] using hSmallFull) (norm_nonneg q)
  have hhalf : ‖q‖ ≤ Cref * ‖B.actualBandFullLinearMap xi q‖ +
      (1 / 2) * ‖q‖ := hraw.trans (add_le_add le_rfl habsorb)
  linarith

/-- Exact terminal: the sharp argument supplies the literal Schur
equivalence, while the endpoint and nuisance estimates give an ordinary
inverse for that same map. -/
theorem actualBandSchur_sameEquiv_ordinary_inverse_of_endpoint_reference
    [Nonempty Head] [Nonempty Band]
    (xi : B.ParamSpace) {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (e : B.RawBandGauge ≃ₗ[ℝ] B.RawBandGauge)
    (he : ∀ q, e q = B.actualBandSchurLinearMap xi hgamma hgap q)
    (Ecert : IntervalCertificate B.partition)
    {Cref Esquare Rpow Rproj deltaSchur : ℝ}
    (hCref : 0 ≤ Cref)
    (hEsquare : 0 ≤ Esquare) (hRpow : 0 ≤ Rpow)
    (hRproj : 0 ≤ Rproj)
    (hRatio : (∑ j : Band,
        B.harmonicMass j * B.bandCenter j) ≤
      Rproj * MovingLowGaugeTransfer.sharpWeightTotal
        B.harmonicMass B.bandCenter)
    (hReference : ∀ q : B.RawBandGauge,
      ‖q‖ ≤ Cref *
        ‖projectedRawLinearMap
          (CompressedArithmeticOperator.arithmeticDiagonal
            (ArithmeticModel.y B.sampleData.n) Ecert.lower Ecert.upper)
          (CompressedArithmeticOperator.arithmeticKernel
            (ArithmeticModel.y B.sampleData.n) Ecert.lower Ecert.upper)
          B.harmonicMass B.bandCenter
          (ne_of_gt B.sharpBandWeightTotal_pos) q‖)
    (hsquare : ∀ q : B.RawBandGauge, ∀ i : Band,
      |SquarefreeSharpBandTransfer.squarefreeBandRow
          (B.actualValuationLaw xi) B.partition q.1 i -
        SquarefreeSharpBandTransfer.referenceBandRow
          B.partition q.1 i| ≤ ‖q‖ * Esquare)
    (hfull : ∀ q : B.RawBandGauge, ∀ i : Band,
      |PrimePowerSharpBandTransfer.fullBandRow
          (B.actualValuationLaw xi) B.partition q.1 i -
        SquarefreeSharpBandTransfer.squarefreeBandRow
          (B.actualValuationLaw xi) B.partition q.1 i| ≤
          ‖q‖ * Rpow)
    (hSmallFull :
      Cref * ((1 + Rproj) * (Rpow + Esquare)) ≤ 1 / 2)
    (hSchurError : ∀ q : B.RawBandGauge,
      ‖B.actualBandSchurLinearMap xi hgamma hgap q -
          B.actualBandFullLinearMap xi q‖ ≤ deltaSchur * ‖q‖)
    (hSmallSchur : (2 * Cref) * deltaSchur ≤ 1 / 2) :
    (∀ q, e q = B.actualBandSchurLinearMap xi hgamma hgap q) ∧
      ∀ v, ‖e.symm v‖ ≤ (4 * Cref) * ‖v‖ := by
  have hFullInverse :=
    B.actualBandFull_ordinary_inverse_of_endpoint_reference
      xi Ecert hCref hEsquare hRpow hRproj hRatio hReference
      hsquare hfull hSmallFull
  refine ⟨he, ?_⟩
  have hCtwo : 0 ≤ 2 * Cref := mul_nonneg (by norm_num) hCref
  have hinv := B.actualBandSchur_inverse_norm_le_of_full_ordinary
    xi hgamma hgap e he hCtwo hSmallSchur hFullInverse hSchurError
  intro v
  have hconstant : 2 * (2 * Cref) * ‖v‖ =
      (4 * Cref) * ‖v‖ := by ring
  exact (hinv v).trans_eq hconstant

end BridgeData
end
end Erdos390.Full.PaperBridgeFit

end

/- Source module: Erdos390.Full.PaperActualSchurEndpointReferenceTransport -/
section


/-!
# Transporting an endpoint reference to a literal bridge partition

The endpoint theorem naturally returns a canonical partition as a local
witness.  A bridge constructed from the same canonical endpoint family may
carry propositionally different proofs of the scale inequalities.  This
small deterministic lemma performs the proof-irrelevant transport once and
then invokes the same-equivalence ordinary Schur connector.
-/

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

open ArithmeticBandGeometry PaperWeightedInverseExport
open SquarefreeReferenceOperatorIdentification PositiveCellTransfer

namespace BridgeData

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]
  (B : BridgeData Head Band)

/-- Endpoint-reference connector allowing the reference partition to be
identified propositionally with the literal partition stored in `B`. -/
theorem actualBandSchur_sameEquiv_ordinary_inverse_of_partition_eq_endpoint_reference
    [Nonempty Head] [Nonempty Band]
    (xi : B.ParamSpace) {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (e : B.RawBandGauge ≃ₗ[ℝ] B.RawBandGauge)
    (he : ∀ q, e q = B.actualBandSchurLinearMap xi hgamma hgap q)
    (P : ArithmeticBandGeometry.Partition
      B.sampleData.n B.sampleData.W Band)
    (hpartition : B.partition = P)
    (Ecert : IntervalCertificate P)
    {Cref Esquare Rpow Rproj deltaSchur : ℝ}
    (hCref : 0 ≤ Cref)
    (hEsquare : 0 ≤ Esquare) (hRpow : 0 ≤ Rpow)
    (hRproj : 0 ≤ Rproj)
    (hRatio : (∑ j : Band,
        B.harmonicMass j * B.bandCenter j) ≤
      Rproj * MovingLowGaugeTransfer.sharpWeightTotal
        B.harmonicMass B.bandCenter)
    (hReference : ∀ q : RawGaugeSpace P.mass P.center,
      ‖q‖ ≤ Cref *
        ‖projectedRawLinearMap
          (CompressedArithmeticOperator.arithmeticDiagonal
            (ArithmeticModel.y B.sampleData.n) Ecert.lower Ecert.upper)
          (CompressedArithmeticOperator.arithmeticKernel
            (ArithmeticModel.y B.sampleData.n) Ecert.lower Ecert.upper)
          P.mass P.center
          (by
            unfold MovingLowGaugeTransfer.sharpWeightTotal
              MovingLowGaugeTransfer.sharpWeight
            simpa only [Erdos390.Lemma84.WeightedBandData.centerEnergy,
              Erdos390.Lemma84.WeightedBandData.bandNormSq,
              Erdos390.Lemma84.WeightedBandData.bandInner, pow_two,
              mul_assoc] using
                (P.centerEnergy_pos B.n_gt_one).ne') q‖)
    (hsquare : ∀ q : B.RawBandGauge, ∀ i : Band,
      |SquarefreeSharpBandTransfer.squarefreeBandRow
          (B.actualValuationLaw xi) B.partition q.1 i -
        SquarefreeSharpBandTransfer.referenceBandRow
          B.partition q.1 i| ≤ ‖q‖ * Esquare)
    (hfull : ∀ q : B.RawBandGauge, ∀ i : Band,
      |PrimePowerSharpBandTransfer.fullBandRow
          (B.actualValuationLaw xi) B.partition q.1 i -
        SquarefreeSharpBandTransfer.squarefreeBandRow
          (B.actualValuationLaw xi) B.partition q.1 i| ≤
          ‖q‖ * Rpow)
    (hSmallFull :
      Cref * ((1 + Rproj) * (Rpow + Esquare)) ≤ 1 / 2)
    (hSchurError : ∀ q : B.RawBandGauge,
      ‖B.actualBandSchurLinearMap xi hgamma hgap q -
          B.actualBandFullLinearMap xi q‖ ≤ deltaSchur * ‖q‖)
    (hSmallSchur : (2 * Cref) * deltaSchur ≤ 1 / 2) :
    (∀ q, e q = B.actualBandSchurLinearMap xi hgamma hgap q) ∧
      ∀ v, ‖e.symm v‖ ≤ (4 * Cref) * ‖v‖ := by
  subst P
  exact B.actualBandSchur_sameEquiv_ordinary_inverse_of_endpoint_reference
    xi hgamma hgap e he Ecert hCref hEsquare hRpow hRproj hRatio
      hReference hsquare hfull hSmallFull hSchurError hSmallSchur

end BridgeData

end

end Erdos390.Full.PaperBridgeFit

end

/- Source module: Erdos390.Full.PaperCanonicalPrimeGraphActualSchurEventually -/
section


/-!
# Canonical prime-graph inverse through the literal nuisance Schur complement

This is the paper-order, assumption-free closure of the sharp arithmetic
reference argument.  The structural cutoff is chosen before the regular
mesh, the finite head family, and the effective tilt ball.  After those data
are fixed, all squarefree-profile, full-valuation, moving-low, marked-row,
and nuisance-Schur smallness estimates are constructed internally.

The final equivalence is not an abstract comparison map: it is pointwise
equal to the literal finite arithmetic map `actualBandSchurLinearMap`.
-/

open scoped BigOperators
open Filter Topology Metric Set

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

open ArithmeticModel ArithmeticBandGeometry FiniteProbability
open PrimeSums PaperWeightedInverseExport MovingLowGaugeTransfer
open OmittedTiltPairChamber PaperPrimePowerChamberError
open PaperGuardCensus RegularMeshPrimeCutoffs

namespace BridgeData



set_option maxHeartbeats 1000000 in
/-- Final fine-mesh form.  The anchor block is no longer data supplied by a
caller: it is constructed uniformly from the regular mesh itself.  Thus the
only mesh premise is the paper's single quantitative fineness condition. -/
theorem exists_fineMesh_cutoff_eventually_actualBandSchur_primeGraph_inverse :
    ∃ meshTol : ℝ, 0 < meshTol ∧
      ∃ Cschur : ℝ, 0 < Cschur ∧
      ∃ W₀ : ℕ,
      ∀ W : ℕ, W₀ ≤ W →
      ∀ {delta eta : ℝ} (M : RegularRelativeMesh.Mesh delta eta)
        (hdelta : 0 < delta),
        delta + M.ratio ≤ meshTol →
        ∀ (Head : Type*) [Fintype Head] [DecidableEq Head] [Nonempty Head],
        ∀ (Phead : Head → HeadPattern.Pattern),
          (∀ h : Head, ∀ p : ℕ,
            p ∈ (Phead h).primes ↔ p.Prime ∧ p ≤ W) →
        ∀ (I : PhysicalIntervals) (U : ℝ) (hU : 1 ≤ U)
          (hlowerOne : ∀ sigma, 1 ≤ I.lower sigma)
          (hupperU : ∀ sigma, I.upper sigma ≤ U),
        ∀ (Cprom Cbank : ℕ) (ledger : ∀ n, Ledger n Cprom Cbank),
        ∀ (a : NNReal) (marginFloor : ℝ), 0 < marginFloor →
        ∀ᶠ n : ℕ in atTop,
          ∀ (B : BridgeData Head (Fin (M.cellCount + 1))),
            B.sampleData.n = n → B.sampleData.W = W →
            ∀ (hBWlarge : 1 < B.sampleData.W),
          ∀ (hsep : physicalBound (I.upper .minus) B.sampleData.n <
              physicalBound (I.lower .plus) B.sampleData.n)
            (hremaining : ∀ c : Cell Head,
              (rawCell Phead I B.sampleData.n c \
                (ledger B.sampleData.n).guards).Nonempty),
            (hcanonical : B.sampleData = canonicalSampleData
              (W := B.sampleData.W) Phead I (ledger B.sampleData.n)
                hsep hremaining) →
            (∃ (hWne : B.sampleData.W ≠ 0)
                (S : ScaleSeparation M B.sampleData.n B.sampleData.W),
              B.partition = RegularMeshPrimeCutoffs.Mesh.canonicalPartition
                M hdelta B.n_gt_one hWne S) →
            ∀ (T : BarycentricTarget B.sampleData)
              (_hTmargin : marginFloor ≤ T.cellMassMargin)
              (hbaseline : B.baseline = T.baseline),
              ∃ e : ∀ (z : B.EffectiveParamSpace),
                  z ∈ closedBall (0 : B.EffectiveParamSpace) (a : ℝ) →
                    B.RawBandGauge ≃ₗ[ℝ] B.RawBandGauge,
                (∀ (z : B.EffectiveParamSpace)
                    (hz : z ∈ closedBall
                      (0 : B.EffectiveParamSpace) (a : ℝ)) q,
                  e z hz q =
                    B.actualBandSchurLinearMap (B.effectiveParamEquiv z)
                      (B.canonicalEffectiveNuisanceGamma_pos
                        I U (3 * (a : ℝ)) T)
                      (B.canonicalEffectiveNuisanceGap_on_closedBall I a
                        hU hlowerOne hupperU
                        (by intro sigma; rw [hcanonical]; rfl)
                        (by intro sigma; rw [hcanonical]; rfl)
                        T hbaseline hBWlarge z hz) q) ∧
                ∀ (z : B.EffectiveParamSpace)
                    (hz : z ∈ closedBall
                      (0 : B.EffectiveParamSpace) (a : ℝ)) v,
                  paperSharpNorm B.harmonicMass B.bandCenter
                      (B.partition.center_ne_zero B.n_gt_one)
                      ((e z hz).symm v) ≤
                    Cschur *
                      paperSharpNorm B.harmonicMass B.bandCenter
                        (B.partition.center_ne_zero B.n_gt_one) v := by
  obtain ⟨meshTol, hmeshTol, Cschur, hCschur, W₀, hmain⟩ :=
    @exists_cutoff_before_mesh_eventually_actualBandSchur_primeGraph_inverse
  let fineTol : ℝ := min meshTol (1 / 16)
  have hfineTol : 0 < fineTol := by
    dsimp only [fineTol]
    exact lt_min hmeshTol (by norm_num)
  refine ⟨fineTol, hfineTol, Cschur, hCschur, W₀, ?_⟩
  intro W hW delta eta M hdelta hfine
  have hmesh : delta + M.ratio ≤ meshTol :=
    hfine.trans (min_le_left _ _)
  have hsumSmall : delta + M.ratio ≤ (1 / 16 : ℝ) :=
    hfine.trans (min_le_right _ _)
  have hdeltaSmall : delta < (1 / 16 : ℝ) := by
    linarith [M.ratio_pos]
  have hratioSmall : M.ratio < (1 / 16 : ℝ) := by
    linarith
  have hwidthSmall : ∀ k : Fin M.cellCount,
      M.width k < (1 / 16 : ℝ) := by
    intro k
    exact (M.width_le_ratio hdelta k).trans_lt hratioSmall
  obtain ⟨anchors, anchor, hanchor, hLower, hUpper, hMass⟩ :=
    M.exists_interiorAnchorBlock hdelta hdeltaSmall hwidthSmall
  have hAnchors : anchors.Nonempty := ⟨anchor, hanchor⟩
  exact hmain W hW M hdelta hmesh anchors hAnchors
    hLower hUpper hMass

end BridgeData

end

end Erdos390.Full.PaperBridgeFit

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





/-- Paper-scale wrapper.  The displayed mesh request is `delta + eta`,
while the proof uses only the smaller actual scale `delta + M.ratio`. -/
theorem exists_paperFineMesh_cutoff_eventually_canonical_ordinaryProjectedRaw_inverse :
    ∃ Cref : ℝ, 0 < Cref ∧
      ∃ w₀ : ℝ, 0 < w₀ ∧
      ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W →
      ∀ {delta eta : ℝ} (M : Mesh delta eta) (hdelta : 0 < delta),
      delta + eta ≤ w₀ →
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
  obtain ⟨Cref, hCref, meshTol, hmeshTol, W₀, hmain⟩ :=
    exists_fineMesh_cutoff_eventually_canonical_ordinaryProjectedRaw_inverse
  refine ⟨Cref, hCref, meshTol, hmeshTol, W₀, ?_⟩
  intro W hW delta eta M hdelta hfine
  exact hmain W hW M hdelta (by linarith [M.ratio_le_eta])

end Mesh
end Erdos390.Full.RegularMeshPrimeCutoffs

end

/- Source module: Erdos390.Full.PaperCanonicalActualSchurOrdinaryEndpointEventually -/
section


/-!
# The same actual Schur equivalence in sharp and ordinary norm

This file composes two independent outputs of Lemma 8.4:

* the canonical prime-graph construction of the literal actual Schur
  equivalence, with its paper sharp-norm inverse; and
* the canonical endpoint arithmetic reference inverse in ordinary norm.

The deterministic endpoint connector then transfers the ordinary estimate
to the very same equivalence.  The remaining hypotheses are exactly the
four perturbative estimates displayed by that connector (moment ratio,
squarefree/reference row, full/squarefree row, and nuisance Schur error),
together with their explicit uniform smallness inequalities.  No anchor,
profile, or abstract inverse assumption is exposed.
-/

open scoped BigOperators
open Filter Topology Metric Set

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

open ArithmeticModel ArithmeticBandGeometry
open PaperGuardCensus PaperWeightedInverseExport
open RegularMeshPrimeCutoffs
open SquarefreeReferenceOperatorIdentification

namespace BridgeData

set_option maxHeartbeats 2000000 in
/--
Paper-scale, independent-`eta` endpoint-to-actual-Schur connector.

All structural constants and the cutoff are selected before the mesh and
the effective box.  The final ambient threshold may depend on the already
fixed finite data and box, exactly as in the source theorems.
-/
theorem exists_paperFineMesh_cutoff_eventually_actualBandSchur_sameEquiv_sharp_and_ordinary_of_endpoint_inputs :
    ∃ meshTol : ℝ, 0 < meshTol ∧
      ∃ Csharp : ℝ, 0 < Csharp ∧
      ∃ Cref : ℝ, 0 < Cref ∧
      ∃ W₀ : ℕ,
      ∀ W : ℕ, W₀ ≤ W →
      ∀ {delta eta : ℝ} (M : RegularRelativeMesh.Mesh delta eta)
        (hdelta : 0 < delta),
        delta + eta ≤ meshTol →
        ∀ (Head : Type*) [Fintype Head] [DecidableEq Head] [Nonempty Head],
        ∀ (Phead : Head → HeadPattern.Pattern),
          (∀ h : Head, ∀ p : ℕ,
            p ∈ (Phead h).primes ↔ p.Prime ∧ p ≤ W) →
        ∀ (I : PhysicalIntervals) (U : ℝ) (hU : 1 ≤ U)
          (hlowerOne : ∀ sigma, 1 ≤ I.lower sigma)
          (hupperU : ∀ sigma, I.upper sigma ≤ U),
        ∀ (Cprom Cbank : ℕ) (ledger : ∀ n, Ledger n Cprom Cbank),
        ∀ (a : NNReal) (marginFloor : ℝ), 0 < marginFloor →
        ∀ᶠ n : ℕ in atTop,
          ∀ (B : BridgeData Head (Fin (M.cellCount + 1))),
            B.sampleData.n = n → B.sampleData.W = W →
            ∀ (hBWlarge : 1 < B.sampleData.W),
          ∀ (hsep : physicalBound (I.upper .minus) B.sampleData.n <
              physicalBound (I.lower .plus) B.sampleData.n)
            (hremaining : ∀ c : Cell Head,
              (rawCell Phead I B.sampleData.n c \
                (ledger B.sampleData.n).guards).Nonempty),
            (hcanonical : B.sampleData = canonicalSampleData
              (W := B.sampleData.W) Phead I (ledger B.sampleData.n)
                hsep hremaining) →
            (hpartition : ∃ (hWne : B.sampleData.W ≠ 0)
                (S : ScaleSeparation M B.sampleData.n B.sampleData.W),
              B.partition = RegularMeshPrimeCutoffs.Mesh.canonicalPartition
                M hdelta B.n_gt_one hWne S) →
            ∀ (T : BarycentricTarget B.sampleData)
              (_hTmargin : marginFloor ≤ T.cellMassMargin)
              (hbaseline : B.baseline = T.baseline),
              ∃ e : ∀ (z : B.EffectiveParamSpace),
                  z ∈ closedBall (0 : B.EffectiveParamSpace) (a : ℝ) →
                    B.RawBandGauge ≃ₗ[ℝ] B.RawBandGauge,
                (∀ (z : B.EffectiveParamSpace)
                    (hz : z ∈ closedBall
                      (0 : B.EffectiveParamSpace) (a : ℝ)) q,
                  e z hz q =
                    B.actualBandSchurLinearMap (B.effectiveParamEquiv z)
                      (B.canonicalEffectiveNuisanceGamma_pos
                        I U (3 * (a : ℝ)) T)
                      (B.canonicalEffectiveNuisanceGap_on_closedBall I a
                        hU hlowerOne hupperU
                        (by intro sigma; rw [hcanonical]; rfl)
                        (by intro sigma; rw [hcanonical]; rfl)
                        T hbaseline hBWlarge z hz) q) ∧
                (∀ (z : B.EffectiveParamSpace)
                    (hz : z ∈ closedBall
                      (0 : B.EffectiveParamSpace) (a : ℝ)) v,
                  paperSharpNorm B.harmonicMass B.bandCenter
                      (B.partition.center_ne_zero B.n_gt_one)
                      ((e z hz).symm v) ≤
                    Csharp *
                      paperSharpNorm B.harmonicMass B.bandCenter
                        (B.partition.center_ne_zero B.n_gt_one) v) ∧
                ∀ {Esquare Rpow Rproj deltaSchur : ℝ},
                  0 ≤ Esquare → 0 ≤ Rpow → 0 ≤ Rproj →
                  (∑ j : Fin (M.cellCount + 1),
                      B.harmonicMass j * B.bandCenter j) ≤
                    Rproj * MovingLowGaugeTransfer.sharpWeightTotal
                      B.harmonicMass B.bandCenter →
                  (∀ (z : B.EffectiveParamSpace)
                      (_hz : z ∈ closedBall
                        (0 : B.EffectiveParamSpace) (a : ℝ))
                      (q : B.RawBandGauge) (i : Fin (M.cellCount + 1)),
                    |SquarefreeSharpBandTransfer.squarefreeBandRow
                        (B.actualValuationLaw (B.effectiveParamEquiv z))
                          B.partition q.1 i -
                      SquarefreeSharpBandTransfer.referenceBandRow
                        B.partition q.1 i| ≤ ‖q‖ * Esquare) →
                  (∀ (z : B.EffectiveParamSpace)
                      (_hz : z ∈ closedBall
                        (0 : B.EffectiveParamSpace) (a : ℝ))
                      (q : B.RawBandGauge) (i : Fin (M.cellCount + 1)),
                    |PrimePowerSharpBandTransfer.fullBandRow
                        (B.actualValuationLaw (B.effectiveParamEquiv z))
                          B.partition q.1 i -
                      SquarefreeSharpBandTransfer.squarefreeBandRow
                        (B.actualValuationLaw (B.effectiveParamEquiv z))
                          B.partition q.1 i| ≤ ‖q‖ * Rpow) →
                  Cref * ((1 + Rproj) * (Rpow + Esquare)) ≤ 1 / 2 →
                  (∀ (z : B.EffectiveParamSpace)
                      (hz : z ∈ closedBall
                        (0 : B.EffectiveParamSpace) (a : ℝ))
                      (q : B.RawBandGauge),
                    ‖B.actualBandSchurLinearMap (B.effectiveParamEquiv z)
                          (B.canonicalEffectiveNuisanceGamma_pos
                            I U (3 * (a : ℝ)) T)
                          (B.canonicalEffectiveNuisanceGap_on_closedBall I a
                            hU hlowerOne hupperU
                            (by intro sigma; rw [hcanonical]; rfl)
                            (by intro sigma; rw [hcanonical]; rfl)
                            T hbaseline hBWlarge z hz) q -
                        B.actualBandFullLinearMap
                          (B.effectiveParamEquiv z) q‖ ≤
                      deltaSchur * ‖q‖) →
                  (2 * Cref) * deltaSchur ≤ 1 / 2 →
                  ∀ (z : B.EffectiveParamSpace)
                    (hz : z ∈ closedBall
                      (0 : B.EffectiveParamSpace) (a : ℝ)) v,
                    ‖(e z hz).symm v‖ ≤ (4 * Cref) * ‖v‖ := by
  obtain ⟨sharpTol, hsharpTol, Csharp, hCsharp, Wsharp, hSharp⟩ :=
    @exists_fineMesh_cutoff_eventually_actualBandSchur_primeGraph_inverse
  obtain ⟨Cref, hCref, refTol, hrefTol, Wref, hReference⟩ :=
    RegularMeshPrimeCutoffs.Mesh.exists_paperFineMesh_cutoff_eventually_canonical_ordinaryProjectedRaw_inverse
  let meshTol : ℝ := min sharpTol refTol
  let W₀ : ℕ := max Wsharp Wref
  have hmeshTol : 0 < meshTol := by
    dsimp only [meshTol]
    exact lt_min hsharpTol hrefTol
  refine ⟨meshTol, hmeshTol, Csharp, hCsharp,
    Cref, hCref, W₀, ?_⟩
  intro W hW delta eta M hdelta hfine
    Head _instHead _instHeadDec _instHeadNonempty Phead hPhead
    I U hU hlowerOne hupperU Cprom Cbank ledger a marginFloor hmargin
  have hWsharp : Wsharp ≤ W :=
    (le_max_left Wsharp Wref).trans hW
  have hWref : Wref ≤ W :=
    (le_max_right Wsharp Wref).trans hW
  have hSharpFine : delta + M.ratio ≤ sharpTol := by
    have hpaper : delta + eta ≤ sharpTol :=
      hfine.trans (min_le_left sharpTol refTol)
    linarith [M.ratio_le_eta]
  have hRefFine : delta + eta ≤ refTol :=
    hfine.trans (min_le_right sharpTol refTol)
  have hSharpN := hSharp W hWsharp M hdelta hSharpFine
    Head Phead hPhead I U hU hlowerOne hupperU
      Cprom Cbank ledger a marginFloor hmargin
  have hReferenceN := hReference W hWref M hdelta hRefFine
  filter_upwards [hSharpN, hReferenceN] with n hSharpAt hReferenceAt
  intro B hBn hBW hBWlarge hsep hremaining hcanonical hpartition
    T hTmargin hbaseline
  subst n
  subst W
  have hSharpB := hSharpAt B rfl rfl hBWlarge hsep hremaining
    hcanonical hpartition T hTmargin hbaseline
  obtain ⟨e, he, hsharp⟩ := hSharpB
  obtain ⟨hWrefNe, hnRef, Sref, hReferenceRaw⟩ := hReferenceAt
  let Pref := RegularMeshPrimeCutoffs.Mesh.canonicalPartition M hdelta
    hnRef hWrefNe Sref
  let Eref := RegularMeshPrimeCutoffs.Mesh.canonicalCertificate M hdelta
    hnRef hWrefNe Sref
  have hReferenceRef :
      ∀ q : RawGaugeSpace Pref.mass Pref.center,
        ‖q‖ ≤ Cref *
          ‖projectedRawLinearMap
            (CompressedArithmeticOperator.arithmeticDiagonal
              (ArithmeticModel.y B.sampleData.n) Eref.lower Eref.upper)
            (CompressedArithmeticOperator.arithmeticKernel
              (ArithmeticModel.y B.sampleData.n) Eref.lower Eref.upper)
            Pref.mass Pref.center
            (by
              unfold MovingLowGaugeTransfer.sharpWeightTotal
                MovingLowGaugeTransfer.sharpWeight
              simpa only [Erdos390.Lemma84.WeightedBandData.centerEnergy,
                Erdos390.Lemma84.WeightedBandData.bandNormSq,
                Erdos390.Lemma84.WeightedBandData.bandInner, pow_two,
                mul_assoc] using
                  (Pref.centerEnergy_pos hnRef).ne') q‖ := by
    simpa only [Pref, Eref] using hReferenceRaw
  obtain ⟨hWuser, Suser, hpartitionUser⟩ := hpartition
  have hpartitionRef : B.partition = Pref := by
    exact hpartitionUser.trans (by dsimp only [Pref])
  refine ⟨e, he, hsharp, ?_⟩
  intro Esquare Rpow Rproj deltaSchur hEsquare hRpow hRproj hRatio
    hsquare hfull hSmallFull hSchurError hSmallSchur z hz v
  have hOrdinary :=
    B.actualBandSchur_sameEquiv_ordinary_inverse_of_partition_eq_endpoint_reference
      (B.effectiveParamEquiv z)
      (B.canonicalEffectiveNuisanceGamma_pos I U (3 * (a : ℝ)) T)
      (B.canonicalEffectiveNuisanceGap_on_closedBall I a
        hU hlowerOne hupperU
        (by intro sigma; rw [hcanonical]; rfl)
        (by intro sigma; rw [hcanonical]; rfl)
        T hbaseline hBWlarge z hz)
      (e z hz) (he z hz) Pref hpartitionRef Eref hCref.le
      hEsquare hRpow hRproj hRatio hReferenceRef
      (hsquare z hz) (hfull z hz) hSmallFull
      (hSchurError z hz) hSmallSchur
  exact hOrdinary.2 v

end BridgeData

end

end Erdos390.Full.PaperBridgeFit

end

/- Source module: Erdos390.Full.PaperCanonicalActualSchurOrdinaryRowsEventually -/
section


/-!
# Fully discharged ordinary perturbation rows for Lemma 8.4

This file packages the three analytic perturbations used by the endpoint
ordinary inverse: squarefree-to-reference, full-to-squarefree, and the
nuisance Schur correction.  The fixed `1/W` tails are made small before the
head data and the effective tilt ball are selected.  Every dependence on the
later ball is confined to an eventual error in the ambient parameter `n`.

The only local premise retained by the last row is the exact first-moment to
centre-energy ratio.  That geometric premise is supplied, without analytic
assumptions, by the separate canonical moment-ratio terminal when the final
Lemma 8.4 wrapper is assembled.
-/

open scoped BigOperators
open Filter Topology Metric Set

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

open ArithmeticModel ArithmeticBandGeometry FiniteProbability
open PaperGuardCensus PrimeSums PaperWeightedInverseExport
open RegularMeshPrimeCutoffs
open SquarefreeCovarianceReference
open PaperPrimePowerChamberError
open PrimeSquarefreeDirichletGeometry

namespace BridgeData





theorem canonicalOrdinaryRowTolerance_pos
    {Cref Rproj : ℝ} (hCref : 0 < Cref) (hRproj : 0 ≤ Rproj) :
    0 < canonicalOrdinaryRowTolerance Cref Rproj := by
  unfold canonicalOrdinaryRowTolerance
  positivity



theorem canonicalOrdinaryRows_small
    {Cref Rproj : ℝ} (hCref : 0 < Cref) (hRproj : 0 ≤ Rproj) :
    Cref * ((1 + Rproj) *
      (canonicalOrdinaryRowTolerance Cref Rproj +
        canonicalOrdinaryRowTolerance Cref Rproj)) ≤ 1 / 2 := by
  have hden : 0 < 8 * Cref * (1 + Rproj) := by positivity
  unfold canonicalOrdinaryRowTolerance
  field_simp [hCref.ne', (by linarith : (1 + Rproj) ≠ 0)]
  linarith

theorem canonicalOrdinarySchur_small
    {Cref : ℝ} (hCref : 0 < Cref) :
    (2 * Cref) * canonicalOrdinarySchurTolerance Cref ≤ 1 / 2 := by
  unfold canonicalOrdinarySchurTolerance
  field_simp [hCref.ne']
  linarith







end BridgeData

end

end Erdos390.Full.PaperBridgeFit

end

/- Source module: Erdos390.Full.PaperCanonicalPositiveCellVarianceEventually -/
section


/-!
# Positive-cell variance on an arbitrary regular relative mesh

The moving low cell alone controls the paper scale only when the positive
relative width is no larger than the low endpoint.  This file supplies the
missing complementary estimate: the sum of the literal within-cell prime
variances in the positive cells is bounded below by a fixed multiple of the
square of the actual common mesh ratio.  The proof first identifies the
finite prime moments with three unconditional PNT quadratures and then
passes to the exact continuum cell variance.
-/

open scoped BigOperators
open Filter Topology

noncomputable section

namespace Erdos390.Full.RegularMeshPrimeCutoffs

open ArithmeticModel ArithmeticBandGeometry RegularRelativeMesh
open PositiveCellTransfer KernelPrimeQuadrature PrimeBandQuadrature
open PrimeCoordinateSecondMoment MovingLowMomentQuadrature

namespace Mesh

variable {delta eta : ℝ} (M : Mesh delta eta)











































/-- The fixed interior prime mass gives a mesh-independent lower floor for
the literal arithmetic centre energy. -/
theorem one_div_64_le_centerEnergy_of_canonical_anchor
    {n W : ℕ} (hdelta : 0 < delta)
    (hn : 1 < n) (hWne : W ≠ 0) (S : ScaleSeparation M n W)
    (anchors : Finset (Fin M.cellCount))
    (hinterior : ∀ p ∈ canonicalPrimeAnchorSet M
        (canonicalPartition M hdelta hn hWne S) anchors,
      tPrime n p.1 ∈ Set.Icc ((1 : ℝ) / 8) (1 - (1 : ℝ) / 8))
    (hAnchorMass : (1 : ℝ) / 8 ≤
      FiniteAnchoredDirichletQuadratic.anchorMass
        (PrimeSquarefreeDirichletGeometry.primeWeight n)
        (canonicalPrimeAnchorSet M
          (canonicalPartition M hdelta hn hWne S) anchors)) :
    (1 : ℝ) / 64 ≤
      (canonicalPartition M hdelta hn hWne S).centerEnergy := by
  let P := canonicalPartition M hdelta hn hWne S
  have hEnergy := epsilon_mul_anchorMass_le_centerEnergy M P hn
    (by norm_num : (0 : ℝ) ≤ 1 / 8) anchors hinterior
  calc
    (1 : ℝ) / 64 = (1 / 8 : ℝ) * (1 / 8 : ℝ) := by norm_num
    _ ≤ (1 / 8 : ℝ) *
        FiniteAnchoredDirichletQuadratic.anchorMass
          (PrimeSquarefreeDirichletGeometry.primeWeight n)
          (canonicalPrimeAnchorSet M P anchors) := by
      exact mul_le_mul_of_nonneg_left hAnchorMass (by norm_num)
    _ ≤ P.centerEnergy := hEnergy



end Mesh

end Erdos390.Full.RegularMeshPrimeCutoffs

end

/- Source module: Erdos390.Full.PaperCanonicalGeometricMomentFineMeshEventually -/
section


/-!
# Paper-scale geometric moment inputs on every permitted fine mesh

This file assembles the arithmetic estimates used after the continuum-to-band
transfer.  The structural prime cutoff and the numerical mesh tolerance are
chosen before the mesh.  The two mesh parameters remain independent: the
only comparison used is the two-sided regularity condition from the paper,
namely

`cMesh * eta ≤ M.ratio ≤ eta`.

The lower variance estimate deliberately combines two different arithmetic
sources.  The moving low cell controls `delta^2`, while the positive cells
control the square of the actual relative width `M.ratio`.  Thus no hidden
hypothesis such as `M.ratio ≤ delta` or `eta ≤ delta` is present.
-/

open scoped BigOperators
open Filter

noncomputable section

namespace Erdos390.Full.RegularMeshPrimeCutoffs

open ArithmeticModel ArithmeticBandGeometry RegularRelativeMesh
open PaperPermittedRegularMesh

namespace Mesh







/--
The canonical centre energy has an absolute lower floor on every sufficiently
fine paper mesh.  The cutoff is chosen before `delta`, `eta`, and the mesh;
no comparison between the two mesh parameters is required.

This is the denominator estimate used when an ordinary row bound is converted
to the paper's quotient moment ratio.  Stating it separately prevents that
conversion from silently importing the regularity hypothesis needed only for
the variance lower bound.
-/
theorem canonicalPaperCenterEnergyFloorCutoff_eventually :
    ∀ W : ℕ, canonicalPrimeAnchorCutoff ≤ W →
      ∀ {delta eta : ℝ} (M : Mesh delta eta)
        (hdelta : 0 < delta),
        delta + eta ≤ canonicalPaperGeometricMeshTolerance →
        ∀ᶠ n : ℕ in atTop,
          ∃ hWne : W ≠ 0, ∃ hn : 1 < n,
            ∀ S : ScaleSeparation M n W,
              (1 : ℝ) / 64 ≤
                (canonicalPartition M hdelta hn hWne S).centerEnergy := by
  intro W hW delta eta M hdelta hfine
  have heta : 0 < eta := M.ratio_pos.trans_le M.ratio_le_eta
  have hdeltaSmall : delta < (1 : ℝ) / 16 := by
    dsimp only [canonicalPaperGeometricMeshTolerance] at hfine
    linarith
  have hratioSmall : M.ratio < (1 : ℝ) / 16 := by
    dsimp only [canonicalPaperGeometricMeshTolerance] at hfine
    linarith [M.ratio_le_eta]
  have hwidthSmall : ∀ k : Fin M.cellCount,
      M.width k < (1 : ℝ) / 16 := by
    intro k
    exact (M.width_le_ratio hdelta k).trans_lt hratioSmall
  obtain ⟨anchors, anchor, hanchor, hIdealLower, hIdealUpper, hIdealMass⟩ :=
    M.exists_interiorAnchorBlock hdelta hdeltaSmall hwidthSmall
  have hAnchors : anchors.Nonempty := ⟨anchor, hanchor⟩
  have hPrimeAnchor := canonicalPrimeAnchorCutoff_eventually M hdelta
    W hW (epsilon := (1 / 8 : ℝ)) anchors hAnchors
      hIdealLower hIdealUpper hIdealMass
  filter_upwards [hPrimeAnchor] with n hAnchorAt
  obtain ⟨hWne, hn, hAnchorAll⟩ := hAnchorAt
  refine ⟨hWne, hn, ?_⟩
  intro S
  obtain ⟨hInterior, hAnchorMass⟩ := hAnchorAll S
  exact one_div_64_le_centerEnergy_of_canonical_anchor M hdelta
    hn hWne S anchors hInterior hAnchorMass



end Mesh

end Erdos390.Full.RegularMeshPrimeCutoffs

end

/- Source module: Erdos390.Full.PaperCanonicalMomentRatioEventually -/
section


/-!
# Canonical paper-scale moment-ratio bound

This file discharges the quotient first-moment ratio used by the ordinary
Schur transfer.  The numerator is the literal arithmetic first moment
`sum_j H_j * alpha_j`; the denominator is the literal sharp projection
weight `sum_j H_j * alpha_j^2`.  A canonical interior prime anchor gives a
uniform positive denominator, while the elementary prime-band estimate
bounds the numerator.

All constants are selected before `W`, the two independent mesh parameters,
and the mesh.  The public statement exposes no anchor or analytic estimate.
-/

open scoped BigOperators
open Filter

noncomputable section

namespace Erdos390.Full.PaperBridgeFit

open ArithmeticModel ArithmeticBandGeometry PrimeSums
open PaperWeightedInverseExport MovingLowGaugeTransfer
open RegularMeshPrimeCutoffs RegularRelativeMesh

namespace BridgeData

/--
Uniform first-moment/centre-energy ratio for the literal canonical
partition.  The displayed fineness condition is the paper scale
`delta + eta`; no comparison between `delta` and `eta` is assumed.
-/
theorem exists_paperFineMesh_cutoff_eventually_canonical_momentRatio :
    ∃ Rproj : ℝ, 0 < Rproj ∧
      ∃ meshTol : ℝ, 0 < meshTol ∧
      ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W →
      ∀ {delta eta : ℝ} (M : Mesh delta eta) (hdelta : 0 < delta),
      delta + eta ≤ meshTol →
      ∀ {Head : Type*} [Fintype Head] [DecidableEq Head] [Nonempty Head],
      ∀ᶠ n : ℕ in atTop,
        ∀ (B : BridgeData Head (Fin (M.cellCount + 1))),
          B.sampleData.n = n → B.sampleData.W = W →
          (∃ hWne : B.sampleData.W ≠ 0,
            ∃ S : ScaleSeparation M B.sampleData.n B.sampleData.W,
              B.partition = RegularMeshPrimeCutoffs.Mesh.canonicalPartition
                M hdelta B.n_gt_one hWne S) →
          (∑ j : Fin (M.cellCount + 1),
              B.harmonicMass j * B.bandCenter j) ≤
            Rproj * sharpWeightTotal B.harmonicMass B.bandCenter := by
  let Rproj : ℝ := 128 * Real.log 4
  have hRproj : 0 < Rproj := by
    dsimp only [Rproj]
    positivity
  refine ⟨Rproj, hRproj,
    RegularMeshPrimeCutoffs.Mesh.canonicalPaperGeometricMeshTolerance,
    by norm_num [RegularMeshPrimeCutoffs.Mesh.canonicalPaperGeometricMeshTolerance],
    RegularMeshPrimeCutoffs.Mesh.canonicalPrimeAnchorCutoff, ?_⟩
  intro W hW delta eta M hdelta hfine Head _instFintype
    _instDecidable _instNonempty
  have hEnergyN :=
    RegularMeshPrimeCutoffs.Mesh.canonicalPaperCenterEnergyFloorCutoff_eventually
      W hW M hdelta hfine
  have hBandTN := eventually_bandTReciprocalSum_le W
  filter_upwards [hEnergyN, hBandTN] with n hEnergyAt hBandTAt
  intro B hBn hBW hpartition
  subst n
  subst W
  obtain ⟨hWne, hn, hEnergyAll⟩ := hEnergyAt
  obtain ⟨hWuser, S, hpartitionUser⟩ := hpartition
  let P := RegularMeshPrimeCutoffs.Mesh.canonicalPartition M hdelta
    hn hWne S
  have hpartitionCanonical : B.partition = P := by
    exact hpartitionUser.trans (by dsimp only [P])
  have hEnergy : (1 : ℝ) / 64 ≤ B.partition.centerEnergy := by
    rw [hpartitionCanonical]
    exact hEnergyAll S
  have hFirstMoment :
      (∑ j : Fin (M.cellCount + 1),
          B.harmonicMass j * B.bandCenter j) =
        bandTReciprocalSum B.sampleData.n B.sampleData.W := by
    simpa only [harmonicMass, bandCenter] using
      B.partition.sum_mass_mul_center_eq_bandTReciprocalSum
  have hSharpWeight :
      sharpWeightTotal B.harmonicMass B.bandCenter =
        B.partition.centerEnergy := by
    unfold sharpWeightTotal sharpWeight harmonicMass bandCenter
    unfold ArithmeticBandGeometry.Partition.centerEnergy
      Erdos390.Lemma84.WeightedBandData.centerEnergy
      Erdos390.Lemma84.WeightedBandData.bandNormSq
      Erdos390.Lemma84.WeightedBandData.bandInner
    simp only [pow_two, mul_assoc]
  calc
    (∑ j : Fin (M.cellCount + 1),
        B.harmonicMass j * B.bandCenter j) =
        bandTReciprocalSum B.sampleData.n B.sampleData.W := hFirstMoment
    _ ≤ 2 * Real.log 4 := hBandTAt
    _ = Rproj * ((1 : ℝ) / 64) := by
      dsimp only [Rproj]
      ring
    _ ≤ Rproj * B.partition.centerEnergy :=
      mul_le_mul_of_nonneg_left hEnergy hRproj.le
    _ = Rproj * sharpWeightTotal B.harmonicMass B.bandCenter := by
      rw [hSharpWeight]

end BridgeData

end PaperBridgeFit

end Full

end Erdos390

end

end

/- Source module: Erdos390.Full.PaperCanonicalActualSchurSharpOrdinaryEventually -/
section


/-!
# Final sharp-and-ordinary same-map form of Lemma 8.4

The endpoint arithmetic inverse, the literal actual Schur equivalence, the
canonical moment ratio, and all three ordinary perturbation rows are joined
here.  The public theorem has no anchor, profile, convergence, row-error,
smallness, or abstract inverse premise.  The equivalence in the two norm
bounds is definitionally the same object and is exactly the finite-`n`
actual Schur map throughout the selected effective ball.
-/

open scoped BigOperators
open Filter Topology Metric Set

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

open ArithmeticModel ArithmeticBandGeometry
open PaperGuardCensus PaperWeightedInverseExport
open RegularMeshPrimeCutoffs

namespace BridgeData

set_option maxHeartbeats 3000000 in
/--
Assumption-free canonical Lemma 8.4 terminal in both paper norms.

All numerical constants and the structural cutoff are chosen before the two
independent mesh parameters, the mesh itself, the finite head data, and the
effective tilt ball.  Only the final ambient threshold may depend on those
already fixed objects.
-/
theorem exists_paperFineMesh_cutoff_eventually_actualBandSchur_sameEquiv_sharp_and_ordinary :
    ∃ meshTol : ℝ, 0 < meshTol ∧
      ∃ Csharp : ℝ, 0 < Csharp ∧
      ∃ Cordinary : ℝ, 0 < Cordinary ∧
      ∃ W₀ : ℕ,
      ∀ W : ℕ, W₀ ≤ W →
      ∀ {delta eta : ℝ} (M : RegularRelativeMesh.Mesh delta eta)
        (hdelta : 0 < delta),
        delta + eta ≤ meshTol →
        ∀ (Head : Type*) [Fintype Head] [DecidableEq Head] [Nonempty Head],
        ∀ (Phead : Head → HeadPattern.Pattern),
          (∀ h : Head, ∀ p : ℕ,
            p ∈ (Phead h).primes ↔ p.Prime ∧ p ≤ W) →
        ∀ (I : PhysicalIntervals) (U : ℝ) (hU : 1 ≤ U)
          (hlowerOne : ∀ sigma, 1 ≤ I.lower sigma)
          (hupperU : ∀ sigma, I.upper sigma ≤ U),
        ∀ (Cprom Cbank : ℕ) (ledger : ∀ n, Ledger n Cprom Cbank),
        ∀ (a : NNReal) (marginFloor : ℝ), 0 < marginFloor →
        ∀ᶠ n : ℕ in atTop,
          ∀ (B : BridgeData Head (Fin (M.cellCount + 1))),
            B.sampleData.n = n → B.sampleData.W = W →
            ∀ (hBWlarge : 1 < B.sampleData.W),
            ∀ (hsep : physicalBound (I.upper .minus) B.sampleData.n <
                physicalBound (I.lower .plus) B.sampleData.n)
              (hremaining : ∀ c : Cell Head,
                (rawCell Phead I B.sampleData.n c \
                  (ledger B.sampleData.n).guards).Nonempty),
              (hcanonical : B.sampleData = canonicalSampleData
                (W := B.sampleData.W) Phead I (ledger B.sampleData.n)
                  hsep hremaining) →
              (hpartition : ∃ (hWne : B.sampleData.W ≠ 0)
                  (S : ScaleSeparation M B.sampleData.n B.sampleData.W),
                B.partition = RegularMeshPrimeCutoffs.Mesh.canonicalPartition
                  M hdelta B.n_gt_one hWne S) →
              ∀ (T : BarycentricTarget B.sampleData)
                (_hTmargin : marginFloor ≤ T.cellMassMargin)
                (hbaseline : B.baseline = T.baseline),
                ∃ e : ∀ (z : B.EffectiveParamSpace),
                    z ∈ closedBall (0 : B.EffectiveParamSpace) (a : ℝ) →
                      B.RawBandGauge ≃ₗ[ℝ] B.RawBandGauge,
                  (∀ (z : B.EffectiveParamSpace)
                      (hz : z ∈ closedBall
                        (0 : B.EffectiveParamSpace) (a : ℝ)) q,
                    e z hz q =
                      B.actualBandSchurLinearMap (B.effectiveParamEquiv z)
                        (B.canonicalEffectiveNuisanceGamma_pos
                          I U (3 * (a : ℝ)) T)
                        (B.canonicalEffectiveNuisanceGap_on_closedBall I a
                          hU hlowerOne hupperU
                          (by intro sigma; rw [hcanonical]; rfl)
                          (by intro sigma; rw [hcanonical]; rfl)
                          T hbaseline hBWlarge z hz) q) ∧
                  (∀ (z : B.EffectiveParamSpace)
                      (hz : z ∈ closedBall
                        (0 : B.EffectiveParamSpace) (a : ℝ)) v,
                    paperSharpNorm B.harmonicMass B.bandCenter
                        (B.partition.center_ne_zero B.n_gt_one)
                        ((e z hz).symm v) ≤
                      Csharp *
                        paperSharpNorm B.harmonicMass B.bandCenter
                          (B.partition.center_ne_zero B.n_gt_one) v) ∧
                  ∀ (z : B.EffectiveParamSpace)
                      (hz : z ∈ closedBall
                        (0 : B.EffectiveParamSpace) (a : ℝ)) v,
                    ‖(e z hz).symm v‖ ≤ Cordinary * ‖v‖ := by
  obtain ⟨Rproj, hRproj, ratioTol, hratioTol, Wratio, hRatio⟩ :=
    exists_paperFineMesh_cutoff_eventually_canonical_momentRatio
  obtain ⟨connectorTol, hconnectorTol, Csharp, hCsharp,
      Cref, hCref, Wconnector, hConnector⟩ :=
    exists_paperFineMesh_cutoff_eventually_actualBandSchur_sameEquiv_sharp_and_ordinary_of_endpoint_inputs
  obtain ⟨Wrows, hRows⟩ :=
    exists_cutoff_eventually_canonical_ordinary_perturbation_rows
      Cref Rproj hCref hRproj.le
  let meshTol : ℝ := min ratioTol connectorTol
  let Cordinary : ℝ := 4 * Cref
  let W₀ : ℕ := max Wratio (max Wconnector Wrows)
  have hmeshTol : 0 < meshTol := by
    dsimp only [meshTol]
    exact lt_min hratioTol hconnectorTol
  have hCordinary : 0 < Cordinary := by
    dsimp only [Cordinary]
    positivity
  refine ⟨meshTol, hmeshTol, Csharp, hCsharp,
    Cordinary, hCordinary, W₀, ?_⟩
  intro W hW delta eta M hdelta hfine
    Head _instHead _instHeadDec _instHeadNonempty Phead hPhead
    I U hU hlowerOne hupperU Cprom Cbank ledger a marginFloor hmargin
  have hWratio : Wratio ≤ W :=
    (le_max_left Wratio _).trans hW
  have hWconnector : Wconnector ≤ W :=
    (le_max_left Wconnector Wrows).trans
      ((le_max_right Wratio _).trans hW)
  have hWrows : Wrows ≤ W :=
    (le_max_right Wconnector Wrows).trans
      ((le_max_right Wratio _).trans hW)
  have hRatioFine : delta + eta ≤ ratioTol :=
    hfine.trans (min_le_left ratioTol connectorTol)
  have hConnectorFine : delta + eta ≤ connectorTol :=
    hfine.trans (min_le_right ratioTol connectorTol)
  have hHeadLe : ∀ h : Head, ∀ p ∈ (Phead h).primes, p ≤ W := by
    intro h p hp
    exact (hPhead h p).mp hp |>.2
  have hRatioN := hRatio W hWratio M hdelta hRatioFine
    (Head := Head)
  have hConnectorN := hConnector W hWconnector M hdelta hConnectorFine
    Head Phead hPhead I U hU hlowerOne hupperU
      Cprom Cbank ledger a marginFloor hmargin
  have hRowsN := hRows W hWrows Phead hHeadLe I U hU
    hlowerOne hupperU Cprom Cbank ledger a marginFloor hmargin
      (Band := Fin (M.cellCount + 1))
  filter_upwards [hRatioN, hConnectorN, hRowsN] with
      n hRatioAt hConnectorAt hRowsAt
  intro B hBn hBW hBWlarge hsep hremaining hcanonical hpartition
    T hTmargin hbaseline
  have hRatioB := hRatioAt B hBn hBW hpartition
  obtain ⟨e, he, hsharp, hconditional⟩ :=
    hConnectorAt B hBn hBW hBWlarge hsep hremaining hcanonical
      hpartition T hTmargin hbaseline
  obtain ⟨hsquare, hfull, hschur⟩ :=
    hRowsAt B hBn hBW hBWlarge hsep hremaining hcanonical
      T hTmargin hbaseline hRatioB
  have hordinary := hconditional
    (Esquare := canonicalOrdinaryRowTolerance Cref Rproj)
    (Rpow := canonicalOrdinaryRowTolerance Cref Rproj)
    (Rproj := Rproj)
    (deltaSchur := canonicalOrdinarySchurTolerance Cref)
    (canonicalOrdinaryRowTolerance_pos hCref hRproj.le).le
    (canonicalOrdinaryRowTolerance_pos hCref hRproj.le).le
    hRproj.le hRatioB hsquare hfull
    (canonicalOrdinaryRows_small hCref hRproj.le)
    hschur (canonicalOrdinarySchur_small hCref)
  refine ⟨e, he, hsharp, ?_⟩
  intro z hz v
  simpa only [Cordinary] using hordinary z hz v

end BridgeData

end

end Erdos390.Full.PaperBridgeFit

end

/- Source module: Erdos390.Full.PaperCanonicalLemma84Eventually -/
section


/-!
# Closed canonical form of paper Lemma 8.4

This is the umbrella statement matching the three conclusions of the paper's
moving-low-cell arithmetic quotient lemma.  It combines the literal
`q_n`-scaled quotient gap and finite nuisance coercivity with an equivalence
which is exactly the actual finite nuisance-Schur band map.  The sharp and
ordinary inverse estimates apply to that same equivalence.

No anchor, convergence rate, row estimate, perturbation smallness condition,
or abstract inverse is exposed at the call site.  Both mesh parameters remain
independent and the displayed fineness condition is `delta + eta`.
-/

open scoped BigOperators
open Filter Topology Metric Set

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

open ArithmeticModel ArithmeticBandGeometry FiniteProbability
open PaperGuardCensus PaperWeightedInverseExport
open RegularMeshPrimeCutoffs

namespace BridgeData

set_option maxHeartbeats 1000000 in
/-- Assumption-free, paper-order, literal finite-`n` Lemma 8.4 terminal. -/
theorem exists_paperFineMesh_cutoff_eventually_canonical_lemma84 :
    ∃ kappa : ℝ, 0 < kappa ∧
      ∃ meshTol : ℝ, 0 < meshTol ∧
      ∃ Csharp : ℝ, 0 < Csharp ∧
      ∃ Cordinary : ℝ, 0 < Cordinary ∧
      ∃ W₀ : ℕ,
      ∀ W : ℕ, W₀ ≤ W →
      ∀ {delta eta : ℝ} (M : RegularRelativeMesh.Mesh delta eta)
        (hdelta : 0 < delta),
        delta + eta ≤ meshTol →
        ∀ (Head : Type*) [Fintype Head] [DecidableEq Head] [Nonempty Head],
        ∀ (Phead : Head → HeadPattern.Pattern),
          (∀ h : Head, ∀ p : ℕ,
            p ∈ (Phead h).primes ↔ p.Prime ∧ p ≤ W) →
        ∀ (I : PhysicalIntervals) (U : ℝ) (hU : 1 ≤ U)
          (hlowerOne : ∀ sigma, 1 ≤ I.lower sigma)
          (hupperU : ∀ sigma, I.upper sigma ≤ U),
        ∀ (Cprom Cbank : ℕ) (ledger : ∀ n, Ledger n Cprom Cbank),
        ∀ (a : NNReal) (marginFloor : ℝ), 0 < marginFloor →
        ∀ᶠ n : ℕ in atTop,
          ∀ (B : BridgeData Head (Fin (M.cellCount + 1))),
            B.sampleData.n = n → B.sampleData.W = W →
            ∀ (hBWlarge : 1 < B.sampleData.W),
            ∀ (hsep : physicalBound (I.upper .minus) B.sampleData.n <
                physicalBound (I.lower .plus) B.sampleData.n)
              (hremaining : ∀ c : Cell Head,
                (rawCell Phead I B.sampleData.n c \
                  (ledger B.sampleData.n).guards).Nonempty),
              (hcanonical : B.sampleData = canonicalSampleData
                (W := B.sampleData.W) Phead I (ledger B.sampleData.n)
                  hsep hremaining) →
              (hpartition : ∃ (hWne : B.sampleData.W ≠ 0)
                  (S : ScaleSeparation M B.sampleData.n B.sampleData.W),
                B.partition = RegularMeshPrimeCutoffs.Mesh.canonicalPartition
                  M hdelta B.n_gt_one hWne S) →
              ∀ (T : BarycentricTarget B.sampleData)
                (hTmargin : marginFloor ≤ T.cellMassMargin)
                (hbaseline : B.baseline = T.baseline),
                ∃ e : ∀ (z : B.EffectiveParamSpace),
                    z ∈ closedBall (0 : B.EffectiveParamSpace) (a : ℝ) →
                      B.RawBandGauge ≃ₗ[ℝ] B.RawBandGauge,
                  (∀ (z : B.EffectiveParamSpace)
                    (hz : z ∈ closedBall
                      (0 : B.EffectiveParamSpace) (a : ℝ)),
                    let xi : B.ParamSpace := B.effectiveParamEquiv z
                    let gamma : ℝ :=
                      B.canonicalEffectiveNuisanceGamma
                        I U (3 * (a : ℝ)) T
                    let hgamma : 0 < gamma :=
                      B.canonicalEffectiveNuisanceGamma_pos
                        I U (3 * (a : ℝ)) T
                    let hgap : ∀ v, gamma * ‖v‖ ^ 2 ≤
                        inner ℝ v
                          (B.nuisanceCovarianceOperator xi v) := by
                      intro v
                      simpa only [gamma, xi] using
                        B.canonicalEffectiveNuisanceGap_on_closedBall I a hU
                          hlowerOne hupperU
                          (by intro sigma; rw [hcanonical]; rfl)
                          (by intro sigma; rw [hcanonical]; rfl)
                          T hbaseline hBWlarge z hz v
                    (0 < gamma) ∧
                    (∀ v, gamma * ‖v‖ ^ 2 ≤
                      inner ℝ v (B.nuisanceCovarianceOperator xi v)) ∧
                    ∀ (b : Fin (M.cellCount + 1) → ℝ) (mu : ℝ),
                      kappa * B.q *
                          (⨅ lambda : ℝ,
                            ∑ j : Fin (M.cellCount + 1),
                              B.harmonicMass j *
                                |b j - lambda * B.bandCenter j| ^ 2) ≤
                        B.q * (B.tiltedLaw xi).covariance
                          (B.nuisanceResidualScore xi hgamma hgap
                            (B.primeValuationScore
                              (B.partition.data.residual b mu)))
                          (B.nuisanceResidualScore xi hgamma hgap
                            (B.primeValuationScore
                              (B.partition.data.residual b mu)))) ∧
                  (∀ (z : B.EffectiveParamSpace)
                      (hz : z ∈ closedBall
                        (0 : B.EffectiveParamSpace) (a : ℝ)) q,
                    e z hz q =
                      B.actualBandSchurLinearMap (B.effectiveParamEquiv z)
                        (B.canonicalEffectiveNuisanceGamma_pos
                          I U (3 * (a : ℝ)) T)
                        (B.canonicalEffectiveNuisanceGap_on_closedBall I a
                          hU hlowerOne hupperU
                          (by intro sigma; rw [hcanonical]; rfl)
                          (by intro sigma; rw [hcanonical]; rfl)
                          T hbaseline hBWlarge z hz) q) ∧
                  (∀ (z : B.EffectiveParamSpace)
                      (hz : z ∈ closedBall
                        (0 : B.EffectiveParamSpace) (a : ℝ)) v,
                    paperSharpNorm B.harmonicMass B.bandCenter
                        (B.partition.center_ne_zero B.n_gt_one)
                        ((e z hz).symm v) ≤
                      Csharp *
                        paperSharpNorm B.harmonicMass B.bandCenter
                          (B.partition.center_ne_zero B.n_gt_one) v) ∧
                  ∀ (z : B.EffectiveParamSpace)
                      (hz : z ∈ closedBall
                        (0 : B.EffectiveParamSpace) (a : ℝ)) v,
                    ‖(e z hz).symm v‖ ≤ Cordinary * ‖v‖ := by
  obtain ⟨kappa, hkappa, gapTol, hgapTol, Wgap, hGap⟩ :=
    exists_paperFineMesh_cutoff_eventually_canonical_lemma84_gap_nuisance
  obtain ⟨inverseTol, hinverseTol, Csharp, hCsharp,
      Cordinary, hCordinary, Winverse, hInverse⟩ :=
    exists_paperFineMesh_cutoff_eventually_actualBandSchur_sameEquiv_sharp_and_ordinary
  let meshTol : ℝ := min gapTol inverseTol
  let W₀ : ℕ := max Wgap Winverse
  have hmeshTol : 0 < meshTol := by
    dsimp only [meshTol]
    exact lt_min hgapTol hinverseTol
  refine ⟨kappa, hkappa, meshTol, hmeshTol,
    Csharp, hCsharp, Cordinary, hCordinary, W₀, ?_⟩
  intro W hW delta eta M hdelta hfine Head _instFintype
    _instDecidable _instNonempty Phead hPhead I U hU hlowerOne hupperU
    Cprom Cbank ledger a marginFloor hmargin
  have hWgap : Wgap ≤ W := (le_max_left Wgap Winverse).trans hW
  have hWinverse : Winverse ≤ W := (le_max_right Wgap Winverse).trans hW
  have hGapFine : delta + eta ≤ gapTol :=
    hfine.trans (min_le_left gapTol inverseTol)
  have hInverseFine : delta + eta ≤ inverseTol :=
    hfine.trans (min_le_right gapTol inverseTol)
  have hGapN := hGap W hWgap M hdelta hGapFine
    (Head := Head) Phead hPhead I U hU hlowerOne hupperU
      Cprom Cbank ledger a marginFloor hmargin
  have hInverseN := hInverse W hWinverse M hdelta hInverseFine
    Head Phead hPhead I U hU hlowerOne hupperU
      Cprom Cbank ledger a marginFloor hmargin
  filter_upwards [hGapN, hInverseN] with n hGapAt hInverseAt
  intro B hBn hBW hBWlarge hsep hremaining hcanonical hpartition
    T hTmargin hbaseline
  have hGapB := hGapAt B hBn hBW hBWlarge hsep hremaining hcanonical
    hpartition T hTmargin hbaseline
  obtain ⟨e, he, hsharp, hordinary⟩ :=
    hInverseAt B hBn hBW hBWlarge hsep hremaining hcanonical
      hpartition T hTmargin hbaseline
  exact ⟨e, hGapB, he, hsharp, hordinary⟩

end BridgeData

end

end Erdos390.Full.PaperBridgeFit

end

/- Source module: Erdos390.Full.PaperCanonicalLemma86CoefficientPackageEventually -/
section


/-!
# Canonical eventual coefficient package for Lemma 8.6

This file joins the paper-scale canonical prime geometry to the literal
first-stage Schur regression.  All prime-deviation moments, the moving-low
cell, the positive-cell variance, and the prime anchor are discharged before
the public call site.  The only quantitative call-site inputs are precisely
those supplied by the preceding inverse lemma:

* an equivalence representing the same literal Schur map, together with its
  sharp inverse estimate; and
* the normalized slow right-row estimate.

The theorem is uniform over an arbitrary effective box.  Its quantifiers are
ordered as in the paper: the structural prime cutoff is fixed before the
mesh, the mesh before the effective box, and only then may the ambient
integer threshold be selected.
-/

open scoped BigOperators
open Filter Topology Metric Set

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

open ArithmeticModel ArithmeticBandGeometry
open PaperWeightedInverseExport PrimeSums
open RegularMeshPrimeCutoffs PaperPermittedRegularMesh

namespace BridgeData



set_option maxHeartbeats 1000000 in
/--
Uniform canonical `q^reg` and compensated-coefficient bounds at the literal
paper scale `B.w = delta + eta`.

No moment, profile, row-residual, or anchor hypothesis occurs in this
statement.  The same-map identity is retained explicitly, so the displayed
regression is certified to solve the literal actual Schur equation rather
than merely being the image of an unrelated bounded equivalence.
-/
theorem canonicalPaperLemma86CoefficientCutoff_eventually
    (cMesh : ℝ) (hcMesh : 0 < cMesh)
    (Cinv Crow : ℝ) (hCinv : 0 ≤ Cinv) (hCrow : 0 ≤ Crow) :
    ∀ W : ℕ, canonicalPaperLemma86CoefficientCutoff ≤ W →
      ∀ {delta eta : ℝ}
        (M : RegularRelativeMesh.Mesh delta eta)
        (hdelta : 0 < delta)
        (_hPermitted : IsPermitted (cMesh := cMesh) M),
        delta + eta ≤
            RegularMeshPrimeCutoffs.Mesh.canonicalPaperGeometricMeshTolerance →
        ∀ {Head : Type*} [Fintype Head] [DecidableEq Head] [Nonempty Head]
          (a : NNReal),
          ∀ᶠ n : ℕ in atTop,
            ∀ (B : BridgeData Head (Fin (M.cellCount + 1))),
              B.sampleData.n = n →
              B.sampleData.W = W →
              (∃ (hWne : B.sampleData.W ≠ 0)
                  (S : ScaleSeparation M B.sampleData.n B.sampleData.W),
                B.partition =
                  RegularMeshPrimeCutoffs.Mesh.canonicalPartition M hdelta
                    B.n_gt_one hWne S) →
              B.w = delta + eta →
              ∀ (z : B.EffectiveParamSpace),
                z ∈ closedBall
                  (0 : B.EffectiveParamSpace) (a : ℝ) →
                ∀ {gamma : ℝ} (hgamma : 0 < gamma)
                  (hgap : ∀ u, gamma * ‖u‖ ^ 2 ≤
                    inner ℝ u (B.nuisanceCovarianceOperator
                      (B.effectiveParamEquiv z) u))
                  (e : B.RawBandGauge ≃ₗ[ℝ] B.RawBandGauge),
                  (∀ q, e q = B.actualBandSchurLinearMap
                    (B.effectiveParamEquiv z) hgamma hgap q) →
                  (∀ v,
                    paperSharpNorm B.harmonicMass B.bandCenter
                        (B.partition.center_ne_zero B.n_gt_one) (e.symm v) ≤
                      Cinv *
                        paperSharpNorm B.harmonicMass B.bandCenter
                          (B.partition.center_ne_zero B.n_gt_one) v) →
                  (∀ j,
                    |B.normalizedBandCovarianceRow
                        (B.effectiveParamEquiv z)
                        (B.nuisanceResidualScore
                          (B.effectiveParamEquiv z) hgamma hgap
                          B.slowScore) j| ≤
                      (Crow * B.w) * B.bandCenter j) →
                  B.actualBandSchurLinearMap
                      (B.effectiveParamEquiv z) hgamma hgap
                      (B.actualBandRegression
                        (B.effectiveParamEquiv z) hgamma hgap e) =
                    B.actualBandRegressionTarget
                      (B.effectiveParamEquiv z) hgamma hgap ∧
                  paperSharpNorm B.harmonicMass B.bandCenter
                      (B.partition.center_ne_zero B.n_gt_one)
                      (B.actualBandRegression
                        (B.effectiveParamEquiv z) hgamma hgap e) ≤
                    (Cinv * (2 * Crow)) * (delta + eta) ∧
                  (∀ p : BandPrime B.sampleData.n B.sampleData.W,
                    |B.actualCompensatedCoefficient
                      (B.actualBandRegression
                        (B.effectiveParamEquiv z) hgamma hgap e) p| ≤
                      (1 + Cinv * (2 * Crow)) * (delta + eta)) ∧
                  B.partition.compensatedL1
                      (B.actualBandRegression
                        (B.effectiveParamEquiv z) hgamma hgap e) ≤
                    (7 + (Cinv * (2 * Crow)) * (2 * Real.log 4)) *
                      (delta + eta) ∧
                  B.partition.compensatedL2Sq
                      (B.actualBandRegression
                        (B.effectiveParamEquiv z) hgamma hgap e) ≤
                    2 * (4 +
                      (Cinv * (2 * Crow)) ^ 2 * (2 * Real.log 4)) *
                        (delta + eta) ^ 2 := by
  intro W hW delta eta M hdelta hPermitted hfine
    Head _instHead _instHeadDec _instHeadNonempty a
  have hWgeom :
      RegularMeshPrimeCutoffs.Mesh.canonicalPaperGeometricCutoff ≤ W := by
    simpa only [canonicalPaperLemma86CoefficientCutoff] using hW
  have hGeometry :=
    RegularMeshPrimeCutoffs.Mesh.canonicalPaperGeometricCutoff_eventually
      cMesh hcMesh W hWgeom M hdelta hPermitted hfine
  have hBandT := eventually_bandTReciprocalSum_le W
  filter_upwards [hGeometry, hBandT] with n hGeometryAt hBandTAt
  intro B hBn hBW hpartition hscale z _hz gamma hgamma hgap e he hinv
    hrightRow
  subst n
  subst W
  obtain ⟨hWgeomNe, hnGeom, hGeometryAll⟩ := hGeometryAt
  obtain ⟨hWuser, S, hpartitionUser⟩ := hpartition
  let Pcanonical :=
    RegularMeshPrimeCutoffs.Mesh.canonicalPartition M hdelta
      hnGeom hWgeomNe S
  have hpartitionCanonical : B.partition = Pcanonical := by
    exact hpartitionUser.trans (by dsimp only [Pcanonical])
  obtain ⟨hdevSupRaw, hdevL1Raw, _hvarLowerRaw, hdevL2Raw,
      _hcenterRaw⟩ := hGeometryAll S
  have hdevSup : ∀ p : BandPrime B.sampleData.n B.sampleData.W,
      |B.partition.deviation p| ≤ B.w := by
    intro p
    rw [hpartitionCanonical, hscale]
    exact hdevSupRaw p
  have hdevL1 : B.partition.totalL1 ≤ 7 * B.w := by
    rw [hpartitionCanonical, hscale]
    exact hdevL1Raw
  have hdevL2 : B.partition.variance ≤ 4 * B.w ^ 2 := by
    rw [hpartitionCanonical, hscale]
    exact hdevL2Raw
  have hright := B.actualBandRegressionTarget_sharpNorm_le_of_row
    (B.effectiveParamEquiv z) hgamma hgap hCrow B.w_pos.le hrightRow
  have hTwoCrow : 0 ≤ 2 * Crow := mul_nonneg (by norm_num) hCrow
  have hsharpRaw := B.actualBandRegression_sharpNorm_le
    (B.effectiveParamEquiv z) hgamma hgap e hCinv hinv hright
  obtain ⟨hcoeffSupRaw, hcoeffL1Raw, hcoeffL2Raw⟩ :=
    B.actualBandRegression_compensatedCoefficient_three_bounds
      (B.effectiveParamEquiv z) hgamma hgap e hCinv hTwoCrow B.w_pos.le
      hinv hright hBandTAt hdevSup hdevL1 hdevL2
  have hnormal := B.actualBandRegression_normalEquation
    (B.effectiveParamEquiv z) hgamma hgap e he
  have hsharp : paperSharpNorm B.harmonicMass B.bandCenter
      (B.partition.center_ne_zero B.n_gt_one)
      (B.actualBandRegression
        (B.effectiveParamEquiv z) hgamma hgap e) ≤
        (Cinv * (2 * Crow)) * (delta + eta) := by
    simpa only [hscale] using hsharpRaw
  have hcoeffSup : ∀ p : BandPrime B.sampleData.n B.sampleData.W,
      |B.actualCompensatedCoefficient
        (B.actualBandRegression
          (B.effectiveParamEquiv z) hgamma hgap e) p| ≤
          (1 + Cinv * (2 * Crow)) * (delta + eta) := by
    simpa only [hscale] using hcoeffSupRaw
  have hcoeffL1 : B.partition.compensatedL1
      (B.actualBandRegression
        (B.effectiveParamEquiv z) hgamma hgap e) ≤
      (7 + (Cinv * (2 * Crow)) * (2 * Real.log 4)) *
        (delta + eta) := by
    simpa only [hscale] using hcoeffL1Raw
  have hcoeffL2 : B.partition.compensatedL2Sq
      (B.actualBandRegression
        (B.effectiveParamEquiv z) hgamma hgap e) ≤
      2 * (4 + (Cinv * (2 * Crow)) ^ 2 * (2 * Real.log 4)) *
        (delta + eta) ^ 2 := by
    simpa only [hscale] using hcoeffL2Raw
  exact ⟨hnormal, hsharp, hcoeffSup, hcoeffL1, hcoeffL2⟩



end BridgeData

end

end Erdos390.Full.PaperBridgeFit

end

/- Source module: Erdos390.Full.PaperCanonicalLemma86GeometryCoefficientsEventually -/
section


/-!
# Closed geometric and coefficient clauses of paper Lemma 8.6

This file combines the already discharged moving-low-cell geometry, the
literal Lemma 8.4 Schur inverse, and the non-step slow right row.  The result
is the first half of the paper-order Lemma 8.6 umbrella: the same equivalence
which is exactly the actual finite nuisance-Schur map supplies the regression
and all three compensated-coefficient estimates.

No anchor, convergence assertion, analytic comparison, or row estimate is
present at the public call site.  The two mesh parameters are independent;
their only smallness condition is on `delta + eta`.  All numerical constants
and the structural cutoff are selected before `W`, the permitted mesh, the
finite head data, and the effective tilt ball.
-/

open scoped BigOperators
open Filter Topology Metric Set

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

open ArithmeticModel ArithmeticBandGeometry FiniteProbability
open PaperGuardCensus PaperWeightedInverseExport
open RegularMeshPrimeCutoffs PaperPermittedRegularMesh

namespace BridgeData

set_option maxHeartbeats 2000000 in
/--
Assumption-free paper-order terminal for the geometric and coefficient
conclusions of Lemma 8.6.

The output retains the literal normal equation and the exact same-map
identity.  Consequently the displayed `q^reg` and compensated coefficients
are attached to the actual finite-`n` nuisance-Schur operator, not merely to
an abstract bounded equivalence.
-/
theorem exists_paperFineMesh_cutoff_eventually_canonical_lemma86_geometry_coefficients
    (cMesh : ℝ) (hcMesh : 0 < cMesh) :
    ∃ meshTol : ℝ, 0 < meshTol ∧
      ∃ Csharp : ℝ, 0 < Csharp ∧
      ∃ Cordinary : ℝ, 0 < Cordinary ∧
      ∃ Crow : ℝ, 0 ≤ Crow ∧
      ∃ W₀ : ℕ,
      ∀ W : ℕ, W₀ ≤ W →
      ∀ {delta eta : ℝ} (M : RegularRelativeMesh.Mesh delta eta)
        (hdelta : 0 < delta)
        (hPermitted : IsPermitted (cMesh := cMesh) M),
        delta + eta ≤ meshTol →
        ∀ (Head : Type*) [Fintype Head] [DecidableEq Head] [Nonempty Head],
        ∀ (Phead : Head → HeadPattern.Pattern),
          (∀ h : Head, ∀ p : ℕ,
            p ∈ (Phead h).primes ↔ p.Prime ∧ p ≤ W) →
        ∀ (I : PhysicalIntervals) (U : ℝ) (hU : 1 ≤ U)
          (hlowerOne : ∀ sigma, 1 ≤ I.lower sigma)
          (hupperU : ∀ sigma, I.upper sigma ≤ U),
        ∀ (Cprom Cbank : ℕ) (ledger : ∀ n, Ledger n Cprom Cbank),
        ∀ (a : NNReal) (marginFloor : ℝ), 0 < marginFloor →
        ∀ᶠ n : ℕ in atTop,
          ∀ (B : BridgeData Head (Fin (M.cellCount + 1))),
            B.sampleData.n = n → B.sampleData.W = W →
            ∀ (hBWlarge : 1 < B.sampleData.W),
            ∀ (hsep : physicalBound (I.upper .minus) B.sampleData.n <
                physicalBound (I.lower .plus) B.sampleData.n)
              (hremaining : ∀ c : Cell Head,
                (rawCell Phead I B.sampleData.n c \
                  (ledger B.sampleData.n).guards).Nonempty),
              (hcanonical : B.sampleData = canonicalSampleData
                (W := B.sampleData.W) Phead I (ledger B.sampleData.n)
                  hsep hremaining) →
              (hpartition : ∃ (hWne : B.sampleData.W ≠ 0)
                  (S : ScaleSeparation M B.sampleData.n B.sampleData.W),
                B.partition = RegularMeshPrimeCutoffs.Mesh.canonicalPartition
                  M hdelta B.n_gt_one hWne S) →
              (hscale : B.w = delta + eta) →
              ∀ (T : BarycentricTarget B.sampleData)
                (hTmargin : marginFloor ≤ T.cellMassMargin)
                (hbaseline : B.baseline = T.baseline),
                (∀ p : BandPrime B.sampleData.n B.sampleData.W,
                    |B.partition.deviation p| ≤ delta + eta) ∧
                B.partition.totalL1 ≤ 7 * (delta + eta) ∧
                (delta + eta) ^ 2 ≤
                  (456 / cMesh ^ 2) * B.partition.variance ∧
                B.partition.variance ≤ 4 * (delta + eta) ^ 2 ∧
                B.partition.variance ≤ B.partition.centerEnergy ∧
                ∃ e : ∀ (z : B.EffectiveParamSpace),
                    z ∈ closedBall (0 : B.EffectiveParamSpace) (a : ℝ) →
                      B.RawBandGauge ≃ₗ[ℝ] B.RawBandGauge,
                  (∀ (z : B.EffectiveParamSpace)
                      (hz : z ∈ closedBall
                        (0 : B.EffectiveParamSpace) (a : ℝ)) q,
                    e z hz q =
                      B.actualBandSchurLinearMap (B.effectiveParamEquiv z)
                        (B.canonicalEffectiveNuisanceGamma_pos
                          I U (3 * (a : ℝ)) T)
                        (B.canonicalEffectiveNuisanceGap_on_closedBall I a
                          hU hlowerOne hupperU
                          (by intro sigma; rw [hcanonical]; rfl)
                          (by intro sigma; rw [hcanonical]; rfl)
                          T hbaseline hBWlarge z hz) q) ∧
                  (∀ (z : B.EffectiveParamSpace)
                      (hz : z ∈ closedBall
                        (0 : B.EffectiveParamSpace) (a : ℝ)) v,
                    paperSharpNorm B.harmonicMass B.bandCenter
                        (B.partition.center_ne_zero B.n_gt_one)
                        ((e z hz).symm v) ≤
                      Csharp *
                        paperSharpNorm B.harmonicMass B.bandCenter
                          (B.partition.center_ne_zero B.n_gt_one) v) ∧
                  (∀ (z : B.EffectiveParamSpace)
                      (hz : z ∈ closedBall
                        (0 : B.EffectiveParamSpace) (a : ℝ)) v,
                    ‖(e z hz).symm v‖ ≤ Cordinary * ‖v‖) ∧
                  ∀ (z : B.EffectiveParamSpace)
                    (hz : z ∈ closedBall
                      (0 : B.EffectiveParamSpace) (a : ℝ)),
                    (∀ j,
                      |B.normalizedBandCovarianceRow
                          (B.effectiveParamEquiv z)
                          (B.nuisanceResidualScore
                            (B.effectiveParamEquiv z)
                            (B.canonicalEffectiveNuisanceGamma_pos
                              I U (3 * (a : ℝ)) T)
                            (B.canonicalEffectiveNuisanceGap_on_closedBall I a
                              hU hlowerOne hupperU
                              (by intro sigma; rw [hcanonical]; rfl)
                              (by intro sigma; rw [hcanonical]; rfl)
                              T hbaseline hBWlarge z hz)
                            B.slowScore) j| ≤
                        (Crow * B.w) * B.bandCenter j) ∧
                    B.actualBandSchurLinearMap
                        (B.effectiveParamEquiv z)
                        (B.canonicalEffectiveNuisanceGamma_pos
                          I U (3 * (a : ℝ)) T)
                        (B.canonicalEffectiveNuisanceGap_on_closedBall I a
                          hU hlowerOne hupperU
                          (by intro sigma; rw [hcanonical]; rfl)
                          (by intro sigma; rw [hcanonical]; rfl)
                          T hbaseline hBWlarge z hz)
                        (B.actualBandRegression
                          (B.effectiveParamEquiv z)
                          (B.canonicalEffectiveNuisanceGamma_pos
                            I U (3 * (a : ℝ)) T)
                          (B.canonicalEffectiveNuisanceGap_on_closedBall I a
                            hU hlowerOne hupperU
                            (by intro sigma; rw [hcanonical]; rfl)
                            (by intro sigma; rw [hcanonical]; rfl)
                            T hbaseline hBWlarge z hz)
                          (e z hz)) =
                      B.actualBandRegressionTarget
                        (B.effectiveParamEquiv z)
                        (B.canonicalEffectiveNuisanceGamma_pos
                          I U (3 * (a : ℝ)) T)
                        (B.canonicalEffectiveNuisanceGap_on_closedBall I a
                          hU hlowerOne hupperU
                          (by intro sigma; rw [hcanonical]; rfl)
                          (by intro sigma; rw [hcanonical]; rfl)
                          T hbaseline hBWlarge z hz) ∧
                    paperSharpNorm B.harmonicMass B.bandCenter
                        (B.partition.center_ne_zero B.n_gt_one)
                        (B.actualBandRegression
                          (B.effectiveParamEquiv z)
                          (B.canonicalEffectiveNuisanceGamma_pos
                            I U (3 * (a : ℝ)) T)
                          (B.canonicalEffectiveNuisanceGap_on_closedBall I a
                            hU hlowerOne hupperU
                            (by intro sigma; rw [hcanonical]; rfl)
                            (by intro sigma; rw [hcanonical]; rfl)
                            T hbaseline hBWlarge z hz)
                          (e z hz)) ≤
                      (Csharp * (2 * Crow)) * (delta + eta) ∧
                    (∀ p : BandPrime B.sampleData.n B.sampleData.W,
                      |B.actualCompensatedCoefficient
                        (B.actualBandRegression
                          (B.effectiveParamEquiv z)
                          (B.canonicalEffectiveNuisanceGamma_pos
                            I U (3 * (a : ℝ)) T)
                          (B.canonicalEffectiveNuisanceGap_on_closedBall I a
                            hU hlowerOne hupperU
                            (by intro sigma; rw [hcanonical]; rfl)
                            (by intro sigma; rw [hcanonical]; rfl)
                            T hbaseline hBWlarge z hz)
                          (e z hz)) p| ≤
                        (1 + Csharp * (2 * Crow)) * (delta + eta)) ∧
                    B.partition.compensatedL1
                        (B.actualBandRegression
                          (B.effectiveParamEquiv z)
                          (B.canonicalEffectiveNuisanceGamma_pos
                            I U (3 * (a : ℝ)) T)
                          (B.canonicalEffectiveNuisanceGap_on_closedBall I a
                            hU hlowerOne hupperU
                            (by intro sigma; rw [hcanonical]; rfl)
                            (by intro sigma; rw [hcanonical]; rfl)
                            T hbaseline hBWlarge z hz)
                          (e z hz)) ≤
                      (7 + (Csharp * (2 * Crow)) * (2 * Real.log 4)) *
                        (delta + eta) ∧
                    B.partition.compensatedL2Sq
                        (B.actualBandRegression
                          (B.effectiveParamEquiv z)
                          (B.canonicalEffectiveNuisanceGamma_pos
                            I U (3 * (a : ℝ)) T)
                          (B.canonicalEffectiveNuisanceGap_on_closedBall I a
                            hU hlowerOne hupperU
                            (by intro sigma; rw [hcanonical]; rfl)
                            (by intro sigma; rw [hcanonical]; rfl)
                            T hbaseline hBWlarge z hz)
                          (e z hz)) ≤
                      2 * (4 +
                        (Csharp * (2 * Crow)) ^ 2 * (2 * Real.log 4)) *
                          (delta + eta) ^ 2 := by
  obtain ⟨_kappa, _hkappa, inverseTol, hinverseTol,
      Csharp, hCsharp, Cordinary, hCordinary, Winverse, hInverse⟩ :=
    exists_paperFineMesh_cutoff_eventually_canonical_lemma84
  obtain ⟨CF, Cprod, hCF, hCprod, Wrow, _hWrowTwo, hRow⟩ :=
    exists_global_cutoff_eventually_canonical_nonstepSlowResidualRow_le
  let Crow : ℝ := 2 + CF + 7 * Cprod
  let meshTol : ℝ := min inverseTol
    RegularMeshPrimeCutoffs.Mesh.canonicalPaperGeometricMeshTolerance
  let W₀ : ℕ := max Winverse
    (max Wrow canonicalPaperLemma86CoefficientCutoff)
  have hCrow : 0 ≤ Crow := by
    dsimp only [Crow]
    positivity
  have hmeshTol : 0 < meshTol := by
    dsimp only [meshTol]
    exact lt_min hinverseTol (by
      norm_num [RegularMeshPrimeCutoffs.Mesh.canonicalPaperGeometricMeshTolerance])
  refine ⟨meshTol, hmeshTol, Csharp, hCsharp, Cordinary, hCordinary,
    Crow, hCrow, W₀, ?_⟩
  intro W hW delta eta M hdelta hPermitted hfine
    Head _instFintype _instDecidable _instNonempty Phead hPhead
    I U hU hlowerOne hupperU Cprom Cbank ledger a marginFloor hmargin
  have hWinverse : Winverse ≤ W := by
    dsimp only [W₀] at hW
    omega
  have hWrow : Wrow ≤ W := by
    dsimp only [W₀] at hW
    omega
  have hWcoefficient : canonicalPaperLemma86CoefficientCutoff ≤ W := by
    dsimp only [W₀] at hW
    omega
  have hInverseFine : delta + eta ≤ inverseTol :=
    hfine.trans (min_le_left inverseTol
      RegularMeshPrimeCutoffs.Mesh.canonicalPaperGeometricMeshTolerance)
  have hGeometryFine : delta + eta ≤
      RegularMeshPrimeCutoffs.Mesh.canonicalPaperGeometricMeshTolerance :=
    hfine.trans (min_le_right inverseTol
      RegularMeshPrimeCutoffs.Mesh.canonicalPaperGeometricMeshTolerance)
  have hInverseN := hInverse W hWinverse M hdelta hInverseFine
    Head Phead hPhead I U hU hlowerOne hupperU
      Cprom Cbank ledger a marginFloor hmargin
  have hRowN := hRow W hWrow hdelta M Phead hPhead I U hU
    hlowerOne hupperU Cprom Cbank ledger a marginFloor hmargin
  have hGeometryN :=
    RegularMeshPrimeCutoffs.Mesh.canonicalPaperGeometricCutoff_eventually
      cMesh hcMesh W hWcoefficient M hdelta hPermitted hGeometryFine
  have hCoefficientN := canonicalPaperLemma86CoefficientCutoff_eventually
    cMesh hcMesh Csharp Crow hCsharp.le hCrow W hWcoefficient
      M hdelta hPermitted hGeometryFine (Head := Head) a
  filter_upwards [hInverseN, hRowN, hGeometryN, hCoefficientN] with
      n hInverseAt hRowAt hGeometryAt hCoefficientAt
  intro B hBn hBW hBWlarge hsep hremaining hcanonical hpartition
    hscale T hTmargin hbaseline
  subst n
  subst W
  obtain ⟨e, _hGap, he, hsharp, hordinary⟩ :=
    hInverseAt B rfl rfl hBWlarge hsep hremaining hcanonical
      hpartition T hTmargin hbaseline
  obtain ⟨hWgeomNe, hnGeom, hGeometryAll⟩ := hGeometryAt
  have hpartitionCall := hpartition
  obtain ⟨hWuser, S, hpartitionUser⟩ := hpartition
  have hSgeom : ScaleSeparation M B.sampleData.n B.sampleData.W := S
  let Pcanonical :=
    RegularMeshPrimeCutoffs.Mesh.canonicalPartition M hdelta
      hnGeom hWgeomNe hSgeom
  have hpartitionCanonical : B.partition = Pcanonical := by
    exact hpartitionUser.trans (by dsimp only [Pcanonical])
  obtain ⟨hdevRaw, hL1Raw, hvarLowerRaw, hvarUpperRaw, hcenterRaw⟩ :=
    hGeometryAll hSgeom
  have hdev : ∀ p : BandPrime B.sampleData.n B.sampleData.W,
      |B.partition.deviation p| ≤ delta + eta := by
    intro p
    rw [hpartitionCanonical]
    exact hdevRaw p
  have hL1 : B.partition.totalL1 ≤ 7 * (delta + eta) := by
    rw [hpartitionCanonical]
    exact hL1Raw
  have hvarLower : (delta + eta) ^ 2 ≤
      (456 / cMesh ^ 2) * B.partition.variance := by
    rw [hpartitionCanonical]
    exact hvarLowerRaw
  have hvarUpper : B.partition.variance ≤ 4 * (delta + eta) ^ 2 := by
    rw [hpartitionCanonical]
    exact hvarUpperRaw
  have hcenter : B.partition.variance ≤ B.partition.centerEnergy := by
    rw [hpartitionCanonical]
    exact hcenterRaw
  refine ⟨hdev, hL1, hvarLower, hvarUpper, hcenter, e, he, hsharp,
    hordinary, ?_⟩
  intro z hz
  let hgamma : 0 < B.canonicalEffectiveNuisanceGamma
      I U (3 * (a : ℝ)) T :=
    B.canonicalEffectiveNuisanceGamma_pos I U (3 * (a : ℝ)) T
  let hgap : ∀ v,
      B.canonicalEffectiveNuisanceGamma I U (3 * (a : ℝ)) T * ‖v‖ ^ 2 ≤
        inner ℝ v (B.nuisanceCovarianceOperator
          (B.effectiveParamEquiv z) v) :=
    B.canonicalEffectiveNuisanceGap_on_closedBall I a hU
      hlowerOne hupperU
      (by intro sigma; rw [hcanonical]; rfl)
      (by intro sigma; rw [hcanonical]; rfl)
      T hbaseline hBWlarge z hz
  have hright : ∀ j,
      |B.normalizedBandCovarianceRow
          (B.effectiveParamEquiv z)
          (B.nuisanceResidualScore
            (B.effectiveParamEquiv z) hgamma hgap B.slowScore) j| ≤
        (Crow * B.w) * B.bandCenter j := by
    intro j
    simpa only [Crow, hgamma, hgap] using
      hRowAt B rfl rfl hsep hremaining hcanonical hpartitionCall hscale
        T hTmargin hbaseline z hz j
  have hCoefficient := hCoefficientAt B rfl rfl hpartitionCall hscale z hz
    hgamma hgap (e z hz) (he z hz) (hsharp z hz) hright
  exact ⟨by simpa only [hgamma, hgap] using hright,
    by simpa only [hgamma, hgap] using hCoefficient⟩

end BridgeData

end

end Erdos390.Full.PaperBridgeFit

end

universe u_1
theorem solution : Erdos390.RemainingAnalyticGoal002_004.{u_1} := by
  exact @Erdos390.Full.PaperBridgeFit.BridgeData.exists_paperFineMesh_cutoff_eventually_canonical_lemma86_geometry_coefficients
