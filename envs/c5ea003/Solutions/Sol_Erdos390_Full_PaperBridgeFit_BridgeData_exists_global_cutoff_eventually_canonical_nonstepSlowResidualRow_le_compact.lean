-- Prove2me | solution 1 for Erdos390.Full.PaperBridgeFit.BridgeData.exists_global_cutoff_eventually_canonical_nonstepSlowResidualRow_le_compact
-- status  : ACCEPTED   (prove)
-- author  : @doctosil
-- created : 2026-09-17T17:16:38.605792+00:00
-- url     : https://prove2.me/submissions/bb3846a9-cc14-4995-b3b0-82e369e2a7f8

import Definitions.Def_erdos390_remaining_analytic_propositions_002
import Definitions.Def_erdos390_analytic_nonstep_certificate
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
import Theorems.Thm_Erdos390_Full_PaperBridgeFit_BridgeData_abs_referenceSlowRow_le_of_harmonicCentering
import Theorems.Thm_Erdos390_Full_PaperBridgeFit_BridgeData_forall_accuracy_exists_cutoff_eventually_canonical_fullSlowRow_sub_reference_compact
import Theorems.Thm_Erdos390_Full_PaperCanonicalMarkedNuisanceRows_PaperBridgeFit_BridgeData_exists_uniform_canonical_tiltedLaw_nuisance_valuation_rate_on_effectiveBall_compact
import Theorems.Thm_Erdos390_Full_RegularMeshPrimeCutoffs_Mesh_canonicalCenterEnvelopeCutoff_eventually_inverse
import Theorems.Thm_Erdos390_Full_RegularMeshPrimeCutoffs_Mesh_momentReady_of_endpointMomentBounds



section
universe u_1 u_2
theorem Erdos390.Full.PaperCanonicalMarkedNuisanceRows.PaperBridgeFit.BridgeData.exists_uniform_canonical_tiltedLaw_nuisance_valuation_rate_on_effectiveBall : Erdos390.RemainingAnalyticGoal004_002.{u_1, u_2} := @Erdos390.Full.PaperCanonicalMarkedNuisanceRows.PaperBridgeFit.BridgeData.exists_uniform_canonical_tiltedLaw_nuisance_valuation_rate_on_effectiveBall_compact
end
section
universe u_1
theorem Erdos390.Full.PaperBridgeFit.BridgeData.forall_accuracy_exists_cutoff_eventually_canonical_fullSlowRow_sub_reference : Erdos390.RemainingAnalyticGoal004_001.{u_1} := @Erdos390.Full.PaperBridgeFit.BridgeData.forall_accuracy_exists_cutoff_eventually_canonical_fullSlowRow_sub_reference_compact
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



/-- The positive cells telescope exactly from `delta` to `1`. -/
theorem sum_width_eq_one_sub_delta :
    ∑ k : Fin M.cellCount, M.width k = 1 - delta := by
  change (∑ k : Fin M.cellCount,
      (fun i : ℕ ↦ M.endpoint (i + 1) - M.endpoint i) k.1) =
    1 - delta
  calc
    (∑ k : Fin M.cellCount,
        (fun i : ℕ ↦ M.endpoint (i + 1) - M.endpoint i) k.1) =
        ∑ k ∈ Finset.range M.cellCount,
          (M.endpoint (k + 1) - M.endpoint k) :=
      Fin.sum_univ_eq_sum_range
        (fun i : ℕ ↦ M.endpoint (i + 1) - M.endpoint i) M.cellCount
    _ = 1 - delta := by
      rw [Finset.sum_range_sub, M.endpoint_cellCount, M.endpoint_zero]

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



theorem covariance_smul_left (mu : FiniteProbability Omega)
    (a : ℝ) (F G : Omega → ℝ) :
    mu.covariance (fun omega ↦ a * F omega) G =
      a * mu.covariance F G := by
  unfold covariance
  rw [mu.expect_smul a F]
  rw [show (fun omega ↦ a * F omega * G omega) =
      fun omega ↦ a * (F omega * G omega) by
    funext omega
    ring]
  rw [mu.expect_smul]
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

theorem covariance_comm (mu : FiniteProbability Omega) (F G : Omega → ℝ) :
    mu.covariance F G = mu.covariance G F := by
  unfold covariance
  congr 1
  · apply Finset.sum_congr rfl
    intro omega _
    ring
  · ring

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

/- Source module: Erdos390.Full.PaperBridgeFit -/
section


/-!
# The finite arithmetic data in the bridge fit

This file instantiates the nonlinear finite-family layer with the actual
objects appearing in Lemmas 8.5--8.6 and Proposition 8.7: guarded smooth
structured cells, arithmetic prime bands, valuation statistics, the physical
logarithm, centered head indicators, and the compensated slow score.

The sample is the tagged disjoint union of the paper's cells.  Tagging is the
formal counterpart of the disjointification performed before normalization;
the underlying integer remains available as `Sample.value`.

All statements in this file are finite identities.  Asymptotic marked-smooth
estimates are not silently inserted as hypotheses equivalent to the desired
fit.  Where a later analytic estimate is still needed, the exact finite
quantity it must bound is exposed explicitly.
-/

open scoped BigOperators
open Metric Set

namespace Erdos390.Full

noncomputable section

open ArithmeticModel StructuredCells HeadPattern

namespace PaperBridgeFit







namespace StructuredSampleData

variable {Head : Type*} [Fintype Head]



































end StructuredSampleData



namespace BaselineAllocation

variable {Head : Type*} [Fintype Head]
  {D : StructuredSampleData Head}



















end BaselineAllocation









namespace BridgeData

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]
  (B : BridgeData Head Band)

















































































/-! ### Exact main/nuisance coordinate splitting -/





























































































theorem nuisanceCovarianceEquiv_apply [Nonempty Head]
    (xi : B.ParamSpace) {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (z : B.NuisanceSpace) :
    B.nuisanceCovarianceEquiv xi hgamma hgap z =
      B.nuisanceCovarianceOperator xi z := by
  simp [nuisanceCovarianceEquiv]



































/-! ## Exact target and moment correspondence -/















































































/-! ## Actual baseline mixture and coarse cells -/





























































































/-! ## Explicit finite diameter -/





















/-! ## A finite `ell^1` tilt bound -/













































/-! ## Target envelopes imply the ODE radius margin -/















/-! ## Concrete Proposition 8.7 endpoint -/











end BridgeData

/-! ## Non-circular order of asymptotic choices -/



end PaperBridgeFit

end


end Erdos390.Full

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



namespace Mesh

variable {delta eta : ℝ} (M : Mesh delta eta)









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











theorem totalL1_eq_sum_bandL1 : P.totalL1 = ∑ j : Band, P.bandL1 j := by
  unfold totalL1 bandL1
  rw [← Finset.sum_fiberwise Finset.univ P.band
    (fun p : BandPrime n W ↦ (1 / (p.1 : ℝ)) * |P.deviation p|)]
  apply Finset.sum_congr rfl
  intro j hj
  rfl

theorem variance_eq_sum_bandVariance :
    P.variance = ∑ j : Band, P.bandVariance j := by
  change (∑ p : BandPrime n W,
      (1 / (p.1 : ℝ)) * P.data.cellDeviation p *
        P.data.cellDeviation p) = _
  rw [← Finset.sum_fiberwise Finset.univ P.band
    (fun p : BandPrime n W ↦
      (1 / (p.1 : ℝ)) * P.data.cellDeviation p *
        P.data.cellDeviation p)]
  apply Finset.sum_congr rfl
  intro j hj
  unfold bandVariance deviation
  apply Finset.sum_congr rfl
  intro p hp
  simp only [Erdos390.Lemma84.WeightedBandData.cellDeviation]
  change (1 / (p.1 : ℝ)) *
      (P.center (P.band p) - tPrime n p.1) *
        (P.center (P.band p) - tPrime n p.1) =
    (1 / (p.1 : ℝ)) * (P.center (P.band p) - tPrime n p.1) ^ 2
  rw [pow_two]
  ring

theorem bandVariance_eq_second_sub_mass_center_sq (j : Band) :
    P.bandVariance j =
      P.bandSecondMoment j - P.mass j * P.center j ^ 2 := by
  have hrewrite : P.bandVariance j =
      ∑ p ∈ P.data.fiber j, (1 / (p.1 : ℝ)) *
        (P.center j - tPrime n p.1) ^ 2 := by
    unfold bandVariance deviation
    apply Finset.sum_congr rfl
    intro p hp
    have hpj : P.band p = j :=
      (Erdos390.Lemma84.WeightedBandData.mem_fiber_iff P.data).mp hp
    rw [hpj]
  rw [hrewrite]
  have hmass : (∑ p ∈ P.data.fiber j, 1 / (p.1 : ℝ)) = P.mass j := rfl
  have hfirst :
      (∑ p ∈ P.data.fiber j,
        (1 / (p.1 : ℝ)) * tPrime n p.1) = P.mass j * P.center j := by
    change (∑ p ∈ P.data.fiber j,
        (1 / (p.1 : ℝ)) * tPrime n p.1) =
      P.data.mass j *
        ((∑ p ∈ P.data.fiber j,
          (1 / (p.1 : ℝ)) * tPrime n p.1) / P.data.mass j)
    field_simp [ne_of_gt (P.data.mass_pos j)]
  calc
    (∑ p ∈ P.data.fiber j,
        (1 / (p.1 : ℝ)) * (P.center j - tPrime n p.1) ^ 2) =
        ∑ p ∈ P.data.fiber j,
          ((1 / (p.1 : ℝ)) * P.center j ^ 2 -
            2 * P.center j * ((1 / (p.1 : ℝ)) * tPrime n p.1) +
            (1 / (p.1 : ℝ)) * tPrime n p.1 ^ 2) := by
      apply Finset.sum_congr rfl
      intro p hp
      ring
    _ = (∑ p ∈ P.data.fiber j, 1 / (p.1 : ℝ)) * P.center j ^ 2 -
        2 * P.center j *
          (∑ p ∈ P.data.fiber j, (1 / (p.1 : ℝ)) * tPrime n p.1) +
        ∑ p ∈ P.data.fiber j, (1 / (p.1 : ℝ)) * tPrime n p.1 ^ 2 := by
      rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
        ← Finset.sum_mul, ← Finset.mul_sum]
    _ = P.bandSecondMoment j - P.mass j * P.center j ^ 2 := by
      rw [hmass, hfirst]
      unfold bandSecondMoment
      ring







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

theorem bandL1_le_width_mul_mass_of_coord_bounds (j : Band) {a b : ℝ}
    (hcoord : ∀ p ∈ P.data.fiber j, tPrime n p.1 ∈ Set.Icc a b) :
    P.bandL1 j ≤ (b - a) * P.mass j := by
  unfold bandL1
  change (∑ p ∈ P.data.fiber j,
      (1 / (p.1 : ℝ)) * |P.deviation p|) ≤
    (b - a) * (∑ p ∈ P.data.fiber j, 1 / (p.1 : ℝ))
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro p hp
  have hw : 0 ≤ 1 / (p.1 : ℝ) := by positivity
  have hdev := P.abs_deviation_le_width_of_coord_bounds j hcoord p hp
  calc
    (1 / (p.1 : ℝ)) * |P.deviation p| ≤
        (1 / (p.1 : ℝ)) * (b - a) :=
      mul_le_mul_of_nonneg_left hdev hw
    _ = (b - a) * (1 / (p.1 : ℝ)) := by ring

theorem bandVariance_le_width_sq_mul_mass_of_coord_bounds
    (j : Band) {a b : ℝ}
    (hcoord : ∀ p ∈ P.data.fiber j, tPrime n p.1 ∈ Set.Icc a b) :
    P.bandVariance j ≤ (b - a) ^ 2 * P.mass j := by
  unfold bandVariance
  change (∑ p ∈ P.data.fiber j,
      (1 / (p.1 : ℝ)) * P.deviation p ^ 2) ≤
    (b - a) ^ 2 * (∑ p ∈ P.data.fiber j, 1 / (p.1 : ℝ))
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro p hp
  have hdev := P.abs_deviation_le_width_of_coord_bounds j hcoord p hp
  have hwidth : 0 ≤ b - a := (abs_nonneg _).trans hdev
  have hsq : P.deviation p ^ 2 ≤ (b - a) ^ 2 :=
    sq_le_sq.mpr (by simpa [abs_of_nonneg hwidth] using hdev)
  calc
    (1 / (p.1 : ℝ)) * P.deviation p ^ 2 ≤
        (1 / (p.1 : ℝ)) * (b - a) ^ 2 :=
      mul_le_mul_of_nonneg_left hsq (by positivity)
    _ = (b - a) ^ 2 * (1 / (p.1 : ℝ)) := by ring

theorem bandL1_le_two_mass_mul_center (j : Band)
    (hcoordNonneg : ∀ p ∈ P.data.fiber j, 0 ≤ tPrime n p.1) :
    P.bandL1 j ≤ 2 * P.mass j * P.center j := by
  have hc0 : 0 ≤ P.center j := by
    change 0 ≤ (∑ q ∈ P.data.fiber j,
      (1 / (q.1 : ℝ)) * tPrime n q.1) / P.mass j
    exact div_nonneg (Finset.sum_nonneg fun q hq ↦
      mul_nonneg (by positivity) (hcoordNonneg q hq)) (P.data.mass_pos j).le
  have hfirst :
      (∑ p ∈ P.data.fiber j,
        (1 / (p.1 : ℝ)) * tPrime n p.1) = P.mass j * P.center j := by
    change (∑ p ∈ P.data.fiber j,
        (1 / (p.1 : ℝ)) * tPrime n p.1) =
      P.data.mass j *
        ((∑ p ∈ P.data.fiber j,
          (1 / (p.1 : ℝ)) * tPrime n p.1) / P.data.mass j)
    field_simp [ne_of_gt (P.data.mass_pos j)]
  have hmass : (∑ p ∈ P.data.fiber j, 1 / (p.1 : ℝ)) = P.mass j := rfl
  unfold bandL1
  calc
    (∑ p ∈ P.data.fiber j, (1 / (p.1 : ℝ)) * |P.deviation p|) ≤
        ∑ p ∈ P.data.fiber j,
          (1 / (p.1 : ℝ)) * (P.center j + tPrime n p.1) := by
      apply Finset.sum_le_sum
      intro p hp
      have hpj : P.band p = j :=
        (Erdos390.Lemma84.WeightedBandData.mem_fiber_iff P.data).mp hp
      rw [deviation, hpj]
      exact mul_le_mul_of_nonneg_left (abs_sub_le_iff.2
        ⟨by linarith [hcoordNonneg p hp], by linarith [hcoordNonneg p hp]⟩)
        (by positivity)
    _ = 2 * P.mass j * P.center j := by
      simp_rw [mul_add]
      rw [Finset.sum_add_distrib, ← Finset.sum_mul, hmass, hfirst]
      ring

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







theorem upper_div_lower_eq_one_add_ratio
    (hdelta : 0 < delta) (k : Fin M.cellCount) :
    M.upper k / M.lower k = 1 + M.ratio := by
  rw [show M.upper k = M.lower k * (1 + M.ratio) by
    unfold upper lower
    exact M.endpoint_succ k.1]
  field_simp [ne_of_gt (M.lower_pos hdelta k)]

theorem cellHarmonicMass_eq_log_one_add_ratio
    (hdelta : 0 < delta) (k : Fin M.cellCount) :
    M.cellHarmonicMass k = Real.log (1 + M.ratio) := by
  unfold cellHarmonicMass
  rw [M.upper_div_lower_eq_one_add_ratio hdelta k]



theorem cellHarmonicMass_le_ratio
    (hdelta : 0 < delta) (k : Fin M.cellCount) :
    M.cellHarmonicMass k ≤ M.ratio := by
  rw [M.cellHarmonicMass_eq_log_one_add_ratio hdelta k]
  have h := Real.log_le_sub_one_of_pos (by linarith [M.ratio_pos] :
    0 < 1 + M.ratio)
  linarith

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



/-- The first-moment part of the finite assembly is uniform for an
arbitrary relative-mesh upper parameter `eta`.  Unlike the variance lower
bound, it does not require `M.ratio ≤ delta`. -/
theorem actual_L1_bound_of_ready
    (hdelta : 0 < delta) (hn : 1 < n)
    (R : MomentReady M P) :
    P.totalL1 ≤ 7 * (delta + M.ratio) := by
  have hrho0 := M.ratio_pos.le
  have hlowCoord := low_coord_bounds M P E hUpper hn
  have hposCoord := positive_coord_bounds M P E hLower hUpper hn
  have hlowL1 := P.bandL1_le_two_mass_mul_center 0
    (fun p hp ↦ (hlowCoord p hp).1)
  have hposL1 (k : Fin M.cellCount) :
      P.bandL1 k.succ ≤ 3 * M.ratio * M.width k := by
    have hraw := P.bandL1_le_width_mul_mass_of_coord_bounds k.succ
      (hposCoord k)
    rw [show M.upper k - M.lower k = M.width k by rfl] at hraw
    calc
      P.bandL1 k.succ ≤ M.width k * P.mass k.succ := hraw
      _ ≤ M.width k * (3 * M.ratio) :=
        mul_le_mul_of_nonneg_left (R.positiveMass k)
          (M.width_pos hdelta k).le
      _ = 3 * M.ratio * M.width k := by ring
  rw [P.totalL1_eq_sum_bandL1, Fin.sum_univ_succ]
  calc
    P.bandL1 0 + ∑ k : Fin M.cellCount, P.bandL1 k.succ ≤
        4 * delta + ∑ k : Fin M.cellCount,
          3 * M.ratio * M.width k := by
      apply add_le_add
      · exact hlowL1.trans (by linarith [R.lowFirst])
      · exact Finset.sum_le_sum fun k hk ↦ hposL1 k
    _ = 4 * delta + 3 * M.ratio * (1 - delta) := by
      rw [← Finset.mul_sum, M.sum_width_eq_one_sub_delta]
    _ ≤ 7 * (delta + M.ratio) := by nlinarith

omit hLower in
/-- The moving low cell contributes a fixed multiple of `delta²` without
any comparison between the positive mesh ratio and `delta`. -/
theorem actual_low_bandVariance_lower_of_ready
    (hdelta : 0 < delta) (hn : 1 < n)
    (R : MomentReady M P) :
    delta ^ 2 / 4 ≤ P.bandVariance 0 := by
  have hlowCoord := low_coord_bounds M P E hUpper hn
  have hlowCenterNonneg : 0 ≤ P.center 0 :=
    (P.center_mem_of_coord_bounds 0 hlowCoord).1
  have hlowFirstNonneg : 0 ≤ P.mass 0 * P.center 0 :=
    mul_nonneg (P.data.mass_pos 0).le hlowCenterNonneg
  have hcenterTerm : P.mass 0 * P.center 0 ^ 2 ≤ delta ^ 2 / 12 := by
    have hmassPos := P.data.mass_pos 0
    have hidentity : P.mass 0 * P.center 0 ^ 2 =
        (P.mass 0 * P.center 0) ^ 2 / P.mass 0 := by
      field_simp [ne_of_gt hmassPos]
    rw [hidentity, div_le_iff₀ hmassPos]
    have hfirstSq : (P.mass 0 * P.center 0) ^ 2 ≤ (2 * delta) ^ 2 :=
      (sq_le_sq₀ hlowFirstNonneg (by positivity)).2 R.lowFirst
    have hright : (2 * delta) ^ 2 ≤ delta ^ 2 / 12 * P.mass 0 := by
      nlinarith [R.lowMass, sq_nonneg delta]
    exact hfirstSq.trans hright
  rw [P.bandVariance_eq_second_sub_mass_center_sq]
  linarith [R.lowSecondLower, hcenterTerm]

/-- The quadratic upper bound is uniform for independent mesh parameters;
it does not use `M.ratio ≤ delta`. -/
theorem actual_variance_upper_of_ready
    (hdelta : 0 < delta) (hn : 1 < n)
    (R : MomentReady M P) :
    P.variance ≤ 4 * (delta + M.ratio) ^ 2 := by
  have hposCoord := positive_coord_bounds M P E hLower hUpper hn
  have hlowVarUpper : P.bandVariance 0 ≤ delta ^ 2 := by
    rw [P.bandVariance_eq_second_sub_mass_center_sq]
    have hterm : 0 ≤ P.mass 0 * P.center 0 ^ 2 :=
      mul_nonneg (P.data.mass_pos 0).le (sq_nonneg _)
    linarith [R.lowSecondUpper]
  have hposVar (k : Fin M.cellCount) :
      P.bandVariance k.succ ≤ 3 * M.ratio * M.width k ^ 2 := by
    have hraw := P.bandVariance_le_width_sq_mul_mass_of_coord_bounds k.succ
      (hposCoord k)
    rw [show M.upper k - M.lower k = M.width k by rfl] at hraw
    calc
      P.bandVariance k.succ ≤ M.width k ^ 2 * P.mass k.succ := hraw
      _ ≤ M.width k ^ 2 * (3 * M.ratio) :=
        mul_le_mul_of_nonneg_left (R.positiveMass k) (sq_nonneg _)
      _ = 3 * M.ratio * M.width k ^ 2 := by ring
  have hsumWidthSq :
      (∑ k : Fin M.cellCount, M.width k ^ 2) ≤ M.ratio := by
    calc
      (∑ k : Fin M.cellCount, M.width k ^ 2) ≤
          ∑ k : Fin M.cellCount, M.ratio * M.width k := by
        apply Finset.sum_le_sum
        intro k hk
        have hw0 := (M.width_pos hdelta k).le
        have hwle := M.width_le_ratio hdelta k
        nlinarith
      _ = M.ratio * (1 - delta) := by
        rw [← Finset.mul_sum, M.sum_width_eq_one_sub_delta]
      _ ≤ M.ratio := by nlinarith [M.ratio_pos]
  rw [P.variance_eq_sum_bandVariance, Fin.sum_univ_succ]
  calc
    P.bandVariance 0 + ∑ k : Fin M.cellCount, P.bandVariance k.succ ≤
        delta ^ 2 + ∑ k : Fin M.cellCount,
          3 * M.ratio * M.width k ^ 2 := by
      exact add_le_add hlowVarUpper
        (Finset.sum_le_sum fun k hk ↦ hposVar k)
    _ = delta ^ 2 + 3 * M.ratio *
        (∑ k : Fin M.cellCount, M.width k ^ 2) := by
      rw [← Finset.mul_sum]
    _ ≤ delta ^ 2 + 3 * M.ratio ^ 2 := by
      have hmul := mul_le_mul_of_nonneg_left hsumWidthSq
        (show 0 ≤ 3 * M.ratio by
          exact mul_nonneg (by norm_num) M.ratio_pos.le)
      nlinarith
    _ ≤ 4 * (delta + M.ratio) ^ 2 := by
      nlinarith [M.ratio_pos, hdelta]



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

theorem tendsto_positive_lowerCoordinate
    (hdelta : 0 < delta) (W : ℕ) (k : Fin M.cellCount) :
    Tendsto (fun n : ℕ ↦ cutoffCoordinate M n W (k.1 + 1))
      atTop (nhds (M.lower k)) := by
  simpa only [cutoffCoordinate, fullCutoff_succ,
    RegularRelativeMesh.Mesh.lower] using
      tendsto_floor_scalePoint_coordinate (M.lower_pos hdelta k)

theorem tendsto_positive_upperCoordinate
    (hdelta : 0 < delta) (W : ℕ) (k : Fin M.cellCount) :
    Tendsto (fun n : ℕ ↦ cutoffCoordinate M n W (k.1 + 2))
      atTop (nhds (M.upper k)) := by
  have hUpperPos : 0 < M.upper k :=
    (M.lower_pos hdelta k).trans (M.lower_lt_upper hdelta k)
  simpa only [cutoffCoordinate, show k.1 + 2 = (k.1 + 1) + 1 by omega,
    fullCutoff_succ, RegularRelativeMesh.Mesh.upper] using
      tendsto_floor_scalePoint_coordinate hUpperPos

theorem tendsto_low_upperCoordinate
    (hdelta : 0 < delta) (W : ℕ) :
    Tendsto (fun n : ℕ ↦ cutoffCoordinate M n W 1)
      atTop (nhds delta) := by
  simpa only [cutoffCoordinate, fullCutoff_succ, M.endpoint_zero] using
    tendsto_floor_scalePoint_coordinate hdelta







theorem tendsto_positiveContinuumMass
    (hdelta : 0 < delta) (W : ℕ) (k : Fin M.cellCount) :
    Tendsto (fun n : ℕ ↦ positiveContinuumMass M n W k) atTop
      (nhds (M.cellHarmonicMass k)) := by
  have hLower := tendsto_positive_lowerCoordinate M hdelta W k
  have hUpper := tendsto_positive_upperCoordinate M hdelta W k
  have hLogLower : Tendsto
      (fun n : ℕ ↦ Real.log (cutoffCoordinate M n W (k.1 + 1)))
      atTop (nhds (Real.log (M.lower k))) :=
    (Real.continuousAt_log (ne_of_gt (M.lower_pos hdelta k))).tendsto.comp
      hLower
  have hUpperPos : 0 < M.upper k :=
    (M.lower_pos hdelta k).trans (M.lower_lt_upper hdelta k)
  have hLogUpper : Tendsto
      (fun n : ℕ ↦ Real.log (cutoffCoordinate M n W (k.1 + 2)))
      atTop (nhds (Real.log (M.upper k))) :=
    (Real.continuousAt_log (ne_of_gt hUpperPos)).tendsto.comp hUpper
  have hDiff := hLogUpper.sub hLogLower
  simpa only [positiveContinuumMass,
    RegularRelativeMesh.Mesh.cellHarmonicMass,
    Real.log_div (ne_of_gt hUpperPos)
      (ne_of_gt (M.lower_pos hdelta k))] using hDiff

theorem tendsto_lowFirstContinuum
    (hdelta : 0 < delta) (W : ℕ) :
    Tendsto (fun n : ℕ ↦ lowFirstContinuum M n W)
      atTop (nhds delta) := by
  simpa only [lowFirstContinuum, sub_zero] using
    (tendsto_low_upperCoordinate M hdelta W).sub
      (tendsto_fixed_cutoffCoordinate_zero W)

theorem tendsto_lowSecondContinuum
    (hdelta : 0 < delta) (W : ℕ) :
    Tendsto (fun n : ℕ ↦ lowSecondContinuum M n W)
      atTop (nhds (delta ^ 2 / 2)) := by
  have hUpper := (tendsto_low_upperCoordinate M hdelta W).pow 2
  have hLower := (tendsto_fixed_cutoffCoordinate_zero W).pow 2
  have hDiff := hUpper.sub hLower
  have hDiv := hDiff.div_const (2 : ℝ)
  simpa only [lowSecondContinuum, zero_pow (by omega : 2 ≠ 0), sub_zero]
    using hDiv

theorem tendsto_positive_lowerCutoff_atTop
    (hdelta : 0 < delta) (W : ℕ) (k : Fin M.cellCount) :
    Tendsto (fun n : ℕ ↦ fullCutoff M n W (k.1 + 1))
      atTop atTop := by
  simpa only [fullCutoff_succ, RegularRelativeMesh.Mesh.lower] using
    tendsto_nat_floor_atTop.comp
      (tendsto_scalePoint_atTop (M.lower_pos hdelta k))

theorem tendsto_positive_massError_zero
    (hdelta : 0 < delta) (W : ℕ) (C : ℝ)
    (k : Fin M.cellCount) :
    Tendsto (fun n : ℕ ↦
      5 * C / Real.log (fullCutoff M n W (k.1 + 1) : ℝ) ^ 3)
      atTop (nhds 0) := by
  have hCutReal : Tendsto
      (fun n : ℕ ↦ (fullCutoff M n W (k.1 + 1) : ℝ))
      atTop atTop :=
    tendsto_natCast_atTop_atTop.comp
      (tendsto_positive_lowerCutoff_atTop M hdelta W k)
  have hLog : Tendsto
      (fun n : ℕ ↦ Real.log (fullCutoff M n W (k.1 + 1) : ℝ))
      atTop atTop := Real.tendsto_log_atTop.comp hCutReal
  have hInv : Tendsto (fun n : ℕ ↦
      (Real.log (fullCutoff M n W (k.1 + 1) : ℝ))⁻¹)
      atTop (nhds 0) := tendsto_inv_atTop_zero.comp hLog
  have hConst : Tendsto (fun _n : ℕ ↦ 5 * C) atTop (nhds (5 * C)) :=
    tendsto_const_nhds
  have hMain := hConst.mul (hInv.pow 3)
  simpa only [div_eq_mul_inv, inv_pow, mul_zero, zero_pow (by omega : 3 ≠ 0)]
    using hMain

theorem tendsto_lowFirstError_zero (C : ℝ) (W : ℕ) :
    Tendsto (fun n : ℕ ↦
      (2 * C / Real.log (W : ℝ) ^ 3 +
        C / (2 * Real.log (W : ℝ) ^ 2)) / Real.log (y n))
      atTop (nhds 0) := by
  exact tendsto_const_nhds.div_atTop tendsto_log_y_atTop

theorem tendsto_lowSecondError_zero
    (C : ℝ) {W : ℕ} (hW : 1 < W) :
    Tendsto (fun n : ℕ ↦
      3 * C / (Real.log (y n) ^ 2 * Real.log (W : ℝ)))
      atTop (nhds 0) := by
  have hInv : Tendsto (fun n : ℕ ↦ (Real.log (y n))⁻¹)
      atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp tendsto_log_y_atTop
  have hConst : Tendsto
      (fun _n : ℕ ↦ 3 * C / Real.log (W : ℝ)) atTop
      (nhds (3 * C / Real.log (W : ℝ))) := tendsto_const_nhds
  have hMain := hConst.mul (hInv.pow 2)
  have hMainZero : Tendsto (fun n : ℕ ↦
      (3 * C / Real.log (W : ℝ)) * (Real.log (y n))⁻¹ ^ 2)
      atTop (nhds 0) := by simpa using hMain
  apply hMainZero.congr'
  filter_upwards with n
  have hLogW : Real.log (W : ℝ) ≠ 0 :=
    ne_of_gt (Real.log_pos (by exact_mod_cast hW))
  field_simp [hLogW]

theorem tendsto_lowHarmonicMain_atTop
    (hdelta : 0 < delta) (W : ℕ) :
    Tendsto (fun n : ℕ ↦
      Real.log (Real.log (fullCutoff M n W 1 : ℝ)) -
        Real.log (Real.log (W : ℝ))) atTop atTop := by
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
  linarith



theorem eventually_endpointMomentBounds
    (hdelta : 0 < delta) (W : ℕ) (Cmass Cfirst Csecond : ℝ)
    (hW : 1 < W) :
    ∀ᶠ n : ℕ in atTop,
      EndpointMomentBounds M n W Cmass Cfirst Csecond := by
  have hPositiveMain : ∀ᶠ n : ℕ in atTop,
      ∀ k : Fin M.cellCount,
        positiveContinuumMass M n W k ≤ 2 * M.ratio := by
    rw [Filter.eventually_all]
    intro k
    have hT := tendsto_positiveContinuumMass M hdelta W k
    have hLimit : M.cellHarmonicMass k < 2 * M.ratio :=
      (M.cellHarmonicMass_le_ratio hdelta k).trans_lt (by
        linarith [M.ratio_pos])
    exact hT.eventually (eventually_le_nhds hLimit)
  have hPositiveError : ∀ᶠ n : ℕ in atTop,
      ∀ k : Fin M.cellCount,
        5 * Cmass / Real.log (fullCutoff M n W (k.1 + 1) : ℝ) ^ 3 ≤
          M.ratio := by
    rw [Filter.eventually_all]
    intro k
    exact (tendsto_positive_massError_zero M hdelta W Cmass k).eventually
      (eventually_le_nhds M.ratio_pos)
  have hFirstMain : ∀ᶠ n : ℕ in atTop,
      lowFirstContinuum M n W ≤ 3 * delta / 2 := by
    have hLimit : delta < 3 * delta / 2 := by linarith
    exact (tendsto_lowFirstContinuum M hdelta W).eventually
      (eventually_le_nhds hLimit)
  have hFirstError : ∀ᶠ n : ℕ in atTop,
      (2 * Cfirst / Real.log (W : ℝ) ^ 3 +
        Cfirst / (2 * Real.log (W : ℝ) ^ 2)) / Real.log (y n) ≤
          delta / 2 := by
    exact (tendsto_lowFirstError_zero Cfirst W).eventually
      (eventually_le_nhds (by linarith : (0 : ℝ) < delta / 2))
  have hSecondLower : ∀ᶠ n : ℕ in atTop,
      5 * delta ^ 2 / 12 ≤ lowSecondContinuum M n W := by
    have hStrict : 5 * delta ^ 2 / 12 < delta ^ 2 / 2 := by
      nlinarith [sq_pos_of_pos hdelta]
    exact (tendsto_lowSecondContinuum M hdelta W).eventually
      (eventually_ge_nhds hStrict)
  have hSecondUpper : ∀ᶠ n : ℕ in atTop,
      lowSecondContinuum M n W ≤ 11 * delta ^ 2 / 12 := by
    have hStrict : delta ^ 2 / 2 < 11 * delta ^ 2 / 12 := by
      nlinarith [sq_pos_of_pos hdelta]
    exact (tendsto_lowSecondContinuum M hdelta W).eventually
      (eventually_le_nhds hStrict)
  have hSecondError : ∀ᶠ n : ℕ in atTop,
      3 * Csecond / (Real.log (y n) ^ 2 * Real.log (W : ℝ)) ≤
        delta ^ 2 / 12 := by
    have hStrict : (0 : ℝ) < delta ^ 2 / 12 := by positivity
    exact (tendsto_lowSecondError_zero Csecond hW).eventually
      (eventually_le_nhds hStrict)
  have hLowMass : ∀ᶠ n : ℕ in atTop,
      48 + 5 * Cmass / Real.log (W : ℝ) ^ 3 ≤
        Real.log (Real.log (fullCutoff M n W 1 : ℝ)) -
          Real.log (Real.log (W : ℝ)) :=
    (tendsto_lowHarmonicMain_atTop M hdelta W).eventually
      (eventually_ge_atTop
        (48 + 5 * Cmass / Real.log (W : ℝ) ^ 3))
  filter_upwards [eventually_gt_atTop 1, hPositiveMain, hPositiveError,
    hFirstMain, hFirstError, hSecondLower, hSecondUpper, hSecondError,
    hLowMass] with n hn hPM hPE hFM hFE hSL hSU hSE hLM
  exact ⟨hn, hPM, hPE, hFM, hFE, hSL, hSU, hSE, hLM⟩

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



























theorem inner_nuisanceCovarianceVector [Nonempty Head]
    (xi : B.ParamSpace) (F : B.sampleData.Sample → ℝ)
    (z : B.NuisanceSpace) :
    inner ℝ z (B.nuisanceCovarianceVector xi F) =
      (B.tiltedLaw xi).covariance
        (fun m ↦ inner ℝ z (B.nuisanceStatistic m)) F := by
  rw [PiLp.inner_apply]
  change (∑ c : NuisanceCoord B.HeadIndex,
      B.nuisanceCovarianceVector xi F c * z c) = _
  rw [show (fun m ↦ inner ℝ z (B.nuisanceStatistic m)) =
      fun m ↦ ∑ c : NuisanceCoord B.HeadIndex,
        z c * B.nuisanceStatistic m c by
    funext m
    rw [PiLp.inner_apply]
    apply Finset.sum_congr rfl
    intro c hc
    rw [RCLike.inner_apply]
    simp only [starRingEnd_apply, star_trivial]
    ring]
  rw [FiniteProbability.covariance_sum_left]
  apply Finset.sum_congr rfl
  intro c hc
  rw [FiniteProbability.covariance_smul_left]
  simp only [B.nuisanceCovarianceVector_apply]
  ring





theorem nuisanceCoefficientOfScore_solve [Nonempty Head]
    (xi : B.ParamSpace) {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (F : B.sampleData.Sample → ℝ) :
    B.nuisanceCovarianceOperator xi
        (B.nuisanceCoefficientOfScore xi hgamma hgap F) =
      B.nuisanceCovarianceVector xi F := by
  rw [← B.nuisanceCovarianceEquiv_apply xi hgamma hgap]
  exact (B.nuisanceCovarianceEquiv xi hgamma hgap).apply_symm_apply _

/-- Coercivity of the literal nuisance covariance block bounds the actual
regression coefficient by the norm of its literal covariance vector. -/
theorem nuisanceCoefficientOfScore_norm_le [Nonempty Head]
    (xi : B.ParamSpace) {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (F : B.sampleData.Sample → ℝ) :
    ‖B.nuisanceCoefficientOfScore xi hgamma hgap F‖ ≤
      ‖B.nuisanceCovarianceVector xi F‖ / gamma := by
  let a := B.nuisanceCoefficientOfScore xi hgamma hgap F
  have hcoer := hgap a
  rw [B.nuisanceCoefficientOfScore_solve xi hgamma hgap F] at hcoer
  have hinner : inner ℝ a (B.nuisanceCovarianceVector xi F) ≤
      ‖a‖ * ‖B.nuisanceCovarianceVector xi F‖ :=
    real_inner_le_norm _ _
  by_cases ha : ‖a‖ = 0
  · change ‖a‖ ≤ ‖B.nuisanceCovarianceVector xi F‖ / gamma
    rw [ha]
    exact div_nonneg (norm_nonneg _) (le_of_lt hgamma)
  · have hapos : 0 < ‖a‖ :=
      lt_of_le_of_ne (norm_nonneg a) (Ne.symm ha)
    have hcancel : gamma * ‖a‖ ≤
        ‖B.nuisanceCovarianceVector xi F‖ := by
      have hmul : (gamma * ‖a‖) * ‖a‖ ≤
          ‖B.nuisanceCovarianceVector xi F‖ * ‖a‖ := by
        calc
          (gamma * ‖a‖) * ‖a‖ = gamma * ‖a‖ ^ 2 := by ring
          _ ≤ inner ℝ a (B.nuisanceCovarianceVector xi F) := hcoer
          _ ≤ ‖B.nuisanceCovarianceVector xi F‖ * ‖a‖ := by
            simpa [mul_comm] using hinner
      exact (mul_le_mul_iff_right₀ hapos).mp (by
        simpa [mul_assoc, mul_comm, mul_left_comm] using hmul)
    change ‖a‖ ≤ ‖B.nuisanceCovarianceVector xi F‖ / gamma
    exact (le_div_iff₀ hgamma).2 (by simpa [mul_comm] using hcancel)

















/-- Exact marked-row identity for an arbitrary nuisance coefficient.  The
vector on the right is the literal covariance vector of the marked score,
so a Euclidean row estimate can be used without introducing a
coordinate-counting loss. -/
theorem covariance_marked_nuisanceScore_eq_inner [Nonempty Head]
    (xi : B.ParamSpace) (F : B.sampleData.Sample → ℝ)
    (z : B.NuisanceSpace) :
    (B.tiltedLaw xi).covariance F
        (fun m ↦ inner ℝ z (B.nuisanceStatistic m)) =
      inner ℝ z (B.nuisanceCovarianceVector xi F) := by
  rw [(B.tiltedLaw xi).covariance_comm]
  exact (B.inner_nuisanceCovarianceVector xi F z).symm

/-- A coordinatewise nuisance-row estimate gives the Euclidean estimate used
in the second regression.  The only loss is the square root of the fixed
nuisance dimension.  Keeping this conversion explicit is useful in the
marked-row argument: the analytic input is naturally proved one physical or
head coordinate at a time, whereas the regression coefficient is controlled
in Euclidean norm. -/
theorem nuisanceCovarianceVector_norm_le_sqrt_card_mul [Nonempty Head]
    (xi : B.ParamSpace) (F : B.sampleData.Sample → ℝ)
    {K : ℝ} (hK : 0 ≤ K)
    (hcoord : ∀ c : NuisanceCoord B.HeadIndex,
      |(B.tiltedLaw xi).covariance
        (fun m ↦ B.nuisanceStatistic m c) F| ≤ K) :
    ‖B.nuisanceCovarianceVector xi F‖ ≤
      Real.sqrt (Fintype.card (NuisanceCoord B.HeadIndex) : ℝ) * K := by
  have hsq : ‖B.nuisanceCovarianceVector xi F‖ ^ 2 ≤
      (Fintype.card (NuisanceCoord B.HeadIndex) : ℝ) * K ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    simp only [Real.norm_eq_abs, B.nuisanceCovarianceVector_apply]
    calc
      (∑ c : NuisanceCoord B.HeadIndex,
          |(B.tiltedLaw xi).covariance
            (fun m ↦ B.nuisanceStatistic m c) F| ^ 2) ≤
          ∑ _c : NuisanceCoord B.HeadIndex, K ^ 2 := by
        apply Finset.sum_le_sum
        intro c hc
        exact pow_le_pow_left₀ (abs_nonneg _) (hcoord c) 2
      _ = (Fintype.card (NuisanceCoord B.HeadIndex) : ℝ) * K ^ 2 := by
        simp
  have hcard : 0 ≤
      (Fintype.card (NuisanceCoord B.HeadIndex) : ℝ) := by positivity
  have hsqrt :
      (Real.sqrt (Fintype.card (NuisanceCoord B.HeadIndex) : ℝ)) ^ 2 =
        (Fintype.card (NuisanceCoord B.HeadIndex) : ℝ) :=
    Real.sq_sqrt hcard
  have hrhs0 : 0 ≤
      Real.sqrt (Fintype.card (NuisanceCoord B.HeadIndex) : ℝ) * K :=
    mul_nonneg (Real.sqrt_nonneg _) hK
  have hrhsSq :
      (Real.sqrt (Fintype.card (NuisanceCoord B.HeadIndex) : ℝ) * K) ^ 2 =
        (Fintype.card (NuisanceCoord B.HeadIndex) : ℝ) * K ^ 2 := by
    rw [mul_pow, hsqrt]
  rw [← hrhsSq] at hsq
  nlinarith [norm_nonneg (B.nuisanceCovarianceVector xi F)]











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



















theorem normalizedBandCovarianceRow_sub [Nonempty Head]
    (xi : B.ParamSpace) (F G : B.sampleData.Sample → ℝ) :
    B.normalizedBandCovarianceRow xi (fun m ↦ F m - G m) =
      B.normalizedBandCovarianceRow xi F -
        B.normalizedBandCovarianceRow xi G := by
  have hsub : (fun m ↦ F m - G m) =
      fun m ↦ F m + (-1 : ℝ) * G m := by
    funext m
    ring
  rw [hsub, B.normalizedBandCovarianceRow_add,
    B.normalizedBandCovarianceRow_smul]
  funext j
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply,
    smul_eq_mul]
  ring



























































end BridgeData

end

end Erdos390.Full.PaperBridgeFit

end

/- Source module: Erdos390.Full.PaperActualSchurMarkedRow -/
section


/-!
# Attaching reciprocal nuisance marked rows to the actual Schur operator

This file performs the finite summations that turn a coordinatewise bound
`|Cov(Z_c,v_p)| <= Cmarked / p` into the two covariance-vector bounds used
by the exact Schur perturbation theorem.  The analytic rate remains a
literal hypothesis; in particular the proof does not replace the required
`O(1/(pL))` estimate by a merely bounded `O(1/p)` row.
-/

open scoped BigOperators

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

open ArithmeticBandGeometry PaperWeightedInverseExport

namespace BridgeData

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]
  (B : BridgeData Head Band)

/-- Summing a reciprocal marked-prime estimate over one literal band gives
exactly its harmonic mass. -/
theorem abs_covariance_nuisance_bandScore_le_of_marked
    [Nonempty Head]
    (xi : B.ParamSpace) (c : NuisanceCoord B.HeadIndex) (i : Band)
    {Cmarked : ℝ}
    (hmarked : ∀ p : BandPrime B.sampleData.n B.sampleData.W,
      |(B.tiltedLaw xi).covariance
        (fun m ↦ B.nuisanceStatistic m c)
        (fun m ↦ ArithmeticModel.valuation p.1
          (B.sampleData.value m))| ≤
        Cmarked * (1 / (p.1 : ℝ))) :
    |(B.tiltedLaw xi).covariance
      (fun m ↦ B.nuisanceStatistic m c) (B.bandScore i)| ≤
        Cmarked * B.harmonicMass i := by
  let mu := B.tiltedLaw xi
  let Z : B.sampleData.Sample → ℝ :=
    fun m ↦ B.nuisanceStatistic m c
  have hsum :
      mu.covariance Z (B.bandScore i) =
        ∑ p ∈ B.partition.data.fiber i,
          mu.covariance Z
            (fun m ↦ ArithmeticModel.valuation p.1
              (B.sampleData.value m)) := by
    unfold bandScore
    rw [mu.covariance_sum_right]
  change |mu.covariance Z (B.bandScore i)| ≤ _
  rw [hsum]
  calc
    |∑ p ∈ B.partition.data.fiber i,
        mu.covariance Z
          (fun m ↦ ArithmeticModel.valuation p.1
            (B.sampleData.value m))| ≤
        ∑ p ∈ B.partition.data.fiber i,
          |mu.covariance Z
            (fun m ↦ ArithmeticModel.valuation p.1
              (B.sampleData.value m))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ p ∈ B.partition.data.fiber i,
        Cmarked * (1 / (p.1 : ℝ)) := by
      apply Finset.sum_le_sum
      intro p hp
      exact hmarked p
    _ = Cmarked * B.harmonicMass i := by
      change (∑ p ∈ B.partition.data.fiber i,
        Cmarked * (1 / (p.1 : ℝ))) =
          Cmarked * ∑ p ∈ B.partition.data.fiber i,
            (1 / (p.1 : ℝ))
      rw [Finset.mul_sum]

/-- Euclidean vector form of the preceding one-band summation. -/
theorem nuisanceCovarianceVector_bandScore_norm_le_of_marked
    [Nonempty Head]
    (xi : B.ParamSpace) (i : Band)
    {Cmarked : ℝ} (hCmarked : 0 ≤ Cmarked)
    (hmarked : ∀ (c : NuisanceCoord B.HeadIndex)
      (p : BandPrime B.sampleData.n B.sampleData.W),
      |(B.tiltedLaw xi).covariance
        (fun m ↦ B.nuisanceStatistic m c)
        (fun m ↦ ArithmeticModel.valuation p.1
          (B.sampleData.value m))| ≤
        Cmarked * (1 / (p.1 : ℝ))) :
    ‖B.nuisanceCovarianceVector xi (B.bandScore i)‖ ≤
      Real.sqrt (Fintype.card (NuisanceCoord B.HeadIndex) : ℝ) *
        (Cmarked * B.harmonicMass i) := by
  have hK : 0 ≤ Cmarked * B.harmonicMass i :=
    mul_nonneg hCmarked (B.harmonicMass_pos i).le
  exact B.nuisanceCovarianceVector_norm_le_sqrt_card_mul
    xi (B.bandScore i) hK (fun c ↦
      B.abs_covariance_nuisance_bandScore_le_of_marked
        xi c i (fun p ↦ hmarked c p))















end BridgeData

end

end Erdos390.Full.PaperBridgeFit

end

/- Source module: Erdos390.Full.CanonicalEndpointCenterEnvelopeEventually -/
section


/-!
# The canonical moving-low centre has the sharp reciprocal envelope

This file records the quantitative fact needed when an `o(1)` prime-profile
error is divided by the centre of the moving low cell.  The loss is exactly
`O(log log n)`: uniformly in every proof of scale separation and in every
canonical band,

`1 / center i <= C * log (log n)`.

The proof does not identify the low centre with a fixed continuum centre.
It uses the already proved *relative* endpoint-centre convergence, the
literal endpoint continuum first moment, and an elementary upper bound for
the literal endpoint continuum harmonic mass.  Thus it remains valid for the
moving low endpoint and has the quantifier order required in Sections 8.4--8.6.
-/

open Filter Topology

noncomputable section

namespace Erdos390.Full.RegularMeshPrimeCutoffs

open ArithmeticModel ArithmeticBandGeometry RegularRelativeMesh
open PositiveCellTransfer PrimeBandQuadrature MovingLowMomentQuadrature
open MovingLowGaugeTransfer KernelPrimeQuadrature

/- A mesh-independent cutoff for the sharp moving-low centre envelope. -/




theorem canonicalCenterEnvelopeConstant_pos {delta : ℝ} (hdelta : 0 < delta) :
    0 < canonicalCenterEnvelopeConstant delta :=
  div_pos (by norm_num) hdelta

namespace Mesh

variable {delta eta : ℝ} (M : Mesh delta eta)







/-- Exact all-band lower form with the same global cutoff. -/
theorem canonicalCenterEnvelopeCutoff_eventually_lower
    (hdelta : 0 < delta) (W : ℕ)
    (hW : canonicalCenterEnvelopeCutoff ≤ W) :
    ∀ᶠ n : ℕ in atTop, ∀ (hn : 1 < n) (hWne : W ≠ 0)
      (S : ScaleSeparation M n W) (i : Fin (M.cellCount + 1)),
      (1 / canonicalCenterEnvelopeConstant delta) /
          Real.log (Scale.L n) ≤
        (canonicalPartition M hdelta hn hWne S).center i := by
  have hCalpha := canonicalCenterEnvelopeConstant_pos hdelta
  have hmain := canonicalCenterEnvelopeCutoff_eventually_inverse M hdelta W hW
  have hLTop : Tendsto Scale.L atTop atTop := by
    simpa only [Scale.L] using
      Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hLogLTop : Tendsto (fun n : ℕ ↦ Real.log (Scale.L n))
      atTop atTop := Real.tendsto_log_atTop.comp hLTop
  have hLogL := hLogLTop.eventually (eventually_gt_atTop (0 : ℝ))
  filter_upwards [hmain, hLogL] with n hinv hlog
  intro hn hWne S i
  let P := canonicalPartition M hdelta hn hWne S
  have hcenter : 0 < P.center i := P.center_pos hn i
  have hprod : 1 ≤
      (canonicalCenterEnvelopeConstant delta * Real.log (Scale.L n)) *
        P.center i :=
    (div_le_iff₀ hcenter).mp (hinv hn hWne S i)
  have hquot :
      1 / (canonicalCenterEnvelopeConstant delta * Real.log (Scale.L n)) ≤
        P.center i :=
    (div_le_iff₀ (mul_pos hCalpha hlog)).mpr (by
      simpa only [mul_comm] using hprod)
  change (1 / canonicalCenterEnvelopeConstant delta) /
      Real.log (Scale.L n) ≤ P.center i
  convert hquot using 1
  field_simp [hCalpha.ne', hlog.ne']





end Mesh
end Erdos390.Full.RegularMeshPrimeCutoffs

end

/- Source module: Erdos390.Full.PaperBridgeBaselineL1 -/
section


/-!
# Uniform baseline-to-actual `L¹` control for the paper bridge

The nuisance covariance argument in Lemma 8.4 needs the *actual* tilted
finite law to remain close to the actual finite baseline law throughout a
fixed effective parameter box.  The medium-prime score is not uniformly
small pointwise, so this cannot be proved by a sup-norm estimate alone.

This file proves the needed finite statement from literal arithmetic-cell
data.  A positive cell-density bound gives an `O(sum_{W<p<=y} 1/p / L)`
first absolute moment for the medium valuation score.  The fixed-dimensional
nuisance score contributes `O(1/L)`.  A fixed pointwise score envelope then
converts that first-moment estimate to normalized `L¹` distance.
-/

open scoped BigOperators

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

open ArithmeticModel ArithmeticBandGeometry FiniteProbability
open ValuationScoreDomination DivisibilityMomentBounds
open Erdos390.Full.OmittedScoreCell
open Erdos390.Full.PrimeSums

namespace BridgeData

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]
  (B : BridgeData Head Band)











/-! ## Fixed-interval/effective-box specialization -/



/-- A paper-effective ball directly supplies both coefficient bounds used by
the finite `L¹` theorem. -/
theorem effective_bounds_of_paperEffectiveSize
    (xi : B.ParamSpace) {A : ℝ}
    (hbox : B.paperEffectiveSize xi ≤ A) :
    (∀ p : BandPrime B.sampleData.n B.sampleData.W,
      |B.effectivePrimeCoefficient xi p| ≤ A) ∧
      ‖B.nuisanceParameter xi‖ ≤ A := by
  have hprimeNorm :
      ‖fun p ↦ B.effectivePrimeCoefficient xi p‖ ≤
        B.paperEffectiveSize xi := by
    unfold paperEffectiveSize
    linarith [norm_nonneg (B.nuisanceParameter xi),
      abs_nonneg (xi MomentCoord.slow)]
  have hnuisance : ‖B.nuisanceParameter xi‖ ≤
      B.paperEffectiveSize xi := by
    unfold paperEffectiveSize
    linarith [norm_nonneg
      (fun p ↦ B.effectivePrimeCoefficient xi p),
      abs_nonneg (xi MomentCoord.slow)]
  constructor
  · intro p
    calc
      |B.effectivePrimeCoefficient xi p| ≤
          ‖fun q ↦ B.effectivePrimeCoefficient xi q‖ := by
        simpa only [Real.norm_eq_abs] using
          norm_le_pi_norm
            (fun q ↦ B.effectivePrimeCoefficient xi q) p
      _ ≤ B.paperEffectiveSize xi := hprimeNorm
      _ ≤ A := hbox
  · exact hnuisance.trans hbox







end BridgeData

end

end Erdos390.Full.PaperBridgeFit

end

/- Source module: Erdos390.Full.PaperCanonicalNuisanceUniformFloor -/
section


/-!
# A root uniform lower floor for the canonical nuisance gap

The exact canonical nuisance gap is allowed to use a varying reference head
and a varying positive barycentric target.  This file bounds its two finite
dimensional constants by quantities depending only on the fixed head type,
and replaces the varying cell-mass margin by one prescribed positive floor.
The result is the uniform positive scalar needed before taking an eventual
Schur-smallness threshold.
-/

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

open ArithmeticModel PaperGuardCensus









namespace BridgeData

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]
  (B : BridgeData Head Band)

/-- The actual nuisance coordinate count is bounded by the full head count
plus the physical coordinate. -/
theorem nuisanceCoord_card_le_head_add_one :
    Fintype.card (NuisanceCoord B.HeadIndex) ≤ Fintype.card Head + 1 := by
  let f : NuisanceCoord B.HeadIndex → Option Head
    | .physical => none
    | .head h => some h.1
  have hf : Function.Injective f := by
    intro x y hxy
    cases x <;> cases y <;> simp_all [f, Subtype.ext_iff]
  simpa using Fintype.card_le_of_injective f hf

theorem sqrt_nuisanceCoord_card_le_ceiling :
    Real.sqrt (Fintype.card (NuisanceCoord B.HeadIndex) : ℝ) ≤
      nuisanceDimensionCeiling Head := by
  unfold nuisanceDimensionCeiling
  apply Real.sqrt_le_sqrt
  exact_mod_cast B.nuisanceCoord_card_le_head_add_one

theorem nuisanceStatisticCoefficient_le_ceiling
    {U : ℝ} (hU : 1 ≤ U) :
    B.nuisanceStatisticCoefficient U ≤
      nuisanceStatisticCoefficientCeiling Head U := by
  unfold nuisanceStatisticCoefficient nuisanceStatisticCoefficientCeiling
  have hmax : 0 ≤ max (PaperStatisticNorm.physicalLogCoefficient U)
      (3 / Real.log 2) := by
    exact (PaperStatisticNorm.physicalLogCoefficient_nonneg hU).trans
      (le_max_left _ _)
  exact mul_le_mul_of_nonneg_right
    B.sqrt_nuisanceCoord_card_le_ceiling hmax

theorem nuisanceGeometryConstant_le_ceiling (sep R : ℝ) :
    B.nuisanceGeometryConstant sep R ≤
      nuisanceGeometryCeiling Head sep R := by
  unfold nuisanceGeometryConstant nuisanceGeometryCeiling
  have hcard : (Fintype.card B.HeadIndex : ℝ) ≤
      (Fintype.card Head : ℝ) := by
    exact_mod_cast Fintype.card_le_of_injective
      (fun h : B.HeadIndex ↦ h.1) (fun _ _ h ↦ Subtype.ext h)
  have hfactor : 0 ≤ 8 * R ^ 2 := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hcard hfactor]

omit [DecidableEq Head] in
theorem canonicalEffectiveNuisanceGammaFloor_pos
    (I : PhysicalIntervals) {U a marginFloor : ℝ} {W : ℕ}
    (hmargin : 0 < marginFloor) :
    0 < canonicalEffectiveNuisanceGammaFloor Head I U a W marginFloor := by
  unfold canonicalEffectiveNuisanceGammaFloor
  have hsep := fixedInterval_separation_pos I
  have hgeom : 0 < nuisanceGeometryCeiling Head
      (Real.log (I.lower .plus) - Real.log (I.upper .minus))
      (Real.log U) := by
    unfold nuisanceGeometryCeiling
    positivity
  exact mul_pos (Real.exp_pos _)
    (div_pos (mul_pos (sq_pos_of_pos hmargin) (sq_pos_of_pos hsep))
      (mul_pos (by norm_num) hgeom))

/-- Every target with the prescribed cell-mass floor has a canonical
nuisance gap bounded below by the preceding root scalar. -/
theorem canonicalEffectiveNuisanceGammaFloor_le
    [Nonempty Head]
    (I : PhysicalIntervals) {U a marginFloor : ℝ}
    (hU : 1 ≤ U) (ha : 0 ≤ a) (hmargin : 0 < marginFloor)
    (T : BarycentricTarget B.sampleData)
    (hTmargin : marginFloor ≤ T.cellMassMargin) :
    canonicalEffectiveNuisanceGammaFloor Head I U a B.sampleData.W
        marginFloor ≤
      B.canonicalEffectiveNuisanceGamma I U a T := by
  let sep : ℝ := Real.log (I.lower .plus) - Real.log (I.upper .minus)
  let R : ℝ := Real.log U
  let Kactual : ℝ :=
    PaperStatisticNorm.valuationLogCoefficient U B.sampleData.W +
      B.nuisanceStatisticCoefficient U
  let Kceiling : ℝ :=
    PaperStatisticNorm.valuationLogCoefficient U B.sampleData.W +
      nuisanceStatisticCoefficientCeiling Head U
  have hK : Kactual ≤ Kceiling := by
    dsimp only [Kactual, Kceiling]
    linarith [B.nuisanceStatisticCoefficient_le_ceiling hU]
  have hKa : Kactual * a ≤ Kceiling * a :=
    mul_le_mul_of_nonneg_right hK ha
  have hexp : Real.exp (-2 * (Kceiling * a)) ≤
      Real.exp (-2 * (Kactual * a)) := by
    exact Real.exp_le_exp.mpr (by nlinarith)
  have hsep : 0 < sep := fixedInterval_separation_pos I
  have hTpos : 0 < T.cellMassMargin := T.cellMassMargin_pos
  have hmarginSq : marginFloor ^ 2 ≤ T.cellMassMargin ^ 2 :=
    (sq_le_sq₀ hmargin.le hTpos.le).2 hTmargin
  have hnum : marginFloor ^ 2 * sep ^ 2 ≤
      T.cellMassMargin ^ 2 * sep ^ 2 :=
    mul_le_mul_of_nonneg_right hmarginSq (sq_nonneg sep)
  have hgeomActual : 0 < B.nuisanceGeometryConstant sep R :=
    B.nuisanceGeometryConstant_pos sep R
  have hgeomCeiling : 0 < nuisanceGeometryCeiling Head sep R := by
    unfold nuisanceGeometryCeiling
    positivity
  have hgeomLe : B.nuisanceGeometryConstant sep R ≤
      nuisanceGeometryCeiling Head sep R :=
    B.nuisanceGeometryConstant_le_ceiling sep R
  have hgap :
      marginFloor ^ 2 * sep ^ 2 /
          (2 * nuisanceGeometryCeiling Head sep R) ≤
        B.uniformNuisanceGap T.cellMassMargin sep R := by
    unfold uniformNuisanceGap
    exact div_le_div₀
      (mul_nonneg (sq_nonneg T.cellMassMargin) (sq_nonneg sep)) hnum
      (mul_pos (by norm_num) hgeomActual)
      (mul_le_mul_of_nonneg_left hgeomLe (by norm_num))
  have hexp0 : 0 ≤ Real.exp (-2 * (Kceiling * a)) :=
    (Real.exp_pos _).le
  have hgap0 : 0 ≤ B.uniformNuisanceGap T.cellMassMargin sep R := by
    unfold uniformNuisanceGap
    positivity
  have hfloorGap0 : 0 ≤
      marginFloor ^ 2 * sep ^ 2 /
        (2 * nuisanceGeometryCeiling Head sep R) := by positivity
  unfold canonicalEffectiveNuisanceGammaFloor canonicalEffectiveNuisanceGamma
  dsimp only [sep, R, Kactual, Kceiling] at hexp hgap ⊢
  exact mul_le_mul hexp hgap hfloorGap0 (Real.exp_pos _).le

end BridgeData

end

end Erdos390.Full.PaperBridgeFit

end

/- Source module: Erdos390.Full.PaperActualSlowRightRowFinite -/
section


/-!
# Exact finite reference estimate for the slow right row

This file isolates the moving-low-cell estimate which is easy to lose if
one bounds the Dickman diagonal by an absolute constant.  The arithmetic
deviation is centred on every actual prime fiber.  We therefore subtract
`F (alpha_i)` in the diagonal term before estimating it.  The resulting
bound retains the factor `alpha_i`, including on the low cell where
`alpha_i` tends to zero.
-/

open scoped BigOperators

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

open ArithmeticModel ArithmeticBandGeometry
open SquarefreeSharpBandTransfer SquarefreeCovarianceReference
open SquarefreeReferenceOperatorIdentification
open PrimeSquarefreeDirichletGeometry
open FiniteAnchoredDirichletQuadratic
open ConditionedPoissonLimit DickmanBasic

namespace PaperActualSlowRightRowFinite

/-- A uniform Lipschitz constant for the Dickman diagonal profile on the
closed unit interval.  This is extracted from the already proved
differentiability and continuity of `F`; it is independent of every mesh,
cutoff, ambient integer, and tilt box. -/
theorem exists_F_lipschitz_unit :
    ∃ CF : ℝ, 0 < CF ∧ ∀ s ∈ Set.Icc (0 : ℝ) 1,
      ∀ t ∈ Set.Icc (0 : ℝ) 1,
        |F s - F t| ≤ CF * |s - t| := by
  have hcontinuous : ContinuousOn (fun x : ℝ => ‖deriv F x‖)
      (Set.Icc (0 : ℝ) 1) := by
    exact (continuousOn_deriv_F.mono (Set.Icc_subset_Icc_right
      (by norm_num : (1 : ℝ) ≤ 2))).norm
  obtain ⟨x, hx, hmax⟩ := isCompact_Icc.exists_isMaxOn
    (Set.nonempty_Icc.mpr (by norm_num : (0 : ℝ) ≤ 1)) hcontinuous
  let CF : ℝ := 1 + ‖deriv F x‖
  have hCF : 0 < CF := by
    dsimp only [CF]
    positivity
  refine ⟨CF, hCF, ?_⟩
  intro s hs t ht
  have hderiv (u : ℝ) (hu : u ∈ Set.Icc (0 : ℝ) 1) :
      ‖deriv F u‖ ≤ CF := by
    dsimp only [CF]
    exact (hmax hu).trans (le_add_of_nonneg_left (by norm_num))
  have hbound := Convex.norm_image_sub_le_of_norm_deriv_le
    (f := F) (C := CF)
    (fun u hu => differentiableAt_F
      ⟨hu.1, hu.2.trans (by norm_num)⟩)
    hderiv (convex_Icc (0 : ℝ) 1) ht hs
  simpa only [Real.norm_eq_abs] using hbound

end PaperActualSlowRightRowFinite

namespace BridgeData

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]
  (B : BridgeData Head Band)



end BridgeData

end

end Erdos390.Full.PaperBridgeFit

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





theorem canonicalSecondMomentBound
    (z : ℝ) (hz : 1 < z) (A Y : ℕ)
    (hA : canonicalSecondMomentCutoff ≤ A) (hAY : A ≤ Y) :
    |KernelPrimeQuadrature.fullWeightedReciprocalSum
          PrimeCoordinateSecondMoment.squareCoordinate z Y -
        KernelPrimeQuadrature.fullWeightedReciprocalSum
          PrimeCoordinateSecondMoment.squareCoordinate z A -
        ((realLogCoordinate z (Y : ℝ) ^ 2 -
          realLogCoordinate z (A : ℝ) ^ 2) / 2)| ≤
      3 * canonicalSecondMomentConstant /
        (Real.log z ^ 2 * Real.log (A : ℝ)) :=
  (Classical.choose_spec
    (Classical.choose_spec
      PrimeCoordinateSecondMoment.exists_uniform_squarePrimeCell_error_bound).2)
    z hz A Y hA hAY



namespace Mesh

section DiagonalMomentMesh

variable {delta : ℝ} (M : Mesh delta delta)





end DiagonalMomentMesh

section GenericFirstMomentMesh

variable {delta eta : ℝ} (M : Mesh delta eta)

/-- The deviation, first-moment, and variance-upper estimates are uniform
for independent mesh parameters `delta` and `eta`.  No variance lower bound,
and hence no comparison `M.ratio ≤ delta`, is used here. -/
theorem canonicalActualPreliminaryMomentCutoff_eventually
    (hdelta : 0 < delta) :
    ∀ W : ℕ, canonicalActualMomentCutoff ≤ W →
      ∀ᶠ n : ℕ in atTop,
        ∃ hWne : W ≠ 0, ∃ hn : 1 < n,
          ∀ S : ScaleSeparation M n W,
            let P := canonicalPartition M hdelta hn hWne S
            (∀ p : BandPrime n W,
              |P.deviation p| ≤ delta + M.ratio) ∧
            P.totalL1 ≤ 7 * (delta + M.ratio) ∧
            delta ^ 2 / 4 ≤ P.bandVariance 0 ∧
            P.variance ≤ 4 * (delta + M.ratio) ^ 2 := by
  let Cmass : ℝ := canonicalMassQuadratureConstant
  let Xmass : ℕ := canonicalMassQuadratureCutoff
  let Cfirst : ℝ :=
    MovingLowMomentQuadrature.fullLogReciprocalSumUniformConstant
  let Xfirst : ℕ :=
    MovingLowMomentQuadrature.fullLogReciprocalSumUniformCutoff
  let Csecond : ℝ := canonicalSecondMomentConstant
  let Xsecond : ℕ := canonicalSecondMomentCutoff
  have hMass : ∀ A Y : ℕ, Xmass ≤ A → A ≤ Y →
      |PrimeSums.fullReciprocalSum Y - PrimeSums.fullReciprocalSum A -
          (Real.log (Real.log (Y : ℝ)) -
            Real.log (Real.log (A : ℝ)))| ≤
        5 * Cmass / Real.log (A : ℝ) ^ 3 := by
    intro A Y hA hAY
    simpa only [Cmass, Xmass] using
      canonicalMassQuadratureBound A Y hA hAY
  have hFirst : ∀ A Y : ℕ, Xfirst ≤ A → A ≤ Y →
      |PrimeSums.fullLogReciprocalSum Y -
          PrimeSums.fullLogReciprocalSum A -
          (Real.log (Y : ℝ) - Real.log (A : ℝ))| ≤
        2 * Cfirst / Real.log (A : ℝ) ^ 3 +
          Cfirst / (2 * Real.log (A : ℝ) ^ 2) := by
    intro A Y hA hAY
    simpa only [Cfirst, Xfirst] using
      MovingLowMomentQuadrature.fullLogReciprocalSumUniform_bound A Y hA hAY
  have hSecond : ∀ z : ℝ, 1 < z → ∀ A Y : ℕ,
      Xsecond ≤ A → A ≤ Y →
      |KernelPrimeQuadrature.fullWeightedReciprocalSum
            PrimeCoordinateSecondMoment.squareCoordinate z Y -
          KernelPrimeQuadrature.fullWeightedReciprocalSum
            PrimeCoordinateSecondMoment.squareCoordinate z A -
          ((realLogCoordinate z (Y : ℝ) ^ 2 -
            realLogCoordinate z (A : ℝ) ^ 2) / 2)| ≤
        3 * Csecond / (Real.log z ^ 2 * Real.log (A : ℝ)) := by
    intro z hz A Y hA hAY
    simpa only [Csecond, Xsecond] using
      canonicalSecondMomentBound z hz A Y hA hAY
  intro W hW
  have hW8 : 8 ≤ W :=
    (le_max_left 8 (max Xmass (max Xfirst Xsecond))).trans hW
  have hXmass : Xmass ≤ W :=
    ((le_max_left Xmass (max Xfirst Xsecond)).trans
      (le_max_right 8 (max Xmass (max Xfirst Xsecond)))).trans hW
  have hXfirst : Xfirst ≤ W :=
    ((le_max_left Xfirst Xsecond).trans
      ((le_max_right Xmass (max Xfirst Xsecond)).trans
        (le_max_right 8 (max Xmass (max Xfirst Xsecond))))).trans hW
  have hXsecond : Xsecond ≤ W :=
    ((le_max_right Xfirst Xsecond).trans
      ((le_max_right Xmass (max Xfirst Xsecond)).trans
        (le_max_right 8 (max Xmass (max Xfirst Xsecond))))).trans hW
  have hWne : W ≠ 0 := by omega
  have hEndpoint := eventually_endpointMomentBounds M hdelta W
    Cmass Cfirst Csecond (by omega : 1 < W)
  filter_upwards [hEndpoint] with n R
  let hn : 1 < n := R.n_gt_one
  refine ⟨hWne, hn, ?_⟩
  intro S
  let P := canonicalPartition M hdelta hn hWne S
  let E := canonicalCertificate M hdelta hn hWne S
  have hReady := momentReady_of_endpointMomentBounds M P E
    (fun j ↦ rfl) (fun j ↦ rfl) hW8 hXmass hXfirst hXsecond
      hMass hFirst hSecond R
  have hL1 := actual_L1_bound_of_ready M P E
    (fun j ↦ rfl) (fun j ↦ rfl) hdelta hn hReady
  have hVarUpper := actual_variance_upper_of_ready M P E
    (fun j ↦ rfl) (fun j ↦ rfl) hdelta hn hReady
  have hLow := actual_low_bandVariance_lower_of_ready M P E
    (fun j ↦ rfl) hdelta hn hReady
  have hSup := actual_deviation_sup_le_scale M P E
    (fun j ↦ rfl) (fun j ↦ rfl) hdelta hn
  exact ⟨hSup, hL1, hLow, hVarUpper⟩

/-- Generic actual-scale upper-moment interface. -/
theorem canonicalActualUpperMomentCutoff_eventually
    (hdelta : 0 < delta) :
    ∀ W : ℕ, canonicalActualMomentCutoff ≤ W →
      ∀ᶠ n : ℕ in atTop,
        ∃ hWne : W ≠ 0, ∃ hn : 1 < n,
          ∀ S : ScaleSeparation M n W,
            let P := canonicalPartition M hdelta hn hWne S
            (∀ p : BandPrime n W,
              |P.deviation p| ≤ delta + M.ratio) ∧
            P.totalL1 ≤ 7 * (delta + M.ratio) ∧
            P.variance ≤ 4 * (delta + M.ratio) ^ 2 := by
  intro W hW
  have hPreliminary :=
    canonicalActualPreliminaryMomentCutoff_eventually M hdelta W hW
  filter_upwards [hPreliminary] with n hAt
  obtain ⟨hWne, hn, hAll⟩ := hAt
  refine ⟨hWne, hn, ?_⟩
  intro S
  obtain ⟨hSup, hL1, _hLow, hVarUpper⟩ := hAll S
  exact ⟨hSup, hL1, hVarUpper⟩

/-- The smaller first-moment interface retained for the prime-graph
reference argument. -/
theorem canonicalActualFirstMomentCutoff_eventually
    (hdelta : 0 < delta) :
    ∀ W : ℕ, canonicalActualMomentCutoff ≤ W →
      ∀ᶠ n : ℕ in atTop,
        ∃ hWne : W ≠ 0, ∃ hn : 1 < n,
          ∀ S : ScaleSeparation M n W,
            let P := canonicalPartition M hdelta hn hWne S
            (∀ p : BandPrime n W,
              |P.deviation p| ≤ delta + M.ratio) ∧
            P.totalL1 ≤ 7 * (delta + M.ratio) := by
  intro W hW
  have hUpper := canonicalActualUpperMomentCutoff_eventually M hdelta W hW
  filter_upwards [hUpper] with n hAt
  obtain ⟨hWne, hn, hAll⟩ := hAt
  refine ⟨hWne, hn, ?_⟩
  intro S
  obtain ⟨hSup, hL1, _hVarUpper⟩ := hAll S
  exact ⟨hSup, hL1⟩





end GenericFirstMomentMesh

section DiagonalMesh

variable {delta : ℝ} (M : Mesh delta delta)





end DiagonalMesh

end Mesh
end Erdos390.Full.RegularMeshPrimeCutoffs

end

/- Source module: Erdos390.Full.PaperSelectedMeshSchurRateEventually -/
section


/-!
# Vanishing nuisance-Schur rate at the moving-low scale

This file isolates the rate calculation needed after the selected-mesh
full-band inverse.  A reciprocal nuisance row of size `epsilon n / p`,
with both `epsilon n -> 0` and `epsilon n * log (log n) -> 0`, survives the
moving-low loss `amin = c / log (log n)`: the resulting Schur perturbation
still tends to zero.  All dimension, moment, and nuisance-gap constants are
explicit.
-/

open scoped BigOperators
open Filter Topology Metric Set

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

namespace BridgeData

open ArithmeticBandGeometry PaperWeightedInverseExport MovingLowGaugeTransfer

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]





/-- A nonnegative row rate whose product with `log (log n)` tends to zero
already tends to zero.  This small lemma lets the analytic marked-row API
expose only its genuinely sharp rate. -/
theorem tendsto_zero_of_nonneg_mul_logL_zero
    (epsilon : ℕ → ℝ)
    (hepsilonNonneg : ∀ n, 0 ≤ epsilon n)
    (hepsilonRate : Tendsto
      (fun n : ℕ ↦ epsilon n * Real.log (Scale.L n))
        atTop (nhds 0)) :
    Tendsto epsilon atTop (nhds 0) := by
  have hLTop : Tendsto Scale.L atTop atTop := by
    simpa only [Scale.L] using
      Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hlogOne : ∀ᶠ n : ℕ in atTop,
      1 ≤ Real.log (Scale.L n) :=
    (Real.tendsto_log_atTop.comp hLTop).eventually
      (eventually_ge_atTop (1 : ℝ))
  have hlower : ∀ᶠ n : ℕ in atTop, 0 ≤ epsilon n :=
    Filter.Eventually.of_forall hepsilonNonneg
  have hupper : ∀ᶠ n : ℕ in atTop,
      epsilon n ≤ epsilon n * Real.log (Scale.L n) := by
    filter_upwards [hlogOne] with n hn
    simpa only [mul_one] using
      mul_le_mul_of_nonneg_left hn (hepsilonNonneg n)
  exact squeeze_zero' hlower hupper hepsilonRate

/-- The moving-low loss is harmless at the sharp marked-row rate. -/
theorem tendsto_selectedMeshSchurRateMajorant_zero
    (epsilon : ℕ → ℝ) {droot momentBound gammaFloor centerScale : ℝ}
    (hepsilon : Tendsto epsilon atTop (nhds 0))
    (hepsilonRate : Tendsto
      (fun n : ℕ ↦ epsilon n * Real.log (Scale.L n))
        atTop (nhds 0))
    (hgamma : 0 < gammaFloor) (hcenter : 0 < centerScale) :
    Tendsto
      (selectedMeshSchurRateMajorant epsilon droot momentBound
        gammaFloor centerScale) atTop (nhds 0) := by
  have hproduct : Tendsto (fun n : ℕ ↦
      (epsilon n * Real.log (Scale.L n)) * epsilon n)
      atTop (nhds 0) := by
    simpa only [zero_mul] using hepsilonRate.mul hepsilon
  let C : ℝ := droot ^ 2 * momentBound / (gammaFloor * centerScale)
  have hscaled : Tendsto (fun n : ℕ ↦
      C * ((epsilon n * Real.log (Scale.L n)) * epsilon n))
      atTop (nhds 0) := by
    simpa only [mul_zero] using tendsto_const_nhds.mul hproduct
  apply hscaled.congr'
  have hLTop : Tendsto Scale.L atTop atTop := by
    simpa only [Scale.L] using
      Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hlogTop : Tendsto (fun n : ℕ ↦ Real.log (Scale.L n))
      atTop atTop := Real.tendsto_log_atTop.comp hLTop
  filter_upwards [hlogTop.eventually (eventually_gt_atTop (0 : ℝ))]
      with n hlog
  unfold selectedMeshSchurRateMajorant
  dsimp only [C]
  field_simp [hgamma.ne', hcenter.ne', hlog.ne']







end BridgeData

end

end Erdos390.Full.PaperBridgeFit

end

/- Source module: Erdos390.Full.PaperCanonicalReferenceSlowEventually -/
section


/-!
# Canonical direct reference slow-row bound

The identity part of the Dickman diagonal is cancelled exactly on each
arithmetic prime fibre.  The remaining diagonal and kernel terms both carry
the literal first moment of that fibre.  Consequently the constant below is
universal: it is chosen before `W`, `delta`, `eta`, and the mesh, and no
factor such as `1 / delta` occurs.
-/

open Filter Topology Metric Set

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

open ArithmeticModel ArithmeticBandGeometry
open PaperActualSlowRightRowFinite
open ConditionedPoissonLimit DickmanBasic
open RegularMeshPrimeCutoffs

namespace BridgeData

/-- Global-order canonical reference-row terminal.  The constants are
universal and `W₀` is selected before the paper scale and mesh. -/
theorem exists_global_cutoff_eventually_canonical_referenceSlowRow_le :
    ∃ CF Cprod : ℝ, 0 ≤ CF ∧ 0 ≤ Cprod ∧
      ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W →
      ∀ {delta eta : ℝ} (hdelta : 0 < delta)
        (M : RegularRelativeMesh.Mesh delta eta),
        ∀ᶠ n : ℕ in atTop,
          ∀ {Head : Type*} [Fintype Head] [DecidableEq Head]
            (B : BridgeData Head (Fin (M.cellCount + 1))),
            B.sampleData.n = n → B.sampleData.W = W →
            (∃ (hWne : B.sampleData.W ≠ 0)
              (S : ScaleSeparation M B.sampleData.n B.sampleData.W),
              B.partition = Mesh.canonicalPartition
                M hdelta B.n_gt_one hWne S) →
            B.w = delta + eta →
            ∀ i : Fin (M.cellCount + 1),
              |B.referenceSlowRow i| ≤
                (CF + 7 * Cprod) *
                  B.w * B.bandCenter i := by
  obtain ⟨CF, hCFpos, hFLipschitz⟩ := exists_F_lipschitz_unit
  obtain ⟨Cprod, hCprod, hProduct⟩ := kernel_product_bound
  let W₀ : ℕ := canonicalActualMomentCutoff
  refine ⟨CF, Cprod, hCFpos.le, hCprod.le, W₀, ?_⟩
  intro W hW delta eta hdelta M
  have hWmoment : canonicalActualMomentCutoff ≤ W := by
    dsimp only [W₀] at hW
    exact hW
  have hMoment :=
    Mesh.canonicalActualFirstMomentCutoff_eventually M hdelta W hWmoment
  filter_upwards [hMoment] with n hMomentN
  intro Head _instFintype _instDecidable B hBn hBW hpartition hscale i
  subst n
  subst W
  obtain ⟨_hWneMoment, _hnMoment, hMomentAll⟩ := hMomentN
  obtain ⟨hWne, S, hpartitionUser⟩ := hpartition
  let Pcanonical := Mesh.canonicalPartition M hdelta B.n_gt_one hWne S
  have hpartitionCanonical : B.partition = Pcanonical := by
    exact hpartitionUser.trans (by rfl)
  obtain ⟨hdevSupRaw, hdevL1Raw⟩ := hMomentAll S
  have hactualScale : delta + M.ratio ≤ B.w := by
    rw [hscale]
    linarith [M.ratio_le_eta]
  have hw : 0 < B.w :=
    (add_pos hdelta M.ratio_pos).trans_le hactualScale
  have hdevSup : ∀ p : BandPrime B.sampleData.n B.sampleData.W,
      |B.primeDeviation p| ≤ B.w := by
    intro p
    change |B.partition.deviation p| ≤ B.w
    rw [hpartitionCanonical]
    exact (hdevSupRaw p).trans hactualScale
  have hdevL1 : B.primeDeviationL1 ≤ 7 * B.w := by
    change B.partition.totalL1 ≤ 7 * B.w
    rw [hpartitionCanonical]
    exact hdevL1Raw.trans
      (mul_le_mul_of_nonneg_left hactualScale (by norm_num))
  have hFone : ∀ p : BandPrime B.sampleData.n B.sampleData.W,
      |F (tPrime B.sampleData.n p.1) - 1| ≤
        CF * tPrime B.sampleData.n p.1 := by
    intro p
    have ht : tPrime B.sampleData.n p.1 ∈ Icc (0 : ℝ) 1 :=
      ⟨(B.bandPrime_tPrime_pos p).le,
        PaperPrimePowerRow.tPrime_le_one_of_mem_primeBand
          B.n_gt_one p.2⟩
    have h := hFLipschitz _ ht 0 (by norm_num)
    simpa only [F_zero, sub_zero, abs_of_nonneg ht.1] using h
  have hKernelProduct : ∀
      p q : BandPrime B.sampleData.n B.sampleData.W,
      |covarianceKernel (tPrime B.sampleData.n p.1)
          (tPrime B.sampleData.n q.1)| ≤
        Cprod * tPrime B.sampleData.n p.1 *
          tPrime B.sampleData.n q.1 := by
    intro p q
    have hp : tPrime B.sampleData.n p.1 ∈ Icc (0 : ℝ) 1 :=
      ⟨(B.bandPrime_tPrime_pos p).le,
        PaperPrimePowerRow.tPrime_le_one_of_mem_primeBand
          B.n_gt_one p.2⟩
    have hq : tPrime B.sampleData.n q.1 ∈ Icc (0 : ℝ) 1 :=
      ⟨(B.bandPrime_tPrime_pos q).le,
        PaperPrimePowerRow.tPrime_le_one_of_mem_primeBand
          B.n_gt_one q.2⟩
    simpa only [covarianceKernel] using hProduct _ hp _ hq
  exact B.abs_referenceSlowRow_le_of_harmonicCentering
    hw.le hCprod.le hFone hKernelProduct hdevSup hdevL1 i

end BridgeData

end

end Erdos390.Full.PaperBridgeFit

end

/- Source module: Erdos390.Full.PaperCanonicalNonstepSlowRightColumnEventually -/
section


/-!
# Literal canonical slow right column

The preceding relative full/reference approximation is combined with the
direct Dickman reference-row bound.  The result is the literal full
valuation slow column at paper scale, with no step-function replacement and
no profile, transfer, row-rate, or moving-low assumptions at the interface.
-/

open Filter

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

open ArithmeticModel ArithmeticBandGeometry
open PaperGuardCensus RegularMeshPrimeCutoffs

namespace BridgeData

/-- Fully discharged `O(w * alpha_i)` bound for the literal full-valuation
slow right column.  The cutoff is selected before `delta`, `eta`, the mesh,
head data, and the tilt box. -/
theorem exists_global_cutoff_eventually_canonical_nonstepSlowRightColumn_le :
    ∃ CF Cprod : ℝ, 0 ≤ CF ∧ 0 ≤ Cprod ∧
      ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W →
      ∀ {delta eta : ℝ} (hdelta : 0 < delta)
        (M : RegularRelativeMesh.Mesh delta eta),
      ∀ {Head : Type*} [Fintype Head] [DecidableEq Head] [Nonempty Head]
        (Phead : Head → HeadPattern.Pattern),
        (∀ h : Head, ∀ p : ℕ,
          p ∈ (Phead h).primes ↔ p.Prime ∧ p ≤ W) →
      ∀ (I : PhysicalIntervals) (Cmax : ℝ),
        (∀ sigma, 1 ≤ I.lower sigma) →
        (∀ sigma, I.upper sigma ≤ Cmax) →
      ∀ (Cprom Cbank : ℕ) (ledger : ∀ n, Ledger n Cprom Cbank),
      ∀ (Acoef Aphys : ℝ), 0 ≤ Acoef → 0 ≤ Aphys →
        ∀ᶠ n : ℕ in atTop,
          ∀ (B : BridgeData Head (Fin (M.cellCount + 1))),
            B.sampleData.n = n → B.sampleData.W = W →
            ∀ (hsep : physicalBound (I.upper .minus) B.sampleData.n <
                physicalBound (I.lower .plus) B.sampleData.n)
              (hremaining : ∀ c : Cell Head,
                (rawCell Phead I B.sampleData.n c \
                  (ledger B.sampleData.n).guards).Nonempty),
              B.sampleData = canonicalSampleData
                (W := B.sampleData.W) Phead I
                  (ledger B.sampleData.n) hsep hremaining →
            (∃ (hWne : B.sampleData.W ≠ 0)
              (S : ScaleSeparation M B.sampleData.n B.sampleData.W),
              B.partition = Mesh.canonicalPartition
                M hdelta B.n_gt_one hWne S) →
            B.w = delta + eta →
            ∀ (xi : B.ParamSpace),
              (∀ p : BandPrime B.sampleData.n B.sampleData.W,
                |B.effectivePrimeCoefficient xi p| ≤ Acoef) →
              |xi MomentCoord.physical| ≤ Aphys →
              ∀ i : Fin (M.cellCount + 1),
                |B.normalizedBandCovarianceRow xi B.slowScore i| ≤
                  (1 + CF + 7 * Cprod) *
                    B.w * B.bandCenter i := by
  obtain ⟨CF, Cprod, hCF, hCprod, Wreference, hReferenceMain⟩ :=
    exists_global_cutoff_eventually_canonical_referenceSlowRow_le
  obtain ⟨Wfull, hFullMain⟩ :=
    forall_accuracy_exists_cutoff_eventually_canonical_fullSlowRow_sub_reference
      (1 : ℝ) (by norm_num)
  let W₀ : ℕ := max Wreference Wfull
  refine ⟨CF, Cprod, hCF, hCprod, W₀, ?_⟩
  intro W hW delta eta hdelta M Head _instFintype _instDecidable
    _instNonempty Phead hhead I Cmax hlowerOne hupperMax
    Cprom Cbank ledger Acoef Aphys hAcoef hAphys
  have hWreference : Wreference ≤ W := by
    dsimp only [W₀] at hW
    omega
  have hWfull : Wfull ≤ W := by
    dsimp only [W₀] at hW
    omega
  have hReference := hReferenceMain W hWreference hdelta M
  have hFull := hFullMain W hWfull hdelta M Phead hhead I Cmax
    hlowerOne hupperMax Cprom Cbank ledger Acoef Aphys hAcoef hAphys
  filter_upwards [hReference, hFull] with n hReferenceN hFullN
  intro B hBn hBW hsep hremaining hcanonical hpartition hscale
    xi heta hphys i
  have href := hReferenceN B hBn hBW hpartition hscale i
  have hfull := hFullN B hBn hBW hsep hremaining hcanonical
    hpartition hscale xi heta hphys i
  calc
    |B.normalizedBandCovarianceRow xi B.slowScore i| =
        |(B.normalizedBandCovarianceRow xi B.slowScore i -
            B.referenceSlowRow i) + B.referenceSlowRow i| := by
      congr 1
      ring
    _ ≤ |B.normalizedBandCovarianceRow xi B.slowScore i -
            B.referenceSlowRow i| + |B.referenceSlowRow i| :=
      abs_add_le _ _
    _ ≤ (1 : ℝ) * B.w * B.bandCenter i +
        (CF + 7 * Cprod) *
          B.w * B.bandCenter i := add_le_add hfull href
    _ = (1 + CF + 7 * Cprod) *
          B.w * B.bandCenter i := by ring

end BridgeData

end

end Erdos390.Full.PaperBridgeFit

end

/- Source module: Erdos390.Full.PaperNonstepSlowNuisanceCorrection -/
section


/-!
# Nuisance correction for the literal non-step slow score

The source covariance vector is estimated from the exact primewise
coefficients `g_p = alpha_{j(p)} - t_p`.  Its natural size is therefore
`Cmarked * sum |g_p|/p`, with no band-centre surrogate and no least-centre
division.  This is the finite statement needed before the sharp
`alpha_0 -> 0` eventual conversion.
-/

open scoped BigOperators

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

open ArithmeticBandGeometry PaperWeightedInverseExport

namespace BridgeData

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]
  (B : BridgeData Head Band)



/-- Reciprocal marked-prime estimates control the nuisance covariance vector
of the literal non-step slow score by its exact global weighted `L¹` norm. -/
theorem nuisanceCovarianceVector_slowScore_norm_le_of_marked
    [Nonempty Head]
    (xi : B.ParamSpace) {Cmarked : ℝ} (hCmarked : 0 ≤ Cmarked)
    (hmarked : ∀ (c : NuisanceCoord B.HeadIndex)
      (p : BandPrime B.sampleData.n B.sampleData.W),
      |(B.tiltedLaw xi).covariance
        (fun m ↦ B.nuisanceStatistic m c)
        (fun m ↦ ArithmeticModel.valuation p.1
          (B.sampleData.value m))| ≤
        Cmarked * (1 / (p.1 : ℝ))) :
    ‖B.nuisanceCovarianceVector xi B.slowScore‖ ≤
      Real.sqrt (Fintype.card (NuisanceCoord B.HeadIndex) : ℝ) *
        (Cmarked * B.primeDeviationL1) := by
  have hL1 : 0 ≤ B.primeDeviationL1 := by
    unfold primeDeviationL1
    exact Finset.sum_nonneg fun p _hp ↦
      mul_nonneg (by positivity) (abs_nonneg _)
  apply B.nuisanceCovarianceVector_norm_le_sqrt_card_mul
    xi B.slowScore (mul_nonneg hCmarked hL1)
  intro c
  have hsum :
      (B.tiltedLaw xi).covariance
          (fun m ↦ B.nuisanceStatistic m c) B.slowScore =
        ∑ p : BandPrime B.sampleData.n B.sampleData.W,
          B.primeDeviation p *
            (B.tiltedLaw xi).covariance
              (fun m ↦ B.nuisanceStatistic m c)
              (fun m ↦ ArithmeticModel.valuation p.1
                (B.sampleData.value m)) := by
    unfold slowScore
    rw [show (fun m ↦ ∑ p : BandPrime B.sampleData.n B.sampleData.W,
        B.primeDeviation p *
          ArithmeticModel.valuation p.1 (B.sampleData.value m)) =
      fun m ↦ ∑ p ∈
          (Finset.univ : Finset
            (BandPrime B.sampleData.n B.sampleData.W)),
        B.primeDeviation p *
          ArithmeticModel.valuation p.1 (B.sampleData.value m) by simp]
    rw [FiniteProbability.covariance_sum_right]
    apply Finset.sum_congr rfl
    intro p _hp
    rw [FiniteProbability.covariance_smul_right]
  rw [hsum]
  calc
    |∑ p : BandPrime B.sampleData.n B.sampleData.W,
        B.primeDeviation p *
          (B.tiltedLaw xi).covariance
            (fun m ↦ B.nuisanceStatistic m c)
            (fun m ↦ ArithmeticModel.valuation p.1
              (B.sampleData.value m))| ≤
      ∑ p : BandPrime B.sampleData.n B.sampleData.W,
        |B.primeDeviation p *
          (B.tiltedLaw xi).covariance
            (fun m ↦ B.nuisanceStatistic m c)
            (fun m ↦ ArithmeticModel.valuation p.1
              (B.sampleData.value m))| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ p : BandPrime B.sampleData.n B.sampleData.W,
        |B.primeDeviation p| *
          (Cmarked * (1 / (p.1 : ℝ))) := by
      apply Finset.sum_le_sum
      intro p _hp
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hmarked c p) (abs_nonneg _)
    _ = Cmarked * B.primeDeviationL1 := by
      unfold primeDeviationL1
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p _hp
      ring

/-- Coercivity converts the preceding source-row estimate into a bound for
the exact nuisance regression coefficient of the slow score. -/
theorem nuisanceCoefficient_slowScore_norm_le_of_marked
    [Nonempty Head]
    (xi : B.ParamSpace) {gamma Cmarked : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (hCmarked : 0 ≤ Cmarked)
    (hmarked : ∀ (c : NuisanceCoord B.HeadIndex)
      (p : BandPrime B.sampleData.n B.sampleData.W),
      |(B.tiltedLaw xi).covariance
        (fun m ↦ B.nuisanceStatistic m c)
        (fun m ↦ ArithmeticModel.valuation p.1
          (B.sampleData.value m))| ≤
        Cmarked * (1 / (p.1 : ℝ))) :
    ‖B.nuisanceCoefficientOfScore xi hgamma hgap B.slowScore‖ ≤
      (Real.sqrt (Fintype.card (NuisanceCoord B.HeadIndex) : ℝ) *
        (Cmarked * B.primeDeviationL1)) / gamma := by
  exact (B.nuisanceCoefficientOfScore_norm_le xi hgamma hgap _).trans
    (div_le_div_of_nonneg_right
      (B.nuisanceCovarianceVector_slowScore_norm_le_of_marked
        xi hCmarked hmarked) hgamma.le)

/-- Coordinatewise normalized Schur correction for the literal slow score.
The input contributes `sum |g_p|/p`; the output band mass cancels exactly. -/
theorem abs_normalizedBandCovarianceRow_slow_nuisanceCorrection_le
    [Nonempty Head]
    (xi : B.ParamSpace) {gamma Cmarked : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (hCmarked : 0 ≤ Cmarked)
    (hmarked : ∀ (c : NuisanceCoord B.HeadIndex)
      (p : BandPrime B.sampleData.n B.sampleData.W),
      |(B.tiltedLaw xi).covariance
        (fun m ↦ B.nuisanceStatistic m c)
        (fun m ↦ ArithmeticModel.valuation p.1
          (B.sampleData.value m))| ≤
        Cmarked * (1 / (p.1 : ℝ)))
    (i : Band) :
    |B.normalizedBandCovarianceRow xi
        (fun m ↦ inner ℝ
          (B.nuisanceCoefficientOfScore xi hgamma hgap B.slowScore)
          (B.nuisanceStatistic m)) i| ≤
      ((Real.sqrt (Fintype.card (NuisanceCoord B.HeadIndex) : ℝ) *
          (Cmarked * B.primeDeviationL1)) / gamma) *
        (Real.sqrt (Fintype.card (NuisanceCoord B.HeadIndex) : ℝ) *
          Cmarked) := by
  let a : B.NuisanceSpace :=
    B.nuisanceCoefficientOfScore xi hgamma hgap B.slowScore
  let droot : ℝ :=
    Real.sqrt (Fintype.card (NuisanceCoord B.HeadIndex) : ℝ)
  have hL1 : 0 ≤ B.primeDeviationL1 := by
    unfold primeDeviationL1
    exact Finset.sum_nonneg fun p _hp ↦
      mul_nonneg (by positivity) (abs_nonneg _)
  have hdroot : 0 ≤ droot := Real.sqrt_nonneg _
  have hupperA : 0 ≤ (droot * (Cmarked * B.primeDeviationL1)) / gamma :=
    div_nonneg (mul_nonneg hdroot (mul_nonneg hCmarked hL1)) hgamma.le
  have ha : ‖a‖ ≤
      (droot * (Cmarked * B.primeDeviationL1)) / gamma := by
    simpa only [a, droot] using
      B.nuisanceCoefficient_slowScore_norm_le_of_marked
        xi hgamma hgap hCmarked hmarked
  have hrow :
      ‖B.nuisanceCovarianceVector xi (B.bandScore i)‖ ≤
        (droot * Cmarked) * B.harmonicMass i := by
    have h := B.nuisanceCovarianceVector_bandScore_norm_le_of_marked
      xi i hCmarked hmarked
    simpa only [droot, mul_assoc] using h
  have hH : 0 < B.harmonicMass i := B.harmonicMass_pos i
  change |B.normalizedBandCovarianceRow xi
    (fun m ↦ inner ℝ a (B.nuisanceStatistic m)) i| ≤ _
  unfold normalizedBandCovarianceRow
  rw [B.covariance_marked_nuisanceScore_eq_inner,
    abs_div, abs_of_pos hH]
  calc
    |inner ℝ a (B.nuisanceCovarianceVector xi (B.bandScore i))| /
          B.harmonicMass i ≤
        (‖a‖ * ‖B.nuisanceCovarianceVector xi (B.bandScore i)‖) /
          B.harmonicMass i :=
      div_le_div_of_nonneg_right (abs_real_inner_le_norm _ _) hH.le
    _ ≤ (((droot * (Cmarked * B.primeDeviationL1)) / gamma) *
          ((droot * Cmarked) * B.harmonicMass i)) /
          B.harmonicMass i := by
      apply div_le_div_of_nonneg_right _ hH.le
      exact mul_le_mul ha hrow (norm_nonneg _) hupperA
    _ = ((droot * (Cmarked * B.primeDeviationL1)) / gamma) *
        (droot * Cmarked) := by
      field_simp [hH.ne']

/-- Paper-scale relative form of the literal slow nuisance correction. -/
theorem abs_normalizedBandCovarianceRow_slow_nuisanceCorrection_le_rate
    [Nonempty Head]
    (xi : B.ParamSpace) {gamma Cmarked CL1 w amin : ℝ}
    (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (hCmarked : 0 ≤ Cmarked) (hCL1 : 0 ≤ CL1) (hw : 0 ≤ w)
    (hamin : 0 < amin)
    (hmarked : ∀ (c : NuisanceCoord B.HeadIndex)
      (p : BandPrime B.sampleData.n B.sampleData.W),
      |(B.tiltedLaw xi).covariance
        (fun m ↦ B.nuisanceStatistic m c)
        (fun m ↦ ArithmeticModel.valuation p.1
          (B.sampleData.value m))| ≤
        Cmarked * (1 / (p.1 : ℝ)))
    (hL1 : B.primeDeviationL1 ≤ CL1 * w)
    (hcenter : ∀ i : Band, amin ≤ B.bandCenter i)
    (i : Band) :
    |B.normalizedBandCovarianceRow xi
        (fun m ↦ inner ℝ
          (B.nuisanceCoefficientOfScore xi hgamma hgap B.slowScore)
          (B.nuisanceStatistic m)) i| ≤
      B.nonstepSlowNuisanceRate Cmarked gamma CL1 amin *
        w * B.bandCenter i := by
  have hraw :=
    B.abs_normalizedBandCovarianceRow_slow_nuisanceCorrection_le
      xi hgamma hgap hCmarked hmarked i
  have hdroot : 0 ≤
      Real.sqrt (Fintype.card (NuisanceCoord B.HeadIndex) : ℝ) :=
    Real.sqrt_nonneg _
  have hgamma0 : 0 ≤ gamma := hgamma.le
  have hamin0 : 0 ≤ amin := hamin.le
  have hcenter0 : 0 ≤ B.bandCenter i := (B.bandCenter_pos i).le
  calc
    |B.normalizedBandCovarianceRow xi
        (fun m ↦ inner ℝ
          (B.nuisanceCoefficientOfScore xi hgamma hgap B.slowScore)
          (B.nuisanceStatistic m)) i| ≤
      ((Real.sqrt (Fintype.card (NuisanceCoord B.HeadIndex) : ℝ) *
          (Cmarked * B.primeDeviationL1)) / gamma) *
        (Real.sqrt (Fintype.card (NuisanceCoord B.HeadIndex) : ℝ) *
          Cmarked) := hraw
    _ ≤ ((Real.sqrt (Fintype.card (NuisanceCoord B.HeadIndex) : ℝ) *
          (Cmarked * (CL1 * w))) / gamma) *
        (Real.sqrt (Fintype.card (NuisanceCoord B.HeadIndex) : ℝ) *
          Cmarked) := by
      gcongr
    _ = (B.nonstepSlowNuisanceRate Cmarked gamma CL1 amin * w) *
          amin := by
      unfold nonstepSlowNuisanceRate
      field_simp [hgamma.ne', hamin.ne']
    _ ≤ (B.nonstepSlowNuisanceRate Cmarked gamma CL1 amin * w) *
          B.bandCenter i := by
      have hrate0 : 0 ≤
          B.nonstepSlowNuisanceRate Cmarked gamma CL1 amin := by
        unfold nonstepSlowNuisanceRate
        positivity
      exact mul_le_mul_of_nonneg_left (hcenter i)
        (mul_nonneg hrate0 hw)
    _ = B.nonstepSlowNuisanceRate Cmarked gamma CL1 amin *
          w * B.bandCenter i := by ring



end BridgeData

end

end Erdos390.Full.PaperBridgeFit

end

/- Source module: Erdos390.Full.PaperCanonicalNonstepSlowResidualEventually -/
section


/-!
# Canonical Schur-projected non-step slow row

The literal full-valuation slow row is projected off the finite nuisance
space.  The marked-prime rate is squared before paying the moving-low
`1/alpha_0` loss, and all nuisance dimension and coercivity constants are
fixed only after `W` and the head/physical data are fixed.  The structural
cutoff remains before `delta`, `eta`, the mesh, and the effective box.
-/

open Filter Topology Metric Set

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

open ArithmeticModel ArithmeticBandGeometry
open PaperGuardCensus RegularMeshPrimeCutoffs
open PaperWeightedInverseExport

namespace BridgeData

set_option maxHeartbeats 2500000

/-- Fully discharged paper-scale slow right row after nuisance Schur
projection.  This is the row hypothesis consumed by the canonical
coefficient package for Lemma 8.6. -/
theorem exists_global_cutoff_eventually_canonical_nonstepSlowResidualRow_le :
    ∃ CF Cprod : ℝ, 0 ≤ CF ∧ 0 ≤ Cprod ∧
      ∃ W₀ : ℕ, ∃ hW₀two : 2 ≤ W₀,
        ∀ W : ℕ, (hW : W₀ ≤ W) →
      ∀ {delta eta : ℝ} (hdelta : 0 < delta)
        (M : RegularRelativeMesh.Mesh delta eta),
      ∀ {Head : Type*} [Fintype Head] [DecidableEq Head] [Nonempty Head]
        (Phead : Head → HeadPattern.Pattern),
        (∀ h : Head, ∀ p : ℕ,
          p ∈ (Phead h).primes ↔ p.Prime ∧ p ≤ W) →
      ∀ (I : PhysicalIntervals) (U : ℝ) (hU : 1 ≤ U),
        (hlowerOne : ∀ sigma, 1 ≤ I.lower sigma) →
        (hupperU : ∀ sigma, I.upper sigma ≤ U) →
      ∀ (Cprom Cbank : ℕ) (ledger : ∀ n, Ledger n Cprom Cbank)
        (a : NNReal) (marginFloor : ℝ), 0 < marginFloor →
        ∀ᶠ n : ℕ in atTop,
          ∀ (B : BridgeData Head (Fin (M.cellCount + 1))),
            (hBn : B.sampleData.n = n) → (hBW : B.sampleData.W = W) →
            ∀ (hsep : physicalBound (I.upper .minus) B.sampleData.n <
                physicalBound (I.lower .plus) B.sampleData.n)
              (hremaining : ∀ c : Cell Head,
                (rawCell Phead I B.sampleData.n c \
                  (ledger B.sampleData.n).guards).Nonempty),
              (hcanonical : B.sampleData = canonicalSampleData
                (W := B.sampleData.W) Phead I
                  (ledger B.sampleData.n) hsep hremaining) →
            (∃ (hWne : B.sampleData.W ≠ 0)
              (S : ScaleSeparation M B.sampleData.n B.sampleData.W),
              B.partition = Mesh.canonicalPartition
                M hdelta B.n_gt_one hWne S) →
            (hscale : B.w = delta + eta) →
            ∀ (T : BarycentricTarget B.sampleData),
              (hTmargin : marginFloor ≤ T.cellMassMargin) →
              (hbaseline : B.baseline = T.baseline) →
              ∀ (z : B.EffectiveParamSpace),
                (hz : z ∈ closedBall
                  (0 : B.EffectiveParamSpace) (a : ℝ)) →
                ∀ i : Fin (M.cellCount + 1),
                  |B.normalizedBandCovarianceRow
                      (B.effectiveParamEquiv z)
                      (B.nuisanceResidualScore
                        (B.effectiveParamEquiv z)
                        (B.canonicalEffectiveNuisanceGamma_pos
                          I U (3 * (a : ℝ)) T)
                        (B.canonicalEffectiveNuisanceGap_on_closedBall
                          I a hU
                          hlowerOne hupperU
                          (by
                            intro sigma
                            rw [hcanonical]
                            rfl)
                          (by
                            intro sigma
                            rw [hcanonical]
                            rfl)
                          T hbaseline
                          (by rw [hBW]; omega) z hz)
                        B.slowScore) i| ≤
                    ((2 + CF + 7 * Cprod) * B.w) *
                      B.bandCenter i := by
  obtain ⟨CF, Cprod, hCF, hCprod, Wraw, hRawMain⟩ :=
    exists_global_cutoff_eventually_canonical_nonstepSlowRightColumn_le
  let W₀ : ℕ := max 2 (max Wraw
    (max canonicalActualMomentCutoff canonicalCenterEnvelopeCutoff))
  refine ⟨CF, Cprod, hCF, hCprod, W₀, ?_, ?_⟩
  · dsimp only [W₀]
    omega
  intro W hW delta eta hdelta M Head _instFintype _instDecidable
    _instNonempty Phead hhead I U hU hlowerOne hupperU
    Cprom Cbank ledger a marginFloor hmarginFloor
  have hWraw : Wraw ≤ W := by
    dsimp only [W₀] at hW
    omega
  have hWmoment : canonicalActualMomentCutoff ≤ W := by
    dsimp only [W₀] at hW
    omega
  have hWcenter : canonicalCenterEnvelopeCutoff ≤ W := by
    dsimp only [W₀] at hW
    omega
  have hWone : 1 < W := by
    omega
  have hHeadLe : ∀ h, ∀ p ∈ (Phead h).primes, p ≤ W := by
    intro h p hp
    exact (hhead h p).mp hp |>.2
  let Acoef : ℝ := 3 * (a : ℝ)
  have hAcoef : 0 ≤ Acoef := by dsimp only [Acoef]; positivity
  have hRaw := hRawMain W hWraw hdelta M Phead hhead I U
    hlowerOne hupperU Cprom Cbank ledger Acoef Acoef hAcoef hAcoef
  obtain ⟨markedError, hmarked0, hmarkedRate, Nmarked, hmarked⟩ :=
    _root_.Erdos390.Full.PaperCanonicalMarkedNuisanceRows.PaperBridgeFit.BridgeData.exists_uniform_canonical_tiltedLaw_nuisance_valuation_rate_on_effectiveBall
      Phead I U hU hlowerOne hupperU Cprom Cbank ledger
        W hWone hHeadLe a
  let Calpha : ℝ := canonicalCenterEnvelopeConstant delta
  have hCalpha : 0 < Calpha := by
    simpa only [Calpha] using canonicalCenterEnvelopeConstant_pos hdelta
  let centerScale : ℝ := 1 / Calpha
  have hcenterScale : 0 < centerScale := one_div_pos.mpr hCalpha
  let gammaFloor : ℝ := canonicalEffectiveNuisanceGammaFloor
    Head I U (3 * (a : ℝ)) W marginFloor
  have hgammaFloor : 0 < gammaFloor := by
    dsimp only [gammaFloor]
    exact canonicalEffectiveNuisanceGammaFloor_pos I hmarginFloor
  let droot : ℝ := nuisanceDimensionCeiling Head
  have hdroot : 0 ≤ droot := by
    dsimp only [droot, nuisanceDimensionCeiling]
    positivity
  have hmarkedT : Tendsto markedError atTop (nhds 0) :=
    tendsto_zero_of_nonneg_mul_logL_zero
      markedError hmarked0 hmarkedRate
  let rateMajorant : ℕ → ℝ :=
    selectedMeshSchurRateMajorant
      markedError droot 7 gammaFloor centerScale
  have hrateT : Tendsto rateMajorant atTop (nhds 0) := by
    simpa only [rateMajorant] using
      tendsto_selectedMeshSchurRateMajorant_zero
        markedError hmarkedT hmarkedRate hgammaFloor hcenterScale
  have hrateSmall : ∀ᶠ n : ℕ in atTop, rateMajorant n < 1 :=
    hrateT.eventually (eventually_lt_nhds (by norm_num))
  have hMoment :=
    Mesh.canonicalActualFirstMomentCutoff_eventually M hdelta W hWmoment
  have hCenterLower :=
    Mesh.canonicalCenterEnvelopeCutoff_eventually_lower
      M hdelta W hWcenter
  have hLogL : ∀ᶠ n : ℕ in atTop,
      0 < Real.log (Scale.L n) := by
    have hLTop : Tendsto Scale.L atTop atTop := by
      simpa only [Scale.L] using
        Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
    exact (Real.tendsto_log_atTop.comp hLTop).eventually
      (eventually_gt_atTop 0)
  filter_upwards [hRaw, hrateSmall, hMoment, hCenterLower, hLogL,
    eventually_ge_atTop Nmarked] with n hRawN hrateSmallN hMomentN
      hCenterLowerN hLogLN hnMarked
  intro B hBn hBW hsep hremaining hcanonical hpartition hscale
    T hTmargin hbaseline z hz i
  subst n
  subst W
  obtain ⟨_hWneMoment, _hnMoment, hMomentAll⟩ := hMomentN
  obtain ⟨hWne, S, hpartitionUser⟩ := hpartition
  let Pcanonical := Mesh.canonicalPartition M hdelta B.n_gt_one hWne S
  have hpartitionCanonical : B.partition = Pcanonical := by
    exact hpartitionUser.trans (by rfl)
  obtain ⟨_hdevSupRaw, hdevL1Raw⟩ := hMomentAll S
  have hactualScale : delta + M.ratio ≤ B.w := by
    rw [hscale]
    linarith [M.ratio_le_eta]
  have hw : 0 < B.w :=
    (add_pos hdelta M.ratio_pos).trans_le hactualScale
  have hdevL1 : B.primeDeviationL1 ≤ 7 * B.w := by
    change B.partition.totalL1 ≤ 7 * B.w
    rw [hpartitionCanonical]
    exact hdevL1Raw.trans
      (mul_le_mul_of_nonneg_left hactualScale (by norm_num))
  have hLo : ∀ sigma, B.sampleData.lo sigma =
      physicalBound (I.lower sigma) B.sampleData.n := by
    intro sigma
    rw [hcanonical]
    rfl
  have hHi : ∀ sigma, B.sampleData.hi sigma =
      physicalBound (I.upper sigma) B.sampleData.n := by
    intro sigma
    rw [hcanonical]
    rfl
  let xi : B.ParamSpace := B.effectiveParamEquiv z
  have hznorm : ‖z‖ ≤ (a : ℝ) := by
    simpa only [mem_closedBall, dist_zero_right] using hz
  have hsize : B.paperEffectiveSize xi ≤ Acoef := by
    dsimp only [xi, Acoef]
    exact (B.paperEffectiveSize_effectiveParamEquiv_le z).trans
      (mul_le_mul_of_nonneg_left hznorm (by norm_num))
  have heffective := B.effective_bounds_of_paperEffectiveSize xi hsize
  have heta : ∀ p : BandPrime B.sampleData.n B.sampleData.W,
      |B.effectivePrimeCoefficient xi p| ≤ Acoef := heffective.1
  have hnuisance : ‖B.nuisanceParameter xi‖ ≤ Acoef := heffective.2
  have hphys : |xi MomentCoord.physical| ≤ Acoef := by
    calc
      |xi MomentCoord.physical| =
          ‖B.nuisanceParameter xi NuisanceCoord.physical‖ := by
        simp only [B.nuisanceParameter_physical, Real.norm_eq_abs]
      _ ≤ ‖B.nuisanceParameter xi‖ :=
        PiLp.norm_apply_le (B.nuisanceParameter xi)
          NuisanceCoord.physical
      _ ≤ Acoef := hnuisance
  have hraw := hRawN B rfl rfl hsep hremaining hcanonical
    ⟨hWne, S, hpartitionUser⟩ hscale xi heta hphys i
  have hmarkedRows : ∀ (c : NuisanceCoord B.HeadIndex)
      (p : BandPrime B.sampleData.n B.sampleData.W),
      |(B.tiltedLaw xi).covariance
        (fun m ↦ B.nuisanceStatistic m c)
        (fun m ↦ valuation p.1 (B.sampleData.value m))| ≤
          markedError B.sampleData.n * (1 / (p.1 : ℝ)) := by
    intro c p
    simpa only [xi] using
      hmarked B z hz hnMarked rfl hsep hremaining hcanonical c p
  let gamma := B.canonicalEffectiveNuisanceGamma
    I U (3 * (a : ℝ)) T
  have hgamma : 0 < gamma := by
    dsimp only [gamma]
    exact B.canonicalEffectiveNuisanceGamma_pos I U (3 * (a : ℝ)) T
  have hgap : ∀ v, gamma * ‖v‖ ^ 2 ≤
      inner ℝ v (B.nuisanceCovarianceOperator xi v) := by
    intro v
    simpa only [gamma, xi] using
      B.canonicalEffectiveNuisanceGap_on_closedBall I a hU
        hlowerOne hupperU hLo hHi T hbaseline
          (by simpa only using hWone) z hz v
  have hgammaFloorLe : gammaFloor ≤ gamma := by
    dsimp only [gammaFloor, gamma]
    exact B.canonicalEffectiveNuisanceGammaFloor_le I hU
      (by positivity : 0 ≤ 3 * (a : ℝ)) hmarginFloor T hTmargin
  let amin : ℝ := centerScale / Real.log (Scale.L B.sampleData.n)
  have hamin : 0 < amin := div_pos hcenterScale hLogLN
  have hcenterAmin : ∀ j : Fin (M.cellCount + 1),
      amin ≤ B.bandCenter j := by
    intro j
    change centerScale / Real.log (Scale.L B.sampleData.n) ≤
      B.partition.center j
    rw [hpartitionUser]
    simpa only [centerScale, Calpha] using
      hCenterLowerN B.n_gt_one hWne S j
  have hdimension : Real.sqrt
      (Fintype.card (NuisanceCoord B.HeadIndex) : ℝ) ≤ droot := by
    dsimp only [droot]
    exact B.sqrt_nuisanceCoord_card_le_ceiling
  have hrateMajorized :
      B.nonstepSlowNuisanceRate (markedError B.sampleData.n)
          gamma 7 amin ≤ rateMajorant B.sampleData.n := by
    have heps0 : 0 ≤ markedError B.sampleData.n :=
      hmarked0 B.sampleData.n
    dsimp only [nonstepSlowNuisanceRate, rateMajorant,
      selectedMeshSchurRateMajorant, amin]
    gcongr
  have hrateOne :
      B.nonstepSlowNuisanceRate (markedError B.sampleData.n)
          gamma 7 amin ≤ 1 :=
    hrateMajorized.trans hrateSmallN.le
  have hcorrection :=
    B.abs_normalizedBandCovarianceRow_slow_nuisanceCorrection_le_rate
      xi hgamma hgap (hmarked0 B.sampleData.n) (by norm_num : (0 : ℝ) ≤ 7)
      hw.le hamin hmarkedRows hdevL1 hcenterAmin i
  have hcorrectionOne :
      |B.normalizedBandCovarianceRow xi
          (fun m ↦ inner ℝ
            (B.nuisanceCoefficientOfScore xi hgamma hgap B.slowScore)
            (B.nuisanceStatistic m)) i| ≤
        B.w * B.bandCenter i := by
    exact hcorrection.trans (by
      calc
        B.nonstepSlowNuisanceRate (markedError B.sampleData.n)
              gamma 7 amin * B.w * B.bandCenter i =
            B.nonstepSlowNuisanceRate (markedError B.sampleData.n)
              gamma 7 amin * (B.w * B.bandCenter i) := by ring
        _ ≤ 1 * (B.w * B.bandCenter i) :=
          mul_le_mul_of_nonneg_right hrateOne
            (mul_nonneg hw.le (B.bandCenter_pos i).le)
        _ = B.w * B.bandCenter i := by ring)
  change |B.normalizedBandCovarianceRow xi
      (B.nuisanceResidualScore xi hgamma hgap B.slowScore) i| ≤ _
  unfold nuisanceResidualScore
  rw [B.normalizedBandCovarianceRow_sub]
  calc
    |B.normalizedBandCovarianceRow xi B.slowScore i -
        B.normalizedBandCovarianceRow xi
          (fun m ↦ inner ℝ
            (B.nuisanceCoefficientOfScore xi hgamma hgap B.slowScore)
            (B.nuisanceStatistic m)) i| ≤
      |B.normalizedBandCovarianceRow xi B.slowScore i| +
        |B.normalizedBandCovarianceRow xi
          (fun m ↦ inner ℝ
            (B.nuisanceCoefficientOfScore xi hgamma hgap B.slowScore)
            (B.nuisanceStatistic m)) i| := abs_sub _ _
    _ ≤ (1 + CF + 7 * Cprod) *
          B.w * B.bandCenter i + B.w * B.bandCenter i :=
      add_le_add hraw hcorrectionOne
    _ = ((2 + CF + 7 * Cprod) * B.w) *
          B.bandCenter i := by ring

end BridgeData

end

end Erdos390.Full.PaperBridgeFit

end

universe u_1
theorem solution : Erdos390.RemainingAnalyticGoal002_002.{u_1} := by
  exact @Erdos390.Full.PaperBridgeFit.BridgeData.exists_global_cutoff_eventually_canonical_nonstepSlowResidualRow_le
