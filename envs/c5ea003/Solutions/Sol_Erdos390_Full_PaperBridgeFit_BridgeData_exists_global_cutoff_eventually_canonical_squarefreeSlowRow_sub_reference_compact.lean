-- Prove2me | solution 1 for Erdos390.Full.PaperBridgeFit.BridgeData.exists_global_cutoff_eventually_canonical_squarefreeSlowRow_sub_reference_compact
-- status  : ACCEPTED   (prove)
-- author  : @doctosil
-- created : 2026-09-17T17:14:59.395109+00:00
-- url     : https://prove2.me/submissions/9f498127-673e-4959-97e3-c4b405a8a4a2

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
import Theorems.Thm_Erdos390_Full_PaperBridgeFit_BridgeData_abs_squarefreeSlowRow_sub_referenceSlowRow_le
import Theorems.Thm_Erdos390_Full_PaperBridgeFit_BridgeData_exists_boxIndependent_actual_component_signed_profiles_compact
import Theorems.Thm_Erdos390_Full_RegularMeshPrimeCutoffs_Mesh_canonicalCenterEnvelopeCutoff_eventually_inverse
import Theorems.Thm_Erdos390_Full_RegularMeshPrimeCutoffs_Mesh_canonicalNonstepLocalDiagonalCutoff_eventually
import Theorems.Thm_Erdos390_Full_RegularMeshPrimeCutoffs_Mesh_momentReady_of_endpointMomentBounds
import Theorems.Thm_Erdos390_Full_SquarefreeCovarianceReference_abs_sigmaMixture_covII_diagonal_sub_reference_le
import Theorems.Thm_Erdos390_Full_SquarefreeCovarianceReference_abs_sigmaMixture_covII_sub_squarefreeKernelEntry_le_of_squarefree_profiles


section
universe u_1 u_3
theorem Erdos390.Full.PaperBridgeFit.BridgeData.exists_boxIndependent_actual_component_signed_profiles : Erdos390.RemainingAnalyticGoal001_010.{u_1, u_3} := @Erdos390.Full.PaperBridgeFit.BridgeData.exists_boxIndependent_actual_component_signed_profiles_compact
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

/- Source module: Erdos390.Full.PoissonDickmanKernelBounds -/
section


/-!
# Uniform bounds for the removable Poisson--Dickman kernel

The moving-low-cell transfer needs a bound which remains valid as either
prime coordinate approaches zero.  The continuous quotient constructed in
`ConditionedPoissonLimit` gives such a bound on the compact unit square.  This
file exports the compactness consequence and converts it back to literal
bounds for the covariance kernel.  No conditioned-law or Palm identity is
used here.
-/

open Set

noncomputable section

namespace Erdos390.Full.PoissonDickmanKernelBounds

open ConditionedPoissonLimit

/-- The removable quotient `K(s,t)/t` is uniformly bounded on the closed unit
square. -/
theorem exists_covarianceKernelQuotient_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
      |covarianceKernelQuotient s t| ≤ C := by
  let S : Set (ℝ × ℝ) := Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1
  have hScompact : IsCompact S := isCompact_Icc.prod isCompact_Icc
  obtain ⟨C, hC⟩ := hScompact.exists_bound_of_continuousOn
    continuous_uncurry_covarianceKernelQuotient.continuousOn
  have hzeroMem : ((0 : ℝ), (0 : ℝ)) ∈ S := by
    exact ⟨by norm_num, by norm_num⟩
  have hCnonneg : 0 ≤ C :=
    (norm_nonneg (covarianceKernelQuotient 0 0)).trans
      (hC (0, 0) hzeroMem)
  refine ⟨C, hCnonneg, ?_⟩
  intro s hs t ht
  simpa only [Real.norm_eq_abs] using hC (s, t) ⟨hs, ht⟩

/-- Consequently the original kernel vanishes at least linearly in its
second coordinate, uniformly in the first. -/
theorem exists_covarianceKernel_abs_le_second :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
      |covarianceKernel s t| ≤ C * t := by
  obtain ⟨C, hCnonneg, hC⟩ := exists_covarianceKernelQuotient_bound
  refine ⟨C, hCnonneg, ?_⟩
  intro s hs t ht
  rw [← mul_covarianceKernelQuotient_eq_kernel hs ht, abs_mul,
    abs_of_nonneg ht.1]
  calc
    t * |covarianceKernelQuotient s t| ≤ t * C :=
      mul_le_mul_of_nonneg_left (hC s hs t ht) ht.1
    _ = C * t := by ring



end Erdos390.Full.PoissonDickmanKernelBounds

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

/- Source module: Erdos390.Full.FiniteProbabilityMixtureTilt -/
section


/-!
# Exponential tilts of finite tagged mixtures

A global exponential tilt of a finite mixture is not obtained by retaining
the old cell weights.  The exact new weights contain the cell partition
functions.  This file proves that identity before any covariance is formed,
so common-profile estimates can safely be averaged across cells.
-/

open scoped BigOperators

namespace Erdos390.Full
namespace FiniteProbability

noncomputable section

variable {Cell : Type*} [Fintype Cell]
  {Omega : Cell → Type*} [∀ c, Fintype (Omega c)]









/-- Pointwise exact factorization of the globally tilted density into the
new cell weight and the componentwise tilted density. -/
theorem exponentialTilt_sigmaMixture_mass
    (weight : FiniteProbability Cell)
    (mu : ∀ c, FiniteProbability (Omega c))
    (S : Sigma Omega → ℝ) (x : Sigma Omega) :
    ((sigmaMixture weight mu).exponentialTilt S).mass x =
      (sigmaMixture (tiltedSigmaWeight weight mu S)
        (fun c => (mu c).exponentialTilt (sigmaCellScore S c))).mass x := by
  rcases x with ⟨c, x⟩
  let Zc := (mu c).expPartition (sigmaCellScore S c)
  let Z := (sigmaMixture weight mu).expPartition S
  have hcellZ : Zc ≠ 0 :=
    ne_of_gt ((mu c).expPartition_pos (sigmaCellScore S c))
  have hglobalZ : Z ≠ 0 :=
    ne_of_gt ((sigmaMixture weight mu).expPartition_pos S)
  change weight.mass c * (mu c).mass x * Real.exp (S ⟨c, x⟩) / Z =
    (weight.mass c * Zc / Z) *
      ((mu c).mass x * Real.exp (S ⟨c, x⟩) / Zc)
  field_simp [hcellZ, hglobalZ]

private theorem finiteProbability_ext
    {Alpha : Type*} [Fintype Alpha]
    {mu nu : FiniteProbability Alpha} (h : mu.mass = nu.mass) : mu = nu := by
  cases mu with
  | mk massMu nonnegMu sumMu =>
    cases nu with
    | mk massNu nonnegNu sumNu =>
      dsimp only at h
      subst massNu
      rfl

/-- Equality of the two finite probability laws, not merely equality of
their expectations. -/
theorem exponentialTilt_sigmaMixture
    (weight : FiniteProbability Cell)
    (mu : ∀ c, FiniteProbability (Omega c))
    (S : Sigma Omega → ℝ) :
    (sigmaMixture weight mu).exponentialTilt S =
      sigmaMixture (tiltedSigmaWeight weight mu S)
        (fun c => (mu c).exponentialTilt (sigmaCellScore S c)) := by
  apply finiteProbability_ext
  funext x
  exact exponentialTilt_sigmaMixture_mass weight mu S x





end

end FiniteProbability
end Erdos390.Full

end

/- Source module: Erdos390.Full.PaperBridgeCellTiltDecomposition -/
section


/-!
# Exact cell-mixture decomposition of the paper bridge tilt

The analytic marked-cell estimates are stated for uniform probability laws on
individual structured cells and their finite tagged mixtures.  This file proves
the exact identification with the probability law carried by `BridgeData`.
Nothing asymptotic is used: the guard-deleted cells, their actual cardinalities,
the baseline cell masses, and the global partition-function reweighting all
remain literal.

This is also the place where the remaining nuisance tilt is exposed.  After the
medium-prime score has been split off, the physical/head factor is an explicit
second exponential tilt; it is not silently absorbed into the prime fugacity.
-/

open scoped BigOperators

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

open FiniteProbability ArithmeticModel ArithmeticBandGeometry

namespace BridgeData

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]
  (B : BridgeData Head Band)



























/-- The actual bridge law, with the global cell partition functions handled
correctly, is a tagged mixture of the componentwise tilted guard-deleted
cell laws. -/
theorem tiltedLaw_eq_tiltedSigmaMixture [Nonempty Head]
    (xi : B.ParamSpace) :
    B.tiltedLaw xi =
      sigmaMixture
        (tiltedSigmaWeight B.baselineCellProbability
          B.guardedCellProbability (B.scaledBridgeScore xi))
        (fun c ↦ (B.guardedCellProbability c).exponentialTilt
          (sigmaCellScore (B.scaledBridgeScore xi) c)) := by
  rw [B.tiltedLaw_eq_exponentialTilt_baseline]
  exact exponentialTilt_sigmaMixture _ _ _



end BridgeData

end

end Erdos390.Full.PaperBridgeFit

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

























theorem pairCovarianceScale_nonneg {E : ℝ} (hE : 0 ≤ E) :
    0 ≤ pairCovarianceScale E := by
  unfold pairCovarianceScale
  have hrho : 0 ≤ 1 / DickmanBasic.rho DickmanBasic.U := by
    exact one_div_nonneg.mpr DickmanBasic.rho_U_pos.le
  positivity















end

end Erdos390.Full.PaperPrimePowerChamberError

end

/- Source module: Erdos390.Full.SquarefreeCovarianceReference -/
section


/-!
# Signed squarefree covariance transfer to the Dickman kernel

The prime-power ledger only needs an absolute upper bound.  Lemma 8.4 needs
the stronger *signed* comparison between the genuine divisor-indicator
covariance and the arithmetic Poisson--Dickman matrix.  This file derives
that comparison from the same common one- and two-divisor profiles, before
any band averaging.  In particular, the between-cell covariance of the
tagged mixture is retained exactly.
-/

namespace Erdos390.Full.SquarefreeCovarianceReference

open ArithmeticModel Scale
open FiniteProbability PrimePowerCovariance
open PrimePowerCovariance.BoundedValuationLaw
open OmittedTiltPairChamber
open PaperScaleMarkedCell PaperPrimePowerChamberError
open FullTiltPrimePowerCovariance
open FixedFiniteMixturePrimePower
open DickmanFourMarkProductKernel ConditionedPoissonLimit

noncomputable section

variable {Cell : Type*} [Fintype Cell]
  {Omega : Cell → Type*} [∀ c, Fintype (Omega c)]
  {M : ℕ}













/-- The signed one- and two-divisor comparisons assembled into the single
entrywise estimate consumed by the sharp band-row theorem. -/
theorem sigmaMixture_squarefree_reference_entry_bound_of_squarefree_profiles
    {E CKernel : ℝ} (hE : 0 ≤ E)
    (weight : FiniteProbability Cell)
    (law : ∀ c, BoundedValuationLaw (Omega c) M)
    {n W : ℕ} (hn : 1 < n)
    (hpair : ∀ c p, p ∈ primeBand n W →
      ∀ q, q ∈ (primeBand n W).erase p →
      |(law c).probability.expect
          (fun omega ↦ divInd (pairPower p q 1 1) ((law c).value omega)) -
        paperDivisibilityMain n (pairPower p q 1 1)| ≤
          E * pairWeight p q 1 1)
    (hsingle : ∀ c p, p ∈ primeBand n W →
      |(law c).probability.expect
          (fun omega ↦ divInd p ((law c).value omega)) -
        paperDivisibilityMain n p| ≤ E * singleWeight p 1)
    (hKernel : ∀ p ∈ primeBand n W,
      |covarianceKernel (tPrime n p) (tPrime n p)| ≤ CKernel) :
    let mix := sigmaMixture weight law
    ∀ p q : ArithmeticBandGeometry.BandPrime n W,
      |mix.covII p.1 q.1 - squarefreeReferenceEntry n p.1 q.1| ≤
        (4 * pairCovarianceScale E) /
            ((p.1 : ℝ) * (q.1 : ℝ)) +
          (if p = q then
            (2 * E) / (p.1 : ℝ) +
              ((1 / DickmanBasic.rho DickmanBasic.U + 2 * E) ^ 2 +
                CKernel) / (p.1 : ℝ) ^ 2
          else 0) := by
  dsimp only
  let mix := sigmaMixture weight law
  intro p q
  by_cases hpq : p = q
  · subst q
    rw [if_pos rfl]
    have hdiag := abs_sigmaMixture_covII_diagonal_sub_reference_le
      hE weight law hn p.2 (fun c ↦ hsingle c p.1 p.2)
      (hKernel p.1 p.2)
    have hcovNonneg : 0 ≤ pairCovarianceScale E :=
      pairCovarianceScale_nonneg hE
    have hpPos : (0 : ℝ) < p.1 := by
      exact_mod_cast (prime_of_mem_primeBand p.2).pos
    have hextra : 0 ≤
        (4 * pairCovarianceScale E) / ((p.1 : ℝ) * (p.1 : ℝ)) :=
      div_nonneg (mul_nonneg (by norm_num) hcovNonneg)
        (mul_nonneg hpPos.le hpPos.le)
    exact hdiag.trans (by
      have htwo : 2 * E / (p.1 : ℝ) = (2 * E) / (p.1 : ℝ) := rfl
      rw [htwo]
      linarith)
  · rw [if_neg hpq]
    have hqErase : q.1 ∈ (primeBand n W).erase p.1 :=
      Finset.mem_erase.mpr ⟨fun h ↦ hpq (Subtype.ext h.symm), q.2⟩
    have hoff :=
      abs_sigmaMixture_covII_sub_squarefreeKernelEntry_le_of_squarefree_profiles
      hE weight law hn p.2 hqErase
      (fun c ↦ hpair c p.1 p.2 q.1 hqErase)
      (fun c ↦ hsingle c p.1 p.2)
      (fun c ↦ hsingle c q.1 q.2)
    have href : squarefreeReferenceEntry n p.1 q.1 =
        squarefreeKernelEntry n p.1 q.1 := by
      rw [squarefreeReferenceEntry, if_neg (by
        intro h
        exact hpq (Subtype.ext h))]
    rw [href]
    have hrewrite :
        pairCovarianceScale E * pairWeight p.1 q.1 1 1 =
          (4 * pairCovarianceScale E) /
            ((p.1 : ℝ) * (q.1 : ℝ)) := by
      unfold pairWeight
      norm_num
      ring
    simpa only [mix, hrewrite, add_zero] using hoff



end

end Erdos390.Full.SquarefreeCovarianceReference

end

/- Source module: Erdos390.Full.PaperActualSquarefreeReference -/
section


/-!
# The actual bridge squarefree law and the canonical reference operator

This file closes two finite-probability identifications needed in Lemma 8.4.
First, a reciprocal signed profile for the medium-only law survives the
literal physical/head component tilt at the same reciprocal scale.  Second,
the partition-function-reweighted mixture of those component laws is exactly
the `BridgeData.tiltedLaw`, including the between-cell covariance.
-/

open scoped BigOperators

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

open ArithmeticModel ArithmeticBandGeometry FiniteProbability
open PrimePowerCovariance PrimePowerCovariance.BoundedValuationLaw
open OmittedTiltPairChamber PaperPrimePowerChamberError
open StructuredCells ValuationScoreDomination

namespace BridgeData

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]
  (B : BridgeData Head Band)





















private theorem boundedValuationLaw_ext
    {Omega : Type*} [Fintype Omega] {M : ℕ}
    {law₁ law₂ : BoundedValuationLaw Omega M}
    (hprob : law₁.probability = law₂.probability)
    (hvalue : law₁.value = law₂.value) : law₁ = law₂ := by
  cases law₁
  cases law₂
  dsimp only at hprob hvalue
  subst_vars
  rfl

/-- The component mixture just constructed is literally the paper's global
tilted bounded valuation law.  In particular no between-cell covariance is
discarded. -/
theorem sigmaMixture_actualComponentValuationLaw_eq_actualValuationLaw
    [Nonempty Head] (xi : B.ParamSpace) :
    let weight := tiltedSigmaWeight B.baselineCellProbability
      B.guardedCellProbability (B.scaledBridgeScore xi)
    sigmaMixture weight (B.actualComponentValuationLaw xi) =
      B.actualValuationLaw xi := by
  dsimp only
  apply boundedValuationLaw_ext
  · exact congrArg id (B.tiltedLaw_eq_tiltedSigmaMixture xi).symm
  · rfl





/-- The profile covariance error keeps the same moving-low rate as the
underlying one- and two-divisor profile. -/
theorem tendsto_pairCovarianceScale_mul_logL_zero
    (E : ℕ → ℝ)
    (hE : Filter.Tendsto E Filter.atTop (nhds 0))
    (hERate : Filter.Tendsto
      (fun n : ℕ ↦ E n * Real.log (Scale.L n))
        Filter.atTop (nhds 0)) :
    Filter.Tendsto
      (fun n : ℕ ↦ PaperPrimePowerChamberError.pairCovarianceScale (E n) *
        Real.log (Scale.L n)) Filter.atTop (nhds 0) := by
  have hSqRate : Filter.Tendsto
      (fun n : ℕ ↦ E n ^ 2 * Real.log (Scale.L n))
        Filter.atTop (nhds 0) := by
    have hraw := hE.mul hERate
    have hzero : Filter.Tendsto
        (fun n : ℕ ↦ E n * (E n * Real.log (Scale.L n)))
          Filter.atTop (nhds 0) := by
      simpa only [mul_zero] using hraw
    apply hzero.congr'
    filter_upwards with n
    ring
  let a : ℝ := 1 + 2 * (1 / DickmanBasic.rho DickmanBasic.U)
  have hlin : Filter.Tendsto
      (fun n : ℕ ↦ a * (E n * Real.log (Scale.L n)))
        Filter.atTop (nhds 0) := by
    simpa only [mul_zero] using
      (tendsto_const_nhds.mul hERate : Filter.Tendsto
        (fun n : ℕ ↦ a * (E n * Real.log (Scale.L n)))
          Filter.atTop (nhds (a * 0)))
  have hsum := hlin.add hSqRate
  have hzero : Filter.Tendsto
      (fun n : ℕ ↦
        a * (E n * Real.log (Scale.L n)) +
          E n ^ 2 * Real.log (Scale.L n))
        Filter.atTop (nhds 0) := by
    simpa only [add_zero] using hsum
  apply hzero.congr'
  filter_upwards with n
  unfold PaperPrimePowerChamberError.pairCovarianceScale
  dsimp only [a]
  ring







/-! ### Exact finite-dimensional attachment to the arithmetic inverse -/



























/-! ### Reference-law row attachment

The literal global-tilt form of Lemma 7.5 is naturally obtained first for an
unguarded component mixture.  The actual bridge law is a guard-deleted
mixture with a residual physical tilt.  The next elementary estimate keeps
that identification issue outside the prime-power algebra: a weighted
prime-row comparison for the full and squarefree covariance matrices moves
the Lemma 7.5 estimate from an arbitrary reference law to the actual law.
The only moving-low loss is displayed explicitly as `rho / center i`.
-/





















end BridgeData

end

end Erdos390.Full.PaperBridgeFit

end

/- Source module: Erdos390.Full.PrimeSquarefreeDirichletGeometry -/
section


/-!
# Prime-level Dirichlet geometry for the squarefree reference covariance

The squarefree Dickman reference matrix is conjugated here on the literal
finite prime band.  The conjugating coordinate is `x_p = c_p / t_p`, the
vertex weight is `t_p / p`, and the quotient metric is `t_p^2 / p`.
Consequently the graph distance to a constant is exactly

`sum_p (c_p - mu * t_p)^2 / p`.

All identities are finite and exact.  The only analytic input in the final
anchor theorem is the already proved uniform negativity of the Dickman
kernel quotient on a fixed interior block.
-/

open scoped BigOperators
open Set

noncomputable section

namespace Erdos390.Full.PrimeSquarefreeDirichletGeometry

open ArithmeticModel
open ConditionedPoissonLimit PoissonDickmanWeightedInverse
open PoissonDickmanDirichlet
open FiniteAnchoredDirichletQuadratic
open SquarefreeCovarianceReference



variable {n W : ℕ}





















theorem tPrime_pos (hn : 1 < n) (p : PrimeIndex n W) :
    0 < tPrime n p.1 := by
  have hp := prime_of_mem_primeBand p.2
  have hn0 : 0 < n := Nat.zero_lt_of_lt hn
  have hlogy : 0 < Real.log (y n) := by
    rw [Scale.log_y hn0]
    exact mul_pos (by norm_num) (Scale.L_pos hn)
  unfold tPrime
  exact div_pos (Real.log_pos (by exact_mod_cast hp.one_lt)) hlogy







theorem tPrime_mem_unit (hn : 1 < n) (p : PrimeIndex n W) :
    tPrime n p.1 ∈ Icc (0 : ℝ) 1 :=
  ⟨(tPrime_pos hn p).le,
    PaperPrimePowerRow.tPrime_le_one_of_mem_primeBand hn p.2⟩





















end Erdos390.Full.PrimeSquarefreeDirichletGeometry

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

/- Source module: Erdos390.Full.PaperCanonicalNonstepSquarefreeSlowEventually -/
section


/-!
# Canonical squarefree non-step slow row

This file performs the sharp moving-low conversion for the literal
coefficient `g_p = alpha_{j(p)} - t_p`.  The off-diagonal profile remainder
is divided by the output centre only after inserting the canonical estimate
`1/alpha_i = O_delta(log L)`.  The diagonal `p^{-2}` remainder is never
replaced by a global `O(1/W)` term: it is retained until the canonical local
diagonal theorem makes it `o(w alpha_i)`.

The structural cutoff is chosen before `delta`, the mesh, the head data, the
tilt box, and the requested accuracy.
-/

open scoped BigOperators
open Filter Topology Metric Set

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

open ArithmeticModel ArithmeticBandGeometry
open PaperGuardCensus RegularMeshPrimeCutoffs
open PrimeSquarefreeDirichletGeometry
open PrimePowerCovariance PrimePowerCovariance.BoundedValuationLaw
open SquarefreeCovarianceReference
open PaperPrimePowerChamberError
open PoissonDickmanKernelBounds
open FiniteProbability

namespace BridgeData

set_option maxHeartbeats 2000000

/-- Global-order, profile-free squarefree/reference slow-row terminal.  All
profile, rate, moving-low centre, first-moment, and local-diagonal estimates
are derived internally. -/
theorem exists_global_cutoff_eventually_canonical_squarefreeSlowRow_sub_reference
    : ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W →
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
      ∀ r : ℝ, 0 < r →
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
              B.partition = RegularMeshPrimeCutoffs.Mesh.canonicalPartition
                M hdelta B.n_gt_one hWne S) →
            B.w = delta + eta →
            ∀ (xi : B.ParamSpace),
              (∀ p : BandPrime B.sampleData.n B.sampleData.W,
                |B.effectivePrimeCoefficient xi p| ≤ Acoef) →
              |xi MomentCoord.physical| ≤ Aphys →
              ∀ i : Fin (M.cellCount + 1),
                |B.normalizedSquarefreeBandCovarianceRow
                    xi B.slowSquarefreeScore i -
                  B.referenceSlowRow i| ≤
                    r * B.w * B.bandCenter i := by
  obtain ⟨CKernel, hCKernel, hKernelBound⟩ :=
    exists_covarianceKernel_abs_le_second
  let W₀ : ℕ := max 2
    (max RegularMeshPrimeCutoffs.canonicalActualMomentCutoff
      (max RegularMeshPrimeCutoffs.canonicalCenterEnvelopeCutoff
        RegularMeshPrimeCutoffs.canonicalNonstepLocalDiagonalCutoff))
  refine ⟨W₀, ?_⟩
  intro W hW delta eta hdelta M Head _instFintype _instDecidable
    _instNonempty Phead hhead I Cmax hlowerOne hupperMax
    Cprom Cbank ledger Acoef Aphys hAcoef hAphys r hr
  have hWone : 1 < W := by
    dsimp only [W₀] at hW
    omega
  have hWmoment :
      RegularMeshPrimeCutoffs.canonicalActualMomentCutoff ≤ W := by
    dsimp only [W₀] at hW
    omega
  have hWcenter :
      RegularMeshPrimeCutoffs.canonicalCenterEnvelopeCutoff ≤ W := by
    dsimp only [W₀] at hW
    omega
  have hWlocal :
      RegularMeshPrimeCutoffs.canonicalNonstepLocalDiagonalCutoff ≤ W := by
    dsimp only [W₀] at hW
    omega
  have hHeadLe : ∀ h, ∀ p ∈ (Phead h).primes, p ≤ W := by
    intro h p hp
    exact (hhead h p).mp hp |>.2
  obtain ⟨profileError, hprofile0, hprofileT, hprofileRate,
      Nprofile, hprofile⟩ :=
    exists_boxIndependent_actual_component_signed_profiles
      Phead I Cmax hlowerOne hupperMax Cprom Cbank ledger
        W hWone hHeadLe Acoef Aphys hAcoef hAphys
  let Calpha : ℝ :=
    RegularMeshPrimeCutoffs.canonicalCenterEnvelopeConstant delta
  let Ctail : ℝ :=
    (1 / DickmanBasic.rho DickmanBasic.U + 2) ^ 2 + CKernel + 1
  have hCtail : 0 < Ctail := by
    dsimp only [Ctail]
    have hrho : 0 < 1 / DickmanBasic.rho DickmanBasic.U :=
      one_div_pos.mpr DickmanBasic.rho_U_pos
    positivity
  let localRequest : ℝ := r / (3 * Ctail)
  have hlocalRequest : 0 < localRequest := by
    dsimp only [localRequest]
    positivity
  have hCovRate :=
    tendsto_pairCovarianceScale_mul_logL_zero
      profileError hprofileT hprofileRate
  have hOffRate : Tendsto
      (fun n : ℕ ↦
        28 * pairCovarianceScale (profileError n) * Calpha *
          Real.log (Scale.L n)) atTop (nhds 0) := by
    have hraw := (tendsto_const_nhds : Tendsto
      (fun _n : ℕ ↦ 28 * Calpha) atTop (nhds (28 * Calpha))).mul
        hCovRate
    convert hraw using 1
    · funext n
      ring
    · ring
  have hDiagRate : Tendsto (fun n : ℕ ↦ 4 * profileError n)
      atTop (nhds 0) := by
    simpa only [mul_zero] using
      (tendsto_const_nhds.mul hprofileT : Tendsto
        (fun n : ℕ ↦ (4 : ℝ) * profileError n) atTop (nhds (4 * 0)))
  have hOffSmall : ∀ᶠ n : ℕ in atTop,
      28 * pairCovarianceScale (profileError n) * Calpha *
          Real.log (Scale.L n) < r / 3 :=
    hOffRate.eventually (eventually_lt_nhds (by positivity))
  have hDiagSmall : ∀ᶠ n : ℕ in atTop,
      4 * profileError n < r * delta / 3 :=
    hDiagRate.eventually (eventually_lt_nhds (by positivity))
  have hProfileOne : ∀ᶠ n : ℕ in atTop, profileError n < 1 :=
    hprofileT.eventually (eventually_lt_nhds (by norm_num))
  have hMoment :=
    RegularMeshPrimeCutoffs.Mesh.canonicalActualFirstMomentCutoff_eventually
      M hdelta W hWmoment
  have hCenter :=
    RegularMeshPrimeCutoffs.Mesh.canonicalCenterEnvelopeCutoff_eventually_inverse
      M hdelta W hWcenter
  have hLocal :=
    RegularMeshPrimeCutoffs.Mesh.canonicalNonstepLocalDiagonalCutoff_eventually
      M hdelta W hWlocal hlocalRequest
  filter_upwards [hOffSmall, hDiagSmall, hProfileOne, hMoment,
    hCenter, hLocal, eventually_ge_atTop Nprofile] with
      n hOffN hDiagN hProfileOneN hMomentN hCenterN hLocalN hnProfile
  intro B hBn hBW hsep hremaining hcanonical hpartition hscale
    xi hetaCoeff hphysical i
  subst n
  subst W
  obtain ⟨_hWmoment, _hnMoment, hMomentAll⟩ := hMomentN
  obtain ⟨hWne, S, hpartitionUser⟩ := hpartition
  let Pcanonical :=
    RegularMeshPrimeCutoffs.Mesh.canonicalPartition M hdelta
      B.n_gt_one hWne S
  have hpartitionCanonical : B.partition = Pcanonical := by
    exact hpartitionUser.trans (by rfl)
  obtain ⟨_devSupRaw, hdevL1Raw⟩ := hMomentAll S
  have hdevL1 : B.primeDeviationL1 ≤ 7 * B.w := by
    change B.partition.totalL1 ≤ 7 * B.w
    rw [hpartitionCanonical]
    calc
      Pcanonical.totalL1 ≤ 7 * (delta + M.ratio) := by
        simpa only [Pcanonical] using hdevL1Raw
      _ ≤ 7 * B.w := by
        rw [hscale]
        nlinarith [M.ratio_le_eta]
  have hPattern : B.sampleData.pattern = Phead := by
    rw [hcanonical]
    rfl
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
  have hGuards : B.sampleData.guards =
      (ledger B.sampleData.n).guards := by
    rw [hcanonical]
    rfl
  obtain ⟨hpair, hsingle⟩ := hprofile B xi hnProfile
    hPattern hLo hHi hGuards hetaCoeff hphysical rfl
  have hKernel : ∀ p ∈
      primeBand B.sampleData.n B.sampleData.W,
      |ConditionedPoissonLimit.covarianceKernel
        (tPrime B.sampleData.n p) (tPrime B.sampleData.n p)| ≤
          CKernel := by
    intro p hp
    let p' : PrimeIndex B.sampleData.n B.sampleData.W := ⟨p, hp⟩
    have ht := tPrime_mem_unit B.n_gt_one p'
    calc
      |ConditionedPoissonLimit.covarianceKernel
          (tPrime B.sampleData.n p) (tPrime B.sampleData.n p)| ≤
        CKernel * tPrime B.sampleData.n p :=
          hKernelBound _ ht _ ht
      _ ≤ CKernel := by
        exact mul_le_of_le_one_right hCKernel ht.2
  let weight := tiltedSigmaWeight B.baselineCellProbability
    B.guardedCellProbability (B.scaledBridgeScore xi)
  have hentryMix :=
    sigmaMixture_squarefree_reference_entry_bound_of_squarefree_profiles
      (hprofile0 B.sampleData.n) weight
      (B.actualComponentValuationLaw xi) B.n_gt_one
      hpair hsingle hKernel
  have hlaw :=
    B.sigmaMixture_actualComponentValuationLaw_eq_actualValuationLaw xi
  dsimp only at hentryMix hlaw
  rw [hlaw] at hentryMix
  let E : ℝ := profileError B.sampleData.n
  let eOff : ℝ := 4 * pairCovarianceScale E
  let eDiag : ℝ := 2 * E
  let cDiag : ℝ :=
    (1 / DickmanBasic.rho DickmanBasic.U + 2 * E) ^ 2 + CKernel
  have hE : 0 ≤ E := by
    simpa only [E] using hprofile0 B.sampleData.n
  have heOff : 0 ≤ eOff := by
    dsimp only [eOff]
    exact mul_nonneg (by norm_num) (pairCovarianceScale_nonneg hE)
  have heDiag : 0 ≤ eDiag := by
    dsimp only [eDiag]
    positivity
  have hentry : ∀ p q :
      BandPrime B.sampleData.n B.sampleData.W,
      |(B.actualValuationLaw xi).covII p.1 q.1 -
          squarefreeReferenceEntry B.sampleData.n p.1 q.1| ≤
        eOff / ((p.1 : ℝ) * (q.1 : ℝ)) +
          (if p = q then
            eDiag / (p.1 : ℝ) + cDiag / (p.1 : ℝ) ^ 2
          else 0) := by
    simpa only [E, eOff, eDiag, cDiag] using hentryMix
  have hraw :=
    B.abs_squarefreeSlowRow_sub_referenceSlowRow_le
      xi heOff heDiag hentry hdevL1 i
  have hcenterInv : 1 / B.bandCenter i ≤
      Calpha * Real.log (Scale.L B.sampleData.n) := by
    change 1 / B.partition.center i ≤ _
    rw [hpartitionUser]
    simpa only [Calpha] using hCenterN B.n_gt_one hWne S i
  have hcenter : 0 < B.bandCenter i := B.bandCenter_pos i
  have hw : 0 < B.w := by
    rw [hscale]
    exact add_pos hdelta (lt_of_lt_of_le M.ratio_pos M.ratio_le_eta)
  have hdeltaW : delta ≤ B.w := by
    rw [hscale]
    linarith [M.ratio_pos, M.ratio_le_eta]
  have hunit : 1 ≤
      (Calpha * Real.log (Scale.L B.sampleData.n)) *
        B.bandCenter i := by
    exact (div_le_iff₀ hcenter).mp hcenterInv
  have hOffTerm : 7 * eOff * B.w ≤
      (r / 3) * B.w * B.bandCenter i := by
    have hcoeff : 0 ≤ 28 * pairCovarianceScale E * B.w := by
      exact mul_nonneg
        (mul_nonneg (by norm_num) (pairCovarianceScale_nonneg hE)) hw.le
    calc
      7 * eOff * B.w =
          (28 * pairCovarianceScale E * B.w) * 1 := by
        dsimp only [eOff]
        ring
      _ ≤ (28 * pairCovarianceScale E * B.w) *
          ((Calpha * Real.log (Scale.L B.sampleData.n)) *
            B.bandCenter i) :=
        mul_le_mul_of_nonneg_left hunit hcoeff
      _ = (28 * pairCovarianceScale E * Calpha *
          Real.log (Scale.L B.sampleData.n)) * B.w *
            B.bandCenter i := by ring
      _ ≤ (r / 3) * B.w * B.bandCenter i := by
        have hOffN' :
            28 * pairCovarianceScale E * Calpha *
                Real.log (Scale.L B.sampleData.n) ≤ r / 3 := by
          simpa only [E] using hOffN.le
        have hmul := mul_le_mul_of_nonneg_right hOffN'
          (mul_nonneg hw.le hcenter.le)
        simpa only [mul_assoc] using hmul
  have hDiagTerm : 2 * eDiag * B.bandCenter i ≤
      (r / 3) * B.w * B.bandCenter i := by
    have hcoef : 4 * E ≤ (r / 3) * B.w := by
      calc
        4 * E ≤ r * delta / 3 := hDiagN.le
        _ ≤ (r / 3) * B.w := by
          nlinarith
    have hcoef' : 2 * eDiag ≤ (r / 3) * B.w := by
      dsimp only [eDiag]
      nlinarith
    exact mul_le_mul_of_nonneg_right hcoef' hcenter.le
  have hEOne : E ≤ 1 := by
    simpa only [E] using hProfileOneN.le
  have hcDiagLe : cDiag ≤ Ctail := by
    have hrho : 0 < 1 / DickmanBasic.rho DickmanBasic.U :=
      one_div_pos.mpr DickmanBasic.rho_U_pos
    have hbase :
        1 / DickmanBasic.rho DickmanBasic.U + 2 * E ≤
          1 / DickmanBasic.rho DickmanBasic.U + 2 := by
      nlinarith
    have hbase0 : 0 ≤
        1 / DickmanBasic.rho DickmanBasic.U + 2 * E := by
      positivity
    have htop0 : 0 ≤
        1 / DickmanBasic.rho DickmanBasic.U + 2 := by
      positivity
    have hsq := (sq_le_sq₀ hbase0 htop0).2 hbase
    dsimp only [cDiag, Ctail]
    nlinarith
  have hD : B.bandDeviationReciprocalSquare i ≤
      localRequest * B.w * B.bandCenter i := by
    change B.partition.normalizedDeviationReciprocalSquare i ≤
      localRequest * B.w * B.partition.center i
    rw [hpartitionUser]
    have hactual := hLocalN B.n_gt_one hWne S i
    calc
      (RegularMeshPrimeCutoffs.Mesh.canonicalPartition M hdelta
          B.n_gt_one hWne S).normalizedDeviationReciprocalSquare i ≤
          localRequest * (delta + M.ratio) *
            (RegularMeshPrimeCutoffs.Mesh.canonicalPartition M hdelta
              B.n_gt_one hWne S).center i := hactual
      _ ≤ localRequest * B.w *
            (RegularMeshPrimeCutoffs.Mesh.canonicalPartition M hdelta
              B.n_gt_one hWne S).center i := by
        have hscale' : delta + M.ratio ≤ B.w := by
          rw [hscale]
          linarith [M.ratio_le_eta]
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hscale' hlocalRequest.le)
          ((RegularMeshPrimeCutoffs.Mesh.canonicalPartition M hdelta
            B.n_gt_one hWne S).center_pos B.n_gt_one i).le
  have hD0 : 0 ≤ B.bandDeviationReciprocalSquare i := by
    unfold bandDeviationReciprocalSquare
    apply mul_nonneg
    · exact one_div_nonneg.mpr (B.harmonicMass_pos i).le
    · exact Finset.sum_nonneg fun p _hp ↦
        mul_nonneg (abs_nonneg _) (sq_nonneg _)
  have hLocalTerm : cDiag * B.bandDeviationReciprocalSquare i ≤
      (r / 3) * B.w * B.bandCenter i := by
    calc
      cDiag * B.bandDeviationReciprocalSquare i ≤
          Ctail * B.bandDeviationReciprocalSquare i :=
        mul_le_mul_of_nonneg_right hcDiagLe hD0
      _ ≤ Ctail * (localRequest * B.w * B.bandCenter i) :=
        mul_le_mul_of_nonneg_left hD hCtail.le
      _ = (r / 3) * B.w * B.bandCenter i := by
        dsimp only [localRequest]
        field_simp [hCtail.ne']
  exact hraw.trans (by
    have := add_le_add (add_le_add hOffTerm hDiagTerm) hLocalTerm
    nlinarith)

end BridgeData

end

end Erdos390.Full.PaperBridgeFit

end

universe u_1
theorem solution : Erdos390.RemainingAnalyticGoal002_003.{u_1} := by
  exact @Erdos390.Full.PaperBridgeFit.BridgeData.exists_global_cutoff_eventually_canonical_squarefreeSlowRow_sub_reference
