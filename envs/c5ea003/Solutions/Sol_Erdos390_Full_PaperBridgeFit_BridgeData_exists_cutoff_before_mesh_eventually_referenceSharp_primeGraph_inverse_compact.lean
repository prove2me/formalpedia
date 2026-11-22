-- Prove2me | solution 1 for Erdos390.Full.PaperBridgeFit.BridgeData.exists_cutoff_before_mesh_eventually_referenceSharp_primeGraph_inverse_compact
-- status  : ACCEPTED   (prove)
-- author  : @doctosil
-- created : 2026-09-17T17:09:24.674974+00:00
-- url     : https://prove2.me/submissions/c6260bd7-d2aa-4c09-a320-31f9bb4d0f75

import Definitions.Def_erdos390_remaining_analytic_propositions_001
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
import Theorems.Thm_Erdos390_Full_PaperBridgeFit_BridgeData_exists_referenceSharpProjectedEquiv_of_primeGraph
import Theorems.Thm_Erdos390_Full_PaperCanonicalPrimeRowResidualEventually_abs_firstMomentWeightedAbelRemainder_le
import Theorems.Thm_Erdos390_Full_PaperCanonicalPrimeRowResidualEventually_abs_primeRowResidual_le_of_relative_quadrature
import Theorems.Thm_Erdos390_Full_RegularMeshPrimeCutoffs_Mesh_canonicalPrimeAnchorCutoff_eventually
import Theorems.Thm_Erdos390_Full_RegularMeshPrimeCutoffs_Mesh_momentReady_of_endpointMomentBounds

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

/- Source module: Erdos390.Full.ConditionedPoissonLimit -/
section


/-!
# Exact analytic identities for the Poisson--Dickman bridge

This file continues the explicit finite-cutoff construction in
`ConditionedPoisson`.  The first layer below isolates the identities which
are needed by the covariance operator and proves them directly from the
method-of-steps Dickman equation.  In particular, the fact that the scale
function `t` is a null direction is not postulated.

The probability-theoretic exact-total projective limit is kept separate from
these analytic identities: this prevents a choice of a regular conditional
law on a null fibre from silently entering the operator calculation.
-/

open Filter Set
open scoped Interval BigOperators ENNReal NNReal

noncomputable section

namespace Erdos390.Full.ConditionedPoissonLimit

open MeasureTheory ProbabilityTheory Real
open DickmanBasic

/-! ## A global method-of-steps Dickman function -/













































































lemma covarianceKernel_comm (s t : ℝ) :
    covarianceKernel s t = covarianceKernel t s := by
  unfold covarianceKernel
  rw [add_comm]
  ring

















/-! ## Density-weighted Palm moments and covariance -/



lemma continuous_covarianceKernel :
    Continuous (Function.uncurry covarianceKernel) := by
  unfold covarianceKernel Function.uncurry
  exact (continuous_F.comp (continuous_fst.add continuous_snd)).sub
    ((continuous_F.comp continuous_fst).mul (continuous_F.comp continuous_snd))

/-! ## The removable axis singularity and a continuous kernel representative -/

















































/-! ## The measurable Cauchy endpoint of the kernel argument -/





/-! The Palm argument produces additivity first on the positive triangle.
The following deterministic lemma records that no global Cauchy equation is
needed: continuity on the closed unit interval and local additivity already
force one common slope. -/







end Erdos390.Full.ConditionedPoissonLimit

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

/-- By symmetry the same constant gives linear vanishing in the first
coordinate. -/
theorem exists_covarianceKernel_abs_le_first :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
      |covarianceKernel s t| ≤ C * s := by
  obtain ⟨C, hCnonneg, hC⟩ := exists_covarianceKernel_abs_le_second
  refine ⟨C, hCnonneg, ?_⟩
  intro s hs t ht
  rw [covarianceKernel_comm]
  exact hC t ht s hs

end Erdos390.Full.PoissonDickmanKernelBounds

end

/- Source module: Erdos390.Full.KernelPrimeQuadrature -/
section


/-!
# Weighted prime quadrature for the Poisson--Dickman kernel

This file generalizes the scalar Abel summation used for `H_j` to a smooth
test function on logarithmic prime coordinates.  The first layer is an exact
finite identity for the actual primes; later declarations specialize it to
the Poisson--Dickman covariance kernel and its compact derivative bounds.
-/

open scoped BigOperators
open Set

noncomputable section

namespace Erdos390.Full.KernelPrimeQuadrature

open MeasureTheory
open ArithmeticModel PrimeSums PrimeBandQuadrature
open DickmanBasic ConditionedPoissonLimit





lemma continuous_covarianceKernelDerivativeSecondExtension_left (s : ℝ) :
    Continuous (covarianceKernelDerivativeSecondExtension s) := by
  unfold covarianceKernelDerivativeSecondExtension
  exact (continuous_derivFExtension.comp
      (continuous_const.add continuous_id)).sub
    (continuous_const.mul continuous_derivFExtension)





lemma covarianceKernelDerivativeSecondExtension_eq {s t : ℝ}
    (hs : s ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1) :
    covarianceKernelDerivativeSecondExtension s t =
      covarianceKernelDerivativeSecond s t := by
  have hst : s + t ∈ Icc (0 : ℝ) 2 := by
    constructor <;> linarith [hs.1, hs.2, ht.1, ht.2]
  unfold covarianceKernelDerivativeSecondExtension
  unfold covarianceKernelDerivativeSecond
  rw [derivFExtension_eq_deriv_of_mem hst,
    derivFExtension_eq_deriv_of_mem
      ⟨ht.1, ht.2.trans (by norm_num)⟩]

lemma continuous_covarianceKernel_left (s : ℝ) :
    Continuous (covarianceKernel s) := by
  exact continuous_covarianceKernel.comp
    (continuous_const.prodMk continuous_id)

lemma hasDerivAt_covarianceKernel_second {s t : ℝ}
    (hs : s ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1) :
    HasDerivAt (covarianceKernel s)
      (covarianceKernelDerivativeSecond s t) t := by
  have ht₂ : t ∈ Icc (0 : ℝ) 2 :=
    ⟨ht.1, ht.2.trans (by norm_num)⟩
  have hst₂ : s + t ∈ Icc (0 : ℝ) 2 := by
    constructor <;> linarith [hs.1, hs.2, ht.1, ht.2]
  have hshift : HasDerivAt (fun u : ℝ => s + u) 1 t := by
    simpa only [zero_add] using
      (hasDerivAt_const t s).add (hasDerivAt_id t)
  have hfirst := (differentiableAt_F hst₂).hasDerivAt.comp t hshift
  have hsecond := (differentiableAt_F ht₂).hasDerivAt.const_mul (F s)
  convert hfirst.sub hsecond using 1
  unfold covarianceKernelDerivativeSecond
  ring



lemma realLogCoordinate_mem_unit {z x : ℝ}
    (hz : 1 < z) (hx : 1 ≤ x) (hxz : x ≤ z) :
    realLogCoordinate z x ∈ Icc (0 : ℝ) 1 := by
  have hlogzpos : 0 < Real.log z := Real.log_pos hz
  have hlogxnonneg : 0 ≤ Real.log x := Real.log_nonneg hx
  have hlogxz : Real.log x ≤ Real.log z :=
    Real.log_le_log (zero_lt_one.trans_le hx) hxz
  unfold realLogCoordinate
  constructor
  · exact div_nonneg hlogxnonneg hlogzpos.le
  · exact (div_le_one hlogzpos).2 hlogxz





































































end Erdos390.Full.KernelPrimeQuadrature

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

























end

end Erdos390.Full.ArithmeticBandGeometry.Partition

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

/- Source module: Erdos390.Full.PaperCanonicalSlowKappa -/
section


/-!
# A fixed slow-direction Dickman gap

The compact interior anchor is always taken in `[1/8,7/8]`.  Hence its
Dickman quotient gap must be selected once, before `n`, the arithmetic mesh,
and every tilt parameter.  This file exposes that fixed choice and threads
it through the exact prime Dirichlet and squarefree lower bounds.
-/

open scoped BigOperators
open Set

noncomputable section

namespace Erdos390.Full.PaperCanonicalSlowKappa

open ArithmeticModel ArithmeticBandGeometry
open ConditionedPoissonLimit PoissonDickmanWeightedInverse
open PoissonDickmanDirichlet OmittedTiltPairChamber
open PrimeSquarefreeDirichletGeometry
open FiniteAnchoredDirichletQuadratic
open PaperSquarefreeSlowQuadraticLower
open PaperBridgeFit PaperBridgeFit.BridgeData
open PaperPrimePowerChamberError
open PaperWeightedInverseExport
open FiniteSignedQuadraticEntryTransfer
open SquarefreeCovarianceReference
open PrimePowerCovariance



theorem canonicalSlowKappa_pos : 0 < canonicalSlowKappa :=
  (Classical.choose_spec
    (exists_transposeQuotient_uniform_gap
      (epsilon := (1 / 8 : ℝ)) (by norm_num) (by norm_num))).1







end Erdos390.Full.PaperCanonicalSlowKappa

namespace Erdos390.Full.PaperBridgeFit.BridgeData

open ArithmeticModel ArithmeticBandGeometry
open ConditionedPoissonLimit OmittedTiltPairChamber
open PrimeSquarefreeDirichletGeometry FiniteAnchoredDirichletQuadratic
open PaperSquarefreeSlowQuadraticLower PaperPrimePowerChamberError
open PaperWeightedInverseExport FiniteSignedQuadraticEntryTransfer
open SquarefreeCovarianceReference PrimePowerCovariance
open PaperCanonicalSlowKappa

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]
  (B : BridgeData Head Band)





end Erdos390.Full.PaperBridgeFit.BridgeData

end

end

/- Source module: Erdos390.Full.PaperCanonicalPrimeRowResidualEventually -/
section


/-!
# Relative prime-row residual for the squarefree Dickman reference

The prime-level anchored Dirichlet proof needs a *relative* row estimate.
An additive estimate for the Dickman kernel is not enough when the marked
prime coordinate tends to zero.  We therefore apply weighted Abel summation
to

`phi_s(t) = t * K(s,t)`.

Both `phi_s` and its derivative in `t` are `O(s)` uniformly on the unit
square.  Consequently the PNT remainder is `O(s / log(W)^3)`.  Kernel
symmetry and the removable quotient row-sum identity then turn this into the
literal bound

`|R_p| <= (D / log(W)^3 + two endpoint tails) * t_p`.

All constants below are chosen before `W`, the ambient integer, and the
marked prime.
-/

open scoped BigOperators
open Set Filter Topology

noncomputable section

namespace Erdos390.Full.PaperCanonicalPrimeRowResidualEventually

open ArithmeticModel PrimeSums PrimeBandQuadrature
open KernelPrimeQuadrature ConditionedPoissonLimit DickmanBasic
open PrimeSquarefreeDirichletGeometry FiniteAnchoredDirichletQuadratic
open MeasureTheory
open DoubleKernelPrimeQuadrature





lemma continuous_firstMomentKernel (s : ℝ) :
    Continuous (firstMomentKernel s) := by
  exact continuous_id.mul (continuous_covarianceKernel_left s)

lemma continuous_firstMomentKernelDerivative (s : ℝ) :
    Continuous (firstMomentKernelDerivative s) := by
  exact (continuous_covarianceKernel_left s).add
    (continuous_id.mul
      (continuous_covarianceKernelDerivativeSecondExtension_left s))

lemma hasDerivAt_firstMomentKernel_second {s t : ℝ}
    (hs : s ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1) :
    HasDerivAt (firstMomentKernel s)
      (firstMomentKernelDerivative s t) t := by
  have hK := hasDerivAt_covarianceKernel_second hs ht
  have hExt := covarianceKernelDerivativeSecondExtension_eq hs ht
  simpa only [firstMomentKernel, firstMomentKernelDerivative, id_eq,
    one_mul, hExt] using (hasDerivAt_id t).mul hK





lemma hasDerivAt_firstMomentAbelCoefficient
    {s z x : ℝ} (hs : s ∈ Icc (0 : ℝ) 1)
    (hz : 1 < z) (hx : 1 < x) (hxz : x ≤ z) :
    HasDerivAt (firstMomentAbelCoefficient s z)
      (firstMomentAbelDerivative s z x) x := by
  have ht := realLogCoordinate_mem_unit hz hx.le hxz
  exact hasDerivAt_weightedAbelCoefficient
    (firstMomentKernel s) (firstMomentKernelDerivative s) hz hx
      (hasDerivAt_firstMomentKernel_second hs ht)

lemma deriv_firstMomentAbelCoefficient
    {s z x : ℝ} (hs : s ∈ Icc (0 : ℝ) 1)
    (hz : 1 < z) (hx : 1 < x) (hxz : x ≤ z) :
    deriv (firstMomentAbelCoefficient s z) x =
      firstMomentAbelDerivative s z x := by
  exact (hasDerivAt_firstMomentAbelCoefficient hs hz hx hxz).deriv

lemma continuousOn_firstMomentAbelDerivative
    (s z : ℝ) (hz : 1 < z) {A Y : ℝ} (hA : 1 < A) :
    ContinuousOn (firstMomentAbelDerivative s z) (Icc A Y) := by
  intro x hx
  exact continuousAt_weightedAbelCoefficientDerivative
    (firstMomentKernel s) (firstMomentKernelDerivative s)
    (continuous_firstMomentKernel s)
    (continuous_firstMomentKernelDerivative s) hz
      (hA.trans_le hx.1) |>.continuousWithinAt

lemma integrableOn_deriv_firstMomentAbelCoefficient
    {s z : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) (hz : 1 < z)
    {Y : ℕ} (hYz : (Y : ℝ) ≤ z) :
    IntegrableOn (deriv (firstMomentAbelCoefficient s z))
      (Icc (2 : ℝ) (Y : ℝ)) := by
  have hcont : ContinuousOn (firstMomentAbelDerivative s z)
      (Icc (2 : ℝ) (Y : ℝ)) :=
    continuousOn_firstMomentAbelDerivative s z hz (by norm_num)
  apply (hcont.integrableOn_Icc).congr_fun
  · intro x hx
    symm
    exact deriv_firstMomentAbelCoefficient hs hz
      (by linarith [hx.1]) (hx.2.trans hYz)
  · exact measurableSet_Icc

lemma intervalIntegrable_deriv_firstMoment_mul_theta
    {s z : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) (hz : 1 < z)
    {Y : ℕ} (hY : 2 ≤ Y) (hYz : (Y : ℝ) ≤ z) :
    IntervalIntegrable
      (fun x : ℝ => deriv (firstMomentAbelCoefficient s z) x *
        Chebyshev.theta x) volume (2 : ℝ) (Y : ℝ) := by
  have h2Y : (2 : ℝ) ≤ (Y : ℝ) := by exact_mod_cast hY
  have hbase := intervalIntegrable_continuous_mul_theta
    (g := firstMomentAbelDerivative s z) (A := (2 : ℝ))
    (Y := (Y : ℝ)) (by norm_num) h2Y
    (continuousOn_firstMomentAbelDerivative s z hz (by norm_num))
  apply hbase.congr
  intro x hx
  have hx' : x ∈ Ioc (2 : ℝ) (Y : ℝ) := by
    simpa only [uIoc_of_le h2Y] using hx
  change firstMomentAbelDerivative s z x * Chebyshev.theta x =
    deriv (firstMomentAbelCoefficient s z) x * Chebyshev.theta x
  congr 1
  exact (deriv_firstMomentAbelCoefficient hs hz
    (by linarith [hx'.1]) (hx'.2.trans hYz)).symm

lemma intervalIntegrable_deriv_firstMoment_mul_id
    {s z : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) (hz : 1 < z)
    {A Y : ℕ} (hA : 2 ≤ A) (hAY : A ≤ Y)
    (hYz : (Y : ℝ) ≤ z) :
    IntervalIntegrable
      (fun x : ℝ => deriv (firstMomentAbelCoefficient s z) x * x)
      volume (A : ℝ) (Y : ℝ) := by
  have hAR : (2 : ℝ) ≤ (A : ℝ) := by exact_mod_cast hA
  have hAYR : (A : ℝ) ≤ (Y : ℝ) := by exact_mod_cast hAY
  have hcont : ContinuousOn
      (fun x : ℝ => firstMomentAbelDerivative s z x * x)
      (Icc (A : ℝ) (Y : ℝ)) :=
    (continuousOn_firstMomentAbelDerivative s z hz (by linarith [hAR])).mul
      continuousOn_id
  have hbase := hcont.intervalIntegrable_of_Icc (μ := volume) hAYR
  apply hbase.congr
  intro x hx
  have hx' : x ∈ Ioc (A : ℝ) (Y : ℝ) := by
    simpa only [uIoc_of_le hAYR] using hx
  change firstMomentAbelDerivative s z x * x =
    deriv (firstMomentAbelCoefficient s z) x * x
  congr 1
  exact (deriv_firstMomentAbelCoefficient hs hz
    (by linarith [hAR, hx'.1]) (hx'.2.trans hYz)).symm

/-- Exact prime-cell identity before estimating the PNT remainder. -/
theorem firstMomentKernel_primeCell_sub_continuum_eq_remainder
    {s z : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) (hz : 1 < z)
    {A Y : ℕ} (hA : 2 ≤ A) (hAY : A ≤ Y)
    (hYz : (Y : ℝ) ≤ z) :
    fullWeightedReciprocalSum (firstMomentKernel s) z Y -
        fullWeightedReciprocalSum (firstMomentKernel s) z A -
        (∫ t in realLogCoordinate z (A : ℝ)..
          realLogCoordinate z (Y : ℝ), firstMomentKernel s t / t) =
      weightedAbelRemainder (firstMomentKernel s) z (A : ℝ) (Y : ℝ) := by
  have hY : 2 ≤ Y := hA.trans hAY
  have hAR : (2 : ℝ) ≤ (A : ℝ) := by exact_mod_cast hA
  have hAYR : (A : ℝ) ≤ (Y : ℝ) := by exact_mod_cast hAY
  have h2Y : (2 : ℝ) ≤ (Y : ℝ) := hAR.trans hAYR
  have hdiff : ∀ x ∈ Icc (2 : ℝ) (Y : ℝ),
      DifferentiableAt ℝ
        (weightedAbelCoefficient (firstMomentKernel s) z) x := by
    intro x hx
    change DifferentiableAt ℝ (firstMomentAbelCoefficient s z) x
    exact (hasDerivAt_firstMomentAbelCoefficient hs hz
      (by linarith [hx.1]) (hx.2.trans hYz)).differentiableAt
  have hint : IntegrableOn
      (deriv (weightedAbelCoefficient (firstMomentKernel s) z))
      (Icc (2 : ℝ) (Y : ℝ)) := by
    simpa only [firstMomentAbelCoefficient] using
      integrableOn_deriv_firstMomentAbelCoefficient hs hz hYz
  have hThetaInt : IntervalIntegrable
      (fun x : ℝ =>
        deriv (weightedAbelCoefficient (firstMomentKernel s) z) x *
          Chebyshev.theta x) volume (2 : ℝ) (Y : ℝ) := by
    simpa only [firstMomentAbelCoefficient] using
      intervalIntegrable_deriv_firstMoment_mul_theta hs hz hY hYz
  have hMainInt : IntervalIntegrable
      (fun x : ℝ =>
        deriv (weightedAbelCoefficient (firstMomentKernel s) z) x * x)
      volume (A : ℝ) (Y : ℝ) := by
    simpa only [firstMomentAbelCoefficient] using
      intervalIntegrable_deriv_firstMoment_mul_id hs hz hA hAY hYz
  have hErrorInt : IntervalIntegrable
      (fun x : ℝ =>
        deriv (weightedAbelCoefficient (firstMomentKernel s) z) x * thetaError x)
      volume (A : ℝ) (Y : ℝ) := by
    have hThetaCell : IntervalIntegrable
        (fun x : ℝ =>
          deriv (weightedAbelCoefficient (firstMomentKernel s) z) x *
            Chebyshev.theta x) volume (A : ℝ) (Y : ℝ) := by
      apply hThetaInt.mono_set
      rw [uIcc_of_le hAYR, uIcc_of_le h2Y]
      intro x hx
      exact ⟨hAR.trans hx.1, hx.2⟩
    have hsub := hThetaCell.sub hMainInt
    apply hsub.congr
    intro x hx
    unfold thetaError
    ring
  have hdecomp :=
    fullWeightedReciprocalSum_interval_sub_main_eq_remainder
      (firstMomentKernel s) z hA hAY hdiff hint hThetaInt hMainInt hErrorInt
  rw [weightedAbelMain_eq_logCoordinateIntegral
    (firstMomentKernel s) (continuous_firstMomentKernel s)
    hz hA hAY hdiff hint] at hdecomp
  exact hdecomp











/-- Box-independent, relative one-index quadrature for the exact test
function occurring in the prime row. -/
theorem exists_uniform_firstMomentKernel_primeCell_relative_bound :
    ∃ D : ℝ, 0 < D ∧ ∃ X₀ : ℕ,
      ∀ s ∈ Icc (0 : ℝ) 1, ∀ z : ℝ, 1 < z →
      ∀ A Y : ℕ, X₀ ≤ A → A ≤ Y → (Y : ℝ) ≤ z →
        |fullWeightedReciprocalSum (firstMomentKernel s) z Y -
            fullWeightedReciprocalSum (firstMomentKernel s) z A -
            (∫ t in realLogCoordinate z (A : ℝ)..
              realLogCoordinate z (Y : ℝ), firstMomentKernel s t / t)| ≤
          (D / Real.log (A : ℝ) ^ 3) * s := by
  obtain ⟨Ctheta, hCtheta, Xtheta, hTheta⟩ :=
    exists_thetaError_log_cube_bound
  obtain ⟨Ckernel, hCkernel, hKernelProduct⟩ := kernel_product_bound
  obtain ⟨Cderiv, hCderiv, hDerivative⟩ :=
    kernel_secondDerivative_first_bound
  let M : ℝ := Ckernel + Cderiv
  have hM : 0 < M := add_pos hCkernel hCderiv
  have hPhi : ∀ u ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
      |firstMomentKernel u t| ≤ M * u := by
    intro u hu t ht
    have hK : |covarianceKernel u t| ≤ Ckernel * u * t := by
      simpa only [covarianceKernel] using hKernelProduct u hu t ht
    rw [firstMomentKernel, abs_mul, abs_of_nonneg ht.1]
    calc
      t * |covarianceKernel u t| ≤ t * (Ckernel * u * t) :=
        mul_le_mul_of_nonneg_left hK ht.1
      _ = (Ckernel * u) * t ^ 2 := by ring
      _ ≤ (Ckernel * u) * 1 := by
        apply mul_le_mul_of_nonneg_left _
          (mul_nonneg hCkernel.le hu.1)
        nlinarith [mul_nonneg ht.1 (sub_nonneg.mpr ht.2)]
      _ ≤ M * u := by
        dsimp only [M]
        nlinarith [mul_nonneg hCderiv.le hu.1]
  have hPhiPrime : ∀ u ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
      |firstMomentKernelDerivative u t| ≤ M * u := by
    intro u hu t ht
    have hK : |covarianceKernel u t| ≤ Ckernel * u * t := by
      simpa only [covarianceKernel] using hKernelProduct u hu t ht
    have hExt := covarianceKernelDerivativeSecondExtension_eq hu ht
    have hD : |covarianceKernelDerivativeSecondExtension u t| ≤
        Cderiv * u := by
      rw [hExt]
      exact hDerivative u hu t ht
    unfold firstMomentKernelDerivative
    calc
      |covarianceKernel u t +
          t * covarianceKernelDerivativeSecondExtension u t| ≤
        |covarianceKernel u t| +
          |t * covarianceKernelDerivativeSecondExtension u t| :=
        abs_add_le _ _
      _ = |covarianceKernel u t| +
          t * |covarianceKernelDerivativeSecondExtension u t| := by
        rw [abs_mul, abs_of_nonneg ht.1]
      _ ≤ Ckernel * u * t + t * (Cderiv * u) := by
        exact add_le_add hK (mul_le_mul_of_nonneg_left hD ht.1)
      _ ≤ M * u := by
        dsimp only [M]
        have hk : Ckernel * u * t ≤ Ckernel * u := by
          exact mul_le_of_le_one_right
            (mul_nonneg hCkernel.le hu.1) ht.2
        have hd : t * (Cderiv * u) ≤ Cderiv * u := by
          rw [mul_comm]
          exact mul_le_of_le_one_right
            (mul_nonneg hCderiv.le hu.1) ht.2
        linarith
  obtain ⟨N, hN⟩ := exists_nat_gt Xtheta
  let D : ℝ := 6 * (Ctheta * M)
  refine ⟨D, by dsimp only [D]; positivity, max N 2, ?_⟩
  intro s hs z hz A Y hA hAY hYz
  have hA2 : 2 ≤ A := (le_max_right N 2).trans hA
  have hNA : N ≤ A := (le_max_left N 2).trans hA
  have hThetaCell : ∀ x ∈ Icc (A : ℝ) (Y : ℝ),
      |thetaError x| ≤ Ctheta * x / Real.log x ^ 3 := by
    intro x hx
    apply hTheta x
    exact le_trans (le_of_lt hN) (by exact_mod_cast hNA) |>.trans hx.1
  rw [firstMomentKernel_primeCell_sub_continuum_eq_remainder
    hs hz hA2 hAY hYz]
  have hbound := abs_firstMomentWeightedAbelRemainder_le
    hCtheta.le hM.le hs hz hA2 hAY hYz hPhi hPhiPrime hThetaCell
  calc
    _ ≤ 6 * (Ctheta * M) * s / Real.log (A : ℝ) ^ 3 := hbound
    _ = (D / Real.log (A : ℝ) ^ 3) * s := by
      dsimp only [D]
      ring















/-- Uniform literal prime-row theorem.  The constant multiplying
`log(W)^{-3}` is selected before the cutoff and before the ambient integer. -/
theorem exists_uniform_primeRowResidual_relative_bound :
    ∃ D : ℝ, 0 < D ∧ ∃ C : ℝ, 0 < C ∧ ∃ X₀ : ℕ,
      ∀ {n W : ℕ}, 1 < n → X₀ ≤ W → W ≤ yNat n →
        ∀ p : PrimeIndex n W,
          |rowResidual (primeWeight n) (primeDiagonal n) (primeKernel n) p| ≤
            primeRowRelativeError D C n W * tPrime n p.1 := by
  obtain ⟨D, hD, Xquad, hquad⟩ :=
    exists_uniform_firstMomentKernel_primeCell_relative_bound
  obtain ⟨C, hC, hKernel⟩ := kernel_product_bound
  refine ⟨D, hD, C, hC, max Xquad 2, ?_⟩
  intro n W hn hW hWY p
  have hW2 : 2 ≤ W := (le_max_right Xquad 2).trans hW
  have hXquad : Xquad ≤ W := (le_max_left Xquad 2).trans hW
  have hy : 1 < y n := by
    have hlog : 0 < Real.log (y n) := by
      rw [Scale.log_y (Nat.zero_lt_of_lt hn)]
      exact mul_pos (by norm_num) (Real.log_pos (by exact_mod_cast hn))
    exact (Real.log_pos_iff (Scale.y_pos
      (Nat.zero_lt_of_lt hn)).le).mp hlog
  have hyNatY : (yNat n : ℝ) ≤ y n :=
    Nat.floor_le (Scale.y_pos (Nat.zero_lt_of_lt hn)).le
  have hrelative : ∀ s ∈ Icc (0 : ℝ) 1,
      |primeCellOperator (y n) W (yNat n) (firstMomentKernel s) -
          (∫ t in realLogCoordinate (y n) (W : ℝ)..
            realLogCoordinate (y n) (yNat n : ℝ),
              firstMomentKernel s t / t)| ≤
        (D / Real.log (W : ℝ) ^ 3) * s := by
    intro s hs
    simpa only [primeCellOperator] using
      hquad s hs (y n) hy W (yNat n) hXquad hWY hyNatY
  exact abs_primeRowResidual_le_of_relative_quadrature hC.le hn hW2 hWY
    (by
      intro u hu t ht
      simpa only [covarianceKernel] using hKernel u hu t ht)
    hrelative p

theorem tendsto_primeRowRelativeError_fixedCutoff
    (D C : ℝ) (W : ℕ) :
    Tendsto (fun n : ℕ ↦ primeRowRelativeError D C n W)
      atTop (nhds (D / Real.log (W : ℝ) ^ 3)) := by
  have hbase : Tendsto (fun n : ℕ ↦
      realLogCoordinate (y n) (W : ℝ)) atTop (nhds 0) := by
    simpa only using
      _root_.Erdos390.Full.RegularMeshPrimeCutoffs.Mesh.tendsto_fixed_cutoffCoordinate_zero W
  have htopRaw :=
    _root_.Erdos390.Full.RegularMeshPrimeCutoffs.Mesh.tendsto_floor_scalePoint_coordinate
      (t := (1 : ℝ)) (by norm_num)
  have htop : Tendsto (fun n : ℕ ↦
      realLogCoordinate (y n) (yNat n : ℝ)) atTop (nhds 1) := by
    apply htopRaw.congr'
    filter_upwards [eventually_gt_atTop 0] with n hn
    unfold yNat RegularMeshPrimeCutoffs.scalePoint
    rw [one_mul, Real.exp_log (Scale.y_pos hn)]
  have htail : Tendsto (fun n : ℕ ↦
      realLogCoordinate (y n) (W : ℝ) +
        (1 - realLogCoordinate (y n) (yNat n : ℝ)))
      atTop (nhds 0) := by
    simpa only [sub_self, add_zero] using
      hbase.add ((tendsto_const_nhds : Tendsto
        (fun _n : ℕ ↦ (1 : ℝ)) atTop (nhds 1)).sub htop)
  have hscaled := (tendsto_const_nhds : Tendsto
      (fun _n : ℕ ↦ C) atTop (nhds C)).mul htail
  have hconst : Tendsto (fun _n : ℕ ↦
      D / Real.log (W : ℝ) ^ 3) atTop
      (nhds (D / Real.log (W : ℝ) ^ 3)) := tendsto_const_nhds
  simpa only [primeRowRelativeError, mul_zero, add_zero] using
    hconst.add hscaled

/-- Fully eventual relative row terminal.  Given any prescribed positive
row tolerance, one cutoff threshold works for every larger cutoff; after
that choice the literal row bound holds for every sufficiently large
ambient integer and every marked prime. -/
theorem exists_cutoff_eventually_primeRowResidual_le
    {target : ℝ} (htarget : 0 < target) :
    ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W →
      ∀ᶠ n : ℕ in atTop, ∀ p : PrimeIndex n W,
        |rowResidual (primeWeight n) (primeDiagonal n) (primeKernel n) p| ≤
          target * tPrime n p.1 := by
  obtain ⟨D, hD, C, hC, Xrow, hrow⟩ :=
    exists_uniform_primeRowResidual_relative_bound
  have hLogTop : Tendsto (fun W : ℕ ↦ Real.log (W : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hInv : Tendsto (fun W : ℕ ↦ (Real.log (W : ℝ))⁻¹)
      atTop (nhds 0) := tendsto_inv_atTop_zero.comp hLogTop
  have hFixed : Tendsto (fun W : ℕ ↦
      D / Real.log (W : ℝ) ^ 3) atTop (nhds 0) := by
    have hmain := (tendsto_const_nhds : Tendsto
      (fun _W : ℕ ↦ D) atTop (nhds D)).mul (hInv.pow 3)
    simpa only [div_eq_mul_inv, inv_pow, mul_zero,
      zero_pow (by norm_num : 3 ≠ 0)] using hmain
  have hFixedSmall : ∀ᶠ W : ℕ in atTop,
      D / Real.log (W : ℝ) ^ 3 < target / 2 :=
    hFixed.eventually (eventually_lt_nhds (half_pos htarget))
  obtain ⟨Wsmall, hWsmall⟩ := eventually_atTop.1 hFixedSmall
  refine ⟨max Xrow Wsmall, ?_⟩
  intro W hW
  have hXrow : Xrow ≤ W := (le_max_left Xrow Wsmall).trans hW
  have hWsmall' : Wsmall ≤ W := (le_max_right Xrow Wsmall).trans hW
  have hfixedW : D / Real.log (W : ℝ) ^ 3 < target / 2 :=
    hWsmall W hWsmall'
  have herrorT := tendsto_primeRowRelativeError_fixedCutoff D C W
  have herrorSmall : ∀ᶠ n : ℕ in atTop,
      primeRowRelativeError D C n W < target :=
    herrorT.eventually (eventually_lt_nhds (by linarith))
  have hyNatTop : Tendsto (fun n : ℕ ↦ yNat n) atTop atTop := by
    unfold yNat
    exact tendsto_nat_floor_atTop.comp
      Erdos390.Full.RegularMeshPrimeCutoffs.tendsto_y_atTop
  have hWY : ∀ᶠ n : ℕ in atTop, W ≤ yNat n :=
    hyNatTop.eventually (eventually_ge_atTop W)
  filter_upwards [eventually_gt_atTop 1, hWY, herrorSmall] with
      n hn hWYn herrorN
  intro p
  have hraw := hrow hn hXrow hWYn p
  exact hraw.trans (mul_le_mul_of_nonneg_right herrorN.le
    (tPrime_mem_unit hn p).1)

end Erdos390.Full.PaperCanonicalPrimeRowResidualEventually

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

/- Source module: Erdos390.Full.PaperCanonicalPrimeGraphReferenceEventually -/
section


/-!
# Canonical arithmetic reference inverse with cutoff before the mesh

This is the paper-order eventual wrapper for the literal prime-graph
argument.  The mesh tolerance, inverse constant, and prime cutoff are
selected before `delta` and the regular mesh.  Only the final ambient
threshold may depend on the fixed mesh and anchor block.
-/

open scoped BigOperators
open Filter Set

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

open ArithmeticModel ArithmeticBandGeometry
open PrimeSquarefreeDirichletGeometry
open FiniteAnchoredDirichletQuadratic
open PaperCanonicalSlowKappa
open PaperWeightedInverseExport
open RegularRelativeMesh

namespace BridgeData

set_option maxHeartbeats 1800000 in
/-- Exact paper-order reference terminal.  In particular, `W₀` is outside
the quantifiers for `delta` and `M`, and the inverse constant is independent
of the number of cells and of the moving low-band centre. -/
theorem exists_cutoff_before_mesh_eventually_referenceSharp_primeGraph_inverse :
    ∃ meshTol : ℝ, 0 < meshTol ∧
      ∃ Cref : ℝ, 0 < Cref ∧
      ∃ W₀ : ℕ,
      ∀ W : ℕ, W₀ ≤ W →
      ∀ (Head : Type*) [Fintype Head] [DecidableEq Head],
      ∀ {delta eta : ℝ} (M : Mesh delta eta) (hdelta : 0 < delta),
        delta + M.ratio ≤ meshTol →
        ∀ (anchors : Finset (Fin M.cellCount)), anchors.Nonempty →
          (∀ k ∈ anchors, (1 / 8 : ℝ) < M.lower k) →
          (∀ k ∈ anchors, M.upper k ≤ 1 - (1 / 8 : ℝ)) →
          ((1 / 8 : ℝ) ≤ (∑ k ∈ anchors, M.width k) / 2) →
          ∀ᶠ n : ℕ in atTop,
            ∀ (B : BridgeData Head (Fin (M.cellCount + 1))),
              B.sampleData.n = n → B.sampleData.W = W →
              (∃ (hWne : B.sampleData.W ≠ 0)
                  (S : RegularMeshPrimeCutoffs.ScaleSeparation
                    M B.sampleData.n B.sampleData.W),
                B.partition =
                  RegularMeshPrimeCutoffs.Mesh.canonicalPartition M
                    hdelta B.n_gt_one hWne S) →
              ∃ cert : PositiveCellTransfer.IntervalCertificate B.partition,
                ∃ referenceEquiv :
                    SharpGaugeSpace B.partition.mass B.partition.center
                        ≃L[ℝ]
                      SharpGaugeSpace B.partition.mass B.partition.center,
                  (∀ q, referenceEquiv q =
                    ArithmeticGaugeStableInverse.projectedSharpCLM
                      (CompressedArithmeticOperator.arithmeticDiagonal
                        (y B.sampleData.n) cert.lower cert.upper)
                      (CompressedArithmeticOperator.arithmeticKernel
                        (y B.sampleData.n) cert.lower cert.upper)
                      B.partition.center
                      (MovingLowGaugeTransfer.sharpWeight
                        B.partition.mass B.partition.center)
                      (ne_of_gt B.actualSharpWeightTotal_pos) q) ∧
                  ∀ v, ‖referenceEquiv.symm v‖ ≤ Cref * ‖v‖ := by
  obtain ⟨CF, hCF, hF⟩ :=
    PaperActualSlowRightRowFinite.exists_F_lipschitz_unit
  obtain ⟨CKernel, hCKernel, hKernel⟩ :=
    PoissonDickmanKernelBounds.exists_covarianceKernel_abs_le_first
  let kappa : ℝ := canonicalSlowKappa
  let anchorFloor : ℝ := 1 / 8
  let A : ℝ := 2 * CF + 7 * CKernel
  let radius : ℝ := kappa * anchorFloor / 16
  let meshTol : ℝ := radius / (2 * (A + 1))
  let rowTarget : ℝ := radius - A * meshTol
  let Cref : ℝ := 8 / (kappa * anchorFloor)
  have hkappa : 0 < kappa := by
    simpa only [kappa] using canonicalSlowKappa_pos
  have hfloor : 0 < anchorFloor := by
    dsimp only [anchorFloor]
    norm_num
  have hA : 0 ≤ A := by
    dsimp only [A]
    positivity
  have hAone : 0 < A + 1 := by linarith
  have hradius : 0 < radius := by
    dsimp only [radius]
    positivity
  have hmeshTol : 0 < meshTol := by
    dsimp only [meshTol]
    positivity
  have hmeshIdentity : meshTol * (2 * (A + 1)) = radius := by
    dsimp only [meshTol]
    field_simp [ne_of_gt hAone]
  have hAmLt : A * meshTol < radius := by
    nlinarith [mul_nonneg hA hmeshTol.le]
  have hrowTarget : 0 < rowTarget := by
    dsimp only [rowTarget]
    linarith
  have hCref : 0 < Cref := by
    dsimp only [Cref]
    positivity
  obtain ⟨Wrow, hRowEvent⟩ :=
    PaperCanonicalPrimeRowResidualEventually.exists_cutoff_eventually_primeRowResidual_le
      hrowTarget
  let W₀ : ℕ := max 2
    (max RegularMeshPrimeCutoffs.canonicalActualMomentCutoff
      (max RegularMeshPrimeCutoffs.Mesh.canonicalPrimeAnchorCutoff Wrow))
  refine ⟨meshTol, hmeshTol, Cref, hCref, W₀, ?_⟩
  intro W hW Head _instFintype _instDecidable
  have hWmoment :
      RegularMeshPrimeCutoffs.canonicalActualMomentCutoff ≤ W :=
    ((le_max_left _
      (max RegularMeshPrimeCutoffs.Mesh.canonicalPrimeAnchorCutoff Wrow)).trans
        (le_max_right 2 _)).trans hW
  have hWanchor :
      RegularMeshPrimeCutoffs.Mesh.canonicalPrimeAnchorCutoff ≤ W :=
    ((le_max_left _ Wrow).trans
      ((le_max_right _
        (max RegularMeshPrimeCutoffs.Mesh.canonicalPrimeAnchorCutoff Wrow)).trans
          (le_max_right 2 _))).trans hW
  have hWrow : Wrow ≤ W :=
    ((le_max_right _ Wrow).trans
      ((le_max_right _
        (max RegularMeshPrimeCutoffs.Mesh.canonicalPrimeAnchorCutoff Wrow)).trans
          (le_max_right 2 _))).trans hW
  have hRow := hRowEvent W hWrow
  intro delta eta M hdelta hmesh anchors hAnchors
    hIdealLower hIdealUpper hIdealMass
  have hMoment :=
    RegularMeshPrimeCutoffs.Mesh.canonicalActualFirstMomentCutoff_eventually
      M hdelta W hWmoment
  have hAnchor :=
    RegularMeshPrimeCutoffs.Mesh.canonicalPrimeAnchorCutoff_eventually
      M hdelta W hWanchor anchors hAnchors hIdealLower hIdealUpper
        hIdealMass
  filter_upwards [hMoment, hAnchor, hRow] with
      n hMomentN hAnchorN hRowN
  intro B hBn hBW hpartition
  subst n
  subst W
  obtain ⟨_hWmoment, _hnMoment, hMomentAll⟩ := hMomentN
  obtain ⟨hWanchor, hnAnchor, hAnchorAll⟩ := hAnchorN
  obtain ⟨hWuser, S, hpartitionUser⟩ := hpartition
  let Pcanonical :=
    RegularMeshPrimeCutoffs.Mesh.canonicalPartition M hdelta
      B.n_gt_one hWuser S
  let Ecanonical :=
    RegularMeshPrimeCutoffs.Mesh.canonicalCertificate M hdelta
      B.n_gt_one hWuser S
  have hpartitionCanonical : B.partition = Pcanonical := by
    exact hpartitionUser.trans (by rfl)
  obtain ⟨hdevSupRaw, hdevL1Raw⟩ := hMomentAll S
  have hdevSup : ∀ p : BandPrime B.sampleData.n B.sampleData.W,
      |B.primeDeviation p| ≤ meshTol := by
    intro p
    have hpRaw : |Pcanonical.deviation p| ≤ delta + M.ratio := by
      simpa only [Pcanonical] using hdevSupRaw p
    change |B.partition.deviation p| ≤ meshTol
    rw [hpartitionCanonical]
    exact hpRaw.trans hmesh
  have hdevL1 : B.primeDeviationL1 ≤ 7 * meshTol := by
    have hL1Raw : Pcanonical.totalL1 ≤ 7 * (delta + M.ratio) := by
      simpa only [Pcanonical] using hdevL1Raw
    change B.partition.totalL1 ≤ 7 * meshTol
    rw [hpartitionCanonical]
    exact hL1Raw.trans
      (mul_le_mul_of_nonneg_left hmesh (by norm_num))
  obtain ⟨hInteriorRaw, hMassRaw⟩ := hAnchorAll S
  let anchor :=
    RegularMeshPrimeCutoffs.Mesh.canonicalPrimeAnchorSet
      M Pcanonical anchors
  have hInterior : ∀ p ∈ anchor,
      tPrime B.sampleData.n p.1 ∈
        Set.Icc (1 / 8 : ℝ) (1 - 1 / 8) := by
    simpa only [anchor, Pcanonical,
      Subsingleton.elim hnAnchor B.n_gt_one,
      Subsingleton.elim hWanchor hWuser] using hInteriorRaw
  have hMass : (1 / 8 : ℝ) ≤
      anchorMass (primeWeight B.sampleData.n) anchor := by
    simpa only [anchor, Pcanonical,
      Subsingleton.elim hnAnchor B.n_gt_one,
      Subsingleton.elim hWanchor hWuser] using hMassRaw
  let cert : PositiveCellTransfer.IntervalCertificate B.partition := by
    rw [hpartitionCanonical]
    exact Ecanonical
  have hFdiff : ∀ p : BandPrime B.sampleData.n B.sampleData.W,
      |DickmanBasic.F (tPrime B.sampleData.n p.1) -
          DickmanBasic.F (B.bandCenter (B.partition.band p))| ≤
        CF * |B.primeDeviation p| := by
    intro p
    simpa only [bandCenter, primeDeviation, abs_sub_comm] using
      hF _ (tPrime_mem_unit B.n_gt_one p) _
        (B.partition.center_mem_zero_one B.n_gt_one
          (B.partition.band p))
  have hKernelFirst : ∀
      p q : BandPrime B.sampleData.n B.sampleData.W,
      |ConditionedPoissonLimit.covarianceKernel
          (tPrime B.sampleData.n p.1)
          (tPrime B.sampleData.n q.1)| ≤
        CKernel * tPrime B.sampleData.n p.1 := by
    intro p q
    exact hKernel _ (tPrime_mem_unit B.n_gt_one p) _
      (tPrime_mem_unit B.n_gt_one q)
  let mass : ℝ := anchorMass (primeWeight B.sampleData.n) anchor
  let base : ℝ := 4 / (kappa * mass)
  let loss : ℝ := base * (2 * radius)
  have hmassFloor : anchorFloor ≤ mass := by
    simpa only [anchorFloor, mass] using hMass
  have hmass : 0 < mass := hfloor.trans_le hmassFloor
  have hlossId : loss = anchorFloor / (2 * mass) := by
    dsimp only [loss, base, radius]
    field_simp [ne_of_gt hkappa, ne_of_gt hmass]
    ring
  have hlossLe : loss ≤ 1 / 2 := by
    rw [hlossId]
    apply (div_le_iff₀ (mul_pos (by norm_num) hmass)).2
    nlinarith
  have hsmallLoss : loss < 1 := hlossLe.trans_lt (by norm_num)
  have herrorIdentity :
      rowTarget + (2 * CF + 7 * CKernel) * meshTol = radius := by
    dsimp only [rowTarget, A]
    ring
  have hsmall :
      (4 / (canonicalSlowKappa *
          anchorMass (primeWeight B.sampleData.n) anchor)) *
        (2 * (rowTarget + (2 * CF + 7 * CKernel) * meshTol)) < 1 := by
    simpa only [kappa, mass, base, loss, herrorIdentity] using hsmallLoss
  obtain ⟨referenceEquiv, hreference, hinv⟩ :=
    B.exists_referenceSharpProjectedEquiv_of_primeGraph cert anchor
      hInterior hrowTarget.le hmeshTol.le hCF.le hCKernel
      hRowN hFdiff hKernelFirst hdevSup hdevL1
      (hfloor.trans_le hmassFloor) hsmall
  have hkMass : 0 < kappa * mass := mul_pos hkappa hmass
  have hkFloor : 0 < kappa * anchorFloor := mul_pos hkappa hfloor
  have hbasePos : 0 < base := by
    dsimp only [base]
    exact div_pos (by norm_num) hkMass
  have hdenHalf : 1 / 2 ≤ 1 - loss := by linarith
  have hbaseBound : base ≤ 4 / (kappa * anchorFloor) := by
    dsimp only [base]
    apply (div_le_div_iff₀ hkMass hkFloor).2
    have hkorder := mul_le_mul_of_nonneg_left hmassFloor hkappa.le
    nlinarith
  have hconstantBound : base / (1 - loss) ≤ Cref := by
    calc
      base / (1 - loss) ≤ base / (1 / 2) :=
        div_le_div_of_nonneg_left hbasePos.le (by norm_num) hdenHalf
      _ = 2 * base := by ring
      _ ≤ 2 * (4 / (kappa * anchorFloor)) :=
        mul_le_mul_of_nonneg_left hbaseBound (by norm_num)
      _ = Cref := by
        dsimp only [Cref]
        ring
  refine ⟨cert, referenceEquiv, hreference, ?_⟩
  intro v
  exact (hinv v).trans
    (mul_le_mul_of_nonneg_right (by
      simpa only [kappa, mass, base, loss, herrorIdentity] using
        hconstantBound) (norm_nonneg v))

end BridgeData
end
end Erdos390.Full.PaperBridgeFit

end

universe u_1
theorem solution : Erdos390.RemainingAnalyticGoal001_013.{u_1} := by
  exact @Erdos390.Full.PaperBridgeFit.BridgeData.exists_cutoff_before_mesh_eventually_referenceSharp_primeGraph_inverse
