-- Prove2me | solution 1 for Erdos390.Full.PaperBridgeFit.BridgeData.exists_paperFineMesh_cutoff_eventually_canonical_lemma86_variance_of_base_compact
-- status  : ACCEPTED   (prove)
-- author  : @doctosil
-- created : 2026-09-17T17:17:03.491403+00:00
-- url     : https://prove2.me/submissions/de35dd50-e022-43c6-b91e-67122cb9059d

import Definitions.Def_erdos390_remaining_analytic_propositions_003
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
import Theorems.Thm_Erdos390_Full_PaperBridgeFit_BridgeData_actualTwoStageCompensatedVariance_bounds_paperScale_of_weightedRow
import Theorems.Thm_Erdos390_Full_PaperBridgeFit_BridgeData_boxIndependent_canonicalRaw_actualWeightedRow_compact
import Theorems.Thm_Erdos390_Full_PaperBridgeFit_BridgeData_exists_boxIndependent_actual_component_signed_profiles_compact
import Theorems.Thm_Erdos390_Full_PaperCanonicalMarkedNuisanceRows_PaperBridgeFit_BridgeData_exists_uniform_canonical_tiltedLaw_nuisance_valuation_rate_on_effectiveBall_compact
import Theorems.Thm_Erdos390_Full_PaperCanonicalPrimeRowResidualEventually_abs_firstMomentWeightedAbelRemainder_le
import Theorems.Thm_Erdos390_Full_PaperCanonicalPrimeRowResidualEventually_abs_primeRowResidual_le_of_relative_quadrature
import Theorems.Thm_Erdos390_Full_RegularMeshPrimeCutoffs_Mesh_canonicalPrimeAnchorCutoff_eventually




section
universe u_1 u_2
theorem Erdos390.Full.PaperCanonicalMarkedNuisanceRows.PaperBridgeFit.BridgeData.exists_uniform_canonical_tiltedLaw_nuisance_valuation_rate_on_effectiveBall : Erdos390.RemainingAnalyticGoal004_002.{u_1, u_2} := @Erdos390.Full.PaperCanonicalMarkedNuisanceRows.PaperBridgeFit.BridgeData.exists_uniform_canonical_tiltedLaw_nuisance_valuation_rate_on_effectiveBall_compact
end
section
universe u_1 u_3
theorem Erdos390.Full.PaperBridgeFit.BridgeData.exists_boxIndependent_actual_component_signed_profiles : Erdos390.RemainingAnalyticGoal001_010.{u_1, u_3} := @Erdos390.Full.PaperBridgeFit.BridgeData.exists_boxIndependent_actual_component_signed_profiles_compact
end
section
universe u_1 u_2
theorem Erdos390.Full.PaperBridgeFit.BridgeData.boxIndependent_canonicalRaw_actualWeightedRow : Erdos390.RemainingAnalyticGoal001_006.{u_1, u_2} := @Erdos390.Full.PaperBridgeFit.BridgeData.boxIndependent_canonicalRaw_actualWeightedRow_compact
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

/- Source module: Erdos390.Full.HeadPattern -/
section


/-!
# Exact finite head patterns

The marked smooth cells impose exact valuations at finitely many fixed head
primes.  This file records their integral factor and modulus and proves the
factorization/divisibility part of the inclusion--exclusion reduction.  No
smooth-number asymptotic is used here.
-/

open scoped BigOperators
open scoped ArithmeticFunction.Moebius

namespace Erdos390.Full.HeadPattern



namespace Pattern

variable (P : Pattern)









theorem factor_ne_zero : P.factor ≠ 0 := by
  rw [factor]
  apply Finset.prod_ne_zero_iff.mpr
  intro p hp
  exact pow_ne_zero _ (P.prime_mem p hp).ne_zero

theorem modulus_ne_zero : P.modulus ≠ 0 := by
  rw [modulus]
  apply Finset.prod_ne_zero_iff.mpr
  intro p hp
  exact (P.prime_mem p hp).ne_zero























end Pattern

end Erdos390.Full.HeadPattern

end

/- Source module: Erdos390.Full.PaperScaleMarkedCell -/
section


/-!
# Paper-scale common main term for marked structured cells

The raw structured-cell asymptotic is a finite sum of endpoint Dickman
terms.  This module performs the algebraic closure required in the paper:
the head Möbius coefficient is evaluated exactly, and the endpoint terms
are compared with one common Dickman translate before normalization.
-/

open scoped BigOperators ArithmeticFunction.Moebius

namespace Erdos390.Full.PaperScaleMarkedCell

open ArithmeticModel DickmanBasic Scale
open StructuredCells HeadPattern MarkedFriableAsymptotic
open StructuredCellAsymptotic
open DivisibilityMomentBounds

noncomputable section

/-! ## Exact closure of the head Möbius coefficient -/











theorem headDensity_pos (P : Pattern) : 0 < headDensity P := by
  have hfactor : (0 : ℝ) < (P.factor : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero P.factor_ne_zero
  have hmod : (0 : ℝ) < (P.modulus : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero P.modulus_ne_zero
  have htot : (0 : ℝ) < (P.modulus.totient : ℝ) := by
    exact_mod_cast Nat.totient_pos.mpr (Nat.pos_of_ne_zero P.modulus_ne_zero)
  exact mul_pos (one_div_pos.mpr hfactor) (div_pos htot hmod)



/-! ## The common paper-scale main term -/





theorem paperCellDensity_pos (P : Pattern) {A B : ℝ} (hAB : A < B) :
    0 < paperCellDensity P A B := by
  exact mul_pos (mul_pos (headDensity_pos P) (sub_pos.mpr hAB)) rho_U_pos

































/-! ## Normalization algebra -/











end

end Erdos390.Full.PaperScaleMarkedCell

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



lemma reciprocalCutoff_le_one {W : Nat} (hW : 1 < W) :
    1 / (W : Real) <= 1 := by
  have h := one_div_le_one_div_of_le (by norm_num : (0 : Real) < 1)
    (by exact_mod_cast hW.le : (1 : Real) <= (W : Real))
  norm_num at h ⊢
  exact h

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

































variable {n W : ℕ}
  (P : Partition n W (Fin (M.cellCount + 1)))
  (E : IntervalCertificate P)
  (hLower : ∀ j, E.lower j = fullCutoff M n W j.1)
  (hUpper : ∀ j, E.upper j = fullCutoff M n W (j.1 + 1))

include E hLower hUpper











end Mesh

end

end Erdos390.Full.RegularMeshPrimeCutoffs

end

/- Source module: Erdos390.Full.DickmanFourMarkProductKernel -/
section


/-!
# The four-mark Dickman product kernel

The four-mark chamber in the proof of Lemma 7.5 uses the normalized
Dickman profile

`F x = rho (U - x) / rho U`

on the full simplex `x, z >= 0`, `x + z <= 4`.  The local product estimate
in `DickmanBasic` covers the unit square by differentiating the actual
method-of-steps solution near the origin.  This file extends that estimate
to the whole four-mark simplex using the globally proved one-Lipschitz
bound for `rho` on `[0,5]`.  In particular, no `C^{1,1}` hypothesis and no
tilt-box parameter occurs in the statement or proof.
-/

open Set

noncomputable section

namespace Erdos390.Full.DickmanFourMarkProductKernel

open DickmanBasic FriableAsymptotic















theorem boxIndependentFourMarkKernelConstant_pos :
    0 < boxIndependentFourMarkKernelConstant :=
  (Classical.choose_spec
    exists_boxIndependent_fourMark_productKernel_bound).1





end Erdos390.Full.DickmanFourMarkProductKernel

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







lemma sixtyFour_le_pairAggregationConstant :
    (64 : ℝ) ≤ pairAggregationConstant := by
  unfold pairAggregationConstant
  linarith [quadraticHalfMass_nonneg]



namespace BoundedValuationLaw

variable {Omega : Type*} [Fintype Omega] {M : ℕ}
  (law : BoundedValuationLaw Omega M)











end BoundedValuationLaw

end


end Erdos390.Full.PaperPrimePowerPairAggregation

end

/- Source module: Erdos390.Full.PaperPrimePowerLemma75 -/
section


/-!
# Exact export of paper Lemma 7.5

This module joins the literal four-mark chamber, the arbitrary-power
fallback, the four prime-power orientations, and their finite row
aggregation.  The final constant is independent of the tilt box.  All box
dependence is confined to a single remainder tending to zero.
-/

open Filter Topology
open scoped BigOperators

namespace Erdos390.Full.PaperPrimePowerLemma75

set_option maxHeartbeats 2400000

open ArithmeticModel Scale HeadPattern StructuredCells
open FiniteProbability PrimePowerCovariance
open PrimePowerCovariance.BoundedValuationLaw
open StructuredCellValuationLaw
open DickmanFourMarkProductKernel
open FullTiltPairChamber FullTiltPairHarmonicRate
open FullTiltPrimePowerFallback
open OmittedTiltPairChamber PaperScaleMarkedCell LocalFugacityBounds
open PaperTwoLocalRestorationBound PaperValuationCutoff
open PaperPrimePowerChamberError PaperPrimePowerActualSplice
open PaperPrimePowerPointwise
open PaperPrimePowerFourDisplays PaperPrimePowerPairAggregation
open PaperPrimePowerTailLedger PaperPrimePowerTailRow
open PaperPrimePowerRemainderRate PaperPrimePowerAuxiliaryPrime
open PaperPrimePowerSumAbsAggregation
open ValuationCutoff PrimeSums PaperPrimePowerRow

noncomputable section





theorem paperPrimePowerConstant_pos {C_K : ℝ} (hCK : 0 < C_K) :
    0 < paperPrimePowerConstant C_K := by
  unfold paperPrimePowerConstant
  have hAgg : 0 < pairAggregationConstant :=
    lt_of_lt_of_le (by norm_num) sixtyFour_le_pairAggregationConstant
  have hMain : 0 < primePowerMainConstant C_K := by
    unfold primePowerMainConstant
    exact add_pos (mul_pos (by norm_num) hCK)
      (one_div_pos.mpr DickmanBasic.rho_U_pos)
  exact mul_pos (mul_pos hAgg hMain) (by positivity)











end

end Erdos390.Full.PaperPrimePowerLemma75

end

/- Source module: Erdos390.Full.FixedFiniteMixtureFullUniform -/
section


/-!
# Full uniform Lemma 7.5 for a fixed finite family of actual cells

This file specializes the marked-cell and full-tilt asymptotics on every
member of a fixed finite family, takes finite common majorants, and applies
the exact tagged-mixture theorem.  No desired covariance or tail estimate
is assumed by the final export.
-/

open Filter Topology
open scoped BigOperators

namespace Erdos390.Full.FixedFiniteMixtureFullUniform

set_option maxHeartbeats 2400000

open ArithmeticModel Scale HeadPattern StructuredCells
open FiniteProbability PrimePowerCovariance
open PrimePowerCovariance.BoundedValuationLaw
open StructuredCellValuationLaw
open ValuationScoreDomination
open OmittedTiltPairChamber FullTiltPairChamber
open FullTiltPairHarmonicRate FullTiltPrimePowerFallback
open DickmanFourMarkProductKernel PaperScaleMarkedCell
open PaperTwoLocalRestorationBound LocalFugacityBounds
open PaperPrimePowerChamberError PaperPrimePowerFourDisplays
open PaperPrimePowerPairAggregation
open PaperPrimePowerTailLedger PaperPrimePowerTailRow
open PaperPrimePowerRemainderRate PaperPrimePowerAuxiliaryPrime
open PaperPrimePowerLemma75 PaperPrimePowerGenericAggregation
open FixedFiniteMixtureLemma75 PaperValuationCutoff ValuationCutoff
open PrimeSums

noncomputable section









variable {Cell : Type*} [Fintype Cell]



theorem boxIndependentPrimePowerConstant_pos :
    0 < boxIndependentPrimePowerConstant :=
  paperPrimePowerConstant_pos boxIndependentFourMarkKernelConstant_pos



end

end Erdos390.Full.FixedFiniteMixtureFullUniform

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







theorem physicalPowerCorrectionRowError_nonneg
    {epsilon G : ℝ} {n W : ℕ}
    (hepsilon : 0 ≤ epsilon) (hG : 0 ≤ G) :
    0 ≤ physicalPowerCorrectionRowError epsilon G n W := by
  unfold physicalPowerCorrectionRowError bandReciprocalSum
  have hQ : 0 ≤ quadraticHalfMass := quadraticHalfMass_nonneg
  positivity















































end BridgeData

end

end Erdos390.Full.PaperBridgeFit

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















omit [DecidableEq Head] in theorem canonicalGuardPerturbationConstant_nonneg
    (P : Head → HeadPattern.Pattern) (I : PhysicalIntervals)
    (Kscore : ℝ) :
    0 ≤ canonicalGuardPerturbationConstant P I Kscore := by
  unfold canonicalGuardPerturbationConstant
  apply Finset.sum_nonneg
  intro c hc
  exact div_nonneg (mul_nonneg (by norm_num) (Real.exp_pos _).le)
    (PaperScaleMarkedCell.paperCellDensity_pos
      (P c.1) (I.lower_lt_upper c.2)).le





















end BridgeData

end

end Erdos390.Full.PaperBridgeFit

end

/- Source module: Erdos390.Full.PaperBridgeCanonicalPhysicalPowerCorrectionEventually -/
section


/-!
# Eventual canonical specialization of the residual physical power row

This file discharges the density, score-envelope, small-tilt, and divisor
fallback inputs of the residual-physical comparison.  All constants are
chosen from the fixed physical cells, cutoff, and preselected coefficient
box.  The resulting row error is also proved to survive division by the
moving-low centre, via its explicit `error * log L -> 0` rate.
-/

open scoped BigOperators
open Filter Topology

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

open ArithmeticModel ArithmeticBandGeometry FiniteProbability
open PaperGuardCensus PrimeSums

namespace BridgeData

variable {Head : Type*} [Fintype Head] [DecidableEq Head]







omit [Fintype Head] [DecidableEq Head] in
theorem canonicalPhysicalCellDensity_pos
    (P : Head → HeadPattern.Pattern) (I : PhysicalIntervals)
    (c : Cell Head) :
    0 < canonicalPhysicalCellDensity P I c := by
  unfold canonicalPhysicalCellDensity
  exact div_pos
    (PaperScaleMarkedCell.paperCellDensity_pos
      (P c.1) (I.lower_lt_upper c.2))
    (mul_pos (by norm_num)
      ((I.lower_pos c.2).trans (I.lower_lt_upper c.2)))

omit [DecidableEq Head] in
theorem canonicalPhysicalPowerCorrectionConstant_nonneg
    (P : Head → HeadPattern.Pattern) (I : PhysicalIntervals)
    (Cmax : ℝ) (W : ℕ) (Acoef : ℝ) :
    0 ≤ canonicalPhysicalPowerCorrectionConstant P I Cmax W Acoef := by
  unfold canonicalPhysicalPowerCorrectionConstant
  exact Finset.sum_nonneg fun c _ ↦
    div_nonneg (Real.exp_pos _).le
      (canonicalPhysicalCellDensity_pos P I c).le





end BridgeData

end

end Erdos390.Full.PaperBridgeFit

end

/- Source module: Erdos390.Full.PaperActualFullProjectedInverseEventually -/
section


/-!
# Eventual inverse for the literal actual full projected operator

This file performs the two stable perturbations in the order used in
Section 8.4.  First the canonical arithmetic reference is perturbed to the
actual squarefree operator; then the proved full-versus-squarefree sharp row
is inserted.  The two perturbation radii and every inverse constant are
chosen before the ambient integer.
-/

open scoped BigOperators
open Filter Topology

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

open ArithmeticModel ArithmeticBandGeometry FiniteProbability
open PrimeSums PaperWeightedInverseExport
open OmittedTiltPairChamber PaperPrimePowerChamberError

namespace BridgeData

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]
  (B : BridgeData Head Band)



















omit [DecidableEq Head] in theorem canonicalCombinedPowerCorrection_nonneg
    [Nonempty Head]
    (P : Head → HeadPattern.Pattern)
    (I : PaperGuardCensus.PhysicalIntervals)
    {Cmax Acoef Aphys : ℝ} {Cprom Cbank W n : ℕ}
    (hCmax : 1 ≤ Cmax)
    (hAphys : 0 ≤ Aphys) (hW : 1 < W) (hn : 1 < n) :
    0 ≤ canonicalCombinedPowerCorrection
      P I Cmax Cprom Cbank W Acoef Aphys n := by
  have hLpos : 0 < Scale.L n := Scale.L_pos hn
  have hlogCmax : 0 ≤ Real.log Cmax := Real.log_nonneg hCmax
  have hepsilon : 0 ≤
      canonicalPhysicalPowerCorrectionEpsilon Aphys Cmax n := by
    unfold canonicalPhysicalPowerCorrectionEpsilon
    exact div_nonneg (mul_nonneg hAphys hlogCmax) hLpos.le
  have hG : 0 ≤
      canonicalPhysicalPowerCorrectionConstant P I Cmax W Acoef :=
    canonicalPhysicalPowerCorrectionConstant_nonneg P I Cmax W Acoef
  have hphysical : 0 ≤
      physicalPowerCorrectionRowError
        (canonicalPhysicalPowerCorrectionEpsilon Aphys Cmax n)
        (canonicalPhysicalPowerCorrectionConstant P I Cmax W Acoef) n W :=
    physicalPowerCorrectionRowError_nonneg hepsilon hG
  have hCenv : 0 ≤
      PaperStatisticNorm.valuationLogCoefficient Cmax W :=
    PaperStatisticNorm.valuationLogCoefficient_nonneg hCmax hW
  have hD : 0 ≤ canonicalGuardPerturbationConstant P I
      (Acoef * PaperStatisticNorm.valuationLogCoefficient Cmax W) :=
    canonicalGuardPerturbationConstant_nonneg P I _
  have hn0 : 0 < n := Nat.zero_lt_of_lt hn
  have hcensus : 0 ≤
      PaperGuardCensus.censusRatioMajorant Cprom Cbank n := by
    unfold PaperGuardCensus.censusRatioMajorant
    have hcoef : 0 ≤ (Cprom : ℝ) +
        3 * (Cbank : ℝ) * (Scale.L n + 2) := by positivity
    exact div_nonneg
      (mul_nonneg hcoef (Scale.y_pos hn0).le) (by positivity)
  have hguard : 0 ≤ guardPowerCorrectionWeightedMajorant Cprom Cbank
      (PaperStatisticNorm.valuationLogCoefficient Cmax W)
      (canonicalGuardPerturbationConstant P I
        (Acoef * PaperStatisticNorm.valuationLogCoefficient Cmax W)) n := by
    unfold guardPowerCorrectionWeightedMajorant
    exact mul_nonneg (Nat.cast_nonneg _)
      (PaperGuardCensus.guardPowerCorrectionRowError_nonneg
        (mul_nonneg hCenv hLpos.le) (mul_nonneg hD hcensus))
  unfold canonicalCombinedPowerCorrection
  exact add_nonneg hphysical hguard















end BridgeData

end

end Erdos390.Full.PaperBridgeFit

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



end Mesh

end

end Erdos390.Full.RegularRelativeMesh

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









end BridgeData

end

end Erdos390.Full.PaperBridgeFit

end

/- Source module: Erdos390.Full.PaperCanonicalLemma86AnchorEventually -/
section


/-!
# Assumption-free canonical interior anchor for Lemma 8.6

The paper-scale variance argument uses an interior set of prime coordinates
with a fixed positive reciprocal-logarithmic mass.  This file combines the
deterministic interior block of every sufficiently fine relative mesh with
the canonical prime-anchor quadrature.  The prime cutoff is selected before
the two mesh parameters; only the ambient threshold may depend on the fixed
mesh.
-/

open scoped BigOperators
open Filter

namespace Erdos390.Full.RegularMeshPrimeCutoffs

noncomputable section

open ArithmeticModel ArithmeticBandGeometry RegularRelativeMesh
open FiniteAnchoredDirichletQuadratic PrimeSquarefreeDirichletGeometry

namespace Mesh

/-- A canonical literal prime anchor, with no anchor set at the call site. -/
theorem canonicalPaperInteriorAnchorCutoff_eventually :
    ∀ W : ℕ, canonicalPrimeAnchorCutoff ≤ W →
      ∀ {delta eta : ℝ} (M : RegularRelativeMesh.Mesh delta eta)
        (hdelta : 0 < delta),
        delta + eta ≤ (1 : ℝ) / 16 →
        ∀ᶠ n : ℕ in atTop,
          ∃ hWne : W ≠ 0, ∃ hn : 1 < n,
            ∀ S : ScaleSeparation M n W,
              let P := canonicalPartition M hdelta hn hWne S;
              let anchor := canonicalPrimeAnchorSet M P M.interiorAnchors;
                (∀ p ∈ anchor,
                  tPrime n p.1 ∈
                    Set.Icc ((1 : ℝ) / 8) (1 - (1 : ℝ) / 8)) ∧
                (1 : ℝ) / 8 ≤ anchorMass (primeWeight n) anchor := by
  intro W hW delta eta M hdelta hfine
  have heta : 0 < eta := M.ratio_pos.trans_le M.ratio_le_eta
  have hdeltaSmall : delta < (1 : ℝ) / 16 := by linarith
  have hratioSmall : M.ratio < (1 : ℝ) / 16 := by
    linarith [M.ratio_le_eta]
  have hwidth : ∀ k : Fin M.cellCount,
      M.width k < (1 : ℝ) / 16 := by
    intro k
    exact (M.width_le_ratio hdelta k).trans_lt hratioSmall
  have hAnchors : M.interiorAnchors.Nonempty :=
    M.interiorAnchors_nonempty hdelta hdeltaSmall hwidth
  have hIdealLower : ∀ k ∈ M.interiorAnchors,
      (1 / 8 : ℝ) < M.lower k := by
    intro k hk
    exact M.interiorAnchors_idealLower hdelta hk
  have hIdealUpper : ∀ k ∈ M.interiorAnchors,
      M.upper k ≤ 1 - (1 / 8 : ℝ) := by
    intro k hk
    exact M.interiorAnchors_idealUpper hdelta hdeltaSmall hwidth hk
  have hIdealMass : (1 / 8 : ℝ) ≤
      (∑ k ∈ M.interiorAnchors, M.width k) / 2 :=
    M.interiorAnchors_mass_lower hdelta hdeltaSmall hwidth
  have hPrime := canonicalPrimeAnchorCutoff_eventually M hdelta W hW
    (epsilon := (1 / 8 : ℝ)) M.interiorAnchors hAnchors
      hIdealLower hIdealUpper hIdealMass
  filter_upwards [hPrime] with n hPrimeAt
  obtain ⟨hWne, hn, hAll⟩ := hPrimeAt
  refine ⟨hWne, hn, ?_⟩
  intro S
  let P := canonicalPartition M hdelta hn hWne S
  let anchor := canonicalPrimeAnchorSet M P M.interiorAnchors
  simpa only [P, anchor] using hAll S

end Mesh

end

end Erdos390.Full.RegularMeshPrimeCutoffs

end

/- Source module: Erdos390.Full.PaperLemma86CommonConstants -/
section


/-!
# Common paper constants for Lemma 8.6

The arithmetic terminal naturally produces three explicit constants for the
pointwise, first-moment, and second-moment compensated-coefficient bounds.
This file replaces them by one positive constant `Ccmp`, exactly as in the
paper.  The choice depends only on the already fixed regression constant and
therefore precedes `W`, the mesh, the head data, and the effective tilt box.

We also record the exact algebra which turns the geometric lower estimate
`w^2 <= (456 / cMesh^2) V` into the positive-factor form
`(cMesh^2 / 456) w^2 <= V` used by the variance assembly.
-/

open scoped BigOperators

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

open ArithmeticModel ArithmeticBandGeometry
open PaperWeightedInverseExport

namespace BridgeData





theorem paperLemma86BandTConstant_nonneg :
    0 ≤ paperLemma86BandTConstant := by
  dsimp only [paperLemma86BandTConstant]
  positivity



variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]







theorem paperLemma86VarianceFactor_pos
    {cMesh : ℝ} (hcMesh : 0 < cMesh) :
    0 < paperLemma86VarianceFactor cMesh := by
  dsimp only [paperLemma86VarianceFactor]
  positivity



end BridgeData

end

end Erdos390.Full.PaperBridgeFit

end

/- Source module: Erdos390.Full.PaperCanonicalLemma86RemainingOutputsEventually -/
section


/-!
# Closed remaining outputs of paper Lemma 8.6

This file closes the three quantitative conclusions not contained in the
geometric/coefficient umbrella: two-sided paper-scale slow variance, the
relative prime-power quadratic error, and every compensated marked prime
row.  Its public theorem has no analytic hypotheses, anchor data, contracts,
or abstract comparison assumptions.  The two mesh parameters remain
independent and all constants used to choose the prime cutoff precede the
cutoff and the effective tilt box.
-/

open scoped BigOperators
open Filter Topology Metric Set

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

open ArithmeticModel ArithmeticBandGeometry FiniteProbability
open PaperGuardCensus PrimeSums PaperWeightedInverseExport
open OmittedTiltPairChamber PaperPrimePowerChamberError
open PrimeSquarefreeDirichletGeometry FiniteAnchoredDirichletQuadratic
open RegularMeshPrimeCutoffs PaperPermittedRegularMesh
open PaperCanonicalSlowKappa

namespace BridgeData

/-- Convert the permitted-mesh variance comparison to the literal relative
factor used by the finite paper-scale variance theorem. -/
private theorem paper_varianceFactor_mul_le
    {c w variance : ℝ} (hc : 0 < c)
    (h : w ^ 2 ≤ (456 / c ^ 2) * variance) :
    (c ^ 2 / 456) * w ^ 2 ≤ variance := by
  have hc2 : 0 < c ^ 2 := sq_pos_of_pos hc
  have hfactor : 0 ≤ c ^ 2 / (456 : ℝ) := by positivity
  calc
    (c ^ 2 / 456) * w ^ 2 ≤
        (c ^ 2 / 456) * ((456 / c ^ 2) * variance) :=
      mul_le_mul_of_nonneg_left h hfactor
    _ = variance := by field_simp [hc2.ne']

/-- Eventual nonnegativity is enough to recover ordinary convergence from
the product-log rate supplied by the canonical power-correction APIs. -/
private theorem tendsto_zero_of_eventually_nonneg_mul_logL_zero_remaining
    (epsilon : ℕ → ℝ)
    (hepsilonNonneg : ∀ᶠ n : ℕ in atTop, 0 ≤ epsilon n)
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
  have hupper : ∀ᶠ n : ℕ in atTop,
      epsilon n ≤ epsilon n * Real.log (Scale.L n) := by
    filter_upwards [hepsilonNonneg, hlogOne] with n he hn
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hn he
  exact squeeze_zero' hepsilonNonneg hupper hepsilonRate



/-- Exact monotonicity calculation behind the uniform upper constant. -/
private theorem paperScaleLemma86SlowUpperConstantOfRow_le_uniform
    {Eprofile CF CKernel C K invW R Rmax : ℝ}
    (hE : 0 ≤ Eprofile) (hEone : Eprofile ≤ 1)
    (hCKernel : 0 ≤ CKernel)
    (hC : 0 ≤ C) (hK : 0 ≤ K)
    (hInvW : 0 ≤ invW) (hInvWone : invW ≤ 1)
    (hRRmax : R ≤ Rmax) :
    paperScaleLemma86SlowUpperConstantOfRow
        Eprofile CF CKernel C K invW R ≤
      paperScaleLemma86SlowUpperUniformConstant CF CKernel C K Rmax := by
  let A : ℝ := 1 / DickmanBasic.rho DickmanBasic.U
  let CL1 : ℝ := slowL1Constant C K
  let CL2 : ℝ := slowL2Constant C K
  have hA : 0 ≤ A := by
    dsimp only [A]
    exact one_div_nonneg.mpr DickmanBasic.rho_U_pos.le
  have hCL1 : 0 ≤ CL1 := by dsimp only [CL1, slowL1Constant]; positivity
  have hCL2 : 0 ≤ CL2 := by dsimp only [CL2, slowL2Constant]; positivity
  have hE2 : Eprofile ^ 2 ≤ Eprofile := by
    nlinarith [mul_nonneg hE (sub_nonneg.mpr hEone)]
  have hpair : pairCovarianceScale Eprofile ≤
      pairCovarianceScale 1 := by
    dsimp only [pairCovarianceScale]
    have hcoef : 0 ≤ 1 + 2 * A := by positivity
    dsimp only [A] at hcoef ⊢
    nlinarith
  have hsigned : signedSecondConstant Eprofile CKernel ≤
      signedSecondConstant 1 CKernel := by
    dsimp only [signedSecondConstant]
    have hbase : A + 2 * Eprofile ≤ A + 2 := by linarith
    have hsquare := (sq_le_sq₀ (by positivity) (by positivity)).2 hbase
    dsimp only [A] at hsquare ⊢
    linarith
  have hsigned0 : 0 ≤ signedSecondConstant 1 CKernel := by
    dsimp only [signedSecondConstant]
    positivity
  have hsignedInv : signedSecondConstant Eprofile CKernel * invW ≤
      signedSecondConstant 1 CKernel * 1 := by
    calc
      _ ≤ signedSecondConstant 1 CKernel * invW :=
        mul_le_mul_of_nonneg_right hsigned hInvW
      _ ≤ signedSecondConstant 1 CKernel * 1 :=
        mul_le_mul_of_nonneg_left hInvWone hsigned0
  have hpairTerm : (4 * pairCovarianceScale Eprofile) * CL1 ^ 2 ≤
      (4 * pairCovarianceScale 1) * CL1 ^ 2 := by
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hpair (by norm_num)) (sq_nonneg CL1)
  have hdiagTerm : (2 * Eprofile) * CL2 ≤ (2 * 1) * CL2 := by
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hEone (by norm_num)) hCL2
  have hsecondTerm :
      signedSecondConstant Eprofile CKernel * invW * CL2 ≤
        signedSecondConstant 1 CKernel * 1 * CL2 := by
    exact mul_le_mul_of_nonneg_right hsignedInv hCL2
  have hprimeFactor : 0 ≤ (1 + C) * (7 + C * K) := by positivity
  have hprimeTerm : ((1 + C) * (7 + C * K)) * R ≤
      ((1 + C) * (7 + C * K)) * Rmax :=
    mul_le_mul_of_nonneg_left hRRmax hprimeFactor
  dsimp only [paperScaleLemma86SlowUpperUniformConstant,
    paperScaleLemma86SlowUpperConstantOfRow,
    paperScaleSquarefreeSlowUpperConstant, CL1, CL2]
  dsimp only [CL1, CL2] at hpairTerm hdiagTerm hsecondTerm
  linarith

/- The main assumption-free eventual theorem is assembled below from the
geometry/coefficient terminal and the literal finite variance and marked-row
estimates. -/

set_option maxHeartbeats 4000000 in
/-- Canonical two-sided slow variance once the exact same-witness base
outputs have been supplied.  Every analytic ingredient is discharged inside
the theorem; its remaining hypotheses are precisely literal outputs of the
strengthened relative-power terminal on the same `e`. -/
theorem exists_paperFineMesh_cutoff_eventually_canonical_lemma86_variance_of_base
    (cMesh Creg : ℝ) (hcMesh : 0 < cMesh) (hCreg : 0 ≤ Creg) :
    ∃ meshTol : ℝ, 0 < meshTol ∧
      ∃ gammaSlow : ℝ, 0 < gammaSlow ∧
      ∃ Cvar : ℝ, 0 < Cvar ∧
      ∃ W₀ : ℕ,
      ∀ W : ℕ, W₀ ≤ W →
      ∀ {delta eta : ℝ} (M : RegularRelativeMesh.Mesh delta eta)
        (hdelta : 0 < delta)
        (_hPermitted : IsPermitted (cMesh := cMesh) M),
        delta + eta ≤ meshTol →
        ∀ {Head : Type*} [Fintype Head] [DecidableEq Head] [Nonempty Head]
          (Phead : Head → HeadPattern.Pattern),
          (∀ h : Head, ∀ p : ℕ,
            p ∈ (Phead h).primes ↔ p.Prime ∧ p ≤ W) →
        ∀ (I : PhysicalIntervals) (U : ℝ) (hU : 1 ≤ U)
          (hlowerOne : ∀ sigma, 1 ≤ I.lower sigma)
          (hupperU : ∀ sigma, I.upper sigma ≤ U),
        ∀ (Cprom Cbank : ℕ) (ledger : ∀ n, Ledger n Cprom Cbank)
          (a : NNReal) (marginFloor : ℝ), 0 < marginFloor →
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
                (hbaseline : B.baseline = T.baseline)
                (z : B.EffectiveParamSpace)
                (hz : z ∈ closedBall
                  (0 : B.EffectiveParamSpace) (a : ℝ))
                (e : B.RawBandGauge ≃ₗ[ℝ] B.RawBandGauge),
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
                        T hbaseline hBWlarge z hz) e) ≤ Creg * B.w →
                (∀ p : BandPrime B.sampleData.n B.sampleData.W,
                  |B.partition.deviation p| ≤ B.w) →
                B.partition.totalL1 ≤ 7 * B.w →
                B.w ^ 2 ≤
                  (456 / cMesh ^ 2) * B.partition.variance →
                B.partition.variance ≤ 4 * B.w ^ 2 →
                B.partition.variance ≤ B.partition.centerEnergy →
                gammaSlow * B.w ^ 2 ≤
                    B.actualTwoStageCompensatedVariance
                      (B.effectiveParamEquiv z)
                      (B.canonicalEffectiveNuisanceGamma_pos
                        I U (3 * (a : ℝ)) T)
                      (B.canonicalEffectiveNuisanceGap_on_closedBall I a
                        hU hlowerOne hupperU
                        (by intro sigma; rw [hcanonical]; rfl)
                        (by intro sigma; rw [hcanonical]; rfl)
                        T hbaseline hBWlarge z hz) e ∧
                  B.actualTwoStageCompensatedVariance
                      (B.effectiveParamEquiv z)
                      (B.canonicalEffectiveNuisanceGamma_pos
                        I U (3 * (a : ℝ)) T)
                      (B.canonicalEffectiveNuisanceGap_on_closedBall I a
                        hU hlowerOne hupperU
                        (by intro sigma; rw [hcanonical]; rfl)
                        (by intro sigma; rw [hcanonical]; rfl)
                        T hbaseline hBWlarge z hz) e ≤
                    Cvar * B.w ^ 2 := by
  obtain ⟨CKernel, hCKernel, hKernelBound⟩ :=
    PoissonDickmanKernelBounds.exists_covarianceKernel_abs_le_second
  let Cpow : ℝ :=
    FixedFiniteMixtureFullUniform.boxIndependentPrimePowerConstant
  let K : ℝ := paperLemma86BandTConstant
  let CL1 : ℝ := slowL1Constant Creg K
  let CL2 : ℝ := slowL2Constant Creg K
  let varianceFactor : ℝ := paperLemma86VarianceFactor cMesh
  let anchorFloor : ℝ := (1 : ℝ) / 8
  let main : ℝ :=
    (canonicalSlowKappa / 4) * anchorFloor * varianceFactor
  let rowTarget : ℝ := main / (16 * CL2)
  let primeFactor : ℝ := (1 + Creg) * CL1
  let gammaSlow : ℝ := main / 2
  let CF : ℝ := 1 / DickmanBasic.rho DickmanBasic.U
  let Rmax : ℝ := Cpow + 2
  let Cvar : ℝ :=
    paperScaleLemma86SlowUpperUniformConstant CF CKernel Creg K Rmax
  have hCpow : 0 < Cpow := by
    simpa only [Cpow] using
      FixedFiniteMixtureFullUniform.boxIndependentPrimePowerConstant_pos
  have hK : 0 ≤ K := by
    simpa only [K] using paperLemma86BandTConstant_nonneg
  have hCL1 : 0 < CL1 := by
    dsimp only [CL1, slowL1Constant]
    positivity
  have hCL2 : 0 < CL2 := by
    dsimp only [CL2, slowL2Constant]
    positivity
  have hvarianceFactor : 0 < varianceFactor := by
    simpa only [varianceFactor] using paperLemma86VarianceFactor_pos hcMesh
  have hanchorFloor : 0 < anchorFloor := by
    dsimp only [anchorFloor]
    norm_num
  have hmain : 0 < main := by
    dsimp only [main]
    exact mul_pos
      (mul_pos (div_pos canonicalSlowKappa_pos (by norm_num)) hanchorFloor)
      hvarianceFactor
  have hrowTarget : 0 < rowTarget := by
    dsimp only [rowTarget]
    positivity
  have hprimeFactor : 0 ≤ primeFactor := by
    dsimp only [primeFactor]
    positivity
  have hgammaSlow : 0 < gammaSlow := by
    dsimp only [gammaSlow]
    positivity
  have hCF : 0 < CF := by
    dsimp only [CF]
    exact one_div_pos.mpr DickmanBasic.rho_U_pos
  have hRmax : 0 < Rmax := by
    dsimp only [Rmax]
    positivity
  have hCvar : 0 < Cvar := by
    dsimp only [Cvar, paperScaleLemma86SlowUpperUniformConstant,
      paperScaleLemma86SlowUpperConstantOfRow,
      paperScaleSquarefreeSlowUpperConstant, CF, K, Rmax,
      slowL1Constant, slowL2Constant, signedSecondConstant,
      pairCovarianceScale]
    positivity
  obtain ⟨Wrow, hrowEvent⟩ :=
    _root_.Erdos390.Full.PaperCanonicalPrimeRowResidualEventually.exists_cutoff_eventually_primeRowResidual_le
      hrowTarget
  have hInvNat : Tendsto (fun W : ℕ ↦ 1 / (W : ℝ))
      atTop (nhds 0) := by
    have hcast : Tendsto (fun W : ℕ ↦ (W : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop
    simpa only [one_div] using tendsto_inv_atTop_zero.comp hcast
  let tailConstant : ℝ :=
    signedSecondConstant 0 CKernel * CL2 + primeFactor * Cpow
  have htailT : Tendsto
      (fun W : ℕ ↦ tailConstant * (1 / (W : ℝ)))
      atTop (nhds 0) := by
    simpa only [mul_zero] using tendsto_const_nhds.mul hInvNat
  obtain ⟨Wtail, hWtail⟩ := eventually_atTop.1
    (htailT.eventually (eventually_lt_nhds
      (show 0 < main / 16 by positivity)))
  let meshTol : ℝ := (1 : ℝ) / 16
  let W₀ : ℕ := max 2 (max
    RegularMeshPrimeCutoffs.Mesh.canonicalPrimeAnchorCutoff
      (max Wrow Wtail))
  have hmeshTol : 0 < meshTol := by dsimp only [meshTol]; norm_num
  refine ⟨meshTol, hmeshTol, gammaSlow, hgammaSlow,
    Cvar, hCvar, W₀, ?_⟩
  intro W hW delta eta M hdelta hPermitted hfine
    Head _instHF _instHD _instHN Phead hPhead
    I U hU hlowerOne hupperU Cprom Cbank ledger a marginFloor hmargin
  have hWone : 1 < W := by
    dsimp only [W₀] at hW
    omega
  have hWanchor :
      RegularMeshPrimeCutoffs.Mesh.canonicalPrimeAnchorCutoff ≤ W := by
    dsimp only [W₀] at hW
    omega
  have hWrow : Wrow ≤ W := by
    dsimp only [W₀] at hW
    omega
  have hWtail' : Wtail ≤ W := by
    dsimp only [W₀] at hW
    omega
  have htailSmall : tailConstant * (1 / (W : ℝ)) < main / 16 :=
    hWtail W hWtail'
  have hHeadLe : ∀ h, ∀ p ∈ (Phead h).primes, p ≤ W := by
    intro h p hp
    exact (hPhead h p).mp hp |>.2
  have hAnchorN :=
    RegularMeshPrimeCutoffs.Mesh.canonicalPaperInteriorAnchorCutoff_eventually
      W hWanchor M hdelta (by simpa only [meshTol] using hfine)
  obtain ⟨_hCpowTerminal, hpowerTerminal⟩ :=
    boxIndependent_canonicalRaw_actualWeightedRow
      Phead I U hlowerOne hupperU Cprom Cbank ledger
  let Acoef : ℝ := 3 * (a : ℝ)
  let Aphys : ℝ := 3 * (a : ℝ)
  have hAcoef : 0 ≤ Acoef := by dsimp only [Acoef]; positivity
  have hAphys : 0 ≤ Aphys := by dsimp only [Aphys]; positivity
  obtain ⟨profileError, hprofile0, hprofileT, _hprofileRate,
      Nprofile, hprofile⟩ :=
    exists_boxIndependent_actual_component_signed_profiles
      Phead I U hlowerOne hupperU Cprom Cbank ledger W hWone hHeadLe
        Acoef Aphys hAcoef hAphys
  obtain ⟨epsilon75, hepsilon750, hepsilon75T, _hepsilon75Rate,
      hcombinedRateRaw, Npower, hpower⟩ :=
    hpowerTerminal W hWone hHeadLe Acoef hAcoef Aphys hAphys
  obtain ⟨markedError, hmarked0, hmarkedRate, Nmarked, hmarked⟩ :=
    _root_.Erdos390.Full.PaperCanonicalMarkedNuisanceRows.PaperBridgeFit.BridgeData.exists_uniform_canonical_tiltedLaw_nuisance_valuation_rate_on_effectiveBall
      Phead I U hU hlowerOne hupperU Cprom Cbank ledger
        W hWone hHeadLe a
  let combined : ℕ → ℝ := fun n ↦
    canonicalCombinedPowerCorrection
      Phead I U Cprom Cbank W Acoef Aphys n
  have hcombinedRate : Tendsto
      (fun n : ℕ ↦ combined n * Real.log (Scale.L n))
        atTop (nhds 0) := by
    simpa only [combined, canonicalCombinedPowerCorrection] using
      hcombinedRateRaw
  have hcombinedNonneg : ∀ᶠ n : ℕ in atTop, 0 ≤ combined n := by
    filter_upwards [eventually_gt_atTop (1 : ℕ)] with n hn
    exact canonicalCombinedPowerCorrection_nonneg
      Phead I hU hAphys hWone hn
  have hcombinedT : Tendsto combined atTop (nhds 0) :=
    tendsto_zero_of_eventually_nonneg_mul_logL_zero_remaining
      combined hcombinedNonneg hcombinedRate
  have hmarkedT : Tendsto markedError atTop (nhds 0) :=
    tendsto_zero_of_nonneg_mul_logL_zero
      markedError hmarked0 hmarkedRate
  let R : ℕ → ℝ := fun n ↦
    Cpow * (1 / (W : ℝ)) + epsilon75 n + combined n
  have hRT : Tendsto R atTop
      (nhds (Cpow * (1 / (W : ℝ)))) := by
    simpa only [R, add_zero] using
      (tendsto_const_nhds.add hepsilon75T).add hcombinedT
  have hpairT : Tendsto
      (fun n : ℕ ↦ pairCovarianceScale (profileError n))
      atTop (nhds 0) := by
    unfold pairCovarianceScale
    have hcoefT : Tendsto
        (fun _n : ℕ ↦
          (1 + 2 * (1 / DickmanBasic.rho DickmanBasic.U) : ℝ))
        atTop (nhds
          (1 + 2 * (1 / DickmanBasic.rho DickmanBasic.U) : ℝ)) :=
      tendsto_const_nhds
    simpa only [zero_mul, zero_pow (by norm_num : 2 ≠ 0), add_zero] using
      (hprofileT.mul hcoefT).add (hprofileT.pow 2)
  have hsignedT : Tendsto
      (fun n : ℕ ↦ signedSecondConstant (profileError n) CKernel)
      atTop (nhds (signedSecondConstant 0 CKernel)) := by
    have hcont : Continuous
        (fun x : ℝ ↦ signedSecondConstant x CKernel) := by
      unfold signedSecondConstant
      fun_prop
    exact hcont.continuousAt.tendsto.comp hprofileT
  let gammaFloor : ℝ := canonicalEffectiveNuisanceGammaFloor
    Head I U (3 * (a : ℝ)) W marginFloor
  have hgammaFloor : 0 < gammaFloor := by
    dsimp only [gammaFloor]
    exact canonicalEffectiveNuisanceGammaFloor_pos I hmargin
  let nuisanceLoss : ℕ → ℝ := fun n ↦
    (nuisanceDimensionCeiling Head * (markedError n * CL1)) ^ 2 /
      gammaFloor
  have hnuisanceT : Tendsto nuisanceLoss atTop (nhds 0) := by
    have hinner : Tendsto
        (fun n : ℕ ↦ nuisanceDimensionCeiling Head *
          (markedError n * CL1)) atTop (nhds 0) := by
      simpa only [mul_zero, zero_mul] using
        (tendsto_const_nhds.mul
          (hmarkedT.mul (tendsto_const_nhds : Tendsto
            (fun _n : ℕ ↦ CL1) atTop (nhds CL1))))
    have hdiv := (hinner.pow 2).div
      (tendsto_const_nhds : Tendsto
        (fun _n : ℕ ↦ gammaFloor) atTop (nhds gammaFloor))
      hgammaFloor.ne'
    simpa only [nuisanceLoss, zero_pow (by norm_num : 2 ≠ 0),
      zero_div] using hdiv
  let loss : ℕ → ℝ := fun n ↦
    rowTarget * CL2 +
      (4 * pairCovarianceScale (profileError n)) * CL1 ^ 2 +
      (2 * profileError n) * CL2 +
      signedSecondConstant (profileError n) CKernel *
        (1 / (W : ℝ)) * CL2 +
      primeFactor * R n + nuisanceLoss n
  let limitLoss : ℝ :=
    rowTarget * CL2 +
      signedSecondConstant 0 CKernel * (1 / (W : ℝ)) * CL2 +
      primeFactor * (Cpow * (1 / (W : ℝ)))
  have hlossT : Tendsto loss atTop (nhds limitLoss) := by
    have hrowConst : Tendsto (fun _n : ℕ ↦ rowTarget * CL2)
        atTop (nhds (rowTarget * CL2)) := tendsto_const_nhds
    have hoff : Tendsto
        (fun n : ℕ ↦
          (4 * pairCovarianceScale (profileError n)) * CL1 ^ 2)
        atTop (nhds 0) := by
      simpa only [mul_zero, zero_mul] using
        (tendsto_const_nhds.mul hpairT).mul tendsto_const_nhds
    have hdiag : Tendsto
        (fun n : ℕ ↦ (2 * profileError n) * CL2)
        atTop (nhds 0) := by
      simpa only [mul_zero, zero_mul] using
        (tendsto_const_nhds.mul hprofileT).mul tendsto_const_nhds
    have hsecond : Tendsto
        (fun n : ℕ ↦ signedSecondConstant (profileError n) CKernel *
          (1 / (W : ℝ)) * CL2)
        atTop (nhds (signedSecondConstant 0 CKernel *
          (1 / (W : ℝ)) * CL2)) :=
      (hsignedT.mul tendsto_const_nhds).mul tendsto_const_nhds
    have hprime : Tendsto (fun n : ℕ ↦ primeFactor * R n)
        atTop (nhds (primeFactor * (Cpow * (1 / (W : ℝ))))) :=
      tendsto_const_nhds.mul hRT
    simpa only [loss, limitLoss, add_zero] using
      ((((hrowConst.add hoff).add hdiag).add hsecond).add hprime).add
        hnuisanceT
  have hrowLoss : rowTarget * CL2 = main / 16 := by
    dsimp only [rowTarget]
    field_simp [hCL2.ne']
  have htailIdentity :
      signedSecondConstant 0 CKernel * (1 / (W : ℝ)) * CL2 +
          primeFactor * (Cpow * (1 / (W : ℝ))) =
        tailConstant * (1 / (W : ℝ)) := by
    dsimp only [tailConstant]
    ring
  have hlimitSmall : limitLoss < main / 8 := by
    dsimp only [limitLoss]
    rw [hrowLoss]
    calc
      main / 16 +
            signedSecondConstant 0 CKernel * (1 / (W : ℝ)) * CL2 +
            primeFactor * (Cpow * (1 / (W : ℝ))) =
          main / 16 + tailConstant * (1 / (W : ℝ)) := by
            rw [add_assoc, htailIdentity]
      _ < main / 8 := by linarith
  have hlossSmall : ∀ᶠ n : ℕ in atTop, loss n < main / 2 :=
    hlossT.eventually (eventually_lt_nhds (by linarith))
  have hprofileOne : ∀ᶠ n : ℕ in atTop, profileError n ≤ 1 :=
    hprofileT.eventually (eventually_le_nhds (by norm_num))
  have hepsilonOne : ∀ᶠ n : ℕ in atTop, epsilon75 n ≤ 1 :=
    hepsilon75T.eventually (eventually_le_nhds (by norm_num))
  have hcombinedOne : ∀ᶠ n : ℕ in atTop, combined n ≤ 1 :=
    hcombinedT.eventually (eventually_le_nhds (by norm_num))
  have hRowN := hrowEvent W hWrow
  have hbandTN := eventually_bandTReciprocalSum_le W
  filter_upwards [hAnchorN, hlossSmall, hprofileOne, hepsilonOne,
    hcombinedOne, hRowN, hbandTN, eventually_ge_atTop Nprofile,
    eventually_ge_atTop Npower, eventually_ge_atTop Nmarked,
    hcombinedNonneg] with
      n hAnchorAt hlossN hprofileOneN hepsilonOneN hcombinedOneN
      hRowAt hbandTAt hnProfile hnPower hnMarked hcombinedN
  intro B hBn hBW hBWlarge hsep hremaining hcanonical hpartition hscale
    T hTmargin hbaseline z hz e hsharp hdevSup hdevL1 hvarLower
    hdevL2 hvariance
  subst n
  subst W
  obtain ⟨hWneAnchor, hnAnchor, hAnchorAll⟩ := hAnchorAt
  obtain ⟨hWneUser, S, hpartitionUser⟩ := hpartition
  let Pcanonical := RegularMeshPrimeCutoffs.Mesh.canonicalPartition
    M hdelta hnAnchor hWneAnchor S
  let anchor := RegularMeshPrimeCutoffs.Mesh.canonicalPrimeAnchorSet
    M Pcanonical M.interiorAnchors
  have hpartitionCanonical : B.partition = Pcanonical := by
    exact hpartitionUser.trans (by dsimp only [Pcanonical])
  obtain ⟨hinteriorRaw, hAnchorMassRaw⟩ := hAnchorAll S
  have hinterior : ∀ p ∈ anchor,
      tPrime B.sampleData.n p.1 ∈
        Set.Icc ((1 : ℝ) / 8) (1 - (1 : ℝ) / 8) := by
    simpa only [anchor, Pcanonical] using hinteriorRaw
  have hAnchorMass : anchorFloor ≤
      anchorMass (primeWeight B.sampleData.n) anchor := by
    simpa only [anchorFloor, anchor, Pcanonical] using hAnchorMassRaw
  have hmass : 0 < anchorMass (primeWeight B.sampleData.n) anchor :=
    hanchorFloor.trans_le hAnchorMass
  have hrowResidual : ∀ p : PrimeIndex B.sampleData.n B.sampleData.W,
      |rowResidual (primeWeight B.sampleData.n)
          (primeDiagonal B.sampleData.n) (primeKernel B.sampleData.n) p| ≤
        rowTarget * tPrime B.sampleData.n p.1 := hRowAt
  have hPattern : B.sampleData.pattern = Phead := by
    rw [hcanonical]
    rfl
  have hlo : ∀ sigma, B.sampleData.lo sigma =
      physicalBound (I.lower sigma) B.sampleData.n := by
    intro sigma
    rw [hcanonical]
    rfl
  have hhi : ∀ sigma, B.sampleData.hi sigma =
      physicalBound (I.upper sigma) B.sampleData.n := by
    intro sigma
    rw [hcanonical]
    rfl
  have hGuards : B.sampleData.guards =
      (ledger B.sampleData.n).guards := by
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
  have hphys : |xi MomentCoord.physical| ≤ Aphys := by
    calc
      |xi MomentCoord.physical| =
          ‖B.nuisanceParameter xi NuisanceCoord.physical‖ := by
        simp only [B.nuisanceParameter_physical, Real.norm_eq_abs]
      _ ≤ ‖B.nuisanceParameter xi‖ :=
        PiLp.norm_apply_le (B.nuisanceParameter xi)
          NuisanceCoord.physical
      _ ≤ Aphys := by simpa only [Acoef, Aphys] using hnuisance
  obtain ⟨hpair, hsingle⟩ := hprofile B xi hnProfile
    hPattern hlo hhi hGuards heta hphys rfl
  have hactualRowRaw := hpower B xi hnPower rfl hsep hremaining
    hcanonical heta hphys
  have hactualRow : ∀ p : BandPrime B.sampleData.n B.sampleData.W,
      (p.1 : ℝ) *
        ∑ r : BandPrime B.sampleData.n B.sampleData.W,
          |(B.actualValuationLaw xi).covVV p.1 r.1 -
            (B.actualValuationLaw xi).covII p.1 r.1| ≤
        R B.sampleData.n := by
    intro p
    simpa only [R, combined, canonicalCombinedPowerCorrection] using
      hactualRowRaw p
  have hmarkedRows : ∀ (c : NuisanceCoord B.HeadIndex)
      (p : BandPrime B.sampleData.n B.sampleData.W),
      |(B.tiltedLaw xi).covariance
        (fun m ↦ B.nuisanceStatistic m c)
        (fun m ↦ valuation p.1 (B.sampleData.value m))| ≤
          markedError B.sampleData.n * (1 / (p.1 : ℝ)) := by
    intro c p
    exact hmarked B z hz hnMarked rfl hsep hremaining hcanonical c p
  have hF : ∀ p : BandPrime B.sampleData.n B.sampleData.W,
      |DickmanBasic.F (tPrime B.sampleData.n p.1)| ≤ CF := by
    intro p
    have ht0 := PaperPrimePowerRow.tPrime_nonneg_of_mem_primeBand
      B.n_gt_one p.2
    have ht1 := PaperPrimePowerRow.tPrime_le_one_of_mem_primeBand
      B.n_gt_one p.2
    have harg : DickmanBasic.U - tPrime B.sampleData.n p.1 ∈
        Set.Icc (1 : ℝ) 5 := by
      constructor <;> norm_num [DickmanBasic.U] <;> linarith
    have hone : (1 : ℝ) ∈ Set.Icc (1 : ℝ) 5 := by norm_num
    have hrho : DickmanBasic.rho
        (DickmanBasic.U - tPrime B.sampleData.n p.1) ≤ 1 := by
      simpa only [DickmanBasic.rho_one] using
        DickmanBasic.antitoneOn_rho_one_five hone harg (by
          norm_num [DickmanBasic.U]
          linarith)
    rw [abs_of_pos (DickmanBasic.F_pos ⟨ht0, ht1.trans (by norm_num)⟩)]
    unfold DickmanBasic.F
    exact (div_le_div_iff_of_pos_right DickmanBasic.rho_U_pos).2 hrho
  have hKernel : ∀ p r : BandPrime B.sampleData.n B.sampleData.W,
      |ConditionedPoissonLimit.covarianceKernel
          (tPrime B.sampleData.n p.1) (tPrime B.sampleData.n r.1)| ≤
        CKernel := by
    intro p r
    have hp0 := PaperPrimePowerRow.tPrime_nonneg_of_mem_primeBand
      B.n_gt_one p.2
    have hp1 := PaperPrimePowerRow.tPrime_le_one_of_mem_primeBand
      B.n_gt_one p.2
    have hr0 := PaperPrimePowerRow.tPrime_nonneg_of_mem_primeBand
      B.n_gt_one r.2
    have hr1 := PaperPrimePowerRow.tPrime_le_one_of_mem_primeBand
      B.n_gt_one r.2
    calc
      _ ≤ CKernel * tPrime B.sampleData.n r.1 :=
        hKernelBound _ ⟨hp0, hp1⟩ _ ⟨hr0, hr1⟩
      _ ≤ CKernel := by
        simpa only [mul_one] using
          mul_le_mul_of_nonneg_left hr1 hCKernel
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
        hlowerOne hupperU hlo hhi T hbaseline hBWlarge z hz v
  have hRnonneg : 0 ≤ R B.sampleData.n := by
    dsimp only [R]
    exact add_nonneg
      (add_nonneg (mul_nonneg hCpow.le (by positivity))
        (hepsilon750 B.sampleData.n)) hcombinedN
  have hgammaFloorLe : gammaFloor ≤ gamma := by
    dsimp only [gammaFloor, gamma]
    exact B.canonicalEffectiveNuisanceGammaFloor_le I hU
      (by positivity : 0 ≤ 3 * (a : ℝ)) hmargin T hTmargin
  have hdim : Real.sqrt
      (Fintype.card (NuisanceCoord B.HeadIndex) : ℝ) ≤
        nuisanceDimensionCeiling Head :=
    B.sqrt_nuisanceCoord_card_le_ceiling
  have hnuisanceActual :
      (Real.sqrt (Fintype.card (NuisanceCoord B.HeadIndex) : ℝ) *
          (markedError B.sampleData.n * CL1)) ^ 2 / gamma ≤
        nuisanceLoss B.sampleData.n := by
    have hmul := mul_le_mul_of_nonneg_right hdim
      (mul_nonneg (hmarked0 B.sampleData.n) hCL1.le)
    have hsq := (sq_le_sq₀
      (mul_nonneg (Real.sqrt_nonneg _)
        (mul_nonneg (hmarked0 B.sampleData.n) hCL1.le))
      (mul_nonneg (by unfold nuisanceDimensionCeiling; positivity)
        (mul_nonneg (hmarked0 B.sampleData.n) hCL1.le))).2 hmul
    calc
      _ ≤ (nuisanceDimensionCeiling Head *
            (markedError B.sampleData.n * CL1)) ^ 2 / gamma :=
        div_le_div_of_nonneg_right hsq hgamma.le
      _ ≤ (nuisanceDimensionCeiling Head *
            (markedError B.sampleData.n * CL1)) ^ 2 / gammaFloor :=
        div_le_div_of_nonneg_left (sq_nonneg _) hgammaFloor
          hgammaFloorLe
      _ = nuisanceLoss B.sampleData.n := by rfl
  have hconstant : gammaSlow ≤
      B.paperScaleLemma86SlowConstantOfRow varianceFactor anchorFloor
        rowTarget (profileError B.sampleData.n) CKernel Creg K
        (1 / (B.sampleData.W : ℝ)) (R B.sampleData.n)
        (markedError B.sampleData.n) gamma := by
    have hloss := hlossN.le
    dsimp only [nuisanceLoss, CL1, slowL1Constant] at hnuisanceActual
    dsimp only [loss, nuisanceLoss, gammaSlow, main,
      paperScaleLemma86SlowConstantOfRow,
      paperScaleSquarefreeSlowConstant, slowL1Constant,
      slowL2Constant, signedSecondConstant, CL1, CL2, primeFactor]
      at hloss ⊢
    nlinarith [hnuisanceActual]
  have hbandTB : bandTReciprocalSum
      B.sampleData.n B.sampleData.W ≤ K := by
    simpa only [K, paperLemma86BandTConstant] using hbandTAt
  have hvarFactor : varianceFactor * B.w ^ 2 ≤
      B.partition.variance := by
    simpa only [varianceFactor, paperLemma86VarianceFactor] using
      paper_varianceFactor_mul_le hcMesh hvarLower
  have hfinite :=
    B.actualTwoStageCompensatedVariance_bounds_paperScale_of_weightedRow
      xi hgamma hgap e hCreg hK hRnonneg hvarianceFactor.le
      hrowTarget.le (hprofile0 B.sampleData.n) hCF.le hCKernel
      (hmarked0 B.sampleData.n) hBWlarge.le hsharp hbandTB
      hdevSup hdevL1 hvarFactor hdevL2 hvariance anchor hinterior
      hmass hAnchorMass hrowResidual hpair hsingle hF hKernel
      hactualRow hmarkedRows
  have hlower :=
    (mul_le_mul_of_nonneg_right hconstant (sq_nonneg B.w)).trans hfinite.1
  have hInvWone : 1 / (B.sampleData.W : ℝ) ≤ 1 :=
    PaperPrimePowerRow.reciprocalCutoff_le_one hBWlarge
  have hRupper : R B.sampleData.n ≤ Rmax := by
    have hmainW := mul_le_mul_of_nonneg_left hInvWone hCpow.le
    dsimp only [R, Rmax]
    linarith
  have hupperConstant :=
    paperScaleLemma86SlowUpperConstantOfRow_le_uniform (CF := CF)
      (hprofile0 B.sampleData.n) hprofileOneN hCKernel hCreg hK
      (by positivity) hInvWone hRupper
  have hupper := hfinite.2.trans
    (mul_le_mul_of_nonneg_right hupperConstant (sq_nonneg B.w))
  exact ⟨by simpa only [xi, gamma, hgap] using hlower,
    by simpa only [Cvar, xi, gamma, hgap] using hupper⟩

/-!
The final paper interface below deliberately repeats the quantitative
clauses instead of returning an opaque package.  Thus its type itself checks
that the geometry, inverse, regression, prime-power, variance, and marked-row
conclusions all use one and the same finite Schur equivalence `e z hz`.
-/


end BridgeData

end


end Erdos390.Full.PaperBridgeFit

end

universe u_1
theorem solution : Erdos390.RemainingAnalyticGoal003_002.{u_1} := by
  exact @Erdos390.Full.PaperBridgeFit.BridgeData.exists_paperFineMesh_cutoff_eventually_canonical_lemma86_variance_of_base
