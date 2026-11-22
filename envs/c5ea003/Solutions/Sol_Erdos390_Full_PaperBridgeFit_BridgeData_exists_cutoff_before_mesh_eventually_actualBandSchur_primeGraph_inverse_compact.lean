-- Prove2me | solution 1 for Erdos390.Full.PaperBridgeFit.BridgeData.exists_cutoff_before_mesh_eventually_actualBandSchur_primeGraph_inverse_compact
-- status  : ACCEPTED   (prove)
-- author  : @doctosil
-- created : 2026-09-17T17:15:10.587474+00:00
-- url     : https://prove2.me/submissions/7e12116c-7cf0-4de1-a770-f53115b3e4c6

import Definitions.Def_erdos390_remaining_analytic_propositions_001
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
import Theorems.Thm_Erdos390_Full_PaperBridgeFit_BridgeData_actualSquarefreeProjectedCLM_sub_arithmetic_le
import Theorems.Thm_Erdos390_Full_PaperBridgeFit_BridgeData_boxIndependent_canonicalRaw_fullSharp_compact
import Theorems.Thm_Erdos390_Full_PaperBridgeFit_BridgeData_eventually_exists_uniform_actualBandSchurEquiv_and_quadratic_compact
import Theorems.Thm_Erdos390_Full_PaperBridgeFit_BridgeData_exists_boxIndependent_actual_component_signed_profiles_compact
import Theorems.Thm_Erdos390_Full_PaperBridgeFit_BridgeData_exists_cutoff_before_mesh_eventually_referenceSharp_primeGraph_inverse_compact
import Theorems.Thm_Erdos390_Full_PaperCanonicalMarkedNuisanceRows_PaperBridgeFit_BridgeData_exists_uniform_canonical_tiltedLaw_nuisance_valuation_rate_on_effectiveBall_compact
import Theorems.Thm_Erdos390_Full_RegularMeshPrimeCutoffs_Mesh_canonicalCenterEnvelopeCutoff_eventually_inverse
import Theorems.Thm_Erdos390_Full_SquarefreeCovarianceReference_abs_sigmaMixture_covII_diagonal_sub_reference_le
import Theorems.Thm_Erdos390_Full_SquarefreeCovarianceReference_abs_sigmaMixture_covII_sub_squarefreeKernelEntry_le_of_squarefree_profiles
import Theorems.Thm_Erdos390_Full_SquarefreeReferenceOperatorIdentification_referenceBandRow_eq_rawOperator
import Theorems.Thm_Erdos390_Full_SquarefreeSharpBandTransfer_abs_squarefreeSharpRow_sub_referenceSharpRow_le






section
universe u_1 u_2
theorem Erdos390.Full.PaperCanonicalMarkedNuisanceRows.PaperBridgeFit.BridgeData.exists_uniform_canonical_tiltedLaw_nuisance_valuation_rate_on_effectiveBall : Erdos390.RemainingAnalyticGoal004_002.{u_1, u_2} := @Erdos390.Full.PaperCanonicalMarkedNuisanceRows.PaperBridgeFit.BridgeData.exists_uniform_canonical_tiltedLaw_nuisance_valuation_rate_on_effectiveBall_compact
end
section
universe u_1
theorem Erdos390.Full.PaperBridgeFit.BridgeData.exists_cutoff_before_mesh_eventually_referenceSharp_primeGraph_inverse : Erdos390.RemainingAnalyticGoal001_013.{u_1} := @Erdos390.Full.PaperBridgeFit.BridgeData.exists_cutoff_before_mesh_eventually_referenceSharp_primeGraph_inverse_compact
end
section
universe u_1 u_3
theorem Erdos390.Full.PaperBridgeFit.BridgeData.exists_boxIndependent_actual_component_signed_profiles : Erdos390.RemainingAnalyticGoal001_010.{u_1, u_3} := @Erdos390.Full.PaperBridgeFit.BridgeData.exists_boxIndependent_actual_component_signed_profiles_compact
end
section
universe u_1 u_3
theorem Erdos390.Full.PaperBridgeFit.BridgeData.boxIndependent_canonicalRaw_fullSharp : Erdos390.RemainingAnalyticGoal001_007.{u_1, u_3} := @Erdos390.Full.PaperBridgeFit.BridgeData.boxIndependent_canonicalRaw_fullSharp_compact
end
section
universe u_1 u_2
theorem Erdos390.Full.PaperBridgeFit.BridgeData.eventually_exists_uniform_actualBandSchurEquiv_and_quadratic : Erdos390.AnalyticCompactGoal002.{u_1, u_2} := @Erdos390.Full.PaperBridgeFit.BridgeData.eventually_exists_uniform_actualBandSchurEquiv_and_quadratic_compact
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

/- Source module: Erdos390.Full.StableInverse -/
section


/-!
# Stable inversion under an operator perturbation

This is the quantitative finite-dimensional perturbation lemma needed after
the continuum inverse has been transferred to the arithmetic gauge space.
It does not assume invertibility of the perturbed operator.  Instead it
derives it from a proved inverse for the reference operator and an operator
error smaller than the reciprocal inverse bound.
-/

namespace Erdos390.Full

noncomputable section

namespace StableInverse

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [FiniteDimensional ℝ X]







theorem perturbedEquiv_apply
    (A Ainv E : X →L[ℝ] X) (C delta : ℝ)
    (hC : 0 ≤ C)
    (hsmall : C * delta < 1)
    (hleft : ∀ x, Ainv (A x) = x)
    (hinv : ∀ y, ‖Ainv y‖ ≤ C * ‖y‖)
    (herror : ∀ x, ‖E x‖ ≤ delta * ‖x‖) (x : X) :
    perturbedEquiv A Ainv E C delta hC hsmall
      hleft hinv herror x = (A + E) x := by
  simp [perturbedEquiv]

theorem perturbed_inverse_bound_mul
    (A Ainv E : X →L[ℝ] X) (C delta : ℝ)
    (hC : 0 ≤ C)
    (hsmall : C * delta < 1)
    (hleft : ∀ x, Ainv (A x) = x)
    (hinv : ∀ y, ‖Ainv y‖ ≤ C * ‖y‖)
    (herror : ∀ x, ‖E x‖ ≤ delta * ‖x‖) (y : X) :
    (1 - C * delta) *
        ‖(perturbedEquiv A Ainv E C delta hC hsmall
          hleft hinv herror).symm y‖ ≤ C * ‖y‖ := by
  let e := perturbedEquiv A Ainv E C delta hC hsmall
    hleft hinv herror
  have hcontrol := reference_control A Ainv E C delta hC
    hleft hinv herror (e.symm y)
  have happ : (A + E) (e.symm y) = y := by
    rw [← perturbedEquiv_apply A Ainv E C delta hC hsmall
      hleft hinv herror]
    exact e.apply_symm_apply y
  simpa [e, happ] using hcontrol

theorem perturbed_inverse_bound
    (A Ainv E : X →L[ℝ] X) (C delta : ℝ)
    (hC : 0 ≤ C)
    (hsmall : C * delta < 1)
    (hleft : ∀ x, Ainv (A x) = x)
    (hinv : ∀ y, ‖Ainv y‖ ≤ C * ‖y‖)
    (herror : ∀ x, ‖E x‖ ≤ delta * ‖x‖) (y : X) :
    ‖(perturbedEquiv A Ainv E C delta hC hsmall
        hleft hinv herror).symm y‖ ≤
      (C / (1 - C * delta)) * ‖y‖ := by
  have hcoef : 0 < 1 - C * delta := sub_pos.mpr hsmall
  rw [show (C / (1 - C * delta)) * ‖y‖ =
      (C * ‖y‖) / (1 - C * delta) by ring]
  apply (le_div_iff₀ hcoef).2
  simpa [mul_comm] using
    perturbed_inverse_bound_mul A Ainv E C delta hC
      hsmall hleft hinv herror y

end StableInverse

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

/- Source module: Erdos390.Full.CompressedArithmeticOperator -/
section


/-!
# The actual compressed arithmetic operator

This file packages the diagonal and double-kernel cells used in the
arithmetic bridge, performs the sharp conjugation, and proves the complete
row aggregation estimate.  The moving low row is not discarded: its
normalization is exactly the one provided by the proved normalized
quadrature modules.

No inverse or spectral gap is an input here.  The output is the explicit
operator error that is fed to the finite graph inverse and then to
`StableInverse`.
-/

open scoped BigOperators

noncomputable section

namespace Erdos390.Full.CompressedArithmeticOperator

open DoubleKernelPrimeQuadrature DiagonalPrimeQuadrature
open FiniteGraphQuotientInverse

variable {Band : Type*} [Fintype Band]









/-! ## Endpoint-specialized arithmetic and continuum matrices -/















/-! ## Projection to the actual arithmetic gauge -/

/-- A positive weighted projection costs at most a factor two in the
pointwise norm.  This applies to the actual sharp weights
`H_j alpha_j^2`, including the moving low band. -/
theorem abs_meanProjection_sub_le
    (omega x y : Band → ℝ) (R : ℝ)
    (homega : ∀ j, 0 ≤ omega j)
    (hTotal : 0 < ∑ j, omega j)
    (hxy : ∀ j, |x j - y j| ≤ R)
    (i : Band) :
    |meanProjection omega x i - meanProjection omega y i| ≤ 2 * R := by
  have htotal0 : (∑ j, omega j) ≠ 0 := ne_of_gt hTotal
  have hmean : |weightedMean omega x - weightedMean omega y| ≤ R := by
    have hidentity :
        weightedMean omega x - weightedMean omega y =
          (∑ j, omega j * (x j - y j)) / ∑ j, omega j := by
      unfold weightedMean weightTotal
      have hsum :
          (∑ j, omega j * x j) - ∑ j, omega j * y j =
            ∑ j, omega j * (x j - y j) := by
        rw [← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro j hj
        ring
      rw [show (∑ j, omega j * x j) / (∑ j, omega j) -
          (∑ j, omega j * y j) / (∑ j, omega j) =
          ((∑ j, omega j * x j) - ∑ j, omega j * y j) /
            (∑ j, omega j) by field_simp [htotal0]]
      rw [hsum]
    rw [hidentity, abs_div, abs_of_pos hTotal]
    apply (div_le_iff₀ hTotal).2
    calc
      |∑ j, omega j * (x j - y j)| ≤
          ∑ j, |omega j * (x j - y j)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j, omega j * R := by
        apply Finset.sum_le_sum
        intro j hj
        rw [abs_mul, abs_of_nonneg (homega j)]
        exact mul_le_mul_of_nonneg_left (hxy j) (homega j)
      _ = R * ∑ j, omega j := by
        rw [← Finset.sum_mul]
        ring
  unfold meanProjection
  calc
    |(x i - weightedMean omega x) -
        (y i - weightedMean omega y)| =
    |(x i - y i) -
          (weightedMean omega x - weightedMean omega y)| := by ring
    _ = |(x i - y i) +
        (-(weightedMean omega x - weightedMean omega y))| := by
      rw [sub_eq_add_neg]
    _ ≤ |x i - y i| +
        |-(weightedMean omega x - weightedMean omega y)| := abs_add_le _ _
    _ = |x i - y i| +
        |weightedMean omega x - weightedMean omega y| := by rw [abs_neg]
    _ ≤ R + R := add_le_add (hxy i) hmean
    _ = 2 * R := by ring

end Erdos390.Full.CompressedArithmeticOperator

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

















omit [Fintype Band] [DecidableEq Band] in
theorem sharpWeight_nonneg_of_mass_nonneg
    (H alpha : Band → ℝ) (hH : ∀ j, 0 ≤ H j) (j : Band) :
    0 ≤ sharpWeight H alpha j := by
  exact mul_nonneg (hH j) (sq_nonneg (alpha j))















end SharpProjection

end Erdos390.Full.MovingLowGaugeTransfer

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

/- Source module: Erdos390.Full.SquarefreeReferenceOperatorIdentification -/
section


/-!
# Exact identification of the signed squarefree reference operator

The signed reference covariance used in the arithmetic part of paper
Lemma 8.4 is defined prime by prime in
`SquarefreeCovarianceReference`.  The moving-low inverse, on the other
hand, is proved for the endpoint matrix called `arithmeticDiagonal` plus
`arithmeticKernel`.  This file proves that these are literally the same
finite operator for every certified prime partition.  No limit, row bound,
covariance estimate, or inverse is assumed.
-/

open scoped BigOperators

noncomputable section

namespace Erdos390.Full.SquarefreeReferenceOperatorIdentification

open ArithmeticModel ArithmeticBandGeometry
open SquarefreeCovarianceReference SquarefreeSharpBandTransfer
open PositiveCellTransfer
open DoubleKernelPrimeQuadrature DiagonalPrimeQuadrature
open CompressedArithmeticOperator
open ConditionedPoissonLimit DickmanBasic

variable {n W : ℕ} {Band : Type*} [Fintype Band] [DecidableEq Band]
variable {P : Partition n W Band}













/-- After the exact centre conjugation, the reference sharp row is exactly
the canonical arithmetic sharp operator used by the inverse theorem. -/
theorem referenceSharpRow_eq_arithmeticSharpOperator
    (E : IntervalCertificate P) (q : Band → ℝ) (i : Band)
    (hcenter : P.center i ≠ 0) :
    referenceSharpRow P q i =
      arithmeticSharpOperator (y n) E.lower E.upper P.center q i := by
  unfold referenceSharpRow arithmeticSharpOperator
  rw [referenceBandRow_eq_rawOperator E]
  unfold PaperWeightedInverseExport.rawOperator sharpOperator
  apply (div_eq_iff hcenter).2
  simp only
  rw [add_mul, Finset.sum_mul]
  apply congrArg₂ (fun x y : ℝ ↦ x + y)
  · ring
  · apply Finset.sum_congr rfl
    intro j hj
    field_simp [hcenter]

section MarkedProfileApplication

variable {Cell : Type*} [Fintype Cell]
variable {Omega : Cell → Type*} [∀ c, Fintype (Omega c)]
variable {M : ℕ}

/-- The common marked one- and two-divisor profiles, including the exact
between-cell covariance of the reweighted sigma mixture, feed directly into
the canonical arithmetic sharp operator.  This theorem is the assumption-free
connector between the signed probability comparison and the deterministic
moving-low inverse: its hypotheses are precisely the local marked-profile
estimates, not an operator comparison or inverse bound. -/
theorem abs_sigmaMixture_squarefreeSharpRow_sub_arithmeticSharpOperator_le
    (cert : IntervalCertificate P)
    {Eprofile CKernel : ℝ} (hEprofile : 0 ≤ Eprofile)
    (weight : FiniteProbability Cell)
    (law : ∀ c, PrimePowerCovariance.BoundedValuationLaw (Omega c) M)
    (hn : 1 < n) (hW : 1 < W)
    (hpair : ∀ c p, p ∈ primeBand n W →
      ∀ q, q ∈ (primeBand n W).erase p →
      |(law c).probability.expect
          (fun omega ↦ divInd (OmittedTiltPairChamber.pairPower p q 1 1)
            ((law c).value omega)) -
        PaperScaleMarkedCell.paperDivisibilityMain n
          (OmittedTiltPairChamber.pairPower p q 1 1)| ≤
        Eprofile * PaperPrimePowerChamberError.pairWeight p q 1 1)
    (hsingle : ∀ c p, p ∈ primeBand n W →
      |(law c).probability.expect
          (fun omega ↦ divInd p ((law c).value omega)) -
        PaperScaleMarkedCell.paperDivisibilityMain n p| ≤
          Eprofile * PaperPrimePowerChamberError.singleWeight p 1)
    (hKernel : ∀ p ∈ primeBand n W,
      |ConditionedPoissonLimit.covarianceKernel
          (tPrime n p) (tPrime n p)| ≤ CKernel)
    (q : Band → ℝ) (hq : ∀ j, |q j| ≤ 1) (i : Band) :
    let mix := PrimePowerCovariance.BoundedValuationLaw.sigmaMixture weight law
    |squarefreeSharpRow mix P q i -
        arithmeticSharpOperator (y n) cert.lower cert.upper P.center q i| ≤
      (4 * PaperPrimePowerChamberError.pairCovarianceScale Eprofile) *
          PrimeSums.bandTReciprocalSum n W / P.center i +
        2 * Eprofile +
        ((1 / DickmanBasic.rho DickmanBasic.U + 2 * Eprofile) ^ 2 +
            CKernel) * (1 / (W : ℝ)) := by
  dsimp only
  let mix := PrimePowerCovariance.BoundedValuationLaw.sigmaMixture weight law
  have hentry :=
    SquarefreeCovarianceReference.sigmaMixture_squarefree_reference_entry_bound_of_squarefree_profiles
      hEprofile weight law hn hpair hsingle hKernel
  have hCKernel : 0 ≤ CKernel := by
    obtain ⟨p, hpband⟩ := P.fiber_nonempty i
    exact (abs_nonneg
      (ConditionedPoissonLimit.covarianceKernel
        (tPrime n p.1) (tPrime n p.1))).trans
          (hKernel p.1 p.2)
  have hCdiag :
      0 ≤ (1 / DickmanBasic.rho DickmanBasic.U + 2 * Eprofile) ^ 2 +
        CKernel := add_nonneg (sq_nonneg _) hCKernel
  have hsharp :=
    SquarefreeSharpBandTransfer.abs_squarefreeSharpRow_sub_referenceSharpRow_le
      mix P hn hW hCdiag hentry q hq i
  rw [referenceSharpRow_eq_arithmeticSharpOperator cert q i
    (ne_of_gt (P.center_pos hn i))] at hsharp
  simpa only [mix, mul_assoc] using hsharp

end MarkedProfileApplication

end Erdos390.Full.SquarefreeReferenceOperatorIdentification

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

/-- Exact actual-law specialization of the signed-profile-to-canonical-row
connector.  The hypotheses are local one- and two-divisor estimates; the
global component weights, their partition functions, and all between-cell
covariance terms are handled by the theorem rather than assumed away. -/
theorem abs_actual_squarefreeSharpRow_sub_arithmeticSharpOperator_le
    [Nonempty Head]
    (xi : B.ParamSpace)
    (cert : Erdos390.Full.PositiveCellTransfer.IntervalCertificate B.partition)
    {Eprofile CKernel : ℝ} (hEprofile : 0 ≤ Eprofile)
    (hn : 1 < B.sampleData.n) (hW : 1 < B.sampleData.W)
    (hpair : ∀ c p, p ∈ primeBand B.sampleData.n B.sampleData.W →
      ∀ q, q ∈ (primeBand B.sampleData.n B.sampleData.W).erase p →
      |(B.actualComponentValuationLaw xi c).probability.expect
          (fun omega ↦ divInd (pairPower p q 1 1)
            ((B.actualComponentValuationLaw xi c).value omega)) -
        PaperScaleMarkedCell.paperDivisibilityMain B.sampleData.n
          (pairPower p q 1 1)| ≤
        Eprofile * pairWeight p q 1 1)
    (hsingle : ∀ c p, p ∈ primeBand B.sampleData.n B.sampleData.W →
      |(B.actualComponentValuationLaw xi c).probability.expect
          (fun omega ↦ divInd p
            ((B.actualComponentValuationLaw xi c).value omega)) -
        PaperScaleMarkedCell.paperDivisibilityMain B.sampleData.n p| ≤
        Eprofile * singleWeight p 1)
    (hKernel : ∀ p ∈ primeBand B.sampleData.n B.sampleData.W,
      |ConditionedPoissonLimit.covarianceKernel
          (tPrime B.sampleData.n p) (tPrime B.sampleData.n p)| ≤ CKernel)
    (q : Band → ℝ) (hq : ∀ j, |q j| ≤ 1) (i : Band) :
    |SquarefreeSharpBandTransfer.squarefreeSharpRow
        (B.actualValuationLaw xi) B.partition q i -
      CompressedArithmeticOperator.arithmeticSharpOperator
        (y B.sampleData.n) cert.lower cert.upper
        B.partition.center q i| ≤
      (4 * PaperPrimePowerChamberError.pairCovarianceScale Eprofile) *
          PrimeSums.bandTReciprocalSum B.sampleData.n B.sampleData.W /
            B.partition.center i +
        2 * Eprofile +
        ((1 / DickmanBasic.rho DickmanBasic.U + 2 * Eprofile) ^ 2 +
            CKernel) * (1 / (B.sampleData.W : ℝ)) := by
  let weight := tiltedSigmaWeight B.baselineCellProbability
    B.guardedCellProbability (B.scaledBridgeScore xi)
  have hraw :=
    SquarefreeReferenceOperatorIdentification.abs_sigmaMixture_squarefreeSharpRow_sub_arithmeticSharpOperator_le
      (P := B.partition) (M := B.sampleEndpoint)
      cert hEprofile weight
      (B.actualComponentValuationLaw xi) hn hW hpair hsingle hKernel q hq i
  have hlaw := B.sigmaMixture_actualComponentValuationLaw_eq_actualValuationLaw xi
  dsimp only at hlaw
  rw [hlaw] at hraw
  simpa only [weight] using hraw



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

/-- A profile with `E log L → 0` produces a vanishing moving-low row term.
The only surviving term is the explicit diagonal `1/W` correction, which is
selected before the ambient limit. -/
theorem tendsto_squarefreeSharpProfileRemainder
    (E : ℕ → ℝ) (Calpha K CKernel : ℝ) (W : ℕ)
    (hE : Filter.Tendsto E Filter.atTop (nhds 0))
    (hERate : Filter.Tendsto
      (fun n : ℕ ↦ E n * Real.log (Scale.L n))
        Filter.atTop (nhds 0)) :
    Filter.Tendsto
      (squarefreeSharpProfileRemainder E Calpha K CKernel W)
      Filter.atTop
      (nhds (((1 / DickmanBasic.rho DickmanBasic.U) ^ 2 + CKernel) *
        (1 / (W : ℝ)))) := by
  have hcovRate := tendsto_pairCovarianceScale_mul_logL_zero E hE hERate
  have hmoving : Filter.Tendsto
      (fun n : ℕ ↦
        (4 * PaperPrimePowerChamberError.pairCovarianceScale (E n)) * K *
          (Calpha * Real.log (Scale.L n)))
        Filter.atTop (nhds 0) := by
    let c : ℝ := 4 * K * Calpha
    have hraw : Filter.Tendsto
        (fun n : ℕ ↦ c *
          (PaperPrimePowerChamberError.pairCovarianceScale (E n) *
            Real.log (Scale.L n))) Filter.atTop (nhds 0) := by
      simpa only [mul_zero] using
        (tendsto_const_nhds.mul hcovRate : Filter.Tendsto
          (fun n : ℕ ↦ c *
            (PaperPrimePowerChamberError.pairCovarianceScale (E n) *
              Real.log (Scale.L n))) Filter.atTop (nhds (c * 0)))
    apply hraw.congr'
    filter_upwards with n
    dsimp only [c]
    ring
  have hlinear : Filter.Tendsto (fun n : ℕ ↦ 2 * E n)
      Filter.atTop (nhds 0) := by
    simpa only [mul_zero] using
      (tendsto_const_nhds.mul hE : Filter.Tendsto
        (fun n : ℕ ↦ (2 : ℝ) * E n) Filter.atTop (nhds (2 * 0)))
  let a : ℝ := 1 / DickmanBasic.rho DickmanBasic.U
  have hinside : Filter.Tendsto (fun n : ℕ ↦ a + 2 * E n)
      Filter.atTop (nhds a) := by
    simpa only [add_zero] using tendsto_const_nhds.add hlinear
  have hlast : Filter.Tendsto
      (fun n : ℕ ↦ ((a + 2 * E n) ^ 2 + CKernel) * (1 / (W : ℝ)))
      Filter.atTop (nhds ((a ^ 2 + CKernel) * (1 / (W : ℝ)))) := by
    exact (hinside.pow 2 |>.add tendsto_const_nhds).mul tendsto_const_nhds
  have hsum := (hmoving.add hlinear).add hlast
  simpa only [squarefreeSharpProfileRemainder, a, zero_add] using hsum

/-- Pointwise moving-low specialization of the actual squarefree reference
bound.  This theorem makes the delicate use of `alpha_0` explicit: the only
input is the quantitative envelope `1/alpha_i ≤ Calpha log L`, and no bare
`o(1)` error is accepted. -/
theorem abs_actual_squarefreeSharpRow_sub_arithmetic_le_profileRemainder
    [Nonempty Head]
    (xi : B.ParamSpace)
    (cert : Erdos390.Full.PositiveCellTransfer.IntervalCertificate B.partition)
    {Eprofile Calpha K CKernel : ℝ}
    (hEprofile : 0 ≤ Eprofile)
    (hW : 1 < B.sampleData.W)
    (hpair : ∀ c p, p ∈ primeBand B.sampleData.n B.sampleData.W →
      ∀ q, q ∈ (primeBand B.sampleData.n B.sampleData.W).erase p →
      |(B.actualComponentValuationLaw xi c).probability.expect
          (fun omega ↦ divInd (pairPower p q 1 1)
            ((B.actualComponentValuationLaw xi c).value omega)) -
        PaperScaleMarkedCell.paperDivisibilityMain B.sampleData.n
          (pairPower p q 1 1)| ≤
        Eprofile * pairWeight p q 1 1)
    (hsingle : ∀ c p, p ∈ primeBand B.sampleData.n B.sampleData.W →
      |(B.actualComponentValuationLaw xi c).probability.expect
          (fun omega ↦ divInd p
            ((B.actualComponentValuationLaw xi c).value omega)) -
        PaperScaleMarkedCell.paperDivisibilityMain B.sampleData.n p| ≤
        Eprofile * singleWeight p 1)
    (hKernel : ∀ p ∈ primeBand B.sampleData.n B.sampleData.W,
      |ConditionedPoissonLimit.covarianceKernel
          (tPrime B.sampleData.n p) (tPrime B.sampleData.n p)| ≤ CKernel)
    (hBandT : PrimeSums.bandTReciprocalSum
      B.sampleData.n B.sampleData.W ≤ K)
    (hcenterInv : ∀ i : Band,
      1 / B.partition.center i ≤
        Calpha * Real.log (Scale.L B.sampleData.n))
    (q : Band → ℝ) (hq : ∀ j, |q j| ≤ 1) (i : Band) :
    |SquarefreeSharpBandTransfer.squarefreeSharpRow
        (B.actualValuationLaw xi) B.partition q i -
      CompressedArithmeticOperator.arithmeticSharpOperator
        (y B.sampleData.n) cert.lower cert.upper
        B.partition.center q i| ≤
      squarefreeSharpProfileRemainder
        (fun _n ↦ Eprofile) Calpha K CKernel
          B.sampleData.W B.sampleData.n := by
  have hbase := B.abs_actual_squarefreeSharpRow_sub_arithmeticSharpOperator_le
    xi cert hEprofile B.n_gt_one
      hW hpair hsingle hKernel q hq i
  have hcov0 : 0 ≤
      4 * PaperPrimePowerChamberError.pairCovarianceScale Eprofile :=
    mul_nonneg (by norm_num)
      (PaperPrimePowerChamberError.pairCovarianceScale_nonneg hEprofile)
  have hBandT0 : 0 ≤ PrimeSums.bandTReciprocalSum
      B.sampleData.n B.sampleData.W := by
    unfold PrimeSums.bandTReciprocalSum
    apply Finset.sum_nonneg
    intro p hp
    exact div_nonneg (B.bandPrime_tPrime_pos ⟨p, hp⟩).le (by positivity)
  have hK0' : 0 ≤ K := hBandT0.trans hBandT
  have hcenterPos : 0 < B.partition.center i :=
    B.partition.center_pos B.n_gt_one i
  have hmoving :
      (4 * PaperPrimePowerChamberError.pairCovarianceScale Eprofile) *
          PrimeSums.bandTReciprocalSum
            B.sampleData.n B.sampleData.W / B.partition.center i ≤
        (4 * PaperPrimePowerChamberError.pairCovarianceScale Eprofile) * K *
          (Calpha * Real.log (Scale.L B.sampleData.n)) := by
    calc
      (4 * PaperPrimePowerChamberError.pairCovarianceScale Eprofile) *
            PrimeSums.bandTReciprocalSum
              B.sampleData.n B.sampleData.W / B.partition.center i =
          (4 * PaperPrimePowerChamberError.pairCovarianceScale Eprofile) *
            PrimeSums.bandTReciprocalSum
              B.sampleData.n B.sampleData.W *
                (1 / B.partition.center i) := by ring
      _ ≤ (4 * PaperPrimePowerChamberError.pairCovarianceScale Eprofile) * K *
            (1 / B.partition.center i) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hBandT hcov0)
          (one_div_nonneg.mpr hcenterPos.le)
      _ ≤ (4 * PaperPrimePowerChamberError.pairCovarianceScale Eprofile) * K *
            (Calpha * Real.log (Scale.L B.sampleData.n)) := by
        exact mul_le_mul_of_nonneg_left (hcenterInv i)
          (mul_nonneg hcov0 hK0')
  unfold squarefreeSharpProfileRemainder
  exact hbase.trans (by linarith [hmoving])



/-! ### Exact finite-dimensional attachment to the arithmetic inverse -/













/-- A proved arithmetic-reference inverse and the proved unit row comparison
produce an inverse for the literal actual squarefree projected operator.
Invertibility of the perturbed operator is a conclusion, not an input. -/
theorem exists_actualSquarefreeProjectedEquiv_of_reference
    [Nonempty Head]
    (xi : B.ParamSpace)
    (cert : Erdos390.Full.PositiveCellTransfer.IntervalCertificate B.partition)
    (referenceEquiv :
      PaperWeightedInverseExport.SharpGaugeSpace
          B.partition.mass B.partition.center ≃L[ℝ]
        PaperWeightedInverseExport.SharpGaugeSpace
          B.partition.mass B.partition.center)
    (hreference : ∀ q, referenceEquiv q =
      ArithmeticGaugeStableInverse.projectedSharpCLM
        (CompressedArithmeticOperator.arithmeticDiagonal
          (y B.sampleData.n) cert.lower cert.upper)
        (CompressedArithmeticOperator.arithmeticKernel
          (y B.sampleData.n) cert.lower cert.upper)
        B.partition.center
        (MovingLowGaugeTransfer.sharpWeight
          B.partition.mass B.partition.center)
        (ne_of_gt (actualSharpWeightTotal_pos B)) q)
    {C r : ℝ} (hC : 0 ≤ C) (hr : 0 ≤ r)
    (hinv : ∀ v, ‖referenceEquiv.symm v‖ ≤ C * ‖v‖)
    (hsmall : C * (2 * r) < 1)
    (hrow : ∀ (q : Band → ℝ), (∀ j, |q j| ≤ 1) → ∀ i : Band,
      |SquarefreeSharpBandTransfer.squarefreeSharpRow
          (B.actualValuationLaw xi) B.partition q i -
        CompressedArithmeticOperator.arithmeticSharpOperator
          (y B.sampleData.n) cert.lower cert.upper
            B.partition.center q i| ≤ r) :
    ∃ actualEquiv :
      PaperWeightedInverseExport.SharpGaugeSpace
          B.partition.mass B.partition.center ≃L[ℝ]
        PaperWeightedInverseExport.SharpGaugeSpace
          B.partition.mass B.partition.center,
      (∀ q, actualEquiv q = B.actualSquarefreeProjectedCLM xi q) ∧
      ∀ v, ‖actualEquiv.symm v‖ ≤
        (C / (1 - C * (2 * r))) * ‖v‖ := by
  let A := ArithmeticGaugeStableInverse.projectedSharpCLM
    (CompressedArithmeticOperator.arithmeticDiagonal
      (y B.sampleData.n) cert.lower cert.upper)
    (CompressedArithmeticOperator.arithmeticKernel
      (y B.sampleData.n) cert.lower cert.upper)
    B.partition.center
    (MovingLowGaugeTransfer.sharpWeight
      B.partition.mass B.partition.center)
    (ne_of_gt (actualSharpWeightTotal_pos B))
  let Ainv : PaperWeightedInverseExport.SharpGaugeSpace
      B.partition.mass B.partition.center →L[ℝ]
      PaperWeightedInverseExport.SharpGaugeSpace
        B.partition.mass B.partition.center := referenceEquiv.symm
  let E := B.actualSquarefreeProjectedCLM xi - A
  have hleft (q : PaperWeightedInverseExport.SharpGaugeSpace
      B.partition.mass B.partition.center) : Ainv (A q) = q := by
    dsimp only [Ainv, A]
    rw [← hreference q]
    exact referenceEquiv.symm_apply_apply q
  have hinv' (v : PaperWeightedInverseExport.SharpGaugeSpace
      B.partition.mass B.partition.center) : ‖Ainv v‖ ≤ C * ‖v‖ := hinv v
  have herror (q : PaperWeightedInverseExport.SharpGaugeSpace
      B.partition.mass B.partition.center) :
      ‖E q‖ ≤ (2 * r) * ‖q‖ := by
    dsimp only [E, A]
    exact B.actualSquarefreeProjectedCLM_sub_arithmetic_le
      xi cert hr hrow q
  let actualEquiv := StableInverse.perturbedEquiv
    A Ainv E C (2 * r) hC hsmall hleft hinv' herror
  refine ⟨actualEquiv, ?_, ?_⟩
  · intro q
    rw [StableInverse.perturbedEquiv_apply]
    dsimp only [actualEquiv, E]
    simp only [add_sub_cancel]
  · intro v
    exact StableInverse.perturbed_inverse_bound
      A Ainv E C (2 * r) hC hsmall hleft hinv' herror v













/-! ### Reference-law row attachment

The literal global-tilt form of Lemma 7.5 is naturally obtained first for an
unguarded component mixture.  The actual bridge law is a guard-deleted
mixture with a residual physical tilt.  The next elementary estimate keeps
that identification issue outside the prime-power algebra: a weighted
prime-row comparison for the full and squarefree covariance matrices moves
the Lemma 7.5 estimate from an arbitrary reference law to the actual law.
The only moving-low loss is displayed explicitly as `rho / center i`.
-/











/-- A literal unit sharp-row estimate yields the projected operator-norm
estimate with the exact factor two from weighted-mean projection.  This
public form lets the fully assembled canonical Lemma 7.5 row be consumed
without re-exposing its internal reference law or transfer certificate. -/
theorem actualFullProjectedCLM_sub_squarefree_le_of_unitSharpRows
    [Nonempty Head]
    (xi : B.ParamSpace) {rpow : ℝ} (hrpow : 0 ≤ rpow)
    (hunit : ∀ q : Band → ℝ, (∀ j, |q j| ≤ 1) → ∀ i : Band,
      |PrimePowerSharpBandTransfer.fullSharpRow
          (B.actualValuationLaw xi) B.partition q i -
        SquarefreeSharpBandTransfer.squarefreeSharpRow
          (B.actualValuationLaw xi) B.partition q i| ≤ rpow)
    (q : PaperWeightedInverseExport.SharpGaugeSpace
      B.partition.mass B.partition.center) :
    ‖(B.actualFullProjectedCLM xi -
        B.actualSquarefreeProjectedCLM xi) q‖ ≤
      (2 * rpow) * ‖q‖ := by
  let omega := MovingLowGaugeTransfer.sharpWeight
    B.partition.mass B.partition.center
  let fullRow : (Band → ℝ) → Band → ℝ := fun b i ↦
    PrimePowerSharpBandTransfer.fullSharpRow
      (B.actualValuationLaw xi) B.partition b i
  let squarefreeRow : (Band → ℝ) → Band → ℝ := fun b i ↦
    SquarefreeSharpBandTransfer.squarefreeSharpRow
      (B.actualValuationLaw xi) B.partition b i
  have hraw (i : Band) :
      |fullRow q.1 i - squarefreeRow q.1 i| ≤ rpow * ‖q‖ := by
    by_cases hqzero : ‖q‖ = 0
    · have hq0 : q = 0 := norm_eq_zero.mp hqzero
      subst q
      have hfull : fullRow (0 : Band → ℝ) i = 0 := by
        simpa only [fullRow, zero_smul, zero_mul] using
          B.fullSharpRow_smul xi 0 (0 : Band → ℝ) i
      have hsf : squarefreeRow (0 : Band → ℝ) i = 0 := by
        simpa only [squarefreeRow, zero_smul, zero_mul] using
          B.squarefreeSharpRow_smul xi 0 (0 : Band → ℝ) i
      have hcoe :
          (((0 : PaperWeightedInverseExport.SharpGaugeSpace
            B.partition.mass B.partition.center) :
              PaperWeightedInverseExport.SharpGaugeSpace
                B.partition.mass B.partition.center) : Band → ℝ) = 0 := rfl
      rw [hcoe]
      rw [hfull, hsf, sub_self, abs_zero, norm_zero, mul_zero]
    · have hqpos : 0 < ‖q‖ :=
        lt_of_le_of_ne (norm_nonneg q) (Ne.symm hqzero)
      let q0 : Band → ℝ := fun j ↦ q.1 j / ‖q‖
      have hq0unit (j : Band) : |q0 j| ≤ 1 := by
        have hj : |q.1 j| ≤ ‖q‖ := by
          rw [← Real.norm_eq_abs]
          exact norm_le_pi_norm q.1 j
        dsimp only [q0]
        rw [abs_div, abs_of_pos hqpos]
        exact (div_le_one hqpos).2 hj
      have hunit' : |fullRow q0 i - squarefreeRow q0 i| ≤ rpow := by
        exact hunit q0 hq0unit i
      have hqEq : q.1 = ‖q‖ • q0 := by
        funext j
        dsimp only [q0]
        simp only [Pi.smul_apply, smul_eq_mul]
        field_simp [hqzero]
      have hfull : fullRow q.1 i = ‖q‖ * fullRow q0 i := by
        rw [hqEq]
        exact B.fullSharpRow_smul xi ‖q‖ q0 i
      have hsf : squarefreeRow q.1 i = ‖q‖ * squarefreeRow q0 i := by
        rw [hqEq]
        exact B.squarefreeSharpRow_smul xi ‖q‖ q0 i
      rw [hfull, hsf, ← mul_sub, abs_mul, abs_of_pos hqpos]
      exact (mul_le_mul_of_nonneg_left hunit' hqpos.le).trans_eq
        (mul_comm ‖q‖ rpow)
  have hprojected (i : Band) :
      |FiniteGraphQuotientInverse.meanProjection omega
          (fullRow q.1) i -
        FiniteGraphQuotientInverse.meanProjection omega
          (squarefreeRow q.1) i| ≤ 2 * (rpow * ‖q‖) :=
    CompressedArithmeticOperator.abs_meanProjection_sub_le omega
      (fullRow q.1) (squarefreeRow q.1) (rpow * ‖q‖)
      (fun i ↦ MovingLowGaugeTransfer.sharpWeight_nonneg_of_mass_nonneg
        B.partition.mass B.partition.center
          (fun j ↦ (B.partition.data.mass_pos j).le) i)
      (actualSharpWeightTotal_pos B) hraw i
  have hnonneg : 0 ≤ (2 * rpow) * ‖q‖ := by positivity
  change ‖(((B.actualFullProjectedCLM xi -
      B.actualSquarefreeProjectedCLM xi) q :
        PaperWeightedInverseExport.SharpGaugeSpace
          B.partition.mass B.partition.center) : Band → ℝ)‖ ≤
    (2 * rpow) * ‖q‖
  rw [pi_norm_le_iff_of_nonneg hnonneg]
  intro i
  rw [Real.norm_eq_abs]
  exact hprojected i |>.trans_eq (by ring)









end BridgeData

end

end Erdos390.Full.PaperBridgeFit

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

/- Source module: Erdos390.Full.PaperActualFullProjectedInverseAssembly -/
section


/-!
# Direct finite assembly of the actual full projected inverse

The analytic prime-power work naturally exports a unit sharp-row estimate.
This file consumes that estimate directly, after the squarefree projected
operator has been inverted.  No reference law or Lemma 7.5 certificate is
carried as an additional hypothesis at this deterministic layer.
-/

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

open PaperWeightedInverseExport

namespace BridgeData

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]
  (B : BridgeData Head Band)

/-- Stable inverse for the actual full-valuation projected operator from a
proved squarefree inverse and the literal full-vs-squarefree unit row. -/
theorem exists_actualFullProjectedEquiv_of_squarefree_of_unitSharpRows
    [Nonempty Head]
    (xi : B.ParamSpace)
    (squarefreeEquiv :
      SharpGaugeSpace B.partition.mass B.partition.center ≃L[ℝ]
        SharpGaugeSpace B.partition.mass B.partition.center)
    (hsquarefree : ∀ q, squarefreeEquiv q =
      B.actualSquarefreeProjectedCLM xi q)
    {C rpow : ℝ}
    (hC : 0 ≤ C) (hrpow : 0 ≤ rpow)
    (hinv : ∀ v, ‖squarefreeEquiv.symm v‖ ≤ C * ‖v‖)
    (hsmall : C * (2 * rpow) < 1)
    (hunit : ∀ q : Band → ℝ, (∀ j, |q j| ≤ 1) → ∀ i : Band,
      |PrimePowerSharpBandTransfer.fullSharpRow
          (B.actualValuationLaw xi) B.partition q i -
        SquarefreeSharpBandTransfer.squarefreeSharpRow
          (B.actualValuationLaw xi) B.partition q i| ≤ rpow) :
    ∃ actualEquiv :
      SharpGaugeSpace B.partition.mass B.partition.center ≃L[ℝ]
        SharpGaugeSpace B.partition.mass B.partition.center,
      (∀ q, actualEquiv q = B.actualFullProjectedCLM xi q) ∧
      ∀ v, ‖actualEquiv.symm v‖ ≤
        (C / (1 - C * (2 * rpow))) * ‖v‖ := by
  let A := B.actualSquarefreeProjectedCLM xi
  let Ainv : SharpGaugeSpace B.partition.mass B.partition.center →L[ℝ]
      SharpGaugeSpace B.partition.mass B.partition.center :=
    squarefreeEquiv.symm
  let E := B.actualFullProjectedCLM xi - A
  have hleft (q : SharpGaugeSpace
      B.partition.mass B.partition.center) : Ainv (A q) = q := by
    dsimp only [Ainv, A]
    rw [← hsquarefree q]
    exact squarefreeEquiv.symm_apply_apply q
  have hinv' (v : SharpGaugeSpace
      B.partition.mass B.partition.center) : ‖Ainv v‖ ≤ C * ‖v‖ :=
    hinv v
  have herror (q : SharpGaugeSpace
      B.partition.mass B.partition.center) :
      ‖E q‖ ≤ (2 * rpow) * ‖q‖ := by
    dsimp only [E, A]
    exact B.actualFullProjectedCLM_sub_squarefree_le_of_unitSharpRows
      xi hrpow hunit q
  let actualEquiv := StableInverse.perturbedEquiv
    A Ainv E C (2 * rpow) hC hsmall hleft hinv' herror
  refine ⟨actualEquiv, ?_, ?_⟩
  · intro q
    rw [StableInverse.perturbedEquiv_apply]
    dsimp only [actualEquiv, E]
    simp only [add_sub_cancel]
  · intro v
    exact StableInverse.perturbed_inverse_bound
      A Ainv E C (2 * rpow) hC hsmall hleft hinv' herror v

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









theorem canonicalProjectedPerturbationRadius_pos
    {C : ℝ} (hC : 0 < C) :
    0 < canonicalProjectedPerturbationRadius C := by
  exact div_pos (by norm_num) (mul_pos (by norm_num) hC)

theorem canonicalProjectedPerturbationRadius_first_small
    {C : ℝ} (hC : 0 < C) :
    C * (2 * canonicalProjectedPerturbationRadius C) < 1 := by
  unfold canonicalProjectedPerturbationRadius
  field_simp [ne_of_gt hC]
  norm_num

theorem canonicalProjectedPerturbationRadius_second_small
    {C : ℝ} (hC : 0 < C) :
    (C / (1 - C * (2 * canonicalProjectedPerturbationRadius C))) *
        (2 * canonicalProjectedPerturbationRadius C) < 1 := by
  unfold canonicalProjectedPerturbationRadius
  field_simp [ne_of_gt hC]
  norm_num

theorem canonicalProjectedPerturbation_finalConstant
    {C : ℝ} (hC : 0 < C) :
    (C / (1 - C * (2 * canonicalProjectedPerturbationRadius C))) /
        (1 - (C / (1 - C *
          (2 * canonicalProjectedPerturbationRadius C))) *
            (2 * canonicalProjectedPerturbationRadius C)) =
      2 * C := by
  unfold canonicalProjectedPerturbationRadius
  field_simp [ne_of_gt hC]
  ring



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



/-- The two sharp moving-low rates leave only the explicit fixed-cutoff
prime-power loss. -/
theorem tendsto_canonicalFullSharpRemainder
    (epsilon combined : ℕ → ℝ)
    (Cpow Calpha K : ℝ) (W : ℕ)
    (hepsilon : Tendsto epsilon atTop (nhds 0))
    (hepsilonRate : Tendsto
      (fun n : ℕ ↦ epsilon n * Real.log (Scale.L n))
        atTop (nhds 0))
    (hcombinedRate : Tendsto
      (fun n : ℕ ↦ combined n * Real.log (Scale.L n))
        atTop (nhds 0)) :
    Tendsto
      (canonicalFullSharpRemainder epsilon combined Cpow Calpha K W)
      atTop
      (nhds (3 * Cpow * (K + 1) * (1 / (W : ℝ)))) := by
  have hmiddleCore : Tendsto (fun n : ℕ ↦
      K * Calpha * (epsilon n * Real.log (Scale.L n)) + epsilon n)
      atTop (nhds 0) := by
    have hfirst : Tendsto (fun n : ℕ ↦
        (K * Calpha) *
          (epsilon n * Real.log (Scale.L n))) atTop (nhds 0) := by
      simpa only [mul_zero] using
        (tendsto_const_nhds.mul hepsilonRate : Tendsto
          (fun n : ℕ ↦ (K * Calpha) *
            (epsilon n * Real.log (Scale.L n)))
            atTop (nhds ((K * Calpha) * 0)))
    simpa only [add_zero] using hfirst.add hepsilon
  have hmiddle : Tendsto (fun n : ℕ ↦
      3 * epsilon n *
        (K * (Calpha * Real.log (Scale.L n)) + 1) *
          (1 / (W : ℝ))) atTop (nhds 0) := by
    have hscaled : Tendsto (fun n : ℕ ↦
        (3 * (1 / (W : ℝ))) *
          (K * Calpha *
            (epsilon n * Real.log (Scale.L n)) + epsilon n))
        atTop (nhds 0) := by
      simpa only [mul_zero] using
        (tendsto_const_nhds.mul hmiddleCore : Tendsto
          (fun n : ℕ ↦ (3 * (1 / (W : ℝ))) *
            (K * Calpha *
              (epsilon n * Real.log (Scale.L n)) + epsilon n))
            atTop (nhds ((3 * (1 / (W : ℝ))) * 0)))
    apply hscaled.congr'
    filter_upwards with n
    ring
  have hlast : Tendsto (fun n : ℕ ↦
      combined n * (Calpha * Real.log (Scale.L n)))
      atTop (nhds 0) := by
    have hscaled : Tendsto (fun n : ℕ ↦
        Calpha * (combined n * Real.log (Scale.L n)))
        atTop (nhds 0) := by
      simpa only [mul_zero] using
        (tendsto_const_nhds.mul hcombinedRate : Tendsto
          (fun n : ℕ ↦
            Calpha * (combined n * Real.log (Scale.L n)))
              atTop (nhds (Calpha * 0)))
    apply hscaled.congr'
    filter_upwards with n
    ring
  have hconst : Tendsto (fun _n : ℕ ↦
      3 * Cpow * (K + 1) * (1 / (W : ℝ))) atTop
      (nhds (3 * Cpow * (K + 1) * (1 / (W : ℝ)))) :=
    tendsto_const_nhds
  simpa only [canonicalFullSharpRemainder, add_zero] using
    (hconst.add hmiddle).add hlast

/-- Insert the reciprocal-centre and reciprocal-prime-mass envelopes into
the literal full-versus-squarefree row.  This is deliberately a finite
inequality: all limiting statements remain outside this lemma. -/
theorem fullSharpRow_le_canonicalFullSharpRemainder
    [Nonempty Head]
    (xi : B.ParamSpace)
    (epsilon combined : ℕ → ℝ)
    {Cpow Calpha K : ℝ}
    (hCpow : 0 ≤ Cpow)
    (hepsilon : 0 ≤ epsilon B.sampleData.n)
    (hcombined : 0 ≤ combined B.sampleData.n)
    (hW : B.sampleData.W ≠ 0)
    (hBandT : bandTReciprocalSum B.sampleData.n B.sampleData.W ≤ K)
    (hcenterInv : ∀ i : Band,
      1 / B.partition.center i ≤
        Calpha * Real.log (Scale.L B.sampleData.n))
    (q : Band → ℝ) (i : Band)
    (hrow :
      |PrimePowerSharpBandTransfer.fullSharpRow
            (B.actualValuationLaw xi) B.partition q i -
          SquarefreeSharpBandTransfer.squarefreeSharpRow
            (B.actualValuationLaw xi) B.partition q i| ≤
        3 * Cpow *
              (bandTReciprocalSum B.sampleData.n B.sampleData.W + 1) *
              (1 / (B.sampleData.W : ℝ)) +
          3 * epsilon B.sampleData.n *
              (bandTReciprocalSum B.sampleData.n B.sampleData.W /
                    B.partition.center i + 1) *
              (1 / (B.sampleData.W : ℝ)) +
          combined B.sampleData.n / B.partition.center i) :
      |PrimePowerSharpBandTransfer.fullSharpRow
            (B.actualValuationLaw xi) B.partition q i -
          SquarefreeSharpBandTransfer.squarefreeSharpRow
            (B.actualValuationLaw xi) B.partition q i| ≤
        canonicalFullSharpRemainder epsilon combined Cpow Calpha K
          B.sampleData.W B.sampleData.n := by
  have hBandT0 : 0 ≤
      bandTReciprocalSum B.sampleData.n B.sampleData.W := by
    unfold bandTReciprocalSum
    apply Finset.sum_nonneg
    intro p hp
    exact div_nonneg (B.bandPrime_tPrime_pos ⟨p, hp⟩).le (by positivity)
  have hK0 : 0 ≤ K := hBandT0.trans hBandT
  have hcenterPos : 0 < B.partition.center i :=
    B.partition.center_pos B.n_gt_one i
  have hcenterInv' : (B.partition.center i)⁻¹ ≤
      Calpha * Real.log (Scale.L B.sampleData.n) := by
    simpa only [one_div] using hcenterInv i
  have hCL0 : 0 ≤ Calpha * Real.log (Scale.L B.sampleData.n) :=
    (one_div_pos.mpr hcenterPos).le.trans (hcenterInv i)
  have hWInv0 : 0 ≤ 1 / (B.sampleData.W : ℝ) := by positivity
  have hfirst :
      3 * Cpow *
            (bandTReciprocalSum B.sampleData.n B.sampleData.W + 1) *
            (1 / (B.sampleData.W : ℝ)) ≤
        3 * Cpow * (K + 1) * (1 / (B.sampleData.W : ℝ)) := by
    gcongr
  have hmiddleCore :
      bandTReciprocalSum B.sampleData.n B.sampleData.W /
            B.partition.center i + 1 ≤
        K * (Calpha * Real.log (Scale.L B.sampleData.n)) + 1 := by
    rw [div_eq_mul_inv]
    simpa only [add_comm] using add_le_add_right
      (mul_le_mul hBandT hcenterInv'
        (inv_nonneg.mpr hcenterPos.le) hK0) 1
  have hmiddle :
      3 * epsilon B.sampleData.n *
            (bandTReciprocalSum B.sampleData.n B.sampleData.W /
                  B.partition.center i + 1) *
            (1 / (B.sampleData.W : ℝ)) ≤
        3 * epsilon B.sampleData.n *
            (K * (Calpha * Real.log (Scale.L B.sampleData.n)) + 1) *
            (1 / (B.sampleData.W : ℝ)) := by
    gcongr
  have hlast :
      combined B.sampleData.n / B.partition.center i ≤
        combined B.sampleData.n *
          (Calpha * Real.log (Scale.L B.sampleData.n)) := by
    rw [div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_left hcenterInv' hcombined
  exact hrow.trans (by
    unfold canonicalFullSharpRemainder
    linarith)



/-- Deterministic two-stage inverse attachment.  This theorem keeps the two
Neumann smallness checks separate, so a later eventual theorem cannot hide a
circular choice of the full-valuation box. -/
theorem exists_actualFullProjectedEquiv_of_reference_of_unitSharpRows
    [Nonempty Head]
    (xi : B.ParamSpace)
    (cert : PositiveCellTransfer.IntervalCertificate B.partition)
    (referenceEquiv :
      SharpGaugeSpace B.partition.mass B.partition.center ≃L[ℝ]
        SharpGaugeSpace B.partition.mass B.partition.center)
    (hreference : ∀ q, referenceEquiv q =
      ArithmeticGaugeStableInverse.projectedSharpCLM
        (CompressedArithmeticOperator.arithmeticDiagonal
          (y B.sampleData.n) cert.lower cert.upper)
        (CompressedArithmeticOperator.arithmeticKernel
          (y B.sampleData.n) cert.lower cert.upper)
        B.partition.center
        (MovingLowGaugeTransfer.sharpWeight
          B.partition.mass B.partition.center)
        (ne_of_gt (B.actualSharpWeightTotal_pos)) q)
    {C rSquare rFull : ℝ}
    (hC : 0 ≤ C) (hrSquare : 0 ≤ rSquare) (hrFull : 0 ≤ rFull)
    (hinv : ∀ v, ‖referenceEquiv.symm v‖ ≤ C * ‖v‖)
    (hsmallSquare : C * (2 * rSquare) < 1)
    (hrowSquare : ∀ q : Band → ℝ, (∀ j, |q j| ≤ 1) → ∀ i : Band,
      |SquarefreeSharpBandTransfer.squarefreeSharpRow
          (B.actualValuationLaw xi) B.partition q i -
        CompressedArithmeticOperator.arithmeticSharpOperator
          (y B.sampleData.n) cert.lower cert.upper
            B.partition.center q i| ≤ rSquare)
    (hsmallFull :
      (C / (1 - C * (2 * rSquare))) * (2 * rFull) < 1)
    (hrowFull : ∀ q : Band → ℝ, (∀ j, |q j| ≤ 1) → ∀ i : Band,
      |PrimePowerSharpBandTransfer.fullSharpRow
          (B.actualValuationLaw xi) B.partition q i -
        SquarefreeSharpBandTransfer.squarefreeSharpRow
          (B.actualValuationLaw xi) B.partition q i| ≤ rFull) :
    ∃ actualEquiv :
      SharpGaugeSpace B.partition.mass B.partition.center ≃L[ℝ]
        SharpGaugeSpace B.partition.mass B.partition.center,
      (∀ q, actualEquiv q = B.actualFullProjectedCLM xi q) ∧
      ∀ v, ‖actualEquiv.symm v‖ ≤
        ((C / (1 - C * (2 * rSquare))) /
          (1 - (C / (1 - C * (2 * rSquare))) * (2 * rFull))) * ‖v‖ := by
  obtain ⟨squarefreeEquiv, hsquarefree, hinvSquare⟩ :=
    B.exists_actualSquarefreeProjectedEquiv_of_reference
      xi cert referenceEquiv hreference hC hrSquare hinv
        hsmallSquare hrowSquare
  exact B.exists_actualFullProjectedEquiv_of_squarefree_of_unitSharpRows
    xi squarefreeEquiv hsquarefree
      (by
        have hden : 0 < 1 - C * (2 * rSquare) := sub_pos.mpr hsmallSquare
        exact div_nonneg hC hden.le)
      hrFull hinvSquare hsmallFull hrowFull





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

/- Source module: Erdos390.Full.PaperActualFullEffectiveBall -/
section


/-!
# From pointwise paper boxes to the preselected effective ODE ball

The selected-mesh actual-full theorem is naturally stated pointwise in the
literal prime-coefficient and physical-coordinate box.  The ODE is run on a
closed ball in the equivalent effective max norm.  This file records the
exact factor-three conversion and packages the pointwise inverses into one
ball-indexed family.
-/

open Metric Set

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

open ArithmeticModel ArithmeticBandGeometry PaperWeightedInverseExport

namespace BridgeData

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]

/-- A pointwise actual-full inverse on the literal paper box supplies a
single family on the closed effective ODE ball.  The family is allowed to
depend on the proof of ball membership, exactly as in the later Schur
constructor; no continuity of this auxiliary choice is needed. -/
theorem exists_actualFullProjectedEquiv_on_closedBall_of_box
    (B : BridgeData Head Band) [Nonempty Head]
    (a : NNReal) {Cfull : ℝ}
    (hpoint : ∀ (xi : B.ParamSpace),
      (∀ p : BandPrime B.sampleData.n B.sampleData.W,
        |B.effectivePrimeCoefficient xi p| ≤ 3 * (a : ℝ)) →
      |xi MomentCoord.physical| ≤ 3 * (a : ℝ) →
      ∃ actualEquiv :
          SharpGaugeSpace B.partition.mass B.partition.center ≃L[ℝ]
            SharpGaugeSpace B.partition.mass B.partition.center,
        (∀ q, actualEquiv q = B.actualFullProjectedCLM xi q) ∧
        ∀ v, ‖actualEquiv.symm v‖ ≤ Cfull * ‖v‖) :
    ∃ fullEquiv : ∀ (z : B.EffectiveParamSpace),
        z ∈ closedBall (0 : B.EffectiveParamSpace) (a : ℝ) →
          SharpGaugeSpace B.partition.mass B.partition.center ≃L[ℝ]
            SharpGaugeSpace B.partition.mass B.partition.center,
      (∀ (z : B.EffectiveParamSpace)
          (hz : z ∈ closedBall (0 : B.EffectiveParamSpace) (a : ℝ)) q,
        fullEquiv z hz q =
          B.actualFullProjectedCLM (B.effectiveParamEquiv z) q) ∧
      ∀ (z : B.EffectiveParamSpace)
          (hz : z ∈ closedBall (0 : B.EffectiveParamSpace) (a : ℝ)) v,
        ‖(fullEquiv z hz).symm v‖ ≤ Cfull * ‖v‖ := by
  have hbox : ∀ (z : B.EffectiveParamSpace),
      z ∈ closedBall (0 : B.EffectiveParamSpace) (a : ℝ) →
        B.paperEffectiveSize (B.effectiveParamEquiv z) ≤ 3 * (a : ℝ) := by
    intro z hz
    have hznorm : ‖z‖ ≤ (a : ℝ) := by
      simpa only [mem_closedBall, dist_zero_right] using hz
    exact (B.paperEffectiveSize_effectiveParamEquiv_le z).trans
      (mul_le_mul_of_nonneg_left hznorm (by norm_num))
  have hdata : ∀ (z : B.EffectiveParamSpace)
      (hz : z ∈ closedBall (0 : B.EffectiveParamSpace) (a : ℝ)),
      ∃ actualEquiv :
          SharpGaugeSpace B.partition.mass B.partition.center ≃L[ℝ]
            SharpGaugeSpace B.partition.mass B.partition.center,
        (∀ q, actualEquiv q =
          B.actualFullProjectedCLM (B.effectiveParamEquiv z) q) ∧
        ∀ v, ‖actualEquiv.symm v‖ ≤ Cfull * ‖v‖ := by
    intro z hz
    have hb := B.effective_bounds_of_paperEffectiveSize
      (B.effectiveParamEquiv z) (hbox z hz)
    have hphysNorm :
        ‖B.nuisanceParameter (B.effectiveParamEquiv z)‖ ≤ 3 * (a : ℝ) :=
      hb.2
    have hphys :
        |B.effectiveParamEquiv z MomentCoord.physical| ≤ 3 * (a : ℝ) := by
      calc
        |B.effectiveParamEquiv z MomentCoord.physical| =
            ‖B.nuisanceParameter (B.effectiveParamEquiv z)
                NuisanceCoord.physical‖ := by
              simp only [B.nuisanceParameter_physical, Real.norm_eq_abs]
        _ ≤ ‖B.nuisanceParameter (B.effectiveParamEquiv z)‖ := by
              exact PiLp.norm_apply_le
                (B.nuisanceParameter (B.effectiveParamEquiv z))
                NuisanceCoord.physical
        _ ≤ 3 * (a : ℝ) := hphysNorm
    exact hpoint (B.effectiveParamEquiv z) hb.1 hphys
  let fullEquiv : ∀ (z : B.EffectiveParamSpace),
      z ∈ closedBall (0 : B.EffectiveParamSpace) (a : ℝ) →
        SharpGaugeSpace B.partition.mass B.partition.center ≃L[ℝ]
          SharpGaugeSpace B.partition.mass B.partition.center :=
    fun z hz ↦ (hdata z hz).choose
  refine ⟨fullEquiv, ?_, ?_⟩
  · intro z hz q
    exact (hdata z hz).choose_spec.1 q
  · intro z hz v
    exact (hdata z hz).choose_spec.2 v

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

set_option maxHeartbeats 4000000 in
/-- Exact paper-order terminal for the literal actual nuisance-Schur band
operator.  There are no profile, row-error, inverse, convergence, or
smallness assumptions in the statement.  In particular, `W` is fixed before
`delta`, the mesh, the head family, and the effective ball. -/
theorem exists_cutoff_before_mesh_eventually_actualBandSchur_primeGraph_inverse :
    ∃ meshTol : ℝ, 0 < meshTol ∧
      ∃ Cschur : ℝ, 0 < Cschur ∧
      ∃ W₀ : ℕ,
      ∀ W : ℕ, W₀ ≤ W →
      ∀ {delta eta : ℝ} (M : RegularRelativeMesh.Mesh delta eta)
        (hdelta : 0 < delta),
        delta + M.ratio ≤ meshTol →
        ∀ (anchors : Finset (Fin M.cellCount)), anchors.Nonempty →
          (∀ k ∈ anchors, (1 / 8 : ℝ) < M.lower k) →
          (∀ k ∈ anchors, M.upper k ≤ 1 - (1 / 8 : ℝ)) →
          ((1 / 8 : ℝ) ≤ (∑ k ∈ anchors, M.width k) / 2) →
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
                        (by
                          intro sigma
                          rw [hcanonical]
                          rfl)
                        (by
                          intro sigma
                          rw [hcanonical]
                          rfl)
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
  obtain ⟨meshTol, hmeshTol, Cref, hCref, Wref, hreferenceEvent⟩ :=
    @exists_cutoff_before_mesh_eventually_referenceSharp_primeGraph_inverse
  obtain ⟨CKernel, hCKernel, hKernelBound⟩ :=
    PoissonDickmanKernelBounds.exists_covarianceKernel_abs_le_second
  let Cpow : ℝ :=
    FixedFiniteMixtureFullUniform.boxIndependentPrimePowerConstant
  let r : ℝ := canonicalProjectedPerturbationRadius Cref
  let Cfull : ℝ := 2 * Cref
  let Cschur : ℝ := 2 * Cfull
  have hr : 0 < r := by
    dsimp only [r]
    exact canonicalProjectedPerturbationRadius_pos hCref
  have hCfull : 0 < Cfull := by
    dsimp only [Cfull]
    positivity
  have hCschur : 0 < Cschur := by
    dsimp only [Cschur]
    positivity
  let K : ℝ := 2 * Real.log 4
  have hK : 0 ≤ K := by
    dsimp only [K]
    positivity
  have hInvNat : Tendsto (fun W : ℕ ↦ 1 / (W : ℝ))
      atTop (nhds 0) := by
    have h := (tendsto_inv_atTop_zero.comp
      tendsto_natCast_atTop_atTop :
        Tendsto (fun W : ℕ ↦ ((W : ℝ))⁻¹) atTop (nhds 0))
    simpa only [one_div] using h
  let squareTailConstant : ℝ :=
    (1 / DickmanBasic.rho DickmanBasic.U) ^ 2 + CKernel
  have hSquareTail : Tendsto (fun W : ℕ ↦
      squareTailConstant * (1 / (W : ℝ))) atTop (nhds 0) := by
    simpa only [mul_zero] using
      (tendsto_const_nhds.mul hInvNat : Tendsto
        (fun W : ℕ ↦ squareTailConstant * (1 / (W : ℝ)))
          atTop (nhds (squareTailConstant * 0)))
  let fullTailConstant : ℝ := 3 * Cpow * (K + 1)
  have hFullTail : Tendsto (fun W : ℕ ↦
      fullTailConstant * (1 / (W : ℝ))) atTop (nhds 0) := by
    simpa only [mul_zero] using
      (tendsto_const_nhds.mul hInvNat : Tendsto
        (fun W : ℕ ↦ fullTailConstant * (1 / (W : ℝ)))
          atTop (nhds (fullTailConstant * 0)))
  obtain ⟨Wsquare, hWsquare⟩ := eventually_atTop.1
    (hSquareTail.eventually (eventually_lt_nhds hr))
  obtain ⟨Wfull, hWfull⟩ := eventually_atTop.1
    (hFullTail.eventually (eventually_lt_nhds hr))
  let W₀ : ℕ := max Wref
    (max RegularMeshPrimeCutoffs.canonicalCenterEnvelopeCutoff
      (max Wsquare (max Wfull 2)))
  refine ⟨meshTol, hmeshTol, Cschur, hCschur, W₀, ?_⟩
  intro W hWcutoff delta eta M hdelta hmesh anchors hAnchors
    hIdealLower hIdealUpper hIdealMass Head _instFintype _instDecidable
    _instNonempty Phead hhead I U hU hlowerOne hupperU Cprom Cbank
    ledger a marginFloor hmarginFloor
  have hWref : Wref ≤ W :=
    (le_max_left _ _).trans hWcutoff
  have hWcenter :
      RegularMeshPrimeCutoffs.canonicalCenterEnvelopeCutoff ≤ W :=
    ((le_max_left _ (max Wsquare (max Wfull 2))).trans
      (le_max_right Wref _)).trans hWcutoff
  have hWsquare' : Wsquare ≤ W :=
    ((le_max_left Wsquare (max Wfull 2)).trans
      (le_max_right
        RegularMeshPrimeCutoffs.canonicalCenterEnvelopeCutoff _)).trans
      ((le_max_right Wref _).trans hWcutoff)
  have hWfull' : Wfull ≤ W :=
    ((le_max_left Wfull 2).trans
      (le_max_right Wsquare _)).trans
      ((le_max_right
        RegularMeshPrimeCutoffs.canonicalCenterEnvelopeCutoff _).trans
        ((le_max_right Wref _).trans hWcutoff))
  have hWtwo : 2 ≤ W :=
    ((le_max_right Wfull 2).trans
      (le_max_right Wsquare _)).trans
      ((le_max_right
        RegularMeshPrimeCutoffs.canonicalCenterEnvelopeCutoff _).trans
        ((le_max_right Wref _).trans hWcutoff))
  have hWone : 1 < W := by omega
  have hSquareTailLt :
      squareTailConstant * (1 / (W : ℝ)) < r :=
    hWsquare W hWsquare'
  have hFullTailLt :
      fullTailConstant * (1 / (W : ℝ)) < r :=
    hWfull W hWfull'
  have hHeadLe : ∀ h, ∀ p ∈ (Phead h).primes, p ≤ W := by
    intro h p hp
    exact (hhead h p).mp hp |>.2
  let Acoef : ℝ := 3 * (a : ℝ)
  let Aphys : ℝ := 3 * (a : ℝ)
  have hAcoef : 0 ≤ Acoef := by dsimp only [Acoef]; positivity
  have hAphys : 0 ≤ Aphys := by dsimp only [Aphys]; positivity
  obtain ⟨profileError, hprofile0, hprofileT, hprofileRate,
      Nprofile, hprofile⟩ :=
    exists_boxIndependent_actual_component_signed_profiles
      Phead I U hlowerOne hupperU Cprom Cbank ledger W hWone hHeadLe
        Acoef Aphys hAcoef hAphys
  obtain ⟨_hCpowTerminal, hfullTerminal⟩ :=
    boxIndependent_canonicalRaw_fullSharp
      Phead I U hlowerOne hupperU Cprom Cbank ledger
  obtain ⟨epsilon75, hepsilon750, hepsilon75T, hepsilon75Rate,
      hcombinedRateRaw, Nfull, hfullRaw⟩ :=
    hfullTerminal W hWone hHeadLe Acoef hAcoef Aphys hAphys
  obtain ⟨markedError, hmarked0, hmarkedRate, Nmarked, hmarked⟩ :=
    _root_.Erdos390.Full.PaperCanonicalMarkedNuisanceRows.PaperBridgeFit.BridgeData.exists_uniform_canonical_tiltedLaw_nuisance_valuation_rate_on_effectiveBall
      Phead I U hU hlowerOne hupperU Cprom Cbank ledger W hWone
        hHeadLe a
  let Calpha : ℝ :=
    RegularMeshPrimeCutoffs.canonicalCenterEnvelopeConstant delta
  let centerScale : ℝ := 1 / Calpha
  have hCalpha : 0 < Calpha := by
    dsimp only [Calpha]
    exact RegularMeshPrimeCutoffs.canonicalCenterEnvelopeConstant_pos hdelta
  have hcenterScale : 0 < centerScale := by
    dsimp only [centerScale]
    exact one_div_pos.mpr hCalpha
  let combined : ℕ → ℝ := fun n ↦
    canonicalCombinedPowerCorrection
      Phead I U Cprom Cbank W Acoef Aphys n
  have hcombinedRate : Tendsto
      (fun n : ℕ ↦ combined n * Real.log (Scale.L n))
        atTop (nhds 0) := by
    simpa only [combined, canonicalCombinedPowerCorrection] using
      hcombinedRateRaw
  have hSquareRemainderT := tendsto_squarefreeSharpProfileRemainder
    profileError Calpha K CKernel W hprofileT hprofileRate
  have hSquareSmall : ∀ᶠ n : ℕ in atTop,
      squarefreeSharpProfileRemainder
        profileError Calpha K CKernel W n < r :=
    hSquareRemainderT.eventually (eventually_lt_nhds (by
      simpa only [squareTailConstant] using hSquareTailLt))
  have hFullRemainderT := tendsto_canonicalFullSharpRemainder
    epsilon75 combined Cpow Calpha K W
      hepsilon75T hepsilon75Rate hcombinedRate
  have hFullSmall : ∀ᶠ n : ℕ in atTop,
      canonicalFullSharpRemainder
        epsilon75 combined Cpow Calpha K W n < r :=
    hFullRemainderT.eventually (eventually_lt_nhds (by
      simpa only [fullTailConstant] using hFullTailLt))
  have hReference := hreferenceEvent W hWref Head M hdelta hmesh anchors hAnchors
      hIdealLower hIdealUpper hIdealMass
  have hCenterInverse :=
    RegularMeshPrimeCutoffs.Mesh.canonicalCenterEnvelopeCutoff_eventually_inverse
      M hdelta W hWcenter
  have hCenterLower :=
    RegularMeshPrimeCutoffs.Mesh.canonicalCenterEnvelopeCutoff_eventually_lower
      M hdelta W hWcenter
  have hBandT := eventually_bandTReciprocalSum_le W
  have hSchurConnector :=
    eventually_exists_uniform_actualBandSchurEquiv_and_quadratic
      (Head := Head) (Band := Fin (M.cellCount + 1))
      I hU hlowerOne hupperU W hWone a marginFloor centerScale Cfull
        hmarginFloor hcenterScale hCfull markedError hmarked0 hmarkedRate
  filter_upwards [hReference, hCenterInverse, hCenterLower, hBandT,
      hSquareSmall, hFullSmall, hSchurConnector,
      eventually_ge_atTop Nprofile, eventually_ge_atTop Nfull,
      eventually_ge_atTop Nmarked] with
      n hReferenceN hCenterInverseN hCenterLowerN hBandTN
      hSquareN hFullN hSchurN hnProfile hnFull hnMarked
  intro B hBn hBW hBWlarge hsep hremaining hcanonical hpartition T hTmargin
    hbaseline
  subst n
  subst W
  obtain ⟨cert, referenceEquiv, hreference, hinvReference⟩ :=
    hReferenceN B rfl rfl hpartition
  obtain ⟨hWne, S, hpartitionCanonical⟩ := hpartition
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
  have hCenterInvActual : ∀ i : Fin (M.cellCount + 1),
      1 / B.partition.center i ≤
        Calpha * Real.log (Scale.L B.sampleData.n) := by
    intro i
    rw [hpartitionCanonical]
    simpa only [Calpha] using
      hCenterInverseN B.n_gt_one hWne S i
  have hCenterLowerActual : ∀ i : Fin (M.cellCount + 1),
      centerScale / Real.log (Scale.L B.sampleData.n) ≤
        B.partition.center i := by
    intro i
    rw [hpartitionCanonical]
    simpa only [centerScale, Calpha] using
      hCenterLowerN B.n_gt_one hWne S i
  have hKernel : ∀ p ∈
      primeBand B.sampleData.n B.sampleData.W,
      |ConditionedPoissonLimit.covarianceKernel
          (tPrime B.sampleData.n p) (tPrime B.sampleData.n p)| ≤
        CKernel := by
    intro p hp
    have ht0 := PaperPrimePowerRow.tPrime_nonneg_of_mem_primeBand
      B.n_gt_one hp
    have ht1 := PaperPrimePowerRow.tPrime_le_one_of_mem_primeBand
      B.n_gt_one hp
    calc
      |ConditionedPoissonLimit.covarianceKernel
          (tPrime B.sampleData.n p) (tPrime B.sampleData.n p)| ≤
          CKernel * tPrime B.sampleData.n p :=
        hKernelBound _ ⟨ht0, ht1⟩ _ ⟨ht0, ht1⟩
      _ ≤ CKernel := by
        exact (mul_le_mul_of_nonneg_left ht1 hCKernel).trans_eq
          (mul_one CKernel)
  have hUstrict : 1 < U :=
    (hlowerOne .minus).trans_lt
      ((I.lower_lt_upper .minus).trans_le (hupperU .minus))
  have hpoint : ∀ (xi : B.ParamSpace),
      (∀ p : BandPrime B.sampleData.n B.sampleData.W,
        |B.effectivePrimeCoefficient xi p| ≤ Acoef) →
      |xi MomentCoord.physical| ≤ Aphys →
      ∃ actualEquiv :
          SharpGaugeSpace B.partition.mass B.partition.center ≃L[ℝ]
            SharpGaugeSpace B.partition.mass B.partition.center,
        (∀ q, actualEquiv q = B.actualFullProjectedCLM xi q) ∧
        ∀ v, ‖actualEquiv.symm v‖ ≤ Cfull * ‖v‖ := by
    intro xi heta hphys
    obtain ⟨hpair, hsingle⟩ := hprofile B xi hnProfile
      hPattern hLo hHi hGuards heta hphys rfl
    have hSquareRow : ∀ q : Fin (M.cellCount + 1) → ℝ,
        (∀ j, |q j| ≤ 1) → ∀ i : Fin (M.cellCount + 1),
        |SquarefreeSharpBandTransfer.squarefreeSharpRow
            (B.actualValuationLaw xi) B.partition q i -
          CompressedArithmeticOperator.arithmeticSharpOperator
            (y B.sampleData.n) cert.lower cert.upper
              B.partition.center q i| ≤ r := by
      intro q hq i
      exact (B.abs_actual_squarefreeSharpRow_sub_arithmetic_le_profileRemainder
        xi cert (hprofile0 B.sampleData.n) (by omega) hpair hsingle
        hKernel hBandTN hCenterInvActual q hq i).trans hSquareN.le
    have hcombined0 : 0 ≤ combined B.sampleData.n := by
      dsimp only [combined]
      exact canonicalCombinedPowerCorrection_nonneg
        Phead I hUstrict.le hAphys (by omega) B.n_gt_one
    have hrawFull := hfullRaw B xi hnFull rfl hsep hremaining
      hcanonical heta hphys
    have hFullRow : ∀ q : Fin (M.cellCount + 1) → ℝ,
        (∀ j, |q j| ≤ 1) → ∀ i : Fin (M.cellCount + 1),
        |PrimePowerSharpBandTransfer.fullSharpRow
            (B.actualValuationLaw xi) B.partition q i -
          SquarefreeSharpBandTransfer.squarefreeSharpRow
            (B.actualValuationLaw xi) B.partition q i| ≤ r := by
      intro q hq i
      have hraw := hrawFull q hq i
      have hbounded := B.fullSharpRow_le_canonicalFullSharpRemainder
        xi epsilon75 combined
          FixedFiniteMixtureFullUniform.boxIndependentPrimePowerConstant_pos.le
          (hepsilon750 B.sampleData.n) hcombined0 (by omega)
          hBandTN hCenterInvActual q i
          (by
            simpa only [Cpow, combined,
              canonicalCombinedPowerCorrection] using hraw)
      exact hbounded.trans hFullN.le
    obtain ⟨actualEquiv, hactual, hinvActual⟩ :=
      B.exists_actualFullProjectedEquiv_of_reference_of_unitSharpRows
        xi cert referenceEquiv hreference hCref.le hr.le hr.le
          hinvReference
          (canonicalProjectedPerturbationRadius_first_small hCref)
          hSquareRow
          (canonicalProjectedPerturbationRadius_second_small hCref)
          hFullRow
    refine ⟨actualEquiv, hactual, ?_⟩
    intro v
    have hbound := hinvActual v
    rw [canonicalProjectedPerturbation_finalConstant hCref] at hbound
    simpa only [Cfull] using hbound
  obtain ⟨fullEquiv, hfull, hinvFull⟩ :=
    B.exists_actualFullProjectedEquiv_on_closedBall_of_box a
      (by simpa only [Acoef, Aphys] using hpoint)
  have hmarkedRows : ∀ (z : B.EffectiveParamSpace)
      (hz : z ∈ closedBall (0 : B.EffectiveParamSpace) (a : ℝ))
      (c : NuisanceCoord B.HeadIndex)
      (p : BandPrime B.sampleData.n B.sampleData.W),
      |(B.tiltedLaw (B.effectiveParamEquiv z)).covariance
        (fun m ↦ B.nuisanceStatistic m c)
        (fun m ↦ valuation p.1 (B.sampleData.value m))| ≤
          markedError B.sampleData.n * (1 / (p.1 : ℝ)) := by
    intro z hz c p
    exact hmarked B z hz hnMarked rfl hsep hremaining hcanonical c p
  have hterminal := hSchurN B rfl rfl T hTmargin hbaseline hLo hHi
    fullEquiv hfull hinvFull hCenterLowerActual hmarkedRows
  dsimp only at hterminal
  obtain ⟨e, he, hinvSchur, hlocalConstant, _hquadratic⟩ := hterminal
  refine ⟨e, ?_, ?_⟩
  · simpa only using he
  · intro z hz v
    exact (hinvSchur z hz v).trans
      (mul_le_mul_of_nonneg_right
        (by simpa only [Cschur, Cfull] using hlocalConstant)
        (norm_nonneg _))



end BridgeData

end

end Erdos390.Full.PaperBridgeFit

end

universe u_1
theorem solution : Erdos390.RemainingAnalyticGoal001_012.{u_1} := by
  exact @Erdos390.Full.PaperBridgeFit.BridgeData.exists_cutoff_before_mesh_eventually_actualBandSchur_primeGraph_inverse
