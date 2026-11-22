-- Prove2me | solution 1 for Erdos390.Full.PaperBridgeFit.BridgeData.exists_physicallyCenteredFixedPartitionFit_of_canonicalTwoStageOutputs
-- status  : ACCEPTED   (prove)
-- author  : @doctosil
-- created : 2026-09-17T16:13:14.417038+00:00
-- url     : https://prove2.me/submissions/f2cad782-a7e3-4e52-9777-93b5f050aebf

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
import Theorems.Thm_Erdos390_Full_PaperBridgeFit_BridgeData_actualBandSchur_fastGauge_eq_projectedTarget
import Theorems.Thm_Erdos390_Full_PaperBridgeFit_BridgeData_main_norm_sq_le_fastSharp_add_storedSlow
import Theorems.Thm_Erdos390_Full_PaperBridgeFit_BridgeData_slow_div_mul_actualTwoStageCompensatedVariance

/- Source module: Erdos390.Full.FiniteExponentialFamily -/
section


/-!
# Finite exponential families

This file develops the exact finite exponential family used by the smooth-row
bridge.  The sample space is finite, the base weights are nonnegative with
positive total mass, and every score is a continuous linear functional on a
finite-dimensional real parameter space.  All normalization, positivity,
smoothness, and covariance-Jacobian statements are proved from these data.
-/

open scoped BigOperators

namespace Erdos390.Full

noncomputable section



namespace FiniteProbability

variable {Ω : Type*} [Fintype Ω]





end FiniteProbability



namespace FiniteExponentialFamily

variable {Ω Param : Type*} [Fintype Ω]
  [NormedAddCommGroup Param] [NormedSpace ℝ Param]
  [FiniteDimensional ℝ Param]





























theorem activeWeight_nonneg (fam : FiniteExponentialFamily Ω Param)
    (ξ : Param) (ω : Ω) : 0 ≤ fam.activeWeight ξ ω :=
  mul_nonneg (le_of_lt fam.baseMass_pos) (fam.probabilityMass_nonneg ξ ω)

theorem activeWeight_sum (fam : FiniteExponentialFamily Ω Param) (ξ : Param) :
    ∑ ω, fam.activeWeight ξ ω = fam.baseMass := by
  simp only [FiniteExponentialFamily.activeWeight]
  rw [← Finset.mul_sum, fam.probabilityMass_sum ξ, mul_one]





































theorem partition_contDiff (fam : FiniteExponentialFamily Ω Param) :
    ContDiff ℝ ⊤ fam.partition := by
  apply ContDiff.sum
  intro ω _
  exact (contDiff_const.mul (((fam.score ω).contDiff.div_const fam.scale).exp))

theorem probabilityMass_contDiff (fam : FiniteExponentialFamily Ω Param) (ω : Ω) :
    ContDiff ℝ ⊤ (fun ξ => fam.probabilityMass ξ ω) := by
  apply ContDiff.div
  · exact contDiff_const.mul (((fam.score ω).contDiff.div_const fam.scale).exp)
  · exact fam.partition_contDiff
  · exact fam.partition_ne_zero



















end FiniteExponentialFamily

end

end Erdos390.Full

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











theorem covariance_self_nonneg (mu : FiniteProbability Omega) (F : Omega → ℝ) :
    0 ≤ mu.covariance F F := by
  unfold covariance expect
  rw [show (∑ omega, mu.mass omega * (F omega * F omega)) =
      ∑ omega, mu.mass omega * F omega ^ 2 by
    apply Finset.sum_congr rfl
    intro omega _
    ring]
  rw [show (∑ omega, mu.mass omega * F omega) *
      (∑ omega, mu.mass omega * F omega) =
        (∑ omega, mu.mass omega * F omega) ^ 2 by ring]
  rw [PatternMixture.weightedVariance_pairDifference mu.mass F mu.mass_sum]
  apply mul_nonneg (by norm_num)
  exact Finset.sum_nonneg fun i _ ↦ Finset.sum_nonneg fun j _ ↦
    mul_nonneg
      (mul_nonneg (mu.mass_nonneg i) (mu.mass_nonneg j)) (sq_nonneg _)

theorem covariance_zero_left (mu : FiniteProbability Omega) (G : Omega → ℝ) :
    mu.covariance (fun _ ↦ 0) G = 0 := by
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

/- Source module: Erdos390.Proposition87 -/
section


/-!
# The finite and ODE algebra behind Proposition 8.7

The analytic inputs to the nonlinear fit (uniform covariance gaps, relative row
errors, and existence of an integral curve inside the preselected box) are kept as
explicit hypotheses.  This file proves the block solve, the slow-coordinate and
effective-velocity ledgers, compatibility recovery, and the straight-target chain
rule with no hidden limiting assertion.
-/

open Metric Set

namespace Erdos390

section BlockInverse

variable {Q : Type*} [AddCommGroup Q] [Module ℝ Q]









end BlockInverse

section SlowCoordinateBounds







end SlowCoordinateBounds

section GaugeAnnihilator

variable {E : Type*} [AddCommGroup E] [Module ℝ E]





end GaugeAnnihilator

section PrechosenBox

variable {E : Type*} [PseudoMetricSpace E]



end PrechosenBox

section StraightTarget

variable {E Y : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]



/-- Picard--Lindelöf produces the explicitly named straight-target path and,
crucially, the constructed path remains in the same closed ball on which the
vector-field hypotheses were checked. -/
theorem hasStraightTargetPath_of_picard [CompleteSpace E]
    (v : E → E) (x₀ : E) (a L K : NNReal)
    (hpl : IsPicardLindelof (fun _ : ℝ => v)
      (⟨0, left_mem_Icc.mpr zero_le_one⟩ : Icc (0 : ℝ) 1) x₀ a 0 L K) :
    HasStraightTargetPath (closedBall x₀ a) v x₀ := by
  obtain ⟨α, hα⟩ := ODE.FunSpace.exists_isFixedPt_next hpl
    (mem_closedBall_self le_rfl)
  refine ⟨α.compProj, ?_, ?_, ?_⟩
  · rw [ODE.FunSpace.compProj_of_mem (left_mem_Icc.mpr zero_le_one), ← hα,
      ODE.FunSpace.next_apply₀]
  · intro t _
    exact α.compProj_mem_closedBall hpl.mul_max_le
  · intro t ht
    apply ODE.hasDerivWithinAt_picard_Icc
      (⟨0, left_mem_Icc.mpr zero_le_one⟩ : Icc (0 : ℝ) 1).2 hpl.continuousOn_uncurry
      α.continuous_compProj.continuousOn
      (fun _ _ => α.compProj_mem_closedBall hpl.mul_max_le) x₀ ht |>.congr_of_mem _ ht
    intro t' ht'
    nth_rw 1 [← hα]
    rw [ODE.FunSpace.compProj_of_mem ht', ODE.FunSpace.next_apply]

/-- A directly usable time-independent Picard package.  The radius `a` is fixed
before the ODE is solved, and `L ≤ a` is exactly the unit-time continuation
budget. -/
theorem hasStraightTargetPath_of_lipschitz [CompleteSpace E]
    (v : E → E) (x₀ : E) (a L K : NNReal)
    (hbound : ∀ x ∈ closedBall x₀ a, ‖v x‖ ≤ (L : ℝ))
    (hlipschitz : LipschitzOnWith K v (closedBall x₀ a))
    (hmargin : L ≤ a) :
    HasStraightTargetPath (closedBall x₀ a) v x₀ := by
  let tzero : Icc (0 : ℝ) 1 := ⟨0, left_mem_Icc.mpr zero_le_one⟩
  have hpl : IsPicardLindelof (fun _ : ℝ => v) tzero x₀ a 0 L K := by
    apply IsPicardLindelof.of_time_independent hbound hlipschitz
    simpa [tzero] using hmargin
  simpa [tzero] using hasStraightTargetPath_of_picard v x₀ a L K hpl

/-- Along a path solving `ξ' = v(ξ)`, the identity `DM(ξ)v(ξ)=τ` forces
the moment map to move on the exact straight target `M(x₀)+tτ`. -/
theorem straight_target_chain_rule
    (Ω : Set E) (v : E → E) (M : E → Y)
    (J : E → E →L[ℝ] Y) (x₀ : E) (τ : Y)
    (hpath : HasStraightTargetPath Ω v x₀)
    (hM : ∀ x ∈ Ω, HasFDerivAt M (J x) x)
    (hsolve : ∀ x ∈ Ω, J x (v x) = τ) :
    ∃ ξ : ℝ → E, ξ 0 = x₀ ∧
      (∀ t ∈ Icc (0 : ℝ) 1, ξ t ∈ Ω) ∧
      (∀ t ∈ Icc (0 : ℝ) 1,
        HasDerivWithinAt ξ (v (ξ t)) (Icc (0 : ℝ) 1) t) ∧
      M (ξ 1) = M x₀ + τ := by
  obtain ⟨ξ, hξzero, hξmem, hξderiv⟩ := hpath
  let F : ℝ → Y := fun t => M (ξ t)
  let G : ℝ → Y := fun t => M (ξ 0) + t • τ
  have hFderiv : ∀ t ∈ Icc (0 : ℝ) 1,
      HasDerivWithinAt F τ (Icc (0 : ℝ) 1) t := by
    intro t ht
    have hcomp := (hM (ξ t) (hξmem t ht)).comp_hasDerivWithinAt t (hξderiv t ht)
    simpa only [F, Function.comp_apply, hsolve (ξ t) (hξmem t ht)] using hcomp
  have hGderiv : ∀ t ∈ Icc (0 : ℝ) 1,
      HasDerivWithinAt G τ (Icc (0 : ℝ) 1) t := by
    intro t _
    have hlinear : HasDerivAt (fun s : ℝ => s • τ) τ t :=
      by simpa using (hasDerivAt_id t).smul_const τ
    exact hlinear.const_add (M (ξ 0)) |>.hasDerivWithinAt
  have hunique : UniqueDiffOn ℝ (Icc (0 : ℝ) 1) := uniqueDiffOn_Icc zero_lt_one
  have hFG : (Icc (0 : ℝ) 1).EqOn F G := by
    apply (convex_Icc (0 : ℝ) 1).eqOn_of_fderivWithin_eq
        (fun t ht => (hFderiv t ht).differentiableWithinAt)
        (fun t ht => (hGderiv t ht).differentiableWithinAt) hunique
    · intro t ht
      rw [(hFderiv t ht).hasFDerivWithinAt.fderivWithin (hunique t ht),
        (hGderiv t ht).hasFDerivWithinAt.fderivWithin (hunique t ht)]
    · exact left_mem_Icc.mpr zero_le_one
    · simp [F, G]
  refine ⟨ξ, hξzero, hξmem, hξderiv, ?_⟩
  have hone : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := right_mem_Icc.mpr zero_le_one
  have := hFG hone
  dsimp [F, G] at this
  simpa [hξzero] using this

/-- Packaged nonlinear-fit conclusion: the prechosen closed-ball hypotheses give
an actual Picard path, and the chain rule makes the target displacement exact. -/
theorem straight_target_fit_of_lipschitz [CompleteSpace E]
    (v : E → E) (M : E → Y) (J : E → E →L[ℝ] Y)
    (x₀ : E) (τ : Y) (a L K : NNReal)
    (hbound : ∀ x ∈ closedBall x₀ a, ‖v x‖ ≤ (L : ℝ))
    (hlipschitz : LipschitzOnWith K v (closedBall x₀ a))
    (hmargin : L ≤ a)
    (hM : ∀ x ∈ closedBall x₀ a, HasFDerivAt M (J x) x)
    (hsolve : ∀ x ∈ closedBall x₀ a, J x (v x) = τ) :
    ∃ ξ : ℝ → E, ξ 0 = x₀ ∧
      (∀ t ∈ Icc (0 : ℝ) 1, ξ t ∈ closedBall x₀ a) ∧
      (∀ t ∈ Icc (0 : ℝ) 1,
        HasDerivWithinAt ξ (v (ξ t)) (Icc (0 : ℝ) 1) t) ∧
      M (ξ 1) = M x₀ + τ := by
  exact straight_target_chain_rule (closedBall x₀ a) v M J x₀ τ
    (hasStraightTargetPath_of_lipschitz v x₀ a L K hbound hlipschitz hmargin)
    hM hsolve

end StraightTarget

end Erdos390

end

/- Source module: Erdos390.Full.NonlinearFitODE -/
section


/-!
# The finite nonlinear moment lift

This file turns the scalar covariance--Jacobian identity for a finite
exponential family into the vector Jacobian used by the nonlinear fitting
argument.  A quantitative covariance gap is then used to construct the
inverse Jacobian (rather than assuming a right inverse), define the actual
ODE vector field, and prove its exact solve and velocity estimates.

The final section records a non-circular continuation theorem.  Its input is
an explicit covariance gap on a ball chosen before solving the ODE; local
Lipschitz continuity is derived from the finite exponential formulas and
operator inversion.
-/

open scoped BigOperators
open Metric Set

namespace Erdos390.Full

noncomputable section



namespace VectorExponentialFamily

variable {Omega E : Type*} [Fintype Omega]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]





































theorem jacobian_isInvertible [CompleteSpace E]
    (vf : VectorExponentialFamily Omega E)
    {gamma : ℝ} (hgamma : 0 < gamma) {xi : E}
    (hgap : vf.HasCovarianceGap gamma xi) :
    (vf.jacobian xi).IsInvertible := by
  exact ⟨vf.jacobianEquiv hgamma hgap, rfl⟩



theorem jacobian_vectorField [CompleteSpace E]
    (vf : VectorExponentialFamily Omega E) (target : E)
    {gamma : ℝ} (hgamma : 0 < gamma) {xi : E}
    (hgap : vf.HasCovarianceGap gamma xi) :
    vf.jacobian xi (vf.vectorField target xi) = target := by
  exact (vf.jacobian_isInvertible hgamma hgap).self_apply_inverse target



/-! ## Smoothness and non-circular continuation -/

theorem expectation_contDiff (vf : VectorExponentialFamily Omega E)
    (F : Omega → ℝ) :
    ContDiff ℝ ⊤ (vf.scalarFamily.expectation F) := by
  change ContDiff ℝ ⊤ (fun xi =>
    ∑ omega, vf.scalarFamily.probabilityMass xi omega * F omega)
  apply ContDiff.sum
  intro omega _
  exact (vf.scalarFamily.probabilityMass_contDiff omega).mul contDiff_const

theorem covarianceScore_contDiff (vf : VectorExponentialFamily Omega E)
    (F : Omega → ℝ) :
    ContDiff ℝ ⊤ (fun xi => vf.scalarFamily.covarianceScore F xi) := by
  simp only [FiniteExponentialFamily.covarianceScore]
  apply ContDiff.sum
  intro omega _
  have hscalar : ContDiff ℝ ⊤ (fun xi =>
      vf.scalarFamily.probabilityMass xi omega *
        (F omega - vf.scalarFamily.expectation F xi)) :=
    (vf.scalarFamily.probabilityMass_contDiff omega).mul
      (contDiff_const.sub (vf.expectation_contDiff F))
  have hscore : ContDiff ℝ ⊤
      (fun _ : E => vf.scalarFamily.score omega) := contDiff_const
  simpa only [Pi.smul_apply] using hscalar.smul hscore

theorem activeWeightFDeriv_contDiff
    (vf : VectorExponentialFamily Omega E) (omega : Omega) :
    ContDiff ℝ ⊤ (fun xi => vf.activeWeightFDeriv xi omega) := by
  simpa only [activeWeightFDeriv] using
    (ContDiff.const_smul (vf.baseMass / vf.scale)
      (vf.covarianceScore_contDiff (delta omega)))

/-- The finite covariance Jacobian varies smoothly on the whole parameter
space. -/
theorem jacobian_contDiff (vf : VectorExponentialFamily Omega E) :
    ContDiff ℝ ⊤ vf.jacobian := by
  change ContDiff ℝ ⊤ (fun xi =>
    ∑ omega, (vf.activeWeightFDeriv xi omega).smulRight
      (vf.statistic omega))
  apply ContDiff.sum
  intro omega _
  exact (vf.activeWeightFDeriv_contDiff omega).smulRight contDiff_const

/-- At every point where the explicit covariance gap holds, the actual
inverse-Jacobian vector field is `C^1`.  This is derived from smooth operator
inversion, not supplied as an ODE regularity hypothesis. -/
theorem vectorField_contDiffAt [CompleteSpace E]
    (vf : VectorExponentialFamily Omega E) (target : E)
    {gamma : ℝ} (hgamma : 0 < gamma) {xi : E}
    (hgap : vf.HasCovarianceGap gamma xi) :
    ContDiffAt ℝ 1 (vf.vectorField target) xi := by
  have hinv : ContDiffAt ℝ 1
      (fun eta => (vf.jacobian eta).inverse) xi :=
    (vf.jacobian_isInvertible hgamma hgap).contDiffAt_map_inverse.comp xi
      (vf.jacobian_contDiff.contDiffAt.of_le (by simp))
  have happ := hinv.clm_apply (contDiffAt_const (x := xi) (c := target))
  simpa only [vectorField] using happ









end VectorExponentialFamily

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



































































/-- The raw slow score is exactly the centered combination of the band
valuations and the physical logarithmic prime score.  This finite identity
is the algebra behind the compensated coordinate in Lemmas 8.5--8.6. -/
theorem slowScore_decomposition (m : B.sampleData.Sample) :
    B.slowScore m =
      (∑ j : Band, B.bandCenter j * B.bandScore j m) -
        ∑ p : ArithmeticBandGeometry.BandPrime
            B.sampleData.n B.sampleData.W,
          ArithmeticModel.tPrime B.sampleData.n p.1 *
            ArithmeticModel.valuation p.1 (B.sampleData.value m) := by
  unfold slowScore primeDeviation
  simp_rw [sub_mul]
  rw [Finset.sum_sub_distrib]
  congr 1
  unfold bandScore
  rw [← Finset.sum_fiberwise Finset.univ B.partition.band
    (fun p => B.bandCenter (B.partition.band p) *
      ArithmeticModel.valuation p.1 (B.sampleData.value m))]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  have hpj : B.partition.band p = j := (Finset.mem_filter.mp hp).2
  rw [hpj]

theorem slowScore_eq_bandScore_sub_primeLogScore
    (m : B.sampleData.Sample) :
    B.slowScore m =
      (∑ j : Band, B.bandCenter j * B.bandScore j m) -
        B.primeLogScore m := by
  exact B.slowScore_decomposition m





theorem coordScale_pos (c : B.Coord) : 0 < B.coordScale c := by
  cases c <;> simp [coordScale, B.w_pos]





/-! ### Exact main/nuisance coordinate splitting -/











































theorem combine_norm_sq (u : B.MainSpace) (z : B.NuisanceSpace) :
    ‖B.combine u z‖ ^ 2 = ‖u‖ ^ 2 + ‖z‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq,
    EuclideanSpace.norm_sq_eq]
  simp only [Real.norm_eq_abs]
  change (∑ c : B.Coord, |B.combine u z c| ^ 2) =
    (∑ c : MainCoord B.GaugeIndex, |u c| ^ 2) +
      ∑ c : NuisanceCoord B.HeadIndex, |z c| ^ 2
  rw [B.sum_coord_split]
  apply congrArg₂ (· + ·)
  · apply Finset.sum_congr rfl
    intro c hc
    cases c <;> simp
  · apply Finset.sum_congr rfl
    intro c hc
    cases c <;> simp

theorem norm_mainEmbed (u : B.MainSpace) :
    ‖B.mainEmbed u‖ = ‖u‖ := by
  have hcombine : B.combine u 0 = B.mainEmbed u := by
    apply (EuclideanSpace.equiv B.Coord ℝ).injective
    funext c
    cases c <;> simp [combine]
  have h := B.combine_norm_sq u 0
  rw [hcombine] at h
  norm_num at h
  nlinarith [norm_nonneg (B.mainEmbed u), norm_nonneg u]

theorem norm_nuisanceEmbed (z : B.NuisanceSpace) :
    ‖B.nuisanceEmbed z‖ = ‖z‖ := by
  have hcombine : B.combine 0 z = B.nuisanceEmbed z := by
    apply (EuclideanSpace.equiv B.Coord ℝ).injective
    funext c
    cases c <;> simp [combine]
  have h := B.combine_norm_sq 0 z
  rw [hcombine] at h
  norm_num at h
  nlinarith [norm_nonneg (B.nuisanceEmbed z), norm_nonneg z]

theorem mainEmbeddingCLM_norm_le_one :
    ‖B.mainEmbeddingCLM‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro u
  change ‖B.mainEmbed u‖ ≤ 1 * ‖u‖
  rw [B.norm_mainEmbed, one_mul]

theorem nuisanceEmbeddingCLM_norm_le_one :
    ‖B.nuisanceEmbeddingCLM‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro z
  change ‖B.nuisanceEmbed z‖ ≤ 1 * ‖z‖
  rw [B.norm_nuisanceEmbed, one_mul]

theorem inner_mainEmbed_combine (u v : B.MainSpace)
    (z : B.NuisanceSpace) :
    inner ℝ (B.mainEmbed u) (B.combine v z) = inner ℝ u v := by
  rw [PiLp.inner_apply, PiLp.inner_apply]
  change (∑ c : B.Coord, B.combine v z c * B.mainEmbed u c) =
    ∑ c : MainCoord B.GaugeIndex, v c * u c
  rw [B.sum_coord_split]
  have hmain : (∑ c : MainCoord B.GaugeIndex,
      B.combine v z (match c with
        | .gauge j => .gauge j
        | .slow => .slow) *
      B.mainEmbed u (match c with
        | .gauge j => .gauge j
        | .slow => .slow)) = ∑ c, v c * u c := by
    apply Finset.sum_congr rfl
    intro c hc
    cases c <;> simp
  have hnuisance : (∑ c : NuisanceCoord B.HeadIndex,
      B.combine v z (match c with
        | .physical => .physical
        | .head h => .head h) *
      B.mainEmbed u (match c with
        | .physical => .physical
        | .head h => .head h)) = 0 := by
    apply Finset.sum_eq_zero
    intro c hc
    cases c <;> simp
  erw [hmain, hnuisance, add_zero]















/-- Bilinear covariance--Jacobian identity for the concrete vector family. -/
theorem inner_jacobian [Nonempty Head]
    (xi x y : B.ParamSpace) :
    inner ℝ x (B.vectorFamily.jacobian xi y) =
      (B.q / B.L) * B.vectorFamily.scalarFamily.covariance
        (fun m => inner ℝ x (B.statistic m))
        (fun m => inner ℝ y (B.statistic m)) xi := by
  let F : B.sampleData.Sample → ℝ :=
    fun m => inner ℝ x (B.statistic m)
  have hleft : HasFDerivAt
      (fun eta => inner ℝ x (B.vectorFamily.vectorMoment eta))
      (((innerSL ℝ) x).comp (B.vectorFamily.jacobian xi)) xi := by
    exact ((innerSL ℝ) x).hasFDerivAt.comp xi
      (B.vectorFamily.hasFDerivAt_vectorMoment xi)
  have hright : HasFDerivAt
      (B.vectorFamily.scalarFamily.moment F)
      ((B.vectorFamily.baseMass / B.vectorFamily.scale) •
        B.vectorFamily.scalarFamily.covarianceScore F xi) xi :=
    B.vectorFamily.scalarFamily.hasFDerivAt_moment_covariance F xi
  have hfun : (fun eta => inner ℝ x
      (B.vectorFamily.vectorMoment eta)) =
      B.vectorFamily.scalarFamily.moment F := by
    funext eta
    exact B.vectorFamily.inner_vectorMoment x eta
  have hmaps : ((innerSL ℝ) x).comp (B.vectorFamily.jacobian xi) =
      (B.vectorFamily.baseMass / B.vectorFamily.scale) •
        B.vectorFamily.scalarFamily.covarianceScore F xi :=
    hleft.unique (hfun ▸ hright)
  have happ := congrArg
    (fun T : B.ParamSpace →L[ℝ] ℝ => T y) hmaps
  change inner ℝ x (B.vectorFamily.jacobian xi y) =
    (B.vectorFamily.baseMass / B.vectorFamily.scale) *
      B.vectorFamily.scalarFamily.covarianceScore F xi y at happ
  rw [B.vectorFamily.scalarFamily.covarianceScore_apply F xi y] at happ
  have hscore :
      (fun m => B.vectorFamily.scalarFamily.score m y) =
        fun m => inner ℝ y (B.statistic m) := by
    funext m
    simp only [VectorExponentialFamily.scalarFamily, innerSL_apply_apply]
    exact real_inner_comm _ _
  rw [hscore, B.vectorFamily_baseMass] at happ
  simpa only [vectorFamily] using happ

theorem inner_covarianceOperator [Nonempty Head]
    (xi x y : B.ParamSpace) :
    inner ℝ x (B.covarianceOperator xi y) =
      B.vectorFamily.scalarFamily.covariance
        (fun m => inner ℝ x (B.statistic m))
        (fun m => inner ℝ y (B.statistic m)) xi := by
  rw [covarianceOperator, ContinuousLinearMap.smul_apply, inner_smul_right,
    B.inner_jacobian]
  field_simp [ne_of_gt B.L_pos, ne_of_gt B.q_pos]

theorem covarianceOperator_symmetric [Nonempty Head]
    (xi x y : B.ParamSpace) :
    inner ℝ x (B.covarianceOperator xi y) =
      inner ℝ y (B.covarianceOperator xi x) := by
  rw [B.inner_covarianceOperator, B.inner_covarianceOperator]
  unfold FiniteExponentialFamily.covariance FiniteProbability.covariance
  congr 1
  · apply Finset.sum_congr rfl
    intro m hm
    ring
  · ring



















theorem nuisanceCovarianceEquiv_apply [Nonempty Head]
    (xi : B.ParamSpace) {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (z : B.NuisanceSpace) :
    B.nuisanceCovarianceEquiv xi hgamma hgap z =
      B.nuisanceCovarianceOperator xi z := by
  simp [nuisanceCovarianceEquiv]













theorem exactNuisanceRegression_solve [Nonempty Head]
    (xi : B.ParamSpace) {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (u : B.MainSpace) :
    B.nuisanceCovarianceOperator xi
        (B.exactNuisanceRegression xi hgamma hgap u) =
      B.crossCovarianceOperator xi u := by
  rw [← B.nuisanceCovarianceEquiv_apply xi hgamma hgap]
  exact (B.nuisanceCovarianceEquiv xi hgamma hgap).apply_symm_apply _

theorem exactNuisanceRegression_isRegression [Nonempty Head]
    (xi : B.ParamSpace) {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z)) :
    B.IsNuisanceRegression xi
      (B.exactNuisanceRegression xi hgamma hgap) := by
  intro u z
  let R := B.exactNuisanceRegression xi hgamma hgap
  have hres : B.schurResidual R u =
      B.mainEmbed u - B.nuisanceEmbed (R u) :=
    B.schurResidual_eq_sub R u
  have hcross : inner ℝ (B.nuisanceEmbed z)
      (B.covarianceOperator xi (B.mainEmbed u)) =
      inner ℝ z (B.crossCovarianceOperator xi u) := by
    simpa only [crossCovarianceOperator, ContinuousLinearMap.comp_apply] using
      (ContinuousLinearMap.adjoint_inner_right B.nuisanceEmbeddingCLM z
        (B.covarianceOperator xi (B.mainEmbeddingCLM u))).symm
  have hblock : inner ℝ (B.nuisanceEmbed z)
      (B.covarianceOperator xi (B.nuisanceEmbed (R u))) =
      inner ℝ z (B.nuisanceCovarianceOperator xi (R u)) := by
    simpa only [nuisanceCovarianceOperator,
      ContinuousLinearMap.comp_apply] using
      (ContinuousLinearMap.adjoint_inner_right B.nuisanceEmbeddingCLM z
        (B.covarianceOperator xi
          (B.nuisanceEmbeddingCLM (R u)))).symm
  have hsecond : inner ℝ (B.nuisanceEmbed z)
      (B.covarianceOperator xi (B.schurResidual R u)) = 0 := by
    rw [hres, map_sub, inner_sub_right, hcross, hblock]
    rw [B.exactNuisanceRegression_solve xi hgamma hgap]
    exact sub_self _
  refine ⟨?_, hsecond⟩
  rw [B.covarianceOperator_symmetric xi]
  exact hsecond

theorem exactSchurCovarianceOperator_quadratic [Nonempty Head]
    (xi : B.ParamSpace) {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (u : B.MainSpace) :
    inner ℝ u (B.exactSchurCovarianceOperator xi hgamma hgap u) =
      inner ℝ
        (B.schurResidual (B.exactNuisanceRegression xi hgamma hgap) u)
        (B.covarianceOperator xi
          (B.schurResidual (B.exactNuisanceRegression xi hgamma hgap) u)) := by
  let R := B.exactNuisanceRegression xi hgamma hgap
  let residual := B.schurResidual R u
  have hleft : inner ℝ u
      (B.exactSchurCovarianceOperator xi hgamma hgap u) =
      inner ℝ (B.mainEmbed u) (B.covarianceOperator xi residual) := by
    simpa only [exactSchurCovarianceOperator,
      ContinuousLinearMap.comp_apply,
      B.exactSchurEmbeddingCLM_apply, R, residual] using
      (ContinuousLinearMap.adjoint_inner_right B.mainEmbeddingCLM u
        (B.covarianceOperator xi residual))
  have hres : residual = B.mainEmbed u - B.nuisanceEmbed (R u) := by
    exact B.schurResidual_eq_sub R u
  have horth :=
    (B.exactNuisanceRegression_isRegression xi hgamma hgap u (R u)).2
  have hmain : B.mainEmbed u = residual + B.nuisanceEmbed (R u) := by
    rw [hres]
    abel
  calc
    inner ℝ u (B.exactSchurCovarianceOperator xi hgamma hgap u) =
        inner ℝ (B.mainEmbed u) (B.covarianceOperator xi residual) := hleft
    _ = inner ℝ residual (B.covarianceOperator xi residual) := by
      rw [hmain, inner_add_left, horth, add_zero]





theorem exactNuisanceRegression_norm_le [Nonempty Head]
    (xi : B.ParamSpace) {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (u : B.MainSpace) :
    ‖B.exactNuisanceRegression xi hgamma hgap u‖ ≤
      (‖B.crossCovarianceOperator xi‖ / gamma) * ‖u‖ := by
  let r := B.exactNuisanceRegression xi hgamma hgap u
  have hcoer := hgap r
  rw [B.exactNuisanceRegression_solve xi hgamma hgap] at hcoer
  have hinner : inner ℝ r (B.crossCovarianceOperator xi u) ≤
      ‖r‖ * ‖B.crossCovarianceOperator xi u‖ :=
    real_inner_le_norm _ _
  have hcross : ‖B.crossCovarianceOperator xi u‖ ≤
      ‖B.crossCovarianceOperator xi‖ * ‖u‖ :=
    B.crossCovarianceOperator xi |>.le_opNorm u
  by_cases hr : ‖r‖ = 0
  · change ‖r‖ ≤ (‖B.crossCovarianceOperator xi‖ / gamma) * ‖u‖
    rw [hr]
    exact mul_nonneg
      (div_nonneg (norm_nonneg _) (le_of_lt hgamma)) (norm_nonneg _)
  · have hrpos : 0 < ‖r‖ :=
      lt_of_le_of_ne (norm_nonneg r) (Ne.symm hr)
    have hcancel : gamma * ‖r‖ ≤
        ‖B.crossCovarianceOperator xi u‖ := by
      have hmul : (gamma * ‖r‖) * ‖r‖ ≤
          ‖B.crossCovarianceOperator xi u‖ * ‖r‖ := by
        calc
          (gamma * ‖r‖) * ‖r‖ = gamma * ‖r‖ ^ 2 := by ring
          _ ≤ inner ℝ r (B.crossCovarianceOperator xi u) := hcoer
          _ ≤ ‖B.crossCovarianceOperator xi u‖ * ‖r‖ := by
            simpa [mul_comm] using hinner
      exact (mul_le_mul_iff_right₀ hrpos).mp (by
        simpa [mul_assoc, mul_comm, mul_left_comm] using hmul)
    calc
      ‖B.exactNuisanceRegression xi hgamma hgap u‖ = ‖r‖ := rfl
      _ ≤ ‖B.crossCovarianceOperator xi u‖ / gamma := by
        exact (le_div_iff₀ hgamma).2 (by simpa [mul_comm] using hcancel)
      _ ≤ (‖B.crossCovarianceOperator xi‖ * ‖u‖) / gamma :=
        div_le_div_of_nonneg_right hcross (le_of_lt hgamma)
      _ = (‖B.crossCovarianceOperator xi‖ / gamma) * ‖u‖ := by ring

/-- Exact coordinate recombination underlying the Schur decomposition. -/
theorem combine_eq_schurResidual_add
    (R : B.MainSpace → B.NuisanceSpace)
    (u : B.MainSpace) (z : B.NuisanceSpace) :
    B.combine u z = B.schurResidual R u + B.nuisanceEmbed (z + R u) := by
  apply (EuclideanSpace.equiv B.Coord ℝ).injective
  funext c
  cases c <;> simp [combine, schurResidual]

/-- With an exact regression, the full covariance quadratic form splits
into its Schur residual and the shifted nuisance quadratic form. -/
theorem covarianceForm_schur_decomposition [Nonempty Head]
    (xi : B.ParamSpace) (R : B.MainSpace → B.NuisanceSpace)
    (hR : B.IsNuisanceRegression xi R)
    (u : B.MainSpace) (z : B.NuisanceSpace) :
    (B.vectorFamily.tiltedMixture xi).covarianceForm (B.combine u z) =
      inner ℝ (B.schurResidual R u)
          (B.covarianceOperator xi (B.schurResidual R u)) +
        inner ℝ (B.nuisanceEmbed (z + R u))
          (B.covarianceOperator xi (B.nuisanceEmbed (z + R u))) := by
  rw [← B.inner_covarianceOperator_self,
    B.combine_eq_schurResidual_add R u z]
  simp only [map_add, inner_add_left, inner_add_right]
  rw [(hR u (z + R u)).1, (hR u (z + R u)).2]
  ring

/-- Explicit Euclidean loss when recombining a Schur residual with a
bounded regression. -/
theorem combine_norm_sq_le_schur_coordinates
    (R : B.MainSpace → B.NuisanceSpace) (C : ℝ)
    (hC : 0 ≤ C) (hRnorm : ∀ u, ‖R u‖ ≤ C * ‖u‖)
    (u : B.MainSpace) (z : B.NuisanceSpace) :
    ‖B.combine u z‖ ^ 2 ≤
      (3 + 2 * C ^ 2) * (‖u‖ ^ 2 + ‖z + R u‖ ^ 2) := by
  have hz : ‖z‖ ≤ ‖z + R u‖ + ‖R u‖ := by
    have hid : z = (z + R u) - R u := by abel
    calc
      ‖z‖ = ‖(z + R u) - R u‖ := congrArg norm hid
      _ ≤ ‖z + R u‖ + ‖R u‖ := norm_sub_le (z + R u) (R u)
  have hzC : ‖z‖ ≤ ‖z + R u‖ + C * ‖u‖ :=
    hz.trans (add_le_add (le_refl ‖z + R u‖) (hRnorm u))
  have hzsq : ‖z‖ ^ 2 ≤
      2 * ‖z + R u‖ ^ 2 + 2 * C ^ 2 * ‖u‖ ^ 2 := by
    have hsquare := pow_le_pow_left₀ (norm_nonneg z) hzC 2
    have hprod : 0 ≤ ‖z + R u‖ * (C * ‖u‖) :=
      mul_nonneg (norm_nonneg _) (mul_nonneg hC (norm_nonneg _))
    calc
      ‖z‖ ^ 2 ≤ (‖z + R u‖ + C * ‖u‖) ^ 2 := hsquare
      _ ≤ 2 * ‖z + R u‖ ^ 2 + 2 * C ^ 2 * ‖u‖ ^ 2 := by
        nlinarith [sq_nonneg (‖z + R u‖ - C * ‖u‖)]
  rw [B.combine_norm_sq]
  have hcoef : 0 ≤ 3 + 2 * C ^ 2 := by positivity
  nlinarith [sq_nonneg ‖u‖, sq_nonneg ‖z + R u‖]

/-- Concrete full-gap conclusion from the two paper Schur blocks.  In
particular the proposition-level ODE need not assume a full covariance
gap once Lemma 8.6 supplies the residual bound and the finite nuisance
block supplies its bound. -/
theorem hasCovarianceGap_of_schur [Nonempty Head]
    (xi : B.ParamSpace) (R : B.MainSpace → B.NuisanceSpace)
    (C gammaMain gammaNuisance : ℝ)
    (hC : 0 ≤ C) (hMain : 0 < gammaMain)
    (hNuisance : 0 < gammaNuisance)
    (hRnorm : ∀ u, ‖R u‖ ≤ C * ‖u‖)
    (hRegression : B.IsNuisanceRegression xi R)
    (hSchur : ∀ u,
      gammaMain * ‖u‖ ^ 2 ≤
        inner ℝ (B.schurResidual R u)
          (B.covarianceOperator xi (B.schurResidual R u)))
    (hGamma : ∀ z,
      gammaNuisance * ‖z‖ ^ 2 ≤
        inner ℝ (B.nuisanceEmbed z)
          (B.covarianceOperator xi (B.nuisanceEmbed z))) :
    B.vectorFamily.HasCovarianceGap
      (min gammaMain gammaNuisance / (3 + 2 * C ^ 2)) xi := by
  intro x
  -- Every full parameter has a unique coordinate split; define it directly.
  let u : B.MainSpace :=
    (EuclideanSpace.equiv (MainCoord B.GaugeIndex) ℝ).symm (fun c =>
      match c with
      | .gauge j => x (MomentCoord.gauge j)
      | .slow => x MomentCoord.slow)
  let z : B.NuisanceSpace :=
    (EuclideanSpace.equiv (NuisanceCoord B.HeadIndex) ℝ).symm (fun c =>
      match c with
      | .physical => x MomentCoord.physical
      | .head h => x (MomentCoord.head h))
  have hx : x = B.combine u z := by
    apply (EuclideanSpace.equiv B.Coord ℝ).injective
    funext c
    cases c <;> simp [u, z]
  rw [hx, B.covarianceForm_schur_decomposition xi R hRegression]
  have hminMain : min gammaMain gammaNuisance * ‖u‖ ^ 2 ≤
      inner ℝ (B.schurResidual R u)
        (B.covarianceOperator xi (B.schurResidual R u)) :=
    (mul_le_mul_of_nonneg_right (min_le_left _ _) (sq_nonneg ‖u‖)).trans
      (hSchur u)
  have hminNuisance : min gammaMain gammaNuisance * ‖z + R u‖ ^ 2 ≤
      inner ℝ (B.nuisanceEmbed (z + R u))
        (B.covarianceOperator xi (B.nuisanceEmbed (z + R u))) :=
    (mul_le_mul_of_nonneg_right (min_le_right _ _)
      (sq_nonneg ‖z + R u‖)).trans (hGamma (z + R u))
  have hsum : min gammaMain gammaNuisance *
      (‖u‖ ^ 2 + ‖z + R u‖ ^ 2) ≤
      inner ℝ (B.schurResidual R u)
          (B.covarianceOperator xi (B.schurResidual R u)) +
        inner ℝ (B.nuisanceEmbed (z + R u))
          (B.covarianceOperator xi (B.nuisanceEmbed (z + R u))) := by
    nlinarith
  have hden : 0 < 3 + 2 * C ^ 2 := by positivity
  have hmin : 0 < min gammaMain gammaNuisance :=
    lt_min hMain hNuisance
  have hnorm := B.combine_norm_sq_le_schur_coordinates R C hC hRnorm u z
  apply le_trans ?_ hsum
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ hden).2
  have hmul := mul_le_mul_of_nonneg_left hnorm (le_of_lt hmin)
  nlinarith



/-! ## Exact target and moment correspondence -/













theorem paperMoment_sub [Nonempty Head]
    (F G : B.sampleData.Sample → ℝ) (xi : B.ParamSpace) :
    B.paperMoment (fun m => F m - G m) xi =
      B.paperMoment F xi - B.paperMoment G xi := by
  unfold paperMoment FiniteExponentialFamily.moment
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro m hm
  ring

theorem paperMoment_add [Nonempty Head]
    (F G : B.sampleData.Sample → ℝ) (xi : B.ParamSpace) :
    B.paperMoment (fun m => F m + G m) xi =
      B.paperMoment F xi + B.paperMoment G xi := by
  unfold paperMoment FiniteExponentialFamily.moment
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro m hm
  ring

theorem paperMoment_const_mul [Nonempty Head]
    (a : ℝ) (F : B.sampleData.Sample → ℝ) (xi : B.ParamSpace) :
    B.paperMoment (fun m => a * F m) xi =
      a * B.paperMoment F xi := by
  unfold paperMoment FiniteExponentialFamily.moment
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m hm
  ring

theorem paperMoment_fintype_sum [Nonempty Head]
    {I : Type*} [Fintype I]
    (F : I → B.sampleData.Sample → ℝ) (xi : B.ParamSpace) :
    B.paperMoment (fun m => ∑ i, F i m) xi =
      ∑ i, B.paperMoment (F i) xi := by
  unfold paperMoment FiniteExponentialFamily.moment
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]

theorem paperMoment_const [Nonempty Head]
    (a : ℝ) (xi : B.ParamSpace) :
    B.paperMoment (fun _ => a) xi = B.q * a := by
  unfold paperMoment FiniteExponentialFamily.moment
  rw [← Finset.sum_mul,
    B.vectorFamily.scalarFamily.activeWeight_sum]
  change B.vectorFamily.baseMass * a = B.q * a
  rw [B.vectorFamily_baseMass]

/-- A coordinate of the vector moment is exactly the corresponding raw paper
moment divided by its anisotropic coordinate scale. -/
theorem paperMoment_eq_coordScale_mul_vectorMoment [Nonempty Head]
    (xi : B.ParamSpace) (c : B.Coord) :
    B.paperMoment (fun m => B.rawStatistic m c) xi =
      B.coordScale c * B.vectorFamily.vectorMoment xi c := by
  change (∑ m, B.vectorFamily.scalarFamily.activeWeight xi m *
      B.rawStatistic m c) =
    B.coordScale c *
      (∑ m, B.vectorFamily.scalarFamily.activeWeight xi m •
        B.statistic m) c
  simp only [WithLp.ofLp_sum, WithLp.ofLp_smul, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul, B.statistic_apply]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m _
  field_simp [ne_of_gt (B.coordScale_pos c)]

/-- Exact coordinate-by-coordinate meaning of the vector endpoint.  No
asymptotic estimate is used here. -/
theorem endpoint_iff_paperMoments [Nonempty Head]
    (Delta : Band → ℝ) (xi0 xi1 : B.ParamSpace) :
    B.vectorFamily.vectorMoment xi1 =
        B.vectorFamily.vectorMoment xi0 + B.targetVector Delta ↔
      ∀ c : B.Coord,
        B.paperMoment (fun m => B.rawStatistic m c) xi1 =
          B.paperMoment (fun m => B.rawStatistic m c) xi0 +
            B.unscaledTarget Delta c := by
  constructor
  · intro h c
    have hc := congrArg
      (fun z : B.ParamSpace => (z : B.Coord → ℝ) c) h
    change B.vectorFamily.vectorMoment xi1 c =
      B.vectorFamily.vectorMoment xi0 c + B.targetVector Delta c at hc
    rw [B.targetVector_apply] at hc
    rw [B.paperMoment_eq_coordScale_mul_vectorMoment,
      B.paperMoment_eq_coordScale_mul_vectorMoment]
    rw [hc]
    field_simp [ne_of_gt (B.coordScale_pos c)]
  · intro h
    apply (EuclideanSpace.equiv B.Coord ℝ).injective
    funext c
    have hc := h c
    rw [B.paperMoment_eq_coordScale_mul_vectorMoment,
      B.paperMoment_eq_coordScale_mul_vectorMoment] at hc
    change B.vectorFamily.vectorMoment xi1 c =
      B.vectorFamily.vectorMoment xi0 c +
        B.unscaledTarget Delta c / B.coordScale c
    apply (mul_left_cancel₀ (ne_of_gt (B.coordScale_pos c)))
    rw [mul_add]
    field_simp [ne_of_gt (B.coordScale_pos c)] at hc ⊢
    exact hc

theorem endpoint_preserves_physical [Nonempty Head]
    (Delta : Band → ℝ) (xi0 xi1 : B.ParamSpace)
    (h : B.vectorFamily.vectorMoment xi1 =
      B.vectorFamily.vectorMoment xi0 + B.targetVector Delta) :
    B.paperMoment B.physicalScore xi1 =
      B.paperMoment B.physicalScore xi0 := by
  have hc := (B.endpoint_iff_paperMoments Delta xi0 xi1).mp h
    (MomentCoord.physical : B.Coord)
  simpa [rawStatistic, unscaledTarget] using hc

theorem endpoint_preserves_head [Nonempty Head]
    (Delta : Band → ℝ) (xi0 xi1 : B.ParamSpace)
    (h : B.vectorFamily.vectorMoment xi1 =
      B.vectorFamily.vectorMoment xi0 + B.targetVector Delta)
    (head : B.HeadIndex) :
    B.paperMoment (B.centeredHeadScore head) xi1 =
      B.paperMoment (B.centeredHeadScore head) xi0 := by
  have hc := (B.endpoint_iff_paperMoments Delta xi0 xi1).mp h
    (MomentCoord.head head : B.Coord)
  simpa [rawStatistic, unscaledTarget] using hc

theorem endpoint_preserves_headIndicator [Nonempty Head]
    (Delta : Band → ℝ) (xi0 xi1 : B.ParamSpace)
    (h : B.vectorFamily.vectorMoment xi1 =
      B.vectorFamily.vectorMoment xi0 + B.targetVector Delta)
    (head : B.HeadIndex) :
    B.paperMoment (B.headIndicator head.1) xi1 =
      B.paperMoment (B.headIndicator head.1) xi0 := by
  have hc := B.endpoint_preserves_head Delta xi0 xi1 h head
  have hexpand (xi : B.ParamSpace) :
      B.paperMoment (B.centeredHeadScore head) xi =
        B.paperMoment (B.headIndicator head.1) xi -
          B.q * B.headBaselineMass head.1 := by
    calc
      B.paperMoment (B.centeredHeadScore head) xi =
          B.paperMoment (fun m => B.headIndicator head.1 m -
            B.headBaselineMass head.1) xi := rfl
      _ = B.paperMoment (B.headIndicator head.1) xi -
          B.paperMoment (fun _ => B.headBaselineMass head.1) xi :=
        B.paperMoment_sub _ _ xi
      _ = B.paperMoment (B.headIndicator head.1) xi -
          B.q * B.headBaselineMass head.1 := by
        rw [B.paperMoment_const]
  rw [hexpand, hexpand] at hc
  linarith



theorem headFunctionScore_decomposition (phi : Head → ℝ)
    (m : B.sampleData.Sample) :
    B.headFunctionScore phi m = phi B.referenceHead +
      ∑ h : B.HeadIndex,
        (phi h.1 - phi B.referenceHead) * B.headIndicator h.1 m := by
  let tag := (B.sampleData.cellOf m).1
  by_cases htag : tag = B.referenceHead
  · have hvalue : B.headFunctionScore phi m = phi B.referenceHead := by
      change phi tag = phi B.referenceHead
      rw [htag]
    rw [hvalue]
    suffices (∑ h : B.HeadIndex,
        (phi h.1 - phi B.referenceHead) * B.headIndicator h.1 m) = 0 by
      rw [this, add_zero]
    apply Finset.sum_eq_zero
    intro h hh
    have hne : tag ≠ h.1 := by
      intro heq
      exact h.2 (heq.symm.trans htag)
    change (phi h.1 - phi B.referenceHead) *
      (if tag = h.1 then 1 else 0) = 0
    rw [if_neg hne, mul_zero]
  · let htagIndex : B.HeadIndex := ⟨tag, htag⟩
    change phi tag = phi B.referenceHead +
      ∑ h : B.HeadIndex,
        (phi h.1 - phi B.referenceHead) * B.headIndicator h.1 m
    have hsum : (∑ h : B.HeadIndex,
        (phi h.1 - phi B.referenceHead) * B.headIndicator h.1 m) =
        phi tag - phi B.referenceHead := by
      rw [Finset.sum_eq_single htagIndex]
      · change (phi tag - phi B.referenceHead) *
          (if tag = tag then 1 else 0) = phi tag - phi B.referenceHead
        simp
      · intro h hh hne
        have hval : h.1 ≠ tag := by
          intro heq
          exact hne (Subtype.ext heq)
        change (phi h.1 - phi B.referenceHead) *
          (if tag = h.1 then 1 else 0) = 0
        rw [if_neg hval.symm, mul_zero]
      · intro hnot
        exact (hnot (Finset.mem_univ htagIndex)).elim
    rw [hsum]
    ring

theorem endpoint_preserves_headFunction [Nonempty Head]
    (Delta : Band → ℝ) (xi0 xi1 : B.ParamSpace)
    (h : B.vectorFamily.vectorMoment xi1 =
      B.vectorFamily.vectorMoment xi0 + B.targetVector Delta)
    (phi : Head → ℝ) :
    B.paperMoment (B.headFunctionScore phi) xi1 =
      B.paperMoment (B.headFunctionScore phi) xi0 := by
  have hexpand (xi : B.ParamSpace) :
      B.paperMoment (B.headFunctionScore phi) xi =
        B.q * phi B.referenceHead +
          ∑ k : B.HeadIndex,
            (phi k.1 - phi B.referenceHead) *
              B.paperMoment (B.headIndicator k.1) xi := by
    calc
      B.paperMoment (B.headFunctionScore phi) xi =
          B.paperMoment (fun m => phi B.referenceHead +
            ∑ k : B.HeadIndex,
              (phi k.1 - phi B.referenceHead) *
                B.headIndicator k.1 m) xi := by
            congr 1
            funext m
            exact B.headFunctionScore_decomposition phi m
      _ = B.paperMoment (fun _ => phi B.referenceHead) xi +
          B.paperMoment (fun m => ∑ k : B.HeadIndex,
            (phi k.1 - phi B.referenceHead) *
              B.headIndicator k.1 m) xi := by
            have := B.paperMoment_sub
            unfold paperMoment FiniteExponentialFamily.moment
            rw [← Finset.sum_add_distrib]
            apply Finset.sum_congr rfl
            intro m hm
            ring
      _ = B.q * phi B.referenceHead +
          ∑ k : B.HeadIndex,
            (phi k.1 - phi B.referenceHead) *
              B.paperMoment (B.headIndicator k.1) xi := by
            rw [B.paperMoment_const, B.paperMoment_fintype_sum]
            apply congrArg₂ (· + ·) rfl
            apply Finset.sum_congr rfl
            intro k hk
            exact B.paperMoment_const_mul
              (phi k.1 - phi B.referenceHead)
              (B.headIndicator k.1) xi
  rw [hexpand, hexpand]
  apply congrArg₂ (· + ·) rfl
  apply Finset.sum_congr rfl
  intro k hk
  rw [B.endpoint_preserves_headIndicator Delta xi0 xi1 h k]





theorem endpoint_preserves_primeLogScore_of_compatibility [Nonempty Head]
    (hcompat : B.HasPrimeLogCompatibility)
    (Delta : Band → ℝ) (xi0 xi1 : B.ParamSpace)
    (h : B.vectorFamily.vectorMoment xi1 =
      B.vectorFamily.vectorMoment xi0 + B.targetVector Delta) :
    B.paperMoment B.primeLogScore xi1 =
      B.paperMoment B.primeLogScore xi0 := by
  obtain ⟨a, phi, hpoint⟩ := hcompat
  have hexpand (xi : B.ParamSpace) :
      B.paperMoment B.primeLogScore xi =
        a * B.paperMoment B.physicalScore xi +
          B.paperMoment (B.headFunctionScore phi) xi := by
    calc
      B.paperMoment B.primeLogScore xi =
          B.paperMoment (fun m =>
            a * B.physicalScore m + B.headFunctionScore phi m) xi := by
            congr 1
            funext m
            exact hpoint m
      _ = B.paperMoment (fun m => a * B.physicalScore m) xi +
          B.paperMoment (B.headFunctionScore phi) xi :=
        B.paperMoment_add _ _ xi
      _ = a * B.paperMoment B.physicalScore xi +
          B.paperMoment (B.headFunctionScore phi) xi := by
        rw [B.paperMoment_const_mul]
  rw [hexpand, hexpand,
    B.endpoint_preserves_physical Delta xi0 xi1 h,
    B.endpoint_preserves_headFunction Delta xi0 xi1 h phi]

theorem endpoint_gauge_moment [Nonempty Head]
    (Delta : Band → ℝ) (xi0 xi1 : B.ParamSpace)
    (h : B.vectorFamily.vectorMoment xi1 =
      B.vectorFamily.vectorMoment xi0 + B.targetVector Delta)
    (j : B.GaugeIndex) :
    B.paperMoment (B.gaugeScore j) xi1 =
      B.paperMoment (B.gaugeScore j) xi0 +
        Delta j.1 - B.lowRatio j * Delta B.lowBand := by
  have hc := (B.endpoint_iff_paperMoments Delta xi0 xi1).mp h
    (MomentCoord.gauge j : B.Coord)
  simpa [rawStatistic, unscaledTarget, add_sub_assoc] using hc

theorem endpoint_slow_moment [Nonempty Head]
    (Delta : Band → ℝ) (xi0 xi1 : B.ParamSpace)
    (h : B.vectorFamily.vectorMoment xi1 =
      B.vectorFamily.vectorMoment xi0 + B.targetVector Delta) :
    B.paperMoment B.slowScore xi1 =
      B.paperMoment B.slowScore xi0 +
        ∑ j, B.bandCenter j * Delta j := by
  have hc := (B.endpoint_iff_paperMoments Delta xi0 xi1).mp h
    (MomentCoord.slow : B.Coord)
  simpa [rawStatistic, unscaledTarget] using hc

theorem paperMoment_gaugeScore [Nonempty Head]
    (j : B.GaugeIndex) (xi : B.ParamSpace) :
    B.paperMoment (B.gaugeScore j) xi =
      B.paperMoment (B.bandScore j.1) xi -
        B.lowRatio j * B.paperMoment (B.bandScore B.lowBand) xi := by
  calc
    B.paperMoment (B.gaugeScore j) xi =
        B.paperMoment (fun m => B.bandScore j.1 m -
          B.lowRatio j * B.bandScore B.lowBand m) xi := rfl
    _ = B.paperMoment (B.bandScore j.1) xi -
        B.paperMoment (fun m =>
          B.lowRatio j * B.bandScore B.lowBand m) xi :=
      B.paperMoment_sub _ _ xi
    _ = B.paperMoment (B.bandScore j.1) xi -
        B.lowRatio j * B.paperMoment (B.bandScore B.lowBand) xi := by
      rw [B.paperMoment_const_mul]

theorem paperMoment_slow_decomposition [Nonempty Head]
    (xi : B.ParamSpace) :
    B.paperMoment B.slowScore xi =
      (∑ j : Band,
        B.bandCenter j * B.paperMoment (B.bandScore j) xi) -
        B.paperMoment B.primeLogScore xi := by
  calc
    B.paperMoment B.slowScore xi =
        B.paperMoment (fun m =>
          (∑ j : Band, B.bandCenter j * B.bandScore j m) -
            B.primeLogScore m) xi := by
      congr 1
      funext m
      exact B.slowScore_eq_bandScore_sub_primeLogScore m
    _ = B.paperMoment (fun m =>
          ∑ j : Band, B.bandCenter j * B.bandScore j m) xi -
        B.paperMoment B.primeLogScore xi :=
      B.paperMoment_sub _ _ xi
    _ = (∑ j : Band,
          B.bandCenter j * B.paperMoment (B.bandScore j) xi) -
        B.paperMoment B.primeLogScore xi := by
      rw [B.paperMoment_fintype_sum]
      apply congrArg₂ (· - ·)
      · apply Finset.sum_congr rfl
        intro j hj
        exact B.paperMoment_const_mul (B.bandCenter j)
          (B.bandScore j) xi
      · rfl





theorem lowRatio_pos (j : B.GaugeIndex) : 0 < B.lowRatio j := by
  exact div_pos
    (mul_pos (B.harmonicMass_pos j.1) (B.bandCenter_pos j.1))
    (mul_pos (B.harmonicMass_pos B.lowBand)
      (B.bandCenter_pos B.lowBand))

theorem bandKernelVector_pos (j : Band) : 0 < B.bandKernelVector j := by
  by_cases hj : j = B.lowBand
  · simp [bandKernelVector, hj]
  · simpa only [bandKernelVector, hj, dite_false] using
      B.lowRatio_pos (⟨j, hj⟩ : B.GaugeIndex)

theorem bandRecoveryCoefficient_pos : 0 < B.bandRecoveryCoefficient := by
  unfold bandRecoveryCoefficient
  exact Finset.sum_pos
    (fun j hj => mul_pos (B.bandCenter_pos j) (B.bandKernelVector_pos j))
    ⟨B.lowBand, Finset.mem_univ _⟩



/-- Gauge moments plus the compensated moment recover every individual
band moment once the medium-prime logarithmic score is preserved.  The
single nonvanishing coefficient is exposed explicitly, so this converse is
not hidden inside a coordinate assertion. -/
theorem endpoint_recovers_all_bandMoments [Nonempty Head]
    (Delta : Band → ℝ) (xi0 xi1 : B.ParamSpace)
    (hendpoint : B.vectorFamily.vectorMoment xi1 =
      B.vectorFamily.vectorMoment xi0 + B.targetVector Delta)
    (hlog : B.paperMoment B.primeLogScore xi1 =
      B.paperMoment B.primeLogScore xi0) :
    ∀ j : Band,
      B.paperMoment (B.bandScore j) xi1 =
        B.paperMoment (B.bandScore j) xi0 + Delta j := by
  let e : Band → ℝ := B.bandMomentError Delta xi0 xi1
  have hrelation : ∀ j, e j = B.bandKernelVector j * e B.lowBand := by
    intro j
    by_cases hj : j = B.lowBand
    · subst j
      simp [bandKernelVector]
    · let jg : B.GaugeIndex := ⟨j, hj⟩
      have hg := B.endpoint_gauge_moment Delta xi0 xi1 hendpoint jg
      rw [B.paperMoment_gaugeScore, B.paperMoment_gaugeScore] at hg
      simp only [e, bandMomentError, bandKernelVector, hj, dite_false]
      linarith
  have hsum : ∑ j : Band, B.bandCenter j * e j = 0 := by
    have hs := B.endpoint_slow_moment Delta xi0 xi1 hendpoint
    rw [B.paperMoment_slow_decomposition,
      B.paperMoment_slow_decomposition, hlog] at hs
    simp only [e, bandMomentError]
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib]
    linarith
  have hfactor : B.bandRecoveryCoefficient * e B.lowBand = 0 := by
    rw [bandRecoveryCoefficient, Finset.sum_mul]
    calc
      (∑ j : Band,
          B.bandCenter j * B.bandKernelVector j * e B.lowBand) =
          ∑ j : Band, B.bandCenter j * e j := by
            apply Finset.sum_congr rfl
            intro j hj
            rw [hrelation j]
            ring
      _ = 0 := hsum
  have helow : e B.lowBand = 0 :=
    (mul_eq_zero.mp hfactor).resolve_left
      (ne_of_gt B.bandRecoveryCoefficient_pos)
  intro j
  have hej : e j = 0 := by rw [hrelation j, helow, mul_zero]
  simp only [e, bandMomentError] at hej
  linarith

theorem endpoint_recovers_all_bandMoments_of_compatibility [Nonempty Head]
    (hcompat : B.HasPrimeLogCompatibility)
    (Delta : Band → ℝ) (xi0 xi1 : B.ParamSpace)
    (hendpoint : B.vectorFamily.vectorMoment xi1 =
      B.vectorFamily.vectorMoment xi0 + B.targetVector Delta) :
    ∀ j : Band,
      B.paperMoment (B.bandScore j) xi1 =
        B.paperMoment (B.bandScore j) xi0 + Delta j := by
  exact B.endpoint_recovers_all_bandMoments Delta xi0 xi1 hendpoint
    (B.endpoint_preserves_primeLogScore_of_compatibility
      hcompat Delta xi0 xi1 hendpoint)











/-! ## Actual baseline mixture and coarse cells -/





























































































/-! ## Explicit finite diameter -/





theorem statistic_distance_le_diameter [Nonempty Head]
    (i j : B.sampleData.Sample) :
    ‖B.statistic i - B.statistic j‖ ≤ B.statisticDiameter := by
  calc
    ‖B.statistic i - B.statistic j‖
        ≤ ∑ k : B.sampleData.Sample, ‖B.statistic i - B.statistic k‖ := by
          exact Finset.single_le_sum
            (fun k _ => norm_nonneg (B.statistic i - B.statistic k))
            (Finset.mem_univ j)
    _ ≤ ∑ h : B.sampleData.Sample, ∑ k : B.sampleData.Sample,
          ‖B.statistic h - B.statistic k‖ := by
          exact Finset.single_le_sum
            (fun h _ => Finset.sum_nonneg fun k _ =>
              norm_nonneg (B.statistic h - B.statistic k))
            (Finset.mem_univ i)

/-- The bilinear pair-difference formula for a finite probability law.  We
record it here because it gives a completely explicit, tilt-independent
operator-norm bound for every covariance block used in Proposition 8.7. -/
theorem finiteProbability_covariance_pairDifference
    {Omega : Type*} [Fintype Omega]
    (mu : FiniteProbability Omega) (F G : Omega → ℝ) :
    mu.covariance F G =
      (1 / 2 : ℝ) * ∑ i, ∑ j,
        mu.mass i * mu.mass j * (F i - F j) * (G i - G j) := by
  have hA : (∑ i, ∑ j,
      mu.mass i * mu.mass j * (F i * G i)) =
      ∑ i, mu.mass i * (F i * G i) := by
    calc
      (∑ i, ∑ j, mu.mass i * mu.mass j * (F i * G i)) =
          ∑ i, (mu.mass i * (F i * G i)) * ∑ j, mu.mass j := by
            apply Finset.sum_congr rfl
            intro i _
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro j _
            ring
      _ = ∑ i, mu.mass i * (F i * G i) := by
        rw [mu.mass_sum]
        simp
  have hB : (∑ i, ∑ j,
      mu.mass i * mu.mass j * (F j * G j)) =
      ∑ j, mu.mass j * (F j * G j) := by
    rw [Finset.sum_comm]
    calc
      (∑ j, ∑ i, mu.mass i * mu.mass j * (F j * G j)) =
          ∑ j, (mu.mass j * (F j * G j)) * ∑ i, mu.mass i := by
            apply Finset.sum_congr rfl
            intro j _
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro i _
            ring
      _ = ∑ j, mu.mass j * (F j * G j) := by
        rw [mu.mass_sum]
        simp
  have hC : (∑ i, ∑ j,
      mu.mass i * mu.mass j * (F i * G j)) =
      (∑ i, mu.mass i * F i) * (∑ j, mu.mass j * G j) := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hD : (∑ i, ∑ j,
      mu.mass i * mu.mass j * (F j * G i)) =
      (∑ i, mu.mass i * F i) * (∑ j, mu.mass j * G j) := by
    rw [Finset.sum_comm, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  simp only [FiniteProbability.covariance, FiniteProbability.expect]
  calc
    (∑ i, mu.mass i * (F i * G i)) -
        (∑ i, mu.mass i * F i) * (∑ i, mu.mass i * G i) =
      (1 / 2 : ℝ) *
        ((∑ i, mu.mass i * (F i * G i)) +
          (∑ j, mu.mass j * (F j * G j)) -
          (∑ i, mu.mass i * F i) * (∑ j, mu.mass j * G j) -
          (∑ i, mu.mass i * F i) * (∑ j, mu.mass j * G j)) := by ring
    _ = (1 / 2 : ℝ) *
        ((∑ i, ∑ j, mu.mass i * mu.mass j * (F i * G i)) +
          (∑ i, ∑ j, mu.mass i * mu.mass j * (F j * G j)) -
          (∑ i, ∑ j, mu.mass i * mu.mass j * (F i * G j)) -
          (∑ i, ∑ j, mu.mass i * mu.mass j * (F j * G i))) := by
      rw [hA, hB, hC, hD]
    _ = (1 / 2 : ℝ) * ∑ i, ∑ j,
        mu.mass i * mu.mass j * (F i - F j) * (G i - G j) := by
      congr 1
      rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib,
        ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i _
      rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib,
        ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro j _
      ring



theorem covarianceOperator_eq_covariancePairOperator [Nonempty Head]
    (xi : B.ParamSpace) :
    B.covarianceOperator xi = B.covariancePairOperator xi := by
  apply ContinuousLinearMap.ext
  intro y
  apply ext_inner_left ℝ
  intro x
  rw [B.inner_covarianceOperator]
  unfold FiniteExponentialFamily.covariance
  rw [finiteProbability_covariance_pairDifference]
  simp only [FiniteExponentialFamily.tiltedProbability]
  unfold covariancePairOperator VectorExponentialFamily.probabilityMass
  rw [ContinuousLinearMap.smul_apply, inner_smul_right]
  congr 1
  simp_rw [ContinuousLinearMap.sum_apply, inner_sum]
  simp only [ContinuousLinearMap.smul_apply, inner_smul_right,
    InnerProductSpace.rankOne_apply]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [inner_sub_left, inner_sub_right,
    real_inner_comm (B.statistic i) y,
    real_inner_comm (B.statistic j) y]
  ring



theorem canonicalCrossBound_nonneg [Nonempty Head] :
    0 ≤ B.canonicalCrossBound := by
  exact div_nonneg (sq_nonneg _) (by norm_num)

theorem covarianceOperator_norm_le_canonicalCrossBound [Nonempty Head]
    (xi : B.ParamSpace) :
    ‖B.covarianceOperator xi‖ ≤ B.canonicalCrossBound := by
  rw [B.covarianceOperator_eq_covariancePairOperator]
  unfold covariancePairOperator canonicalCrossBound
  calc
    ‖(1 / 2 : ℝ) • ∑ i : B.sampleData.Sample,
        ∑ j : B.sampleData.Sample,
          (B.vectorFamily.probabilityMass xi i *
            B.vectorFamily.probabilityMass xi j) •
              InnerProductSpace.rankOne ℝ
                (B.statistic i - B.statistic j)
                (B.statistic i - B.statistic j)‖
        ≤ (1 / 2 : ℝ) * ∑ i : B.sampleData.Sample,
            ∑ j : B.sampleData.Sample,
              (B.vectorFamily.probabilityMass xi i *
                B.vectorFamily.probabilityMass xi j) *
                ‖B.statistic i - B.statistic j‖ ^ 2 := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by norm_num)]
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          calc
            ‖∑ i : B.sampleData.Sample,
                ∑ j : B.sampleData.Sample,
                  (B.vectorFamily.probabilityMass xi i *
                    B.vectorFamily.probabilityMass xi j) •
                      InnerProductSpace.rankOne ℝ
                        (B.statistic i - B.statistic j)
                        (B.statistic i - B.statistic j)‖
                ≤ ∑ i : B.sampleData.Sample,
                    ‖∑ j : B.sampleData.Sample,
                      (B.vectorFamily.probabilityMass xi i *
                        B.vectorFamily.probabilityMass xi j) •
                          InnerProductSpace.rankOne ℝ
                            (B.statistic i - B.statistic j)
                            (B.statistic i - B.statistic j)‖ :=
                  norm_sum_le _ _
            _ ≤ ∑ i : B.sampleData.Sample,
                ∑ j : B.sampleData.Sample,
                  ‖(B.vectorFamily.probabilityMass xi i *
                    B.vectorFamily.probabilityMass xi j) •
                      InnerProductSpace.rankOne ℝ
                        (B.statistic i - B.statistic j)
                        (B.statistic i - B.statistic j)‖ := by
                  apply Finset.sum_le_sum
                  intro i _
                  exact norm_sum_le _ _
            _ = ∑ i : B.sampleData.Sample,
                ∑ j : B.sampleData.Sample,
                  (B.vectorFamily.probabilityMass xi i *
                    B.vectorFamily.probabilityMass xi j) *
                    ‖B.statistic i - B.statistic j‖ ^ 2 := by
                  apply Finset.sum_congr rfl
                  intro i _
                  apply Finset.sum_congr rfl
                  intro j _
                  have hi : 0 ≤ B.vectorFamily.probabilityMass xi i :=
                    B.vectorFamily.scalarFamily.probabilityMass_nonneg xi i
                  have hj : 0 ≤ B.vectorFamily.probabilityMass xi j :=
                    B.vectorFamily.scalarFamily.probabilityMass_nonneg xi j
                  rw [norm_smul, InnerProductSpace.norm_rankOne,
                    Real.norm_eq_abs,
                    abs_of_nonneg (mul_nonneg hi hj)]
                  ring
    _ ≤ (1 / 2 : ℝ) * ∑ i : B.sampleData.Sample,
          ∑ j : B.sampleData.Sample,
            (B.vectorFamily.probabilityMass xi i *
              B.vectorFamily.probabilityMass xi j) *
              B.statisticDiameter ^ 2 := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        apply Finset.sum_le_sum
        intro i _
        apply Finset.sum_le_sum
        intro j _
        exact mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (norm_nonneg _)
            (B.statistic_distance_le_diameter i j) 2)
          (mul_nonneg
            (B.vectorFamily.scalarFamily.probabilityMass_nonneg xi i)
            (B.vectorFamily.scalarFamily.probabilityMass_nonneg xi j))
    _ = B.statisticDiameter ^ 2 / 2 := by
      have hsum : ∑ i : B.sampleData.Sample,
          B.vectorFamily.probabilityMass xi i = 1 :=
        B.vectorFamily.scalarFamily.probabilityMass_sum xi
      have hdouble :
          (∑ i : B.sampleData.Sample,
            ∑ j : B.sampleData.Sample,
              (B.vectorFamily.probabilityMass xi i *
                B.vectorFamily.probabilityMass xi j) *
                B.statisticDiameter ^ 2) =
              B.statisticDiameter ^ 2 := by
        calc
        (∑ i : B.sampleData.Sample,
            ∑ j : B.sampleData.Sample,
              (B.vectorFamily.probabilityMass xi i *
                B.vectorFamily.probabilityMass xi j) *
                B.statisticDiameter ^ 2) =
            ∑ i : B.sampleData.Sample,
              (B.vectorFamily.probabilityMass xi i *
                B.statisticDiameter ^ 2) *
                ∑ j : B.sampleData.Sample,
                  B.vectorFamily.probabilityMass xi j := by
              apply Finset.sum_congr rfl
              intro i _
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro j _
              ring
        _ = ∑ i : B.sampleData.Sample,
              B.vectorFamily.probabilityMass xi i *
                B.statisticDiameter ^ 2 := by rw [hsum]; simp
        _ = (∑ i : B.sampleData.Sample,
              B.vectorFamily.probabilityMass xi i) *
                B.statisticDiameter ^ 2 := by rw [Finset.sum_mul]
        _ = B.statisticDiameter ^ 2 := by rw [hsum, one_mul]
      rw [hdouble]
      ring

/-- In particular, the main-to-nuisance cross block has the same canonical
tilt-independent bound.  Thus Proposition 8.7 does not need an additional
analytic cross-block hypothesis or a box-dependent constant. -/
theorem crossCovarianceOperator_norm_le_canonicalCrossBound
    [Nonempty Head] (xi : B.ParamSpace) :
    ‖B.crossCovarianceOperator xi‖ ≤ B.canonicalCrossBound := by
  have hAdj : ‖B.nuisanceEmbeddingCLM.adjoint‖ ≤ 1 := by
    simpa using B.nuisanceEmbeddingCLM_norm_le_one
  have hinner :
      ‖(B.covarianceOperator xi).comp B.mainEmbeddingCLM‖ ≤
        B.canonicalCrossBound * 1 := by
    calc
      ‖(B.covarianceOperator xi).comp B.mainEmbeddingCLM‖ ≤
          ‖B.covarianceOperator xi‖ * ‖B.mainEmbeddingCLM‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ B.canonicalCrossBound * 1 :=
        mul_le_mul (B.covarianceOperator_norm_le_canonicalCrossBound xi)
          B.mainEmbeddingCLM_norm_le_one
          (norm_nonneg _) B.canonicalCrossBound_nonneg
  unfold crossCovarianceOperator
  calc
    ‖B.nuisanceEmbeddingCLM.adjoint.comp
        ((B.covarianceOperator xi).comp B.mainEmbeddingCLM)‖ ≤
        ‖B.nuisanceEmbeddingCLM.adjoint‖ *
          ‖(B.covarianceOperator xi).comp B.mainEmbeddingCLM‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ 1 * (B.canonicalCrossBound * 1) :=
      mul_le_mul hAdj hinner (norm_nonneg _) zero_le_one
    _ = B.canonicalCrossBound := by ring

/-! ## A finite `ell^1` tilt bound -/













































/-! ## Target envelopes imply the ODE radius margin -/















/-! ## Concrete Proposition 8.7 endpoint -/











end BridgeData

/-! ## Non-circular order of asymptotic choices -/



end PaperBridgeFit

end


end Erdos390.Full

end

/- Source module: Erdos390.Full.PaperBridgeFitFeasibility -/
section


/-!
# Feasibility and frozen-ledger consequences of the actual bridge tilt

The nonlinear bridge changes only the active structured-cell coordinates.
This file records, for the literal finite exponential family used in
`PaperBridgeFit`, the conclusions which are independent of the analytic
covariance estimates: positivity, preservation of the active mass, an
explicit coordinate ceiling on a preselected parameter ball, and literal
preservation of every frozen top/protected coordinate and integer quota.

The coordinate ceiling is not postulated as a property of the output.  It is
deduced from the exact finite density-ratio estimate and an explicit baseline
slack inequality.  In the final Proposition 8.7 specialization that baseline
slack is discharged by the structured-cell count and the paper's `O(1/L)`
baseline-coordinate bound.
-/

open scoped BigOperators

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

open FiniteExponentialFamily

namespace StructuredSampleData

variable {Head : Type*} [Fintype Head]







end StructuredSampleData

namespace BridgeData

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]
  (B : BridgeData Head Band)



theorem activeCoordinateWeight_nonneg [Nonempty Head]
    (xi : B.ParamSpace) (m : B.sampleData.Sample) :
    0 <= B.activeCoordinateWeight xi m :=
  B.vectorFamily.scalarFamily.activeWeight_nonneg xi m



/-- The active smooth-row mass is exactly fixed by every exponential tilt. -/
theorem sum_activeCoordinateWeight [Nonempty Head]
    (xi : B.ParamSpace) :
    (Finset.univ.sum fun m : B.sampleData.Sample =>
      B.activeCoordinateWeight xi m) = B.q := by
  change (Finset.univ.sum fun m : B.sampleData.Sample =>
    B.vectorFamily.scalarFamily.activeWeight xi m) = B.q
  rw [B.vectorFamily.scalarFamily.activeWeight_sum]
  exact B.vectorFamily_baseMass



/-! The paper uses a compact *effective-score* box, not the crude sum of
all score norms.  The next estimates therefore take the correct pointwise
score bound and have constants independent of the number of active cells. -/

theorem exp_neg_effectiveBound_mul_q_le_partition
    [Nonempty Head] (xi : B.ParamSpace) (R : Real)
    (hscore : forall m : B.sampleData.Sample,
      |B.vectorFamily.scalarFamily.score m xi / B.L| <= R) :
    Real.exp (-R) * B.q <=
      B.vectorFamily.scalarFamily.partition xi := by
  rw [FiniteExponentialFamily.partition]
  calc
    Real.exp (-R) * B.q =
        Finset.univ.sum fun m : B.sampleData.Sample =>
          B.baseline.baseWeight m * Real.exp (-R) := by
      rw [← Finset.sum_mul, B.baseline.baseWeight_sum]
      simp [q, mul_comm]
    _ <= Finset.univ.sum fun m : B.sampleData.Sample =>
        B.vectorFamily.scalarFamily.unnormalizedWeight xi m := by
      apply Finset.sum_le_sum
      intro m _
      simp only [FiniteExponentialFamily.unnormalizedWeight,
        vectorFamily, VectorExponentialFamily.scalarFamily]
      apply mul_le_mul_of_nonneg_left _ (B.baseline.baseWeight_nonneg m)
      apply Real.exp_le_exp.mpr
      exact (neg_le_neg (hscore m)).trans
        (neg_abs_le (B.vectorFamily.scalarFamily.score m xi / B.L))

theorem probabilityMass_le_exp_twoEffectiveBound_mul_baseline
    [Nonempty Head] (xi : B.ParamSpace) (R : Real)
    (hscore : forall m : B.sampleData.Sample,
      |B.vectorFamily.scalarFamily.score m xi / B.L| <= R)
    (m : B.sampleData.Sample) :
    B.vectorFamily.probabilityMass xi m <=
      Real.exp (2 * R) * B.vectorFamily.probabilityMass 0 m := by
  have hq : B.q ≠ 0 := ne_of_gt B.q_pos
  have hZ : 0 < B.vectorFamily.scalarFamily.partition xi :=
    B.vectorFamily.scalarFamily.partition_pos xi
  have hexp : Real.exp (2 * R) * Real.exp (-R) = Real.exp R := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [B.probabilityMass_zero m]
  change B.vectorFamily.scalarFamily.unnormalizedWeight xi m /
      B.vectorFamily.scalarFamily.partition xi <=
    Real.exp (2 * R) * (B.baseline.baseWeight m / B.q)
  apply (div_le_iff₀ hZ).2
  calc
    B.vectorFamily.scalarFamily.unnormalizedWeight xi m =
        B.baseline.baseWeight m *
          Real.exp (B.vectorFamily.scalarFamily.score m xi / B.L) := by
      rfl
    _ <= B.baseline.baseWeight m * Real.exp R := by
      apply mul_le_mul_of_nonneg_left _ (B.baseline.baseWeight_nonneg m)
      exact Real.exp_le_exp.mpr
        ((le_abs_self _).trans (hscore m))
    _ = (Real.exp (2 * R) * (B.baseline.baseWeight m / B.q)) *
        (Real.exp (-R) * B.q) := by
      field_simp [hq]
      calc
        B.baseline.baseWeight m * Real.exp R =
            B.baseline.baseWeight m *
              (Real.exp (2 * R) * Real.exp (-R)) := by rw [hexp]
        _ = B.baseline.baseWeight m * Real.exp (2 * R) *
              Real.exp (-R) := by ring
    _ <= (Real.exp (2 * R) * (B.baseline.baseWeight m / B.q)) *
        B.vectorFamily.scalarFamily.partition xi := by
      exact mul_le_mul_of_nonneg_left
        (B.exp_neg_effectiveBound_mul_q_le_partition xi R hscore)
        (mul_nonneg (le_of_lt (Real.exp_pos _))
          (div_nonneg (B.baseline.baseWeight_nonneg m)
            (le_of_lt B.q_pos)))

theorem activeCoordinateWeight_le_exp_twoEffectiveBound_mul_baseline
    [Nonempty Head] (xi : B.ParamSpace) (R : Real)
    (hscore : forall m : B.sampleData.Sample,
      |B.vectorFamily.scalarFamily.score m xi / B.L| <= R)
    (m : B.sampleData.Sample) :
    B.activeCoordinateWeight xi m <=
      Real.exp (2 * R) * B.baseline.baseWeight m := by
  rw [activeCoordinateWeight, FiniteExponentialFamily.activeWeight]
  change B.vectorFamily.baseMass * B.vectorFamily.probabilityMass xi m <=
    Real.exp (2 * R) * B.baseline.baseWeight m
  rw [B.vectorFamily_baseMass]
  calc
    B.q * B.vectorFamily.probabilityMass xi m <=
        B.q * (Real.exp (2 * R) *
          B.vectorFamily.probabilityMass 0 m) :=
      mul_le_mul_of_nonneg_left
        (B.probabilityMass_le_exp_twoEffectiveBound_mul_baseline
          xi R hscore m) (le_of_lt B.q_pos)
    _ = Real.exp (2 * R) * B.baseline.baseWeight m := by
      rw [B.probabilityMass_zero m]
      field_simp [ne_of_gt B.q_pos]







/-! ## Actual natural-number coordinates -/



theorem ambientActiveWeight_nonneg [Nonempty Head]
    (xi : B.ParamSpace) (a : Nat) :
    0 <= B.ambientActiveWeight xi a := by
  apply Finset.sum_nonneg
  intro m _
  split_ifs
  · exact B.activeCoordinateWeight_nonneg xi m
  · exact le_rfl

theorem ambientActiveWeight_eq_of_value
    [Nonempty Head]
    (hsep : B.sampleData.HeadPatternsSeparated)
    (xi : B.ParamSpace) (m : B.sampleData.Sample) :
    B.ambientActiveWeight xi (B.sampleData.value m) =
      B.activeCoordinateWeight xi m := by
  classical
  rw [ambientActiveWeight, Finset.sum_eq_single m]
  · simp
  · intro k _ hkm
    rw [if_neg]
    intro hvalue
    exact hkm
      (B.sampleData.value_injective_of_headPatternsSeparated hsep hvalue)
  · simp

theorem ambientActiveWeight_eq_zero_of_not_value
    [Nonempty Head] (xi : B.ParamSpace) (a : Nat)
    (ha : forall m : B.sampleData.Sample, B.sampleData.value m ≠ a) :
    B.ambientActiveWeight xi a = 0 := by
  rw [ambientActiveWeight]
  apply Finset.sum_eq_zero
  intro m _
  rw [if_neg (ha m)]





/-- Feasibility in the paper's correct compact effective-score box.  Unlike
the preceding crude Euclidean-ball corollary, this bound has no factor equal
to the number of active coordinates and is the form consumed by the final
non-circular ODE argument. -/
theorem ambientCombinedWeight_mem_Icc_of_effectiveScoreBound
    [Nonempty Head]
    (hsep : B.sampleData.HeadPatternsSeparated)
    (frozenWeight : Nat -> Real)
    (hfrozen : forall a, frozenWeight a ∈ Set.Icc (0 : Real) 1)
    (xi : B.ParamSpace) (R : Real)
    (hscore : forall m : B.sampleData.Sample,
      |B.vectorFamily.scalarFamily.score m xi / B.L| <= R)
    (hslack : forall m : B.sampleData.Sample,
      frozenWeight (B.sampleData.value m) +
        Real.exp (2 * R) * B.baseline.baseWeight m <= 1) :
    forall a : Nat,
      B.ambientCombinedWeight frozenWeight xi a ∈ Set.Icc (0 : Real) 1 := by
  intro a
  constructor
  · exact add_nonneg (hfrozen a).1 (B.ambientActiveWeight_nonneg xi a)
  · by_cases ha : exists m : B.sampleData.Sample, B.sampleData.value m = a
    · obtain ⟨m, hm⟩ := ha
      rw [ambientCombinedWeight, ← hm,
        B.ambientActiveWeight_eq_of_value hsep xi m]
      calc
        frozenWeight (B.sampleData.value m) + B.activeCoordinateWeight xi m
            <= frozenWeight (B.sampleData.value m) +
              Real.exp (2 * R) * B.baseline.baseWeight m := by
          simpa [add_comm] using add_le_add_left
            (B.activeCoordinateWeight_le_exp_twoEffectiveBound_mul_baseline
              xi R hscore m)
            (frozenWeight (B.sampleData.value m))
        _ <= 1 := hslack m
    · rw [ambientCombinedWeight,
        B.ambientActiveWeight_eq_zero_of_not_value xi a
          (fun m hm => ha ⟨m, hm⟩), add_zero]
      exact (hfrozen a).2



/-! ## Frozen top/protected coordinates and the integer ledger -/









/-- Frozen coordinates are literally unchanged between any two bridge
parameters, not merely equal in total mass. -/
theorem combinedWeight_fixed_unchanged [Nonempty Head]
    {Fixed : Type*} (fixedWeight : Fixed -> Real)
    (xi eta : B.ParamSpace) (f : Fixed) :
    B.combinedWeight fixedWeight xi (Sum.inl f) =
      B.combinedWeight fixedWeight eta (Sum.inl f) := rfl

theorem sum_combinedWeight [Nonempty Head]
    {Fixed : Type*} [Fintype Fixed]
    (fixedWeight : Fixed -> Real) (xi : B.ParamSpace) :
    (Finset.univ.sum fun a : Fixed ⊕ B.sampleData.Sample =>
      B.combinedWeight fixedWeight xi a) =
      (Finset.univ.sum fixedWeight) + B.q := by
  rw [Fintype.sum_sum_type]
  simp only [combinedWeight]
  rw [B.sum_activeCoordinateWeight xi]

/-- The exact integer smooth-row quota is preserved because the active mass
is fixed and every other ledger entry is frozen. -/
theorem sum_combinedWeight_eq_integerQuota [Nonempty Head]
    {Fixed : Type*} [Fintype Fixed]
    (fixedWeight : Fixed -> Real) (quota : Int)
    (hquota : (quota : Real) =
      (Finset.univ.sum fixedWeight) + B.q)
    (xi : B.ParamSpace) :
    (Finset.univ.sum fun a : Fixed ⊕ B.sampleData.Sample =>
      B.combinedWeight fixedWeight xi a) = (quota : Real) := by
  rw [B.sum_combinedWeight fixedWeight xi, ← hquota]



end BridgeData

end

end Erdos390.Full.PaperBridgeFit

end

/- Source module: Erdos390.Full.EquivalentNormODE -/
section


/-!
# Straight-target continuation in a preselected equivalent norm

The paper controls the nonlinear bridge in an effective norm rather than in
the ambient Euclidean norm.  This file records the exact transport needed for
that argument.  A continuous linear equivalence identifies the effective
parameter space with the original one; Picard--Lindelof is run on the closed
ball in the effective space, and the resulting path is then mapped back.

The theorem below constructs the path.  In particular it does not assume an
integral curve or a continuation principle.  Its hypotheses are precisely the
boxwise smoothness, speed, derivative, and solve identities that the arithmetic
Schur analysis supplies.
-/

open Metric Set

namespace Erdos390.Full.EquivalentNormODE

noncomputable section

section GenericTransport

variable {E F Y : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  [CompleteSpace F] [FiniteDimensional ℝ F]

/-- Non-circular straight-target lift in a norm transported by a continuous
linear equivalence.  The radius and every hypothesis on its closed ball are
fixed before the path is constructed. -/
theorem exists_straightTargetLift_on_preselectedEquivalentBall
    (e : F ≃L[ℝ] E)
    (v : E → E) (M : E → Y) (J : E → E →L[ℝ] Y)
    (x0 : E) (target : Y) (a speed : NNReal)
    (hsmooth : ContDiffOn ℝ 1
      (fun z : F => e.symm (v (e z)))
      (closedBall (e.symm x0) (a : ℝ)))
    (hbound : ∀ z ∈ closedBall (e.symm x0) (a : ℝ),
      ‖e.symm (v (e z))‖ ≤ (speed : ℝ))
    (hmargin : speed ≤ a)
    (hM : ∀ z ∈ closedBall (e.symm x0) (a : ℝ),
      HasFDerivAt M (J (e z)) (e z))
    (hsolve : ∀ z ∈ closedBall (e.symm x0) (a : ℝ),
      J (e z) (v (e z)) = target) :
    ∃ path : ℝ → E,
      path 0 = x0 ∧
      (∀ t ∈ Icc (0 : ℝ) 1,
        e.symm (path t) ∈ closedBall (e.symm x0) (a : ℝ)) ∧
      (∀ t ∈ Icc (0 : ℝ) 1,
        HasDerivWithinAt path (v (path t)) (Icc (0 : ℝ) 1) t) ∧
      M (path 1) = M x0 + target := by
  let vF : F → F := fun z => e.symm (v (e z))
  let MF : F → Y := fun z => M (e z)
  let JF : F → F →L[ℝ] Y := fun z => (J (e z)).comp e.toContinuousLinearMap
  obtain ⟨K, hK⟩ := hsmooth.exists_lipschitzOnWith one_ne_zero
    (convex_closedBall (e.symm x0) (a : ℝ))
    (isCompact_closedBall (e.symm x0) (a : ℝ))
  have hMF : ∀ z ∈ closedBall (e.symm x0) (a : ℝ),
      HasFDerivAt MF (JF z) z := by
    intro z hz
    simpa only [MF, JF] using
      (hM z hz).comp z e.hasFDerivAt
  have hsolveF : ∀ z ∈ closedBall (e.symm x0) (a : ℝ),
      JF z (vF z) = target := by
    intro z hz
    simpa [JF, vF] using hsolve z hz
  obtain ⟨pathF, hzero, hball, hderiv, hend⟩ :=
    Erdos390.straight_target_fit_of_lipschitz
      vF MF JF (e.symm x0) target a speed K
      (by simpa only [vF] using hbound) hK hmargin hMF hsolveF
  let path : ℝ → E := fun t => e (pathF t)
  refine ⟨path, ?_, ?_, ?_, ?_⟩
  · simp only [path, hzero, ContinuousLinearEquiv.apply_symm_apply]
  · intro t ht
    simpa only [path, ContinuousLinearEquiv.symm_apply_apply] using hball t ht
  · intro t ht
    have hcomp := e.hasFDerivAt.comp_hasDerivWithinAt t (hderiv t ht)
    simpa [path, vF] using hcomp
  · simpa only [path, MF, ContinuousLinearEquiv.apply_symm_apply] using hend

end GenericTransport

namespace VectorExponentialFamily

variable {Omega E F : Type*} [Fintype Omega]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [CompleteSpace F] [FiniteDimensional ℝ F]

/-- Effective-norm continuation for the actual finite exponential family.
The covariance gap proves both Jacobian inversion and local smoothness.  The
only additional quantitative input is the effective velocity bound on the
box; the path, its confinement, and the exact endpoint are conclusions. -/
theorem exists_straightTargetLift_on_preselectedEquivalentBall
    (vf : Erdos390.Full.VectorExponentialFamily Omega E)
    (e : F ≃L[ℝ] E) (x0 target : E) (a speed : NNReal)
    {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z ∈ closedBall (e.symm x0) (a : ℝ),
      vf.HasCovarianceGap gamma (e z))
    (hbound : ∀ z ∈ closedBall (e.symm x0) (a : ℝ),
      ‖e.symm (vf.vectorField target (e z))‖ ≤ (speed : ℝ))
    (hmargin : speed ≤ a) :
    ∃ path : ℝ → E,
      path 0 = x0 ∧
      (∀ t ∈ Icc (0 : ℝ) 1,
        e.symm (path t) ∈ closedBall (e.symm x0) (a : ℝ)) ∧
      (∀ t ∈ Icc (0 : ℝ) 1,
        HasDerivWithinAt path
          (vf.vectorField target (path t)) (Icc (0 : ℝ) 1) t) ∧
      vf.vectorMoment (path 1) = vf.vectorMoment x0 + target := by
  have hsmooth : ContDiffOn ℝ 1
      (fun z : F => e.symm (vf.vectorField target (e z)))
      (closedBall (e.symm x0) (a : ℝ)) := by
    intro z hz
    have hv : ContDiffAt ℝ 1 (vf.vectorField target) (e z) :=
      vf.vectorField_contDiffAt target hgamma (hgap z hz)
    have hinner : ContDiffAt ℝ 1
        (fun y : F => vf.vectorField target (e y)) z :=
      hv.comp z e.contDiff.contDiffAt
    exact (e.symm.contDiff.contDiffAt.comp z hinner).contDiffWithinAt
  exact Erdos390.Full.EquivalentNormODE.exists_straightTargetLift_on_preselectedEquivalentBall
    e (vf.vectorField target) vf.vectorMoment vf.jacobian x0 target a speed
    hsmooth hbound hmargin
    (fun z _ => vf.hasFDerivAt_vectorMoment (e z))
    (fun z hz => vf.jacobian_vectorField target hgamma (hgap z hz))

end VectorExponentialFamily

end

end Erdos390.Full.EquivalentNormODE

end

/- Source module: Erdos390.Full.PaperEffectiveNorm -/
section


/-!
# The concrete effective parameter norm of Proposition 8.7

The paper controls a parameter by three quantities: the largest effective
prime fugacity, the Euclidean nuisance block, and the scaled slow parameter
`w * lambda`.  The slow coordinate of `BridgeData.ParamSpace` is already
`w * lambda`.  We therefore map the actual parameter space injectively into
the product of these three normed spaces and use the norm inherited by the
range.  This gives a genuine complete finite-dimensional normed space and a
continuous linear equivalence back to the original parameter space, exactly
the input required by `EquivalentNormODE`.
-/

open scoped BigOperators
open Metric Set

namespace Erdos390.Full.PaperBridgeFit
namespace BridgeData

open ArithmeticBandGeometry

noncomputable section

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]
  (B : BridgeData Head Band)

























































/-! ## Non-circular ODE transport in the literal paper norm -/

/-- The finite exponential-family ODE on a ball chosen in the effective
paper norm.  The path is constructed, remains in the preselected box, and
has the exact raw endpoint.  The two analytic hypotheses are deliberately
stated on that same preselected ball so a later theorem can discharge them
from Lemmas 8.4--8.6 without changing norms or choosing a box a posteriori. -/
theorem exists_paperFit_on_preselectedEffectiveBall [Nonempty Head]
    (Delta : Band → ℝ) (a speed : NNReal) {gamma : ℝ}
    (hgamma : 0 < gamma)
    (hgap : ∀ z ∈ closedBall (0 : B.EffectiveParamSpace) (a : ℝ),
      B.vectorFamily.HasCovarianceGap gamma (B.effectiveParamEquiv z))
    (hbound : ∀ z ∈ closedBall (0 : B.EffectiveParamSpace) (a : ℝ),
      ‖B.effectiveParamEquiv.symm
        (B.vectorFamily.vectorField (B.targetVector Delta)
          (B.effectiveParamEquiv z))‖ ≤ (speed : ℝ))
    (hmargin : speed ≤ a) :
    ∃ path : ℝ → B.ParamSpace,
      path 0 = 0 ∧
      (∀ t ∈ Icc (0 : ℝ) 1,
        B.effectiveParamEquiv.symm (path t) ∈
          closedBall (0 : B.EffectiveParamSpace) (a : ℝ)) ∧
      (∀ t ∈ Icc (0 : ℝ) 1,
        B.paperEffectiveSize (path t) ≤ 3 * (a : ℝ)) ∧
      (∀ t ∈ Icc (0 : ℝ) 1,
        HasDerivWithinAt path
          (B.vectorFamily.vectorField (B.targetVector Delta) (path t))
          (Icc (0 : ℝ) 1) t) ∧
      ∀ c : B.Coord,
        B.paperMoment (fun m => B.rawStatistic m c) (path 1) =
          B.paperMoment (fun m => B.rawStatistic m c) 0 +
            B.unscaledTarget Delta c := by
  obtain ⟨path, hzero, hball, hderiv, hend⟩ :=
    Erdos390.Full.EquivalentNormODE.VectorExponentialFamily.exists_straightTargetLift_on_preselectedEquivalentBall
        B.vectorFamily B.effectiveParamEquiv (0 : B.ParamSpace)
        (B.targetVector Delta) a speed hgamma
        (by simpa using hgap) (by simpa using hbound) hmargin
  have hballZero : ∀ t ∈ Icc (0 : ℝ) 1,
      B.effectiveParamEquiv.symm (path t) ∈
        closedBall (0 : B.EffectiveParamSpace) (a : ℝ) := by
    simpa using hball
  refine ⟨path, hzero, hballZero, ?_, hderiv, ?_⟩
  · intro t ht
    let z : B.EffectiveParamSpace := B.effectiveParamEquiv.symm (path t)
    have hzBall : z ∈ closedBall (0 : B.EffectiveParamSpace) (a : ℝ) :=
      hballZero t ht
    have hzNorm : ‖z‖ ≤ (a : ℝ) := by
      simpa only [mem_closedBall, dist_zero_right] using hzBall
    have hpath : B.effectiveParamEquiv z = path t := by
      exact B.effectiveParamEquiv.apply_symm_apply (path t)
    rw [← hpath]
    exact (B.paperEffectiveSize_effectiveParamEquiv_le z).trans
      (mul_le_mul_of_nonneg_left hzNorm (by norm_num))
  · exact (B.endpoint_iff_paperMoments Delta 0 (path 1)).mp hend



end

end BridgeData
end Erdos390.Full.PaperBridgeFit

end

/- Source module: Erdos390.Full.PaperBaselineSlack -/
section


/-!
# Converting the baseline `O(1 / log n)` ledger into coordinate slack

The baseline active-measure lemma and the protected-floor construction give
separate `C / L` bounds.  This file contains the exact finite inequality which
turns those bounds into the combined ceiling required after a compact
effective tilt.  Thus Proposition 8.7 need not assume its final `[0,1]`
conclusion.
-/

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

namespace BridgeData

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]
  (B : BridgeData Head Band)



/-- Separate `C/L` bounds imply the exact frozen-plus-active baseline slack
once `L` exceeds the displayed fixed constant. -/
theorem combinedBaselineSlack_of_div_log_bounds
    [Nonempty Head]
    (frozenWeight : Nat -> Real) (Cfixed Cactive R : Real)
    (hfrozen : forall m : B.sampleData.Sample,
      frozenWeight (B.sampleData.value m) <= Cfixed / B.L)
    (hactive : forall m : B.sampleData.Sample,
      B.baseline.baseWeight m <= Cactive / B.L)
    (hlarge : Cfixed + Real.exp (2 * R) * Cactive <= B.L) :
    forall m : B.sampleData.Sample,
      frozenWeight (B.sampleData.value m) +
        Real.exp (2 * R) * B.baseline.baseWeight m <= 1 := by
  intro m
  calc
    frozenWeight (B.sampleData.value m) +
        Real.exp (2 * R) * B.baseline.baseWeight m <=
      Cfixed / B.L + Real.exp (2 * R) * (Cactive / B.L) :=
        add_le_add (hfrozen m) (mul_le_mul_of_nonneg_left
          (hactive m) (le_of_lt (Real.exp_pos _)))
    _ = (Cfixed + Real.exp (2 * R) * Cactive) / B.L := by ring
    _ <= B.L / B.L :=
      div_le_div_of_nonneg_right hlarge (le_of_lt B.L_pos)
    _ = 1 := div_self (ne_of_gt B.L_pos)



end BridgeData

end

end Erdos390.Full.PaperBridgeFit

end

/- Source module: Erdos390.Full.PaperEffectiveScoreBound -/
section


/-!
# Dimension-free score control in the paper's effective parameter norm

The Euclidean parameter norm has one coordinate per prime band and is not the
norm used in the non-circular argument of Proposition 8.7.  This file proves
the exact re-expansion of the finite exponential-family score into the
effective prime fugacities and the fixed nuisance block.  It then obtains a
pointwise score bound whose constant is independent of the number of bands.
-/

open scoped BigOperators

namespace Erdos390.Full.PaperBridgeFit
namespace BridgeData

open ArithmeticModel ArithmeticBandGeometry
open Erdos390.Full.PaperStatisticNorm
open Erdos390.Full.PaperStatisticNorm.BridgeData

noncomputable section

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]
  (B : BridgeData Head Band)













/-! ## Dimension-free pointwise bounds -/















/-- Literal natural-coordinate feasibility from the paper effective box and
the two proved `O(1/L)` ledgers.  Unlike the earlier Euclidean corollary, its
constant does not grow with the number of prime bands. -/
theorem ambientCombinedWeight_mem_Icc_of_paperEffectiveSize
    [Nonempty Head]
    {C a Cfixed Cactive : ℝ}
    (hC : 1 ≤ C) (hW : 1 < B.sampleData.W)
    (hhi : ∀ sigma, B.sampleData.hi sigma ≤
      physicalBound C B.sampleData.n)
    (hsep : B.sampleData.HeadPatternsSeparated)
    (frozenWeight : ℕ → ℝ)
    (hfrozenFeasible : ∀ x, frozenWeight x ∈ Set.Icc (0 : ℝ) 1)
    (xi : B.ParamSpace) (hxi : B.paperEffectiveSize xi ≤ a)
    (hfrozen : ∀ m : B.sampleData.Sample,
      frozenWeight (B.sampleData.value m) ≤ Cfixed / B.L)
    (hactive : ∀ m : B.sampleData.Sample,
      B.baseline.baseWeight m ≤ Cactive / B.L)
    (hlarge : Cfixed +
      Real.exp (2 *
        ((valuationLogCoefficient C B.sampleData.W +
          B.nuisanceStatisticCoefficient C) * a)) * Cactive ≤ B.L) :
    ∀ x : ℕ,
      B.ambientCombinedWeight frozenWeight xi x ∈ Set.Icc (0 : ℝ) 1 := by
  let R := (valuationLogCoefficient C B.sampleData.W +
    B.nuisanceStatisticCoefficient C) * a
  apply B.ambientCombinedWeight_mem_Icc_of_effectiveScoreBound
    hsep frozenWeight hfrozenFeasible xi R
      (B.effectiveScoreBound_of_paperEffectiveSize hC hW hhi xi hxi)
  exact B.combinedBaselineSlack_of_div_log_bounds frozenWeight
    Cfixed Cactive R hfrozen hactive (by simpa only [R] using hlarge)

end

end BridgeData
end Erdos390.Full.PaperBridgeFit

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

/-- The first-stage residual is exactly `S_g - sum_j q_j Omega_j`. -/
theorem postBandPrimeScore_eq_slow_sub_bandRegression
    (q : B.RawBandGauge) (m : B.sampleData.Sample) :
    B.postBandPrimeScore q m =
      B.slowScore m - B.bandRegressionScore q m := by
  rw [B.bandRegressionScore_eq_primeSum q m]
  unfold postBandPrimeScore actualCompensatedCoefficient
    slowScore primeDeviation bandRegressionCoefficient
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  ring







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

/-- Bilinear form of the actual nuisance covariance block. -/
theorem inner_nuisanceCovarianceOperator_bilinear [Nonempty Head]
    (xi : B.ParamSpace) (z a : B.NuisanceSpace) :
    inner ℝ z (B.nuisanceCovarianceOperator xi a) =
      (B.tiltedLaw xi).covariance
        (fun m ↦ inner ℝ z (B.nuisanceStatistic m))
        (fun m ↦ inner ℝ a (B.nuisanceStatistic m)) := by
  have hadjoint :
      inner ℝ z (B.nuisanceCovarianceOperator xi a) =
        inner ℝ (B.nuisanceEmbed z)
          (B.covarianceOperator xi (B.nuisanceEmbed a)) := by
    simpa only [nuisanceCovarianceOperator,
      ContinuousLinearMap.comp_apply] using
      (ContinuousLinearMap.adjoint_inner_right B.nuisanceEmbeddingCLM z
        (B.covarianceOperator xi (B.nuisanceEmbeddingCLM a)))
  rw [hadjoint, B.inner_covarianceOperator]
  congr 1
  · funext m
    rw [B.statistic_eq_combine m,
      B.inner_nuisanceEmbed_combine z (B.nuisanceStatistic m)
        (B.mainStatistic m)]
  · funext m
    rw [B.statistic_eq_combine m,
      B.inner_nuisanceEmbed_combine a (B.nuisanceStatistic m)
        (B.mainStatistic m)]



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





private theorem covariance_sub_right
    {Omega : Type*} [Fintype Omega]
    (mu : FiniteProbability Omega) (F G H : Omega → ℝ) :
    mu.covariance F (fun omega ↦ G omega - H omega) =
      mu.covariance F G - mu.covariance F H := by
  have hfun : (fun omega ↦ G omega - H omega) =
      fun omega ↦ G omega + (-1 : ℝ) * H omega := by
    funext omega
    ring
  rw [hfun, mu.covariance_add_right, mu.covariance_smul_right]
  ring

/-- Exact Schur orthogonality of the actual nuisance residual. -/
theorem nuisanceResidualScore_covariance_zero [Nonempty Head]
    (xi : B.ParamSpace) {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (F : B.sampleData.Sample → ℝ) (z : B.NuisanceSpace) :
    (B.tiltedLaw xi).covariance
        (fun m ↦ inner ℝ z (B.nuisanceStatistic m))
        (B.nuisanceResidualScore xi hgamma hgap F) = 0 := by
  let a := B.nuisanceCoefficientOfScore xi hgamma hgap F
  unfold nuisanceResidualScore
  rw [covariance_sub_right]
  have hfirst := B.inner_nuisanceCovarianceVector xi F z
  have hsecond := B.inner_nuisanceCovarianceOperator_bilinear xi z a
  have hsolve := congrArg (fun v : B.NuisanceSpace ↦ inner ℝ z v)
    (B.nuisanceCoefficientOfScore_solve xi hgamma hgap F)
  change inner ℝ z (B.nuisanceCovarianceOperator xi a) =
    inner ℝ z (B.nuisanceCovarianceVector xi F) at hsolve
  rw [hfirst, hsecond] at hsolve
  exact sub_eq_zero.mpr hsolve.symm





theorem actualCompensatedScore_covariance_nuisance_zero [Nonempty Head]
    (xi : B.ParamSpace) {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (q : B.RawBandGauge) (z : B.NuisanceSpace) :
    (B.tiltedLaw xi).covariance
        (fun m ↦ inner ℝ z (B.nuisanceStatistic m))
        (B.actualCompensatedScore xi hgamma hgap q) = 0 := by
  exact B.nuisanceResidualScore_covariance_zero xi hgamma hgap
    (B.postBandPrimeScore q) z

















end BridgeData

end

end Erdos390.Full.PaperBridgeFit

end

/- Source module: Erdos390.Full.FiniteProbabilityCovarianceCauchySchwarz -/
section


/-!
# Cauchy--Schwarz for a literal finite covariance

The two-stage Schur argument needs Cauchy--Schwarz for the actual finite
tilted law, not an abstract positive-semidefinite assumption.  This file
derives it directly from the mass function of `FiniteProbability`.
-/

open scoped BigOperators

namespace Erdos390.Full.FiniteProbability

noncomputable section

variable {Omega : Type*} [Fintype Omega]

/-- Covariance is the weighted inner product of the two centered functions. -/
theorem covariance_eq_sum_mass_mul_centered
    (mu : FiniteProbability Omega) (F G : Omega → ℝ) :
    mu.covariance F G =
      ∑ omega, mu.mass omega * (F omega - mu.expect F) *
        (G omega - mu.expect G) := by
  unfold covariance
  generalize hEF : mu.expect F = EF
  generalize hEG : mu.expect G = EG
  unfold expect at hEF hEG ⊢
  symm
  calc
    (∑ omega, mu.mass omega * (F omega - EF) * (G omega - EG)) =
        (∑ omega, mu.mass omega * (F omega * G omega)) -
          (∑ omega, mu.mass omega * F omega) * EG -
          EF * (∑ omega, mu.mass omega * G omega) +
          (EF * EG) * (∑ omega, mu.mass omega) := by
      rw [Finset.sum_mul, Finset.mul_sum, Finset.mul_sum]
      rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib,
        ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro omega homega
      ring
    _ = (∑ omega, mu.mass omega * (F omega * G omega)) - EF * EG := by
      rw [mu.mass_sum, ← hEF, ← hEG]
      ring

/-- Squared Cauchy--Schwarz inequality for the exact finite covariance. -/
theorem covariance_sq_le_mul_self
    (mu : FiniteProbability Omega) (F G : Omega → ℝ) :
    mu.covariance F G ^ 2 ≤
      mu.covariance F F * mu.covariance G G := by
  let f : Omega → ℝ := fun omega ↦
    Real.sqrt (mu.mass omega) * (F omega - mu.expect F)
  let g : Omega → ℝ := fun omega ↦
    Real.sqrt (mu.mass omega) * (G omega - mu.expect G)
  have hcross : (∑ omega, f omega * g omega) = mu.covariance F G := by
    rw [mu.covariance_eq_sum_mass_mul_centered]
    apply Finset.sum_congr rfl
    intro omega homega
    dsimp only [f, g]
    have hsqrt : Real.sqrt (mu.mass omega) ^ 2 = mu.mass omega :=
      Real.sq_sqrt (mu.mass_nonneg omega)
    calc
      Real.sqrt (mu.mass omega) * (F omega - mu.expect F) *
          (Real.sqrt (mu.mass omega) * (G omega - mu.expect G)) =
          Real.sqrt (mu.mass omega) ^ 2 *
            (F omega - mu.expect F) * (G omega - mu.expect G) := by ring
      _ = mu.mass omega * (F omega - mu.expect F) *
            (G omega - mu.expect G) := by rw [hsqrt]
  have hleft : (∑ omega, f omega ^ 2) = mu.covariance F F := by
    rw [mu.covariance_eq_sum_mass_mul_centered]
    apply Finset.sum_congr rfl
    intro omega homega
    dsimp only [f]
    have hsqrt : Real.sqrt (mu.mass omega) ^ 2 = mu.mass omega :=
      Real.sq_sqrt (mu.mass_nonneg omega)
    rw [mul_pow, hsqrt]
    ring
  have hright : (∑ omega, g omega ^ 2) = mu.covariance G G := by
    rw [mu.covariance_eq_sum_mass_mul_centered]
    apply Finset.sum_congr rfl
    intro omega homega
    dsimp only [g]
    have hsqrt : Real.sqrt (mu.mass omega) ^ 2 = mu.mass omega :=
      Real.sq_sqrt (mu.mass_nonneg omega)
    rw [mul_pow, hsqrt]
    ring
  have hCS := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ f g
  simpa only [hcross, hleft, hright] using hCS

end

end Erdos390.Full.FiniteProbability

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

/-- The kernel of the exact arithmetic projection is orthogonal to every
raw-gauge vector in the `D` pairing. -/
theorem weighted_sum_eq_zero_of_projectRawBandVector_eq_zero
    [Nonempty Band]
    (x : Band → ℝ) (q : B.RawBandGauge)
    (hx : B.projectRawBandVector x = 0) :
    (∑ j : Band, B.harmonicMass j * q.1 j * x j) = 0 := by
  let mu : ℝ :=
    (∑ k : Band, B.harmonicMass k * B.bandCenter k * x k) /
      sharpWeightTotal B.harmonicMass B.bandCenter
  have hxcoord (j : Band) : x j = B.bandCenter j * mu := by
    have hzero := congrArg (fun v : B.RawBandGauge ↦ v.1 j) hx
    change weightedGaugeProjection B.harmonicMass B.bandCenter x j = 0 at hzero
    unfold weightedGaugeProjection at hzero
    dsimp only [mu]
    linarith
  calc
    (∑ j : Band, B.harmonicMass j * q.1 j * x j) =
        mu * ∑ j : Band,
          rawGaugeWeight B.harmonicMass B.bandCenter j * q.1 j := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      rw [hxcoord j]
      unfold rawGaugeWeight
      ring
    _ = 0 := by
      have hq := q.2
      change (∑ j : Band,
        rawGaugeWeight B.harmonicMass B.bandCenter j * q.1 j) = 0 at hq
      rw [hq, mul_zero]







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













theorem nuisanceResidualScore_sub [Nonempty Head]
    (xi : B.ParamSpace) {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (F G : B.sampleData.Sample → ℝ) :
    B.nuisanceResidualScore xi hgamma hgap (fun m ↦ F m - G m) =
      fun m ↦ B.nuisanceResidualScore xi hgamma hgap F m -
        B.nuisanceResidualScore xi hgamma hgap G m := by
  have hsub : (fun m ↦ F m - G m) =
      fun m ↦ F m + (-1 : ℝ) * G m := by
    funext m
    ring
  rw [hsub, B.nuisanceResidualScore_add xi hgamma hgap,
    B.nuisanceResidualScore_smul xi hgamma hgap]
  funext m
  ring





theorem bandRegressionScore_sub
    (q r : B.RawBandGauge) :
    B.bandRegressionScore (q - r) =
      fun m ↦ B.bandRegressionScore q m - B.bandRegressionScore r m := by
  have hneg : -r = (-1 : ℝ) • r := (neg_one_smul ℝ r).symm
  rw [sub_eq_add_neg, B.bandRegressionScore_add, hneg,
    B.bandRegressionScore_smul]
  funext m
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

/-- The constructed first-stage regression makes the literal normalized
band row of the fully nuisance-projected score vanish after arithmetic gauge
projection. -/
theorem actualBandRegression_projectedResidual_zero
    [Nonempty Head] [Nonempty Band]
    (xi : B.ParamSpace) {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (e : B.RawBandGauge ≃ₗ[ℝ] B.RawBandGauge)
    (he : ∀ q, e q = B.actualBandSchurLinearMap xi hgamma hgap q) :
    B.projectRawBandVector
      (B.normalizedBandCovarianceRow xi
        (B.actualCompensatedScore xi hgamma hgap
          (B.actualBandRegression xi hgamma hgap e))) = 0 := by
  let q := B.actualBandRegression xi hgamma hgap e
  have hnormal := B.actualBandRegression_normalEquation
    xi hgamma hgap e he
  have hpost : B.postBandPrimeScore q =
      fun m ↦ B.slowScore m - B.bandRegressionScore q m := by
    funext m
    exact B.postBandPrimeScore_eq_slow_sub_bandRegression q m
  have hresidual :
      B.actualCompensatedScore xi hgamma hgap q =
        fun m ↦
          B.nuisanceResidualScore xi hgamma hgap B.slowScore m -
          B.nuisanceResidualScore xi hgamma hgap
            (B.bandRegressionScore q) m := by
    unfold actualCompensatedScore
    rw [hpost, B.nuisanceResidualScore_sub xi hgamma hgap]
  rw [hresidual, B.normalizedBandCovarianceRow_sub,
    B.projectRawBandVector_sub]
  change B.actualBandRegressionTarget xi hgamma hgap -
      B.actualBandSchurLinearMap xi hgamma hgap q = 0
  rw [← hnormal]
  exact sub_self _

/-- Exact covariance of a raw gauge score with an arbitrary finite score,
written in the normalized band-row coordinates. -/
theorem covariance_bandRegressionScore_eq_weightedRow [Nonempty Head]
    (xi : B.ParamSpace) (q : B.RawBandGauge)
    (F : B.sampleData.Sample → ℝ) :
    (B.tiltedLaw xi).covariance (B.bandRegressionScore q) F =
      ∑ j : Band, B.harmonicMass j * q.1 j *
        B.normalizedBandCovarianceRow xi F j := by
  unfold bandRegressionScore normalizedBandCovarianceRow
  rw [FiniteProbability.covariance_sum_left]
  apply Finset.sum_congr rfl
  intro j hj
  rw [FiniteProbability.covariance_smul_left]
  have hH := B.harmonicMass_pos j
  field_simp [ne_of_gt hH]

/-- The first-stage normal equation is genuine covariance orthogonality to
every arithmetic gauge score. -/
theorem actualBandRegression_covariance_gauge_zero
    [Nonempty Head] [Nonempty Band]
    (xi : B.ParamSpace) {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (e : B.RawBandGauge ≃ₗ[ℝ] B.RawBandGauge)
    (he : ∀ q, e q = B.actualBandSchurLinearMap xi hgamma hgap q)
    (r : B.RawBandGauge) :
    (B.tiltedLaw xi).covariance (B.bandRegressionScore r)
      (B.actualCompensatedScore xi hgamma hgap
        (B.actualBandRegression xi hgamma hgap e)) = 0 := by
  rw [B.covariance_bandRegressionScore_eq_weightedRow]
  exact B.weighted_sum_eq_zero_of_projectRawBandVector_eq_zero
    (B.normalizedBandCovarianceRow xi
      (B.actualCompensatedScore xi hgamma hgap
        (B.actualBandRegression xi hgamma hgap e))) r
    (B.actualBandRegression_projectedResidual_zero
      xi hgamma hgap e he)

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











/-- The fully fitted literal score is orthogonal both to every nuisance
score and to every raw arithmetic-gauge band score. -/
theorem actualTwoStageCompensatedScore_orthogonal
    [Nonempty Head] [Nonempty Band]
    (xi : B.ParamSpace) {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (e : B.RawBandGauge ≃ₗ[ℝ] B.RawBandGauge)
    (he : ∀ q, e q = B.actualBandSchurLinearMap xi hgamma hgap q) :
    (∀ z : B.NuisanceSpace,
      (B.tiltedLaw xi).covariance
        (fun m ↦ inner ℝ z (B.nuisanceStatistic m))
        (B.actualTwoStageCompensatedScore xi hgamma hgap e) = 0) ∧
    ∀ r : B.RawBandGauge,
      (B.tiltedLaw xi).covariance (B.bandRegressionScore r)
        (B.actualTwoStageCompensatedScore xi hgamma hgap e) = 0 := by
  constructor
  · intro z
    exact B.actualCompensatedScore_covariance_nuisance_zero
      xi hgamma hgap (B.actualBandRegression xi hgamma hgap e) z
  · intro r
    exact B.actualBandRegression_covariance_gauge_zero
      xi hgamma hgap e he r

end BridgeData

end

end Erdos390.Full.PaperBridgeFit

end

/- Source module: Erdos390.Full.PaperVectorFieldSchur -/
section


/-!
# Exact Schur decomposition of the paper vector field

The nonlinear ODE uses the literal vector field

`(D M(xi))^{-1} target`.

This file proves, for the actual finite covariance operator and the actual
paper coordinates, that its main and nuisance coordinate blocks are obtained
by the same exact Schur solve used in Lemmas 8.4 and 8.6.  No inverse estimate,
covariance gap, or marked-row estimate is packaged as data here.  The only
positivity hypotheses are the pointwise gaps needed to make the two displayed
finite linear maps invertible.
-/

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

open scoped BigOperators

namespace BridgeData

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]
  (B : BridgeData Head Band)













/-- The two coordinate projections recombine to the original parameter. -/
theorem combine_mainPart_nuisancePart (x : B.ParamSpace) :
    B.combine (B.mainPart x) (B.nuisancePart x) = x := by
  apply (EuclideanSpace.equiv B.Coord ℝ).injective
  funext c
  cases c <;> simp [combine]

/-- The main coordinate projection is the adjoint of the main inclusion. -/
theorem mainEmbedding_adjoint_apply (x : B.ParamSpace) :
    B.mainEmbeddingCLM.adjoint x = B.mainPart x := by
  apply ext_inner_left ℝ
  intro u
  rw [ContinuousLinearMap.adjoint_inner_right]
  have hx := B.combine_mainPart_nuisancePart x
  change inner ℝ (B.mainEmbed u) x = inner ℝ u (B.mainPart x)
  calc
    inner ℝ (B.mainEmbed u) x =
        inner ℝ (B.mainEmbed u)
          (B.combine (B.mainPart x) (B.nuisancePart x)) := by rw [hx]
    _ = inner ℝ u (B.mainPart x) :=
      B.inner_mainEmbed_combine u (B.mainPart x) (B.nuisancePart x)

/-- The nuisance coordinate projection is the adjoint of the nuisance
inclusion. -/
theorem nuisanceEmbedding_adjoint_apply (x : B.ParamSpace) :
    B.nuisanceEmbeddingCLM.adjoint x = B.nuisancePart x := by
  apply ext_inner_left ℝ
  intro z
  rw [ContinuousLinearMap.adjoint_inner_right]
  have hx := B.combine_mainPart_nuisancePart x
  change inner ℝ (B.nuisanceEmbed z) x = inner ℝ z (B.nuisancePart x)
  calc
    inner ℝ (B.nuisanceEmbed z) x =
        inner ℝ (B.nuisanceEmbed z)
          (B.combine (B.mainPart x) (B.nuisancePart x)) := by rw [hx]
    _ = inner ℝ z (B.nuisancePart x) :=
      B.inner_nuisanceEmbed_combine z (B.nuisancePart x) (B.mainPart x)

/-- The normalized covariance operator sends the actual inverse-Jacobian
vector field to the normalized paper target. -/
theorem covarianceOperator_vectorField [Nonempty Head]
    (xi : B.ParamSpace) (Delta : Band → ℝ)
    {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : B.vectorFamily.HasCovarianceGap gamma xi) :
    B.covarianceOperator xi
        (B.vectorFamily.vectorField (B.targetVector Delta) xi) =
      B.normalizedTarget Delta := by
  rw [covarianceOperator, ContinuousLinearMap.smul_apply,
    B.vectorFamily.jacobian_vectorField (B.targetVector Delta) hgamma hgap]
  rfl

/-- Exact nuisance block of the actual covariance equation. -/
theorem nuisancePart_covarianceOperator_combine [Nonempty Head]
    (xi : B.ParamSpace) (u : B.MainSpace) (z : B.NuisanceSpace) :
    B.nuisancePart (B.covarianceOperator xi (B.combine u z)) =
      B.crossCovarianceOperator xi u +
        B.nuisanceCovarianceOperator xi z := by
  rw [← B.nuisanceEmbedding_adjoint_apply]
  change B.nuisanceEmbeddingCLM.adjoint
      (B.covarianceOperator xi (B.mainEmbed u + B.nuisanceEmbed z)) =
    B.nuisanceEmbeddingCLM.adjoint
        (B.covarianceOperator xi (B.mainEmbed u)) +
      B.nuisanceEmbeddingCLM.adjoint
        (B.covarianceOperator xi (B.nuisanceEmbed z))
  simp only [map_add]

/-- Exact main block after inserting the actual nuisance regression. -/
theorem mainPart_covarianceOperator_schurResidual [Nonempty Head]
    (xi : B.ParamSpace) {gammaNuisance : ℝ}
    (hgammaNuisance : 0 < gammaNuisance)
    (hGamma : ∀ z, gammaNuisance * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (u : B.MainSpace) :
    B.mainPart (B.covarianceOperator xi
        (B.schurResidual
          (B.exactNuisanceRegression xi hgammaNuisance hGamma) u)) =
      B.exactSchurCovarianceOperator xi hgammaNuisance hGamma u := by
  rw [← B.mainEmbedding_adjoint_apply]
  simp only [exactSchurCovarianceOperator,
    ContinuousLinearMap.comp_apply, B.exactSchurEmbeddingCLM_apply]



set_option maxHeartbeats 1000000 in
/-- The actual inverse-Jacobian vector field is exactly a Schur residual,
and its main coordinate solves the literal Schur equation. -/
theorem vectorField_eq_schurResidual_and_mainEquation [Nonempty Head]
    (xi : B.ParamSpace) (Delta : Band → ℝ)
    {gammaFull gammaNuisance : ℝ}
    (hgammaFull : 0 < gammaFull)
    (hFull : B.vectorFamily.HasCovarianceGap gammaFull xi)
    (hgammaNuisance : 0 < gammaNuisance)
    (hGamma : ∀ z, gammaNuisance * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z)) :
    let v := B.vectorFamily.vectorField (B.targetVector Delta) xi
    let u := B.mainPart v
    v = B.schurResidual
        (B.exactNuisanceRegression xi hgammaNuisance hGamma) u ∧
      B.exactSchurCovarianceOperator xi hgammaNuisance hGamma u =
        B.mainPart (B.normalizedTarget Delta) := by
  dsimp only
  let v := B.vectorFamily.vectorField (B.targetVector Delta) xi
  let u := B.mainPart v
  let z := B.nuisancePart v
  let R := B.exactNuisanceRegression xi hgammaNuisance hGamma
  have hvDecomp : B.combine u z = v := by
    exact B.combine_mainPart_nuisancePart v
  have hsolve : B.covarianceOperator xi v = B.normalizedTarget Delta :=
    B.covarianceOperator_vectorField xi Delta hgammaFull hFull
  have hnuisance :
      B.crossCovarianceOperator xi u +
        B.nuisanceCovarianceOperator xi z = 0 := by
    have h := congrArg B.nuisancePart hsolve
    rw [← hvDecomp, B.nuisancePart_covarianceOperator_combine,
      B.nuisancePart_normalizedTarget] at h
    exact h
  have hz : z = -R u := by
    apply B.nuisanceCovarianceOperator_injective xi hgammaNuisance hGamma
    have hRu : B.nuisanceCovarianceOperator xi (R u) =
        B.crossCovarianceOperator xi u := by
      exact B.exactNuisanceRegression_solve xi hgammaNuisance hGamma u
    rw [map_neg, hRu]
    rw [eq_neg_iff_add_eq_zero]
    calc
      B.nuisanceCovarianceOperator xi z +
          B.crossCovarianceOperator xi u =
        B.crossCovarianceOperator xi u +
          B.nuisanceCovarianceOperator xi z := add_comm _ _
      _ = 0 := hnuisance
  have hvSchur : v = B.schurResidual R u := by
    rw [← hvDecomp, hz]
    rfl
  refine ⟨?_, ?_⟩
  · simpa only [v, u, R] using hvSchur
  · have hmain := congrArg B.mainPart hsolve
    rw [hvSchur,
      B.mainPart_covarianceOperator_schurResidual] at hmain
    simpa only [u, R] using hmain



/-- A pointwise full covariance gap obtained from the two literal Schur
blocks with a constant which is uniform in the parameter.  The nuisance
regression is the actual finite operator `Gamma_{xi,n}^{-1} B_{xi,n}`;
the only uniformization is the already proved canonical bound for the
cross-covariance operator.  Thus a proposition-level theorem can consume
the nuisance and main/slow gaps separately, without assuming the full
Jacobian gap as an additional analytic input. -/
theorem hasCovarianceGap_of_uniform_exactSchur [Nonempty Head]
    (xi : B.ParamSpace) (gammaMain gammaNuisance : ℝ)
    (hgammaMain : 0 < gammaMain)
    (hgammaNuisance : 0 < gammaNuisance)
    (hGamma : ∀ z, gammaNuisance * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (hSchur : ∀ u, gammaMain * ‖u‖ ^ 2 ≤
      inner ℝ
        (B.schurResidual
          (B.exactNuisanceRegression xi hgammaNuisance hGamma) u)
        (B.covarianceOperator xi
          (B.schurResidual
            (B.exactNuisanceRegression xi hgammaNuisance hGamma) u))) :
    B.vectorFamily.HasCovarianceGap
      (min gammaMain gammaNuisance /
        (3 + 2 * (B.canonicalCrossBound / gammaNuisance) ^ 2)) xi := by
  let R := B.exactNuisanceRegression xi hgammaNuisance hGamma
  have hC : 0 ≤ B.canonicalCrossBound / gammaNuisance :=
    div_nonneg B.canonicalCrossBound_nonneg hgammaNuisance.le
  apply B.hasCovarianceGap_of_schur xi R
    (B.canonicalCrossBound / gammaNuisance)
    gammaMain gammaNuisance hC hgammaMain hgammaNuisance
  · intro u
    dsimp only [R]
    calc
      ‖B.exactNuisanceRegression xi hgammaNuisance hGamma u‖ ≤
          (‖B.crossCovarianceOperator xi‖ / gammaNuisance) * ‖u‖ :=
        B.exactNuisanceRegression_norm_le xi hgammaNuisance hGamma u
      _ ≤ (B.canonicalCrossBound / gammaNuisance) * ‖u‖ := by
        exact mul_le_mul_of_nonneg_right
          (div_le_div_of_nonneg_right
            (B.crossCovarianceOperator_norm_le_canonicalCrossBound xi)
            hgammaNuisance.le)
          (norm_nonneg u)
  · dsimp only [R]
    exact B.exactNuisanceRegression_isRegression
      xi hgammaNuisance hGamma
  · dsimp only [R]
    exact hSchur
  · intro z
    simpa only [nuisanceCovarianceOperator,
      ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.adjoint_inner_right] using hGamma z

end BridgeData

end

end Erdos390.Full.PaperBridgeFit

end

/- Source module: Erdos390.Full.PaperMainRawGaugeCoordinates -/
section


/-!
# Exact identification of the main coordinates with the paper raw gauge

The ODE parameter space stores one coordinate for each concrete gauge-basis
vector and stores `w * lambda` in the slow coordinate.  Lemma 8.6 instead
writes the band coefficient as a vector in the arithmetic hyperplane
`sum_j H_j alpha_j q_j = 0`.  This file identifies these two descriptions
exactly, including the moving low coordinate.  No estimate is used.
-/

open scoped BigOperators

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

open ArithmeticBandGeometry PaperWeightedInverseExport

namespace BridgeData

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]
  (B : BridgeData Head Band)

























/-- Exact effective prime coefficient of a Schur residual. -/
theorem schurResidual_effectivePrimeCoefficient
    (R : B.MainSpace → B.NuisanceSpace) (u : B.MainSpace)
    (p : BandPrime B.sampleData.n B.sampleData.W) :
    B.effectivePrimeCoefficient (B.schurResidual R u) p =
      (B.rawGaugeOfMain u).1 (B.partition.band p) +
        (u MainCoord.slow / B.w) * B.primeDeviation p := by
  rw [B.schurResidual_eq_sub]
  have hadd := B.effectivePrimeCoefficient_add
    (B.mainEmbed u) (-B.nuisanceEmbed (R u)) p
  have hneg := B.effectivePrimeCoefficient_smul (-1)
    (B.nuisanceEmbed (R u)) p
  rw [sub_eq_add_neg, hadd]
  change B.effectivePrimeCoefficient (B.mainEmbed u) p +
      B.effectivePrimeCoefficient (-B.nuisanceEmbed (R u)) p = _
  rw [show -B.nuisanceEmbed (R u) =
      (-1 : ℝ) • B.nuisanceEmbed (R u) by simp,
    hneg, B.nuisanceEmbed_effectivePrimeCoefficient]
  simp





/-- Exact score represented by a main parameter in intrinsic raw-gauge and
stored-slow coordinates.  The factor `1 / w` is visible because the actual
`MainSpace` stores `w * lambda`. -/
theorem vectorScore_mainEmbed_eq_rawGauge_add_slow [Nonempty Head]
    (u : B.MainSpace) (m : B.sampleData.Sample) :
    B.vectorFamily.scalarFamily.score m (B.mainEmbed u) =
      B.bandRegressionScore (B.rawGaugeOfMain u) m +
        (u MainCoord.slow / B.w) * B.slowScore m := by
  rw [B.vectorScore_eq_effectivePrime_add_nuisance]
  have hnuisance : B.nuisanceParameter (B.mainEmbed u) = 0 := by
    apply (EuclideanSpace.equiv (NuisanceCoord B.HeadIndex) ℝ).injective
    funext c
    cases c <;> rfl
  rw [hnuisance, inner_zero_left, add_zero]
  simp_rw [B.mainEmbed_effectivePrimeCoefficient, add_mul]
  rw [Finset.sum_add_distrib]
  have hband := B.bandRegressionScore_eq_primeSum
    (B.rawGaugeOfMain u) m
  unfold bandRegressionCoefficient at hband
  rw [← hband]
  unfold slowScore
  rw [Finset.mul_sum]
  apply congrArg₂ (fun x y : ℝ ↦ x + y) rfl
  apply Finset.sum_congr rfl
  intro p hp
  ring

/-- Exact score of a Schur residual.  This is the literal finite score on
which the band and marked covariance rows act. -/
theorem vectorScore_schurResidual_eq_rawGauge_slow_nuisance
    [Nonempty Head]
    (R : B.MainSpace → B.NuisanceSpace) (u : B.MainSpace)
    (m : B.sampleData.Sample) :
    B.vectorFamily.scalarFamily.score m (B.schurResidual R u) =
      B.bandRegressionScore (B.rawGaugeOfMain u) m +
        (u MainCoord.slow / B.w) * B.slowScore m -
          inner ℝ (R u) (B.nuisanceStatistic m) := by
  rw [B.vectorScore_eq_effectivePrime_add_nuisance,
    B.nuisanceParameter_schurResidual]
  simp_rw [B.schurResidual_effectivePrimeCoefficient, add_mul]
  rw [Finset.sum_add_distrib]
  have hband := B.bandRegressionScore_eq_primeSum
    (B.rawGaugeOfMain u) m
  unfold bandRegressionCoefficient at hband
  rw [← hband]
  unfold slowScore
  rw [inner_neg_left]
  have hslow :
      (∑ p : BandPrime B.sampleData.n B.sampleData.W,
        u MainCoord.slow / B.w * B.primeDeviation p *
          ArithmeticModel.valuation p.1 (B.sampleData.value m)) =
        (u MainCoord.slow / B.w) *
          ∑ p : BandPrime B.sampleData.n B.sampleData.W,
            B.primeDeviation p *
              ArithmeticModel.valuation p.1 (B.sampleData.value m) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p hp
    ring
  rw [hslow]
  ring

end BridgeData

end

end Erdos390.Full.PaperBridgeFit

end

/- Source module: Erdos390.Full.PaperExactSchurRawSlow -/
section


/-!
# Exact raw-gauge/slow form of the finite Schur regression

This file identifies the nuisance regression occurring in the actual Schur
operator with the regression of the literal raw-gauge/slow score.  It is an
exact finite-dimensional identity, and is the first attachment needed to
turn the two-stage estimates of Lemma 8.6 into bounds for the Proposition
8.7 vector field.
-/

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

namespace BridgeData

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]
  (B : BridgeData Head Band)

/-- The exponential-family score of a pure nuisance parameter is exactly
the Euclidean pairing with the literal physical/head statistic. -/
theorem vectorScore_nuisanceEmbed_eq_nuisanceStatistic [Nonempty Head]
    (z : B.NuisanceSpace) (m : B.sampleData.Sample) :
    B.vectorFamily.scalarFamily.score m (B.nuisanceEmbed z) =
      inner ℝ z (B.nuisanceStatistic m) := by
  rw [B.vectorScore_eq_effectivePrime_add_nuisance]
  have hnuisance : B.nuisanceParameter (B.nuisanceEmbed z) = z := by
    apply (EuclideanSpace.equiv (NuisanceCoord B.HeadIndex) ℝ).injective
    funext c
    cases c <;> rfl
  simp_rw [B.nuisanceEmbed_effectivePrimeCoefficient]
  rw [hnuisance]
  simp

/-- The main-to-nuisance covariance block is the covariance vector of the
literal main score. -/
theorem crossCovarianceOperator_eq_nuisanceCovarianceVector_mainScore
    [Nonempty Head]
    (xi : B.ParamSpace) (u : B.MainSpace) :
    B.crossCovarianceOperator xi u =
      B.nuisanceCovarianceVector xi
        (fun m ↦ B.vectorFamily.scalarFamily.score m (B.mainEmbed u)) := by
  apply ext_inner_left ℝ
  intro z
  have hcross :
      inner ℝ z (B.crossCovarianceOperator xi u) =
        inner ℝ (B.nuisanceEmbed z)
          (B.covarianceOperator xi (B.mainEmbed u)) := by
    simpa only [crossCovarianceOperator,
      ContinuousLinearMap.comp_apply] using
      (ContinuousLinearMap.adjoint_inner_right
        B.nuisanceEmbeddingCLM z
        (B.covarianceOperator xi (B.mainEmbeddingCLM u)))
  rw [hcross, B.inner_covarianceOperator,
    B.inner_nuisanceCovarianceVector]
  congr 1
  funext m
  calc
    inner ℝ (B.nuisanceEmbed z) (B.statistic m) =
        inner ℝ (B.statistic m) (B.nuisanceEmbed z) :=
      real_inner_comm _ _
    _ = inner ℝ z (B.nuisanceStatistic m) := by
      simpa only [VectorExponentialFamily.scalarFamily,
        innerSL_apply_apply] using
          B.vectorScore_nuisanceEmbed_eq_nuisanceStatistic z m
  funext m
  simpa only [VectorExponentialFamily.scalarFamily,
    innerSL_apply_apply] using
      (real_inner_comm (B.mainEmbed u) (B.statistic m)).symm

/-- The nuisance component of the exact Schur residual is the actual finite
regression coefficient of the literal main score. -/
theorem exactNuisanceRegression_eq_nuisanceCoefficient_mainScore
    [Nonempty Head]
    (xi : B.ParamSpace) {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (u : B.MainSpace) :
    B.exactNuisanceRegression xi hgamma hgap u =
      B.nuisanceCoefficientOfScore xi hgamma hgap
        (fun m ↦ B.vectorFamily.scalarFamily.score m (B.mainEmbed u)) := by
  apply B.nuisanceCovarianceOperator_injective xi hgamma hgap
  rw [B.exactNuisanceRegression_solve,
    B.nuisanceCoefficientOfScore_solve]
  exact B.crossCovarianceOperator_eq_nuisanceCovarianceVector_mainScore xi u

/-- Consequently the score of the exact Schur residual is literally the
nuisance residual of the raw main score. -/
theorem vectorScore_exactSchurResidual_eq_nuisanceResidual_mainScore
    [Nonempty Head]
    (xi : B.ParamSpace) {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (u : B.MainSpace) :
    (fun m ↦ B.vectorFamily.scalarFamily.score m
      (B.schurResidual (B.exactNuisanceRegression xi hgamma hgap) u)) =
      B.nuisanceResidualScore xi hgamma hgap
        (fun m ↦ B.vectorFamily.scalarFamily.score m (B.mainEmbed u)) := by
  funext m
  rw [B.vectorScore_schurResidual_eq_rawGauge_slow_nuisance]
  unfold nuisanceResidualScore
  rw [← B.exactNuisanceRegression_eq_nuisanceCoefficient_mainScore]
  change _ =
    B.vectorFamily.scalarFamily.score m (B.mainEmbed u) -
      inner ℝ (B.exactNuisanceRegression xi hgamma hgap u)
        (B.nuisanceStatistic m)
  rw [B.vectorScore_mainEmbed_eq_rawGauge_add_slow]

/-- Exact fast/slow score decomposition used by the full block inverse.  If
the raw gauge coordinate has the algebraic form

`q_fast - lambda * q_reg`

and the stored slow coordinate is `w * lambda`, then the Schur-residual
score is the nuisance-projected fast score plus `lambda` times the literal
two-stage compensated score.  This is the finite identity behind the marked
row integration in Proposition 8.7. -/
theorem vectorScore_exactSchurResidual_fast_add_compensated
    [Nonempty Head]
    (xi : B.ParamSpace) {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (u : B.MainSpace) (qFast qReg : B.RawBandGauge) (lambda : ℝ)
    (hq : B.rawGaugeOfMain u = qFast - lambda • qReg)
    (hslow : u MainCoord.slow = B.w * lambda) :
    (fun m ↦ B.vectorFamily.scalarFamily.score m
      (B.schurResidual (B.exactNuisanceRegression xi hgamma hgap) u)) =
      fun m ↦
        B.nuisanceResidualScore xi hgamma hgap
            (B.bandRegressionScore qFast) m +
          lambda * B.actualCompensatedScore xi hgamma hgap qReg m := by
  rw [B.vectorScore_exactSchurResidual_eq_nuisanceResidual_mainScore]
  have hinput :
      (fun m ↦ B.vectorFamily.scalarFamily.score m (B.mainEmbed u)) =
        fun m ↦ B.bandRegressionScore qFast m +
          lambda * B.postBandPrimeScore qReg m := by
    funext m
    rw [B.vectorScore_mainEmbed_eq_rawGauge_add_slow, hq,
      B.bandRegressionScore_sub,
      B.bandRegressionScore_smul, hslow,
      mul_div_cancel_left₀ lambda (ne_of_gt B.w_pos),
      B.postBandPrimeScore_eq_slow_sub_bandRegression]
    ring
  rw [hinput, B.nuisanceResidualScore_add,
    B.nuisanceResidualScore_smul]
  rfl

end BridgeData

end

end Erdos390.Full.PaperBridgeFit

end

/- Source module: Erdos390.Full.PaperWeightedGaugeDGeometry -/
section


/-!
# Finite `D`-pairing geometry in the paper's sharp gauge

These are the exact finite weighted inequalities used when covariance
Cauchy--Schwarz is combined with the sharp-gauge inverse.  No continuum
centre or limiting weight is introduced.
-/

open scoped BigOperators

noncomputable section

namespace Erdos390.Full.PaperWeightedInverseExport

open MovingLowGaugeTransfer

variable {Band : Type*} [Fintype Band] [Nonempty Band]





theorem rawDLowerWeight_le (H alpha : Band → ℝ) (j : Band) :
    rawDLowerWeight H alpha ≤ H j * alpha j ^ 2 := by
  classical
  unfold rawDLowerWeight
  exact Finset.min'_le _ _ (Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩)

/-- Positivity of the literal finite minimum. -/
theorem rawDLowerWeight_pos
    (H alpha : Band → ℝ) (hH : ∀ j, 0 < H j)
    (hAlpha : ∀ j, alpha j ≠ 0) :
    0 < rawDLowerWeight H alpha := by
  classical
  let s : Finset ℝ := Finset.univ.image (fun j ↦ H j * alpha j ^ 2)
  have hs : s.Nonempty := Finset.univ_nonempty.image _
  have hmem := Finset.min'_mem s hs
  obtain ⟨j, hj, hEq⟩ := Finset.mem_image.mp hmem
  have hAlphaSq : 0 < alpha j ^ 2 := sq_pos_of_ne_zero (hAlpha j)
  unfold rawDLowerWeight
  change 0 < s.min' hs
  rw [← hEq]
  exact mul_pos (hH j) hAlphaSq

/-- The `D` quadratic form controls the paper's sharp supremum norm by the
smallest literal sharp diagonal weight. -/
theorem rawDLowerWeight_mul_paperSharpNorm_sq_le
    (H alpha : Band → ℝ) (hH : ∀ j, 0 < H j)
    (hAlpha : ∀ j, alpha j ≠ 0)
    (q : RawGaugeSpace H alpha) :
    rawDLowerWeight H alpha *
        paperSharpNorm H alpha hAlpha q ^ 2 ≤
      rawDPairing H alpha q q := by
  classical
  let f : Band → ℝ := fun j ↦ q.1 j / alpha j
  obtain ⟨j, hj, hsup⟩ :=
    Finset.exists_mem_eq_sup' Finset.univ_nonempty
      (fun k : Band ↦ ‖f k‖₊)
  have hnorm : paperSharpNorm H alpha hAlpha q = |f j| := by
    rw [paperSharpNorm_eq_piNorm]
    change ‖f‖ = |f j|
    rw [Pi.norm_def, ← Finset.sup'_eq_sup Finset.univ_nonempty, hsup]
    simp only [coe_nnnorm, Real.norm_eq_abs]
  have hmin0 : 0 ≤ rawDLowerWeight H alpha :=
    (rawDLowerWeight_pos H alpha hH hAlpha).le
  have hterm :
      rawDLowerWeight H alpha * |f j| ^ 2 ≤ H j * q.1 j ^ 2 := by
    calc
      rawDLowerWeight H alpha * |f j| ^ 2 ≤
          (H j * alpha j ^ 2) * |f j| ^ 2 :=
        mul_le_mul_of_nonneg_right (rawDLowerWeight_le H alpha j)
          (sq_nonneg _)
      _ = H j * q.1 j ^ 2 := by
        dsimp only [f]
        rw [sq_abs]
        field_simp [hAlpha j]
  rw [hnorm]
  exact hterm.trans (by
    unfold rawDPairing
    simpa only [pow_two, mul_assoc] using
      (Finset.single_le_sum
        (fun k hk ↦ mul_nonneg (hH k).le (sq_nonneg (q.1 k)))
        (Finset.mem_univ j)))

/-- Absolute `D` pairing is bounded by the total sharp weight times the two
paper-sharp norms. -/
theorem abs_rawDPairing_le_sharpWeightTotal_mul
    (H alpha : Band → ℝ) (hH : ∀ j, 0 < H j)
    (hAlpha : ∀ j, alpha j ≠ 0)
    (q r : RawGaugeSpace H alpha) :
    |rawDPairing H alpha q r| ≤
      sharpWeightTotal H alpha * paperSharpNorm H alpha hAlpha q *
        paperSharpNorm H alpha hAlpha r := by
  have hq (j : Band) :
      |q.1 j / alpha j| ≤ paperSharpNorm H alpha hAlpha q := by
    rw [paperSharpNorm_eq_piNorm]
    simpa only [Real.norm_eq_abs] using
      ((pi_norm_le_iff_of_nonempty
        (fun k ↦ q.1 k / alpha k)).mp le_rfl j)
  have hr (j : Band) :
      |r.1 j / alpha j| ≤ paperSharpNorm H alpha hAlpha r := by
    rw [paperSharpNorm_eq_piNorm]
    simpa only [Real.norm_eq_abs] using
      ((pi_norm_le_iff_of_nonempty
        (fun k ↦ r.1 k / alpha k)).mp le_rfl j)
  have hq0 : 0 ≤ paperSharpNorm H alpha hAlpha q := norm_nonneg _
  have hr0 : 0 ≤ paperSharpNorm H alpha hAlpha r := norm_nonneg _
  calc
    |rawDPairing H alpha q r| ≤
        ∑ j, |H j * q.1 j * r.1 j| := by
      unfold rawDPairing
      exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j, (H j * alpha j ^ 2) *
          paperSharpNorm H alpha hAlpha q *
            paperSharpNorm H alpha hAlpha r := by
      apply Finset.sum_le_sum
      intro j hj
      have hweight : 0 ≤ H j * alpha j ^ 2 :=
        mul_nonneg (hH j).le (sq_nonneg _)
      have hratio :
          |q.1 j / alpha j| * |r.1 j / alpha j| ≤
            paperSharpNorm H alpha hAlpha q *
              paperSharpNorm H alpha hAlpha r :=
        mul_le_mul (hq j) (hr j) (abs_nonneg _) hq0
      calc
        |H j * q.1 j * r.1 j| =
            (H j * alpha j ^ 2) *
              (|q.1 j / alpha j| * |r.1 j / alpha j|) := by
          rw [abs_mul, abs_mul, abs_of_pos (hH j), abs_div, abs_div,
            ← sq_abs]
          field_simp [abs_ne_zero.mpr (hAlpha j)]
        _ ≤ (H j * alpha j ^ 2) *
              (paperSharpNorm H alpha hAlpha q *
                paperSharpNorm H alpha hAlpha r) :=
          mul_le_mul_of_nonneg_left hratio hweight
        _ = (H j * alpha j ^ 2) *
              paperSharpNorm H alpha hAlpha q *
                paperSharpNorm H alpha hAlpha r := by ring
    _ = sharpWeightTotal H alpha * paperSharpNorm H alpha hAlpha q *
          paperSharpNorm H alpha hAlpha r := by
      unfold sharpWeightTotal sharpWeight
      rw [← Finset.sum_mul, ← Finset.sum_mul]

end Erdos390.Full.PaperWeightedInverseExport

end

/- Source module: Erdos390.Full.PaperExactSchurTwoStageQuadratic -/
section


/-!
# Exact quadratic attachment for the two-stage Schur regression

This file supplies the finite-dimensional algebra between the arithmetic
band inverse of Lemma 8.4 and the compensated slow score of Lemma 8.6.  In
particular, no limiting operator, mesh estimate, or covariance lower bound
is assumed here.

The first identity identifies the quadratic form of the literal projected
band Schur operator with the variance of the nuisance-residual band score.
The second identity proves that the fast band residual and the fitted slow
score are exactly covariance-orthogonal.  Combining them gives the exact
fast/slow quadratic decomposition of the main Schur block used in
Proposition 8.7.
-/

open scoped BigOperators

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

open ArithmeticModel ArithmeticBandGeometry
open PaperWeightedInverseExport MovingLowGaugeTransfer

namespace BridgeData

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]
  (B : BridgeData Head Band)



/-- Projecting a normalized band row does not change its pairing with an
arithmetic-gauge vector.  This is the exact finite arithmetic centering
identity; in particular it does not replace the arithmetic centres by
continuum cell centres. -/
theorem weighted_pairing_projectRawBandVector
    [Nonempty Band]
    (q : B.RawBandGauge) (x : Band → ℝ) :
    (∑ j : Band, B.harmonicMass j * q.1 j *
        (B.projectRawBandVector x).1 j) =
      ∑ j : Band, B.harmonicMass j * q.1 j * x j := by
  let mu : ℝ :=
    (∑ k : Band, B.harmonicMass k * B.bandCenter k * x k) /
      sharpWeightTotal B.harmonicMass B.bandCenter
  have hcoord (j : Band) :
      (B.projectRawBandVector x).1 j = x j - B.bandCenter j * mu := by
    change weightedGaugeProjection B.harmonicMass B.bandCenter x j = _
    unfold weightedGaugeProjection
    rfl
  rw [show (∑ j : Band, B.harmonicMass j * q.1 j *
      (B.projectRawBandVector x).1 j) =
      (∑ j : Band, B.harmonicMass j * q.1 j * x j) -
        mu * (∑ j : Band,
          rawGaugeWeight B.harmonicMass B.bandCenter j * q.1 j) by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    rw [hcoord]
    unfold rawGaugeWeight
    ring]
  have hq := q.2
  change (∑ j : Band,
    rawGaugeWeight B.harmonicMass B.bandCenter j * q.1 j) = 0 at hq
  rw [hq, mul_zero, sub_zero]

/-- The quadratic form of the literal arithmetic band Schur map is exactly
the variance of the band score after the actual finite nuisance regression.
This is an equality at finite `n`, in the arithmetic `D`-pairing. -/
theorem actualBandSchur_quadratic_eq_residualVariance
    [Nonempty Head] [Nonempty Band]
    (xi : B.ParamSpace) {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (q : B.RawBandGauge) :
    (∑ j : Band, B.harmonicMass j * q.1 j *
        (B.actualBandSchurLinearMap xi hgamma hgap q).1 j) =
      (B.tiltedLaw xi).covariance
        (B.nuisanceResidualScore xi hgamma hgap
          (B.bandRegressionScore q))
        (B.nuisanceResidualScore xi hgamma hgap
          (B.bandRegressionScore q)) := by
  let F : B.sampleData.Sample → ℝ := B.bandRegressionScore q
  let a : B.NuisanceSpace :=
    B.nuisanceCoefficientOfScore xi hgamma hgap F
  let Z : B.sampleData.Sample → ℝ :=
    fun m ↦ inner ℝ a (B.nuisanceStatistic m)
  let R : B.sampleData.Sample → ℝ :=
    B.nuisanceResidualScore xi hgamma hgap F
  have hF : F = fun m ↦ R m + Z m := by
    funext m
    simp only [F, R, Z, a]
    unfold nuisanceResidualScore
    ring
  have horth : (B.tiltedLaw xi).covariance Z R = 0 := by
    simpa only [Z, R, a] using
      B.nuisanceResidualScore_covariance_zero
        xi hgamma hgap F a
  calc
    (∑ j : Band, B.harmonicMass j * q.1 j *
        (B.actualBandSchurLinearMap xi hgamma hgap q).1 j) =
        ∑ j : Band, B.harmonicMass j * q.1 j *
          B.normalizedBandCovarianceRow xi R j := by
      exact B.weighted_pairing_projectRawBandVector q
        (B.normalizedBandCovarianceRow xi R)
    _ = (B.tiltedLaw xi).covariance F R := by
      exact (B.covariance_bandRegressionScore_eq_weightedRow
        xi q R).symm
    _ = (B.tiltedLaw xi).covariance R R := by
      rw [hF, FiniteProbability.covariance_add_left, horth, add_zero]

/-- Bilinear form of the preceding identity.  It is needed for the
covariance Cauchy--Schwarz conversion from a sharp inverse bound to a
positive `D`-quadratic gap. -/
theorem actualBandSchur_bilinear_eq_residualCovariance
    [Nonempty Head] [Nonempty Band]
    (xi : B.ParamSpace) {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (q r : B.RawBandGauge) :
    B.bandDPairing q (B.actualBandSchurLinearMap xi hgamma hgap r) =
      (B.tiltedLaw xi).covariance
        (B.nuisanceResidualScore xi hgamma hgap
          (B.bandRegressionScore q))
        (B.nuisanceResidualScore xi hgamma hgap
          (B.bandRegressionScore r)) := by
  let Fq : B.sampleData.Sample → ℝ := B.bandRegressionScore q
  let Fr : B.sampleData.Sample → ℝ := B.bandRegressionScore r
  let aq : B.NuisanceSpace :=
    B.nuisanceCoefficientOfScore xi hgamma hgap Fq
  let Zq : B.sampleData.Sample → ℝ :=
    fun m ↦ inner ℝ aq (B.nuisanceStatistic m)
  let Rq : B.sampleData.Sample → ℝ :=
    B.nuisanceResidualScore xi hgamma hgap Fq
  let Rr : B.sampleData.Sample → ℝ :=
    B.nuisanceResidualScore xi hgamma hgap Fr
  have hFq : Fq = fun m ↦ Rq m + Zq m := by
    funext m
    simp only [Fq, Rq, Zq, aq]
    unfold nuisanceResidualScore
    ring
  have horth : (B.tiltedLaw xi).covariance Zq Rr = 0 := by
    simpa only [Zq, Rr, aq] using
      B.nuisanceResidualScore_covariance_zero
        xi hgamma hgap Fr aq
  calc
    B.bandDPairing q (B.actualBandSchurLinearMap xi hgamma hgap r) =
        ∑ j : Band, B.harmonicMass j * q.1 j *
          B.normalizedBandCovarianceRow xi Rr j := by
      unfold bandDPairing
      exact B.weighted_pairing_projectRawBandVector q
        (B.normalizedBandCovarianceRow xi Rr)
    _ = (B.tiltedLaw xi).covariance Fq Rr := by
      exact (B.covariance_bandRegressionScore_eq_weightedRow
        xi q Rr).symm
    _ = (B.tiltedLaw xi).covariance Rq Rr := by
      rw [hFq, FiniteProbability.covariance_add_left, horth, add_zero]

/-- Covariance Cauchy--Schwarz converts an inverse bound for the literal
band Schur map into a quantitative `D`-quadratic estimate.  The two displayed
`D` comparisons are pure finite weighted-gauge geometry; they are kept as
arguments here so this analytic attachment cannot silently change norms. -/
theorem actualBandSchur_quadratic_mul_bound_of_inverse
    [Nonempty Head] [Nonempty Band]
    (xi : B.ParamSpace) {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (e : B.RawBandGauge ≃ₗ[ℝ] B.RawBandGauge)
    (he : ∀ q, e q = B.actualBandSchurLinearMap xi hgamma hgap q)
    {Cinv Dlower Dupper : ℝ}
    (hCinv : 0 ≤ Cinv) (hDlower : 0 ≤ Dlower)
    (hDupper : 0 ≤ Dupper)
    (hinv : ∀ v,
      paperSharpNorm B.harmonicMass B.bandCenter
          (B.partition.center_ne_zero B.n_gt_one) (e.symm v) ≤
        Cinv * paperSharpNorm B.harmonicMass B.bandCenter
          (B.partition.center_ne_zero B.n_gt_one) v)
    (hDdiag : ∀ v,
      Dlower *
          paperSharpNorm B.harmonicMass B.bandCenter
            (B.partition.center_ne_zero B.n_gt_one) v ^ 2 ≤
        B.bandDPairing v v)
    (hDbilin : ∀ v u,
      |B.bandDPairing v u| ≤
        Dupper *
          paperSharpNorm B.harmonicMass B.bandCenter
            (B.partition.center_ne_zero B.n_gt_one) v *
          paperSharpNorm B.harmonicMass B.bandCenter
            (B.partition.center_ne_zero B.n_gt_one) u)
    (q : B.RawBandGauge) :
    Dlower ^ 2 *
        paperSharpNorm B.harmonicMass B.bandCenter
          (B.partition.center_ne_zero B.n_gt_one) q ^ 2 ≤
      (Dupper * Cinv) *
        (B.tiltedLaw xi).covariance
          (B.nuisanceResidualScore xi hgamma hgap
            (B.bandRegressionScore q))
          (B.nuisanceResidualScore xi hgamma hgap
            (B.bandRegressionScore q)) := by
  let S : B.RawBandGauge → ℝ := fun v ↦
    paperSharpNorm B.harmonicMass B.bandCenter
      (B.partition.center_ne_zero B.n_gt_one) v
  let R : B.RawBandGauge → B.sampleData.Sample → ℝ := fun v ↦
    B.nuisanceResidualScore xi hgamma hgap (B.bandRegressionScore v)
  let Q : B.RawBandGauge → ℝ := fun v ↦
    (B.tiltedLaw xi).covariance (R v) (R v)
  let y : B.RawBandGauge := e.symm q
  have hey : B.actualBandSchurLinearMap xi hgamma hgap y = q := by
    rw [← he, LinearEquiv.apply_symm_apply]
  have hDqq : Dlower * S q ^ 2 ≤ B.bandDPairing q q := hDdiag q
  have hDqq0 : 0 ≤ B.bandDPairing q q :=
    (mul_nonneg hDlower (sq_nonneg _)).trans hDqq
  have hcross : B.bandDPairing q q =
      (B.tiltedLaw xi).covariance (R q) (R y) := by
    calc
      B.bandDPairing q q =
          B.bandDPairing q
            (B.actualBandSchurLinearMap xi hgamma hgap y) := by rw [hey]
      _ = (B.tiltedLaw xi).covariance (R q) (R y) :=
        B.actualBandSchur_bilinear_eq_residualCovariance
          xi hgamma hgap q y
  have hcs : (B.bandDPairing q q) ^ 2 ≤ Q q * Q y := by
    rw [hcross]
    exact (B.tiltedLaw xi).covariance_sq_le_mul_self (R q) (R y)
  have hQy : Q y = B.bandDPairing y q := by
    calc
      Q y = B.bandDPairing y
          (B.actualBandSchurLinearMap xi hgamma hgap y) :=
        (B.actualBandSchur_quadratic_eq_residualVariance
          xi hgamma hgap y).symm
      _ = B.bandDPairing y q := by rw [hey]
  have hSy : S y ≤ Cinv * S q := hinv q
  have hS0 (v : B.RawBandGauge) : 0 ≤ S v := by
    exact norm_nonneg _
  have hQy0 : 0 ≤ Q y :=
    (B.tiltedLaw xi).covariance_self_nonneg (R y)
  have hQq0 : 0 ≤ Q q :=
    (B.tiltedLaw xi).covariance_self_nonneg (R q)
  have hQyUpper : Q y ≤ Dupper * Cinv * S q ^ 2 := by
    rw [hQy]
    calc
      B.bandDPairing y q ≤ |B.bandDPairing y q| := le_abs_self _
      _ ≤ Dupper * S y * S q := hDbilin y q
      _ ≤ Dupper * (Cinv * S q) * S q := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hSy hDupper) (hS0 q)
      _ = Dupper * Cinv * S q ^ 2 := by ring
  by_cases hSq : S q = 0
  · change Dlower ^ 2 * S q ^ 2 ≤ (Dupper * Cinv) * Q q
    rw [hSq]
    norm_num
    exact mul_nonneg (mul_nonneg hDupper hCinv) hQq0
  · have hSqPos : 0 < S q := lt_of_le_of_ne (hS0 q) (Ne.symm hSq)
    have hDsq : (Dlower * S q ^ 2) ^ 2 ≤
        (B.bandDPairing q q) ^ 2 := by
      exact sq_le_sq₀ (mul_nonneg hDlower (sq_nonneg _)) hDqq0 |>.2 hDqq
    have hmaster : (Dlower * S q ^ 2) ^ 2 ≤
        Q q * (Dupper * Cinv * S q ^ 2) := by
      exact hDsq.trans (hcs.trans
        (mul_le_mul_of_nonneg_left hQyUpper hQq0))
    nlinarith [sq_pos_of_pos hSqPos]

/-- Division form of the preceding quantitative gap. -/
theorem actualBandSchur_quadratic_lower_of_inverse
    [Nonempty Head] [Nonempty Band]
    (xi : B.ParamSpace) {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (e : B.RawBandGauge ≃ₗ[ℝ] B.RawBandGauge)
    (he : ∀ q, e q = B.actualBandSchurLinearMap xi hgamma hgap q)
    {Cinv Dlower Dupper : ℝ}
    (hCinv : 0 < Cinv) (hDlower : 0 ≤ Dlower)
    (hDupper : 0 < Dupper)
    (hinv : ∀ v,
      paperSharpNorm B.harmonicMass B.bandCenter
          (B.partition.center_ne_zero B.n_gt_one) (e.symm v) ≤
        Cinv * paperSharpNorm B.harmonicMass B.bandCenter
          (B.partition.center_ne_zero B.n_gt_one) v)
    (hDdiag : ∀ v,
      Dlower *
          paperSharpNorm B.harmonicMass B.bandCenter
            (B.partition.center_ne_zero B.n_gt_one) v ^ 2 ≤
        B.bandDPairing v v)
    (hDbilin : ∀ v u,
      |B.bandDPairing v u| ≤
        Dupper *
          paperSharpNorm B.harmonicMass B.bandCenter
            (B.partition.center_ne_zero B.n_gt_one) v *
          paperSharpNorm B.harmonicMass B.bandCenter
            (B.partition.center_ne_zero B.n_gt_one) u)
    (q : B.RawBandGauge) :
    (Dlower ^ 2 / (Dupper * Cinv)) *
        paperSharpNorm B.harmonicMass B.bandCenter
          (B.partition.center_ne_zero B.n_gt_one) q ^ 2 ≤
      (B.tiltedLaw xi).covariance
        (B.nuisanceResidualScore xi hgamma hgap
          (B.bandRegressionScore q))
        (B.nuisanceResidualScore xi hgamma hgap
          (B.bandRegressionScore q)) := by
  have hmul := B.actualBandSchur_quadratic_mul_bound_of_inverse
    xi hgamma hgap e he hCinv.le hDlower hDupper.le
    hinv hDdiag hDbilin q
  have hden : 0 < Dupper * Cinv := mul_pos hDupper hCinv
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ hden).2
  simpa only [mul_comm, mul_left_comm, mul_assoc] using hmul

/-- Literal arithmetic specialization of the inverse-to-quadratic theorem.
The two `D` constants and both weighted inequalities are now conclusions of
the finite positive harmonic masses and centres. -/
theorem actualBandSchur_quadratic_lower_of_inverse_arithmetic
    [Nonempty Head] [Nonempty Band]
    (xi : B.ParamSpace) {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (e : B.RawBandGauge ≃ₗ[ℝ] B.RawBandGauge)
    (he : ∀ q, e q = B.actualBandSchurLinearMap xi hgamma hgap q)
    {Cinv : ℝ} (hCinv : 0 < Cinv)
    (hinv : ∀ v,
      paperSharpNorm B.harmonicMass B.bandCenter
          (B.partition.center_ne_zero B.n_gt_one) (e.symm v) ≤
        Cinv * paperSharpNorm B.harmonicMass B.bandCenter
          (B.partition.center_ne_zero B.n_gt_one) v)
    (q : B.RawBandGauge) :
    (rawDLowerWeight B.harmonicMass B.bandCenter ^ 2 /
        (sharpWeightTotal B.harmonicMass B.bandCenter * Cinv)) *
        paperSharpNorm B.harmonicMass B.bandCenter
          (B.partition.center_ne_zero B.n_gt_one) q ^ 2 ≤
      (B.tiltedLaw xi).covariance
        (B.nuisanceResidualScore xi hgamma hgap
          (B.bandRegressionScore q))
        (B.nuisanceResidualScore xi hgamma hgap
          (B.bandRegressionScore q)) := by
  apply B.actualBandSchur_quadratic_lower_of_inverse
    xi hgamma hgap e he hCinv
    (rawDLowerWeight_pos B.harmonicMass B.bandCenter
      B.harmonicMass_pos
      (B.partition.center_ne_zero B.n_gt_one)).le
    B.sharpBandWeightTotal_pos
    hinv
  · intro v
    simpa only [bandDPairing, rawDPairing] using
      rawDLowerWeight_mul_paperSharpNorm_sq_le
        B.harmonicMass B.bandCenter B.harmonicMass_pos
        (B.partition.center_ne_zero B.n_gt_one) v
  · intro v u
    simpa only [bandDPairing, rawDPairing] using
      abs_rawDPairing_le_sharpWeightTotal_mul
        B.harmonicMass B.bandCenter B.harmonicMass_pos
        (B.partition.center_ne_zero B.n_gt_one) v u

/-- The nuisance-residual fast band score is exactly orthogonal to the
two-stage compensated slow score.  Both the band normal equation and the
nuisance normal equation are used; neither orthogonality is postulated. -/
theorem fastResidual_covariance_twoStageCompensated_eq_zero
    [Nonempty Head] [Nonempty Band]
    (xi : B.ParamSpace) {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (e : B.RawBandGauge ≃ₗ[ℝ] B.RawBandGauge)
    (he : ∀ q, e q = B.actualBandSchurLinearMap xi hgamma hgap q)
    (qFast : B.RawBandGauge) :
    (B.tiltedLaw xi).covariance
        (B.nuisanceResidualScore xi hgamma hgap
          (B.bandRegressionScore qFast))
        (B.actualTwoStageCompensatedScore xi hgamma hgap e) = 0 := by
  let a : B.NuisanceSpace := B.nuisanceCoefficientOfScore xi hgamma hgap
    (B.bandRegressionScore qFast)
  have hband : (B.tiltedLaw xi).covariance
      (B.bandRegressionScore qFast)
      (B.actualTwoStageCompensatedScore xi hgamma hgap e) = 0 :=
    (B.actualTwoStageCompensatedScore_orthogonal
      xi hgamma hgap e he).2 qFast
  have hnuisance : (B.tiltedLaw xi).covariance
      (fun m ↦ inner ℝ a (B.nuisanceStatistic m))
      (B.actualTwoStageCompensatedScore xi hgamma hgap e) = 0 :=
    (B.actualTwoStageCompensatedScore_orthogonal
      xi hgamma hgap e he).1 a
  have hresidual :
      B.nuisanceResidualScore xi hgamma hgap
          (B.bandRegressionScore qFast) =
        fun m ↦ B.bandRegressionScore qFast m -
          inner ℝ a (B.nuisanceStatistic m) := by
    rfl
  rw [hresidual]
  have hsub : (fun m ↦ B.bandRegressionScore qFast m -
      inner ℝ a (B.nuisanceStatistic m)) =
      fun m ↦ B.bandRegressionScore qFast m +
        (-1 : ℝ) * inner ℝ a (B.nuisanceStatistic m) := by
    funext m
    ring
  rw [hsub, FiniteProbability.covariance_add_left,
    FiniteProbability.covariance_smul_left, hband, hnuisance]
  ring

/-- Exact Pythagorean identity for the finite two-stage regression. -/
theorem covariance_fast_add_slow_twoStage
    [Nonempty Head] [Nonempty Band]
    (xi : B.ParamSpace) {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (e : B.RawBandGauge ≃ₗ[ℝ] B.RawBandGauge)
    (he : ∀ q, e q = B.actualBandSchurLinearMap xi hgamma hgap q)
    (qFast : B.RawBandGauge) (lambda : ℝ) :
    (B.tiltedLaw xi).covariance
        (fun m ↦
          B.nuisanceResidualScore xi hgamma hgap
              (B.bandRegressionScore qFast) m +
            lambda * B.actualTwoStageCompensatedScore
              xi hgamma hgap e m)
        (fun m ↦
          B.nuisanceResidualScore xi hgamma hgap
              (B.bandRegressionScore qFast) m +
            lambda * B.actualTwoStageCompensatedScore
              xi hgamma hgap e m) =
      (B.tiltedLaw xi).covariance
          (B.nuisanceResidualScore xi hgamma hgap
            (B.bandRegressionScore qFast))
          (B.nuisanceResidualScore xi hgamma hgap
            (B.bandRegressionScore qFast)) +
        lambda ^ 2 * (B.tiltedLaw xi).covariance
          (B.actualTwoStageCompensatedScore xi hgamma hgap e)
          (B.actualTwoStageCompensatedScore xi hgamma hgap e) := by
  let F := B.nuisanceResidualScore xi hgamma hgap
    (B.bandRegressionScore qFast)
  let C := B.actualTwoStageCompensatedScore xi hgamma hgap e
  have hFC : (B.tiltedLaw xi).covariance F C = 0 := by
    exact B.fastResidual_covariance_twoStageCompensated_eq_zero
      xi hgamma hgap e he qFast
  have hCF : (B.tiltedLaw xi).covariance C F = 0 := by
    rw [(B.tiltedLaw xi).covariance_comm]
    exact hFC
  rw [FiniteProbability.covariance_add_left,
    FiniteProbability.covariance_add_right,
    FiniteProbability.covariance_add_right,
    FiniteProbability.covariance_smul_left,
    FiniteProbability.covariance_smul_right,
    FiniteProbability.covariance_smul_right,
    hFC, hCF]
  rw [FiniteProbability.covariance_smul_left]
  ring

/-- Exact quadratic decomposition of the actual main Schur block.  For the
canonical first-stage regression `qReg`, every main vector is written with
raw coordinate `qFast - lambda qReg` and stored slow coordinate
`w * lambda`.  The resulting Schur quadratic form is the sum of the fast
band residual variance and `lambda^2` times the fully compensated slow
variance. -/
theorem exactSchur_quadratic_eq_fast_add_slow_twoStage
    [Nonempty Head] [Nonempty Band]
    (xi : B.ParamSpace) {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (e : B.RawBandGauge ≃ₗ[ℝ] B.RawBandGauge)
    (he : ∀ q, e q = B.actualBandSchurLinearMap xi hgamma hgap q)
    (u : B.MainSpace) (qFast : B.RawBandGauge) (lambda : ℝ)
    (hq : B.rawGaugeOfMain u = qFast - lambda •
      B.actualBandRegression xi hgamma hgap e)
    (hslow : u MainCoord.slow = B.w * lambda) :
    inner ℝ u (B.exactSchurCovarianceOperator xi hgamma hgap u) =
      (B.tiltedLaw xi).covariance
          (B.nuisanceResidualScore xi hgamma hgap
            (B.bandRegressionScore qFast))
          (B.nuisanceResidualScore xi hgamma hgap
            (B.bandRegressionScore qFast)) +
        lambda ^ 2 * (B.tiltedLaw xi).covariance
          (B.actualTwoStageCompensatedScore xi hgamma hgap e)
          (B.actualTwoStageCompensatedScore xi hgamma hgap e) := by
  rw [B.exactSchurCovarianceOperator_quadratic,
    B.inner_covarianceOperator]
  have hscore := B.vectorScore_exactSchurResidual_fast_add_compensated
    xi hgamma hgap u qFast
      (B.actualBandRegression xi hgamma hgap e) lambda hq hslow
  have hinnerScore :
      (fun m ↦ inner ℝ
        (B.schurResidual (B.exactNuisanceRegression xi hgamma hgap) u)
        (B.statistic m)) =
      fun m ↦ B.vectorFamily.scalarFamily.score m
        (B.schurResidual
          (B.exactNuisanceRegression xi hgamma hgap) u) := by
    funext m
    simp only [VectorExponentialFamily.scalarFamily, innerSL_apply_apply]
    exact real_inner_comm _ _
  rw [hinnerScore, hscore]
  exact B.covariance_fast_add_slow_twoStage
    xi hgamma hgap e he qFast lambda

/-- Deterministic fast/slow coercivity assembly.  The only coordinate input
is the displayed comparison between the concrete Euclidean `MainSpace` norm
and the intrinsic sharp-fast/stored-slow coordinates.  The analytic inputs
are exactly the fast band variance lower bound and the compensated slow
variance lower bound; an undischarged Schur-gap hypothesis is not used. -/
theorem exactSchurGap_of_fastSlow
    [Nonempty Head] [Nonempty Band]
    (xi : B.ParamSpace) {gammaNuisance : ℝ}
    (hgammaNuisance : 0 < gammaNuisance)
    (hGamma : ∀ z, gammaNuisance * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (e : B.RawBandGauge ≃ₗ[ℝ] B.RawBandGauge)
    (he : ∀ q,
      e q = B.actualBandSchurLinearMap
        xi hgammaNuisance hGamma q)
    {gammaFast gammaSlow Ccoord : ℝ}
    (hgammaFast : 0 < gammaFast)
    (hgammaSlow : 0 < gammaSlow)
    (hCcoord : 0 < Ccoord)
    (hfast : ∀ q,
      gammaFast *
          paperSharpNorm B.harmonicMass B.bandCenter
            (B.partition.center_ne_zero B.n_gt_one) q ^ 2 ≤
        (B.tiltedLaw xi).covariance
          (B.nuisanceResidualScore xi hgammaNuisance hGamma
            (B.bandRegressionScore q))
          (B.nuisanceResidualScore xi hgammaNuisance hGamma
            (B.bandRegressionScore q)))
    (hslow : gammaSlow * B.w ^ 2 ≤
      (B.tiltedLaw xi).covariance
        (B.actualTwoStageCompensatedScore
          xi hgammaNuisance hGamma e)
        (B.actualTwoStageCompensatedScore
          xi hgammaNuisance hGamma e))
    (hcoordinate : ∀ (u : B.MainSpace) (qFast : B.RawBandGauge)
        (lambda : ℝ),
      B.rawGaugeOfMain u = qFast - lambda •
          B.actualBandRegression xi hgammaNuisance hGamma e →
      u MainCoord.slow = B.w * lambda →
      ‖u‖ ^ 2 ≤ Ccoord *
        (paperSharpNorm B.harmonicMass B.bandCenter
            (B.partition.center_ne_zero B.n_gt_one) qFast ^ 2 +
          (B.w * lambda) ^ 2)) :
    ∀ u,
      (min gammaFast gammaSlow / Ccoord) * ‖u‖ ^ 2 ≤
        inner ℝ
          (B.schurResidual
            (B.exactNuisanceRegression
              xi hgammaNuisance hGamma) u)
          (B.covarianceOperator xi
            (B.schurResidual
              (B.exactNuisanceRegression
                xi hgammaNuisance hGamma) u)) := by
  intro u
  let lambda : ℝ := u MainCoord.slow / B.w
  let qReg : B.RawBandGauge :=
    B.actualBandRegression xi hgammaNuisance hGamma e
  let qFast : B.RawBandGauge := B.rawGaugeOfMain u + lambda • qReg
  have hq : B.rawGaugeOfMain u = qFast - lambda • qReg := by
    simp only [qFast]
    abel
  have hstored : u MainCoord.slow = B.w * lambda := by
    dsimp only [lambda]
    field_simp [ne_of_gt B.w_pos]
  have hcoord := hcoordinate u qFast lambda hq (by
    simpa only [qReg] using hstored)
  have hdecomp := B.exactSchur_quadratic_eq_fast_add_slow_twoStage
    xi hgammaNuisance hGamma e he u qFast lambda hq
      (by simpa only [qReg] using hstored)
  let S : ℝ := paperSharpNorm B.harmonicMass B.bandCenter
    (B.partition.center_ne_zero B.n_gt_one) qFast
  let Vfast : ℝ := (B.tiltedLaw xi).covariance
    (B.nuisanceResidualScore xi hgammaNuisance hGamma
      (B.bandRegressionScore qFast))
    (B.nuisanceResidualScore xi hgammaNuisance hGamma
      (B.bandRegressionScore qFast))
  let Vslow : ℝ := (B.tiltedLaw xi).covariance
    (B.actualTwoStageCompensatedScore xi hgammaNuisance hGamma e)
    (B.actualTwoStageCompensatedScore xi hgammaNuisance hGamma e)
  have hfast' : gammaFast * S ^ 2 ≤ Vfast := hfast qFast
  have hslow' : gammaSlow * B.w ^ 2 ≤ Vslow := hslow
  have hlambdaSq : 0 ≤ lambda ^ 2 := sq_nonneg _
  have hslowScaled : gammaSlow * (B.w * lambda) ^ 2 ≤
      lambda ^ 2 * Vslow := by
    have := mul_le_mul_of_nonneg_left hslow' hlambdaSq
    nlinarith
  have hminFast : min gammaFast gammaSlow * S ^ 2 ≤ Vfast :=
    (mul_le_mul_of_nonneg_right (min_le_left _ _) (sq_nonneg S)).trans
      hfast'
  have hminSlow : min gammaFast gammaSlow * (B.w * lambda) ^ 2 ≤
      lambda ^ 2 * Vslow :=
    (mul_le_mul_of_nonneg_right (min_le_right _ _)
      (sq_nonneg (B.w * lambda))).trans hslowScaled
  have hsum : min gammaFast gammaSlow *
      (S ^ 2 + (B.w * lambda) ^ 2) ≤
      Vfast + lambda ^ 2 * Vslow := by
    nlinarith
  have hminPos : 0 < min gammaFast gammaSlow :=
    lt_min hgammaFast hgammaSlow
  have hscaledCoord :
      (min gammaFast gammaSlow / Ccoord) * ‖u‖ ^ 2 ≤
        min gammaFast gammaSlow *
          (S ^ 2 + (B.w * lambda) ^ 2) := by
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ hCcoord).2
    have hmul := mul_le_mul_of_nonneg_left hcoord hminPos.le
    dsimp only [S] at hmul ⊢
    nlinarith
  rw [← B.exactSchurCovarianceOperator_quadratic]
  rw [hdecomp]
  exact hscaledCoord.trans hsum

end BridgeData

end

end Erdos390.Full.PaperBridgeFit

end

/- Source module: Erdos390.Full.PaperMainFastSlowCoordinates -/
section


/-!
# Concrete main-coordinate bound for the fast/slow Schur split

This file discharges the finite coordinate comparison left explicit by
`exactSchurGap_of_fastSlow`.  The constant is literal and finite; it may
depend on the fixed arithmetic partition, but it is chosen before the ODE
and no continuum or asymptotic assertion enters its proof.
-/

open scoped BigOperators

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

open ArithmeticBandGeometry PaperWeightedInverseExport

namespace BridgeData

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]
  (B : BridgeData Head Band)



theorem gaugeCenterSquareSum_nonneg : 0 ≤ B.gaugeCenterSquareSum := by
  unfold gaugeCenterSquareSum
  exact Finset.sum_nonneg fun j hj ↦ sq_nonneg _









end BridgeData

end

end Erdos390.Full.PaperBridgeFit

end

/- Source module: Erdos390.Full.PaperExactSchurFastSlowCoercivity -/
section


/-!
# Closed finite fast/slow coercivity connector

The actual band inverse, the compensated slow variance, and the proved
first-stage regression bound now imply the literal augmented main Schur gap.
No Schur coercivity or coordinate-comparison conclusion remains as a
hypothesis.
-/

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

open ArithmeticBandGeometry PaperWeightedInverseExport

namespace BridgeData

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]
  (B : BridgeData Head Band)

theorem exactSchurGap_of_fastSlow_of_regressionBound
    [Nonempty Head] [Nonempty Band]
    (xi : B.ParamSpace) {gammaNuisance : ℝ}
    (hgammaNuisance : 0 < gammaNuisance)
    (hGamma : ∀ z, gammaNuisance * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (e : B.RawBandGauge ≃ₗ[ℝ] B.RawBandGauge)
    (he : ∀ q,
      e q = B.actualBandSchurLinearMap
        xi hgammaNuisance hGamma q)
    {gammaFast gammaSlow Creg : ℝ}
    (hgammaFast : 0 < gammaFast)
    (hgammaSlow : 0 < gammaSlow)
    (hCreg : 0 ≤ Creg)
    (hfast : ∀ q,
      gammaFast *
          paperSharpNorm B.harmonicMass B.bandCenter
            (B.partition.center_ne_zero B.n_gt_one) q ^ 2 ≤
        (B.tiltedLaw xi).covariance
          (B.nuisanceResidualScore xi hgammaNuisance hGamma
            (B.bandRegressionScore q))
          (B.nuisanceResidualScore xi hgammaNuisance hGamma
            (B.bandRegressionScore q)))
    (hslow : gammaSlow * B.w ^ 2 ≤
      (B.tiltedLaw xi).covariance
        (B.actualTwoStageCompensatedScore
          xi hgammaNuisance hGamma e)
        (B.actualTwoStageCompensatedScore
          xi hgammaNuisance hGamma e))
    (hreg : paperSharpNorm B.harmonicMass B.bandCenter
        (B.partition.center_ne_zero B.n_gt_one)
        (B.actualBandRegression xi hgammaNuisance hGamma e) ≤
      Creg * B.w) :
    ∀ u,
      (min gammaFast gammaSlow /
        (1 + 2 * B.gaugeCenterSquareSum * (1 + Creg ^ 2))) * ‖u‖ ^ 2 ≤
      inner ℝ
        (B.schurResidual
          (B.exactNuisanceRegression xi hgammaNuisance hGamma) u)
        (B.covarianceOperator xi
          (B.schurResidual
            (B.exactNuisanceRegression xi hgammaNuisance hGamma) u)) := by
  have hCcoord : 0 <
      1 + 2 * B.gaugeCenterSquareSum * (1 + Creg ^ 2) := by
    have hA := B.gaugeCenterSquareSum_nonneg
    have hC2 : 0 ≤ Creg ^ 2 := sq_nonneg _
    positivity
  apply B.exactSchurGap_of_fastSlow
    xi hgammaNuisance hGamma e he hgammaFast hgammaSlow hCcoord
    hfast hslow
  intro u qFast lambda hq hstored
  exact B.main_norm_sq_le_fastSharp_add_storedSlow
    u qFast (B.actualBandRegression xi hgammaNuisance hGamma e)
      lambda Creg hCreg hreg hq hstored



end BridgeData

end

end Erdos390.Full.PaperBridgeFit

end

/- Source module: Erdos390.Full.PaperBridgePrimewiseRate -/
section


/-!
# Primewise moment transport along the actual bridge ODE

The paper obtains the post-bridge bound for each marked prime by integrating
the covariance row along the nonlinear moment-fitting path.  This file proves
that passage for the genuine finite exponential family.  It is not an
asymptotic contract: the derivative is the exact covariance derivative of the
finite active moment, and the endpoint estimate is a direct mean-value bound
on the interval `[0,1]`.
-/

open Metric Set

namespace Erdos390.Full

noncomputable section

namespace FiniteExponentialFamily

variable {Omega Param : Type*} [Fintype Omega]
  [NormedAddCommGroup Param] [NormedSpace Real Param]
  [FiniteDimensional Real Param]

/-- Exact endpoint transport for an arbitrary marked statistic.  A bound for
the normalized covariance row along a differentiable path gives the active
moment change with the paper's exact factor `baseMass / scale`.

This is the rigorous finite-dimensional replacement for the phrase
"multiply by `q_n/L` and integrate the marked row along the ODE". -/
theorem abs_moment_path_sub_le_of_covariance_bound
    (fam : FiniteExponentialFamily Omega Param)
    (F : Omega -> Real) (path velocity : Real -> Param) (C : Real)
    (hpath : ∀ t ∈ Icc (0 : Real) 1,
      HasDerivWithinAt path (velocity t) (Icc (0 : Real) 1) t)
    (hcov : ∀ t ∈ Icc (0 : Real) 1,
      |fam.covariance F (fun omega => fam.score omega (velocity t))
          (path t)| <= C) :
    |fam.moment F (path 1) - fam.moment F (path 0)| <=
      (fam.baseMass / fam.scale) * C := by
  let momentPath : Real -> Real := fun t => fam.moment F (path t)
  let momentDeriv : Real -> Real := fun t =>
    (fam.baseMass / fam.scale) *
      fam.covariance F (fun omega => fam.score omega (velocity t)) (path t)
  have hderiv : ∀ t ∈ Icc (0 : Real) 1,
      HasDerivWithinAt momentPath (momentDeriv t) (Icc (0 : Real) 1) t := by
    intro t ht
    have hcomp := (fam.hasFDerivAt_moment_covariance F (path t)).comp_hasDerivWithinAt
      t (hpath t ht)
    simpa only [momentPath, momentDeriv, Function.comp_apply,
      ContinuousLinearMap.smul_apply, smul_eq_mul,
      fam.covarianceScore_apply F (path t) (velocity t)] using hcomp
  have hbound : ∀ t ∈ Icc (0 : Real) 1,
      ‖momentDeriv t‖ <= (fam.baseMass / fam.scale) * C := by
    intro t ht
    have hfactor : 0 <= fam.baseMass / fam.scale :=
      div_nonneg (le_of_lt fam.baseMass_positive) (le_of_lt fam.scale_pos)
    simp only [Real.norm_eq_abs, momentDeriv, abs_mul,
      abs_of_nonneg hfactor]
    exact mul_le_mul_of_nonneg_left (hcov t ht) hfactor
  have hmv := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    hderiv hbound (convex_Icc (0 : Real) 1)
    (show (0 : Real) ∈ Icc 0 1 by norm_num)
    (show (1 : Real) ∈ Icc 0 1 by norm_num)
  simpa only [momentPath, Real.norm_eq_abs, sub_zero, norm_one, mul_one]
    using hmv

end FiniteExponentialFamily

namespace PaperBridgeFit

namespace BridgeData

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]
  (B : BridgeData Head Band)



/-- Exact marked-prime transport along an arbitrary differentiable parameter
path in the concrete bridge family.  The covariance hypothesis is precisely
the row estimate proved by Lemma 8.6; no endpoint estimate is assumed. -/
theorem abs_markedMoment_path_sub_le_of_covariance_bound
    [Nonempty Head]
    (p : Nat) (path velocity : Real -> B.ParamSpace) (C : Real)
    (hpath : ∀ t ∈ Icc (0 : Real) 1,
      HasDerivWithinAt path (velocity t) (Icc (0 : Real) 1) t)
    (hcov : ∀ t ∈ Icc (0 : Real) 1,
      |B.vectorFamily.scalarFamily.covariance
          (B.markedValuation p)
          (fun m => B.vectorFamily.scalarFamily.score m (velocity t))
          (path t)| <= C) :
    |B.paperMoment (B.markedValuation p) (path 1) -
        B.paperMoment (B.markedValuation p) (path 0)| <=
      (B.q / B.L) * C := by
  have h := B.vectorFamily.scalarFamily.abs_moment_path_sub_le_of_covariance_bound
      (B.markedValuation p) path velocity C hpath hcov
  change |B.paperMoment (B.markedValuation p) (path 1) -
      B.paperMoment (B.markedValuation p) (path 0)| <=
    (B.vectorFamily.baseMass / B.L) * C at h
  rw [B.vectorFamily_baseMass] at h
  exact h

/-- Paper-scaled form of the preceding theorem.  A normalized row
`Cprime / p` changes the actual valuation moment by exactly at most
`q_n Cprime / (p L)`. -/
theorem abs_markedMoment_path_sub_le_div_prime
    [Nonempty Head]
    (p : Nat) (hp : 0 < p)
    (path velocity : Real -> B.ParamSpace) (Cprime : Real)
    (hpath : ∀ t ∈ Icc (0 : Real) 1,
      HasDerivWithinAt path (velocity t) (Icc (0 : Real) 1) t)
    (hcov : ∀ t ∈ Icc (0 : Real) 1,
      |B.vectorFamily.scalarFamily.covariance
          (B.markedValuation p)
          (fun m => B.vectorFamily.scalarFamily.score m (velocity t))
          (path t)| <= Cprime / (p : Real)) :
    |B.paperMoment (B.markedValuation p) (path 1) -
        B.paperMoment (B.markedValuation p) (path 0)| <=
      B.q * Cprime / ((p : Real) * B.L) := by
  have h := B.abs_markedMoment_path_sub_le_of_covariance_bound
    p path velocity (Cprime / (p : Real)) hpath hcov
  calc
    |B.paperMoment (B.markedValuation p) (path 1) -
          B.paperMoment (B.markedValuation p) (path 0)|
        <= (B.q / B.L) * (Cprime / (p : Real)) := h
    _ = B.q * Cprime / ((p : Real) * B.L) := by
      field_simp [ne_of_gt B.L_pos, by exact_mod_cast hp]

/-- Combination with the pre-bridge marked residual.  This is the exact
finite inequality used at the end of Proposition 8.7: the bridge row adds
its rate constant to the already fixed rough-stage constant, while an upper
bound `q_n <= Cmass * N` converts the active mass to the paper's `N` scale. -/
theorem abs_target_sub_markedMoment_one_le_of_initial_rate
    [Nonempty Head]
    (p : Nat) (hp : 0 < p)
    (path velocity : Real -> B.ParamSpace)
    (target N Cinitial Cmass Crow : Real)
    (hCrow : 0 <= Crow)
    (hq : B.q <= Cmass * N)
    (hpath : ∀ t ∈ Icc (0 : Real) 1,
      HasDerivWithinAt path (velocity t) (Icc (0 : Real) 1) t)
    (hcov : ∀ t ∈ Icc (0 : Real) 1,
      |B.vectorFamily.scalarFamily.covariance
          (B.markedValuation p)
          (fun m => B.vectorFamily.scalarFamily.score m (velocity t))
          (path t)| <= Crow / (p : Real))
    (hinitial :
      |target - B.paperMoment (B.markedValuation p) (path 0)| <=
        Cinitial * N / ((p : Real) * B.L)) :
    |target - B.paperMoment (B.markedValuation p) (path 1)| <=
      (Cinitial + Cmass * Crow) * N / ((p : Real) * B.L) := by
  have htransport := B.abs_markedMoment_path_sub_le_div_prime
    p hp path velocity Crow hpath hcov
  have hden : 0 <= (p : Real) * B.L := by
    exact mul_nonneg (by exact_mod_cast (Nat.zero_le p)) (le_of_lt B.L_pos)
  have hbridge :
      |B.paperMoment (B.markedValuation p) (path 0) -
          B.paperMoment (B.markedValuation p) (path 1)| <=
        (Cmass * N) * Crow / ((p : Real) * B.L) := by
    rw [abs_sub_comm]
    exact htransport.trans
      (div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right hq hCrow) hden)
  calc
    |target - B.paperMoment (B.markedValuation p) (path 1)| =
        |(target - B.paperMoment (B.markedValuation p) (path 0)) +
          (B.paperMoment (B.markedValuation p) (path 0) -
            B.paperMoment (B.markedValuation p) (path 1))| := by ring_nf
    _ <= |target - B.paperMoment (B.markedValuation p) (path 0)| +
        |B.paperMoment (B.markedValuation p) (path 0) -
          B.paperMoment (B.markedValuation p) (path 1)| := abs_add_le _ _
    _ <= Cinitial * N / ((p : Real) * B.L) +
        (Cmass * N) * Crow / ((p : Real) * B.L) :=
      add_le_add hinitial hbridge
    _ = (Cinitial + Cmass * Crow) * N /
        ((p : Real) * B.L) := by ring

end BridgeData

end PaperBridgeFit

end

end Erdos390.Full

end

/- Source module: Erdos390.Full.PaperVectorFieldEffectiveBound -/
section


/-!
# Effective-norm bound for the literal paper vector field

The ODE continuation argument uses the effective max norm, not the ambient
Euclidean norm.  This file proves the exact finite identity which converts
the Schur solution into its three paper components:

* the prime-by-prime effective fugacity;
* the nuisance regression coefficient;
* the stored slow coordinate `w * lambda`.

It then shows that uniform bounds for those three components of every
solution of the *actual* Schur equation imply the required effective
velocity bound.  Thus Proposition 8.7 can consume the literal quantitative
outputs of Lemmas 8.4--8.6 without assuming a norm bound for the already
assembled vector field.
-/

open Metric Set

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

namespace BridgeData

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]
  (B : BridgeData Head Band)

/-- Exact effective norm of a Schur residual.  In particular, the nuisance
term enters with the norm of the genuine finite regression `R u`; no
coordinate comparison or asymptotic estimate occurs in this identity. -/
theorem norm_effectiveParamEquiv_symm_schurResidual
    (R : B.MainSpace → B.NuisanceSpace) (u : B.MainSpace) :
    ‖B.effectiveParamEquiv.symm (B.schurResidual R u)‖ =
      max
        (max
          ‖fun p : ArithmeticBandGeometry.BandPrime
              B.sampleData.n B.sampleData.W ↦
            (B.rawGaugeOfMain u).1 (B.partition.band p) +
              (u MainCoord.slow / B.w) * B.primeDeviation p‖
          ‖R u‖)
        |u MainCoord.slow| := by
  rw [B.norm_effectiveParamEquiv_symm,
    B.norm_effectiveCoordinateCLM_eq,
    B.nuisanceParameter_schurResidual,
    B.schurResidual_slow, norm_neg]
  have hprime :
      (fun p : ArithmeticBandGeometry.BandPrime
          B.sampleData.n B.sampleData.W ↦
        B.effectivePrimeCoefficient (B.schurResidual R u) p) =
      (fun p ↦
        (B.rawGaugeOfMain u).1 (B.partition.band p) +
          (u MainCoord.slow / B.w) * B.primeDeviation p) := by
    funext p
    exact B.schurResidual_effectivePrimeCoefficient R u p
  rw [hprime]

/-- The effective velocity follows from componentwise bounds on the unique
solution of the literal Schur equation.  The hypotheses are deliberately
formulated for an arbitrary `u` satisfying that equation, rather than for
the vector field itself.  This is the exact interface exported by the
weighted inverse, compensated slow, and nuisance-regression estimates. -/
theorem effectiveVelocity_le_of_exactSchur_solution_component_bounds
    [Nonempty Head]
    (xi : B.ParamSpace) (Delta : Band → ℝ)
    {gammaFull gammaNuisance speed : ℝ}
    (hgammaFull : 0 < gammaFull)
    (hFull : B.vectorFamily.HasCovarianceGap gammaFull xi)
    (hgammaNuisance : 0 < gammaNuisance)
    (hGamma : ∀ z, gammaNuisance * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (hprime : ∀ u,
      B.exactSchurCovarianceOperator xi hgammaNuisance hGamma u =
          B.mainPart (B.normalizedTarget Delta) →
        ‖fun p : ArithmeticBandGeometry.BandPrime
              B.sampleData.n B.sampleData.W ↦
            (B.rawGaugeOfMain u).1 (B.partition.band p) +
              (u MainCoord.slow / B.w) * B.primeDeviation p‖ ≤ speed)
    (hnuisance : ∀ u,
      B.exactSchurCovarianceOperator xi hgammaNuisance hGamma u =
          B.mainPart (B.normalizedTarget Delta) →
        ‖B.exactNuisanceRegression xi hgammaNuisance hGamma u‖ ≤ speed)
    (hslow : ∀ u,
      B.exactSchurCovarianceOperator xi hgammaNuisance hGamma u =
          B.mainPart (B.normalizedTarget Delta) →
        |u MainCoord.slow| ≤ speed) :
    ‖B.effectiveParamEquiv.symm
        (B.vectorFamily.vectorField (B.targetVector Delta) xi)‖ ≤ speed := by
  let v := B.vectorFamily.vectorField (B.targetVector Delta) xi
  let u := B.mainPart v
  let R := B.exactNuisanceRegression xi hgammaNuisance hGamma
  have hsolve :=
    B.vectorField_eq_schurResidual_and_mainEquation xi Delta
      hgammaFull hFull hgammaNuisance hGamma
  have hv : v = B.schurResidual R u := by
    simpa only [v, u, R] using hsolve.1
  have hu : B.exactSchurCovarianceOperator xi hgammaNuisance hGamma u =
      B.mainPart (B.normalizedTarget Delta) := by
    simpa only [u, v] using hsolve.2
  rw [show B.vectorFamily.vectorField (B.targetVector Delta) xi = v by rfl,
    hv, B.norm_effectiveParamEquiv_symm_schurResidual]
  exact max_le (max_le (hprime u hu) (hnuisance u hu)) (hslow u hu)



end BridgeData

end

end Erdos390.Full.PaperBridgeFit

end

/- Source module: Erdos390.Full.PaperExactTwoStageTargetSolve -/
section


/-!
# Exact two-stage solution of the finite Schur target equation

This file performs the algebraic block solve which is used, but usually
left implicit, in Proposition 8.7.  The right side is the literal normalized
paper target.  Its fast band component and compensated slow component are
defined below from the actual finite arithmetic data.  No asymptotic
estimate, continuum operator, or covariance lower bound is asserted here.
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

private theorem sum_mainCoord_target {Gauge : Type*} [Fintype Gauge]
    (f : MainCoord Gauge → ℝ) :
    (∑ c : MainCoord Gauge, f c) =
      (∑ j : Gauge, f (.gauge j)) + f .slow := by
  let e : MainCoord Gauge ≃ Gauge ⊕ Unit :=
    { toFun := fun c => match c with
        | .gauge j => Sum.inl j
        | .slow => Sum.inr ()
      invFun := fun s => match s with
        | Sum.inl j => .gauge j
        | Sum.inr _ => .slow
      left_inv := by intro c; cases c <;> rfl
      right_inv := by intro s; cases s <;> rfl }
  calc
    (∑ c : MainCoord Gauge, f c) =
        ∑ s : Gauge ⊕ Unit, f (e.symm s) := by
      exact Fintype.sum_equiv e f (fun s => f (e.symm s))
        (fun c => by simp)
    _ = _ := by
      rw [Fintype.sum_sum_type]
      simp [e]







/-- The projected target row represents exactly the gauge part of the
normalized paper target under the finite arithmetic `D` pairing. -/
theorem bandDPairing_projectedNormalizedTargetBand
    [Nonempty Head] [Nonempty Band]
    (Delta : Band → ℝ) (r : B.RawBandGauge) :
    B.bandDPairing r (B.projectedNormalizedTargetBand Delta) =
      inner ℝ (B.mainRawSlowLinearEquiv.symm (r, 0))
        (B.mainPart (B.normalizedTarget Delta)) := by
  rw [PiLp.inner_apply]
  change B.bandDPairing r (B.projectedNormalizedTargetBand Delta) =
    ∑ c : MainCoord B.GaugeIndex,
      B.mainPart (B.normalizedTarget Delta) c *
        B.mainRawSlowLinearEquiv.symm (r, 0) c
  rw [sum_mainCoord_target]
  simp only [B.mainRawSlowLinearEquiv_symm_gauge,
    B.mainRawSlowLinearEquiv_symm_slow, mul_zero, add_zero,
    B.mainPart_gauge]
  rw [show B.bandDPairing r (B.projectedNormalizedTargetBand Delta) =
      ∑ j : Band, B.harmonicMass j * r.1 j *
        B.normalizedTargetBandRow Delta j by
    unfold projectedNormalizedTargetBand bandDPairing
    exact B.weighted_pairing_projectRawBandVector r
      (B.normalizedTargetBandRow Delta)]
  unfold normalizedTargetBandRow
  have hmass (j : Band) : B.harmonicMass j ≠ 0 :=
    ne_of_gt (B.harmonicMass_pos j)
  have hcancel (j : Band) :
      B.harmonicMass j * r.1 j *
          ((B.L / B.q) * Delta j / B.harmonicMass j) =
        r.1 j * ((B.L / B.q) * Delta j) := by
    field_simp [hmass j]
  simp_rw [hcancel]
  rw [Fintype.sum_eq_add_sum_subtype_ne
    (fun j : Band => r.1 j * ((B.L / B.q) * Delta j)) B.lowBand]
  rw [B.rawBandGauge_low_eq]
  simp only [B.normalizedTarget_apply, unscaledTarget, coordScale,
    div_one]
  have hrhs :
      (∑ x : B.GaugeIndex,
        (B.L / B.q) *
            (Delta x.1 - B.lowRatio x * Delta B.lowBand) * r.1 x.1) =
        (∑ x : B.GaugeIndex,
          r.1 x.1 * ((B.L / B.q) * Delta x.1)) -
          (∑ x : B.GaugeIndex, B.lowRatio x * r.1 x.1) *
            ((B.L / B.q) * Delta B.lowBand) := by
    calc
      (∑ x : B.GaugeIndex,
        (B.L / B.q) *
            (Delta x.1 - B.lowRatio x * Delta B.lowBand) * r.1 x.1) =
          ∑ x : B.GaugeIndex,
            (r.1 x.1 * ((B.L / B.q) * Delta x.1) -
              (B.lowRatio x * r.1 x.1) *
                ((B.L / B.q) * Delta B.lowBand)) := by
        apply Finset.sum_congr rfl
        intro x hx
        ring
      _ = _ := by
        rw [Finset.sum_sub_distrib, Finset.sum_mul]
  rw [hrhs]
  ring

/-- Full raw/slow pairing with the normalized target.  This extends the
preceding gauge identity by the literal stored slow coordinate. -/
theorem inner_mainRawSlow_symm_normalizedTarget
    [Nonempty Head] [Nonempty Band]
    (Delta : Band → ℝ) (q : B.RawBandGauge) (s : ℝ) :
    inner ℝ (B.mainRawSlowLinearEquiv.symm (q, s))
        (B.mainPart (B.normalizedTarget Delta)) =
      B.bandDPairing q (B.projectedNormalizedTargetBand Delta) +
        s * B.mainPart (B.normalizedTarget Delta) MainCoord.slow := by
  have hband := B.bandDPairing_projectedNormalizedTargetBand Delta q
  rw [PiLp.inner_apply] at hband ⊢
  change
    (∑ c : MainCoord B.GaugeIndex,
      B.mainPart (B.normalizedTarget Delta) c *
        B.mainRawSlowLinearEquiv.symm (q, s) c) = _
  change B.bandDPairing q (B.projectedNormalizedTargetBand Delta) =
    ∑ c : MainCoord B.GaugeIndex,
      B.mainPart (B.normalizedTarget Delta) c *
        B.mainRawSlowLinearEquiv.symm (q, 0) c at hband
  rw [sum_mainCoord_target] at hband ⊢
  simp only [B.mainRawSlowLinearEquiv_symm_gauge,
    B.mainRawSlowLinearEquiv_symm_slow, mul_zero, add_zero] at hband ⊢
  rw [hband]
  ring













theorem rawGauge_eq_fastGauge_sub_regression
    [Nonempty Head] [Nonempty Band]
    (xi : B.ParamSpace) {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (e : B.RawBandGauge ≃ₗ[ℝ] B.RawBandGauge)
    (u : B.MainSpace) :
    B.rawGaugeOfMain u =
      B.fastGaugeOfMain xi hgamma hgap e u -
        (u MainCoord.slow / B.w) •
          B.actualBandRegression xi hgamma hgap e := by
  unfold fastGaugeOfMain
  abel

theorem slow_eq_w_mul_slow_div (u : B.MainSpace) :
    u MainCoord.slow = B.w * (u MainCoord.slow / B.w) := by
  field_simp [ne_of_gt B.w_pos]



/-- Consequently the fast coordinate is literally the inverse image of the
projected normalized target row. -/
theorem fastGauge_eq_inverse_projectedTarget
    [Nonempty Head] [Nonempty Band]
    (xi : B.ParamSpace) {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (e : B.RawBandGauge ≃ₗ[ℝ] B.RawBandGauge)
    (he : ∀ q, e q = B.actualBandSchurLinearMap xi hgamma hgap q)
    (Delta : Band → ℝ) (u : B.MainSpace)
    (hu : B.exactSchurCovarianceOperator xi hgamma hgap u =
      B.mainPart (B.normalizedTarget Delta)) :
    B.fastGaugeOfMain xi hgamma hgap e u =
      e.symm (B.projectedNormalizedTargetBand Delta) := by
  apply e.injective
  rw [e.apply_symm_apply, he]
  exact B.actualBandSchur_fastGauge_eq_projectedTarget
    xi hgamma hgap e he Delta u hu











/-- Exact target-only formula for the compensated scalar.  All dependence
on the tilted law occurs through the already constructed first-stage
regression vector. -/
theorem compensatedNormalizedTarget_eq_slow_sub_bandDPairing
    [Nonempty Head] [Nonempty Band]
    (xi : B.ParamSpace) {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (e : B.RawBandGauge ≃ₗ[ℝ] B.RawBandGauge)
    (Delta : Band → ℝ) :
    B.compensatedNormalizedTarget xi hgamma hgap e Delta =
      -B.bandDPairing
          (B.actualBandRegression xi hgamma hgap e)
          (B.projectedNormalizedTargetBand Delta) +
        B.w * B.mainPart (B.normalizedTarget Delta) MainCoord.slow := by
  unfold compensatedNormalizedTarget compensatedMainDirection
  rw [B.inner_mainRawSlow_symm_normalizedTarget]
  have hneg :
      B.bandDPairing (-B.actualBandRegression xi hgamma hgap e)
          (B.projectedNormalizedTargetBand Delta) =
        -B.bandDPairing (B.actualBandRegression xi hgamma hgap e)
          (B.projectedNormalizedTargetBand Delta) := by
    unfold bandDPairing
    simp only [Submodule.coe_neg, Pi.neg_apply]
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  rw [hneg]









/-- Division form of the exact slow solve. -/
theorem slow_div_eq_compensatedTarget_div_variance
    [Nonempty Head] [Nonempty Band]
    (xi : B.ParamSpace) {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (e : B.RawBandGauge ≃ₗ[ℝ] B.RawBandGauge)
    (he : ∀ q, e q = B.actualBandSchurLinearMap xi hgamma hgap q)
    (Delta : Band → ℝ) (u : B.MainSpace)
    (hu : B.exactSchurCovarianceOperator xi hgamma hgap u =
      B.mainPart (B.normalizedTarget Delta))
    (hvariance : B.actualTwoStageCompensatedVariance
      xi hgamma hgap e ≠ 0) :
    u MainCoord.slow / B.w =
      B.compensatedNormalizedTarget xi hgamma hgap e Delta /
        B.actualTwoStageCompensatedVariance xi hgamma hgap e := by
  apply (eq_div_iff hvariance).2
  exact B.slow_div_mul_actualTwoStageCompensatedVariance
    xi hgamma hgap e he Delta u hu



/-- A lower bound for the literal compensated variance and an upper bound
for its literal target give the exact slow-velocity estimate. -/
theorem abs_slow_div_le_of_variance_target_bounds
    [Nonempty Head] [Nonempty Band]
    (xi : B.ParamSpace) {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (e : B.RawBandGauge ≃ₗ[ℝ] B.RawBandGauge)
    (he : ∀ q, e q = B.actualBandSchurLinearMap xi hgamma hgap q)
    (Delta : Band → ℝ) (u : B.MainSpace)
    (hu : B.exactSchurCovarianceOperator xi hgamma hgap u =
      B.mainPart (B.normalizedTarget Delta))
    {Vlower Tbound : ℝ} (hVlower : 0 < Vlower)
    (hvariance : Vlower ≤ B.actualTwoStageCompensatedVariance
      xi hgamma hgap e)
    (hTbound : 0 ≤ Tbound)
    (htarget : |B.compensatedNormalizedTarget
      xi hgamma hgap e Delta| ≤ Tbound) :
    |u MainCoord.slow / B.w| ≤ Tbound / Vlower := by
  have hVpos : 0 < B.actualTwoStageCompensatedVariance
      xi hgamma hgap e := hVlower.trans_le hvariance
  have hformula := B.slow_div_eq_compensatedTarget_div_variance
    xi hgamma hgap e he Delta u hu (ne_of_gt hVpos)
  rw [hformula, abs_div, abs_of_pos hVpos]
  calc
    |B.compensatedNormalizedTarget xi hgamma hgap e Delta| /
        B.actualTwoStageCompensatedVariance xi hgamma hgap e ≤
      Tbound / B.actualTwoStageCompensatedVariance
        xi hgamma hgap e :=
      div_le_div_of_nonneg_right htarget hVpos.le
    _ ≤ Tbound / Vlower :=
      div_le_div_of_nonneg_left hTbound hVlower hvariance

/-- Stored-slow form of the preceding estimate. -/
theorem abs_slow_le_of_variance_target_bounds
    [Nonempty Head] [Nonempty Band]
    (xi : B.ParamSpace) {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (e : B.RawBandGauge ≃ₗ[ℝ] B.RawBandGauge)
    (he : ∀ q, e q = B.actualBandSchurLinearMap xi hgamma hgap q)
    (Delta : Band → ℝ) (u : B.MainSpace)
    (hu : B.exactSchurCovarianceOperator xi hgamma hgap u =
      B.mainPart (B.normalizedTarget Delta))
    {Vlower Tbound : ℝ} (hVlower : 0 < Vlower)
    (hvariance : Vlower ≤ B.actualTwoStageCompensatedVariance
      xi hgamma hgap e)
    (hTbound : 0 ≤ Tbound)
    (htarget : |B.compensatedNormalizedTarget
      xi hgamma hgap e Delta| ≤ Tbound) :
    |u MainCoord.slow| ≤ B.w * (Tbound / Vlower) := by
  have hlambda := B.abs_slow_div_le_of_variance_target_bounds
    xi hgamma hgap e he Delta u hu hVlower hvariance hTbound htarget
  have hs := B.slow_eq_w_mul_slow_div u
  rw [hs, abs_mul, abs_of_pos B.w_pos]
  exact mul_le_mul_of_nonneg_left hlambda B.w_pos.le

/-- Exact prime-coefficient identity for the two-stage decomposition of an
arbitrary main vector. -/
theorem effectivePrimeCoefficient_fast_compensated
    [Nonempty Head] [Nonempty Band]
    (xi : B.ParamSpace) {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (e : B.RawBandGauge ≃ₗ[ℝ] B.RawBandGauge)
    (u : B.MainSpace)
    (p : BandPrime B.sampleData.n B.sampleData.W) :
    (B.rawGaugeOfMain u).1 (B.partition.band p) +
        (u MainCoord.slow / B.w) * B.primeDeviation p =
      (B.fastGaugeOfMain xi hgamma hgap e u).1
          (B.partition.band p) +
        (u MainCoord.slow / B.w) *
          B.actualCompensatedCoefficient
            (B.actualBandRegression xi hgamma hgap e) p := by
  have hq := B.rawGauge_eq_fastGauge_sub_regression
    xi hgamma hgap e u
  have hp := congrArg
    (fun q : B.RawBandGauge => q.1 (B.partition.band p)) hq
  simp only [Submodule.coe_sub, Pi.sub_apply, SetLike.val_smul,
    Pi.smul_apply, smul_eq_mul] at hp
  unfold actualCompensatedCoefficient bandRegressionCoefficient
  rw [hp]
  ring



/-- Exact nuisance component of the two-stage main solve before inserting
the target identities. -/
theorem exactNuisanceRegression_eq_fast_add_twoStage
    [Nonempty Head] [Nonempty Band]
    (xi : B.ParamSpace) {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (e : B.RawBandGauge ≃ₗ[ℝ] B.RawBandGauge)
    (u : B.MainSpace) :
    B.exactNuisanceRegression xi hgamma hgap u =
      B.nuisanceCoefficientOfScore xi hgamma hgap
          (B.bandRegressionScore
            (B.fastGaugeOfMain xi hgamma hgap e u)) +
        (u MainCoord.slow / B.w) •
          B.actualTwoStageNuisanceCoefficient xi hgamma hgap e := by
  let qReg := B.actualBandRegression xi hgamma hgap e
  let lambda := u MainCoord.slow / B.w
  let qFast := B.fastGaugeOfMain xi hgamma hgap e u
  have hq : B.rawGaugeOfMain u = qFast - lambda • qReg := by
    simpa only [qFast, lambda, qReg] using
      B.rawGauge_eq_fastGauge_sub_regression xi hgamma hgap e u
  have hs : u MainCoord.slow = B.w * lambda := by
    simpa only [lambda] using B.slow_eq_w_mul_slow_div u
  have hinput :
      (fun m => B.vectorFamily.scalarFamily.score m (B.mainEmbed u)) =
        fun m => B.bandRegressionScore qFast m +
          lambda * B.postBandPrimeScore qReg m := by
    funext m
    rw [B.vectorScore_mainEmbed_eq_rawGauge_add_slow, hq,
      B.bandRegressionScore_sub, B.bandRegressionScore_smul, hs,
      mul_div_cancel_left₀ lambda (ne_of_gt B.w_pos),
      B.postBandPrimeScore_eq_slow_sub_bandRegression]
    ring
  rw [B.exactNuisanceRegression_eq_nuisanceCoefficient_mainScore,
    hinput, B.nuisanceCoefficientOfScore_add,
    B.nuisanceCoefficientOfScore_smul]
  rfl



/-- A literal covariance-vector row bounded by `gamma * C` gives the
corresponding target-fast nuisance coefficient bound `C`.  Thus the
coefficient estimate is a consequence of the nuisance covariance gap, not
an additional analytic input. -/
theorem targetFastNuisanceCoefficient_norm_le_of_covarianceVector
    [Nonempty Head] [Nonempty Band]
    (xi : B.ParamSpace) {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (e : B.RawBandGauge ≃ₗ[ℝ] B.RawBandGauge)
    (Delta : Band → ℝ) {C : ℝ}
    (hcov : ‖B.nuisanceCovarianceVector xi
      (B.bandRegressionScore
        (e.symm (B.projectedNormalizedTargetBand Delta)))‖ ≤
          gamma * C) :
    ‖B.targetFastNuisanceCoefficient xi hgamma hgap e Delta‖ ≤ C := by
  unfold targetFastNuisanceCoefficient
  calc
    ‖B.nuisanceCoefficientOfScore xi hgamma hgap
        (B.bandRegressionScore
          (e.symm (B.projectedNormalizedTargetBand Delta)))‖ ≤
      ‖B.nuisanceCovarianceVector xi
        (B.bandRegressionScore
          (e.symm (B.projectedNormalizedTargetBand Delta)))‖ / gamma :=
        B.nuisanceCoefficientOfScore_norm_le xi hgamma hgap _
    _ ≤ (gamma * C) / gamma :=
      div_le_div_of_nonneg_right hcov hgamma.le
    _ = C := by field_simp [ne_of_gt hgamma]

/-- The same gap reduction for the literal post-band slow row. -/
theorem actualTwoStageNuisanceCoefficient_norm_le_of_covarianceVector
    [Nonempty Head] [Nonempty Band]
    (xi : B.ParamSpace) {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (e : B.RawBandGauge ≃ₗ[ℝ] B.RawBandGauge)
    {C : ℝ}
    (hcov : ‖B.nuisanceCovarianceVector xi
      (B.postBandPrimeScore
        (B.actualBandRegression xi hgamma hgap e))‖ ≤ gamma * C) :
    ‖B.actualTwoStageNuisanceCoefficient xi hgamma hgap e‖ ≤ C := by
  unfold actualTwoStageNuisanceCoefficient actualNuisanceCoefficient
  calc
    ‖B.nuisanceCoefficientOfScore xi hgamma hgap
        (B.postBandPrimeScore
          (B.actualBandRegression xi hgamma hgap e))‖ ≤
      ‖B.nuisanceCovarianceVector xi
        (B.postBandPrimeScore
          (B.actualBandRegression xi hgamma hgap e))‖ / gamma :=
        B.nuisanceCoefficientOfScore_norm_le xi hgamma hgap _
    _ ≤ (gamma * C) / gamma :=
      div_le_div_of_nonneg_right hcov hgamma.le
    _ = C := by field_simp [ne_of_gt hgamma]

/-- After imposing the Schur equation, the nuisance component is the sum
of the literal target-fast coefficient and the literal compensated-slow
coefficient. -/
theorem exactNuisanceRegression_eq_targetFast_add_twoStage
    [Nonempty Head] [Nonempty Band]
    (xi : B.ParamSpace) {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (e : B.RawBandGauge ≃ₗ[ℝ] B.RawBandGauge)
    (he : ∀ q, e q = B.actualBandSchurLinearMap xi hgamma hgap q)
    (Delta : Band → ℝ) (u : B.MainSpace)
    (hu : B.exactSchurCovarianceOperator xi hgamma hgap u =
      B.mainPart (B.normalizedTarget Delta)) :
    B.exactNuisanceRegression xi hgamma hgap u =
      B.targetFastNuisanceCoefficient xi hgamma hgap e Delta +
        (u MainCoord.slow / B.w) •
          B.actualTwoStageNuisanceCoefficient xi hgamma hgap e := by
  rw [B.exactNuisanceRegression_eq_fast_add_twoStage]
  unfold targetFastNuisanceCoefficient
  rw [B.fastGauge_eq_inverse_projectedTarget
    xi hgamma hgap e he Delta u hu]

/-- Nuisance-velocity estimate from the two explicit coefficients and the
already solved slow scalar. -/
theorem exactNuisanceRegression_norm_le_of_twoStage
    [Nonempty Head] [Nonempty Band]
    (xi : B.ParamSpace) {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (e : B.RawBandGauge ≃ₗ[ℝ] B.RawBandGauge)
    (he : ∀ q, e q = B.actualBandSchurLinearMap xi hgamma hgap q)
    (Delta : Band → ℝ) (u : B.MainSpace)
    (hu : B.exactSchurCovarianceOperator xi hgamma hgap u =
      B.mainPart (B.normalizedTarget Delta))
    {CfastNuisance Clambda CslowNuisance : ℝ}
    (hClambda : 0 ≤ Clambda)
    (hfast : ‖B.targetFastNuisanceCoefficient
      xi hgamma hgap e Delta‖ ≤ CfastNuisance)
    (hlambda : |u MainCoord.slow / B.w| ≤ Clambda)
    (hslow : ‖B.actualTwoStageNuisanceCoefficient
      xi hgamma hgap e‖ ≤ CslowNuisance) :
    ‖B.exactNuisanceRegression xi hgamma hgap u‖ ≤
      CfastNuisance + Clambda * CslowNuisance := by
  rw [B.exactNuisanceRegression_eq_targetFast_add_twoStage
    xi hgamma hgap e he Delta u hu]
  calc
    ‖B.targetFastNuisanceCoefficient xi hgamma hgap e Delta +
        (u MainCoord.slow / B.w) •
          B.actualTwoStageNuisanceCoefficient xi hgamma hgap e‖ ≤
      ‖B.targetFastNuisanceCoefficient xi hgamma hgap e Delta‖ +
        ‖(u MainCoord.slow / B.w) •
          B.actualTwoStageNuisanceCoefficient xi hgamma hgap e‖ :=
      norm_add_le _ _
    _ = ‖B.targetFastNuisanceCoefficient xi hgamma hgap e Delta‖ +
        |u MainCoord.slow / B.w| *
          ‖B.actualTwoStageNuisanceCoefficient xi hgamma hgap e‖ := by
      rw [norm_smul, Real.norm_eq_abs]
    _ ≤ CfastNuisance + Clambda * CslowNuisance :=
      add_le_add hfast
        (mul_le_mul hlambda hslow (norm_nonneg _) hClambda)



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























/-- Mixed pairing estimate used by the target numerator: the regression
vector is sharp, while the projected fast target is only ordinary bounded.
The exact arithmetic first moment `sum_j H_j alpha_j` is retained. -/
theorem abs_bandDPairing_le_sharp_mul_raw
    [Nonempty Band]
    (q r : B.RawBandGauge) :
    |B.bandDPairing q r| ≤
      (∑ j : Band, B.harmonicMass j * B.bandCenter j) *
        paperSharpNorm B.harmonicMass B.bandCenter
          (B.partition.center_ne_zero B.n_gt_one) q * ‖r‖ := by
  have hq (j : Band) :
      |q.1 j| ≤ B.bandCenter j *
        paperSharpNorm B.harmonicMass B.bandCenter
          (B.partition.center_ne_zero B.n_gt_one) q := by
    have h := abs_raw_coordinate_le_paperSharpNorm
      B.harmonicMass B.bandCenter
      (B.partition.center_ne_zero B.n_gt_one) q j
    simpa only [abs_of_pos (B.bandCenter_pos j)] using h
  have hr (j : Band) : |r.1 j| ≤ ‖r‖ := by
    simpa only [Real.norm_eq_abs] using norm_le_pi_norm r.1 j
  have hsharp : 0 ≤ paperSharpNorm B.harmonicMass B.bandCenter
      (B.partition.center_ne_zero B.n_gt_one) q := norm_nonneg _
  have hrnorm : 0 ≤ ‖r‖ := norm_nonneg _
  calc
    |B.bandDPairing q r| ≤
        ∑ j : Band, |B.harmonicMass j * q.1 j * r.1 j| := by
      unfold bandDPairing
      exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j : Band,
        (B.harmonicMass j * B.bandCenter j) *
          paperSharpNorm B.harmonicMass B.bandCenter
            (B.partition.center_ne_zero B.n_gt_one) q * ‖r‖ := by
      apply Finset.sum_le_sum
      intro j hj
      rw [abs_mul, abs_mul, abs_of_pos (B.harmonicMass_pos j)]
      have hleft : 0 ≤ B.harmonicMass j := (B.harmonicMass_pos j).le
      calc
        B.harmonicMass j * |q.1 j| * |r.1 j| ≤
            B.harmonicMass j *
                (B.bandCenter j *
                  paperSharpNorm B.harmonicMass B.bandCenter
                    (B.partition.center_ne_zero B.n_gt_one) q) *
              ‖r‖ := by
          exact mul_le_mul
            (mul_le_mul_of_nonneg_left (hq j) hleft)
            (hr j) (abs_nonneg _)
            (mul_nonneg hleft
              (mul_nonneg (B.bandCenter_pos j).le hsharp))
        _ = (B.harmonicMass j * B.bandCenter j) *
              paperSharpNorm B.harmonicMass B.bandCenter
                (B.partition.center_ne_zero B.n_gt_one) q * ‖r‖ := by
          ring
    _ = (∑ j : Band, B.harmonicMass j * B.bandCenter j) *
          paperSharpNorm B.harmonicMass B.bandCenter
            (B.partition.center_ne_zero B.n_gt_one) q * ‖r‖ := by
      rw [Finset.sum_mul, Finset.sum_mul]

/-- Ordinary raw-sup fast-coordinate estimate from the ordinary inverse.
This is the exact finite version of (8.59). -/
theorem fastGauge_norm_le_of_ordinary_inverse
    [Nonempty Head] [Nonempty Band]
    (xi : B.ParamSpace) {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (e : B.RawBandGauge ≃ₗ[ℝ] B.RawBandGauge)
    (he : ∀ q, e q = B.actualBandSchurLinearMap xi hgamma hgap q)
    {Cinv : ℝ}
    (hinv : ∀ v, ‖e.symm v‖ ≤ Cinv * ‖v‖)
    (Delta : Band → ℝ) (u : B.MainSpace)
    (hu : B.exactSchurCovarianceOperator xi hgamma hgap u =
      B.mainPart (B.normalizedTarget Delta)) :
    ‖B.fastGaugeOfMain xi hgamma hgap e u‖ ≤
      Cinv * ‖B.projectedNormalizedTargetBand Delta‖ := by
  rw [B.fastGauge_eq_inverse_projectedTarget
    xi hgamma hgap e he Delta u hu]
  exact hinv _



/-- A sharp slow-regression estimate and an ordinary fast-target estimate
bound the compensated scalar target.  No division of the fast target by
`alpha_0` occurs. -/
theorem abs_compensatedNormalizedTarget_le_of_regression_ordinaryTarget
    [Nonempty Head] [Nonempty Band]
    (xi : B.ParamSpace) {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (e : B.RawBandGauge ≃ₗ[ℝ] B.RawBandGauge)
    (Delta : Band → ℝ)
    {Creg Tband TslowCoord : ℝ}
    (hCreg : 0 ≤ Creg)
    (hreg : paperSharpNorm B.harmonicMass B.bandCenter
      (B.partition.center_ne_zero B.n_gt_one)
      (B.actualBandRegression xi hgamma hgap e) ≤ Creg * B.w)
    (htargetBand : ‖B.projectedNormalizedTargetBand Delta‖ ≤ Tband)
    (htargetSlowCoord :
      |B.mainPart (B.normalizedTarget Delta) MainCoord.slow| ≤
        TslowCoord) :
    |B.compensatedNormalizedTarget xi hgamma hgap e Delta| ≤
      B.twoStageCompensatedTargetBoundOrdinaryFast
        Creg Tband TslowCoord := by
  unfold twoStageCompensatedTargetBoundOrdinaryFast
  rw [B.compensatedNormalizedTarget_eq_slow_sub_bandDPairing]
  have hD := B.abs_bandDPairing_le_sharp_mul_raw
    (B.actualBandRegression xi hgamma hgap e)
    (B.projectedNormalizedTargetBand Delta)
  have hmoment : 0 ≤ ∑ j : Band,
      B.harmonicMass j * B.bandCenter j := by
    apply Finset.sum_nonneg
    intro j hj
    exact mul_nonneg (B.harmonicMass_pos j).le (B.bandCenter_pos j).le
  have hregNonneg : 0 ≤ Creg * B.w :=
    mul_nonneg hCreg B.w_pos.le
  have hD' :
      |B.bandDPairing (B.actualBandRegression xi hgamma hgap e)
          (B.projectedNormalizedTargetBand Delta)| ≤
        (∑ j : Band, B.harmonicMass j * B.bandCenter j) *
          (Creg * B.w) * Tband := by
    calc
      |B.bandDPairing (B.actualBandRegression xi hgamma hgap e)
          (B.projectedNormalizedTargetBand Delta)| ≤
        (∑ j : Band, B.harmonicMass j * B.bandCenter j) *
          paperSharpNorm B.harmonicMass B.bandCenter
            (B.partition.center_ne_zero B.n_gt_one)
            (B.actualBandRegression xi hgamma hgap e) *
          ‖B.projectedNormalizedTargetBand Delta‖ := hD
      _ ≤ (∑ j : Band, B.harmonicMass j * B.bandCenter j) *
          (Creg * B.w) * Tband := by
        exact mul_le_mul
          (mul_le_mul_of_nonneg_left hreg hmoment)
          htargetBand (norm_nonneg _)
          (mul_nonneg hmoment hregNonneg)
  calc
    |-B.bandDPairing (B.actualBandRegression xi hgamma hgap e)
          (B.projectedNormalizedTargetBand Delta) +
        B.w * B.mainPart (B.normalizedTarget Delta) MainCoord.slow| ≤
      |B.bandDPairing (B.actualBandRegression xi hgamma hgap e)
          (B.projectedNormalizedTargetBand Delta)| +
        B.w * |B.mainPart (B.normalizedTarget Delta) MainCoord.slow| := by
      calc
        _ ≤ |-B.bandDPairing
              (B.actualBandRegression xi hgamma hgap e)
              (B.projectedNormalizedTargetBand Delta)| +
            |B.w * B.mainPart (B.normalizedTarget Delta)
              MainCoord.slow| := abs_add_le _ _
        _ = _ := by rw [abs_neg, abs_mul, abs_of_pos B.w_pos]
    _ ≤ (∑ j : Band, B.harmonicMass j * B.bandCenter j) *
          (Creg * B.w) * Tband + B.w * TslowCoord :=
      add_le_add hD'
        (mul_le_mul_of_nonneg_left htargetSlowCoord B.w_pos.le)

/-- Prime-fugacity estimate with an ordinary fast vector and the sharp
compensated slow coefficient estimate. -/
theorem effectivePrimeVelocity_norm_le_of_ordinaryFast_compensated
    [Nonempty Head] [Nonempty Band]
    (xi : B.ParamSpace) {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (e : B.RawBandGauge ≃ₗ[ℝ] B.RawBandGauge)
    (u : B.MainSpace)
    {Cfast Clambda Ccomp : ℝ}
    (hCfast : 0 ≤ Cfast) (hClambda : 0 ≤ Clambda)
    (hCcomp : 0 ≤ Ccomp)
    (hfast : ‖B.fastGaugeOfMain xi hgamma hgap e u‖ ≤ Cfast)
    (hlambda : |u MainCoord.slow / B.w| ≤ Clambda)
    (hcomp : ∀ p : BandPrime B.sampleData.n B.sampleData.W,
      |B.actualCompensatedCoefficient
        (B.actualBandRegression xi hgamma hgap e) p| ≤ Ccomp) :
    ‖fun p : BandPrime B.sampleData.n B.sampleData.W =>
        (B.rawGaugeOfMain u).1 (B.partition.band p) +
          (u MainCoord.slow / B.w) * B.primeDeviation p‖ ≤
      Cfast + Clambda * Ccomp := by
  have hbound : 0 ≤ Cfast + Clambda * Ccomp :=
    add_nonneg hCfast (mul_nonneg hClambda hCcomp)
  rw [pi_norm_le_iff_of_nonneg hbound]
  intro p
  rw [Real.norm_eq_abs,
    B.effectivePrimeCoefficient_fast_compensated xi hgamma hgap e u p]
  have hq :
      |(B.fastGaugeOfMain xi hgamma hgap e u).1
          (B.partition.band p)| ≤ Cfast := by
    calc
      |(B.fastGaugeOfMain xi hgamma hgap e u).1
          (B.partition.band p)| ≤
          ‖B.fastGaugeOfMain xi hgamma hgap e u‖ := by
        simpa only [Real.norm_eq_abs] using norm_le_pi_norm
          (B.fastGaugeOfMain xi hgamma hgap e u).1
          (B.partition.band p)
      _ ≤ Cfast := hfast
  calc
    |(B.fastGaugeOfMain xi hgamma hgap e u).1
          (B.partition.band p) +
        (u MainCoord.slow / B.w) *
          B.actualCompensatedCoefficient
            (B.actualBandRegression xi hgamma hgap e) p| ≤
      |(B.fastGaugeOfMain xi hgamma hgap e u).1
          (B.partition.band p)| +
        |u MainCoord.slow / B.w| *
          |B.actualCompensatedCoefficient
            (B.actualBandRegression xi hgamma hgap e) p| := by
      simpa only [abs_mul] using
        abs_add_le
          ((B.fastGaugeOfMain xi hgamma hgap e u).1
            (B.partition.band p))
          ((u MainCoord.slow / B.w) *
            B.actualCompensatedCoefficient
              (B.actualBandRegression xi hgamma hgap e) p)
    _ ≤ Cfast + Clambda * Ccomp :=
      add_le_add hq
        (mul_le_mul hlambda (hcomp p) (abs_nonneg _) hClambda)

/-- Norm-correct three-component estimate for Proposition 8.7.  The same
literal Schur equivalence carries an ordinary inverse estimate for the fast
target and a sharp inverse estimate for the slow regression. -/
theorem exactSchur_solution_component_bounds_of_ordinaryFast_twoStageTargets
    [Nonempty Head] [Nonempty Band]
    (xi : B.ParamSpace) {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (e : B.RawBandGauge ≃ₗ[ℝ] B.RawBandGauge)
    (he : ∀ q, e q = B.actualBandSchurLinearMap xi hgamma hgap q)
    (Delta : Band → ℝ)
    {CinvOrd Tband Vlower Tslow Ccomp
      CfastNuisance CslowNuisance : ℝ}
    (hCinvOrd : 0 ≤ CinvOrd) (hTband : 0 ≤ Tband)
    (hVlower : 0 < Vlower) (hTslow : 0 ≤ Tslow)
    (hCcomp : 0 ≤ Ccomp)
    (hinvOrd : ∀ v, ‖e.symm v‖ ≤ CinvOrd * ‖v‖)
    (htargetBand : ‖B.projectedNormalizedTargetBand Delta‖ ≤ Tband)
    (hvariance : Vlower ≤ B.actualTwoStageCompensatedVariance
      xi hgamma hgap e)
    (htargetSlow : |B.compensatedNormalizedTarget
      xi hgamma hgap e Delta| ≤ Tslow)
    (hcomp : ∀ p : BandPrime B.sampleData.n B.sampleData.W,
      |B.actualCompensatedCoefficient
        (B.actualBandRegression xi hgamma hgap e) p| ≤ Ccomp)
    (hfastNuisance : ‖B.targetFastNuisanceCoefficient
      xi hgamma hgap e Delta‖ ≤ CfastNuisance)
    (hslowNuisance : ‖B.actualTwoStageNuisanceCoefficient
      xi hgamma hgap e‖ ≤ CslowNuisance)
    (u : B.MainSpace)
    (hu : B.exactSchurCovarianceOperator xi hgamma hgap u =
      B.mainPart (B.normalizedTarget Delta)) :
    ‖fun p : BandPrime B.sampleData.n B.sampleData.W =>
        (B.rawGaugeOfMain u).1 (B.partition.band p) +
          (u MainCoord.slow / B.w) * B.primeDeviation p‖ ≤
        CinvOrd * Tband + (Tslow / Vlower) * Ccomp ∧
      ‖B.exactNuisanceRegression xi hgamma hgap u‖ ≤
        CfastNuisance + (Tslow / Vlower) * CslowNuisance ∧
      |u MainCoord.slow| ≤ B.w * (Tslow / Vlower) := by
  have hfast : ‖B.fastGaugeOfMain xi hgamma hgap e u‖ ≤
      CinvOrd * Tband := by
    calc
      ‖B.fastGaugeOfMain xi hgamma hgap e u‖ ≤
          CinvOrd * ‖B.projectedNormalizedTargetBand Delta‖ :=
        B.fastGauge_norm_le_of_ordinary_inverse
          xi hgamma hgap e he hinvOrd Delta u hu
      _ ≤ CinvOrd * Tband :=
        mul_le_mul_of_nonneg_left htargetBand hCinvOrd
  have hlambda : |u MainCoord.slow / B.w| ≤ Tslow / Vlower :=
    B.abs_slow_div_le_of_variance_target_bounds
      xi hgamma hgap e he Delta u hu hVlower hvariance
      hTslow htargetSlow
  have hClambda : 0 ≤ Tslow / Vlower :=
    div_nonneg hTslow hVlower.le
  have hprime := B.effectivePrimeVelocity_norm_le_of_ordinaryFast_compensated
    xi hgamma hgap e u
    (mul_nonneg hCinvOrd hTband) hClambda hCcomp hfast hlambda hcomp
  have hnuisance := B.exactNuisanceRegression_norm_le_of_twoStage
    xi hgamma hgap e he Delta u hu hClambda
      hfastNuisance hlambda hslowNuisance
  have hslow := B.abs_slow_le_of_variance_target_bounds
    xi hgamma hgap e he Delta u hu hVlower hvariance
      hTslow htargetSlow
  exact ⟨hprime, hnuisance, hslow⟩

end BridgeData

end

end Erdos390.Full.PaperBridgeFit

end

/- Source module: Erdos390.Full.PaperProposition87Assembly -/
section


/-!
# Finite assembly layer for Proposition 8.7

This file assembles the already proved finite exponential-family, ODE,
endpoint, marked-row, and feasibility statements in the literal effective
norm used in the paper.  It deliberately does not assert the analytic
estimates of Lemmas 8.4 and 8.6: the three hypotheses `hgap`, `hvelocity`,
and `hmarkedRow` are exactly the uniform analytic outputs which those lemmas
must supply on the effective box chosen before the path.

The conclusion is not packaged as an abstract contract.  It exhibits the
actual bridge path and states the individual band, physical, head,
logarithmic, marked-prime, natural-coordinate feasibility, frozen-coordinate,
mass, and integer-quota conclusions directly.
-/

open scoped BigOperators
open Metric Set

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

namespace BridgeData

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]
  (B : BridgeData Head Band)





theorem endpoint_preserves_ordinaryLog [Nonempty Head]
    (Delta : Band → ℝ) (xi0 xi1 : B.ParamSpace)
    (hendpoint : B.vectorFamily.vectorMoment xi1 =
      B.vectorFamily.vectorMoment xi0 + B.targetVector Delta) :
    B.paperMoment B.ordinaryLogScore xi1 =
      B.paperMoment B.ordinaryLogScore xi0 := by
  have hpoint (m : B.sampleData.Sample) :
      B.ordinaryLogScore m =
        B.physicalScore m + Real.log (B.sampleData.n : ℝ) := by
    have hm : (B.sampleData.value m : ℝ) ≠ 0 := by
      exact_mod_cast Nat.ne_of_gt (B.sampleData.value_pos m)
    have hn : (B.sampleData.n : ℝ) ≠ 0 := by
      exact_mod_cast Nat.ne_of_gt (Nat.zero_lt_of_lt B.n_gt_one)
    rw [ordinaryLogScore, physicalScore, Real.log_div hm hn]
    ring
  have hexpand (xi : B.ParamSpace) :
      B.paperMoment B.ordinaryLogScore xi =
        B.paperMoment B.physicalScore xi +
          B.q * Real.log (B.sampleData.n : ℝ) := by
    calc
      B.paperMoment B.ordinaryLogScore xi =
          B.paperMoment (fun m =>
            B.physicalScore m + Real.log (B.sampleData.n : ℝ)) xi := by
        congr 1
        funext m
        exact hpoint m
      _ = B.paperMoment B.physicalScore xi +
          B.paperMoment (fun _ => Real.log (B.sampleData.n : ℝ)) xi :=
        B.paperMoment_add _ _ xi
      _ = B.paperMoment B.physicalScore xi +
          B.q * Real.log (B.sampleData.n : ℝ) := by
        rw [B.paperMoment_const]
  rw [hexpand, hexpand,
    B.endpoint_preserves_physical Delta xi0 xi1 hendpoint]

/--
Finite, statement-level assembly of the physically centered
fixed-partition fit.

The analytic input is limited to a covariance gap, a dimension-free inverse
velocity estimate, and the marked covariance row, all uniform on the same
preselected effective ball.  The target and baseline ledger hypotheses are
the data entering Proposition 8.7 before the nonlinear fit.  In particular,
the theorem neither assumes a path nor assumes any endpoint, feasibility,
support, or quota conclusion.
-/
theorem exists_physicallyCenteredFixedPartitionFit_of_analyticOutputs
    [Nonempty Head]
    {Fixed : Type*} [Fintype Fixed]
    (hcompat : B.HasPrimeLogCompatibility)
    (Delta : Band → ℝ)
    (a speed : NNReal) {gamma : ℝ}
    (hgamma : 0 < gamma)
    (hgap : ∀ z ∈ closedBall (0 : B.EffectiveParamSpace) (a : ℝ),
      B.vectorFamily.HasCovarianceGap gamma (B.effectiveParamEquiv z))
    (hvelocity : ∀ z ∈ closedBall (0 : B.EffectiveParamSpace) (a : ℝ),
      ‖B.effectiveParamEquiv.symm
        (B.vectorFamily.vectorField (B.targetVector Delta)
          (B.effectiveParamEquiv z))‖ ≤ (speed : ℝ))
    (hmargin : speed ≤ a)
    (monitoredPrimes : Finset ℕ)
    (Crow : ℝ) (hCrow : 0 ≤ Crow)
    (hmarkedRow : ∀ p ∈ monitoredPrimes,
      ∀ z ∈ closedBall (0 : B.EffectiveParamSpace) (a : ℝ),
        |B.vectorFamily.scalarFamily.covariance
            (B.markedValuation p)
            (fun m => B.vectorFamily.scalarFamily.score m
              (B.vectorFamily.vectorField (B.targetVector Delta)
                (B.effectiveParamEquiv z)))
            (B.effectiveParamEquiv z)| ≤ Crow / (p : ℝ))
    (markedTarget : ℕ → ℝ)
    (N Cinitial Cmass : ℝ)
    (hprimePos : ∀ p ∈ monitoredPrimes, 0 < p)
    (hqMass : B.q ≤ Cmass * N)
    (hinitialMarked : ∀ p ∈ monitoredPrimes,
      |markedTarget p - B.paperMoment (B.markedValuation p) 0| ≤
        Cinitial * N / ((p : ℝ) * B.L))
    (fixedValue : Fixed → ℕ) (fixedWeight : Fixed → ℝ)
    (quota : ℤ)
    (hquota : (quota : ℝ) = (∑ f, fixedWeight f) + B.q)
    {C Cfixed Cactive : ℝ}
    (hC : 1 ≤ C) (hW : 1 < B.sampleData.W)
    (hhi : ∀ sigma, B.sampleData.hi sigma ≤
      ArithmeticModel.physicalBound C B.sampleData.n)
    (hsep : B.sampleData.HeadPatternsSeparated)
    (hfrozenFeasible : ∀ x,
      frozenAmbientWeight fixedValue fixedWeight x ∈ Set.Icc (0 : ℝ) 1)
    (hfrozenLedger : ∀ m : B.sampleData.Sample,
      frozenAmbientWeight fixedValue fixedWeight
        (B.sampleData.value m) ≤ Cfixed / B.L)
    (hactiveLedger : ∀ m : B.sampleData.Sample,
      B.baseline.baseWeight m ≤ Cactive / B.L)
    (hlarge : Cfixed +
      Real.exp (2 *
        ((PaperStatisticNorm.valuationLogCoefficient C B.sampleData.W +
          B.nuisanceStatisticCoefficient C) * (3 * (a : ℝ)))) *
            Cactive ≤ B.L) :
    ∃ path : ℝ → B.ParamSpace,
      path 0 = 0 ∧
      (∀ t ∈ Icc (0 : ℝ) 1,
        B.effectiveParamEquiv.symm (path t) ∈
          closedBall (0 : B.EffectiveParamSpace) (a : ℝ)) ∧
      (∀ t ∈ Icc (0 : ℝ) 1,
        B.paperEffectiveSize (path t) ≤ 3 * (a : ℝ)) ∧
      (∀ t ∈ Icc (0 : ℝ) 1,
        HasDerivWithinAt path
          (B.vectorFamily.vectorField (B.targetVector Delta) (path t))
          (Icc (0 : ℝ) 1) t) ∧
      (∀ j : Band,
        B.paperMoment (B.bandScore j) (path 1) =
          B.paperMoment (B.bandScore j) 0 + Delta j) ∧
      B.paperMoment B.physicalScore (path 1) =
        B.paperMoment B.physicalScore 0 ∧
      B.paperMoment B.ordinaryLogScore (path 1) =
        B.paperMoment B.ordinaryLogScore 0 ∧
      (∀ h : B.HeadIndex,
        B.paperMoment (B.headIndicator h.1) (path 1) =
          B.paperMoment (B.headIndicator h.1) 0) ∧
      B.paperMoment B.primeLogScore (path 1) =
        B.paperMoment B.primeLogScore 0 ∧
      (∀ p ∈ monitoredPrimes,
        |markedTarget p - B.paperMoment (B.markedValuation p) (path 1)| ≤
          (Cinitial + Cmass * Crow) * N / ((p : ℝ) * B.L)) ∧
      (∀ t ∈ Icc (0 : ℝ) 1, ∀ x : ℕ,
        B.ambientCombinedWeight
            (frozenAmbientWeight fixedValue fixedWeight) (path t) x ∈
          Set.Icc (0 : ℝ) 1) ∧
      (∀ t ∈ Icc (0 : ℝ) 1, ∀ f : Fixed,
        B.combinedWeight fixedWeight (path t) (Sum.inl f) =
          B.combinedWeight fixedWeight 0 (Sum.inl f)) ∧
      (∀ t ∈ Icc (0 : ℝ) 1,
        (∑ m : B.sampleData.Sample,
          B.activeCoordinateWeight (path t) m) = B.q) ∧
      (∀ t ∈ Icc (0 : ℝ) 1,
        (∑ x : Fixed ⊕ B.sampleData.Sample,
          B.combinedWeight fixedWeight (path t) x) = (quota : ℝ)) := by
  obtain ⟨path, hpathZero, hball, hsize, hderiv, hraw⟩ :=
    B.exists_paperFit_on_preselectedEffectiveBall Delta a speed hgamma
      hgap hvelocity hmargin
  have hendpoint : B.vectorFamily.vectorMoment (path 1) =
      B.vectorFamily.vectorMoment 0 + B.targetVector Delta :=
    (B.endpoint_iff_paperMoments Delta 0 (path 1)).mpr hraw
  have hbands : ∀ j : Band,
      B.paperMoment (B.bandScore j) (path 1) =
        B.paperMoment (B.bandScore j) 0 + Delta j :=
    B.endpoint_recovers_all_bandMoments_of_compatibility
      hcompat Delta 0 (path 1) hendpoint
  have hphysical : B.paperMoment B.physicalScore (path 1) =
      B.paperMoment B.physicalScore 0 :=
    B.endpoint_preserves_physical Delta 0 (path 1) hendpoint
  have hordinaryLog : B.paperMoment B.ordinaryLogScore (path 1) =
      B.paperMoment B.ordinaryLogScore 0 :=
    B.endpoint_preserves_ordinaryLog Delta 0 (path 1) hendpoint
  have hheads : ∀ h : B.HeadIndex,
      B.paperMoment (B.headIndicator h.1) (path 1) =
        B.paperMoment (B.headIndicator h.1) 0 :=
    fun h => B.endpoint_preserves_headIndicator Delta 0 (path 1) hendpoint h
  have hlog : B.paperMoment B.primeLogScore (path 1) =
      B.paperMoment B.primeLogScore 0 :=
    B.endpoint_preserves_primeLogScore_of_compatibility
      hcompat Delta 0 (path 1) hendpoint
  have hmarked : ∀ p ∈ monitoredPrimes,
      |markedTarget p - B.paperMoment (B.markedValuation p) (path 1)| ≤
        (Cinitial + Cmass * Crow) * N / ((p : ℝ) * B.L) := by
    intro p hp
    apply B.abs_target_sub_markedMoment_one_le_of_initial_rate
      p (hprimePos p hp) path
      (fun t => B.vectorFamily.vectorField (B.targetVector Delta) (path t))
      (markedTarget p) N Cinitial Cmass Crow hCrow hqMass hderiv
    · intro t ht
      let z : B.EffectiveParamSpace := B.effectiveParamEquiv.symm (path t)
      have hz : z ∈ closedBall (0 : B.EffectiveParamSpace) (a : ℝ) :=
        hball t ht
      have hpathEq : B.effectiveParamEquiv z = path t :=
        B.effectiveParamEquiv.apply_symm_apply (path t)
      rw [← hpathEq]
      exact hmarkedRow p hp z hz
    · simpa only [hpathZero] using hinitialMarked p hp
  have hfeasible : ∀ t ∈ Icc (0 : ℝ) 1, ∀ x : ℕ,
      B.ambientCombinedWeight
          (frozenAmbientWeight fixedValue fixedWeight) (path t) x ∈
        Set.Icc (0 : ℝ) 1 := by
    intro t ht
    exact B.ambientCombinedWeight_mem_Icc_of_paperEffectiveSize
      hC hW hhi hsep
      (frozenAmbientWeight fixedValue fixedWeight)
      hfrozenFeasible (path t) (hsize t ht)
      hfrozenLedger hactiveLedger hlarge
  have hfixed : ∀ t ∈ Icc (0 : ℝ) 1, ∀ f : Fixed,
      B.combinedWeight fixedWeight (path t) (Sum.inl f) =
        B.combinedWeight fixedWeight 0 (Sum.inl f) := by
    intro t ht f
    exact B.combinedWeight_fixed_unchanged fixedWeight (path t) 0 f
  have hmass : ∀ t ∈ Icc (0 : ℝ) 1,
      (∑ m : B.sampleData.Sample,
        B.activeCoordinateWeight (path t) m) = B.q := by
    intro t ht
    exact B.sum_activeCoordinateWeight (path t)
  have hquotaPath : ∀ t ∈ Icc (0 : ℝ) 1,
      (∑ x : Fixed ⊕ B.sampleData.Sample,
        B.combinedWeight fixedWeight (path t) x) = (quota : ℝ) := by
    intro t ht
    exact B.sum_combinedWeight_eq_integerQuota
      fixedWeight quota hquota (path t)
  exact ⟨path, hpathZero, hball, hsize, hderiv, hbands, hphysical,
    hordinaryLog, hheads, hlog, hmarked, hfeasible, hfixed, hmass,
    hquotaPath⟩

/--
Proposition 8.7 with the full covariance-gap input eliminated in favor of
the two literal analytic Schur blocks.  The nuisance hypothesis is the
finite covariance coercivity of the actual head/physical statistics, and
the main hypothesis is the coercivity of the actual exact-regression Schur
residual.  The full Jacobian gap used by the ODE is a conclusion, with one
constant valid on the whole preselected effective ball.

The effective-velocity estimate is no longer assumed as a conclusion about
the assembled vector field.  Instead the theorem receives the three literal
component bounds for every solution of the actual Schur equation (effective
prime fugacity, nuisance coefficient, and stored slow coordinate) and proves
the velocity bound from the exact block identity.  The marked row remains an
explicit quantitative Lemma 8.6 output used for the post-bridge primewise
rate.
-/
theorem exists_physicallyCenteredFixedPartitionFit_of_exactSchurOutputs
    [Nonempty Head]
    {Fixed : Type*} [Fintype Fixed]
    (hcompat : B.HasPrimeLogCompatibility)
    (Delta : Band → ℝ)
    (a speed : NNReal) (gammaMain gammaNuisance : ℝ)
    (hgammaMain : 0 < gammaMain)
    (hgammaNuisance : 0 < gammaNuisance)
    (hGamma : ∀ z ∈ closedBall (0 : B.EffectiveParamSpace) (a : ℝ),
      ∀ v, gammaNuisance * ‖v‖ ^ 2 ≤
        inner ℝ v (B.nuisanceCovarianceOperator
          (B.effectiveParamEquiv z) v))
    (hSchur : ∀ z (hz : z ∈
        closedBall (0 : B.EffectiveParamSpace) (a : ℝ)) u,
      gammaMain * ‖u‖ ^ 2 ≤
        inner ℝ
          (B.schurResidual
            (B.exactNuisanceRegression (B.effectiveParamEquiv z)
              hgammaNuisance (hGamma z hz)) u)
          (B.covarianceOperator (B.effectiveParamEquiv z)
            (B.schurResidual
              (B.exactNuisanceRegression (B.effectiveParamEquiv z)
                hgammaNuisance (hGamma z hz)) u)))
    (hprime : ∀ z (hz : z ∈
        closedBall (0 : B.EffectiveParamSpace) (a : ℝ)) u,
      B.exactSchurCovarianceOperator (B.effectiveParamEquiv z)
          hgammaNuisance (hGamma z hz) u =
          B.mainPart (B.normalizedTarget Delta) →
        ‖fun p : ArithmeticBandGeometry.BandPrime
              B.sampleData.n B.sampleData.W ↦
            (B.rawGaugeOfMain u).1 (B.partition.band p) +
              (u MainCoord.slow / B.w) * B.primeDeviation p‖ ≤
          (speed : ℝ))
    (hnuisance : ∀ z (hz : z ∈
        closedBall (0 : B.EffectiveParamSpace) (a : ℝ)) u,
      B.exactSchurCovarianceOperator (B.effectiveParamEquiv z)
          hgammaNuisance (hGamma z hz) u =
          B.mainPart (B.normalizedTarget Delta) →
        ‖B.exactNuisanceRegression (B.effectiveParamEquiv z)
          hgammaNuisance (hGamma z hz) u‖ ≤ (speed : ℝ))
    (hslow : ∀ z (hz : z ∈
        closedBall (0 : B.EffectiveParamSpace) (a : ℝ)) u,
      B.exactSchurCovarianceOperator (B.effectiveParamEquiv z)
          hgammaNuisance (hGamma z hz) u =
          B.mainPart (B.normalizedTarget Delta) →
        |u MainCoord.slow| ≤ (speed : ℝ))
    (hmargin : speed ≤ a)
    (monitoredPrimes : Finset ℕ)
    (Crow : ℝ) (hCrow : 0 ≤ Crow)
    (hmarkedRow : ∀ p ∈ monitoredPrimes,
      ∀ z ∈ closedBall (0 : B.EffectiveParamSpace) (a : ℝ),
        |B.vectorFamily.scalarFamily.covariance
            (B.markedValuation p)
            (fun m => B.vectorFamily.scalarFamily.score m
              (B.vectorFamily.vectorField (B.targetVector Delta)
                (B.effectiveParamEquiv z)))
            (B.effectiveParamEquiv z)| ≤ Crow / (p : ℝ))
    (markedTarget : ℕ → ℝ)
    (N Cinitial Cmass : ℝ)
    (hprimePos : ∀ p ∈ monitoredPrimes, 0 < p)
    (hqMass : B.q ≤ Cmass * N)
    (hinitialMarked : ∀ p ∈ monitoredPrimes,
      |markedTarget p - B.paperMoment (B.markedValuation p) 0| ≤
        Cinitial * N / ((p : ℝ) * B.L))
    (fixedValue : Fixed → ℕ) (fixedWeight : Fixed → ℝ)
    (quota : ℤ)
    (hquota : (quota : ℝ) = (∑ f, fixedWeight f) + B.q)
    {C Cfixed Cactive : ℝ}
    (hC : 1 ≤ C) (hW : 1 < B.sampleData.W)
    (hhi : ∀ sigma, B.sampleData.hi sigma ≤
      ArithmeticModel.physicalBound C B.sampleData.n)
    (hsep : B.sampleData.HeadPatternsSeparated)
    (hfrozenFeasible : ∀ x,
      frozenAmbientWeight fixedValue fixedWeight x ∈ Set.Icc (0 : ℝ) 1)
    (hfrozenLedger : ∀ m : B.sampleData.Sample,
      frozenAmbientWeight fixedValue fixedWeight
        (B.sampleData.value m) ≤ Cfixed / B.L)
    (hactiveLedger : ∀ m : B.sampleData.Sample,
      B.baseline.baseWeight m ≤ Cactive / B.L)
    (hlarge : Cfixed +
      Real.exp (2 *
        ((PaperStatisticNorm.valuationLogCoefficient C B.sampleData.W +
          B.nuisanceStatisticCoefficient C) * (3 * (a : ℝ)))) *
            Cactive ≤ B.L) :
    ∃ path : ℝ → B.ParamSpace,
      path 0 = 0 ∧
      (∀ t ∈ Icc (0 : ℝ) 1,
        B.effectiveParamEquiv.symm (path t) ∈
          closedBall (0 : B.EffectiveParamSpace) (a : ℝ)) ∧
      (∀ t ∈ Icc (0 : ℝ) 1,
        B.paperEffectiveSize (path t) ≤ 3 * (a : ℝ)) ∧
      (∀ t ∈ Icc (0 : ℝ) 1,
        HasDerivWithinAt path
          (B.vectorFamily.vectorField (B.targetVector Delta) (path t))
          (Icc (0 : ℝ) 1) t) ∧
      (∀ j : Band,
        B.paperMoment (B.bandScore j) (path 1) =
          B.paperMoment (B.bandScore j) 0 + Delta j) ∧
      B.paperMoment B.physicalScore (path 1) =
        B.paperMoment B.physicalScore 0 ∧
      B.paperMoment B.ordinaryLogScore (path 1) =
        B.paperMoment B.ordinaryLogScore 0 ∧
      (∀ h : B.HeadIndex,
        B.paperMoment (B.headIndicator h.1) (path 1) =
          B.paperMoment (B.headIndicator h.1) 0) ∧
      B.paperMoment B.primeLogScore (path 1) =
        B.paperMoment B.primeLogScore 0 ∧
      (∀ p ∈ monitoredPrimes,
        |markedTarget p - B.paperMoment (B.markedValuation p) (path 1)| ≤
          (Cinitial + Cmass * Crow) * N / ((p : ℝ) * B.L)) ∧
      (∀ t ∈ Icc (0 : ℝ) 1, ∀ x : ℕ,
        B.ambientCombinedWeight
            (frozenAmbientWeight fixedValue fixedWeight) (path t) x ∈
          Set.Icc (0 : ℝ) 1) ∧
      (∀ t ∈ Icc (0 : ℝ) 1, ∀ f : Fixed,
        B.combinedWeight fixedWeight (path t) (Sum.inl f) =
          B.combinedWeight fixedWeight 0 (Sum.inl f)) ∧
      (∀ t ∈ Icc (0 : ℝ) 1,
        (∑ m : B.sampleData.Sample,
          B.activeCoordinateWeight (path t) m) = B.q) ∧
      (∀ t ∈ Icc (0 : ℝ) 1,
        (∑ x : Fixed ⊕ B.sampleData.Sample,
          B.combinedWeight fixedWeight (path t) x) = (quota : ℝ)) := by
  let gammaFull := min gammaMain gammaNuisance /
    (3 + 2 * (B.canonicalCrossBound / gammaNuisance) ^ 2)
  have hden : 0 < 3 + 2 *
      (B.canonicalCrossBound / gammaNuisance) ^ 2 := by positivity
  have hgammaFull : 0 < gammaFull := by
    exact div_pos (lt_min hgammaMain hgammaNuisance) hden
  have hfull : ∀ z ∈
      closedBall (0 : B.EffectiveParamSpace) (a : ℝ),
      B.vectorFamily.HasCovarianceGap gammaFull
        (B.effectiveParamEquiv z) := by
    intro z hz
    exact B.hasCovarianceGap_of_uniform_exactSchur
      (B.effectiveParamEquiv z) gammaMain gammaNuisance
      hgammaMain hgammaNuisance (hGamma z hz) (hSchur z hz)
  have hvelocity : ∀ z ∈
      closedBall (0 : B.EffectiveParamSpace) (a : ℝ),
      ‖B.effectiveParamEquiv.symm
        (B.vectorFamily.vectorField (B.targetVector Delta)
          (B.effectiveParamEquiv z))‖ ≤ (speed : ℝ) := by
    intro z hz
    exact B.effectiveVelocity_le_of_exactSchur_solution_component_bounds
      (B.effectiveParamEquiv z) Delta hgammaFull (hfull z hz)
      hgammaNuisance (hGamma z hz)
      (hprime z hz) (hnuisance z hz) (hslow z hz)
  exact B.exists_physicallyCenteredFixedPartitionFit_of_analyticOutputs
    hcompat Delta a speed hgammaFull hfull hvelocity hmargin
    monitoredPrimes Crow hCrow hmarkedRow markedTarget
    N Cinitial Cmass hprimePos hqMass hinitialMarked
    fixedValue fixedWeight quota hquota hC hW hhi hsep
    hfrozenFeasible hfrozenLedger hactiveLedger hlarge

end BridgeData

end

end Erdos390.Full.PaperBridgeFit

end

/- Source module: Erdos390.Full.PaperHeadPrimeMarkedExact -/
section


/-!
# Exact fixed-head-prime rows

For `p ≤ W`, the canonical head pattern fixes the full `p`-adic valuation
pointwise on every structured cell.  Thus the marked valuation is literally
a function of the finite head tag.  The ODE endpoint preserves its moment
exactly; no moving-prime `C / p` estimate or limiting argument is needed.
-/

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

open ArithmeticModel

namespace BridgeData

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]
  (B : BridgeData Head Band)

/-- A fixed head-prime valuation is exactly the head-tag function carrying
the prescribed exponent. -/
theorem markedValuation_eq_headFunctionScore_of_exactHeadPrimes
    (hhead : ∀ h : Head, ∀ r : ℕ,
      r ∈ (B.sampleData.pattern h).primes ↔
        r.Prime ∧ r ≤ B.sampleData.W)
    {p : ℕ} (hp : p.Prime) (hpW : p ≤ B.sampleData.W)
    (m : B.sampleData.Sample) :
    B.markedValuation p m =
      B.headFunctionScore
        (fun h ↦ ((B.sampleData.pattern h).exponent p : ℝ)) m := by
  have hmem : p ∈
      (B.sampleData.pattern (B.sampleData.cellOf m).1).primes :=
    (hhead (B.sampleData.cellOf m).1 p).2 ⟨hp, hpW⟩
  have hmatch := B.sampleData.value_matches_head m p hmem
  unfold markedValuation headFunctionScore ArithmeticModel.valuation
  simpa only using congrArg (fun k : ℕ ↦ (k : ℝ)) hmatch



/-- Endpoint preservation can also be read directly from the individual
head-indicator moment equations emitted by the Proposition 8.7 assembly. -/
theorem paperMoment_headFunction_eq_of_headIndicatorMoments
    [Nonempty Head]
    (phi : Head → ℝ) (xi0 xi1 : B.ParamSpace)
    (hheads : ∀ h : B.HeadIndex,
      B.paperMoment (B.headIndicator h.1) xi1 =
        B.paperMoment (B.headIndicator h.1) xi0) :
    B.paperMoment (B.headFunctionScore phi) xi1 =
      B.paperMoment (B.headFunctionScore phi) xi0 := by
  have hexpand (xi : B.ParamSpace) :
      B.paperMoment (B.headFunctionScore phi) xi =
        B.q * phi B.referenceHead +
          ∑ h : B.HeadIndex,
            (phi h.1 - phi B.referenceHead) *
              B.paperMoment (B.headIndicator h.1) xi := by
    calc
      B.paperMoment (B.headFunctionScore phi) xi =
          B.paperMoment (fun m ↦ phi B.referenceHead +
            ∑ h : B.HeadIndex,
              (phi h.1 - phi B.referenceHead) *
                B.headIndicator h.1 m) xi := by
            congr 1
            funext m
            exact B.headFunctionScore_decomposition phi m
      _ = B.paperMoment (fun _ ↦ phi B.referenceHead) xi +
          B.paperMoment (fun m ↦ ∑ h : B.HeadIndex,
            (phi h.1 - phi B.referenceHead) *
              B.headIndicator h.1 m) xi := by
            unfold paperMoment FiniteExponentialFamily.moment
            rw [← Finset.sum_add_distrib]
            apply Finset.sum_congr rfl
            intro m hm
            ring
      _ = B.q * phi B.referenceHead +
          ∑ h : B.HeadIndex,
            (phi h.1 - phi B.referenceHead) *
              B.paperMoment (B.headIndicator h.1) xi := by
            rw [B.paperMoment_const, B.paperMoment_fintype_sum]
            apply congrArg₂ (· + ·) rfl
            apply Finset.sum_congr rfl
            intro h hh
            exact B.paperMoment_const_mul
              (phi h.1 - phi B.referenceHead)
              (B.headIndicator h.1) xi
  rw [hexpand, hexpand]
  apply congrArg₂ (· + ·) rfl
  apply Finset.sum_congr rfl
  intro h hh
  rw [hheads h]

/-- The fixed-head valuation conclusion can therefore be appended to the
literal path conclusion of the finite ODE assembly without reconstructing
the hidden vector-moment endpoint. -/
theorem headPrimeMarkedMoment_eq_of_headIndicatorMoments
    [Nonempty Head]
    (hhead : ∀ h : Head, ∀ r : ℕ,
      r ∈ (B.sampleData.pattern h).primes ↔
        r.Prime ∧ r ≤ B.sampleData.W)
    (xi0 xi1 : B.ParamSpace)
    (hheads : ∀ h : B.HeadIndex,
      B.paperMoment (B.headIndicator h.1) xi1 =
        B.paperMoment (B.headIndicator h.1) xi0)
    {p : ℕ} (hp : p.Prime) (hpW : p ≤ B.sampleData.W) :
    B.paperMoment (B.markedValuation p) xi1 =
      B.paperMoment (B.markedValuation p) xi0 := by
  let phi : Head → ℝ := fun h ↦
    ((B.sampleData.pattern h).exponent p : ℝ)
  have hpoint : B.markedValuation p = B.headFunctionScore phi := by
    funext m
    exact B.markedValuation_eq_headFunctionScore_of_exactHeadPrimes
      hhead hp hpW m
  rw [hpoint]
  exact B.paperMoment_headFunction_eq_of_headIndicatorMoments
    phi xi0 xi1 hheads






end BridgeData

end

end Erdos390.Full.PaperBridgeFit

end

/- Source module: Erdos390.Full.PaperProposition87CanonicalTwoStageAssembly -/
section


/-!
# Proposition 8.7 with canonical nuisance gap and exact two-stage solve

This is the finite terminal assembly after removing the abstract nuisance
gap, main Schur gap, and the three solution-component hypotheses from the
older exact-Schur interface.  The remaining quantitative inputs are the
literal uniform analytic estimates: the ordinary raw-sup inverse used for
the fast target, the sharp weighted inverse used for slow regression,
compensated slow variance, the slow-column and target/nuisance rows, and
the marked row.  The two inverse estimates concern the same Schur
equivalence; they are deliberately kept separate because the moving low
cell prevents one from deriving the ordinary estimate from the sharp one.
Both first-stage regression and nuisance-coefficient bounds are derived.
-/

open scoped BigOperators
open Metric Set

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

open ArithmeticModel ArithmeticBandGeometry PaperGuardCensus
open PaperWeightedInverseExport
open MovingLowGaugeTransfer

namespace BridgeData

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]
  (B : BridgeData Head Band)

/-- Fully specialized finite assembly.  The explicit speed comparisons are
algebraic choices of the preselected ODE radius; they are not analytic
conclusions about the unknown path. -/
theorem exists_physicallyCenteredFixedPartitionFit_of_canonicalTwoStageOutputs
    [Nonempty Head] [Nonempty Band]
    {Fixed : Type*} [Fintype Fixed]
    (I : PhysicalIntervals) {U : ℝ}
    (hU : 1 ≤ U)
    (hlowerOne : ∀ sigma, 1 ≤ I.lower sigma)
    (hupperU : ∀ sigma, I.upper sigma ≤ U)
    (hlo : ∀ sigma, B.sampleData.lo sigma =
      physicalBound (I.lower sigma) B.sampleData.n)
    (hhiIntervals : ∀ sigma, B.sampleData.hi sigma =
      physicalBound (I.upper sigma) B.sampleData.n)
    (T : BarycentricTarget B.sampleData)
    (hbaseline : B.baseline = T.baseline)
    (hW : 1 < B.sampleData.W)
    (hcompat : B.HasPrimeLogCompatibility)
    (hhead : ∀ h : Head, ∀ p : ℕ,
      p ∈ (B.sampleData.pattern h).primes ↔
        p.Prime ∧ p ≤ B.sampleData.W)
    (Delta : Band → ℝ)
    (a speed : NNReal)
    {Cinv CinvOrd gammaSlow CrightRow Tband TslowCoord Ccomp
      CfastNuisance CslowNuisance : ℝ}
    (hCinv : 0 < Cinv) (hCinvOrd : 0 ≤ CinvOrd)
    (hgammaSlow : 0 < gammaSlow)
    (hCrightRow : 0 ≤ CrightRow) (hTband : 0 ≤ Tband)
    (hTslowCoord : 0 ≤ TslowCoord) (hCcomp : 0 ≤ Ccomp)
    (e : ∀ (z : B.EffectiveParamSpace),
      z ∈ closedBall (0 : B.EffectiveParamSpace) (a : ℝ) →
        B.RawBandGauge ≃ₗ[ℝ] B.RawBandGauge)
    (he : ∀ (z : B.EffectiveParamSpace)
        (hz : z ∈ closedBall (0 : B.EffectiveParamSpace) (a : ℝ)) q,
      e z hz q =
        B.actualBandSchurLinearMap (B.effectiveParamEquiv z)
          (B.canonicalEffectiveNuisanceGamma_pos I U (3 * (a : ℝ)) T)
          (B.canonicalEffectiveNuisanceGap_on_closedBall I a hU
            hlowerOne hupperU hlo hhiIntervals T hbaseline
            hW z hz) q)
    (hinv : ∀ (z : B.EffectiveParamSpace)
        (hz : z ∈ closedBall (0 : B.EffectiveParamSpace) (a : ℝ)) v,
      paperSharpNorm B.harmonicMass B.bandCenter
          (B.partition.center_ne_zero B.n_gt_one) ((e z hz).symm v) ≤
        Cinv * paperSharpNorm B.harmonicMass B.bandCenter
          (B.partition.center_ne_zero B.n_gt_one) v)
    (hinvOrd : ∀ (z : B.EffectiveParamSpace)
        (hz : z ∈ closedBall (0 : B.EffectiveParamSpace) (a : ℝ)) v,
      ‖(e z hz).symm v‖ ≤ CinvOrd * ‖v‖)
    (hslowVariance : ∀ (z : B.EffectiveParamSpace)
        (hz : z ∈ closedBall (0 : B.EffectiveParamSpace) (a : ℝ)),
      gammaSlow * B.w ^ 2 ≤
        B.actualTwoStageCompensatedVariance (B.effectiveParamEquiv z)
          (B.canonicalEffectiveNuisanceGamma_pos I U (3 * (a : ℝ)) T)
          (B.canonicalEffectiveNuisanceGap_on_closedBall I a hU
            hlowerOne hupperU hlo hhiIntervals T hbaseline
            hW z hz) (e z hz))
    (hregRightRow : ∀ (z : B.EffectiveParamSpace)
        (hz : z ∈ closedBall (0 : B.EffectiveParamSpace) (a : ℝ)) j,
      |B.normalizedBandCovarianceRow (B.effectiveParamEquiv z)
        (B.nuisanceResidualScore (B.effectiveParamEquiv z)
          (B.canonicalEffectiveNuisanceGamma_pos I U (3 * (a : ℝ)) T)
          (B.canonicalEffectiveNuisanceGap_on_closedBall I a hU
            hlowerOne hupperU hlo hhiIntervals T hbaseline
            hW z hz) B.slowScore) j| ≤
        (CrightRow * B.w) * B.bandCenter j)
    (htargetBand : ‖B.projectedNormalizedTargetBand Delta‖ ≤ Tband)
    (htargetSlowCoord :
      |B.mainPart (B.normalizedTarget Delta) MainCoord.slow| ≤
        TslowCoord)
    (hcomp : ∀ (z : B.EffectiveParamSpace)
        (hz : z ∈ closedBall (0 : B.EffectiveParamSpace) (a : ℝ))
        (p : BandPrime B.sampleData.n B.sampleData.W),
      |B.actualCompensatedCoefficient
        (B.actualBandRegression (B.effectiveParamEquiv z)
          (B.canonicalEffectiveNuisanceGamma_pos I U (3 * (a : ℝ)) T)
          (B.canonicalEffectiveNuisanceGap_on_closedBall I a hU
            hlowerOne hupperU hlo hhiIntervals T hbaseline
            hW z hz) (e z hz)) p| ≤ Ccomp)
    (hfastNuisanceRow : ∀ (z : B.EffectiveParamSpace)
        (hz : z ∈ closedBall (0 : B.EffectiveParamSpace) (a : ℝ)),
      ‖B.nuisanceCovarianceVector (B.effectiveParamEquiv z)
        (B.bandRegressionScore
          ((e z hz).symm (B.projectedNormalizedTargetBand Delta)))‖ ≤
        B.canonicalEffectiveNuisanceGamma I U (3 * (a : ℝ)) T *
          CfastNuisance)
    (hslowNuisanceRow : ∀ (z : B.EffectiveParamSpace)
        (hz : z ∈ closedBall (0 : B.EffectiveParamSpace) (a : ℝ)),
      ‖B.nuisanceCovarianceVector (B.effectiveParamEquiv z)
        (B.postBandPrimeScore
          (B.actualBandRegression (B.effectiveParamEquiv z)
            (B.canonicalEffectiveNuisanceGamma_pos I U
              (3 * (a : ℝ)) T)
            (B.canonicalEffectiveNuisanceGap_on_closedBall I a hU
              hlowerOne hupperU hlo hhiIntervals T hbaseline
              hW z hz) (e z hz)))‖ ≤
        B.canonicalEffectiveNuisanceGamma I U (3 * (a : ℝ)) T *
          CslowNuisance)
    (hspeedPrime : CinvOrd * Tband +
      (B.twoStageCompensatedTargetBoundOrdinaryFast
          (Cinv * (2 * CrightRow)) Tband TslowCoord /
          (gammaSlow * B.w ^ 2)) * Ccomp ≤ (speed : ℝ))
    (hspeedNuisance : CfastNuisance +
      (B.twoStageCompensatedTargetBoundOrdinaryFast
          (Cinv * (2 * CrightRow)) Tband TslowCoord /
          (gammaSlow * B.w ^ 2)) * CslowNuisance ≤ (speed : ℝ))
    (hspeedSlow : B.w *
      (B.twoStageCompensatedTargetBoundOrdinaryFast
          (Cinv * (2 * CrightRow)) Tband TslowCoord /
          (gammaSlow * B.w ^ 2)) ≤ (speed : ℝ))
    (hmargin : speed ≤ a)
    (monitoredPrimes : Finset ℕ)
    (Crow : ℝ) (hCrow : 0 ≤ Crow)
    (hmarkedRow : ∀ p ∈ monitoredPrimes,
      ∀ z ∈ closedBall (0 : B.EffectiveParamSpace) (a : ℝ),
        |B.vectorFamily.scalarFamily.covariance
            (B.markedValuation p)
            (fun m => B.vectorFamily.scalarFamily.score m
              (B.vectorFamily.vectorField (B.targetVector Delta)
                (B.effectiveParamEquiv z)))
            (B.effectiveParamEquiv z)| ≤ Crow / (p : ℝ))
    (markedTarget : ℕ → ℝ)
    (N Cinitial Cmass : ℝ)
    (hprimePos : ∀ p ∈ monitoredPrimes, 0 < p)
    (hqMass : B.q ≤ Cmass * N)
    (hinitialMarked : ∀ p ∈ monitoredPrimes,
      |markedTarget p - B.paperMoment (B.markedValuation p) 0| ≤
        Cinitial * N / ((p : ℝ) * B.L))
    (fixedValue : Fixed → ℕ) (fixedWeight : Fixed → ℝ)
    (quota : ℤ)
    (hquota : (quota : ℝ) = (∑ f, fixedWeight f) + B.q)
    {C Cfixed Cactive : ℝ}
    (hC : 1 ≤ C)
    (hhi : ∀ sigma, B.sampleData.hi sigma ≤
      physicalBound C B.sampleData.n)
    (hsep : B.sampleData.HeadPatternsSeparated)
    (hfrozenFeasible : ∀ x,
      frozenAmbientWeight fixedValue fixedWeight x ∈ Set.Icc (0 : ℝ) 1)
    (hfrozenLedger : ∀ m : B.sampleData.Sample,
      frozenAmbientWeight fixedValue fixedWeight
        (B.sampleData.value m) ≤ Cfixed / B.L)
    (hactiveLedger : ∀ m : B.sampleData.Sample,
      B.baseline.baseWeight m ≤ Cactive / B.L)
    (hlarge : Cfixed +
      Real.exp (2 *
        ((PaperStatisticNorm.valuationLogCoefficient C B.sampleData.W +
          B.nuisanceStatisticCoefficient C) * (3 * (a : ℝ)))) *
            Cactive ≤ B.L) :
    ∃ path : ℝ → B.ParamSpace,
      path 0 = 0 ∧
      (∀ t ∈ Icc (0 : ℝ) 1,
        B.effectiveParamEquiv.symm (path t) ∈
          closedBall (0 : B.EffectiveParamSpace) (a : ℝ)) ∧
      (∀ t ∈ Icc (0 : ℝ) 1,
        B.paperEffectiveSize (path t) ≤ 3 * (a : ℝ)) ∧
      (∀ t ∈ Icc (0 : ℝ) 1,
        HasDerivWithinAt path
          (B.vectorFamily.vectorField (B.targetVector Delta) (path t))
          (Icc (0 : ℝ) 1) t) ∧
      (∀ j : Band,
        B.paperMoment (B.bandScore j) (path 1) =
          B.paperMoment (B.bandScore j) 0 + Delta j) ∧
      B.paperMoment B.physicalScore (path 1) =
        B.paperMoment B.physicalScore 0 ∧
      B.paperMoment B.ordinaryLogScore (path 1) =
        B.paperMoment B.ordinaryLogScore 0 ∧
      (∀ h : B.HeadIndex,
        B.paperMoment (B.headIndicator h.1) (path 1) =
          B.paperMoment (B.headIndicator h.1) 0) ∧
      (∀ p : ℕ, p.Prime → p ≤ B.sampleData.W →
        B.paperMoment (B.markedValuation p) (path 1) =
          B.paperMoment (B.markedValuation p) 0) ∧
      B.paperMoment B.primeLogScore (path 1) =
        B.paperMoment B.primeLogScore 0 ∧
      (∀ p ∈ monitoredPrimes,
        |markedTarget p - B.paperMoment (B.markedValuation p) (path 1)| ≤
          (Cinitial + Cmass * Crow) * N / ((p : ℝ) * B.L)) ∧
      (∀ t ∈ Icc (0 : ℝ) 1, ∀ x : ℕ,
        B.ambientCombinedWeight
            (frozenAmbientWeight fixedValue fixedWeight) (path t) x ∈
          Set.Icc (0 : ℝ) 1) ∧
      (∀ t ∈ Icc (0 : ℝ) 1, ∀ f : Fixed,
        B.combinedWeight fixedWeight (path t) (Sum.inl f) =
          B.combinedWeight fixedWeight 0 (Sum.inl f)) ∧
      (∀ t ∈ Icc (0 : ℝ) 1,
        (∑ m : B.sampleData.Sample,
          B.activeCoordinateWeight (path t) m) = B.q) ∧
      (∀ t ∈ Icc (0 : ℝ) 1,
        (∑ x : Fixed ⊕ B.sampleData.Sample,
          B.combinedWeight fixedWeight (path t) x) = (quota : ℝ)) := by
  let gammaNuisance :=
    B.canonicalEffectiveNuisanceGamma I U (3 * (a : ℝ)) T
  let Creg := Cinv * (2 * CrightRow)
  let gammaFast :=
    rawDLowerWeight B.harmonicMass B.bandCenter ^ 2 /
      (sharpWeightTotal B.harmonicMass B.bandCenter * Cinv)
  let gammaMain := min gammaFast gammaSlow /
    (1 + 2 * B.gaugeCenterSquareSum * (1 + Creg ^ 2))
  have hgammaNuisance : 0 < gammaNuisance := by
    exact B.canonicalEffectiveNuisanceGamma_pos I U (3 * (a : ℝ)) T
  have hgammaFast : 0 < gammaFast := by
    dsimp only [gammaFast]
    exact div_pos
      (sq_pos_of_pos (rawDLowerWeight_pos B.harmonicMass B.bandCenter
        B.harmonicMass_pos
        (B.partition.center_ne_zero B.n_gt_one)))
      (mul_pos B.sharpBandWeightTotal_pos hCinv)
  have hcoordDen : 0 <
      1 + 2 * B.gaugeCenterSquareSum * (1 + Creg ^ 2) := by
    have hg := B.gaugeCenterSquareSum_nonneg
    positivity
  have hgammaMain : 0 < gammaMain := by
    exact div_pos (lt_min hgammaFast hgammaSlow) hcoordDen
  have hGamma : ∀ z ∈
      closedBall (0 : B.EffectiveParamSpace) (a : ℝ), ∀ v,
      gammaNuisance * ‖v‖ ^ 2 ≤
        inner ℝ v (B.nuisanceCovarianceOperator
          (B.effectiveParamEquiv z) v) := by
    intro z hz v
    exact B.canonicalEffectiveNuisanceGap_on_closedBall I a hU
      hlowerOne hupperU hlo hhiIntervals T hbaseline hW z hz v
  have he' : ∀ z (hz : z ∈
      closedBall (0 : B.EffectiveParamSpace) (a : ℝ)) q,
      e z hz q = B.actualBandSchurLinearMap
        (B.effectiveParamEquiv z) hgammaNuisance (hGamma z hz) q := by
    intro z hz q
    simpa only [gammaNuisance] using he z hz q
  have hfast : ∀ z (hz : z ∈
      closedBall (0 : B.EffectiveParamSpace) (a : ℝ)) q,
      gammaFast *
          paperSharpNorm B.harmonicMass B.bandCenter
            (B.partition.center_ne_zero B.n_gt_one) q ^ 2 ≤
        (B.tiltedLaw (B.effectiveParamEquiv z)).covariance
          (B.nuisanceResidualScore (B.effectiveParamEquiv z)
            hgammaNuisance (hGamma z hz) (B.bandRegressionScore q))
          (B.nuisanceResidualScore (B.effectiveParamEquiv z)
            hgammaNuisance (hGamma z hz) (B.bandRegressionScore q)) := by
    intro z hz q
    simpa only [gammaFast] using
      B.actualBandSchur_quadratic_lower_of_inverse_arithmetic
        (B.effectiveParamEquiv z) hgammaNuisance (hGamma z hz)
        (e z hz) (he' z hz) hCinv (hinv z hz) q
  have hslow' : ∀ z (hz : z ∈
      closedBall (0 : B.EffectiveParamSpace) (a : ℝ)),
      gammaSlow * B.w ^ 2 ≤
        (B.tiltedLaw (B.effectiveParamEquiv z)).covariance
          (B.actualTwoStageCompensatedScore (B.effectiveParamEquiv z)
            hgammaNuisance (hGamma z hz) (e z hz))
          (B.actualTwoStageCompensatedScore (B.effectiveParamEquiv z)
            hgammaNuisance (hGamma z hz) (e z hz)) := by
    intro z hz
    simpa only [actualTwoStageCompensatedVariance, gammaNuisance] using
      hslowVariance z hz
  have hCreg : 0 ≤ Creg := by
    dsimp only [Creg]
    exact mul_nonneg hCinv.le (mul_nonneg (by norm_num) hCrightRow)
  have hreg' : ∀ z (hz : z ∈
      closedBall (0 : B.EffectiveParamSpace) (a : ℝ)),
      paperSharpNorm B.harmonicMass B.bandCenter
          (B.partition.center_ne_zero B.n_gt_one)
          (B.actualBandRegression (B.effectiveParamEquiv z)
            hgammaNuisance (hGamma z hz) (e z hz)) ≤ Creg * B.w := by
    intro z hz
    have hright := B.actualBandRegressionTarget_sharpNorm_le_of_row
      (B.effectiveParamEquiv z) hgammaNuisance (hGamma z hz)
      hCrightRow B.w_pos.le (by
        intro j
        simpa only [gammaNuisance] using hregRightRow z hz j)
    have hraw := B.actualBandRegression_sharpNorm_le
      (B.effectiveParamEquiv z) hgammaNuisance (hGamma z hz)
      (e z hz) hCinv.le (hinv z hz) hright
    simpa only [Creg] using hraw
  have hSchur : ∀ z (hz : z ∈
      closedBall (0 : B.EffectiveParamSpace) (a : ℝ)) u,
      gammaMain * ‖u‖ ^ 2 ≤
        inner ℝ
          (B.schurResidual
            (B.exactNuisanceRegression (B.effectiveParamEquiv z)
              hgammaNuisance (hGamma z hz)) u)
          (B.covarianceOperator (B.effectiveParamEquiv z)
            (B.schurResidual
              (B.exactNuisanceRegression (B.effectiveParamEquiv z)
                hgammaNuisance (hGamma z hz)) u)) := by
    intro z hz u
    simpa only [gammaMain] using
      B.exactSchurGap_of_fastSlow_of_regressionBound
        (B.effectiveParamEquiv z) hgammaNuisance (hGamma z hz)
        (e z hz) (he' z hz) hgammaFast hgammaSlow hCreg
        (hfast z hz) (hslow' z hz) (hreg' z hz) u
  have hVlower : 0 < gammaSlow * B.w ^ 2 :=
    mul_pos hgammaSlow (sq_pos_of_pos B.w_pos)
  have hTslow : 0 ≤
      B.twoStageCompensatedTargetBoundOrdinaryFast
        Creg Tband TslowCoord := by
    unfold twoStageCompensatedTargetBoundOrdinaryFast
    have hmoment : 0 ≤ ∑ j : Band,
        B.harmonicMass j * B.bandCenter j := by
      apply Finset.sum_nonneg
      intro j hj
      exact mul_nonneg (B.harmonicMass_pos j).le
        (B.bandCenter_pos j).le
    exact add_nonneg
      (mul_nonneg
        (mul_nonneg hmoment
          (mul_nonneg hCreg B.w_pos.le)) hTband)
      (mul_nonneg B.w_pos.le hTslowCoord)
  have hcomponents : ∀ z (hz : z ∈
      closedBall (0 : B.EffectiveParamSpace) (a : ℝ)) u,
      B.exactSchurCovarianceOperator (B.effectiveParamEquiv z)
          hgammaNuisance (hGamma z hz) u =
          B.mainPart (B.normalizedTarget Delta) →
      ‖fun p : BandPrime B.sampleData.n B.sampleData.W =>
          (B.rawGaugeOfMain u).1 (B.partition.band p) +
            (u MainCoord.slow / B.w) * B.primeDeviation p‖ ≤
          CinvOrd * Tband +
            (B.twoStageCompensatedTargetBoundOrdinaryFast
              Creg Tband TslowCoord /
              (gammaSlow * B.w ^ 2)) * Ccomp ∧
        ‖B.exactNuisanceRegression (B.effectiveParamEquiv z)
          hgammaNuisance (hGamma z hz) u‖ ≤
          CfastNuisance +
            (B.twoStageCompensatedTargetBoundOrdinaryFast
              Creg Tband TslowCoord /
              (gammaSlow * B.w ^ 2)) * CslowNuisance ∧
        |u MainCoord.slow| ≤
          B.w * (B.twoStageCompensatedTargetBoundOrdinaryFast
            Creg Tband TslowCoord / (gammaSlow * B.w ^ 2)) := by
    intro z hz u hu
    apply B.exactSchur_solution_component_bounds_of_ordinaryFast_twoStageTargets
      (B.effectiveParamEquiv z) hgammaNuisance (hGamma z hz)
      (e z hz) (he' z hz) Delta hCinvOrd hTband hVlower
      hTslow hCcomp (hinvOrd z hz) htargetBand
    · simpa only [actualTwoStageCompensatedVariance, gammaNuisance] using
        hslowVariance z hz
    · simpa only [gammaNuisance] using
        B.abs_compensatedNormalizedTarget_le_of_regression_ordinaryTarget
          (B.effectiveParamEquiv z) hgammaNuisance (hGamma z hz)
          (e z hz) Delta hCreg (hreg' z hz) htargetBand
          htargetSlowCoord
    · intro p
      simpa only [gammaNuisance] using hcomp z hz p
    · exact B.targetFastNuisanceCoefficient_norm_le_of_covarianceVector
        (B.effectiveParamEquiv z) hgammaNuisance (hGamma z hz)
        (e z hz) Delta (by
          simpa only [gammaNuisance] using hfastNuisanceRow z hz)
    · exact B.actualTwoStageNuisanceCoefficient_norm_le_of_covarianceVector
        (B.effectiveParamEquiv z) hgammaNuisance (hGamma z hz)
        (e z hz) (by
          simpa only [gammaNuisance] using hslowNuisanceRow z hz)
    · exact hu
  have hprime : ∀ z (hz : z ∈
      closedBall (0 : B.EffectiveParamSpace) (a : ℝ)) u,
      B.exactSchurCovarianceOperator (B.effectiveParamEquiv z)
          hgammaNuisance (hGamma z hz) u =
          B.mainPart (B.normalizedTarget Delta) →
      ‖fun p : BandPrime B.sampleData.n B.sampleData.W =>
          (B.rawGaugeOfMain u).1 (B.partition.band p) +
            (u MainCoord.slow / B.w) * B.primeDeviation p‖ ≤
        (speed : ℝ) := by
    intro z hz u hu
    exact (hcomponents z hz u hu).1.trans hspeedPrime
  have hnuisance : ∀ z (hz : z ∈
      closedBall (0 : B.EffectiveParamSpace) (a : ℝ)) u,
      B.exactSchurCovarianceOperator (B.effectiveParamEquiv z)
          hgammaNuisance (hGamma z hz) u =
          B.mainPart (B.normalizedTarget Delta) →
      ‖B.exactNuisanceRegression (B.effectiveParamEquiv z)
        hgammaNuisance (hGamma z hz) u‖ ≤ (speed : ℝ) := by
    intro z hz u hu
    exact (hcomponents z hz u hu).2.1.trans hspeedNuisance
  have hstoredSlow : ∀ z (hz : z ∈
      closedBall (0 : B.EffectiveParamSpace) (a : ℝ)) u,
      B.exactSchurCovarianceOperator (B.effectiveParamEquiv z)
          hgammaNuisance (hGamma z hz) u =
          B.mainPart (B.normalizedTarget Delta) →
      |u MainCoord.slow| ≤ (speed : ℝ) := by
    intro z hz u hu
    exact (hcomponents z hz u hu).2.2.trans hspeedSlow
  obtain ⟨path, hpathZero, hball, hsize, hderiv, hbands, hphysical,
      hordinaryLog, hheads, hlog, hmarked, hfeasible, hfixed, hmass,
      hquotaPath⟩ :=
    B.exists_physicallyCenteredFixedPartitionFit_of_exactSchurOutputs
    hcompat Delta a speed gammaMain gammaNuisance hgammaMain
    hgammaNuisance hGamma hSchur hprime hnuisance hstoredSlow hmargin
    monitoredPrimes Crow hCrow hmarkedRow markedTarget N Cinitial Cmass
    hprimePos hqMass hinitialMarked fixedValue fixedWeight quota hquota
    hC hW hhi hsep hfrozenFeasible hfrozenLedger hactiveLedger hlarge
  have hheadPrimes : ∀ p : ℕ, p.Prime → p ≤ B.sampleData.W →
      B.paperMoment (B.markedValuation p) (path 1) =
        B.paperMoment (B.markedValuation p) 0 := by
    intro p hp hpW
    exact B.headPrimeMarkedMoment_eq_of_headIndicatorMoments
      hhead 0 (path 1) hheads hp hpW
  exact ⟨path, hpathZero, hball, hsize, hderiv, hbands, hphysical,
    hordinaryLog, hheads, hheadPrimes, hlog, hmarked, hfeasible, hfixed,
    hmass, hquotaPath⟩

end BridgeData

end

end Erdos390.Full.PaperBridgeFit

end

universe u_1 u_2 u_3
theorem solution :
∀ {Head : Type u_1} {Band : Type u_2} [inst : Fintype.{u_1} Head] [inst_1 : DecidableEq.{u_1 + 1} Head]
  [inst_2 : Fintype.{u_2} Band] [inst_3 : DecidableEq.{u_2 + 1} Band]
  (B : Erdos390.Full.PaperBridgeFit.BridgeData.{u_1, u_2} Head Band) [inst_4 : Nonempty.{u_1 + 1} Head]
  [inst_5 : Nonempty.{u_2 + 1} Band] {Fixed : Type u_3} [inst_6 : Fintype.{u_3} Fixed]
  (I : Erdos390.Full.PaperGuardCensus.PhysicalIntervals) {U : Real} (hU : LE.le.{0} (1 : Real) U)
  (hlowerOne :
    ∀ (sigma : Erdos390.Full.PaperBridgeFit.PhysicalSign),
      LE.le.{0} (1 : Real) (Erdos390.Full.PaperGuardCensus.PhysicalIntervals.lower I sigma))
  (hupperU :
    ∀ (sigma : Erdos390.Full.PaperBridgeFit.PhysicalSign),
      LE.le.{0} (Erdos390.Full.PaperGuardCensus.PhysicalIntervals.upper I sigma) U)
  (hlo :
    ∀ (sigma : Erdos390.Full.PaperBridgeFit.PhysicalSign),
      Eq.{1}
        (Erdos390.Full.PaperBridgeFit.StructuredSampleData.lo.{u_1}
          (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B) sigma)
        (Erdos390.Full.ArithmeticModel.physicalBound (Erdos390.Full.PaperGuardCensus.PhysicalIntervals.lower I sigma)
          (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
            (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B))))
  (hhiIntervals :
    ∀ (sigma : Erdos390.Full.PaperBridgeFit.PhysicalSign),
      Eq.{1}
        (Erdos390.Full.PaperBridgeFit.StructuredSampleData.hi.{u_1}
          (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B) sigma)
        (Erdos390.Full.ArithmeticModel.physicalBound (Erdos390.Full.PaperGuardCensus.PhysicalIntervals.upper I sigma)
          (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
            (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B))))
  (T :
    Erdos390.Full.PaperGuardCensus.BarycentricTarget.{u_1}
      (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B))
  (hbaseline :
    Eq.{u_1 + 1} (Erdos390.Full.PaperBridgeFit.BridgeData.baseline.{u_1, u_2} B)
      (Erdos390.Full.PaperGuardCensus.BarycentricTarget.baseline.{u_1} T))
  (hW :
    LT.lt.{0} (1 : Nat)
      (Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1}
        (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B))),
  Erdos390.Full.PaperBridgeFit.BridgeData.HasPrimeLogCompatibility.{u_1, u_2} B →
    (∀ (h : Head) (p : Nat),
        Iff
          (Membership.mem.{0, 0}
            (Erdos390.Full.HeadPattern.Pattern.primes
              (Erdos390.Full.PaperBridgeFit.StructuredSampleData.pattern.{u_1}
                (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B) h))
            p)
          (And (Nat.Prime p)
            (LE.le.{0} p
              (Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1}
                (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B))))) →
      ∀ (Delta : Band → Real) (a speed : NNReal)
        {Cinv CinvOrd gammaSlow CrightRow Tband TslowCoord Ccomp CfastNuisance CslowNuisance : Real},
        LT.lt.{0} (0 : Real) Cinv →
          LE.le.{0} (0 : Real) CinvOrd →
            LT.lt.{0} (0 : Real) gammaSlow →
              LE.le.{0} (0 : Real) CrightRow →
                LE.le.{0} (0 : Real) Tband →
                  LE.le.{0} (0 : Real) TslowCoord →
                    LE.le.{0} (0 : Real) Ccomp →
                      ∀
                        (e :
                          (z : ↥(Erdos390.Full.PaperBridgeFit.BridgeData.EffectiveParamSpace.{u_1, u_2} B)) →
                            Membership.mem.{u_1, u_1}
                                (Metric.closedBall.{u_1}
                                  (0 : ↥(Erdos390.Full.PaperBridgeFit.BridgeData.EffectiveParamSpace.{u_1, u_2} B)) ↑a)
                                z →
                              LinearEquiv.{0, 0, u_2, u_2} (RingHom.id.{0} Real)
                                ↥(Erdos390.Full.PaperBridgeFit.BridgeData.RawBandGauge.{u_1, u_2} B)
                                ↥(Erdos390.Full.PaperBridgeFit.BridgeData.RawBandGauge.{u_1, u_2} B)),
                        (∀ (z : ↥(Erdos390.Full.PaperBridgeFit.BridgeData.EffectiveParamSpace.{u_1, u_2} B))
                            (hz :
                              Membership.mem.{u_1, u_1}
                                (Metric.closedBall.{u_1}
                                  (0 : ↥(Erdos390.Full.PaperBridgeFit.BridgeData.EffectiveParamSpace.{u_1, u_2} B)) ↑a)
                                z)
                            (q : ↥(Erdos390.Full.PaperBridgeFit.BridgeData.RawBandGauge.{u_1, u_2} B)),
                            Eq.{u_2 + 1} ((e z hz) q)
                              ((Erdos390.Full.PaperBridgeFit.BridgeData.actualBandSchurLinearMap.{u_1, u_2} B
                                  ((Erdos390.Full.PaperBridgeFit.BridgeData.effectiveParamEquiv.{u_1, u_2} B) z)
                                  (Erdos390.Full.PaperBridgeFit.BridgeData.canonicalEffectiveNuisanceGamma_pos.{u_1,
                                      u_2}
                                    B I U (HMul.hMul.{0, 0, 0} (3 : Real) ↑a) T)
                                  (Erdos390.Full.PaperBridgeFit.BridgeData.canonicalEffectiveNuisanceGap_on_closedBall.{u_1,
                                      u_2}
                                    B I a hU hlowerOne hupperU hlo hhiIntervals T hbaseline hW z hz))
                                q)) →
                          (∀ (z : ↥(Erdos390.Full.PaperBridgeFit.BridgeData.EffectiveParamSpace.{u_1, u_2} B))
                              (hz :
                                Membership.mem.{u_1, u_1}
                                  (Metric.closedBall.{u_1}
                                    (0 : ↥(Erdos390.Full.PaperBridgeFit.BridgeData.EffectiveParamSpace.{u_1, u_2} B))
                                    ↑a)
                                  z)
                              (v : ↥(Erdos390.Full.PaperBridgeFit.BridgeData.RawBandGauge.{u_1, u_2} B)),
                              LE.le.{0}
                                (Erdos390.Full.PaperWeightedInverseExport.paperSharpNorm.{u_2}
                                  (Erdos390.Full.PaperBridgeFit.BridgeData.harmonicMass.{u_1, u_2} B)
                                  (Erdos390.Full.PaperBridgeFit.BridgeData.bandCenter.{u_1, u_2} B)
                                  (Erdos390.Full.ArithmeticBandGeometry.Partition.center_ne_zero.{u_2}
                                    (Erdos390.Full.PaperBridgeFit.BridgeData.partition.{u_1, u_2} B)
                                    (Erdos390.Full.PaperBridgeFit.BridgeData.n_gt_one.{u_1, u_2} B))
                                  ((LinearEquiv.symm.{0, 0, u_2, u_2} (e z hz)) v))
                                (HMul.hMul.{0, 0, 0} Cinv
                                  (Erdos390.Full.PaperWeightedInverseExport.paperSharpNorm.{u_2}
                                    (Erdos390.Full.PaperBridgeFit.BridgeData.harmonicMass.{u_1, u_2} B)
                                    (Erdos390.Full.PaperBridgeFit.BridgeData.bandCenter.{u_1, u_2} B)
                                    (Erdos390.Full.ArithmeticBandGeometry.Partition.center_ne_zero.{u_2}
                                      (Erdos390.Full.PaperBridgeFit.BridgeData.partition.{u_1, u_2} B)
                                      (Erdos390.Full.PaperBridgeFit.BridgeData.n_gt_one.{u_1, u_2} B))
                                    v))) →
                            (∀ (z : ↥(Erdos390.Full.PaperBridgeFit.BridgeData.EffectiveParamSpace.{u_1, u_2} B))
                                (hz :
                                  Membership.mem.{u_1, u_1}
                                    (Metric.closedBall.{u_1}
                                      (0 : ↥(Erdos390.Full.PaperBridgeFit.BridgeData.EffectiveParamSpace.{u_1, u_2} B))
                                      ↑a)
                                    z)
                                (v : ↥(Erdos390.Full.PaperBridgeFit.BridgeData.RawBandGauge.{u_1, u_2} B)),
                                LE.le.{0} (Norm.norm.{u_2} ((LinearEquiv.symm.{0, 0, u_2, u_2} (e z hz)) v))
                                  (HMul.hMul.{0, 0, 0} CinvOrd (Norm.norm.{u_2} v))) →
                              (∀ (z : ↥(Erdos390.Full.PaperBridgeFit.BridgeData.EffectiveParamSpace.{u_1, u_2} B))
                                  (hz :
                                    Membership.mem.{u_1, u_1}
                                      (Metric.closedBall.{u_1}
                                        (0 :
                                          ↥(Erdos390.Full.PaperBridgeFit.BridgeData.EffectiveParamSpace.{u_1, u_2} B))
                                        ↑a)
                                      z),
                                  LE.le.{0}
                                    (HMul.hMul.{0, 0, 0} gammaSlow
                                      (HPow.hPow.{0, 0, 0} (Erdos390.Full.PaperBridgeFit.BridgeData.w.{u_1, u_2} B)
                                        (2 : Nat)))
                                    (Erdos390.Full.PaperBridgeFit.BridgeData.actualTwoStageCompensatedVariance.{u_1,
                                        u_2}
                                      B ((Erdos390.Full.PaperBridgeFit.BridgeData.effectiveParamEquiv.{u_1, u_2} B) z)
                                      (Erdos390.Full.PaperBridgeFit.BridgeData.canonicalEffectiveNuisanceGamma_pos.{u_1,
                                          u_2}
                                        B I U (HMul.hMul.{0, 0, 0} (3 : Real) ↑a) T)
                                      (Erdos390.Full.PaperBridgeFit.BridgeData.canonicalEffectiveNuisanceGap_on_closedBall.{u_1,
                                          u_2}
                                        B I a hU hlowerOne hupperU hlo hhiIntervals T hbaseline hW z hz)
                                      (e z hz))) →
                                (∀ (z : ↥(Erdos390.Full.PaperBridgeFit.BridgeData.EffectiveParamSpace.{u_1, u_2} B))
                                    (hz :
                                      Membership.mem.{u_1, u_1}
                                        (Metric.closedBall.{u_1}
                                          (0 :
                                            ↥(Erdos390.Full.PaperBridgeFit.BridgeData.EffectiveParamSpace.{u_1, u_2} B))
                                          ↑a)
                                        z)
                                    (j : Band),
                                    LE.le.{0}
                                      (abs.{0}
                                        (Erdos390.Full.PaperBridgeFit.BridgeData.normalizedBandCovarianceRow.{u_1, u_2}
                                          B
                                          ((Erdos390.Full.PaperBridgeFit.BridgeData.effectiveParamEquiv.{u_1, u_2} B) z)
                                          (Erdos390.Full.PaperBridgeFit.BridgeData.nuisanceResidualScore.{u_1, u_2} B
                                            ((Erdos390.Full.PaperBridgeFit.BridgeData.effectiveParamEquiv.{u_1, u_2} B)
                                              z)
                                            (Erdos390.Full.PaperBridgeFit.BridgeData.canonicalEffectiveNuisanceGamma_pos.{u_1,
                                                u_2}
                                              B I U (HMul.hMul.{0, 0, 0} (3 : Real) ↑a) T)
                                            (Erdos390.Full.PaperBridgeFit.BridgeData.canonicalEffectiveNuisanceGap_on_closedBall.{u_1,
                                                u_2}
                                              B I a hU hlowerOne hupperU hlo hhiIntervals T hbaseline hW z hz)
                                            (Erdos390.Full.PaperBridgeFit.BridgeData.slowScore.{u_1, u_2} B))
                                          j))
                                      (HMul.hMul.{0, 0, 0}
                                        (HMul.hMul.{0, 0, 0} CrightRow
                                          (Erdos390.Full.PaperBridgeFit.BridgeData.w.{u_1, u_2} B))
                                        (Erdos390.Full.PaperBridgeFit.BridgeData.bandCenter.{u_1, u_2} B j))) →
                                  LE.le.{0}
                                      (Norm.norm.{u_2}
                                        (Erdos390.Full.PaperBridgeFit.BridgeData.projectedNormalizedTargetBand.{u_1,
                                            u_2}
                                          B Delta))
                                      Tband →
                                    LE.le.{0}
                                        (abs.{0}
                                          (WithLp.ofLp.{u_2}
                                            (Erdos390.Full.PaperBridgeFit.BridgeData.mainPart.{u_1, u_2} B
                                              (Erdos390.Full.PaperBridgeFit.BridgeData.normalizedTarget.{u_1, u_2} B
                                                Delta))
                                            Erdos390.Full.PaperBridgeFit.MainCoord.slow.{u_2}))
                                        TslowCoord →
                                      (∀
                                          (z :
                                            ↥(Erdos390.Full.PaperBridgeFit.BridgeData.EffectiveParamSpace.{u_1, u_2} B))
                                          (hz :
                                            Membership.mem.{u_1, u_1}
                                              (Metric.closedBall.{u_1}
                                                (0 :
                                                  ↥(Erdos390.Full.PaperBridgeFit.BridgeData.EffectiveParamSpace.{u_1,
                                                        u_2}
                                                      B))
                                                ↑a)
                                              z)
                                          (p :
                                            Erdos390.Full.ArithmeticBandGeometry.BandPrime
                                              (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                                                (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B))
                                              (Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1}
                                                (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B))),
                                          LE.le.{0}
                                            (abs.{0}
                                              (Erdos390.Full.PaperBridgeFit.BridgeData.actualCompensatedCoefficient.{u_1,
                                                  u_2}
                                                B
                                                (Erdos390.Full.PaperBridgeFit.BridgeData.actualBandRegression.{u_1, u_2}
                                                  B
                                                  ((Erdos390.Full.PaperBridgeFit.BridgeData.effectiveParamEquiv.{u_1,
                                                        u_2}
                                                      B)
                                                    z)
                                                  (Erdos390.Full.PaperBridgeFit.BridgeData.canonicalEffectiveNuisanceGamma_pos.{u_1,
                                                      u_2}
                                                    B I U (HMul.hMul.{0, 0, 0} (3 : Real) ↑a) T)
                                                  (Erdos390.Full.PaperBridgeFit.BridgeData.canonicalEffectiveNuisanceGap_on_closedBall.{u_1,
                                                      u_2}
                                                    B I a hU hlowerOne hupperU hlo hhiIntervals T hbaseline hW z hz)
                                                  (e z hz))
                                                p))
                                            Ccomp) →
                                        (∀
                                            (z :
                                              ↥(Erdos390.Full.PaperBridgeFit.BridgeData.EffectiveParamSpace.{u_1, u_2}
                                                  B))
                                            (hz :
                                              Membership.mem.{u_1, u_1}
                                                (Metric.closedBall.{u_1}
                                                  (0 :
                                                    ↥(Erdos390.Full.PaperBridgeFit.BridgeData.EffectiveParamSpace.{u_1,
                                                          u_2}
                                                        B))
                                                  ↑a)
                                                z),
                                            LE.le.{0}
                                              (Norm.norm.{u_1}
                                                (Erdos390.Full.PaperBridgeFit.BridgeData.nuisanceCovarianceVector.{u_1,
                                                    u_2}
                                                  B
                                                  ((Erdos390.Full.PaperBridgeFit.BridgeData.effectiveParamEquiv.{u_1,
                                                        u_2}
                                                      B)
                                                    z)
                                                  (Erdos390.Full.PaperBridgeFit.BridgeData.bandRegressionScore.{u_1,
                                                      u_2}
                                                    B
                                                    ((LinearEquiv.symm.{0, 0, u_2, u_2} (e z hz))
                                                      (Erdos390.Full.PaperBridgeFit.BridgeData.projectedNormalizedTargetBand.{u_1,
                                                          u_2}
                                                        B Delta)))))
                                              (HMul.hMul.{0, 0, 0}
                                                (Erdos390.Full.PaperBridgeFit.BridgeData.canonicalEffectiveNuisanceGamma.{u_1,
                                                    u_2}
                                                  B I U (HMul.hMul.{0, 0, 0} (3 : Real) ↑a) T)
                                                CfastNuisance)) →
                                          (∀
                                              (z :
                                                ↥(Erdos390.Full.PaperBridgeFit.BridgeData.EffectiveParamSpace.{u_1, u_2}
                                                    B))
                                              (hz :
                                                Membership.mem.{u_1, u_1}
                                                  (Metric.closedBall.{u_1}
                                                    (0 :
                                                      ↥(Erdos390.Full.PaperBridgeFit.BridgeData.EffectiveParamSpace.{u_1,
                                                            u_2}
                                                          B))
                                                    ↑a)
                                                  z),
                                              LE.le.{0}
                                                (Norm.norm.{u_1}
                                                  (Erdos390.Full.PaperBridgeFit.BridgeData.nuisanceCovarianceVector.{u_1,
                                                      u_2}
                                                    B
                                                    ((Erdos390.Full.PaperBridgeFit.BridgeData.effectiveParamEquiv.{u_1,
                                                          u_2}
                                                        B)
                                                      z)
                                                    (Erdos390.Full.PaperBridgeFit.BridgeData.postBandPrimeScore.{u_1,
                                                        u_2}
                                                      B
                                                      (Erdos390.Full.PaperBridgeFit.BridgeData.actualBandRegression.{u_1,
                                                          u_2}
                                                        B
                                                        ((Erdos390.Full.PaperBridgeFit.BridgeData.effectiveParamEquiv.{u_1,
                                                              u_2}
                                                            B)
                                                          z)
                                                        (Erdos390.Full.PaperBridgeFit.BridgeData.canonicalEffectiveNuisanceGamma_pos.{u_1,
                                                            u_2}
                                                          B I U (HMul.hMul.{0, 0, 0} (3 : Real) ↑a) T)
                                                        (Erdos390.Full.PaperBridgeFit.BridgeData.canonicalEffectiveNuisanceGap_on_closedBall.{u_1,
                                                            u_2}
                                                          B I a hU hlowerOne hupperU hlo hhiIntervals T hbaseline hW z
                                                          hz)
                                                        (e z hz)))))
                                                (HMul.hMul.{0, 0, 0}
                                                  (Erdos390.Full.PaperBridgeFit.BridgeData.canonicalEffectiveNuisanceGamma.{u_1,
                                                      u_2}
                                                    B I U (HMul.hMul.{0, 0, 0} (3 : Real) ↑a) T)
                                                  CslowNuisance)) →
                                            LE.le.{0}
                                                (HAdd.hAdd.{0, 0, 0} (HMul.hMul.{0, 0, 0} CinvOrd Tband)
                                                  (HMul.hMul.{0, 0, 0}
                                                    (HDiv.hDiv.{0, 0, 0}
                                                      (Erdos390.Full.PaperBridgeFit.BridgeData.twoStageCompensatedTargetBoundOrdinaryFast.{u_1,
                                                          u_2}
                                                        B
                                                        (HMul.hMul.{0, 0, 0} Cinv
                                                          (HMul.hMul.{0, 0, 0} (2 : Real) CrightRow))
                                                        Tband TslowCoord)
                                                      (HMul.hMul.{0, 0, 0} gammaSlow
                                                        (HPow.hPow.{0, 0, 0}
                                                          (Erdos390.Full.PaperBridgeFit.BridgeData.w.{u_1, u_2} B)
                                                          (2 : Nat))))
                                                    Ccomp))
                                                ↑speed →
                                              LE.le.{0}
                                                  (HAdd.hAdd.{0, 0, 0} CfastNuisance
                                                    (HMul.hMul.{0, 0, 0}
                                                      (HDiv.hDiv.{0, 0, 0}
                                                        (Erdos390.Full.PaperBridgeFit.BridgeData.twoStageCompensatedTargetBoundOrdinaryFast.{u_1,
                                                            u_2}
                                                          B
                                                          (HMul.hMul.{0, 0, 0} Cinv
                                                            (HMul.hMul.{0, 0, 0} (2 : Real) CrightRow))
                                                          Tband TslowCoord)
                                                        (HMul.hMul.{0, 0, 0} gammaSlow
                                                          (HPow.hPow.{0, 0, 0}
                                                            (Erdos390.Full.PaperBridgeFit.BridgeData.w.{u_1, u_2} B)
                                                            (2 : Nat))))
                                                      CslowNuisance))
                                                  ↑speed →
                                                LE.le.{0}
                                                    (HMul.hMul.{0, 0, 0}
                                                      (Erdos390.Full.PaperBridgeFit.BridgeData.w.{u_1, u_2} B)
                                                      (HDiv.hDiv.{0, 0, 0}
                                                        (Erdos390.Full.PaperBridgeFit.BridgeData.twoStageCompensatedTargetBoundOrdinaryFast.{u_1,
                                                            u_2}
                                                          B
                                                          (HMul.hMul.{0, 0, 0} Cinv
                                                            (HMul.hMul.{0, 0, 0} (2 : Real) CrightRow))
                                                          Tband TslowCoord)
                                                        (HMul.hMul.{0, 0, 0} gammaSlow
                                                          (HPow.hPow.{0, 0, 0}
                                                            (Erdos390.Full.PaperBridgeFit.BridgeData.w.{u_1, u_2} B)
                                                            (2 : Nat)))))
                                                    ↑speed →
                                                  LE.le.{0} speed a →
                                                    ∀ (monitoredPrimes : Finset.{0} Nat) (Crow : Real),
                                                      LE.le.{0} (0 : Real) Crow →
                                                        (∀ (p : Nat),
                                                            Membership.mem.{0, 0} monitoredPrimes p →
                                                              ∀
                                                                (z :
                                                                  ↥(Erdos390.Full.PaperBridgeFit.BridgeData.EffectiveParamSpace.{u_1,
                                                                        u_2}
                                                                      B)),
                                                                Membership.mem.{u_1, u_1}
                                                                    (Metric.closedBall.{u_1}
                                                                      (0 :
                                                                        ↥(Erdos390.Full.PaperBridgeFit.BridgeData.EffectiveParamSpace.{u_1,
                                                                              u_2}
                                                                            B))
                                                                      ↑a)
                                                                    z →
                                                                  LE.le.{0}
                                                                    (abs.{0}
                                                                      (Erdos390.Full.FiniteExponentialFamily.covariance.{u_1,
                                                                          max u_1 u_2}
                                                                        (Erdos390.Full.VectorExponentialFamily.scalarFamily.{u_1,
                                                                            max u_1 u_2}
                                                                          (Erdos390.Full.PaperBridgeFit.BridgeData.vectorFamily.{u_1,
                                                                              u_2}
                                                                            B))
                                                                        (Erdos390.Full.PaperBridgeFit.BridgeData.markedValuation.{u_1,
                                                                            u_2}
                                                                          B p)
                                                                        (fun m =>
                                                                          (Erdos390.Full.FiniteExponentialFamily.score.{u_1,
                                                                                max u_1 u_2}
                                                                              (Erdos390.Full.VectorExponentialFamily.scalarFamily.{u_1,
                                                                                  max u_1 u_2}
                                                                                (Erdos390.Full.PaperBridgeFit.BridgeData.vectorFamily.{u_1,
                                                                                    u_2}
                                                                                  B))
                                                                              m)
                                                                            (Erdos390.Full.VectorExponentialFamily.vectorField.{u_1,
                                                                                max u_1 u_2}
                                                                              (Erdos390.Full.PaperBridgeFit.BridgeData.vectorFamily.{u_1,
                                                                                  u_2}
                                                                                B)
                                                                              (Erdos390.Full.PaperBridgeFit.BridgeData.targetVector.{u_1,
                                                                                  u_2}
                                                                                B Delta)
                                                                              ((Erdos390.Full.PaperBridgeFit.BridgeData.effectiveParamEquiv.{u_1,
                                                                                    u_2}
                                                                                  B)
                                                                                z)))
                                                                        ((Erdos390.Full.PaperBridgeFit.BridgeData.effectiveParamEquiv.{u_1,
                                                                              u_2}
                                                                            B)
                                                                          z)))
                                                                    (HDiv.hDiv.{0, 0, 0} Crow ↑p)) →
                                                          ∀ (markedTarget : Nat → Real) (N Cinitial Cmass : Real),
                                                            (∀ (p : Nat),
                                                                Membership.mem.{0, 0} monitoredPrimes p →
                                                                  LT.lt.{0} (0 : Nat) p) →
                                                              LE.le.{0}
                                                                  (Erdos390.Full.PaperBridgeFit.BridgeData.q.{u_1, u_2}
                                                                    B)
                                                                  (HMul.hMul.{0, 0, 0} Cmass N) →
                                                                (∀ (p : Nat),
                                                                    Membership.mem.{0, 0} monitoredPrimes p →
                                                                      LE.le.{0}
                                                                        (abs.{0}
                                                                          (HSub.hSub.{0, 0, 0} (markedTarget p)
                                                                            (Erdos390.Full.PaperBridgeFit.BridgeData.paperMoment.{u_1,
                                                                                u_2}
                                                                              B
                                                                              (Erdos390.Full.PaperBridgeFit.BridgeData.markedValuation.{u_1,
                                                                                  u_2}
                                                                                B p)
                                                                              (0 :
                                                                                Erdos390.Full.PaperBridgeFit.BridgeData.ParamSpace.{u_1,
                                                                                    u_2}
                                                                                  B))))
                                                                        (HDiv.hDiv.{0, 0, 0}
                                                                          (HMul.hMul.{0, 0, 0} Cinitial N)
                                                                          (HMul.hMul.{0, 0, 0} (↑p)
                                                                            (Erdos390.Full.PaperBridgeFit.BridgeData.L.{u_1,
                                                                                u_2}
                                                                              B)))) →
                                                                  ∀ (fixedValue : Fixed → Nat)
                                                                    (fixedWeight : Fixed → Real) (quota : Int),
                                                                    Eq.{1} (↑quota)
                                                                        (HAdd.hAdd.{0, 0, 0} (∑ f, fixedWeight f)
                                                                          (Erdos390.Full.PaperBridgeFit.BridgeData.q.{u_1,
                                                                              u_2}
                                                                            B)) →
                                                                      ∀ {C Cfixed Cactive : Real},
                                                                        LE.le.{0} (1 : Real) C →
                                                                          (∀
                                                                              (sigma :
                                                                                Erdos390.Full.PaperBridgeFit.PhysicalSign),
                                                                              LE.le.{0}
                                                                                (Erdos390.Full.PaperBridgeFit.StructuredSampleData.hi.{u_1}
                                                                                  (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1,
                                                                                      u_2}
                                                                                    B)
                                                                                  sigma)
                                                                                (Erdos390.Full.ArithmeticModel.physicalBound
                                                                                  C
                                                                                  (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                                                                                    (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1,
                                                                                        u_2}
                                                                                      B)))) →
                                                                            Erdos390.Full.PaperBridgeFit.StructuredSampleData.HeadPatternsSeparated.{u_1}
                                                                                (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1,
                                                                                    u_2}
                                                                                  B) →
                                                                              (∀ (x : Nat),
                                                                                  Membership.mem.{0, 0}
                                                                                    (Set.Icc.{0} (0 : Real) (1 : Real))
                                                                                    (Erdos390.Full.PaperBridgeFit.BridgeData.frozenAmbientWeight.{u_3}
                                                                                      fixedValue fixedWeight x)) →
                                                                                (∀
                                                                                    (m :
                                                                                      Erdos390.Full.PaperBridgeFit.StructuredSampleData.Sample.{u_1}
                                                                                        (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1,
                                                                                            u_2}
                                                                                          B)),
                                                                                    LE.le.{0}
                                                                                      (Erdos390.Full.PaperBridgeFit.BridgeData.frozenAmbientWeight.{u_3}
                                                                                        fixedValue fixedWeight
                                                                                        (Erdos390.Full.PaperBridgeFit.StructuredSampleData.value.{u_1}
                                                                                          (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1,
                                                                                              u_2}
                                                                                            B)
                                                                                          m))
                                                                                      (HDiv.hDiv.{0, 0, 0} Cfixed
                                                                                        (Erdos390.Full.PaperBridgeFit.BridgeData.L.{u_1,
                                                                                            u_2}
                                                                                          B))) →
                                                                                  (∀
                                                                                      (m :
                                                                                        Erdos390.Full.PaperBridgeFit.StructuredSampleData.Sample.{u_1}
                                                                                          (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1,
                                                                                              u_2}
                                                                                            B)),
                                                                                      LE.le.{0}
                                                                                        (Erdos390.Full.PaperBridgeFit.BaselineAllocation.baseWeight.{u_1}
                                                                                          (Erdos390.Full.PaperBridgeFit.BridgeData.baseline.{u_1,
                                                                                              u_2}
                                                                                            B)
                                                                                          m)
                                                                                        (HDiv.hDiv.{0, 0, 0} Cactive
                                                                                          (Erdos390.Full.PaperBridgeFit.BridgeData.L.{u_1,
                                                                                              u_2}
                                                                                            B))) →
                                                                                    LE.le.{0}
                                                                                        (HAdd.hAdd.{0, 0, 0} Cfixed
                                                                                          (HMul.hMul.{0, 0, 0}
                                                                                            (Real.exp
                                                                                              (HMul.hMul.{0, 0, 0}
                                                                                                (2 : Real)
                                                                                                (HMul.hMul.{0, 0, 0}
                                                                                                  (HAdd.hAdd.{0, 0, 0}
                                                                                                    (Erdos390.Full.PaperStatisticNorm.valuationLogCoefficient
                                                                                                      C
                                                                                                      (Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1}
                                                                                                        (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1,
                                                                                                            u_2}
                                                                                                          B)))
                                                                                                    (Erdos390.Full.PaperBridgeFit.BridgeData.nuisanceStatisticCoefficient.{u_1,
                                                                                                        u_2}
                                                                                                      B C))
                                                                                                  (HMul.hMul.{0, 0, 0}
                                                                                                    (3 : Real) ↑a))))
                                                                                            Cactive))
                                                                                        (Erdos390.Full.PaperBridgeFit.BridgeData.L.{u_1,
                                                                                            u_2}
                                                                                          B) →
                                                                                      ∃ path,
                                                                                        And
                                                                                          (Eq.{max (u_1 + 1) (u_2 + 1)}
                                                                                            (path (0 : Real))
                                                                                            (0 :
                                                                                              Erdos390.Full.PaperBridgeFit.BridgeData.ParamSpace.{u_1,
                                                                                                  u_2}
                                                                                                B))
                                                                                          (And
                                                                                            (∀ (t : Real),
                                                                                              Membership.mem.{0, 0}
                                                                                                  (Set.Icc.{0}
                                                                                                    (0 : Real)
                                                                                                    (1 : Real))
                                                                                                  t →
                                                                                                Membership.mem.{u_1,
                                                                                                    u_1}
                                                                                                  (Metric.closedBall.{u_1}
                                                                                                    (0 :
                                                                                                      ↥(Erdos390.Full.PaperBridgeFit.BridgeData.EffectiveParamSpace.{u_1,
                                                                                                            u_2}
                                                                                                          B))
                                                                                                    ↑a)
                                                                                                  ((ContinuousLinearEquiv.symm.{0,
                                                                                                        0, u_1,
                                                                                                        max u_1 u_2}
                                                                                                      (Erdos390.Full.PaperBridgeFit.BridgeData.effectiveParamEquiv.{u_1,
                                                                                                          u_2}
                                                                                                        B))
                                                                                                    (path t)))
                                                                                            (And
                                                                                              (∀ (t : Real),
                                                                                                Membership.mem.{0, 0}
                                                                                                    (Set.Icc.{0}
                                                                                                      (0 : Real)
                                                                                                      (1 : Real))
                                                                                                    t →
                                                                                                  LE.le.{0}
                                                                                                    (Erdos390.Full.PaperBridgeFit.BridgeData.paperEffectiveSize.{u_1,
                                                                                                        u_2}
                                                                                                      B (path t))
                                                                                                    (HMul.hMul.{0, 0, 0}
                                                                                                      (3 : Real) ↑a))
                                                                                              (And
                                                                                                (∀ (t : Real),
                                                                                                  Membership.mem.{0, 0}
                                                                                                      (Set.Icc.{0}
                                                                                                        (0 : Real)
                                                                                                        (1 : Real))
                                                                                                      t →
                                                                                                    HasDerivWithinAt.{0,
                                                                                                        max u_1 u_2}
                                                                                                      path
                                                                                                      (Erdos390.Full.VectorExponentialFamily.vectorField.{u_1,
                                                                                                          max u_1 u_2}
                                                                                                        (Erdos390.Full.PaperBridgeFit.BridgeData.vectorFamily.{u_1,
                                                                                                            u_2}
                                                                                                          B)
                                                                                                        (Erdos390.Full.PaperBridgeFit.BridgeData.targetVector.{u_1,
                                                                                                            u_2}
                                                                                                          B Delta)
                                                                                                        (path t))
                                                                                                      (Set.Icc.{0}
                                                                                                        (0 : Real)
                                                                                                        (1 : Real))
                                                                                                      t)
                                                                                                (And
                                                                                                  (∀ (j : Band),
                                                                                                    Eq.{1}
                                                                                                      (Erdos390.Full.PaperBridgeFit.BridgeData.paperMoment.{u_1,
                                                                                                          u_2}
                                                                                                        B
                                                                                                        (Erdos390.Full.PaperBridgeFit.BridgeData.bandScore.{u_1,
                                                                                                            u_2}
                                                                                                          B j)
                                                                                                        (path
                                                                                                          (1 : Real)))
                                                                                                      (HAdd.hAdd.{0, 0,
                                                                                                          0}
                                                                                                        (Erdos390.Full.PaperBridgeFit.BridgeData.paperMoment.{u_1,
                                                                                                            u_2}
                                                                                                          B
                                                                                                          (Erdos390.Full.PaperBridgeFit.BridgeData.bandScore.{u_1,
                                                                                                              u_2}
                                                                                                            B j)
                                                                                                          (0 :
                                                                                                            Erdos390.Full.PaperBridgeFit.BridgeData.ParamSpace.{u_1,
                                                                                                                u_2}
                                                                                                              B))
                                                                                                        (Delta j)))
                                                                                                  (And
                                                                                                    (Eq.{1}
                                                                                                      (Erdos390.Full.PaperBridgeFit.BridgeData.paperMoment.{u_1,
                                                                                                          u_2}
                                                                                                        B
                                                                                                        (Erdos390.Full.PaperBridgeFit.BridgeData.physicalScore.{u_1,
                                                                                                            u_2}
                                                                                                          B)
                                                                                                        (path
                                                                                                          (1 : Real)))
                                                                                                      (Erdos390.Full.PaperBridgeFit.BridgeData.paperMoment.{u_1,
                                                                                                          u_2}
                                                                                                        B
                                                                                                        (Erdos390.Full.PaperBridgeFit.BridgeData.physicalScore.{u_1,
                                                                                                            u_2}
                                                                                                          B)
                                                                                                        (0 :
                                                                                                          Erdos390.Full.PaperBridgeFit.BridgeData.ParamSpace.{u_1,
                                                                                                              u_2}
                                                                                                            B)))
                                                                                                    (And
                                                                                                      (Eq.{1}
                                                                                                        (Erdos390.Full.PaperBridgeFit.BridgeData.paperMoment.{u_1,
                                                                                                            u_2}
                                                                                                          B
                                                                                                          (Erdos390.Full.PaperBridgeFit.BridgeData.ordinaryLogScore.{u_1,
                                                                                                              u_2}
                                                                                                            B)
                                                                                                          (path
                                                                                                            (1 : Real)))
                                                                                                        (Erdos390.Full.PaperBridgeFit.BridgeData.paperMoment.{u_1,
                                                                                                            u_2}
                                                                                                          B
                                                                                                          (Erdos390.Full.PaperBridgeFit.BridgeData.ordinaryLogScore.{u_1,
                                                                                                              u_2}
                                                                                                            B)
                                                                                                          (0 :
                                                                                                            Erdos390.Full.PaperBridgeFit.BridgeData.ParamSpace.{u_1,
                                                                                                                u_2}
                                                                                                              B)))
                                                                                                      (And
                                                                                                        (∀
                                                                                                          (h :
                                                                                                            Erdos390.Full.PaperBridgeFit.BridgeData.HeadIndex.{u_1,
                                                                                                                u_2}
                                                                                                              B),
                                                                                                          Eq.{1}
                                                                                                            (Erdos390.Full.PaperBridgeFit.BridgeData.paperMoment.{u_1,
                                                                                                                u_2}
                                                                                                              B
                                                                                                              (Erdos390.Full.PaperBridgeFit.BridgeData.headIndicator.{u_1,
                                                                                                                  u_2}
                                                                                                                B ↑h)
                                                                                                              (path
                                                                                                                (1 :
                                                                                                                  Real)))
                                                                                                            (Erdos390.Full.PaperBridgeFit.BridgeData.paperMoment.{u_1,
                                                                                                                u_2}
                                                                                                              B
                                                                                                              (Erdos390.Full.PaperBridgeFit.BridgeData.headIndicator.{u_1,
                                                                                                                  u_2}
                                                                                                                B ↑h)
                                                                                                              (0 :
                                                                                                                Erdos390.Full.PaperBridgeFit.BridgeData.ParamSpace.{u_1,
                                                                                                                    u_2}
                                                                                                                  B)))
                                                                                                        (And
                                                                                                          (∀ (p : Nat),
                                                                                                            Nat.Prime
                                                                                                                p →
                                                                                                              LE.le.{0}
                                                                                                                  p
                                                                                                                  (Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1}
                                                                                                                    (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1,
                                                                                                                        u_2}
                                                                                                                      B)) →
                                                                                                                Eq.{1}
                                                                                                                  (Erdos390.Full.PaperBridgeFit.BridgeData.paperMoment.{u_1,
                                                                                                                      u_2}
                                                                                                                    B
                                                                                                                    (Erdos390.Full.PaperBridgeFit.BridgeData.markedValuation.{u_1,
                                                                                                                        u_2}
                                                                                                                      B
                                                                                                                      p)
                                                                                                                    (path
                                                                                                                      (1 :
                                                                                                                        Real)))
                                                                                                                  (Erdos390.Full.PaperBridgeFit.BridgeData.paperMoment.{u_1,
                                                                                                                      u_2}
                                                                                                                    B
                                                                                                                    (Erdos390.Full.PaperBridgeFit.BridgeData.markedValuation.{u_1,
                                                                                                                        u_2}
                                                                                                                      B
                                                                                                                      p)
                                                                                                                    (0 :
                                                                                                                      Erdos390.Full.PaperBridgeFit.BridgeData.ParamSpace.{u_1,
                                                                                                                          u_2}
                                                                                                                        B)))
                                                                                                          (And
                                                                                                            (Eq.{1}
                                                                                                              (Erdos390.Full.PaperBridgeFit.BridgeData.paperMoment.{u_1,
                                                                                                                  u_2}
                                                                                                                B
                                                                                                                (Erdos390.Full.PaperBridgeFit.BridgeData.primeLogScore.{u_1,
                                                                                                                    u_2}
                                                                                                                  B)
                                                                                                                (path
                                                                                                                  (1 :
                                                                                                                    Real)))
                                                                                                              (Erdos390.Full.PaperBridgeFit.BridgeData.paperMoment.{u_1,
                                                                                                                  u_2}
                                                                                                                B
                                                                                                                (Erdos390.Full.PaperBridgeFit.BridgeData.primeLogScore.{u_1,
                                                                                                                    u_2}
                                                                                                                  B)
                                                                                                                (0 :
                                                                                                                  Erdos390.Full.PaperBridgeFit.BridgeData.ParamSpace.{u_1,
                                                                                                                      u_2}
                                                                                                                    B)))
                                                                                                            (And
                                                                                                              (∀
                                                                                                                (p :
                                                                                                                  Nat),
                                                                                                                Membership.mem.{0,
                                                                                                                      0}
                                                                                                                    monitoredPrimes
                                                                                                                    p →
                                                                                                                  LE.le.{0}
                                                                                                                    (abs.{0}
                                                                                                                      (HSub.hSub.{0,
                                                                                                                          0,
                                                                                                                          0}
                                                                                                                        (markedTarget
                                                                                                                          p)
                                                                                                                        (Erdos390.Full.PaperBridgeFit.BridgeData.paperMoment.{u_1,
                                                                                                                            u_2}
                                                                                                                          B
                                                                                                                          (Erdos390.Full.PaperBridgeFit.BridgeData.markedValuation.{u_1,
                                                                                                                              u_2}
                                                                                                                            B
                                                                                                                            p)
                                                                                                                          (path
                                                                                                                            (1 :
                                                                                                                              Real)))))
                                                                                                                    (HDiv.hDiv.{0,
                                                                                                                        0,
                                                                                                                        0}
                                                                                                                      (HMul.hMul.{0,
                                                                                                                          0,
                                                                                                                          0}
                                                                                                                        (HAdd.hAdd.{0,
                                                                                                                            0,
                                                                                                                            0}
                                                                                                                          Cinitial
                                                                                                                          (HMul.hMul.{0,
                                                                                                                              0,
                                                                                                                              0}
                                                                                                                            Cmass
                                                                                                                            Crow))
                                                                                                                        N)
                                                                                                                      (HMul.hMul.{0,
                                                                                                                          0,
                                                                                                                          0}
                                                                                                                        (↑p)
                                                                                                                        (Erdos390.Full.PaperBridgeFit.BridgeData.L.{u_1,
                                                                                                                            u_2}
                                                                                                                          B))))
                                                                                                              (And
                                                                                                                (∀
                                                                                                                  (t :
                                                                                                                    Real),
                                                                                                                  Membership.mem.{0,
                                                                                                                        0}
                                                                                                                      (Set.Icc.{0}
                                                                                                                        (0 :
                                                                                                                          Real)
                                                                                                                        (1 :
                                                                                                                          Real))
                                                                                                                      t →
                                                                                                                    ∀
                                                                                                                      (x :
                                                                                                                        Nat),
                                                                                                                      Membership.mem.{0,
                                                                                                                          0}
                                                                                                                        (Set.Icc.{0}
                                                                                                                          (0 :
                                                                                                                            Real)
                                                                                                                          (1 :
                                                                                                                            Real))
                                                                                                                        (Erdos390.Full.PaperBridgeFit.BridgeData.ambientCombinedWeight.{u_1,
                                                                                                                            u_2}
                                                                                                                          B
                                                                                                                          (Erdos390.Full.PaperBridgeFit.BridgeData.frozenAmbientWeight.{u_3}
                                                                                                                            fixedValue
                                                                                                                            fixedWeight)
                                                                                                                          (path
                                                                                                                            t)
                                                                                                                          x))
                                                                                                                (And
                                                                                                                  (∀
                                                                                                                    (t :
                                                                                                                      Real),
                                                                                                                    Membership.mem.{0,
                                                                                                                          0}
                                                                                                                        (Set.Icc.{0}
                                                                                                                          (0 :
                                                                                                                            Real)
                                                                                                                          (1 :
                                                                                                                            Real))
                                                                                                                        t →
                                                                                                                      ∀
                                                                                                                        (f :
                                                                                                                          Fixed),
                                                                                                                        Eq.{1}
                                                                                                                          (Erdos390.Full.PaperBridgeFit.BridgeData.combinedWeight.{u_1,
                                                                                                                              u_2,
                                                                                                                              u_3}
                                                                                                                            B
                                                                                                                            fixedWeight
                                                                                                                            (path
                                                                                                                              t)
                                                                                                                            (Sum.inl.{u_3,
                                                                                                                                u_1}
                                                                                                                              f))
                                                                                                                          (Erdos390.Full.PaperBridgeFit.BridgeData.combinedWeight.{u_1,
                                                                                                                              u_2,
                                                                                                                              u_3}
                                                                                                                            B
                                                                                                                            fixedWeight
                                                                                                                            (0 :
                                                                                                                              Erdos390.Full.PaperBridgeFit.BridgeData.ParamSpace.{u_1,
                                                                                                                                  u_2}
                                                                                                                                B)
                                                                                                                            (Sum.inl.{u_3,
                                                                                                                                u_1}
                                                                                                                              f)))
                                                                                                                  (And
                                                                                                                    (∀
                                                                                                                      (t :
                                                                                                                        Real),
                                                                                                                      Membership.mem.{0,
                                                                                                                            0}
                                                                                                                          (Set.Icc.{0}
                                                                                                                            (0 :
                                                                                                                              Real)
                                                                                                                            (1 :
                                                                                                                              Real))
                                                                                                                          t →
                                                                                                                        Eq.{1}
                                                                                                                          (∑
                                                                                                                            m,
                                                                                                                            Erdos390.Full.PaperBridgeFit.BridgeData.activeCoordinateWeight.{u_1,
                                                                                                                                u_2}
                                                                                                                              B
                                                                                                                              (path
                                                                                                                                t)
                                                                                                                              m)
                                                                                                                          (Erdos390.Full.PaperBridgeFit.BridgeData.q.{u_1,
                                                                                                                              u_2}
                                                                                                                            B))
                                                                                                                    (∀
                                                                                                                      (t :
                                                                                                                        Real),
                                                                                                                      Membership.mem.{0,
                                                                                                                            0}
                                                                                                                          (Set.Icc.{0}
                                                                                                                            (0 :
                                                                                                                              Real)
                                                                                                                            (1 :
                                                                                                                              Real))
                                                                                                                          t →
                                                                                                                        Eq.{1}
                                                                                                                          (∑
                                                                                                                            x,
                                                                                                                            Erdos390.Full.PaperBridgeFit.BridgeData.combinedWeight.{u_1,
                                                                                                                                u_2,
                                                                                                                                u_3}
                                                                                                                              B
                                                                                                                              fixedWeight
                                                                                                                              (path
                                                                                                                                t)
                                                                                                                              x)
                                                                                                                          ↑quota)))))))))))))) := by
  exact @Erdos390.Full.PaperBridgeFit.BridgeData.exists_physicallyCenteredFixedPartitionFit_of_canonicalTwoStageOutputs
