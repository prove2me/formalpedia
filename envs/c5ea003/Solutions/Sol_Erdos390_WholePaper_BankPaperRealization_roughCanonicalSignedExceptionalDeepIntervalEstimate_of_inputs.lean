-- Prove2me | solution 1 for Erdos390.WholePaper.BankPaperRealization.roughCanonicalSignedExceptionalDeepIntervalEstimate_of_inputs
-- status  : ACCEPTED   (prove)
-- author  : @doctosil
-- created : 2026-09-17T16:05:54.077271+00:00
-- url     : https://prove2.me/submissions/d79e5742-e82e-4583-bb92-d4b48ed9ab3e

import Mathlib
import Definitions.Def_erdos390_source_bank_interface
import Definitions.Def_erdos390_dickman_step_function
import Theorems.Thm_MediumPNT
import Definitions.Def_erdos390_analytic_foundations_001
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_product_bound
import Theorems.Thm_Erdos390_Full_DickmanBasic_rho_pos_on_zero_five
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_secondDerivative_first_bound
import Definitions.Def_erdos390_analytic_foundations_008
import Definitions.Def_erdos390_analytic_foundations_009
import Theorems.Thm_Erdos390_WholePaper_BankPaperRealization_roughCanonicalFourFiveDeep_shortFreezingEndpointRate_le

/- Source module: Erdos390.WholePaper.RoughSaiasSharpCanonicalRowPaperScale -/
section


/-!
# Canonical sharp Saias row-scale geometry

This file specializes the closed sharp endpoint and fixed-head estimates to
the paper's literal balanced raw point.  The high-block multiplicity is
written as `K0 + 1`, so its positivity is built into the data rather than
assumed separately.
-/

open Filter Topology
open scoped BigOperators ArithmeticFunction.Moebius

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.DickmanBasic
open Erdos390.Full.Scale
open Erdos390.Full.StructuredCells

noncomputable section

/-! ## Uniform control of the literal balanced coefficient -/







/-! ## Fixed constants for the three row ledgers -/















/-! ## Quotient and logarithmic geometry -/

/-- A natural quotient differs from the corresponding real quotient by
strictly less than one. -/
theorem roughNatQuotient_sub_realQuotient_abs_lt_one
    {N r : ℕ} (hr : 0 < r) :
    |(((N / r : ℕ) : ℝ)) - (N : ℝ) / (r : ℝ)| < 1 := by
  have hrReal : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr
  have hle :
      (((N / r : ℕ) : ℝ)) ≤ (N : ℝ) / (r : ℝ) :=
    Nat.cast_div_le
  rw [abs_of_nonpos (sub_nonpos.mpr hle), neg_sub]
  have hdecomp :=
    congrArg (fun z : ℕ ↦ (z : ℝ)) (Nat.div_add_mod N r)
  norm_num only [Nat.cast_add, Nat.cast_mul] at hdecomp
  have hmod : (((N % r : ℕ) : ℝ)) < (r : ℝ) := by
    exact_mod_cast Nat.mod_lt N hr
  calc
    (N : ℝ) / (r : ℝ) - ((N / r : ℕ) : ℝ) =
        ((N % r : ℕ) : ℝ) / (r : ℝ) := by
      field_simp [hrReal.ne']
      nlinarith
    _ < 1 := (div_lt_one hrReal).2 hmod

/-- The real quotient lies below the natural quotient plus one. -/
theorem roughRealQuotient_lt_natQuotient_add_one
    {N r : ℕ} (hr : 0 < r) :
    (N : ℝ) / (r : ℝ) < ((N / r : ℕ) : ℝ) + 1 := by
  have hfloor :=
    roughNatQuotient_sub_realQuotient_abs_lt_one
      (N := N) hr
  rw [abs_lt] at hfloor
  linarith

























/-! ## The balanced Dickman main ledger -/





/-! ## The weighted sharp Saias transition ledger -/



/-! ## Absorption of the sharp fixed-head divisor sum -/



/-! ## One unified canonical raw-row allowance -/













end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankPaperFourFiveFixedSimplexKernel -/
section


/-!
# Fixed-simplex kernels for the four/five chamber

For `m = j - 1`, the paper moves the continuum ordered-prime kernel to the
fixed simplex

`Delta_m = {z_i >= 0, sum z_i <= 1}`

by writing `T = u - j` and `s_i = 1 + T z_i`.  The resulting integrand is

`T^m / (prod_i (1 + T z_i) * (1 + T * (1 - sum_i z_i)))`.

This file defines that expression literally for every finite dimension,
proves its parameter derivative, justifies differentiation under the
compact-simplex integral, and packages the four kernels needed in the
ordered mixture.  On `4.1 <= u <= 4.7`, all relevant parameters satisfy
`0 < T < 3`, so every denominator is bounded away from zero.  Compactness
then supplies one common bound for the mixture and its continuous first
derivative.
-/

open scoped BigOperators
open Set

noncomputable section

namespace Erdos390.WholePaper.BankPaperRealization

open MeasureTheory

/-! ## The fixed simplex and its rational integrand -/



theorem isClosed_fourFiveClosedSimplex (m : Nat) :
    IsClosed (fourFiveClosedSimplex m) := by
  have hnonneg : IsClosed {z : Fin m -> Real | ∀ i, 0 <= z i} := by
    rw [Set.setOf_forall]
    exact isClosed_iInter fun i =>
      isClosed_le continuous_const (continuous_apply i)
  have hsum : IsClosed {z : Fin m -> Real | (∑ i, z i) <= 1} := by
    exact isClosed_le
      (continuous_finset_sum Finset.univ fun i _hi => continuous_apply i)
      continuous_const
  simpa only [fourFiveClosedSimplex, Set.setOf_and] using hnonneg.inter hsum

theorem fourFiveClosedSimplex_subset_Icc (m : Nat) :
    fourFiveClosedSimplex m ⊆
      Set.Icc (0 : Fin m -> Real) (1 : Fin m -> Real) := by
  intro z hz
  constructor
  · intro i
    simpa only [Pi.zero_apply] using hz.1 i
  · intro i
    change z i <= 1
    exact (Finset.single_le_sum (fun k _hk => hz.1 k)
      (Finset.mem_univ i)).trans hz.2

theorem isCompact_fourFiveClosedSimplex (m : Nat) :
    IsCompact (fourFiveClosedSimplex m) :=
  isCompact_Icc.of_isClosed_subset
    (isClosed_fourFiveClosedSimplex m)
    (fourFiveClosedSimplex_subset_Icc m)















theorem fourFiveSimplexDenominator_pos
    {m : Nat} {T : Real} {z : Fin m -> Real}
    (hT : 0 <= T) (hz : z ∈ fourFiveClosedSimplex m) :
    0 < fourFiveSimplexDenominator m T z := by
  have hfactor : ∀ i : Fin m, 0 < 1 + T * z i := by
    intro i
    have hmul : 0 <= T * z i := mul_nonneg hT (hz.1 i)
    linarith
  have hprod : 0 < fourFiveSimplexFactorProduct m T z := by
    unfold fourFiveSimplexFactorProduct
    exact Finset.prod_pos fun i _hi => hfactor i
  have hslack : 0 <= 1 - ∑ i, z i := sub_nonneg.mpr hz.2
  have hrem : 0 < fourFiveSimplexRemainderFactor m T z := by
    unfold fourFiveSimplexRemainderFactor
    have := mul_nonneg hT hslack
    linarith
  exact mul_pos hprod hrem

private theorem continuous_fourFiveSimplexDenominator (m : Nat) :
    Continuous (fun p : Real × (Fin m -> Real) =>
      fourFiveSimplexDenominator m p.1 p.2) := by
  unfold fourFiveSimplexDenominator fourFiveSimplexFactorProduct
    fourFiveSimplexRemainderFactor
  fun_prop

private theorem continuous_fourFiveSimplexDenominatorDerivative (m : Nat) :
    Continuous (fun p : Real × (Fin m -> Real) =>
      fourFiveSimplexDenominatorDerivative m p.1 p.2) := by
  unfold fourFiveSimplexDenominatorDerivative
    fourFiveSimplexFactorProductDerivative
    fourFiveSimplexFactorProduct fourFiveSimplexRemainderFactor
  fun_prop

theorem continuousOn_fourFiveFixedSimplexIntegrand (m : Nat) :
    ContinuousOn
      (fun p : Real × (Fin m -> Real) =>
        fourFiveFixedSimplexIntegrand m p.1 p.2)
      (Set.Icc (0 : Real) 3 ×ˢ fourFiveClosedSimplex m) := by
  intro p hp
  have hden : 0 < fourFiveSimplexDenominator m p.1 p.2 :=
    fourFiveSimplexDenominator_pos hp.1.1 hp.2
  apply ContinuousAt.continuousWithinAt
  unfold fourFiveFixedSimplexIntegrand
  exact (continuousAt_fst.pow m).div
    (continuous_fourFiveSimplexDenominator m).continuousAt hden.ne'

theorem continuousOn_fourFiveFixedSimplexIntegrandDerivative (m : Nat) :
    ContinuousOn
      (fun p : Real × (Fin m -> Real) =>
        fourFiveFixedSimplexIntegrandDerivative m p.1 p.2)
      (Set.Icc (0 : Real) 3 ×ˢ fourFiveClosedSimplex m) := by
  intro p hp
  have hden : 0 < fourFiveSimplexDenominator m p.1 p.2 :=
    fourFiveSimplexDenominator_pos hp.1.1 hp.2
  apply ContinuousAt.continuousWithinAt
  unfold fourFiveFixedSimplexIntegrandDerivative
  have hnum : ContinuousAt
      (fun q : Real × (Fin m -> Real) =>
        (((m : Real) * q.1 ^ (m - 1)) *
              fourFiveSimplexDenominator m q.1 q.2 -
            q.1 ^ m *
              fourFiveSimplexDenominatorDerivative m q.1 q.2)) p := by
    exact ((continuousAt_const.mul (continuousAt_fst.pow (m - 1))).mul
      (continuous_fourFiveSimplexDenominator m).continuousAt).sub
        ((continuousAt_fst.pow m).mul
          (continuous_fourFiveSimplexDenominatorDerivative m).continuousAt)
  exact hnum.div
    ((continuous_fourFiveSimplexDenominator m).continuousAt.pow 2)
    (pow_ne_zero 2 hden.ne')

private theorem hasDerivAt_fourFiveSimplexFactorProduct
    (m : Nat) (T : Real) (z : Fin m -> Real) :
    HasDerivAt (fun t => fourFiveSimplexFactorProduct m t z)
      (fourFiveSimplexFactorProductDerivative m T z) T := by
  have hfactor : ∀ i ∈ (Finset.univ : Finset (Fin m)),
      HasDerivAt (fun t : Real => 1 + t * z i) (z i) T := by
    intro i _hi
    convert (hasDerivAt_const T (1 : Real)).add
      ((hasDerivAt_id T).mul_const (z i)) using 1
    ring
  simpa [fourFiveSimplexFactorProduct,
    fourFiveSimplexFactorProductDerivative, smul_eq_mul] using
      (HasDerivAt.fun_finset_prod hfactor)

private theorem hasDerivAt_fourFiveSimplexRemainderFactor
    (m : Nat) (T : Real) (z : Fin m -> Real) :
    HasDerivAt (fun t => fourFiveSimplexRemainderFactor m t z)
      (1 - ∑ i, z i) T := by
  convert (hasDerivAt_const T (1 : Real)).add
    ((hasDerivAt_id T).mul_const (1 - ∑ i, z i)) using 1
  ring

private theorem hasDerivAt_fourFiveSimplexDenominator
    (m : Nat) (T : Real) (z : Fin m -> Real) :
    HasDerivAt (fun t => fourFiveSimplexDenominator m t z)
      (fourFiveSimplexDenominatorDerivative m T z) T := by
  have hp := hasDerivAt_fourFiveSimplexFactorProduct m T z
  have hr := hasDerivAt_fourFiveSimplexRemainderFactor m T z
  simpa [fourFiveSimplexDenominator,
    fourFiveSimplexDenominatorDerivative] using hp.mul hr

theorem hasDerivAt_fourFiveFixedSimplexIntegrand
    {m : Nat} {T : Real} {z : Fin m -> Real}
    (hT : 0 <= T) (hz : z ∈ fourFiveClosedSimplex m) :
    HasDerivAt (fun t => fourFiveFixedSimplexIntegrand m t z)
      (fourFiveFixedSimplexIntegrandDerivative m T z) T := by
  have hpow : HasDerivAt (fun t : Real => t ^ m)
      ((m : Real) * T ^ (m - 1)) T :=
    hasDerivAt_pow m T
  have hden := hasDerivAt_fourFiveSimplexDenominator m T z
  have hdenne : fourFiveSimplexDenominator m T z ≠ 0 :=
    (fourFiveSimplexDenominator_pos hT hz).ne'
  simpa [fourFiveFixedSimplexIntegrand,
    fourFiveFixedSimplexIntegrandDerivative] using
      hpow.div hden hdenne

/-! ## Differentiation under the compact-simplex integral -/





private theorem integrable_fourFiveFixedSimplexIntegrand
    {m : Nat} {T : Real} (hT : T ∈ Set.Icc (0 : Real) 3) :
    Integrable (fourFiveFixedSimplexIntegrand m T)
      (volume.restrict (fourFiveClosedSimplex m)) := by
  change IntegrableOn (fourFiveFixedSimplexIntegrand m T)
    (fourFiveClosedSimplex m) volume
  apply ContinuousOn.integrableOn_compact
    (isCompact_fourFiveClosedSimplex m)
  exact (continuousOn_fourFiveFixedSimplexIntegrand m).comp
    (continuous_const.prodMk continuous_id).continuousOn
    (fun z hz => ⟨hT, hz⟩)

private theorem integrable_fourFiveFixedSimplexIntegrandDerivative
    {m : Nat} {T : Real} (hT : T ∈ Set.Icc (0 : Real) 3) :
    Integrable (fourFiveFixedSimplexIntegrandDerivative m T)
      (volume.restrict (fourFiveClosedSimplex m)) := by
  change IntegrableOn (fourFiveFixedSimplexIntegrandDerivative m T)
    (fourFiveClosedSimplex m) volume
  apply ContinuousOn.integrableOn_compact
    (isCompact_fourFiveClosedSimplex m)
  exact (continuousOn_fourFiveFixedSimplexIntegrandDerivative m).comp
    (continuous_const.prodMk continuous_id).continuousOn
    (fun z hz => ⟨hT, hz⟩)

theorem hasDerivAt_fourFiveFixedSimplexKernel
    {m : Nat} {T : Real} (hT : T ∈ Set.Ioo (0 : Real) 3) :
    HasDerivAt (fourFiveFixedSimplexKernel m)
      (fourFiveFixedSimplexKernelDerivative m T) T := by
  let P : Set (Real × (Fin m -> Real)) :=
    Set.Icc (0 : Real) 3 ×ˢ fourFiveClosedSimplex m
  have hPcompact : IsCompact P :=
    isCompact_Icc.prod (isCompact_fourFiveClosedSimplex m)
  obtain ⟨C, hC⟩ := hPcompact.exists_bound_of_continuousOn
    (continuousOn_fourFiveFixedSimplexIntegrandDerivative m)
  have hsimplexMeas : MeasurableSet (fourFiveClosedSimplex m) :=
    (isClosed_fourFiveClosedSimplex m).measurableSet
  have hnhds : Set.Ioo (0 : Real) 3 ∈ nhds T :=
    Ioo_mem_nhds hT.1 hT.2
  have hresult := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (fourFiveClosedSimplex m))
    (F := fourFiveFixedSimplexIntegrand m)
    (x₀ := T)
    (bound := fun _ : Fin m -> Real => C)
    (s := Set.Ioo (0 : Real) 3) hnhds
    (by
      filter_upwards [hnhds] with t ht
      exact (integrable_fourFiveFixedSimplexIntegrand
        ⟨ht.1.le, ht.2.le⟩).aestronglyMeasurable)
    (integrable_fourFiveFixedSimplexIntegrand
      ⟨hT.1.le, hT.2.le⟩)
    (F' := fourFiveFixedSimplexIntegrandDerivative m)
    (integrable_fourFiveFixedSimplexIntegrandDerivative
      ⟨hT.1.le, hT.2.le⟩).aestronglyMeasurable
    (by
      filter_upwards [ae_restrict_mem hsimplexMeas] with z hz
      intro t ht
      exact hC (t, z) ⟨⟨ht.1.le, ht.2.le⟩, hz⟩)
    (by
      change IntegrableOn (fun _ : Fin m -> Real => C)
        (fourFiveClosedSimplex m) volume
      exact integrableOn_const
        (isCompact_fourFiveClosedSimplex m).measure_ne_top)
    (by
      filter_upwards [ae_restrict_mem hsimplexMeas] with z hz
      intro t ht
      exact hasDerivAt_fourFiveFixedSimplexIntegrand ht.1.le hz)
  simpa [fourFiveFixedSimplexKernel,
    fourFiveFixedSimplexKernelDerivative] using hresult.2





/-! ## The four ordered continuum kernels -/

















theorem hasDerivAt_fourFiveContinuumKernelOne
    {u : Real} (hu : u ≠ 0) :
    HasDerivAt fourFiveContinuumKernelOne
      (fourFiveContinuumKernelOneDerivative u) u := by
  simpa [fourFiveContinuumKernelOne,
    fourFiveContinuumKernelOneDerivative] using hasDerivAt_inv hu

theorem hasDerivAt_fourFiveContinuumKernelTwo
    {u : Real} (hu : u ∈ Set.Icc ((41 : Real) / 10) ((47 : Real) / 10)) :
    HasDerivAt fourFiveContinuumKernelTwo
      (fourFiveContinuumKernelTwoDerivative u) u := by
  have hT : u - 2 ∈ Set.Ioo (0 : Real) 3 := by
    constructor <;> linarith [hu.1, hu.2]
  have h := hasDerivAt_fourFiveFixedSimplexKernel (m := 1) hT
  convert h.comp u ((hasDerivAt_id u).sub_const 2) using 1;
    simp [fourFiveContinuumKernelTwoDerivative]

theorem hasDerivAt_fourFiveContinuumKernelThree
    {u : Real} (hu : u ∈ Set.Icc ((41 : Real) / 10) ((47 : Real) / 10)) :
    HasDerivAt fourFiveContinuumKernelThree
      (fourFiveContinuumKernelThreeDerivative u) u := by
  have hT : u - 3 ∈ Set.Ioo (0 : Real) 3 := by
    constructor <;> linarith [hu.1, hu.2]
  have h := hasDerivAt_fourFiveFixedSimplexKernel (m := 2) hT
  convert h.comp u ((hasDerivAt_id u).sub_const 3) using 1;
    simp [fourFiveContinuumKernelThreeDerivative]

theorem hasDerivAt_fourFiveContinuumKernelFour
    {u : Real} (hu : u ∈ Set.Icc ((41 : Real) / 10) ((47 : Real) / 10)) :
    HasDerivAt fourFiveContinuumKernelFour
      (fourFiveContinuumKernelFourDerivative u) u := by
  have hT : u - 4 ∈ Set.Ioo (0 : Real) 3 := by
    constructor <;> linarith [hu.1, hu.2]
  have h := hasDerivAt_fourFiveFixedSimplexKernel (m := 3) hT
  convert h.comp u ((hasDerivAt_id u).sub_const 4) using 1;
    simp [fourFiveContinuumKernelFourDerivative]











theorem hasDerivAt_fourFiveContinuumMixtureKernel
    {u : Real} (hu : u ∈ Set.Icc ((41 : Real) / 10) ((47 : Real) / 10)) :
    HasDerivAt fourFiveContinuumMixtureKernel
      (fourFiveContinuumMixtureKernelDerivative u) u := by
  have hu0 : u ≠ 0 := by linarith [hu.1]
  have h1 := hasDerivAt_fourFiveContinuumKernelOne hu0
  have h2 := (hasDerivAt_fourFiveContinuumKernelTwo hu).div_const 2
  have h3 := (hasDerivAt_fourFiveContinuumKernelThree hu).div_const 6
  have h4 := (hasDerivAt_fourFiveContinuumKernelFour hu).div_const 24
  simpa [fourFiveContinuumMixtureKernel,
    fourFiveContinuumMixtureKernelDerivative] using
      ((h1.add h2).add h3).add h4

theorem continuousOn_fourFiveContinuumMixtureKernel :
    ContinuousOn fourFiveContinuumMixtureKernel
      (Set.Icc ((41 : Real) / 10) ((47 : Real) / 10)) := by
  intro u hu
  exact (hasDerivAt_fourFiveContinuumMixtureKernel hu).continuousAt.continuousWithinAt





end Erdos390.WholePaper.BankPaperRealization

end

/- Source module: Erdos390.WholePaper.BankPaperFourFiveSignedCoreErrorAdapter -/
section


/-!
# Error adapter from the four/five assembly to a signed smooth core

The four/five continuum calculation ends with a completely explicit error
ledger.  This file performs the remaining algebra needed by the signed
exceptional-core argument:

* compress the four factorially weighted assembly errors to one
  `Z / log(y)^3` bound;
* add the repeated-prime transfer and convert `log(y)` to the paper scale
  `L`;
* freeze the continuum mixture kernel at one reference logarithmic
  coordinate;
* expose the exact balanced normalization for the paper multiplicity
  `K0 + 1`;
* combine three independently estimated physical intervals without losing
  the signed periodic main term.

The module deliberately does not identify a literal smooth-core fibre with
the three rough intervals.  That finite reindexing is an independent input
to the final connector.
-/

open Filter Topology
open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel
open Erdos390.Full.PrimeBandQuadrature
open Erdos390.Full.Scale

noncomputable section

namespace BankPaperRealization

/-! ## Compression of the explicit four-layer error ledger -/

















/-! ## Freezing the common continuum kernel -/

/-- The compact `C^1` certificate gives the literal Lipschitz estimate
needed to freeze the mixture kernel at one reference point. -/
theorem abs_fourFiveContinuumMixtureKernel_sub_le_of_C1
    {C u v : Real}
    (hu : u ∈ Set.Icc ((41 : Real) / 10) ((47 : Real) / 10))
    (hv : v ∈ Set.Icc ((41 : Real) / 10) ((47 : Real) / 10))
    (_hC : 0 <= C)
    (hderiv : ∀ x ∈
      Set.Icc ((41 : Real) / 10) ((47 : Real) / 10),
      |fourFiveContinuumMixtureKernelDerivative x| <= C) :
    |fourFiveContinuumMixtureKernel u -
        fourFiveContinuumMixtureKernel v| <= C * |u - v| := by
  have hdiff (x : Real)
      (hx : x ∈ Set.Icc ((41 : Real) / 10) ((47 : Real) / 10)) :
      DifferentiableAt Real fourFiveContinuumMixtureKernel x :=
    (hasDerivAt_fourFiveContinuumMixtureKernel hx).differentiableAt
  have hbound (x : Real)
      (hx : x ∈ Set.Icc ((41 : Real) / 10) ((47 : Real) / 10)) :
      ‖deriv fourFiveContinuumMixtureKernel x‖ <= C := by
    rw [(hasDerivAt_fourFiveContinuumMixtureKernel hx).deriv,
      Real.norm_eq_abs]
    exact hderiv x hx
  simpa only [Real.norm_eq_abs] using
    Convex.norm_image_sub_le_of_norm_deriv_le
      hdiff hbound
      (convex_Icc ((41 : Real) / 10) ((47 : Real) / 10))
      hv hu

/-- Paper-range hypotheses also supply interval integrability of the common
mixture kernel.  This is the integrability input used by kernel freezing. -/
theorem intervalIntegrable_fourFiveContinuumMixtureKernel_of_paperRange
    {y A B : Nat}
    (hy : 2 <= y) (hyA : y <= A) (hAB : A <= B)
    (hrange : ∀ t ∈ Set.Icc (A : Real) (B : Real),
      Real.log t / Real.log (y : Real) ∈
        Set.Icc ((41 : Real) / 10) ((47 : Real) / 10)) :
    IntervalIntegrable
      (fun t : Real => fourFiveContinuumMixtureKernel
        (Real.log t / Real.log (y : Real)))
      MeasureTheory.volume (A : Real) (B : Real) := by
  have hABReal : (A : Real) <= (B : Real) := by exact_mod_cast hAB
  have hyReal : (0 : Real) < (y : Real) := by positivity
  have hyAReal : (y : Real) <= (A : Real) := by exact_mod_cast hyA
  have hcoord : ContinuousOn
      (fun t : Real => Real.log t / Real.log (y : Real))
      (Set.Icc (A : Real) (B : Real)) := by
    intro t ht
    have ht0 : t ≠ 0 :=
      ne_of_gt (hyReal.trans_le (hyAReal.trans ht.1))
    exact ((Real.continuousAt_log ht0).div_const
      (Real.log (y : Real))).continuousWithinAt
  exact
    (continuousOn_fourFiveContinuumMixtureKernel.comp'
      hcoord hrange).intervalIntegrable_of_Icc hABReal

/-- Freeze the one-integral continuum main at `u0`.

`D` is a geometric bound for the normalized logarithmic displacement on the
physical interval.  This separates the universal kernel argument from the
three interval-specific endpoint geometry. -/
theorem abs_fourFiveContinuumMixtureIntegralMain_sub_frozen_le
    {y A B : Nat} {C D u0 : Real}
    (hAB : A <= B)
    (hlog : 0 < Real.log (y : Real))
    (hC : 0 <= C) (_hD : 0 <= D)
    (hu0 : u0 ∈ Set.Icc ((41 : Real) / 10) ((47 : Real) / 10))
    (hrange : ∀ t ∈ Set.Icc (A : Real) (B : Real),
      Real.log t / Real.log (y : Real) ∈
        Set.Icc ((41 : Real) / 10) ((47 : Real) / 10))
    (hdisplacement : ∀ t ∈ Set.Icc (A : Real) (B : Real),
      |Real.log t / Real.log (y : Real) - u0| <= D)
    (hderiv : ∀ x ∈
      Set.Icc ((41 : Real) / 10) ((47 : Real) / 10),
      |fourFiveContinuumMixtureKernelDerivative x| <= C)
    (hintegrable : IntervalIntegrable
      (fun t : Real => fourFiveContinuumMixtureKernel
        (Real.log t / Real.log (y : Real)))
      MeasureTheory.volume (A : Real) (B : Real)) :
    |fourFiveContinuumMixtureIntegralMain y A B -
        (((B : Real) - (A : Real)) / Real.log (y : Real)) *
          fourFiveContinuumMixtureKernel u0| <=
      ((((B : Real) - (A : Real)) / Real.log (y : Real)) * C) * D := by
  let F : Real -> Real := fun t =>
    fourFiveContinuumMixtureKernel
      (Real.log t / Real.log (y : Real))
  let K0 := fourFiveContinuumMixtureKernel u0
  have hABReal : (A : Real) <= (B : Real) := by exact_mod_cast hAB
  have hlength0 : 0 <= (B : Real) - (A : Real) := sub_nonneg.mpr hABReal
  have hpoint (t : Real) (ht : t ∈ Set.uIcc (A : Real) (B : Real)) :
      |F t - K0| <= C * D := by
    have htIcc : t ∈ Set.Icc (A : Real) (B : Real) := by
      simpa only [Set.uIcc_of_le hABReal] using ht
    exact
      (abs_fourFiveContinuumMixtureKernel_sub_le_of_C1
        (hrange t htIcc) hu0 hC hderiv).trans
        (mul_le_mul_of_nonneg_left (hdisplacement t htIcc) hC)
  have hnorm :=
    intervalIntegral.norm_integral_le_of_norm_le_const
      (f := fun t => F t - K0)
      (fun t ht => by
        simpa only [Real.norm_eq_abs] using
          hpoint t (Set.uIoc_subset_uIcc ht))
  have hrewrite :
      fourFiveContinuumMixtureIntegralMain y A B -
          (((B : Real) - (A : Real)) / Real.log (y : Real)) * K0 =
        (1 / Real.log (y : Real)) *
          (∫ t in (A : Real)..(B : Real), F t - K0) := by
    unfold fourFiveContinuumMixtureIntegralMain
    rw [intervalIntegral.integral_sub hintegrable intervalIntegrable_const]
    simp only [intervalIntegral.integral_const, smul_eq_mul]
    ring
  rw [hrewrite, abs_mul, abs_of_nonneg (one_div_nonneg.mpr hlog.le)]
  calc
    (1 / Real.log (y : Real)) *
        |∫ t in (A : Real)..(B : Real), F t - K0| <=
      (1 / Real.log (y : Real)) *
        ((C * D) * |(B : Real) - (A : Real)|) :=
      mul_le_mul_of_nonneg_left
        (by simpa only [Real.norm_eq_abs] using hnorm)
        (one_div_nonneg.mpr hlog.le)
    _ =
      ((((B : Real) - (A : Real)) / Real.log (y : Real)) * C) * D := by
      rw [abs_of_nonneg hlength0]
      ring

/-! ### Quotient endpoints and ideal physical lengths -/



/-- Combine an arithmetic-to-continuum error, kernel freezing at the literal
integer interval length, and the single quotient-endpoint discrepancy.

This small triangle lemma is what turns the natural endpoints used by
`fourFiveRoughInterval` into the ideal lengths appearing in the balanced
normalization. -/
theorem abs_count_sub_idealFrozen_le
    {count main kernel literalLength idealLength
      arithmeticError freezeError endpointError kernelBound : Real}
    (harithmetic : |count - main| <= arithmeticError)
    (hfreeze : |main - kernel * literalLength| <= freezeError)
    (hlength : |literalLength - idealLength| <= endpointError)
    (hkernel : |kernel| <= kernelBound)
    (_hendpoint : 0 <= endpointError) (hkernelBound : 0 <= kernelBound) :
    |count - kernel * idealLength| <=
      arithmeticError + freezeError + kernelBound * endpointError := by
  have hkernelLength :
      |kernel * literalLength - kernel * idealLength| <=
        kernelBound * endpointError := by
    rw [← mul_sub, abs_mul]
    exact mul_le_mul hkernel hlength (abs_nonneg _)
      hkernelBound
  calc
    |count - kernel * idealLength| =
        |(count - main) +
          (main - kernel * literalLength) +
          (kernel * literalLength - kernel * idealLength)| := by ring_nf
    _ <= |count - main| +
        |main - kernel * literalLength| +
        |kernel * literalLength - kernel * idealLength| := by
      exact (abs_add_le _ _).trans
        (add_le_add_left (abs_add_le _ _) _)
    _ <= arithmeticError + freezeError +
        kernelBound * endpointError :=
      add_le_add (add_le_add harithmetic hfreeze) hkernelLength

/-! ## Exact `K0+1` balance and signed three-interval algebra -/







/-! ## Positive cutoff-band algebra -/



end BankPaperRealization

end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankPaperCanonicalSignedExceptionalClippedIntervalGeometry -/
section


/-!
# Endpoint geometry for the three clipped signed exceptional intervals

This file isolates the elementary endpoint work needed before applying the
four/five rough-interval estimate to the three physical intervals in the
signed exceptional core.

There are two separate layers.

* A common endpoint certificate controls the literal real exceptional floor,
  the fifth-power rough chamber, and the padded logarithmic coordinate range.
* For a fixed positive smooth core, each clipped physical interval is either
  empty or satisfies exactly the endpoint hypotheses consumed by the
  four/five counting and kernel-freezing adapters.

The common certificate is proved eventually from
`0 <= deltaStar < 1/18`.  In particular, the proof retains both rounding
operations: the exceptional lower endpoint is a natural floor, while the
smooth-core prefix is bounded by twice the natural ceiling
`tangentPaperExceptionalCutoff`.
-/

open Filter Topology

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel
open Erdos390.Full.Scale
open Erdos390.Full.PaperScaleMarkedCell

noncomputable section

namespace BankPaperRealization

/-! ## Named endpoints and the exact adapter geometry -/





theorem roughCanonicalExceptionalClippedRoughInterval_eq_endpoints
    (n b lo hi : Nat) (deltaStar : Real) :
    roughCanonicalExceptionalClippedRoughInterval
        n deltaStar b lo hi =
      fourFiveRoughInterval (yNat n)
        (roughCanonicalExceptionalPhysicalLowerEndpoint
          n deltaStar b lo)
        (roughCanonicalExceptionalPhysicalUpperEndpoint b hi) := by
  rfl







/-! ## Empty-interval handling -/

theorem fourFiveRoughInterval_eq_empty_of_upper_le_lower
    {y A B : Nat} (hBA : B <= A) :
    fourFiveRoughInterval y A B = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro r hr
  have hrData := mem_fourFiveRoughInterval.mp hr
  omega





/-! ## A common certificate gives every nonempty clipped interval -/

theorem roughCanonicalExceptionalClippedInterval_geometry
    {n b lo hi : Nat} {deltaStar : Real}
    (hcommon :
      RoughCanonicalExceptionalCommonEndpointGeometry n deltaStar)
    (hb : b ∈ Finset.Icc 1
      (2 * tangentPaperExceptionalCutoff deltaStar n))
    (hAB :
      roughCanonicalExceptionalPhysicalLowerEndpoint
          n deltaStar b lo <=
        roughCanonicalExceptionalPhysicalUpperEndpoint b hi)
    (hhi : hi <= 3 * n) :
    RoughCanonicalExceptionalPhysicalIntervalGeometry
      n deltaStar b
      (roughCanonicalExceptionalPhysicalLowerEndpoint
        n deltaStar b lo)
      (roughCanonicalExceptionalPhysicalUpperEndpoint b hi) := by
  let A :=
    roughCanonicalExceptionalPhysicalLowerEndpoint
      n deltaStar b lo
  let B := roughCanonicalExceptionalPhysicalUpperEndpoint b hi
  have hbData := Finset.mem_Icc.mp hb
  have hcutA :
      roughCanonicalRealExceptionalRoughCutoff n deltaStar <= A := by
    exact le_max_right _ _
  have hBHi : B <= hi := by
    dsimp only [B, roughCanonicalExceptionalPhysicalUpperEndpoint]
    exact Nat.div_le_self _ _
  have hBThree : B <= 3 * n := hBHi.trans hhi
  have hBScale : B <= 3 * n / b + 1 := by
    have hdiv : B <= 3 * n / b := by
      dsimp only [B, roughCanonicalExceptionalPhysicalUpperEndpoint]
      exact Nat.div_le_div_right hhi
    omega
  refine
    { core_pos := hbData.1
      core_le_cutoff := hbData.2
      lower_pos := hcommon.exceptional_floor_pos.trans hcutA
      lower_le_upper := by simpa only [A, B] using hAB
      upper_le_paperScale := by simpa only [B] using hBScale
      rough_cutoff_le_lower :=
        hcommon.rough_cutoff_le_exceptional_floor.trans hcutA
      omega_chamber := hBThree.trans_lt hcommon.omega_cap
      padded_log_range := ?_ }
  intro t ht
  apply hcommon.padded_log_range t
  constructor
  · have hcutAR :
        (roughCanonicalRealExceptionalRoughCutoff
          n deltaStar : Real) <= (A : Real) := by
      exact_mod_cast hcutA
    exact hcutAR.trans ht.1
  · have hBThreeR : (B : Real) <= ((3 * n : Nat) : Real) := by
      exact_mod_cast hBThree
    exact ht.2.trans hBThreeR





/-! ## The literal exceptional floor dominates `n^(1-deltaStar)` -/







/-! ## Padded logarithmic coordinates -/





/-! ## Fifth-power chamber and the eventual common certificate -/









end BankPaperRealization

end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankPaperCanonicalSignedExceptionalFourFiveChamberConnector -/
section


/-!
# Four/five chamber connector for the signed exceptional core

This file joins the four pieces which are already formalized separately.

* The ordered four/five estimate is converted to the paper rate on every
  certified exceptional physical interval.
* The continuum kernel is frozen at the literal coordinate
  `log((2n)/b) / log(yNat n)`.
* Natural quotient lengths are compared with the three ideal balanced
  lengths.
* Three frozen deep estimates and three positive cutoff estimates are
  assembled into the signed exceptional-core chamber.

The remaining input is deliberately exposed by
`RoughCanonicalSignedExceptionalFourFiveChamberInputAt`.  It consists of
the three interval estimates after the elementary displacement and clipping
budgets, together with the padded coordinate range for the prime-power
samples of the frozen kernel.  No unproved analytic assertion is hidden in
the connector.
-/

open Filter Topology
open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel
open Erdos390.Full.PrimeBandQuadrature
open Erdos390.Full.Scale

noncomputable section

namespace BankPaperRealization

/-! ## The geometry-facing ordered-to-rough rate -/













/-! ## One-interval freezing and quotient normalization -/

/-- Freeze a geometry-certified physical interval and replace its literal
natural length by an arbitrary ideal length.

The first term is the arithmetic-to-continuum error, the second is the
kernel displacement, and the last is the quotient/clipping endpoint loss.
-/
theorem
    abs_roughCanonicalExceptionalPhysicalInterval_card_sub_idealFrozen_le
    {n b A B : Nat} {deltaStar : Real}
    {arithmeticError Ckernel D u0 idealLength endpointError : Real}
    (hy : 2 <= yNat n)
    (hgeometry :
      RoughCanonicalExceptionalPhysicalIntervalGeometry
        n deltaStar b A B)
    (harithmetic :
      abs (((fourFiveRoughInterval (yNat n) A B).card : Real) -
          fourFiveContinuumMixtureIntegralMain (yNat n) A B) <=
        arithmeticError)
    (hCkernel : 0 <= Ckernel) (hD : 0 <= D)
    (hendpointError : 0 <= endpointError)
    (hu0 :
      u0 ∈ Set.Icc ((41 : Real) / 10) ((47 : Real) / 10))
    (hbound :
      ∀ z ∈ Set.Icc ((41 : Real) / 10) ((47 : Real) / 10),
        abs (fourFiveContinuumMixtureKernel z) <= Ckernel ∧
        abs (fourFiveContinuumMixtureKernelDerivative z) <= Ckernel)
    (hdisplacement :
      ∀ t ∈ Set.Icc (A : Real) (B : Real),
        abs (Real.log t / Real.log (yNat n : Real) - u0) <= D)
    (hlength :
      abs ((((B - A : Nat) : Real)) - idealLength) <= endpointError) :
    abs (((fourFiveRoughInterval (yNat n) A B).card : Real) -
        (fourFiveContinuumMixtureKernel u0 /
          Real.log (yNat n : Real)) * idealLength) <=
      arithmeticError +
        (((((B - A : Nat) : Real)) /
          Real.log (yNat n : Real)) * Ckernel) * D +
        (Ckernel / Real.log (yNat n : Real)) * endpointError := by
  have hAB := hgeometry.lower_le_upper
  have hlog : 0 < Real.log (yNat n : Real) :=
    Real.log_pos (by exact_mod_cast (show 1 < yNat n by omega))
  have hintegrable :=
    intervalIntegrable_fourFiveContinuumMixtureKernel_of_paperRange
      hy hgeometry.rough_cutoff_le_lower hAB
      hgeometry.padded_log_range
  have hfreeze0 :=
    abs_fourFiveContinuumMixtureIntegralMain_sub_frozen_le
      hAB hlog hCkernel hD hu0 hgeometry.padded_log_range
      hdisplacement (fun z hz => (hbound z hz).2) hintegrable
  have hfreeze :
      abs (fourFiveContinuumMixtureIntegralMain (yNat n) A B -
        (fourFiveContinuumMixtureKernel u0 /
          Real.log (yNat n : Real)) * ((B - A : Nat) : Real)) <=
        (((((B - A : Nat) : Real)) /
          Real.log (yNat n : Real)) * Ckernel) * D := by
    rw [show
      (fourFiveContinuumMixtureKernel u0 /
          Real.log (yNat n : Real)) * ((B - A : Nat) : Real) =
        (((B : Real) - (A : Real)) /
          Real.log (yNat n : Real)) *
            fourFiveContinuumMixtureKernel u0 by
      rw [Nat.cast_sub hAB]
      ring]
    simpa only [Nat.cast_sub hAB] using hfreeze0
  have hkernel :
      abs (fourFiveContinuumMixtureKernel u0 /
        Real.log (yNat n : Real)) <=
          Ckernel / Real.log (yNat n : Real) := by
    rw [abs_div, abs_of_pos hlog]
    exact div_le_div_of_nonneg_right (hbound u0 hu0).1 hlog.le
  exact
    abs_count_sub_idealFrozen_le
      harithmetic hfreeze hlength hkernel
      hendpointError (div_nonneg hCkernel hlog.le)





/-! ## Three-interval certificates -/





/-! ## Replacing the physical upper scale by `n/b` -/





/-! ## Signed deep and cutoff bounds -/















/-! ## Exact remaining chamber input -/





/-! ## Chamber and final residual assembly -/







end BankPaperRealization

end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankPaperCanonicalSignedExceptionalFourFiveDeepDisplacementConnector -/
section


/-!
# Frozen-coordinate displacement on the deep exceptional core

This file isolates the displacement input used when the continuum mixture
kernel is frozen at

`log((2n)/b) / log(yNat n)`.

Natural quotient rounding contributes one unit at each lower endpoint.
On the deep prefix, the existing bound
`tangentPaperExceptionalCutoff <= n / L^2` absorbs that unit.  The upper and
high intervals then have displacement `O(1/L^2)`, while the broad interval
has displacement `O(1/L)`.

Only endpoint arithmetic and previously proved scale bounds occur here.
No interval count and no clipping-length estimate is asserted.
-/

open Filter Topology

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel
open Erdos390.Full.Scale

noncomputable section

namespace BankPaperRealization

/-! ## A normalized logarithmic displacement lemma -/



/-! ## Fixed rate constants -/







theorem roughCanonicalFourFiveDeepUpperDisplacementConstant_nonneg
    {c : Real} (hc : 0 <= c) :
    0 <= roughCanonicalFourFiveDeepUpperDisplacementConstant c := by
  unfold roughCanonicalFourFiveDeepUpperDisplacementConstant
  positivity

theorem roughCanonicalFourFiveDeepHighDisplacementConstant_nonneg
    (K0 : Nat) {c : Real} (hc : 0 <= c) :
    0 <= roughCanonicalFourFiveDeepHighDisplacementConstant K0 c := by
  unfold roughCanonicalFourFiveDeepHighDisplacementConstant
  positivity

theorem roughCanonicalFourFiveDeepBroadDisplacementConstant_pos :
    0 < roughCanonicalFourFiveDeepBroadDisplacementConstant := by
  unfold roughCanonicalFourFiveDeepBroadDisplacementConstant
  norm_num

/-! ## Elementary deep-prefix scale reductions -/







/-! ## Finite displacement bounds in adapter form -/







/-! ## Simultaneous adapter-facing packaging -/











/-! ## Eventual simultaneous form -/





end BankPaperRealization

end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankPaperCanonicalSignedExceptionalFourFiveDeepIntervalEstimateConnector -/
section


/-!
# Deep exceptional four/five interval estimates

This connector assembles the three inputs already isolated for a deep
smooth core:

* the uniform arithmetic `Z / L^3` estimate;
* freezing at the literal coordinate, using the uniform compact `C¹`
  kernel bound and the deep displacement package;
* the literal endpoint-length errors.

The upper and high intervals use their eventual no-clipping conclusions.
The broad interval continues to use its clipped lower endpoint.  If that
clipping passes the broad upper endpoint, the literal interval is empty and
the same endpoint budget controls the removed frozen main term.
-/

open Filter Topology

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel
open Erdos390.Full.Scale

noncomputable section

namespace BankPaperRealization

/-! ## Algebraic rate absorption -/



/-- The broad freezing and clipped-endpoint terms are absorbed at the
`Z/L^2+1` rate. -/
theorem roughCanonicalFourFiveDeep_broadFreezingEndpointRate_le
    {Z ell logY literal C D : Real}
    (hZ : 0 <= Z) (hLone : 1 <= ell)
    (hlogLower : (1 / 5 : Real) * ell <= logY)
    (hC : 0 <= C) (hD : 0 <= D)
    (hliteral : literal <= 3 * Z + 2)
    (hliteralNonneg : 0 <= literal) :
    (((literal / logY) * C) * (D / ell) +
        (C / logY) * (2 * (Z / ell + 1))) <=
      (25 * C * D + 10 * C) *
        (Z / ell ^ 2 + 1) := by
  have hL : 0 < ell := zero_lt_one.trans_le hLone
  have hlog : 0 < logY :=
    (mul_pos (by norm_num) hL).trans_le hlogLower
  have hinvLog : 1 / logY <= 5 / ell := by
    apply (div_le_div_iff₀ hlog hL).2
    nlinarith [hlogLower]
  have hfiveL : 0 <= 5 / ell := div_nonneg (by norm_num) hL.le
  have hscaledCD :
      0 <= C * (D / ell) :=
    mul_nonneg hC (div_nonneg hD hL.le)
  have hInvSq : 1 / ell ^ 2 <= 1 :=
    (div_le_one (sq_pos_of_pos hL)).2
      (one_le_pow₀ (n := 2) hLone)
  have hInvL : 1 / ell <= 1 :=
    (div_le_one hL).2 hLone
  have hq : 0 <= Z / ell ^ 2 :=
    div_nonneg hZ (sq_nonneg ell)
  have hqOne : 1 <= Z / ell ^ 2 + 1 := by linarith
  have hcoeffMain : 0 <= 15 * C * D := by positivity
  have hcoeffUnit : 0 <= 10 * C * D := by positivity
  have hfreeze :
      ((literal / logY) * C) * (D / ell) <=
        (25 * C * D) * (Z / ell ^ 2 + 1) := by
    calc
      ((literal / logY) * C) * (D / ell) =
          (literal * (C * (D / ell))) * (1 / logY) := by ring
      _ <=
          (literal * (C * (D / ell))) * (5 / ell) :=
        mul_le_mul_of_nonneg_left hinvLog
          (mul_nonneg hliteralNonneg hscaledCD)
      _ <=
          ((3 * Z + 2) * (C * (D / ell))) * (5 / ell) := by
        exact
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hliteral hscaledCD)
            hfiveL
      _ =
          (15 * C * D) * (Z / ell ^ 2) +
            (10 * C * D) * (1 / ell ^ 2) := by ring
      _ <=
          (15 * C * D) * (Z / ell ^ 2) +
            (10 * C * D) * 1 :=
        add_le_add le_rfl
          (mul_le_mul_of_nonneg_left hInvSq hcoeffUnit)
      _ <=
          ((15 * C * D) + (10 * C * D)) *
            (Z / ell ^ 2 + 1) := by
        calc
          (15 * C * D) * (Z / ell ^ 2) +
              (10 * C * D) * 1 <=
              ((15 * C * D) * (Z / ell ^ 2) +
                (10 * C * D) * 1) +
                ((15 * C * D) +
                  (10 * C * D) * (Z / ell ^ 2)) :=
            le_add_of_nonneg_right
              (add_nonneg hcoeffMain (mul_nonneg hcoeffUnit hq))
          _ =
              ((15 * C * D) + (10 * C * D)) *
                (Z / ell ^ 2 + 1) := by ring
      _ = (25 * C * D) * (Z / ell ^ 2 + 1) := by ring
  have hendpoint :
      (C / logY) * (2 * (Z / ell + 1)) <=
        (10 * C) * (Z / ell ^ 2 + 1) := by
    have hmult :
        0 <= C * (2 * (Z / ell + 1)) := by positivity
    calc
      (C / logY) * (2 * (Z / ell + 1)) =
          (C * (2 * (Z / ell + 1))) * (1 / logY) := by ring
      _ <=
          (C * (2 * (Z / ell + 1))) * (5 / ell) :=
        mul_le_mul_of_nonneg_left hinvLog hmult
      _ =
          (10 * C) * (Z / ell ^ 2 + 1 / ell) := by ring
      _ <=
          (10 * C) * (Z / ell ^ 2 + 1) :=
        mul_le_mul_of_nonneg_left
          (by linarith [hInvL]) (mul_nonneg (by norm_num) hC)
  exact
    (add_le_add hfreeze hendpoint).trans_eq (by ring)

/-! ## Generic one-interval assemblers -/









/-- Generic upper/high assembler.  It is deliberately phrased for one
geometry-certified interval; the only interval-specific inputs are the
displacement numerator, the ideal-length scale, and the endpoint theorem. -/
theorem
    abs_roughCanonicalExceptionalPhysicalInterval_card_sub_idealFrozen_le_deepShortRate
    {n b A B : Nat} {deltaStar : Real}
    {P C D a u0 idealLength : Real}
    (hy : 2 <= yNat n)
    (hgeometry :
      RoughCanonicalExceptionalPhysicalIntervalGeometry
        n deltaStar b A B)
    (hP : 0 <= P) (hC : 0 <= C) (hD : 0 <= D) (ha : 0 <= a)
    (hLone : 1 <= L n)
    (hlogLower :
      (1 / 5 : Real) * L n <= Real.log (yNat n : Real))
    (hu0 :
      u0 ∈ Set.Icc ((41 : Real) / 10) ((47 : Real) / 10))
    (hbound :
      ∀ z ∈ Set.Icc ((41 : Real) / 10) ((47 : Real) / 10),
        abs (fourFiveContinuumMixtureKernel z) <= C ∧
        abs (fourFiveContinuumMixtureKernelDerivative z) <= C)
    (harithmetic :
      abs (((fourFiveRoughInterval (yNat n) A B).card : Real) -
          fourFiveContinuumMixtureIntegralMain (yNat n) A B) <=
        P * (roughCanonicalExceptionalPhysicalRateScale n b / L n ^ 3))
    (hdisplacement :
      ∀ t ∈ Set.Icc (A : Real) (B : Real),
        abs (Real.log t / Real.log (yNat n : Real) - u0) <=
          D / L n ^ 2)
    (hlength :
      abs ((((B - A : Nat) : Real)) - idealLength) <= 1)
    (hidealRate :
      idealLength <=
        2 * a * roughCanonicalExceptionalPhysicalRateScale n b / L n) :
    abs (((fourFiveRoughInterval (yNat n) A B).card : Real) -
        (fourFiveContinuumMixtureKernel u0 /
          Real.log (yNat n : Real)) * idealLength) <=
      roughCanonicalFourFiveDeepShortEstimateConstant P C D a *
        (roughCanonicalExceptionalPhysicalRateScale n b / L n ^ 3 + 1) := by
  have hL : 0 < L n := zero_lt_one.trans_le hLone
  have hZ :
      0 <= roughCanonicalExceptionalPhysicalRateScale n b := by
    unfold roughCanonicalExceptionalPhysicalRateScale
    positivity
  have hliteral :
      (((B - A : Nat) : Real)) <=
        2 * a * roughCanonicalExceptionalPhysicalRateScale n b / L n + 1 := by
    have hdiff :
        (((B - A : Nat) : Real)) - idealLength <= 1 :=
      (le_abs_self _).trans hlength
    linarith
  have hraw :=
    abs_roughCanonicalExceptionalPhysicalInterval_card_sub_idealFrozen_le
      (arithmeticError :=
        P * (roughCanonicalExceptionalPhysicalRateScale n b / L n ^ 3))
      (Ckernel := C) (D := D / L n ^ 2)
      (u0 := u0) (idealLength := idealLength) (endpointError := 1)
      hy hgeometry harithmetic hC
      (div_nonneg hD (sq_nonneg (L n))) (by norm_num)
      hu0 hbound hdisplacement hlength
  have hfreezeEndpoint :=
    roughCanonicalFourFiveDeep_shortFreezingEndpointRate_le
      hZ hLone hlogLower hC hD ha hliteral (Nat.cast_nonneg _)
  have hq :
      0 <= roughCanonicalExceptionalPhysicalRateScale n b / L n ^ 3 :=
    div_nonneg hZ (pow_nonneg hL.le 3)
  calc
    abs (((fourFiveRoughInterval (yNat n) A B).card : Real) -
        (fourFiveContinuumMixtureKernel u0 /
          Real.log (yNat n : Real)) * idealLength) <=
      P * (roughCanonicalExceptionalPhysicalRateScale n b / L n ^ 3) +
        (((((B - A : Nat) : Real)) /
            Real.log (yNat n : Real)) * C) * (D / L n ^ 2) +
          (C / Real.log (yNat n : Real)) * 1 := hraw
    _ <=
        P *
            (roughCanonicalExceptionalPhysicalRateScale n b / L n ^ 3 + 1) +
          (5 * C * D * (2 * a + 1) + 5 * C) *
            (roughCanonicalExceptionalPhysicalRateScale n b / L n ^ 3 + 1) :=
      by
        simpa only [add_assoc] using
          (add_le_add
            (mul_le_mul_of_nonneg_left
              (le_add_of_nonneg_right (by norm_num)) hP)
            hfreezeEndpoint)
    _ =
        roughCanonicalFourFiveDeepShortEstimateConstant P C D a *
          (roughCanonicalExceptionalPhysicalRateScale n b / L n ^ 3 + 1) := by
      unfold roughCanonicalFourFiveDeepShortEstimateConstant
      ring

/-- Generic broad assembler.  The lower endpoint remains clipped, and its
complete endpoint budget is used both to bound the literal span and in the
freezing adapter. -/
theorem
    abs_roughCanonicalExceptionalPhysicalInterval_card_sub_idealFrozen_le_deepBroadRate
    {n b A B : Nat} {deltaStar : Real}
    {P C D u0 idealLength : Real}
    (hy : 2 <= yNat n)
    (hgeometry :
      RoughCanonicalExceptionalPhysicalIntervalGeometry
        n deltaStar b A B)
    (hP : 0 <= P) (hC : 0 <= C) (hD : 0 <= D)
    (hLone : 1 <= L n)
    (hlogLower :
      (1 / 5 : Real) * L n <= Real.log (yNat n : Real))
    (hu0 :
      u0 ∈ Set.Icc ((41 : Real) / 10) ((47 : Real) / 10))
    (hbound :
      ∀ z ∈ Set.Icc ((41 : Real) / 10) ((47 : Real) / 10),
        abs (fourFiveContinuumMixtureKernel z) <= C ∧
        abs (fourFiveContinuumMixtureKernelDerivative z) <= C)
    (harithmetic :
      abs (((fourFiveRoughInterval (yNat n) A B).card : Real) -
          fourFiveContinuumMixtureIntegralMain (yNat n) A B) <=
        P * (roughCanonicalExceptionalPhysicalRateScale n b / L n ^ 3))
    (hdisplacement :
      ∀ t ∈ Set.Icc (A : Real) (B : Real),
        abs (Real.log t / Real.log (yNat n : Real) - u0) <=
          D / L n)
    (hlength :
      abs ((((B - A : Nat) : Real)) - idealLength) <=
        2 *
          (roughCanonicalExceptionalPhysicalRateScale n b / L n + 1))
    (hidealRate :
      idealLength <= roughCanonicalExceptionalPhysicalRateScale n b) :
    abs (((fourFiveRoughInterval (yNat n) A B).card : Real) -
        (fourFiveContinuumMixtureKernel u0 /
          Real.log (yNat n : Real)) * idealLength) <=
      roughCanonicalFourFiveDeepBroadEstimateConstant P C D *
        (roughCanonicalExceptionalPhysicalRateScale n b / L n ^ 2 + 1) := by
  have hL : 0 < L n := zero_lt_one.trans_le hLone
  have hZ :
      0 <= roughCanonicalExceptionalPhysicalRateScale n b := by
    unfold roughCanonicalExceptionalPhysicalRateScale
    positivity
  have hZdiv :
      roughCanonicalExceptionalPhysicalRateScale n b / L n <=
        roughCanonicalExceptionalPhysicalRateScale n b := by
    exact div_le_self hZ hLone
  have hliteral :
      (((B - A : Nat) : Real)) <=
        3 * roughCanonicalExceptionalPhysicalRateScale n b + 2 := by
    have hdiff :
        (((B - A : Nat) : Real)) - idealLength <=
          2 *
            (roughCanonicalExceptionalPhysicalRateScale n b / L n + 1) :=
      (le_abs_self _).trans hlength
    nlinarith
  have hraw :=
    abs_roughCanonicalExceptionalPhysicalInterval_card_sub_idealFrozen_le
      (arithmeticError :=
        P * (roughCanonicalExceptionalPhysicalRateScale n b / L n ^ 3))
      (Ckernel := C) (D := D / L n)
      (u0 := u0) (idealLength := idealLength)
      (endpointError :=
        2 *
          (roughCanonicalExceptionalPhysicalRateScale n b / L n + 1))
      hy hgeometry harithmetic hC (div_nonneg hD hL.le)
      (by positivity) hu0 hbound hdisplacement hlength
  have hfreezeEndpoint :=
    roughCanonicalFourFiveDeep_broadFreezingEndpointRate_le
      hZ hLone hlogLower hC hD hliteral (Nat.cast_nonneg _)
  have hLsqLeCube : L n ^ 2 <= L n ^ 3 := by
    calc
      L n ^ 2 = L n ^ 2 * 1 := by ring
      _ <= L n ^ 2 * L n :=
        mul_le_mul_of_nonneg_left hLone (sq_nonneg (L n))
      _ = L n ^ 3 := by ring
  have hq :
      roughCanonicalExceptionalPhysicalRateScale n b / L n ^ 3 <=
        roughCanonicalExceptionalPhysicalRateScale n b / L n ^ 2 :=
    div_le_div_of_nonneg_left hZ (sq_pos_of_pos hL) hLsqLeCube
  calc
    abs (((fourFiveRoughInterval (yNat n) A B).card : Real) -
        (fourFiveContinuumMixtureKernel u0 /
          Real.log (yNat n : Real)) * idealLength) <=
      P * (roughCanonicalExceptionalPhysicalRateScale n b / L n ^ 3) +
        (((((B - A : Nat) : Real)) /
            Real.log (yNat n : Real)) * C) * (D / L n) +
          (C / Real.log (yNat n : Real)) *
            (2 *
              (roughCanonicalExceptionalPhysicalRateScale n b / L n + 1)) :=
      hraw
    _ <=
        P *
            (roughCanonicalExceptionalPhysicalRateScale n b / L n ^ 2 + 1) +
          (25 * C * D + 10 * C) *
            (roughCanonicalExceptionalPhysicalRateScale n b / L n ^ 2 + 1) :=
      by
        simpa only [add_assoc] using
          (add_le_add
            (mul_le_mul_of_nonneg_left
              (hq.trans (le_add_of_nonneg_right (by norm_num))) hP)
            hfreezeEndpoint)
    _ =
        roughCanonicalFourFiveDeepBroadEstimateConstant P C D *
          (roughCanonicalExceptionalPhysicalRateScale n b / L n ^ 2 + 1) := by
      unfold roughCanonicalFourFiveDeepBroadEstimateConstant
      ring

/-- The real core quotient is bounded by the physical paper-rate scale. -/
theorem roughCanonicalFourFiveDeep_self_div_core_le_rateScale
    {n b : Nat} (hb : 0 < b) :
    (n : Real) / (b : Real) <=
      roughCanonicalExceptionalPhysicalRateScale n b := by
  have hround :
      (n : Real) / (b : Real) <
        ((n / b : Nat) : Real) + 1 :=
    roughRealQuotient_lt_natQuotient_add_one
      (N := n) hb
  have hmono : n / b <= (3 * n) / b :=
    Nat.div_le_div_right (by omega)
  have hcast :
      ((n / b : Nat) : Real) + 1 <=
        (((3 * n) / b : Nat) : Real) + 1 := by
    exact add_le_add (by exact_mod_cast hmono) le_rfl
  unfold roughCanonicalExceptionalPhysicalRateScale
  rw [Nat.cast_add, Nat.cast_one]
  exact (hround.trans_le hcast).le

/-- A short ideal length inherits the deep `Z/L` scale from its undivided
physical length. -/
theorem roughCanonicalFourFiveDeep_shortIdealLength_le
    {n b : Nat} {H a : Real}
    (hb : 0 < b) (ha : 0 <= a) (hLone : 1 <= L n)
    (hH : H <= 2 * a * (n : Real) / L n) :
    H / (b : Real) <=
      2 * a * roughCanonicalExceptionalPhysicalRateScale n b / L n := by
  have hbReal : (0 : Real) < (b : Real) := by
    exact_mod_cast hb
  have hL : 0 < L n := zero_lt_one.trans_le hLone
  have hcore :=
    roughCanonicalFourFiveDeep_self_div_core_le_rateScale
      (n := n) hb
  calc
    H / (b : Real) <=
        (2 * a * (n : Real) / L n) / (b : Real) :=
      div_le_div_of_nonneg_right hH hbReal.le
    _ = (2 * a / L n) * ((n : Real) / (b : Real)) := by
      field_simp [hL.ne', hbReal.ne']
    _ <=
        (2 * a / L n) *
          roughCanonicalExceptionalPhysicalRateScale n b :=
      mul_le_mul_of_nonneg_left hcore
        (div_nonneg (mul_nonneg (by norm_num) ha) hL.le)
    _ =
        2 * a * roughCanonicalExceptionalPhysicalRateScale n b / L n := by
      ring

/-- The broad endpoint term alone is absorbed by `10*C*(Z/L^2+1)`.
This is the estimate used when clipping makes the literal broad interval
empty. -/
theorem roughCanonicalFourFiveDeep_broadEndpointRate_le
    {Z ell logY C : Real}
    (hZ : 0 <= Z) (hLone : 1 <= ell)
    (hlogLower : (1 / 5 : Real) * ell <= logY)
    (hC : 0 <= C) :
    (C / logY) * (2 * (Z / ell + 1)) <=
      (10 * C) * (Z / ell ^ 2 + 1) := by
  have hL : 0 < ell := zero_lt_one.trans_le hLone
  have hlog : 0 < logY :=
    (mul_pos (by norm_num) hL).trans_le hlogLower
  have hinvLog : 1 / logY <= 5 / ell := by
    apply (div_le_div_iff₀ hlog hL).2
    nlinarith [hlogLower]
  have hInvL : 1 / ell <= 1 :=
    (div_le_one hL).2 hLone
  have hmult :
      0 <= C * (2 * (Z / ell + 1)) := by positivity
  calc
    (C / logY) * (2 * (Z / ell + 1)) =
        (C * (2 * (Z / ell + 1))) * (1 / logY) := by ring
    _ <= (C * (2 * (Z / ell + 1))) * (5 / ell) :=
      mul_le_mul_of_nonneg_left hinvLog hmult
    _ = (10 * C) * (Z / ell ^ 2 + 1 / ell) := by ring
    _ <= (10 * C) * (Z / ell ^ 2 + 1) :=
      mul_le_mul_of_nonneg_left
        (by linarith [hInvL]) (mul_nonneg (by norm_num) hC)

/-- Empty-interval companion to the generic broad assembler.  The endpoint
error controls the entire ideal frozen main term. -/
theorem
    abs_fourFiveRoughInterval_card_sub_idealFrozen_le_deepBroadRate_of_empty
    {n b A B : Nat} {C u0 idealLength : Real}
    (hBA : B <= A)
    (hC : 0 <= C) (hLone : 1 <= L n)
    (hlogLower :
      (1 / 5 : Real) * L n <= Real.log (yNat n : Real))
    (hu0 :
      u0 ∈ Set.Icc ((41 : Real) / 10) ((47 : Real) / 10))
    (hbound :
      ∀ z ∈ Set.Icc ((41 : Real) / 10) ((47 : Real) / 10),
        abs (fourFiveContinuumMixtureKernel z) <= C ∧
        abs (fourFiveContinuumMixtureKernelDerivative z) <= C)
    (hlength :
      abs ((((B - A : Nat) : Real)) - idealLength) <=
        2 *
          (roughCanonicalExceptionalPhysicalRateScale n b / L n + 1)) :
    abs (((fourFiveRoughInterval (yNat n) A B).card : Real) -
        (fourFiveContinuumMixtureKernel u0 /
          Real.log (yNat n : Real)) * idealLength) <=
      (10 * C) *
        (roughCanonicalExceptionalPhysicalRateScale n b / L n ^ 2 + 1) := by
  have hL : 0 < L n := zero_lt_one.trans_le hLone
  have hlog : 0 < Real.log (yNat n : Real) :=
    (mul_pos (by norm_num) hL).trans_le hlogLower
  have hZ :
      0 <= roughCanonicalExceptionalPhysicalRateScale n b := by
    unfold roughCanonicalExceptionalPhysicalRateScale
    positivity
  have hidealAbs :
      abs idealLength <=
        2 *
          (roughCanonicalExceptionalPhysicalRateScale n b / L n + 1) := by
    simpa only [Nat.sub_eq_zero_of_le hBA, Nat.cast_zero, zero_sub,
      abs_neg] using hlength
  have hkernel :
      abs (fourFiveContinuumMixtureKernel u0 /
          Real.log (yNat n : Real)) <=
        C / Real.log (yNat n : Real) := by
    rw [abs_div, abs_of_pos hlog]
    exact div_le_div_of_nonneg_right (hbound u0 hu0).1 hlog.le
  have hmain :
      abs ((fourFiveContinuumMixtureKernel u0 /
          Real.log (yNat n : Real)) * idealLength) <=
        (C / Real.log (yNat n : Real)) *
          (2 *
            (roughCanonicalExceptionalPhysicalRateScale n b / L n + 1)) := by
    rw [abs_mul]
    exact mul_le_mul hkernel hidealAbs (abs_nonneg _)
      (div_nonneg hC hlog.le)
  rw [fourFiveRoughInterval_eq_empty_of_upper_le_lower hBA]
  simp only [Finset.card_empty, Nat.cast_zero, zero_sub, abs_neg]
  exact hmain.trans
    (roughCanonicalFourFiveDeep_broadEndpointRate_le
      hZ hLone hlogLower hC)

/-! ## The three fixed deep constants -/













/-! ## Finite three-interval assembly -/

/-- Assemble all three frozen deep estimates from the uniform arithmetic
bound, common geometry, displacement package, and endpoint package.  The
broad proof splits on the literal clipped endpoint order; no broad
no-clipping premise occurs. -/
theorem roughCanonicalSignedExceptionalDeepIntervalEstimate_of_inputs
    {K0 n b : Nat} {c deltaStar P C : Real}
    (hy : 2 <= yNat n)
    (hc : 0 <= c) (hP : 0 <= P) (hC : 0 <= C)
    (hLone : 1 <= L n)
    (hlogLower :
      (1 / 5 : Real) * L n <= Real.log (yNat n : Real))
    (htail :
      (upperTailLength c n : Real) <=
        2 * c * (n : Real) / L n)
    (htailNat : upperTailLength c n <= n)
    (hcommon :
      RoughCanonicalExceptionalCommonEndpointGeometry n deltaStar)
    (hu0 :
      roughCanonicalFourFiveFrozenCoordinate n b ∈
        Set.Icc ((41 : Real) / 10) ((47 : Real) / 10))
    (hb : b ∈ roughCanonicalExceptionalDeepCoreSet deltaStar n)
    (hbound :
      ∀ z ∈ Set.Icc ((41 : Real) / 10) ((47 : Real) / 10),
        abs (fourFiveContinuumMixtureKernel z) <= C ∧
        abs (fourFiveContinuumMixtureKernelDerivative z) <= C)
    (harithmetic :
      ∀ A B : Nat,
        RoughCanonicalExceptionalPhysicalIntervalGeometry
            n deltaStar b A B ->
          abs (((fourFiveRoughInterval (yNat n) A B).card : Real) -
              fourFiveContinuumMixtureIntegralMain (yNat n) A B) <=
            P *
              (roughCanonicalExceptionalPhysicalRateScale n b / L n ^ 3))
    (hdisplacement :
      RoughCanonicalFourFiveDeepFrozenDisplacementBoundsAt
        K0 n b c deltaStar)
    (hendpoint :
      RoughCanonicalFourFiveDeepEndpointLengthErrorsAt
        K0 n b c deltaStar) :
    RoughCanonicalSignedExceptionalDeepIntervalEstimate
      K0 n b c deltaStar
      (roughCanonicalFourFiveDeepUpperEstimateConstant P C c)
      (roughCanonicalFourFiveDeepHighEstimateConstant K0 P C c)
      (roughCanonicalFourFiveDeepBroadFinalEstimateConstant P C) := by
  have hbDeep :
      b ∈ Finset.Icc 1
        (tangentPaperExceptionalCutoff deltaStar n / 2) := by
    simpa only [roughCanonicalExceptionalDeepCoreSet] using hb
  have hbData := Finset.mem_Icc.mp hbDeep
  have hbPos : 0 < b := by omega
  have hbReal : (0 : Real) < (b : Real) := by
    exact_mod_cast hbPos
  have hbPrefix :
      b ∈ Finset.Icc 1
        (2 * tangentPaperExceptionalCutoff deltaStar n) := by
    exact Finset.mem_Icc.mpr ⟨hbData.1, by omega⟩
  have hZ :
      0 <= roughCanonicalExceptionalPhysicalRateScale n b := by
    unfold roughCanonicalExceptionalPhysicalRateScale
    positivity
  have hL : 0 < L n := zero_lt_one.trans_le hLone
  have hcore :=
    roughCanonicalFourFiveDeep_self_div_core_le_rateScale
      (n := n) hbPos
  refine ⟨?_, ?_, ?_⟩
  · let A :=
      roughCanonicalExceptionalPhysicalLowerEndpoint
        n deltaStar b (2 * n)
    let B :=
      roughCanonicalExceptionalPhysicalUpperEndpoint
        b (2 * n + upperTailLength c n)
    have hAB : A <= B := by
      dsimp only [A, B, roughCanonicalExceptionalPhysicalLowerEndpoint,
        roughCanonicalExceptionalPhysicalUpperEndpoint]
      rw [max_eq_left hendpoint.upper_noClipping]
      exact Nat.div_le_div_right (by omega)
    have hgeometry :
        RoughCanonicalExceptionalPhysicalIntervalGeometry
          n deltaStar b A B := by
      simpa only [A, B] using
        (roughCanonicalExceptionalClippedInterval_geometry
          (lo := 2 * n)
          (hi := 2 * n + upperTailLength c n)
          hcommon hbPrefix hAB (by omega))
    have hidealRate :
        (upperTailLength c n : Real) / (b : Real) <=
          2 * c * roughCanonicalExceptionalPhysicalRateScale n b / L n :=
      roughCanonicalFourFiveDeep_shortIdealLength_le
        hbPos hc hLone htail
    have hfinal :=
      abs_roughCanonicalExceptionalPhysicalInterval_card_sub_idealFrozen_le_deepShortRate
        (P := P) (C := C)
        (D := roughCanonicalFourFiveDeepUpperDisplacementConstant c)
        (a := c)
        (u0 := roughCanonicalFourFiveFrozenCoordinate n b)
        (idealLength :=
          (upperTailLength c n : Real) / (b : Real))
        hy hgeometry hP hC
        (roughCanonicalFourFiveDeepUpperDisplacementConstant_nonneg hc)
        hc hLone hlogLower hu0 hbound
        (harithmetic A B hgeometry)
        (by
          simpa only [A, B] using hdisplacement.upper_displacement)
        (by
          simpa only [A, B] using hendpoint.upper_length_error)
        hidealRate
    simpa only [A, B,
      roughCanonicalFourFiveDeepUpperEstimateConstant,
      roughCanonicalExceptionalUpperPhysicalRoughInterval,
      roughCanonicalExceptionalClippedRoughInterval_eq_endpoints] using
        hfinal
  · let A :=
      roughCanonicalExceptionalPhysicalLowerEndpoint n deltaStar b
        (2 * n - (K0 + 1) * upperTailLength c n)
    let B :=
      roughCanonicalExceptionalPhysicalUpperEndpoint b (2 * n)
    have hAB : A <= B := by
      dsimp only [A, B, roughCanonicalExceptionalPhysicalLowerEndpoint,
        roughCanonicalExceptionalPhysicalUpperEndpoint]
      rw [max_eq_left hendpoint.high_noClipping]
      exact Nat.div_le_div_right (Nat.sub_le _ _)
    have hgeometry :
        RoughCanonicalExceptionalPhysicalIntervalGeometry
          n deltaStar b A B := by
      simpa only [A, B] using
        (roughCanonicalExceptionalClippedInterval_geometry
          (lo := 2 * n -
            (K0 + 1) * upperTailLength c n)
          (hi := 2 * n)
          hcommon hbPrefix hAB (by omega))
    have htailDepth :
        (((K0 + 1) * upperTailLength c n : Nat) : Real) <=
          2 * (((K0 + 1 : Nat) : Real) * c) *
            (n : Real) / L n := by
      rw [Nat.cast_mul]
      calc
        ((K0 + 1 : Nat) : Real) *
            (upperTailLength c n : Real) <=
          ((K0 + 1 : Nat) : Real) *
            (2 * c * (n : Real) / L n) :=
          mul_le_mul_of_nonneg_left htail (Nat.cast_nonneg _)
        _ =
            2 * (((K0 + 1 : Nat) : Real) * c) *
              (n : Real) / L n := by ring
    have hidealRate :
        (((K0 + 1) * upperTailLength c n : Nat) : Real) /
            (b : Real) <=
          2 * (((K0 + 1 : Nat) : Real) * c) *
            roughCanonicalExceptionalPhysicalRateScale n b / L n :=
      roughCanonicalFourFiveDeep_shortIdealLength_le
        hbPos (mul_nonneg (Nat.cast_nonneg _) hc) hLone htailDepth
    have hfinal :=
      abs_roughCanonicalExceptionalPhysicalInterval_card_sub_idealFrozen_le_deepShortRate
        (P := P) (C := C)
        (D :=
          roughCanonicalFourFiveDeepHighDisplacementConstant K0 c)
        (a := ((K0 + 1 : Nat) : Real) * c)
        (u0 := roughCanonicalFourFiveFrozenCoordinate n b)
        (idealLength :=
          (((K0 + 1) * upperTailLength c n : Nat) : Real) /
            (b : Real))
        hy hgeometry hP hC
        (roughCanonicalFourFiveDeepHighDisplacementConstant_nonneg K0 hc)
        (mul_nonneg (Nat.cast_nonneg _) hc)
        hLone hlogLower hu0 hbound
        (harithmetic A B hgeometry)
        (by
          simpa only [A, B] using hdisplacement.high_displacement)
        (by
          simpa only [A, B] using hendpoint.high_length_error)
        hidealRate
    simpa only [A, B,
      roughCanonicalFourFiveDeepHighEstimateConstant,
      roughCanonicalExceptionalHighPhysicalRoughInterval,
      roughCanonicalExceptionalClippedRoughInterval_eq_endpoints] using
        hfinal
  · let A :=
      roughCanonicalExceptionalPhysicalLowerEndpoint
        n deltaStar b n
    let B :=
      roughCanonicalExceptionalPhysicalUpperEndpoint b
        (2 * n - (K0 + 1) * upperTailLength c n)
    let idealLength : Real :=
      ((n - (K0 + 1) * upperTailLength c n : Nat) : Real) /
        (b : Real)
    have hidealRate :
        idealLength <= roughCanonicalExceptionalPhysicalRateScale n b := by
      calc
        idealLength <= (n : Real) / (b : Real) := by
          dsimp only [idealLength]
          exact
            div_le_div_of_nonneg_right
              (by
                exact_mod_cast
                  (Nat.sub_le n
                    ((K0 + 1) * upperTailLength c n)))
              hbReal.le
        _ <= roughCanonicalExceptionalPhysicalRateScale n b := hcore
    have hlength :
        abs ((((B - A : Nat) : Real)) - idealLength) <=
          2 *
            (roughCanonicalExceptionalPhysicalRateScale n b / L n + 1) := by
      simpa only [A, B, idealLength] using hendpoint.broad_length_error
    by_cases hAB : A <= B
    · have hgeometry :
          RoughCanonicalExceptionalPhysicalIntervalGeometry
            n deltaStar b A B := by
        simpa only [A, B] using
          (roughCanonicalExceptionalClippedInterval_geometry
            (lo := n)
            (hi := 2 * n -
              (K0 + 1) * upperTailLength c n)
            hcommon hbPrefix hAB (by omega))
      have hfinal :=
        abs_roughCanonicalExceptionalPhysicalInterval_card_sub_idealFrozen_le_deepBroadRate
          (P := P) (C := C)
          (D := roughCanonicalFourFiveDeepBroadDisplacementConstant)
          (u0 := roughCanonicalFourFiveFrozenCoordinate n b)
          (idealLength := idealLength)
          hy hgeometry hP hC
          roughCanonicalFourFiveDeepBroadDisplacementConstant_pos.le
          hLone hlogLower hu0 hbound
          (harithmetic A B hgeometry)
          (by
            simpa only [A, B] using hdisplacement.broad_displacement)
          hlength hidealRate
      simpa only [A, B, idealLength,
        roughCanonicalFourFiveDeepBroadFinalEstimateConstant,
        roughCanonicalExceptionalBroadPhysicalRoughInterval,
        roughCanonicalExceptionalClippedRoughInterval_eq_endpoints] using
          hfinal
    · have hBA : B <= A := by omega
      have hempty :=
        abs_fourFiveRoughInterval_card_sub_idealFrozen_le_deepBroadRate_of_empty
          (n := n) (b := b) (A := A) (B := B)
          (C := C) (u0 := roughCanonicalFourFiveFrozenCoordinate n b)
          (idealLength := idealLength)
          hBA hC hLone hlogLower hu0 hbound hlength
      have hconstant :
          10 * C <=
            roughCanonicalFourFiveDeepBroadFinalEstimateConstant P C := by
        unfold roughCanonicalFourFiveDeepBroadFinalEstimateConstant
          roughCanonicalFourFiveDeepBroadEstimateConstant
        have hCD :
            0 <=
              C * roughCanonicalFourFiveDeepBroadDisplacementConstant :=
          mul_nonneg hC
            roughCanonicalFourFiveDeepBroadDisplacementConstant_pos.le
        nlinarith
      have hscale :
          0 <=
            roughCanonicalExceptionalPhysicalRateScale n b / L n ^ 2 + 1 :=
        add_nonneg (div_nonneg hZ (sq_nonneg (L n))) (by norm_num)
      have hfinal :=
        hempty.trans
          (mul_le_mul_of_nonneg_right hconstant hscale)
      simpa only [A, B, idealLength,
        roughCanonicalExceptionalBroadPhysicalRoughInterval,
        roughCanonicalExceptionalClippedRoughInterval_eq_endpoints] using
          hfinal

/-! ## Eventual three-interval package -/



end BankPaperRealization

end

end Erdos390.WholePaper

end

theorem solution :
∀ {K0 n b : Nat} {c deltaStar P C : Real},
  LE.le.{0} (2 : Nat) (Erdos390.Full.ArithmeticModel.yNat n) →
    LE.le.{0} (0 : Real) c →
      LE.le.{0} (0 : Real) P →
        LE.le.{0} (0 : Real) C →
          LE.le.{0} (1 : Real) (Erdos390.Full.Scale.L n) →
            LE.le.{0} (HMul.hMul.{0, 0, 0} (1 / 5 : Real) (Erdos390.Full.Scale.L n))
                (Real.log ↑(Erdos390.Full.ArithmeticModel.yNat n)) →
              LE.le.{0} (↑(Erdos390.WholePaper.upperTailLength c n))
                  (HDiv.hDiv.{0, 0, 0} (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} (2 : Real) c) ↑n)
                    (Erdos390.Full.Scale.L n)) →
                LE.le.{0} (Erdos390.WholePaper.upperTailLength c n) n →
                  Erdos390.WholePaper.BankPaperRealization.RoughCanonicalExceptionalCommonEndpointGeometry n deltaStar →
                    Membership.mem.{0, 0} (Set.Icc.{0} (41 / 10 : Real) (47 / 10 : Real))
                        (Erdos390.WholePaper.BankPaperRealization.roughCanonicalFourFiveFrozenCoordinate n b) →
                      Membership.mem.{0, 0}
                          (Erdos390.WholePaper.BankPaperRealization.roughCanonicalExceptionalDeepCoreSet deltaStar n)
                          b →
                        (∀ (z : Real),
                            Membership.mem.{0, 0} (Set.Icc.{0} (41 / 10 : Real) (47 / 10 : Real)) z →
                              And
                                (LE.le.{0}
                                  (abs.{0} (Erdos390.WholePaper.BankPaperRealization.fourFiveContinuumMixtureKernel z))
                                  C)
                                (LE.le.{0}
                                  (abs.{0}
                                    (Erdos390.WholePaper.BankPaperRealization.fourFiveContinuumMixtureKernelDerivative
                                      z))
                                  C)) →
                          (∀ (A B : Nat),
                              Erdos390.WholePaper.BankPaperRealization.RoughCanonicalExceptionalPhysicalIntervalGeometry
                                  n deltaStar b A B →
                                LE.le.{0}
                                  (abs.{0}
                                    (HSub.hSub.{0, 0, 0}
                                      (↑(Finset.card.{0}
                                          (Erdos390.WholePaper.BankPaperRealization.fourFiveRoughInterval
                                            (Erdos390.Full.ArithmeticModel.yNat n) A B)))
                                      (Erdos390.WholePaper.BankPaperRealization.fourFiveContinuumMixtureIntegralMain
                                        (Erdos390.Full.ArithmeticModel.yNat n) A B)))
                                  (HMul.hMul.{0, 0, 0} P
                                    (HDiv.hDiv.{0, 0, 0}
                                      (Erdos390.WholePaper.BankPaperRealization.roughCanonicalExceptionalPhysicalRateScale
                                        n b)
                                      (HPow.hPow.{0, 0, 0} (Erdos390.Full.Scale.L n) (3 : Nat))))) →
                            Erdos390.WholePaper.BankPaperRealization.RoughCanonicalFourFiveDeepFrozenDisplacementBoundsAt
                                K0 n b c deltaStar →
                              Erdos390.WholePaper.BankPaperRealization.RoughCanonicalFourFiveDeepEndpointLengthErrorsAt
                                  K0 n b c deltaStar →
                                Erdos390.WholePaper.BankPaperRealization.RoughCanonicalSignedExceptionalDeepIntervalEstimate
                                  K0 n b c deltaStar
                                  (Erdos390.WholePaper.BankPaperRealization.roughCanonicalFourFiveDeepUpperEstimateConstant
                                    P C c)
                                  (Erdos390.WholePaper.BankPaperRealization.roughCanonicalFourFiveDeepHighEstimateConstant
                                    K0 P C c)
                                  (Erdos390.WholePaper.BankPaperRealization.roughCanonicalFourFiveDeepBroadFinalEstimateConstant
                                    P C) := by
  exact @Erdos390.WholePaper.BankPaperRealization.roughCanonicalSignedExceptionalDeepIntervalEstimate_of_inputs
