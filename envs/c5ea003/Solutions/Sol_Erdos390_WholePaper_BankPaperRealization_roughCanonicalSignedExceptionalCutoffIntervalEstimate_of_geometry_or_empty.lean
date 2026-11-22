-- Prove2me | solution 1 for Erdos390.WholePaper.BankPaperRealization.roughCanonicalSignedExceptionalCutoffIntervalEstimate_of_geometry_or_empty
-- status  : ACCEPTED   (prove)
-- author  : @doctosil
-- created : 2026-09-17T16:00:18.701109+00:00
-- url     : https://prove2.me/submissions/b113505c-42be-429f-9a23-806bbc3f2823

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

/- Source module: Erdos390.WholePaper.FixedModulusReducedResidueCount -/
section


/-!
# Fixed-modulus reduced-residue counts

This file proves the elementary `O_W(1)` input used in the rough selector
and in the tangent-list census.  A reduced-residue predicate is counted on
literal finite intervals by splitting the interval into complete periods
and one remainder.  Multiples of a number coprime to the fixed modulus are
then reindexed exactly by division.

There is no prime-number theorem, smooth-number estimate, or asymptotic
hypothesis in this module.  The final CRT-style error constant is the
explicit number `M + 1`, independent of the multiplier and the interval.
-/

namespace Erdos390.WholePaper

noncomputable section









/-! ## Exact periodic decomposition -/

















/-! ## Explicit fixed-period error -/







/-! ## Exact CRT reindexing and multiplier-independent error -/



/-- Integer quotient lengths differ from real division by less than one.
This is the only extra endpoint cost after the exact multiplication
reindexing. -/
theorem quotientIocLength_sub_realLengthDiv_abs_lt_one
    {D lo hi : ℕ} (hD : 0 < D) (hlohi : lo ≤ hi) :
    |(((hi / D - lo / D : ℕ) : ℝ)) -
        ((hi - lo : ℕ) : ℝ) / (D : ℝ)| < 1 := by
  have hquotient : lo / D ≤ hi / D := Nat.div_le_div_right hlohi
  have hDRealPos : (0 : ℝ) < (D : ℝ) := by
    exact_mod_cast hD
  have hDReal : (D : ℝ) ≠ 0 := hDRealPos.ne'
  have hhi := congrArg (fun z : ℕ ↦ (z : ℝ)) (Nat.mod_add_div hi D)
  have hlo := congrArg (fun z : ℕ ↦ (z : ℝ)) (Nat.mod_add_div lo D)
  simp only [Nat.cast_add, Nat.cast_mul] at hhi hlo
  have herror :
      (((hi / D - lo / D : ℕ) : ℝ)) -
          ((hi - lo : ℕ) : ℝ) / (D : ℝ) =
        ((lo % D : ℕ) : ℝ) / (D : ℝ) -
          ((hi % D : ℕ) : ℝ) / (D : ℝ) := by
    rw [Nat.cast_sub hquotient, Nat.cast_sub hlohi]
    field_simp [hDReal]
    nlinarith [hhi, hlo]
  have hloMod : ((lo % D : ℕ) : ℝ) / (D : ℝ) < 1 := by
    apply (div_lt_one hDRealPos).2
    exact_mod_cast Nat.mod_lt lo hD
  have hhiMod : ((hi % D : ℕ) : ℝ) / (D : ℝ) < 1 := by
    apply (div_lt_one hDRealPos).2
    exact_mod_cast Nat.mod_lt hi hD
  have hloModNonneg :
      0 ≤ ((lo % D : ℕ) : ℝ) / (D : ℝ) :=
    div_nonneg (Nat.cast_nonneg _) hDRealPos.le
  have hhiModNonneg :
      0 ≤ ((hi % D : ℕ) : ℝ) / (D : ℝ) :=
    div_nonneg (Nat.cast_nonneg _) hDRealPos.le
  rw [herror, abs_lt]
  constructor <;> linarith



/-! ## Paper-head specializations -/









end

end Erdos390.WholePaper

end

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

/-- The length of a quotient interval is bounded by its real length plus
one. -/
theorem roughQuotientGap_cast_le
    {A B r : ℕ} (hr : 0 < r) (hAB : A ≤ B) :
    (((B / r - A / r : ℕ) : ℝ)) ≤
      (((B - A : ℕ) : ℝ)) / (r : ℝ) + 1 := by
  have hfloor :=
    quotientIocLength_sub_realLengthDiv_abs_lt_one hr hAB
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







/-! ## A common certificate gives every nonempty clipped interval -/







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

/- Source module: Erdos390.WholePaper.BankPaperCanonicalSignedExceptionalFourFiveCutoffIntervalPrecursorConnector -/
section


/-!
# Positive cutoff-interval precursor for the signed four/five chamber

The cutoff band does not need a frozen main term.  On every nonempty
geometry-certified interval we freeze at the fixed padded endpoint `4.1`,
choose ideal length zero, and charge the literal interval span as endpoint
error.  The choices

`u0 = 41/10`, `D = 3/5`, `idealLength = 0`

therefore turn the existing freezing adapter into a positive cardinality
bound.  Empty intervals contribute zero.

This file also proves the generic clipped-span estimate and scales the upper
and high spans to `Z/L^2`, and the broad span to `Z/L`.
-/

open Filter Topology

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel
open Erdos390.Full.Scale

noncomputable section

namespace BankPaperRealization

/-! ## Generic clipped spans -/

/-- Clipping the lower quotient endpoint can only shorten an interval.
Consequently its natural span is bounded by the ideal physical length
divided by the core, plus the single quotient-rounding unit. -/
theorem roughCanonicalExceptional_clippedPhysicalEndpoint_span_le
    {n b lo hi : Nat} {deltaStar : Real}
    (hb : 0 < b) (hlohi : lo <= hi) :
    ((roughCanonicalExceptionalPhysicalUpperEndpoint b hi -
        roughCanonicalExceptionalPhysicalLowerEndpoint
          n deltaStar b lo : Nat) : Real) <=
      ((hi - lo : Nat) : Real) / (b : Real) + 1 := by
  have hlower :
      lo / b <=
        roughCanonicalExceptionalPhysicalLowerEndpoint
          n deltaStar b lo := by
    unfold roughCanonicalExceptionalPhysicalLowerEndpoint
    exact le_max_left _ _
  have hspanNat :
      roughCanonicalExceptionalPhysicalUpperEndpoint b hi -
          roughCanonicalExceptionalPhysicalLowerEndpoint
            n deltaStar b lo <=
        hi / b - lo / b := by
    unfold roughCanonicalExceptionalPhysicalUpperEndpoint
    omega
  calc
    ((roughCanonicalExceptionalPhysicalUpperEndpoint b hi -
        roughCanonicalExceptionalPhysicalLowerEndpoint
          n deltaStar b lo : Nat) : Real) <=
        ((hi / b - lo / b : Nat) : Real) := by
      exact_mod_cast hspanNat
    _ <= ((hi - lo : Nat) : Real) / (b : Real) + 1 :=
      roughQuotientGap_cast_le hb hlohi

/-- The real core quotient is dominated by the paper-rate scale
`3*n/b+1`, including all natural quotient rounding. -/
theorem roughCanonicalExceptional_self_div_core_le_physicalRateScale
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

/-! ## Freezing at the fixed padded endpoint -/

/-- A geometry-certified interval can be frozen at `4.1` with zero ideal
length.  The literal span pays its own endpoint error, while the padded
coordinate range gives displacement at most `0.6`. -/
theorem
    fourFiveRoughInterval_card_le_arithmetic_add_fixedEndpointFreezing
    {n b A B : Nat} {deltaStar arithmeticError Ckernel : Real}
    (hy : 2 <= yNat n)
    (hgeometry :
      RoughCanonicalExceptionalPhysicalIntervalGeometry
        n deltaStar b A B)
    (harithmetic :
      abs (((fourFiveRoughInterval (yNat n) A B).card : Real) -
          fourFiveContinuumMixtureIntegralMain (yNat n) A B) <=
        arithmeticError)
    (hCkernel : 0 <= Ckernel)
    (hbound :
      ∀ z ∈ Set.Icc ((41 : Real) / 10) ((47 : Real) / 10),
        abs (fourFiveContinuumMixtureKernel z) <= Ckernel ∧
        abs (fourFiveContinuumMixtureKernelDerivative z) <= Ckernel) :
    ((fourFiveRoughInterval (yNat n) A B).card : Real) <=
      arithmeticError +
        (8 / 5 : Real) * Ckernel *
          (((B - A : Nat) : Real) /
            Real.log (yNat n : Real)) := by
  have hspanNonneg :
      0 <= ((B - A : Nat) : Real) := Nat.cast_nonneg _
  have hu0 :
      ((41 : Real) / 10) ∈
        Set.Icc ((41 : Real) / 10) ((47 : Real) / 10) := by
    norm_num
  have hdisplacement :
      ∀ t ∈ Set.Icc (A : Real) (B : Real),
        abs (Real.log t / Real.log (yNat n : Real) -
          (41 : Real) / 10) <= (3 : Real) / 5 := by
    intro t ht
    have hz := hgeometry.padded_log_range t ht
    rw [abs_of_nonneg (sub_nonneg.mpr hz.1)]
    linarith [hz.2]
  have hlength :
      abs (((B - A : Nat) : Real) - 0) <=
        ((B - A : Nat) : Real) := by
    have habs :
        abs (((B - A : Nat) : Real) - 0) =
          ((B - A : Nat) : Real) := by
      rw [sub_zero, abs_of_nonneg hspanNonneg]
    exact habs.le
  have hadapter :=
    abs_roughCanonicalExceptionalPhysicalInterval_card_sub_idealFrozen_le
      (arithmeticError := arithmeticError)
      (Ckernel := Ckernel) (D := (3 : Real) / 5)
      (u0 := (41 : Real) / 10) (idealLength := 0)
      (endpointError := ((B - A : Nat) : Real))
      hy hgeometry harithmetic hCkernel (by norm_num)
      hspanNonneg hu0 hbound hdisplacement hlength
  have hcardNonneg :
      0 <= ((fourFiveRoughInterval (yNat n) A B).card : Real) :=
    Nat.cast_nonneg _
  calc
    ((fourFiveRoughInterval (yNat n) A B).card : Real) =
        abs (((fourFiveRoughInterval (yNat n) A B).card : Real) -
          (fourFiveContinuumMixtureKernel ((41 : Real) / 10) /
            Real.log (yNat n : Real)) * 0) := by
      rw [mul_zero, sub_zero, abs_of_nonneg hcardNonneg]
    _ <= arithmeticError +
        (((((B - A : Nat) : Real)) /
          Real.log (yNat n : Real)) * Ckernel) * ((3 : Real) / 5) +
        (Ckernel / Real.log (yNat n : Real)) *
          ((B - A : Nat) : Real) := hadapter
    _ = arithmeticError +
        (8 / 5 : Real) * Ckernel *
          (((B - A : Nat) : Real) /
            Real.log (yNat n : Real)) := by ring

/-! ## Span scaling -/

/-- A short physical span `H` satisfying the paper tail bound gives the
cutoff `Z/L^2+1` scale after division by `log(yNat)`. -/
theorem roughCanonicalExceptional_shortClippedSpan_div_log_le
    {n b : Nat} {H span a : Real}
    (hb : 0 < b)
    (ha : 0 <= a) (_hspanNonneg : 0 <= span)
    (hLone : 1 <= L n)
    (hlogLower :
      (1 / 5 : Real) * L n <= Real.log (yNat n : Real))
    (hH : 0 <= H)
    (hHupper : H <= 2 * a * (n : Real) / L n)
    (hspan : span <= H / (b : Real) + 1) :
    span / Real.log (yNat n : Real) <=
      (10 * a + 5) *
        (roughCanonicalExceptionalPhysicalRateScale n b / L n ^ 2 + 1) := by
  have hbReal : (0 : Real) < (b : Real) := by
    exact_mod_cast hb
  have hL : 0 < L n := zero_lt_one.trans_le hLone
  have hlog : 0 < Real.log (yNat n : Real) :=
    (mul_pos (by norm_num) hL).trans_le hlogLower
  have hcore :=
    roughCanonicalExceptional_self_div_core_le_physicalRateScale
      (n := n) hb
  have hHdiv :
      H / (b : Real) <=
        2 * a *
          roughCanonicalExceptionalPhysicalRateScale n b / L n := by
    calc
      H / (b : Real) <=
          (2 * a * (n : Real) / L n) / (b : Real) :=
        div_le_div_of_nonneg_right hHupper hbReal.le
      _ = (2 * a / L n) * ((n : Real) / (b : Real)) := by
        field_simp [hL.ne', hbReal.ne']
      _ <= (2 * a / L n) *
          roughCanonicalExceptionalPhysicalRateScale n b :=
        mul_le_mul_of_nonneg_left hcore
          (div_nonneg (mul_nonneg (by norm_num) ha) hL.le)
      _ = 2 * a *
          roughCanonicalExceptionalPhysicalRateScale n b / L n := by ring
  have hinvLog :
      1 / Real.log (yNat n : Real) <= 5 / L n := by
    apply (div_le_div_iff₀ hlog hL).2
    nlinarith [hlogLower]
  have hspanLog :
      span / Real.log (yNat n : Real) <=
        (2 * a *
            roughCanonicalExceptionalPhysicalRateScale n b / L n + 1) *
          (5 / L n) := by
    calc
      span / Real.log (yNat n : Real) =
          span * (1 / Real.log (yNat n : Real)) := by ring
      _ <= (H / (b : Real) + 1) * (5 / L n) :=
        mul_le_mul hspan hinvLog
          (one_div_nonneg.mpr hlog.le)
          (add_nonneg (div_nonneg hH hbReal.le) (by norm_num))
      _ <=
          (2 * a *
              roughCanonicalExceptionalPhysicalRateScale n b / L n + 1) *
            (5 / L n) :=
        mul_le_mul_of_nonneg_right
          (add_le_add hHdiv le_rfl) (div_nonneg (by norm_num) hL.le)
  have hInvL : 5 / L n <= 5 := by
    exact (div_le_iff₀ hL).2 (by nlinarith)
  let x :=
    roughCanonicalExceptionalPhysicalRateScale n b / L n ^ 2
  have hx : 0 <= x := by
    dsimp only [x]
    exact div_nonneg
      (by
        unfold roughCanonicalExceptionalPhysicalRateScale
        exact Nat.cast_nonneg _)
      (sq_nonneg (L n))
  calc
    span / Real.log (yNat n : Real) <=
        (2 * a *
            roughCanonicalExceptionalPhysicalRateScale n b / L n + 1) *
          (5 / L n) := hspanLog
    _ =
        10 * a *
          (roughCanonicalExceptionalPhysicalRateScale n b / L n ^ 2) +
          5 / L n := by ring
    _ <= 10 * a * x + 5 := by
      dsimp only [x]
      exact add_le_add le_rfl hInvL
    _ <= (10 * a + 5) * x + (10 * a + 5) := by
      exact add_le_add
        (mul_le_mul_of_nonneg_right (by linarith) hx)
        (by linarith)
    _ = (10 * a + 5) *
        (roughCanonicalExceptionalPhysicalRateScale n b / L n ^ 2 + 1) := by
      dsimp only [x]
      ring

/-- A broad physical span at most `n/b+1` gives the cutoff `Z/L+1`
scale after division by `log(yNat)`. -/
theorem roughCanonicalExceptional_broadClippedSpan_div_log_le
    {n b : Nat} {span : Real}
    (hb : 0 < b) (_hspanNonneg : 0 <= span)
    (hLone : 1 <= L n)
    (hlogLower :
      (1 / 5 : Real) * L n <= Real.log (yNat n : Real))
    (hspan : span <= (n : Real) / (b : Real) + 1) :
    span / Real.log (yNat n : Real) <=
      5 *
        (roughCanonicalExceptionalPhysicalRateScale n b / L n + 1) := by
  have hbReal : (0 : Real) < (b : Real) := by
    exact_mod_cast hb
  have hL : 0 < L n := zero_lt_one.trans_le hLone
  have hlog : 0 < Real.log (yNat n : Real) :=
    (mul_pos (by norm_num) hL).trans_le hlogLower
  have hcore :=
    roughCanonicalExceptional_self_div_core_le_physicalRateScale
      (n := n) hb
  have hinvLog :
      1 / Real.log (yNat n : Real) <= 5 / L n := by
    apply (div_le_div_iff₀ hlog hL).2
    nlinarith [hlogLower]
  have hspanLog :
      span / Real.log (yNat n : Real) <=
        (roughCanonicalExceptionalPhysicalRateScale n b + 1) *
          (5 / L n) := by
    calc
      span / Real.log (yNat n : Real) =
          span * (1 / Real.log (yNat n : Real)) := by ring
      _ <= ((n : Real) / (b : Real) + 1) * (5 / L n) :=
        mul_le_mul hspan hinvLog
          (one_div_nonneg.mpr hlog.le)
          (add_nonneg (div_nonneg (Nat.cast_nonneg n) hbReal.le)
            (by norm_num))
      _ <=
          (roughCanonicalExceptionalPhysicalRateScale n b + 1) *
            (5 / L n) :=
        mul_le_mul_of_nonneg_right
          (add_le_add hcore le_rfl) (div_nonneg (by norm_num) hL.le)
  have hInvL : 5 / L n <= 5 := by
    exact (div_le_iff₀ hL).2 (by nlinarith)
  calc
    span / Real.log (yNat n : Real) <=
        (roughCanonicalExceptionalPhysicalRateScale n b + 1) *
          (5 / L n) := hspanLog
    _ =
        5 * (roughCanonicalExceptionalPhysicalRateScale n b / L n) +
          5 / L n := by ring
    _ <=
        5 * (roughCanonicalExceptionalPhysicalRateScale n b / L n) +
          5 := add_le_add le_rfl hInvL
    _ = 5 *
        (roughCanonicalExceptionalPhysicalRateScale n b / L n + 1) := by
      ring

/-- The arithmetic paper rate is stronger than the cutoff square-log rate. -/
theorem roughCanonicalExceptional_paperRate_le_cutoffSqRate
    {n b : Nat} {P : Real}
    (hP : 0 <= P) (hLone : 1 <= L n) :
    P * (roughCanonicalExceptionalPhysicalRateScale n b / L n ^ 3) <=
      P *
        (roughCanonicalExceptionalPhysicalRateScale n b / L n ^ 2 + 1) := by
  have hL : 0 < L n := zero_lt_one.trans_le hLone
  have hLsqLeCube : L n ^ 2 <= L n ^ 3 := by
    calc
      L n ^ 2 = L n ^ 2 * 1 := by ring
      _ <= L n ^ 2 * L n :=
        mul_le_mul_of_nonneg_left hLone (sq_nonneg (L n))
      _ = L n ^ 3 := by ring
  have hrate :
      roughCanonicalExceptionalPhysicalRateScale n b / L n ^ 3 <=
        roughCanonicalExceptionalPhysicalRateScale n b / L n ^ 2 := by
    exact
      div_le_div_of_nonneg_left
        (by
          unfold roughCanonicalExceptionalPhysicalRateScale
          exact Nat.cast_nonneg _)
        (sq_pos_of_pos hL) hLsqLeCube
  exact mul_le_mul_of_nonneg_left
    (hrate.trans (le_add_of_nonneg_right (by norm_num))) hP

/-- The arithmetic paper rate is also stronger than the broad cutoff rate. -/
theorem roughCanonicalExceptional_paperRate_le_cutoffBroadRate
    {n b : Nat} {P : Real}
    (hP : 0 <= P) (hLone : 1 <= L n) :
    P * (roughCanonicalExceptionalPhysicalRateScale n b / L n ^ 3) <=
      P *
        (roughCanonicalExceptionalPhysicalRateScale n b / L n + 1) := by
  have hL : 0 < L n := zero_lt_one.trans_le hLone
  have hLLeCube : L n <= L n ^ 3 := by
    have hLsq : 1 <= L n ^ 2 :=
      one_le_pow₀ (n := 2) hLone
    calc
      L n = L n * 1 := by ring
      _ <= L n * L n ^ 2 :=
        mul_le_mul_of_nonneg_left hLsq hL.le
      _ = L n ^ 3 := by ring
  have hrate :
      roughCanonicalExceptionalPhysicalRateScale n b / L n ^ 3 <=
        roughCanonicalExceptionalPhysicalRateScale n b / L n := by
    exact
      div_le_div_of_nonneg_left
        (by
          unfold roughCanonicalExceptionalPhysicalRateScale
          exact Nat.cast_nonneg _)
        hL hLLeCube
  exact mul_le_mul_of_nonneg_left
    (hrate.trans (le_add_of_nonneg_right (by norm_num))) hP

/-! ## Three cutoff constants -/







theorem roughCanonicalFourFiveCutoffUpperEstimateConstant_nonneg
    {P Ckernel c : Real}
    (hP : 0 <= P) (hCkernel : 0 <= Ckernel) (hc : 0 <= c) :
    0 <= roughCanonicalFourFiveCutoffUpperEstimateConstant P Ckernel c := by
  unfold roughCanonicalFourFiveCutoffUpperEstimateConstant
  positivity

theorem roughCanonicalFourFiveCutoffHighEstimateConstant_nonneg
    (K0 : Nat) {P Ckernel c : Real}
    (hP : 0 <= P) (hCkernel : 0 <= Ckernel) (hc : 0 <= c) :
    0 <=
      roughCanonicalFourFiveCutoffHighEstimateConstant K0 P Ckernel c := by
  unfold roughCanonicalFourFiveCutoffHighEstimateConstant
  positivity

theorem roughCanonicalFourFiveCutoffBroadEstimateConstant_nonneg
    {P Ckernel : Real}
    (hP : 0 <= P) (hCkernel : 0 <= Ckernel) :
    0 <= roughCanonicalFourFiveCutoffBroadEstimateConstant P Ckernel := by
  unfold roughCanonicalFourFiveCutoffBroadEstimateConstant
  positivity

/-! ## Finite geometry-or-empty cutoff assembly -/

theorem roughCanonicalSignedExceptionalCutoffIntervalEstimate_of_geometry_or_empty
    {K0 n b : Nat} {c deltaStar P Ckernel : Real}
    (hy : 2 <= yNat n) (hc : 0 <= c)
    (hP : 0 <= P) (hCkernel : 0 <= Ckernel)
    (hLone : 1 <= L n)
    (hlogLower :
      (1 / 5 : Real) * L n <= Real.log (yNat n : Real))
    (htail :
      (upperTailLength c n : Real) <=
        2 * c * (n : Real) / L n)
    (hb :
      b ∈ roughCanonicalExceptionalCutoffCoreSet deltaStar n)
    (hbound :
      ∀ z ∈ Set.Icc ((41 : Real) / 10) ((47 : Real) / 10),
        abs (fourFiveContinuumMixtureKernel z) <= Ckernel ∧
        abs (fourFiveContinuumMixtureKernelDerivative z) <= Ckernel)
    (harithmetic :
      ∀ A B : Nat,
        RoughCanonicalExceptionalPhysicalIntervalGeometry
            n deltaStar b A B ->
          abs (((fourFiveRoughInterval (yNat n) A B).card : Real) -
              fourFiveContinuumMixtureIntegralMain (yNat n) A B) <=
            P * (roughCanonicalExceptionalPhysicalRateScale n b / L n ^ 3))
    (hintervals :
      (RoughCanonicalExceptionalPhysicalIntervalGeometry
          n deltaStar b
          (roughCanonicalExceptionalPhysicalLowerEndpoint
            n deltaStar b (2 * n))
          (roughCanonicalExceptionalPhysicalUpperEndpoint
            b (2 * n + upperTailLength c n)) ∨
        roughCanonicalExceptionalUpperPhysicalRoughInterval
            n (upperTailLength c n) deltaStar b = ∅) ∧
      (RoughCanonicalExceptionalPhysicalIntervalGeometry
          n deltaStar b
          (roughCanonicalExceptionalPhysicalLowerEndpoint n deltaStar b
            (2 * n - (K0 + 1) * upperTailLength c n))
          (roughCanonicalExceptionalPhysicalUpperEndpoint b (2 * n)) ∨
        roughCanonicalExceptionalHighPhysicalRoughInterval
            n (upperTailLength c n) (K0 + 1) deltaStar b = ∅) ∧
      (RoughCanonicalExceptionalPhysicalIntervalGeometry
          n deltaStar b
          (roughCanonicalExceptionalPhysicalLowerEndpoint
            n deltaStar b n)
          (roughCanonicalExceptionalPhysicalUpperEndpoint b
            (2 * n - (K0 + 1) * upperTailLength c n)) ∨
        roughCanonicalExceptionalBroadPhysicalRoughInterval
            n (upperTailLength c n) (K0 + 1) deltaStar b = ∅)) :
    RoughCanonicalSignedExceptionalCutoffIntervalEstimate
      K0 n b c deltaStar
      (roughCanonicalFourFiveCutoffUpperEstimateConstant P Ckernel c)
      (roughCanonicalFourFiveCutoffHighEstimateConstant
        K0 P Ckernel c)
      (roughCanonicalFourFiveCutoffBroadEstimateConstant P Ckernel) := by
  have hbData := Finset.mem_Ioc.mp
    (by simpa only [roughCanonicalExceptionalCutoffCoreSet] using hb)
  have hbPos : 0 < b := by omega
  have hLPos : 0 < L n := zero_lt_one.trans_le hLone
  have hscaleNonneg :
      0 <= roughCanonicalExceptionalPhysicalRateScale n b := by
    unfold roughCanonicalExceptionalPhysicalRateScale
    exact Nat.cast_nonneg _
  have hPupper :=
    roughCanonicalExceptional_paperRate_le_cutoffSqRate
      (n := n) (b := b) hP hLone
  have hPbroad :=
    roughCanonicalExceptional_paperRate_le_cutoffBroadRate
      (n := n) (b := b) hP hLone
  refine
    { upper := ?_
      high := ?_
      broad := ?_ }
  · rcases hintervals.1 with hgeometry | hempty
    · let A :=
        roughCanonicalExceptionalPhysicalLowerEndpoint
          n deltaStar b (2 * n)
      let B :=
        roughCanonicalExceptionalPhysicalUpperEndpoint
          b (2 * n + upperTailLength c n)
      have hcard :=
        fourFiveRoughInterval_card_le_arithmetic_add_fixedEndpointFreezing
          hy hgeometry (harithmetic A B hgeometry)
          hCkernel hbound
      have hlength : 2 * n + upperTailLength c n - 2 * n =
          upperTailLength c n := by omega
      have hspan :
          (((B - A : Nat) : Real)) <=
            (upperTailLength c n : Real) / (b : Real) + 1 := by
        simpa only [A, B, hlength] using
          (roughCanonicalExceptional_clippedPhysicalEndpoint_span_le
            (n := n) (b := b) (lo := 2 * n)
            (hi := 2 * n + upperTailLength c n)
            (deltaStar := deltaStar) hbPos (by omega))
      have hspanRate :=
        roughCanonicalExceptional_shortClippedSpan_div_log_le
          (n := n) (b := b)
          (H := (upperTailLength c n : Real))
          (span := ((B - A : Nat) : Real)) (a := c)
          hbPos hc (Nat.cast_nonneg _)
          hLone hlogLower (Nat.cast_nonneg _) htail hspan
      have hfinal :
          ((fourFiveRoughInterval (yNat n) A B).card : Real) <=
            roughCanonicalFourFiveCutoffUpperEstimateConstant P Ckernel c *
              (roughCanonicalExceptionalPhysicalRateScale n b / L n ^ 2 +
                1) := by
        calc
          ((fourFiveRoughInterval (yNat n) A B).card : Real) <=
              P * (roughCanonicalExceptionalPhysicalRateScale n b /
                  L n ^ 3) +
                (8 / 5 : Real) * Ckernel *
                  (((B - A : Nat) : Real) /
                    Real.log (yNat n : Real)) := hcard
          _ <=
              P * (roughCanonicalExceptionalPhysicalRateScale n b /
                  L n ^ 2 + 1) +
                (8 / 5 : Real) * Ckernel *
                  ((10 * c + 5) *
                    (roughCanonicalExceptionalPhysicalRateScale n b /
                      L n ^ 2 + 1)) :=
            add_le_add hPupper
              (mul_le_mul_of_nonneg_left hspanRate
                (mul_nonneg (by norm_num) hCkernel))
          _ =
              roughCanonicalFourFiveCutoffUpperEstimateConstant
                  P Ckernel c *
                (roughCanonicalExceptionalPhysicalRateScale n b /
                  L n ^ 2 + 1) := by
            unfold roughCanonicalFourFiveCutoffUpperEstimateConstant
            ring
      simpa only [A, B,
        roughCanonicalExceptionalUpperPhysicalRoughInterval,
        roughCanonicalExceptionalClippedRoughInterval_eq_endpoints] using
          hfinal
    · simp only [hempty, Finset.card_empty, Nat.cast_zero]
      exact mul_nonneg
        (roughCanonicalFourFiveCutoffUpperEstimateConstant_nonneg
          hP hCkernel hc)
        (add_nonneg (div_nonneg hscaleNonneg (sq_nonneg (L n)))
          (by norm_num : (0 : Real) <= 1))
  · rcases hintervals.2.1 with hgeometry | hempty
    · let A :=
        roughCanonicalExceptionalPhysicalLowerEndpoint n deltaStar b
          (2 * n - (K0 + 1) * upperTailLength c n)
      let B :=
        roughCanonicalExceptionalPhysicalUpperEndpoint b (2 * n)
      have hcard :=
        fourFiveRoughInterval_card_le_arithmetic_add_fixedEndpointFreezing
          hy hgeometry (harithmetic A B hgeometry)
          hCkernel hbound
      have hlength :
          2 * n -
              (2 * n - (K0 + 1) * upperTailLength c n) <=
            (K0 + 1) * upperTailLength c n := by
        omega
      have hspan0 :=
        roughCanonicalExceptional_clippedPhysicalEndpoint_span_le
          (n := n) (b := b)
          (lo := 2 * n - (K0 + 1) * upperTailLength c n)
          (hi := 2 * n) (deltaStar := deltaStar)
          hbPos (Nat.sub_le _ _)
      have hspan :
          (((B - A : Nat) : Real)) <=
            (((K0 + 1) * upperTailLength c n : Nat) : Real) /
              (b : Real) + 1 := by
        calc
          (((B - A : Nat) : Real)) <=
              ((2 * n -
                (2 * n - (K0 + 1) * upperTailLength c n) : Nat) : Real) /
                  (b : Real) + 1 := by
            simpa only [A, B] using hspan0
          _ <=
              (((K0 + 1) * upperTailLength c n : Nat) : Real) /
                  (b : Real) + 1 :=
            add_le_add
              (div_le_div_of_nonneg_right
                (by exact_mod_cast hlength) (by positivity))
              le_rfl
      have htailDepth :
          (((K0 + 1) * upperTailLength c n : Nat) : Real) <=
            2 * (((K0 + 1 : Nat) : Real) * c) *
              (n : Real) / L n := by
        norm_num only [Nat.cast_mul]
        calc
          ((K0 + 1 : Nat) : Real) *
              (upperTailLength c n : Real) <=
            ((K0 + 1 : Nat) : Real) *
              (2 * c * (n : Real) / L n) :=
            mul_le_mul_of_nonneg_left htail (Nat.cast_nonneg _)
          _ = 2 * (((K0 + 1 : Nat) : Real) * c) *
              (n : Real) / L n := by ring
      have hspanRate :=
        roughCanonicalExceptional_shortClippedSpan_div_log_le
          (n := n) (b := b)
          (H :=
            (((K0 + 1) * upperTailLength c n : Nat) : Real))
          (span := ((B - A : Nat) : Real))
          (a := ((K0 + 1 : Nat) : Real) * c)
          hbPos (mul_nonneg (Nat.cast_nonneg _) hc)
          (Nat.cast_nonneg _) hLone hlogLower (Nat.cast_nonneg _)
          htailDepth hspan
      have hfinal :
          ((fourFiveRoughInterval (yNat n) A B).card : Real) <=
            roughCanonicalFourFiveCutoffHighEstimateConstant
                K0 P Ckernel c *
              (roughCanonicalExceptionalPhysicalRateScale n b /
                L n ^ 2 + 1) := by
        calc
          ((fourFiveRoughInterval (yNat n) A B).card : Real) <=
              P * (roughCanonicalExceptionalPhysicalRateScale n b /
                  L n ^ 3) +
                (8 / 5 : Real) * Ckernel *
                  (((B - A : Nat) : Real) /
                    Real.log (yNat n : Real)) := hcard
          _ <=
              P * (roughCanonicalExceptionalPhysicalRateScale n b /
                  L n ^ 2 + 1) +
                (8 / 5 : Real) * Ckernel *
                  ((10 * (((K0 + 1 : Nat) : Real) * c) + 5) *
                    (roughCanonicalExceptionalPhysicalRateScale n b /
                      L n ^ 2 + 1)) :=
            add_le_add hPupper
              (mul_le_mul_of_nonneg_left hspanRate
                (mul_nonneg (by norm_num) hCkernel))
          _ =
              roughCanonicalFourFiveCutoffHighEstimateConstant
                  K0 P Ckernel c *
                (roughCanonicalExceptionalPhysicalRateScale n b /
                  L n ^ 2 + 1) := by
            unfold roughCanonicalFourFiveCutoffHighEstimateConstant
            ring
      simpa only [A, B,
        roughCanonicalExceptionalHighPhysicalRoughInterval,
        roughCanonicalExceptionalClippedRoughInterval_eq_endpoints] using
          hfinal
    · simp only [hempty, Finset.card_empty, Nat.cast_zero]
      exact mul_nonneg
        (roughCanonicalFourFiveCutoffHighEstimateConstant_nonneg
          K0 hP hCkernel hc)
        (add_nonneg (div_nonneg hscaleNonneg (sq_nonneg (L n)))
          (by norm_num : (0 : Real) <= 1))
  · rcases hintervals.2.2 with hgeometry | hempty
    · let A :=
        roughCanonicalExceptionalPhysicalLowerEndpoint
          n deltaStar b n
      let B :=
        roughCanonicalExceptionalPhysicalUpperEndpoint b
          (2 * n - (K0 + 1) * upperTailLength c n)
      have hcard :=
        fourFiveRoughInterval_card_le_arithmetic_add_fixedEndpointFreezing
          hy hgeometry (harithmetic A B hgeometry)
          hCkernel hbound
      have hupperNat :
          B <= roughCanonicalExceptionalPhysicalUpperEndpoint b (2 * n) := by
        dsimp only [B, roughCanonicalExceptionalPhysicalUpperEndpoint]
        exact Nat.div_le_div_right (Nat.sub_le _ _)
      have hspanNat :
          B - A <=
            roughCanonicalExceptionalPhysicalUpperEndpoint b (2 * n) -
              roughCanonicalExceptionalPhysicalLowerEndpoint
                n deltaStar b n := by
        omega
      have hspan0 :=
        roughCanonicalExceptional_clippedPhysicalEndpoint_span_le
          (n := n) (b := b) (lo := n) (hi := 2 * n)
          (deltaStar := deltaStar) hbPos (by omega)
      have htwoSub : 2 * n - n = n := by
        omega
      have hspan :
          (((B - A : Nat) : Real)) <=
            (n : Real) / (b : Real) + 1 := by
        calc
          (((B - A : Nat) : Real)) <=
              ((roughCanonicalExceptionalPhysicalUpperEndpoint b (2 * n) -
                roughCanonicalExceptionalPhysicalLowerEndpoint
                  n deltaStar b n : Nat) : Real) := by
            exact_mod_cast hspanNat
          _ <= ((2 * n - n : Nat) : Real) / (b : Real) + 1 :=
            hspan0
          _ = (n : Real) / (b : Real) + 1 := by
            simp only [htwoSub]
      have hspanRate :=
        roughCanonicalExceptional_broadClippedSpan_div_log_le
          (n := n) (b := b)
          (span := ((B - A : Nat) : Real))
          hbPos (Nat.cast_nonneg _) hLone hlogLower hspan
      have hfinal :
          ((fourFiveRoughInterval (yNat n) A B).card : Real) <=
            roughCanonicalFourFiveCutoffBroadEstimateConstant P Ckernel *
              (roughCanonicalExceptionalPhysicalRateScale n b / L n + 1) := by
        calc
          ((fourFiveRoughInterval (yNat n) A B).card : Real) <=
              P * (roughCanonicalExceptionalPhysicalRateScale n b /
                  L n ^ 3) +
                (8 / 5 : Real) * Ckernel *
                  (((B - A : Nat) : Real) /
                    Real.log (yNat n : Real)) := hcard
          _ <=
              P * (roughCanonicalExceptionalPhysicalRateScale n b /
                  L n + 1) +
                (8 / 5 : Real) * Ckernel *
                  (5 *
                    (roughCanonicalExceptionalPhysicalRateScale n b /
                      L n + 1)) :=
            add_le_add hPbroad
              (mul_le_mul_of_nonneg_left hspanRate
                (mul_nonneg (by norm_num) hCkernel))
          _ =
              roughCanonicalFourFiveCutoffBroadEstimateConstant P Ckernel *
                (roughCanonicalExceptionalPhysicalRateScale n b / L n +
                  1) := by
            unfold roughCanonicalFourFiveCutoffBroadEstimateConstant
            ring
      simpa only [A, B,
        roughCanonicalExceptionalBroadPhysicalRoughInterval,
        roughCanonicalExceptionalClippedRoughInterval_eq_endpoints] using
          hfinal
    · simp only [hempty, Finset.card_empty, Nat.cast_zero]
      exact mul_nonneg
        (roughCanonicalFourFiveCutoffBroadEstimateConstant_nonneg
          hP hCkernel)
        (add_nonneg (div_nonneg hscaleNonneg hLPos.le)
          (by norm_num : (0 : Real) <= 1))

/-! ## Eventual cutoff estimates -/



end BankPaperRealization

end

end Erdos390.WholePaper

end

theorem solution :
∀ {K0 n b : Nat} {c deltaStar P Ckernel : Real},
  LE.le.{0} (2 : Nat) (Erdos390.Full.ArithmeticModel.yNat n) →
    LE.le.{0} (0 : Real) c →
      LE.le.{0} (0 : Real) P →
        LE.le.{0} (0 : Real) Ckernel →
          LE.le.{0} (1 : Real) (Erdos390.Full.Scale.L n) →
            LE.le.{0} (HMul.hMul.{0, 0, 0} (1 / 5 : Real) (Erdos390.Full.Scale.L n))
                (Real.log ↑(Erdos390.Full.ArithmeticModel.yNat n)) →
              LE.le.{0} (↑(Erdos390.WholePaper.upperTailLength c n))
                  (HDiv.hDiv.{0, 0, 0} (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} (2 : Real) c) ↑n)
                    (Erdos390.Full.Scale.L n)) →
                Membership.mem.{0, 0}
                    (Erdos390.WholePaper.BankPaperRealization.roughCanonicalExceptionalCutoffCoreSet deltaStar n) b →
                  (∀ (z : Real),
                      Membership.mem.{0, 0} (Set.Icc.{0} (41 / 10 : Real) (47 / 10 : Real)) z →
                        And
                          (LE.le.{0}
                            (abs.{0} (Erdos390.WholePaper.BankPaperRealization.fourFiveContinuumMixtureKernel z))
                            Ckernel)
                          (LE.le.{0}
                            (abs.{0}
                              (Erdos390.WholePaper.BankPaperRealization.fourFiveContinuumMixtureKernelDerivative z))
                            Ckernel)) →
                    (∀ (A B : Nat),
                        Erdos390.WholePaper.BankPaperRealization.RoughCanonicalExceptionalPhysicalIntervalGeometry n
                            deltaStar b A B →
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
                                (Erdos390.WholePaper.BankPaperRealization.roughCanonicalExceptionalPhysicalRateScale n
                                  b)
                                (HPow.hPow.{0, 0, 0} (Erdos390.Full.Scale.L n) (3 : Nat))))) →
                      And
                          (Or
                            (Erdos390.WholePaper.BankPaperRealization.RoughCanonicalExceptionalPhysicalIntervalGeometry
                              n deltaStar b
                              (Erdos390.WholePaper.BankPaperRealization.roughCanonicalExceptionalPhysicalLowerEndpoint n
                                deltaStar b (HMul.hMul.{0, 0, 0} (2 : Nat) n))
                              (Erdos390.WholePaper.BankPaperRealization.roughCanonicalExceptionalPhysicalUpperEndpoint b
                                (HAdd.hAdd.{0, 0, 0} (HMul.hMul.{0, 0, 0} (2 : Nat) n)
                                  (Erdos390.WholePaper.upperTailLength c n))))
                            (Eq.{1}
                              (Erdos390.WholePaper.BankPaperRealization.roughCanonicalExceptionalUpperPhysicalRoughInterval
                                n (Erdos390.WholePaper.upperTailLength c n) deltaStar b)
                              EmptyCollection.emptyCollection.{0}))
                          (And
                            (Or
                              (Erdos390.WholePaper.BankPaperRealization.RoughCanonicalExceptionalPhysicalIntervalGeometry
                                n deltaStar b
                                (Erdos390.WholePaper.BankPaperRealization.roughCanonicalExceptionalPhysicalLowerEndpoint
                                  n deltaStar b
                                  (HSub.hSub.{0, 0, 0} (HMul.hMul.{0, 0, 0} (2 : Nat) n)
                                    (HMul.hMul.{0, 0, 0} (HAdd.hAdd.{0, 0, 0} K0 (1 : Nat))
                                      (Erdos390.WholePaper.upperTailLength c n))))
                                (Erdos390.WholePaper.BankPaperRealization.roughCanonicalExceptionalPhysicalUpperEndpoint
                                  b (HMul.hMul.{0, 0, 0} (2 : Nat) n)))
                              (Eq.{1}
                                (Erdos390.WholePaper.BankPaperRealization.roughCanonicalExceptionalHighPhysicalRoughInterval
                                  n (Erdos390.WholePaper.upperTailLength c n) (HAdd.hAdd.{0, 0, 0} K0 (1 : Nat))
                                  deltaStar b)
                                EmptyCollection.emptyCollection.{0}))
                            (Or
                              (Erdos390.WholePaper.BankPaperRealization.RoughCanonicalExceptionalPhysicalIntervalGeometry
                                n deltaStar b
                                (Erdos390.WholePaper.BankPaperRealization.roughCanonicalExceptionalPhysicalLowerEndpoint
                                  n deltaStar b n)
                                (Erdos390.WholePaper.BankPaperRealization.roughCanonicalExceptionalPhysicalUpperEndpoint
                                  b
                                  (HSub.hSub.{0, 0, 0} (HMul.hMul.{0, 0, 0} (2 : Nat) n)
                                    (HMul.hMul.{0, 0, 0} (HAdd.hAdd.{0, 0, 0} K0 (1 : Nat))
                                      (Erdos390.WholePaper.upperTailLength c n)))))
                              (Eq.{1}
                                (Erdos390.WholePaper.BankPaperRealization.roughCanonicalExceptionalBroadPhysicalRoughInterval
                                  n (Erdos390.WholePaper.upperTailLength c n) (HAdd.hAdd.{0, 0, 0} K0 (1 : Nat))
                                  deltaStar b)
                                EmptyCollection.emptyCollection.{0}))) →
                        Erdos390.WholePaper.BankPaperRealization.RoughCanonicalSignedExceptionalCutoffIntervalEstimate
                          K0 n b c deltaStar
                          (Erdos390.WholePaper.BankPaperRealization.roughCanonicalFourFiveCutoffUpperEstimateConstant P
                            Ckernel c)
                          (Erdos390.WholePaper.BankPaperRealization.roughCanonicalFourFiveCutoffHighEstimateConstant K0
                            P Ckernel c)
                          (Erdos390.WholePaper.BankPaperRealization.roughCanonicalFourFiveCutoffBroadEstimateConstant P
                            Ckernel) := by
  exact @Erdos390.WholePaper.BankPaperRealization.roughCanonicalSignedExceptionalCutoffIntervalEstimate_of_geometry_or_empty
