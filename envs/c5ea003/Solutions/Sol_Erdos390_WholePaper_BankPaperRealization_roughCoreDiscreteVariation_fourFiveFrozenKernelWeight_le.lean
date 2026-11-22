-- Prove2me | solution 1 for Erdos390.WholePaper.BankPaperRealization.roughCoreDiscreteVariation_fourFiveFrozenKernelWeight_le
-- status  : ACCEPTED   (prove)
-- author  : @doctosil
-- created : 2026-09-17T16:01:50.248661+00:00
-- url     : https://prove2.me/submissions/62ee133c-8848-4acd-81e5-8ca3629ea554

import Mathlib
import Definitions.Def_erdos390_source_bank_interface
import Definitions.Def_erdos390_dickman_step_function
import Theorems.Thm_MediumPNT
import Definitions.Def_erdos390_analytic_foundations_001
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_product_bound
import Theorems.Thm_Erdos390_Full_DickmanBasic_rho_pos_on_zero_five
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_secondDerivative_first_bound
import Definitions.Def_erdos390_analytic_foundations_009

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







end Erdos390.WholePaper.BankPaperRealization

end

/- Source module: Erdos390.WholePaper.BankPaperCanonicalFourFiveKernelVariation -/
section


/-!
# Discrete variation of the frozen four/five kernel

The periodic exceptional-core argument needs the prime-power variation of

`b ↦ K(log((2n)/b) / log(yNat n)) / b`.

This file proves that estimate from the already formalized uniform `C¹`
bound for `fourFiveContinuumMixtureKernel`.  The coordinate-range premise is
kept explicit: it is the elementary chamber geometry asserting that all
sampled logarithmic coordinates lie in the padded interval `[4.1,4.7]`.

No rough-number count or exceptional-core asymptotic is used here.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel

noncomputable section

namespace BankPaperRealization

/-! ## The literal frozen kernel -/





/-! ## Compact `C¹` control -/

/-- A common derivative bound on the padded chamber makes the continuum
mixture kernel Lipschitz there. -/
theorem abs_fourFiveContinuumMixtureKernel_sub_le_of_C1_bound
    {C u v : Real}
    (hbound :
      ∀ z ∈ Set.Icc ((41 : Real) / 10) ((47 : Real) / 10),
        abs (fourFiveContinuumMixtureKernel z) <= C ∧
        abs (fourFiveContinuumMixtureKernelDerivative z) <= C)
    (hu : u ∈ Set.Icc ((41 : Real) / 10) ((47 : Real) / 10))
    (hv : v ∈ Set.Icc ((41 : Real) / 10) ((47 : Real) / 10)) :
    abs (fourFiveContinuumMixtureKernel u -
      fourFiveContinuumMixtureKernel v) <= C * abs (u - v) := by
  have hdiff (z : Real)
      (hz : z ∈ Set.Icc ((41 : Real) / 10) ((47 : Real) / 10)) :
      DifferentiableAt Real fourFiveContinuumMixtureKernel z :=
    (hasDerivAt_fourFiveContinuumMixtureKernel hz).differentiableAt
  have hderiv (z : Real)
      (hz : z ∈ Set.Icc ((41 : Real) / 10) ((47 : Real) / 10)) :
      ‖deriv fourFiveContinuumMixtureKernel z‖ <= C := by
    rw [(hasDerivAt_fourFiveContinuumMixtureKernel hz).deriv,
      Real.norm_eq_abs]
    exact (hbound z hz).2
  have hmean := Convex.norm_image_sub_le_of_norm_deriv_le
    hdiff hderiv
      (convex_Icc ((41 : Real) / 10) ((47 : Real) / 10)) hv hu
  simpa only [Real.norm_eq_abs] using hmean

/-! ## Coordinate increments -/

/-- Multiplication by a fixed positive integer cancels from the consecutive
logarithmic-coordinate increment. -/
theorem roughCanonicalFourFiveFrozenCoordinate_sub_succ
    {n D m : Nat} (hn : 0 < n) (hD : 0 < D) (hm : 0 < m)
    (hlogY : Real.log (yNat n : Real) ≠ 0) :
    roughCanonicalFourFiveFrozenCoordinate n (D * m) -
        roughCanonicalFourFiveFrozenCoordinate n (D * (m + 1)) =
      Real.log (((m + 1 : Nat) : Real) / (m : Real)) /
        Real.log (yNat n : Real) := by
  have hnReal : (0 : Real) < (n : Real) := by exact_mod_cast hn
  have htwoN : (0 : Real) < 2 * (n : Real) := by positivity
  have hDReal : (0 : Real) < (D : Real) := by exact_mod_cast hD
  have hmReal : (0 : Real) < (m : Real) := by exact_mod_cast hm
  have hmOneReal : (0 : Real) < ((m + 1 : Nat) : Real) := by positivity
  have hmSuccReal : (0 : Real) < (m : Real) + 1 := by positivity
  unfold roughCanonicalFourFiveFrozenCoordinate
  simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  rw [Real.log_div htwoN.ne' (mul_pos hDReal hmReal).ne',
    Real.log_div htwoN.ne' (mul_pos hDReal hmSuccReal).ne',
    Real.log_mul hDReal.ne' hmReal.ne',
    Real.log_mul hDReal.ne' hmSuccReal.ne',
    Real.log_div hmSuccReal.ne' hmReal.ne']
  field_simp [hlogY]
  ring

/-- If `log(yNat n) >= 1`, one consecutive frozen coordinate changes by at
most `1/m`. -/
theorem abs_roughCanonicalFourFiveFrozenCoordinate_sub_succ_le
    {n D m : Nat} (hn : 0 < n) (hD : 0 < D) (hm : 0 < m)
    (hlogY : 1 <= Real.log (yNat n : Real)) :
    abs (roughCanonicalFourFiveFrozenCoordinate n (D * m) -
      roughCanonicalFourFiveFrozenCoordinate n (D * (m + 1))) <=
        1 / (m : Real) := by
  have hmReal : (0 : Real) < (m : Real) := by exact_mod_cast hm
  have hmOneReal : (0 : Real) < ((m + 1 : Nat) : Real) := by positivity
  have hratioPos :
      (0 : Real) < ((m + 1 : Nat) : Real) / (m : Real) :=
    div_pos hmOneReal hmReal
  have hratioOne :
      (1 : Real) <= ((m + 1 : Nat) : Real) / (m : Real) := by
    apply (le_div_iff₀ hmReal).2
    simpa only [one_mul] using
      (show (m : Real) <= ((m + 1 : Nat) : Real) by
        exact_mod_cast Nat.le_succ m)
  have hlogRatioNonneg :
      0 <= Real.log (((m + 1 : Nat) : Real) / (m : Real)) :=
    Real.log_nonneg hratioOne
  have hlogRatio :
      Real.log (((m + 1 : Nat) : Real) / (m : Real)) <=
        1 / (m : Real) := by
    have h := Real.log_le_sub_one_of_pos hratioPos
    calc
      Real.log (((m + 1 : Nat) : Real) / (m : Real)) <=
          ((m + 1 : Nat) : Real) / (m : Real) - 1 := h
      _ = 1 / (m : Real) := by
        field_simp [hmReal.ne']
        push_cast
        ring
  have hlogYPos : 0 < Real.log (yNat n : Real) :=
    zero_lt_one.trans_le hlogY
  rw [roughCanonicalFourFiveFrozenCoordinate_sub_succ
    hn hD hm hlogYPos.ne',
    abs_of_nonneg (div_nonneg hlogRatioNonneg hlogYPos.le)]
  exact (div_le_self hlogRatioNonneg hlogY).trans hlogRatio

/-! ## Finite variation algebra -/

/-- An endpoint bound and a telescoping reciprocal-step bound imply the
required total discrete variation. -/
theorem roughCoreDiscreteVariation_le_two_mul_div_of_reciprocalSteps
    {F : Nat -> Real} {D B : Nat} {C : Real}
    (hD : 0 < D) (hB : 1 <= B) (hC : 0 <= C)
    (hend : abs (F B) <= C / ((D : Real) * (B : Real)))
    (hstep : ∀ m ∈ Finset.Ioc 0 (B - 1),
      abs (F m - F (m + 1)) <=
        (2 * C / (D : Real)) *
          (1 / (m : Real) - 1 / ((m + 1 : Nat) : Real))) :
    roughCoreDiscreteVariation F B <= 2 * C / (D : Real) := by
  have hB0 : B ≠ 0 := by omega
  have hDReal : (0 : Real) < (D : Real) := by exact_mod_cast hD
  have hBReal : (0 : Real) < (B : Real) := by exact_mod_cast hB
  have hinterval :
      Finset.Ioc 0 (B - 1) = Finset.Ico 1 B := by
    ext m
    simp only [Finset.mem_Ioc, Finset.mem_Ico]
    omega
  have htelescope :
      (∑ m ∈ Finset.Ioc 0 (B - 1),
        (1 / (m : Real) - 1 / ((m + 1 : Nat) : Real))) =
          1 - 1 / (B : Real) := by
    rw [hinterval]
    simpa only [neg_sub_neg, one_div, Nat.cast_one, inv_one] using
      (Finset.sum_Ico_sub
        (fun m : Nat => -(1 / (m : Real))) hB)
  rw [roughCoreDiscreteVariation, if_neg hB0]
  calc
    abs (F B) +
        ∑ m ∈ Finset.Ioc 0 (B - 1), abs (F m - F (m + 1)) <=
      C / ((D : Real) * (B : Real)) +
        ∑ m ∈ Finset.Ioc 0 (B - 1),
          (2 * C / (D : Real)) *
            (1 / (m : Real) - 1 / ((m + 1 : Nat) : Real)) :=
      add_le_add hend (Finset.sum_le_sum hstep)
    _ = C / ((D : Real) * (B : Real)) +
        (2 * C / (D : Real)) * (1 - 1 / (B : Real)) := by
      rw [← Finset.mul_sum, htelescope]
    _ = 2 * C / (D : Real) -
        C / ((D : Real) * (B : Real)) := by
      field_simp [hDReal.ne', hBReal.ne']
      ring
    _ <= 2 * C / (D : Real) := by
      exact sub_le_self _ (div_nonneg hC
        (mul_nonneg hDReal.le hBReal.le))

/-! ## The literal kernel variation -/

/-- A uniform `C¹` bound and the padded coordinate geometry give the
discrete variation of the literal frozen four/five kernel. -/
theorem roughCoreDiscreteVariation_fourFiveFrozenKernelWeight_le
    {n D B : Nat} {C : Real}
    (hn : 0 < n) (hD : 0 < D) (hlogY : 1 <= Real.log (yNat n : Real))
    (hC : 0 <= C)
    (hbound :
      ∀ z ∈ Set.Icc ((41 : Real) / 10) ((47 : Real) / 10),
        abs (fourFiveContinuumMixtureKernel z) <= C ∧
        abs (fourFiveContinuumMixtureKernelDerivative z) <= C)
    (hcoordinate : ∀ m ∈ Finset.Icc 1 B,
      roughCanonicalFourFiveFrozenCoordinate n (D * m) ∈
        Set.Icc ((41 : Real) / 10) ((47 : Real) / 10)) :
    roughCoreDiscreteVariation
        (fun m => roughCanonicalFourFiveFrozenKernelWeight n (D * m)) B <=
      2 * C / (D : Real) := by
  by_cases hB0 : B = 0
  · subst B
    simp only [roughCoreDiscreteVariation]
    exact div_nonneg (mul_nonneg (by norm_num) hC)
      (Nat.cast_nonneg D)
  have hB : 1 <= B := Nat.one_le_iff_ne_zero.mpr hB0
  apply roughCoreDiscreteVariation_le_two_mul_div_of_reciprocalSteps
    hD hB hC
  · have hDB0 : D * B ≠ 0 :=
      Nat.mul_ne_zero (Nat.ne_of_gt hD) hB0
    have hDBReal : (0 : Real) < ((D * B : Nat) : Real) := by
      exact_mod_cast Nat.mul_pos hD (by omega : 0 < B)
    rw [roughCanonicalFourFiveFrozenKernelWeight, if_neg hDB0,
      abs_div, abs_of_pos hDBReal]
    simpa only [Nat.cast_mul] using
      div_le_div_of_nonneg_right
        (hbound _ (hcoordinate B (Finset.mem_Icc.mpr ⟨hB, le_rfl⟩))).1
        hDBReal.le
  · intro m hm
    have hmData := Finset.mem_Ioc.mp hm
    have hmPos : 0 < m := hmData.1
    have hmOneLeB : m + 1 <= B := by omega
    have hmMem : m ∈ Finset.Icc 1 B :=
      Finset.mem_Icc.mpr ⟨hmPos, by omega⟩
    have hmOneMem : m + 1 ∈ Finset.Icc 1 B :=
      Finset.mem_Icc.mpr ⟨by omega, hmOneLeB⟩
    have hDReal : (0 : Real) < (D : Real) := by exact_mod_cast hD
    have hmReal : (0 : Real) < (m : Real) := by exact_mod_cast hmPos
    have hmOneReal : (0 : Real) < ((m + 1 : Nat) : Real) := by
      positivity
    have hDm0 : D * m ≠ 0 :=
      Nat.mul_ne_zero (Nat.ne_of_gt hD) (Nat.ne_of_gt hmPos)
    have hDmOne0 : D * (m + 1) ≠ 0 :=
      Nat.mul_ne_zero (Nat.ne_of_gt hD) (by omega)
    have hDmOneReal :
        (0 : Real) < ((D * (m + 1) : Nat) : Real) := by
      exact_mod_cast Nat.mul_pos hD (by omega : 0 < m + 1)
    let u := roughCanonicalFourFiveFrozenCoordinate n (D * m)
    let v := roughCanonicalFourFiveFrozenCoordinate n (D * (m + 1))
    have hu : u ∈ Set.Icc ((41 : Real) / 10) ((47 : Real) / 10) :=
      hcoordinate m hmMem
    have hv : v ∈ Set.Icc ((41 : Real) / 10) ((47 : Real) / 10) :=
      hcoordinate (m + 1) hmOneMem
    have hcoordinateStep : abs (u - v) <= 1 / (m : Real) := by
      exact abs_roughCanonicalFourFiveFrozenCoordinate_sub_succ_le
        hn hD hmPos hlogY
    have hkernel :
        abs (fourFiveContinuumMixtureKernel u -
          fourFiveContinuumMixtureKernel v) <=
            C * (1 / (m : Real)) := by
      exact (abs_fourFiveContinuumMixtureKernel_sub_le_of_C1_bound
        hbound hu hv).trans
          (mul_le_mul_of_nonneg_left hcoordinateStep hC)
    have hstepNonneg :
        0 <= 1 / (m : Real) -
          1 / ((m + 1 : Nat) : Real) := by
      exact sub_nonneg.mpr
        (one_div_le_one_div_of_le hmReal
          (by exact_mod_cast (Nat.le_succ m)))
    have hreciprocalD :
        1 / ((D * m : Nat) : Real) -
            1 / ((D * (m + 1) : Nat) : Real) =
          (1 / (D : Real)) *
            (1 / (m : Real) -
              1 / ((m + 1 : Nat) : Real)) := by
      push_cast
      field_simp [hDReal.ne', hmReal.ne', hmOneReal.ne']
    have hreciprocalNonneg :
        0 <= 1 / ((D * m : Nat) : Real) -
          1 / ((D * (m + 1) : Nat) : Real) := by
      rw [hreciprocalD]
      exact mul_nonneg (by positivity) hstepNonneg
    have hfirst :
        abs (fourFiveContinuumMixtureKernel u *
          (1 / ((D * m : Nat) : Real) -
            1 / ((D * (m + 1) : Nat) : Real))) <=
          (C / (D : Real)) *
            (1 / (m : Real) -
              1 / ((m + 1 : Nat) : Real)) := by
      rw [abs_mul, abs_of_nonneg hreciprocalNonneg, hreciprocalD]
      calc
        abs (fourFiveContinuumMixtureKernel u) *
            ((1 / (D : Real)) *
              (1 / (m : Real) -
                1 / ((m + 1 : Nat) : Real))) <=
          C * ((1 / (D : Real)) *
              (1 / (m : Real) -
                1 / ((m + 1 : Nat) : Real))) :=
            mul_le_mul_of_nonneg_right (hbound u hu).1
              (mul_nonneg (by positivity) hstepNonneg)
        _ = (C / (D : Real)) *
            (1 / (m : Real) -
              1 / ((m + 1 : Nat) : Real)) := by ring
    have hsecond :
        abs ((fourFiveContinuumMixtureKernel u -
            fourFiveContinuumMixtureKernel v) /
          ((D * (m + 1) : Nat) : Real)) <=
          (C / (D : Real)) *
            (1 / (m : Real) -
              1 / ((m + 1 : Nat) : Real)) := by
      rw [abs_div, abs_of_pos hDmOneReal]
      calc
        abs (fourFiveContinuumMixtureKernel u -
            fourFiveContinuumMixtureKernel v) /
            ((D * (m + 1) : Nat) : Real) <=
          (C * (1 / (m : Real))) /
            ((D * (m + 1) : Nat) : Real) :=
              div_le_div_of_nonneg_right hkernel hDmOneReal.le
        _ = (C / (D : Real)) *
            (1 / (m : Real) -
              1 / ((m + 1 : Nat) : Real)) := by
          push_cast
          field_simp [hDReal.ne', hmReal.ne', hmOneReal.ne']
          ring
    have hweightM :
        roughCanonicalFourFiveFrozenKernelWeight n (D * m) =
          fourFiveContinuumMixtureKernel u /
            ((D * m : Nat) : Real) := by
      rw [roughCanonicalFourFiveFrozenKernelWeight, if_neg hDm0]
    have hweightMOne :
        roughCanonicalFourFiveFrozenKernelWeight n (D * (m + 1)) =
          fourFiveContinuumMixtureKernel v /
            ((D * (m + 1) : Nat) : Real) := by
      rw [roughCanonicalFourFiveFrozenKernelWeight, if_neg hDmOne0]
    have hdecomposition :
        fourFiveContinuumMixtureKernel u /
              ((D * m : Nat) : Real) -
            fourFiveContinuumMixtureKernel v /
              ((D * (m + 1) : Nat) : Real) =
          fourFiveContinuumMixtureKernel u *
              (1 / ((D * m : Nat) : Real) -
                1 / ((D * (m + 1) : Nat) : Real)) +
            (fourFiveContinuumMixtureKernel u -
              fourFiveContinuumMixtureKernel v) /
                ((D * (m + 1) : Nat) : Real) := by
      ring
    rw [hweightM, hweightMOne, hdecomposition]
    calc
      abs (fourFiveContinuumMixtureKernel u *
            (1 / ((D * m : Nat) : Real) -
              1 / ((D * (m + 1) : Nat) : Real)) +
          (fourFiveContinuumMixtureKernel u -
            fourFiveContinuumMixtureKernel v) /
              ((D * (m + 1) : Nat) : Real)) <=
        abs (fourFiveContinuumMixtureKernel u *
            (1 / ((D * m : Nat) : Real) -
              1 / ((D * (m + 1) : Nat) : Real))) +
          abs ((fourFiveContinuumMixtureKernel u -
            fourFiveContinuumMixtureKernel v) /
              ((D * (m + 1) : Nat) : Real)) :=
        abs_add_le _ _
      _ <= (C / (D : Real)) *
            (1 / (m : Real) -
              1 / ((m + 1 : Nat) : Real)) +
          (C / (D : Real)) *
            (1 / (m : Real) -
              1 / ((m + 1 : Nat) : Real)) :=
        add_le_add hfirst hsecond
      _ = (2 * C / (D : Real)) *
          (1 / (m : Real) -
            1 / ((m + 1 : Nat) : Real)) := by ring







end BankPaperRealization

end

end Erdos390.WholePaper

end

theorem solution :
∀ {n D B : Nat} {C : Real},
  LT.lt.{0} (0 : Nat) n →
    LT.lt.{0} (0 : Nat) D →
      LE.le.{0} (1 : Real) (Real.log ↑(Erdos390.Full.ArithmeticModel.yNat n)) →
        LE.le.{0} (0 : Real) C →
          (∀ (z : Real),
              Membership.mem.{0, 0} (Set.Icc.{0} (41 / 10 : Real) (47 / 10 : Real)) z →
                And (LE.le.{0} (abs.{0} (Erdos390.WholePaper.BankPaperRealization.fourFiveContinuumMixtureKernel z)) C)
                  (LE.le.{0}
                    (abs.{0} (Erdos390.WholePaper.BankPaperRealization.fourFiveContinuumMixtureKernelDerivative z))
                    C)) →
            (∀ (m : Nat),
                Membership.mem.{0, 0} (Finset.Icc.{0} (1 : Nat) B) m →
                  Membership.mem.{0, 0} (Set.Icc.{0} (41 / 10 : Real) (47 / 10 : Real))
                    (Erdos390.WholePaper.BankPaperRealization.roughCanonicalFourFiveFrozenCoordinate n
                      (HMul.hMul.{0, 0, 0} D m))) →
              LE.le.{0}
                (Erdos390.WholePaper.BankPaperRealization.roughCoreDiscreteVariation
                  (fun m =>
                    Erdos390.WholePaper.BankPaperRealization.roughCanonicalFourFiveFrozenKernelWeight n
                      (HMul.hMul.{0, 0, 0} D m))
                  B)
                (HDiv.hDiv.{0, 0, 0} (HMul.hMul.{0, 0, 0} (2 : Real) C) ↑D) := by
  exact @Erdos390.WholePaper.BankPaperRealization.roughCoreDiscreteVariation_fourFiveFrozenKernelWeight_le
