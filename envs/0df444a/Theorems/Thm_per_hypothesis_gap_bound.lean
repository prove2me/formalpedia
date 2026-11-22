-- Prove2me | Theorems.Thm_per_hypothesis_gap_bound
-- name    : per_hypothesis_gap_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:38:23.814383+00:00
-- url     : https://prove2.me/theorems/c625b165-ed33-46a4-9d96-b82452688c4f
-- title:
--   per hypothesis gap bound: per hypothesis gap bound
-- statement:
--   Per-hypothesis Hoeffding on the double sample: for a FIXED hypothesis h,
--       the probability that EmpErr(h,S') - EmpErr(h,S) ≥ ε/2 under D^m ⊗ D^m
--       is at most exp(-mε²/8).
--
--       Proof: The gap = (1/m)∑ᵢ (Zᵢ' - Zᵢ) where Zᵢ = 1[h(xᵢ)≠c(xᵢ)], Zᵢ' = 1[h(x'ᵢ)≠c(x'ᵢ)]
--       are iid Bernoulli(p) with p = TrueError(h,c,D). The differences Wᵢ = Zᵢ' - Zᵢ are
--       independent, bounded in [-1,1], and centered (E[Wᵢ] = 0).
--       By Hoeffding's inequality: P[(1/m)∑Wᵢ ≥ ε/2] ≤ exp(-mε²/8).
--
--       This uses the sub-Gaussian machinery from T1, extended to the product space.
--
--       **Proof sketch:**
--       1. Pair D^m ⊗ D^m ≅ (D⊗D)^m via the natural isomorphism
--          (Fin m → X) × (Fin m → X) ≃ᵐ Fin m → X × X
--       2. Define g : X × X → ℝ, g(a,b) = 1[h(b)≠c(b)] - 1[h(a)≠c(a)]
--          Then g ∈ [-1,1], E_{D⊗D}[g] = 0, so HasSubgaussianMGF g 1 (D⊗D)
--       3. The gap = (1/m)∑ᵢ g(xᵢ, x'ᵢ) where pairs are iIndepFun under (D⊗D)^m
--       4. By measure_sum_ge_le_of_iIndepFun: P[∑g ≥ mε/2] ≤ exp(-(mε/2)²/(2m)) = exp(-mε²/8)
--
--       **Mathlib chain:** iIndepFun_pi + HasSubgaussianMGF.of_map + measure_sum_ge_le_of_iIndepFun
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Complexity/Symmetrization.lean#L425-L544
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Complexity/Symmetrization.lean#L425-L544

module
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Generalization_Core
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Rademacher
public import Mathlib.Probability.Moments.SubGaussian
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Symmetrization
set_option autoImplicit true
@[expose] public section
public section
universe u v
open MeasureTheory ENNReal

theorem per_hypothesis_gap_bound {X : Type u} [MeasurableSpace X]
    (D : MeasureTheory.Measure X) [MeasureTheory.IsProbabilityMeasure D]
    (h c : Concept X Bool) (hmeas_h : Measurable h) (hc_meas : Measurable c)
    (m : ℕ) (hm : 0 < m) (ε : ℝ) (hε : 0 < ε) :
    let μ := MeasureTheory.Measure.pi (fun _ : Fin m => D)
    (μ.prod μ)
      {p : (Fin m → X) × (Fin m → X) |
        EmpiricalError X Bool h (fun i => (p.2 i, c (p.2 i))) (zeroOneLoss Bool) -
        EmpiricalError X Bool h (fun i => (p.1 i, c (p.1 i))) (zeroOneLoss Bool) ≥ ε / 2}
    ≤ ENNReal.ofReal (Real.exp (-(↑m * ε ^ 2 / 8))) := by sorry
