-- Prove2me | solution 1 for MarkovChainCLT.asymptoticVariance_eq_of_clt_of_bounded
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-08-21T19:45:06.221202+00:00
-- url     : https://prove2.me/submissions/0454b9fb-2eb9-442d-ac67-81276b132de0

import Definitions.Def_MarkovAsymptoticVariance
import Definitions.Def_MarkovErgodicity
import Definitions.Def_MarkovChainPathMeasure
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.Probability.Moments.Variance
import Theorems.Thm_MarkovChainCLT_integral_sq_iterKernel_pow_le
import Theorems.Thm_MarkovChainCLT_exists_lag_tvDist_le_of_uniformlyErgodic
import Theorems.Thm_MarkovChainCLT_clt_of_bounded_of_uniformlyErgodic
import Theorems.Thm_MarkovChainCLT_integral_mul_coord_eq
import Theorems.Thm_MarkovChainCLT_integral_pow_four_scaled_sampleAvg_le
import Mathlib.Topology.ContinuousMap.Bounded.Basic
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Theorems.Thm_MarkovChainCLT_integral_sq_scaled_sampleAvg_le
import Theorems.Thm_MarkovChainCLT_integrable_sq_scaled_sampleAvg
import Theorems.Thm_MarkovChainCLT_gaussian_variance_le_of_tendstoInDistribution
import Theorems.Thm_MarkovChainCLT_abs_exp_variance_sub_le_of_tendstoInDistribution
import Theorems.Thm_MarkovChainCLT_abs_sub_le_exp_mul_abs_exp_neg_half_sub

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology

namespace MarkovChainCLT

variable {X : Type*} [MeasurableSpace X]

lemma sq_integral_le_integral_sq {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (g : Ω → ℝ) (hg : MemLp g 2 μ) :
    (∫ x, g x ∂μ) ^ 2 ≤ ∫ x, (g x) ^ 2 ∂μ := by
  have h := ProbabilityTheory.variance_nonneg g μ
  rw [ProbabilityTheory.variance_eq_sub hg] at h
  simp only [Pi.pow_apply] at h
  linarith

/-- Bochner version of the composition formula for a measure and a kernel. -/
lemma integral_comp_measure (P : Kernel X X) [IsMarkovKernel P] (π : Measure X)
    [IsProbabilityMeasure π] (f : X → ℝ) (hf : Integrable f (P ∘ₘ π)) :
    ∫ z, f z ∂(P ∘ₘ π) = ∫ x, ∫ y, f y ∂(P x) ∂π := by
  rw [Measure.comp_eq_comp_const_apply] at hf ⊢
  rw [ProbabilityTheory.Kernel.integral_comp hf]
  simp

/-- Jensen: the transition operator does not increase the `L²(π)` norm when `π` is
invariant. -/
lemma integral_sq_step_le (P : Kernel X X) [IsMarkovKernel P] (π : Measure X)
    [IsProbabilityMeasure π] (hinv : Kernel.Invariant P π)
    (g : X → ℝ) (hg : Measurable g) (hL2 : Integrable (fun x => (g x) ^ 2) π) :
    ∫ x, (∫ y, g y ∂(P x)) ^ 2 ∂π ≤ ∫ x, (g x) ^ 2 ∂π := by
  have hcomp : (P ∘ₘ π) = π := hinv
  have hL2c : Integrable (fun x => (g x) ^ 2) (P ∘ₘ π) := by rw [hcomp]; exact hL2
  have hsplit := (Measure.integrable_comp_iff (κ := P) (μ := π) (f := fun x => (g x) ^ 2)
    ((hg.pow_const 2).aestronglyMeasurable)).1 hL2c
  have hnormeq : (fun x => ∫ y, ‖(g y) ^ 2‖ ∂(P x)) = fun x => ∫ y, (g y) ^ 2 ∂(P x) := by
    funext x
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    dsimp only
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  have hint2 : Integrable (fun x => ∫ y, (g y) ^ 2 ∂(P x)) π := by
    rw [← hnormeq]; exact hsplit.2
  have heq : ∫ x, (∫ y, (g y) ^ 2 ∂(P x)) ∂π = ∫ x, (g x) ^ 2 ∂π := by
    rw [← integral_comp_measure P π _ hL2c, hcomp]
  rw [← heq]
  refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun x => sq_nonneg _) hint2 ?_
  filter_upwards [hsplit.1] with x hx
  exact sq_integral_le_integral_sq (P x) g
    ((memLp_two_iff_integrable_sq hg.aestronglyMeasurable).2 hx)

lemma integrable_sq_step (P : Kernel X X) [IsMarkovKernel P] (π : Measure X)
    [IsProbabilityMeasure π] (g : X → ℝ) (hg : Measurable g)
    (hL2 : Integrable (fun x => (g x) ^ 2) π) (hinv : Kernel.Invariant P π) :
    Integrable (fun x => (∫ y, g y ∂(P x)) ^ 2) π := by
  have hcomp : (P ∘ₘ π) = π := hinv
  have hL2c : Integrable (fun x => (g x) ^ 2) (P ∘ₘ π) := by rw [hcomp]; exact hL2
  have hsplit := (Measure.integrable_comp_iff (κ := P) (μ := π) (f := fun x => (g x) ^ 2)
    ((hg.pow_const 2).aestronglyMeasurable)).1 hL2c
  have hnormeq : (fun x => ∫ y, ‖(g y) ^ 2‖ ∂(P x)) = fun x => ∫ y, (g y) ^ 2 ∂(P x) := by
    funext x
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    dsimp only
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  have hint2 : Integrable (fun x => ∫ y, (g y) ^ 2 ∂(P x)) π := by
    rw [← hnormeq]; exact hsplit.2
  refine Integrable.mono' hint2 ?_ ?_
  · exact ((StronglyMeasurable.integral_kernel (κ := P)
      hg.stronglyMeasurable).pow 2).aestronglyMeasurable
  · filter_upwards [hsplit.1] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact sq_integral_le_integral_sq (P x) g
      ((memLp_two_iff_integrable_sq hg.aestronglyMeasurable).2 hx)

@[simp] lemma iterKernel_one (P : Kernel X X) [IsMarkovKernel P] : iterKernel P 1 = P := by
  rw [iterKernel_succ, iterKernel_zero, Kernel.comp_id]

lemma iterKernel_add (P : Kernel X X) [IsMarkovKernel P] (a b : ℕ) :
    iterKernel P (a + b) = iterKernel P a ∘ₖ iterKernel P b := by
  induction a with
  | zero => simp
  | succ a ih =>
      have hab : a + 1 + b = (a + b) + 1 := by omega
      rw [hab, iterKernel_succ, ih, iterKernel_succ, Kernel.comp_assoc]

lemma invariant_iterKernel (P : Kernel X X) [IsMarkovKernel P] (π : Measure X)
    [IsProbabilityMeasure π] (hinv : Kernel.Invariant P π) (k : ℕ) :
    Kernel.Invariant (iterKernel P k) π := by
  induction k with
  | zero =>
      have hid : ⇑(iterKernel P 0) = (Measure.dirac : X → Measure X) := by
        funext x; rw [iterKernel_zero, Kernel.id_apply]
      show ⇑(iterKernel P 0) ∘ₘ π = π
      rw [hid]
      exact Measure.bind_dirac
  | succ k ih => rw [iterKernel_succ]; exact Kernel.Invariant.comp hinv ih

/-- The conditional-mean operator of the `k`-step kernel is an `L²(π)` contraction. -/
lemma iterMean_bound (P : Kernel X X) [IsMarkovKernel P] (π : Measure X)
    [IsProbabilityMeasure π] (hinv : Kernel.Invariant P π) :
    ∀ (k : ℕ) (g : X → ℝ), Measurable g → Integrable (fun x => (g x) ^ 2) π →
      Integrable (fun x => (∫ y, g y ∂(iterKernel P k x)) ^ 2) π ∧
      ∫ x, (∫ y, g y ∂(iterKernel P k x)) ^ 2 ∂π ≤ ∫ x, (g x) ^ 2 ∂π := by
  intro k
  induction k with
  | zero =>
      intro g hg hL2
      have hd : ∀ x, ∫ y, g y ∂(iterKernel P 0 x) = g x := by
        intro x
        rw [iterKernel_zero, Kernel.id_apply]
        exact integral_dirac' _ x hg.stronglyMeasurable
      simp only [hd]
      exact ⟨hL2, le_rfl⟩
  | succ k ih =>
      intro g hg hL2
      have hgint : Integrable g π :=
        ((memLp_two_iff_integrable_sq hg.aestronglyMeasurable).2 hL2).integrable (by norm_num)
      have hPg : Measurable (fun x => ∫ y, g y ∂(P x)) :=
        (StronglyMeasurable.integral_kernel (κ := P) hg.stronglyMeasurable).measurable
      have hPgL2 : Integrable (fun x => (∫ y, g y ∂(P x)) ^ 2) π :=
        integrable_sq_step P π g hg hL2 hinv
      have hstep := ih (fun x => ∫ y, g y ∂(P x)) hPg hPgL2
      -- rewrite the (k+1)-step mean as the k-step mean of the one-step mean
      have hae : ∀ᵐ x ∂π, ∫ y, g y ∂(iterKernel P (k + 1) x)
          = ∫ w, (∫ y, g y ∂(P w)) ∂(iterKernel P k x) := by
        have hinvk : Kernel.Invariant (iterKernel P (k + 1)) π :=
          invariant_iterKernel P π hinv (k + 1)
        have hgc : Integrable g ((iterKernel P (k + 1)) ∘ₘ π) := by
          rw [show ((iterKernel P (k + 1)) ∘ₘ π) = π from hinvk]; exact hgint
        have hsplit := (Measure.integrable_comp_iff (κ := iterKernel P (k + 1)) (μ := π)
          (f := g) hg.aestronglyMeasurable).1 hgc
        filter_upwards [hsplit.1] with x hx
        rw [iterKernel_succ] at hx ⊢
        exact ProbabilityTheory.Kernel.integral_comp hx
      constructor
      · refine (hstep.1).congr' ?_ ?_
        · exact ((StronglyMeasurable.integral_kernel (κ := iterKernel P (k + 1))
            hg.stronglyMeasurable).pow 2).aestronglyMeasurable
        · filter_upwards [hae] with x hx; rw [hx]
      · rw [integral_congr_ae (g := fun x => (∫ w, (∫ y, g y ∂(P w)) ∂(iterKernel P k x)) ^ 2)
          (by filter_upwards [hae] with x hx; rw [hx])]
        exact le_trans hstep.2 (integral_sq_step_le P π hinv g hg hL2)

lemma iterMean_add_ae (P : Kernel X X) [IsMarkovKernel P] (π : Measure X)
    [IsProbabilityMeasure π] (hinv : Kernel.Invariant P π) (g : X → ℝ) (hg : Measurable g)
    (hint : Integrable g π) (a b : ℕ) :
    ∀ᵐ x ∂π, ∫ y, g y ∂(iterKernel P (a + b) x)
      = ∫ w, (∫ y, g y ∂(iterKernel P a w)) ∂(iterKernel P b x) := by
  have hinvk : Kernel.Invariant (iterKernel P (a + b)) π := invariant_iterKernel P π hinv (a + b)
  have hgc : Integrable g ((iterKernel P (a + b)) ∘ₘ π) := by
    rw [show ((iterKernel P (a + b)) ∘ₘ π) = π from hinvk]; exact hint
  have hsplit := (Measure.integrable_comp_iff (κ := iterKernel P (a + b)) (μ := π)
    (f := g) hg.aestronglyMeasurable).1 hgc
  filter_upwards [hsplit.1] with x hx
  rw [iterKernel_add] at hx ⊢
  exact ProbabilityTheory.Kernel.integral_comp hx

/-- Geometric `L²` decay of the `k`-step conditional mean of a centred observable. -/
lemma integral_sq_iterKernel_geom_decay (P : Kernel X X) [IsMarkovKernel P] (π : Measure X)
    [IsProbabilityMeasure π] (hinv : Kernel.Invariant P π) (N : ℕ) (hN : 1 ≤ N) (ρ : ℝ)
    (hρ0 : 0 ≤ ρ) (hρ : 4 * ρ ≤ 1 / 4) (hrate : ∀ x, tvDist (iterKernel P N x) π ≤ ρ)
    (h : X → ℝ) (hh : Measurable h) (hL2 : Integrable (fun x => (h x) ^ 2) π)
    (hmean : ∫ x, h x ∂π = 0) (k : ℕ) :
    ∫ x, (∫ y, h y ∂(iterKernel P k x)) ^ 2 ∂π
      ≤ (1 / 4 : ℝ) ^ (k / N) * ∫ x, (h x) ^ 2 ∂π := by
  set j := k / N with hj
  set s := k % N with hs
  have hk : j * N + s = k := by
    rw [hj, hs, mul_comm]
    exact Nat.div_add_mod k N
  have hint : Integrable h π :=
    ((memLp_two_iff_integrable_sq hh.aestronglyMeasurable).2 hL2).integrable (by norm_num)
  set G : X → ℝ := fun w => ∫ y, h y ∂(iterKernel P (j * N) w) with hG
  have hGmeas : Measurable G :=
    (StronglyMeasurable.integral_kernel (κ := iterKernel P (j * N))
      hh.stronglyMeasurable).measurable
  have hGb := iterMean_bound P π hinv (j * N) h hh hL2
  have hGpow := integral_sq_iterKernel_pow_le P π hinv N ρ hρ0 hρ hrate h hh hL2 hmean j
  have hae := iterMean_add_ae P π hinv h hh hint (j * N) s
  have hrw : ∫ x, (∫ y, h y ∂(iterKernel P k x)) ^ 2 ∂π
      = ∫ x, (∫ w, G w ∂(iterKernel P s x)) ^ 2 ∂π := by
    rw [← hk]
    exact integral_congr_ae (by filter_upwards [hae] with x hx; rw [hx])
  rw [hrw]
  exact le_trans (iterMean_bound P π hinv s G hGmeas hGb.1).2 hGpow

lemma summable_half_pow_div (N : ℕ) (hN : 1 ≤ N) :
    Summable (fun k : ℕ => (1 / 2 : ℝ) ^ (k / N)) := by
  set r : ℝ := (1 / 2 : ℝ) ^ ((1 : ℝ) / N) with hr
  have hNpos : (0:ℝ) < N := by exact_mod_cast hN
  have hr0 : 0 < r := Real.rpow_pos_of_pos (by norm_num) _
  have hr1 : r < 1 := by
    rw [hr]
    exact Real.rpow_lt_one (by norm_num) (by norm_num) (by positivity)
  have hbound : ∀ k : ℕ, (1 / 2 : ℝ) ^ (k / N) ≤ 2 * r ^ k := by
    intro k
    have h1 : N * (k / N) + k % N = k := Nat.div_add_mod k N
    have h2 : k % N < N := Nat.mod_lt _ (by omega)
    have h3 : (k : ℝ) < (N : ℝ) * ((k / N : ℕ) : ℝ) + (N : ℝ) := by
      have : k < N * (k / N) + N := by omega
      exact_mod_cast this
    have hk : (k : ℝ) / N - 1 ≤ ((k / N : ℕ) : ℝ) := by
      rw [sub_le_iff_le_add, div_le_iff₀ hNpos]
      nlinarith [h3]
    have e1 : (1 / 2 : ℝ) ^ (k / N) = (1 / 2 : ℝ) ^ (((k / N : ℕ) : ℝ)) :=
      (Real.rpow_natCast _ _).symm
    have e2 : (1 / 2 : ℝ) ^ (((k / N : ℕ) : ℝ)) ≤ (1 / 2 : ℝ) ^ ((k : ℝ) / N - 1) :=
      Real.rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num) hk
    have e3 : (1 / 2 : ℝ) ^ ((k : ℝ) / N - 1) = 2 * r ^ k := by
      have hkN : (k : ℝ) / N = (1 / (N:ℝ)) * (k:ℝ) := by ring
      have hpow : (1 / 2 : ℝ) ^ ((k : ℝ) / N) = r ^ k := by
        rw [hkN, Real.rpow_mul (by norm_num), ← hr, Real.rpow_natCast]
      rw [Real.rpow_sub (by norm_num), Real.rpow_one, hpow]
      ring
    rw [e1]
    exact le_trans e2 (le_of_eq e3)
  refine Summable.of_nonneg_of_le (fun k => by positivity) hbound ?_
  exact (summable_geometric_of_lt_one hr0.le hr1).mul_left 2


/-! ### Cauchy-Schwarz and the `L²(π)` norm -/

/-- Cauchy-Schwarz for the Bochner integral, via nonnegativity of the discriminant. -/
lemma abs_integral_mul_le (π : Measure X) [IsProbabilityMeasure π] (a b : X → ℝ)
    (ha : MemLp a 2 π) (hb : MemLp b 2 π) :
    |∫ x, a x * b x ∂π|
      ≤ Real.sqrt (∫ x, (a x) ^ 2 ∂π) * Real.sqrt (∫ x, (b x) ^ 2 ∂π) := by
  set A := ∫ x, (a x) ^ 2 ∂π with hA
  set B := ∫ x, (b x) ^ 2 ∂π with hB
  set C := ∫ x, a x * b x ∂π with hC
  have hA0 : 0 ≤ A := integral_nonneg fun x => sq_nonneg _
  have hB0 : 0 ≤ B := integral_nonneg fun x => sq_nonneg _
  have hAi : Integrable (fun x => (a x) ^ 2) π := (memLp_two_iff_integrable_sq
    ha.aestronglyMeasurable).1 ha
  have hBi : Integrable (fun x => (b x) ^ 2) π := (memLp_two_iff_integrable_sq
    hb.aestronglyMeasurable).1 hb
  have hCi : Integrable (fun x => a x * b x) π := MemLp.integrable_mul (p := 2) (q := 2) ha hb
  have hquad : ∀ lam : ℝ, 0 ≤ lam ^ 2 * A + 2 * lam * C + B := by
    intro lam
    have hexp : ∀ x, (lam * a x + b x) ^ 2
        = lam ^ 2 * (a x) ^ 2 + 2 * lam * (a x * b x) + (b x) ^ 2 := by
      intro x; ring
    have i1 : Integrable (fun x => lam ^ 2 * (a x) ^ 2) π := hAi.const_mul _
    have i2 : Integrable (fun x => 2 * lam * (a x * b x)) π := hCi.const_mul _
    have i12 : Integrable (fun x => lam ^ 2 * (a x) ^ 2 + 2 * lam * (a x * b x)) π := i1.fun_add i2
    have h0 : (0:ℝ) ≤ ∫ x, (lam * a x + b x) ^ 2 ∂π := integral_nonneg fun x => sq_nonneg _
    rw [integral_congr_ae (Filter.Eventually.of_forall hexp),
      integral_add i12 hBi, integral_add i1 i2,
      integral_const_mul, integral_const_mul] at h0
    exact h0
  have hdisc : C ^ 2 ≤ A * B := by
    rcases eq_or_lt_of_le hA0 with hA0' | hApos
    · -- A = 0 forces C = 0
      have hC0 : C = 0 := by
        by_contra hne
        have h := hquad (-(B + 1) / (2 * C))
        have hne2 : (2:ℝ) * C ≠ 0 := mul_ne_zero two_ne_zero hne
        have key : 2 * (-(B + 1) / (2 * C)) * C = -(B + 1) := by field_simp
        rw [← hA0', mul_zero, zero_add, key] at h
        linarith
      rw [hC0, ← hA0']; simp
    · have h := hquad (-C / A)
      have hAne : A ≠ 0 := ne_of_gt hApos
      have key : (-C / A) ^ 2 * A + 2 * (-C / A) * C + B = B - C ^ 2 / A := by
        field_simp; ring
      rw [key, sub_nonneg, div_le_iff₀ hApos] at h
      exact le_trans h (le_of_eq (mul_comm B A))
  have hfin : |C| ≤ Real.sqrt A * Real.sqrt B := by
    rw [← Real.sqrt_sq_eq_abs, ← Real.sqrt_mul hA0]
    exact Real.sqrt_le_sqrt hdisc
  exact hfin

/-- The `L²(π)` norm of a real observable. -/
noncomputable def l2NormAux (π : Measure X) (g : X → ℝ) : ℝ :=
  Real.sqrt (∫ x, (g x) ^ 2 ∂π)

lemma l2NormAux_nonneg (π : Measure X) (g : X → ℝ) : 0 ≤ l2NormAux π g := Real.sqrt_nonneg _

/-- The lagged covariance, written as an integral of the centred observable against the
`k`-step conditional mean of the centred observable. -/
lemma lagCovariance_eq_centred (P : Kernel X X) [IsMarkovKernel P] (π : Measure X)
    [IsProbabilityMeasure π] (hinv : Kernel.Invariant P π)
    (φ ψ : X → ℝ) (hψ : Measurable ψ) (hψint : Integrable ψ π) (k : ℕ) :
    lagCovariance P π φ ψ k
      = ∫ x, (φ x - ∫ y, φ y ∂π)
          * (∫ y, (ψ y - ∫ z, ψ z ∂π) ∂(iterKernel P k x)) ∂π := by
  have hinvk : Kernel.Invariant (iterKernel P k) π := invariant_iterKernel P π hinv k
  have hψc : Integrable ψ ((iterKernel P k) ∘ₘ π) := by
    rw [show ((iterKernel P k) ∘ₘ π) = π from hinvk]; exact hψint
  have hsplit := (Measure.integrable_comp_iff (κ := iterKernel P k) (μ := π)
    (f := ψ) hψ.aestronglyMeasurable).1 hψc
  unfold lagCovariance
  refine integral_congr_ae ?_
  filter_upwards [hsplit.1] with x hx
  congr 1
  rw [integral_sub hx (integrable_const _), integral_const]
  simp

/-- **Geometric decay of the lagged covariance, bilinear form.** -/
lemma abs_lagCovariance_le_bilin (P : Kernel X X) [IsMarkovKernel P] (π : Measure X)
    [IsProbabilityMeasure π] (hinv : Kernel.Invariant P π) (N : ℕ) (hN : 1 ≤ N)
    (hrate : ∀ x, tvDist (iterKernel P N x) π ≤ 1 / 16)
    (φ ψ : X → ℝ) (hφ : Measurable φ) (hψ : Measurable ψ)
    (hφ2 : MemLp φ 2 π) (hψ2 : MemLp ψ 2 π) (k : ℕ) :
    |lagCovariance P π φ ψ k|
      ≤ l2NormAux π (fun x => φ x - ∫ y, φ y ∂π)
        * l2NormAux π (fun x => ψ x - ∫ y, ψ y ∂π) * (1 / 2 : ℝ) ^ (k / N) := by
  set hφc : X → ℝ := fun x => φ x - ∫ y, φ y ∂π with hφcdef
  set hψc : X → ℝ := fun x => ψ x - ∫ y, ψ y ∂π with hψcdef
  have hφcm : Measurable hφc := hφ.sub measurable_const
  have hψcm : Measurable hψc := hψ.sub measurable_const
  have hφcL2 : MemLp hφc 2 π := hφ2.sub (memLp_const _)
  have hψcL2 : MemLp hψc 2 π := hψ2.sub (memLp_const _)
  have hψcsq : Integrable (fun x => (hψc x) ^ 2) π :=
    (memLp_two_iff_integrable_sq hψcm.aestronglyMeasurable).1 hψcL2
  have hψcmean : ∫ x, hψc x ∂π = 0 := by
    rw [hψcdef]
    rw [integral_sub (hψ2.integrable (by norm_num)) (integrable_const _), integral_const]
    simp
  set G : X → ℝ := fun x => ∫ y, hψc y ∂(iterKernel P k x) with hGdef
  have hGmeas : Measurable G :=
    (StronglyMeasurable.integral_kernel (κ := iterKernel P k) hψcm.stronglyMeasurable).measurable
  have hGb := iterMean_bound P π hinv k hψc hψcm hψcsq
  have hGL2 : MemLp G 2 π := (memLp_two_iff_integrable_sq hGmeas.aestronglyMeasurable).2 hGb.1
  have hrw : lagCovariance P π φ ψ k = ∫ x, hφc x * G x ∂π :=
    lagCovariance_eq_centred P π hinv φ ψ hψ (hψ2.integrable (by norm_num)) k
  rw [hrw]
  refine le_trans (abs_integral_mul_le π hφc G hφcL2 hGL2) ?_
  have hGdecay := integral_sq_iterKernel_geom_decay P π hinv N hN (1 / 16) (by norm_num)
    (by norm_num) hrate hψc hψcm hψcsq hψcmean k
  have hGnorm : Real.sqrt (∫ x, (G x) ^ 2 ∂π)
      ≤ (1 / 2 : ℝ) ^ (k / N) * l2NormAux π hψc := by
    have hpow : (1 / 4 : ℝ) ^ (k / N) = ((1 / 2 : ℝ) ^ (k / N)) ^ 2 := by
      have h4 : (1 / 4 : ℝ) = (1 / 2 : ℝ) ^ 2 := by norm_num
      rw [h4, ← pow_mul, ← pow_mul, Nat.mul_comm 2 (k / N)]
    have h1 : Real.sqrt (∫ x, (G x) ^ 2 ∂π)
        ≤ Real.sqrt (((1 / 2 : ℝ) ^ (k / N)) ^ 2 * ∫ x, (hψc x) ^ 2 ∂π) := by
      refine Real.sqrt_le_sqrt ?_
      rw [← hpow]
      exact hGdecay
    refine le_trans h1 (le_of_eq ?_)
    rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by positivity), l2NormAux]
  calc l2NormAux π hφc * Real.sqrt (∫ x, (G x) ^ 2 ∂π)
      ≤ l2NormAux π hφc * ((1 / 2 : ℝ) ^ (k / N) * l2NormAux π hψc) :=
        mul_le_mul_of_nonneg_left hGnorm (l2NormAux_nonneg _ _)
    _ = l2NormAux π hφc * l2NormAux π hψc * (1 / 2 : ℝ) ^ (k / N) := by ring

lemma summable_lagCovariance_succ (P : Kernel X X) [IsMarkovKernel P] (π : Measure X)
    [IsProbabilityMeasure π] (hinv : Kernel.Invariant P π) (N : ℕ) (hN : 1 ≤ N)
    (hrate : ∀ x, tvDist (iterKernel P N x) π ≤ 1 / 16)
    (φ ψ : X → ℝ) (hφ : Measurable φ) (hψ : Measurable ψ)
    (hφ2 : MemLp φ 2 π) (hψ2 : MemLp ψ 2 π) :
    Summable (fun k : ℕ => lagCovariance P π φ ψ (k + 1)) := by
  set M := l2NormAux π (fun x => φ x - ∫ y, φ y ∂π)
    * l2NormAux π (fun x => ψ x - ∫ y, ψ y ∂π) with hM
  have hM0 : 0 ≤ M := mul_nonneg (l2NormAux_nonneg _ _) (l2NormAux_nonneg _ _)
  refine Summable.of_norm_bounded (g := fun k : ℕ => M * (1 / 2 : ℝ) ^ (k / N))
    ((summable_half_pow_div N hN).mul_left M) fun k => ?_
  rw [Real.norm_eq_abs]
  refine le_trans (abs_lagCovariance_le_bilin P π hinv N hN hrate φ ψ hφ hψ hφ2 hψ2 (k + 1)) ?_
  have hle : k / N ≤ (k + 1) / N := Nat.div_le_div_right (by omega)
  have hp : (1 / 2 : ℝ) ^ ((k + 1) / N) ≤ (1 / 2 : ℝ) ^ (k / N) :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) hle
  nlinarith [hM0, hp]

/-- Bilinearity of the lagged covariance, in the form needed to compare two observables. -/
lemma lagCovariance_diag_sub (P : Kernel X X) [IsMarkovKernel P] (π : Measure X)
    [IsProbabilityMeasure π] (hinv : Kernel.Invariant P π)
    (φ ψ : X → ℝ) (hφ : Measurable φ) (hψ : Measurable ψ)
    (hφ2 : MemLp φ 2 π) (hψ2 : MemLp ψ 2 π) (k : ℕ) :
    lagCovariance P π φ φ k - lagCovariance P π ψ ψ k
      = lagCovariance P π (fun x => φ x - ψ x) φ k
        + lagCovariance P π ψ (fun x => φ x - ψ x) k := by
  have hφi : Integrable φ π := hφ2.integrable (by norm_num)
  have hψi : Integrable ψ π := hψ2.integrable (by norm_num)
  have hdi : Integrable (fun x => φ x - ψ x) π := hφi.sub hψi
  set cφ := ∫ y, φ y ∂π with hcφ
  set cψ := ∫ y, ψ y ∂π with hcψ
  have hcd : ∫ y, (φ y - ψ y) ∂π = cφ - cψ := integral_sub hφi hψi
  set Hφ : X → ℝ := fun x => φ x - cφ with hHφ
  set Hψ : X → ℝ := fun x => ψ x - cψ with hHψ
  have hHφm : Measurable Hφ := hφ.sub measurable_const
  have hHψm : Measurable Hψ := hψ.sub measurable_const
  have hHφ2 : MemLp Hφ 2 π := hφ2.sub (memLp_const _)
  have hHψ2 : MemLp Hψ 2 π := hψ2.sub (memLp_const _)
  have hHφsq : Integrable (fun x => (Hφ x) ^ 2) π :=
    (memLp_two_iff_integrable_sq hHφm.aestronglyMeasurable).1 hHφ2
  have hHψsq : Integrable (fun x => (Hψ x) ^ 2) π :=
    (memLp_two_iff_integrable_sq hHψm.aestronglyMeasurable).1 hHψ2
  set Gφ : X → ℝ := fun x => ∫ y, Hφ y ∂(iterKernel P k x) with hGφ
  set Gψ : X → ℝ := fun x => ∫ y, Hψ y ∂(iterKernel P k x) with hGψ
  have hGφm : Measurable Gφ :=
    (StronglyMeasurable.integral_kernel (κ := iterKernel P k) hHφm.stronglyMeasurable).measurable
  have hGψm : Measurable Gψ :=
    (StronglyMeasurable.integral_kernel (κ := iterKernel P k) hHψm.stronglyMeasurable).measurable
  have hGφ2 : MemLp Gφ 2 π := (memLp_two_iff_integrable_sq hGφm.aestronglyMeasurable).2
    (iterMean_bound P π hinv k Hφ hHφm hHφsq).1
  have hGψ2 : MemLp Gψ 2 π := (memLp_two_iff_integrable_sq hGψm.aestronglyMeasurable).2
    (iterMean_bound P π hinv k Hψ hHψm hHψsq).1
  -- the four lagged covariances as integrals
  have e1 : lagCovariance P π φ φ k = ∫ x, Hφ x * Gφ x ∂π :=
    lagCovariance_eq_centred P π hinv φ φ hφ hφi k
  have e2 : lagCovariance P π ψ ψ k = ∫ x, Hψ x * Gψ x ∂π :=
    lagCovariance_eq_centred P π hinv ψ ψ hψ hψi k
  have e3 : lagCovariance P π (fun x => φ x - ψ x) φ k
      = ∫ x, (Hφ x - Hψ x) * Gφ x ∂π := by
    rw [lagCovariance_eq_centred P π hinv (fun x => φ x - ψ x) φ hφ hφi k]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    congr 1
    rw [hcd, hHφ, hHψ]; ring
  have e4 : lagCovariance P π ψ (fun x => φ x - ψ x) k
      = ∫ x, Hψ x * (Gφ x - Gψ x) ∂π := by
    have hdm : Measurable (fun x => φ x - ψ x) := hφ.sub hψ
    rw [lagCovariance_eq_centred P π hinv ψ (fun x => φ x - ψ x) hdm hdi k]
    have hinvk : Kernel.Invariant (iterKernel P k) π := invariant_iterKernel P π hinv k
    have hsplitφ := (Measure.integrable_comp_iff (κ := iterKernel P k) (μ := π)
      (f := Hφ) hHφm.aestronglyMeasurable).1
      (by rw [show ((iterKernel P k) ∘ₘ π) = π from hinvk]
          exact hHφ2.integrable (by norm_num))
    have hsplitψ := (Measure.integrable_comp_iff (κ := iterKernel P k) (μ := π)
      (f := Hψ) hHψm.aestronglyMeasurable).1
      (by rw [show ((iterKernel P k) ∘ₘ π) = π from hinvk]
          exact hHψ2.integrable (by norm_num))
    refine integral_congr_ae ?_
    filter_upwards [hsplitφ.1, hsplitψ.1] with x hxφ hxψ
    congr 1
    have : ∀ y, (φ y - ψ y) - (cφ - cψ) = Hφ y - Hψ y := by intro y; rw [hHφ, hHψ]; ring
    rw [hcd]
    rw [integral_congr_ae (Filter.Eventually.of_forall this), integral_sub hxφ hxψ]
  -- combine
  have i1 : Integrable (fun x => Hφ x * Gφ x) π := MemLp.integrable_mul (p := 2) (q := 2) hHφ2 hGφ2
  have i2 : Integrable (fun x => Hψ x * Gψ x) π := MemLp.integrable_mul (p := 2) (q := 2) hHψ2 hGψ2
  have i3 : Integrable (fun x => Hψ x * Gφ x) π := MemLp.integrable_mul (p := 2) (q := 2) hHψ2 hGφ2
  have i4 : Integrable (fun x => (Hφ x - Hψ x) * Gφ x) π :=
    MemLp.integrable_mul (p := 2) (q := 2) (hHφ2.sub hHψ2) hGφ2
  have i5 : Integrable (fun x => Hψ x * (Gφ x - Gψ x)) π :=
    MemLp.integrable_mul (p := 2) (q := 2) hHψ2 (hGφ2.sub hGψ2)
  rw [e1, e2, e3, e4]
  have s1 : ∫ x, (Hφ x - Hψ x) * Gφ x ∂π
      = (∫ x, Hφ x * Gφ x ∂π) - ∫ x, Hψ x * Gφ x ∂π := by
    rw [← integral_sub i1 i3]
    exact integral_congr_ae (Filter.Eventually.of_forall fun x => by ring)
  have s2 : ∫ x, Hψ x * (Gφ x - Gψ x) ∂π
      = (∫ x, Hψ x * Gφ x ∂π) - ∫ x, Hψ x * Gψ x ∂π := by
    rw [← integral_sub i3 i2]
    exact integral_congr_ae (Filter.Eventually.of_forall fun x => by ring)
  rw [s1, s2]; ring

/-- **The asymptotic variance is `L²(π)`-continuous**, with an explicit modulus. -/
lemma abs_asymptoticVariance_sub_le (P : Kernel X X) [IsMarkovKernel P] (π : Measure X)
    [IsProbabilityMeasure π] (hinv : Kernel.Invariant P π) (N : ℕ) (hN : 1 ≤ N)
    (hrate : ∀ x, tvDist (iterKernel P N x) π ≤ 1 / 16)
    (φ ψ : X → ℝ) (hφ : Measurable φ) (hψ : Measurable ψ)
    (hφ2 : MemLp φ 2 π) (hψ2 : MemLp ψ 2 π) :
    |asymptoticVariance P π φ - asymptoticVariance P π ψ|
      ≤ (l2NormAux π (fun x => φ x - ∫ y, φ y ∂π)
          + l2NormAux π (fun x => ψ x - ∫ y, ψ y ∂π))
        * l2NormAux π (fun x => (φ x - ψ x) - ∫ y, (φ y - ψ y) ∂π)
        * (1 + 2 * ∑' k : ℕ, (1 / 2 : ℝ) ^ (k / N)) := by
  classical
  set D : X → ℝ := fun x => φ x - ψ x with hD
  have hDm : Measurable D := hφ.sub hψ
  have hD2 : MemLp D 2 π := hφ2.sub hψ2
  set Lφ := l2NormAux π (fun x => φ x - ∫ y, φ y ∂π) with hLφ
  set Lψ := l2NormAux π (fun x => ψ x - ∫ y, ψ y ∂π) with hLψ
  set LD := l2NormAux π (fun x => D x - ∫ y, D y ∂π) with hLD
  have hLφ0 : 0 ≤ Lφ := l2NormAux_nonneg _ _
  have hLψ0 : 0 ≤ Lψ := l2NormAux_nonneg _ _
  have hLD0 : 0 ≤ LD := l2NormAux_nonneg _ _
  set M := (Lφ + Lψ) * LD with hM
  have hM0 : 0 ≤ M := mul_nonneg (by linarith) hLD0
  -- pointwise bound on the difference of the diagonal lagged covariances
  have hdiff : ∀ k : ℕ, |lagCovariance P π φ φ k - lagCovariance P π ψ ψ k|
      ≤ M * (1 / 2 : ℝ) ^ (k / N) := by
    intro k
    rw [lagCovariance_diag_sub P π hinv φ ψ hφ hψ hφ2 hψ2 k]
    refine le_trans (abs_add_le _ _) ?_
    have b1 := abs_lagCovariance_le_bilin P π hinv N hN hrate D φ hDm hφ hD2 hφ2 k
    have b2 := abs_lagCovariance_le_bilin P π hinv N hN hrate ψ D hψ hDm hψ2 hD2 k
    have hp0 : (0:ℝ) ≤ (1 / 2 : ℝ) ^ (k / N) := by positivity
    calc |lagCovariance P π D φ k| + |lagCovariance P π ψ D k|
        ≤ LD * Lφ * (1 / 2 : ℝ) ^ (k / N) + Lψ * LD * (1 / 2 : ℝ) ^ (k / N) :=
          add_le_add b1 b2
      _ = M * (1 / 2 : ℝ) ^ (k / N) := by rw [hM]; ring
  -- summability
  have hsumφ := summable_lagCovariance_succ P π hinv N hN hrate φ φ hφ hφ hφ2 hφ2
  have hsumψ := summable_lagCovariance_succ P π hinv N hN hrate ψ ψ hψ hψ hψ2 hψ2
  have hgeo := summable_half_pow_div N hN
  have hSnn : 0 ≤ ∑' k : ℕ, (1 / 2 : ℝ) ^ (k / N) :=
    tsum_nonneg fun k => by positivity
  have hbnd : ∀ k : ℕ, ‖lagCovariance P π φ φ (k + 1) - lagCovariance P π ψ ψ (k + 1)‖
      ≤ M * (1 / 2 : ℝ) ^ (k / N) := by
    intro k
    rw [Real.norm_eq_abs]
    refine le_trans (hdiff (k + 1)) ?_
    have hle : k / N ≤ (k + 1) / N := Nat.div_le_div_right (by omega)
    have hp : (1 / 2 : ℝ) ^ ((k + 1) / N) ≤ (1 / 2 : ℝ) ^ (k / N) :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) hle
    nlinarith [hM0, hp]
  have hsumabs : Summable (fun k : ℕ =>
      ‖lagCovariance P π φ φ (k + 1) - lagCovariance P π ψ ψ (k + 1)‖) :=
    Summable.of_nonneg_of_le (fun k => norm_nonneg _) hbnd (hgeo.mul_left M)
  have htail : |(∑' k : ℕ, lagCovariance P π φ φ (k + 1))
      - ∑' k : ℕ, lagCovariance P π ψ ψ (k + 1)|
      ≤ M * ∑' k : ℕ, (1 / 2 : ℝ) ^ (k / N) := by
    rw [← Summable.tsum_sub hsumφ hsumψ]
    refine le_trans (by simpa using norm_tsum_le_tsum_norm hsumabs) ?_
    rw [← hgeo.tsum_mul_left M]
    exact hsumabs.tsum_le_tsum hbnd (hgeo.mul_left M)
  have hzero : |lagCovariance P π φ φ 0 - lagCovariance P π ψ ψ 0| ≤ M := by
    have := hdiff 0
    simpa using this
  -- assemble
  have hexp : asymptoticVariance P π φ - asymptoticVariance P π ψ
      = (lagCovariance P π φ φ 0 - lagCovariance P π ψ ψ 0)
        + 2 * ((∑' k : ℕ, lagCovariance P π φ φ (k + 1))
              - ∑' k : ℕ, lagCovariance P π ψ ψ (k + 1)) := by
    simp only [asymptoticVariance, asymptoticCovariance]
    ring
  rw [hexp]
  refine le_trans (abs_add_le _ _) ?_
  rw [abs_mul, abs_two]
  have : M + 2 * (M * ∑' k : ℕ, (1 / 2 : ℝ) ^ (k / N))
      = M * (1 + 2 * ∑' k : ℕ, (1 / 2 : ℝ) ^ (k / N)) := by ring
  calc |lagCovariance P π φ φ 0 - lagCovariance P π ψ ψ 0|
        + 2 * |(∑' k : ℕ, lagCovariance P π φ φ (k + 1))
              - ∑' k : ℕ, lagCovariance P π ψ ψ (k + 1)|
      ≤ M + 2 * (M * ∑' k : ℕ, (1 / 2 : ℝ) ^ (k / N)) := by
        exact add_le_add hzero (by linarith [htail])
    _ = M * (1 + 2 * ∑' k : ℕ, (1 / 2 : ℝ) ^ (k / N)) := this


/-! ### The scaled variance converges to the autocovariance series -/

lemma sq_scaled_eq (π : Measure X) (f : X → ℝ) (n : ℕ) (ω : ℕ → X) :
    (Real.sqrt n * (sampleAvg f n ω - ∫ x, f x ∂π)) ^ 2
      = (n:ℝ)⁻¹ * (∑ i ∈ Finset.range n, (f (ω (i + 1)) - ∫ x, f x ∂π)) ^ 2 := by
  set c := ∫ x, f x ∂π with hc
  have hsum : ∑ i ∈ Finset.range n, (f (ω (i + 1)) - c)
      = (∑ i ∈ Finset.range n, f (ω (i + 1))) - (n:ℝ) * c := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · have hn0 : (n:ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
    have hsq : (Real.sqrt n) ^ 2 = (n:ℝ) := Real.sq_sqrt (Nat.cast_nonneg n)
    rw [hsum, sampleAvg, mul_pow, hsq]
    field_simp

lemma integrable_prod_coord (P : Kernel X X) [IsMarkovKernel P] (π : Measure X)
    [IsProbabilityMeasure π] (h : X → ℝ) (hh : Measurable h) (Bh : ℝ)
    (hBh : ∀ x, |h x| ≤ Bh) (i j : ℕ) :
    Integrable (fun ω : ℕ → X => h (ω (i + 1)) * h (ω (j + 1))) (chainMeasure P π) := by
  refine Integrable.mono' (integrable_const (Bh * Bh)) ?_ ?_
  · exact ((hh.comp (measurable_pi_apply (i + 1))).mul
      (hh.comp (measurable_pi_apply (j + 1)))).aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun ω => ?_
    rw [Real.norm_eq_abs, abs_mul]
    have h0 : (0:ℝ) ≤ Bh := le_trans (abs_nonneg _) (hBh (ω (i + 1)))
    exact mul_le_mul (hBh _) (hBh _) (abs_nonneg _) h0

lemma integral_sq_sum_coord_eq_double (P : Kernel X X) [IsMarkovKernel P] (π : Measure X)
    [IsProbabilityMeasure π] (h : X → ℝ) (hh : Measurable h) (Bh : ℝ)
    (hBh : ∀ x, |h x| ≤ Bh) (n : ℕ) :
    ∫ ω, (∑ i ∈ Finset.range n, h (ω (i + 1))) ^ 2 ∂(chainMeasure P π)
      = ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n,
          ∫ ω, h (ω (i + 1)) * h (ω (j + 1)) ∂(chainMeasure P π) := by
  have hpt : ∀ ω : ℕ → X, (∑ i ∈ Finset.range n, h (ω (i + 1))) ^ 2
      = ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n, h (ω (i + 1)) * h (ω (j + 1)) := by
    intro ω; rw [sq, Finset.sum_mul_sum]
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt)]
  rw [integral_finset_sum _ (fun i _ => integrable_finset_sum _
    (fun j _ => integrable_prod_coord P π h hh Bh hBh i j))]
  exact Finset.sum_congr rfl fun i _ =>
    integral_finset_sum _ (fun j _ => integrable_prod_coord P π h hh Bh hBh i j)

/-- The chain covariance of two coordinates depends only on the lag. -/
lemma integral_prod_coord_eq_lagCovariance (P : Kernel X X) [IsMarkovKernel P] (π : Measure X)
    [IsProbabilityMeasure π] (hinv : Kernel.Invariant P π) (f : X → ℝ) (hf : Measurable f)
    (B : ℝ) (hB : ∀ x, |f x| ≤ B) (i j : ℕ) :
    ∫ ω, (f (ω (i + 1)) - ∫ x, f x ∂π) * (f (ω (j + 1)) - ∫ x, f x ∂π) ∂(chainMeasure P π)
      = lagCovariance P π f f (max i j - min i j) := by
  set c := ∫ x, f x ∂π with hc
  set h : X → ℝ := fun x => f x - c with hhdef
  have hhm : Measurable h := hf.sub measurable_const
  have hfi : Integrable f π := by
    refine Integrable.mono' (integrable_const B) hf.aestronglyMeasurable ?_
    exact Filter.Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hB x
  have hcabs : |c| ≤ B := by
    rw [hc]
    refine le_trans (abs_integral_le_integral_abs) ?_
    refine le_trans (integral_mono hfi.abs (integrable_const B)
      (fun x => hB x)) ?_
    simp
  have hhB : ∀ x, |h x| ≤ 2 * B := by
    intro x
    calc |h x| = |f x - c| := rfl
      _ ≤ |f x| + |c| := abs_sub _ _
      _ ≤ 2 * B := by linarith [hB x, hcabs]
  have hlag : ∀ d : ℕ, ∫ x, h x * (∫ y, h y ∂(iterKernel P d x)) ∂π
      = lagCovariance P π f f d := fun d =>
    (lagCovariance_eq_centred P π hinv f f hf hfi d).symm
  rcases le_total i j with hij | hij
  · have hd : i + 1 + (j - i) = j + 1 := by omega
    have hmax : max i j - min i j = j - i := by
      rw [max_eq_right hij, min_eq_left hij]
    rw [hmax, ← hlag (j - i)]
    have := integral_mul_coord_eq P π hinv h hhm (2 * B) hhB i (j - i)
    rw [hd] at this
    exact this
  · have hd : j + 1 + (i - j) = i + 1 := by omega
    have hmax : max i j - min i j = i - j := by
      rw [max_eq_left hij, min_eq_right hij]
    rw [hmax, ← hlag (i - j)]
    have := integral_mul_coord_eq P π hinv h hhm (2 * B) hhB j (i - j)
    rw [hd] at this
    rw [← this]
    exact integral_congr_ae (Filter.Eventually.of_forall fun ω => mul_comm _ _)

lemma sum_lag_row (c : ℕ → ℝ) (n i : ℕ) (hi : i < n) :
    ∑ j ∈ Finset.range n, c (max i j - min i j)
      = (∑ d ∈ Finset.range (i + 1), c d)
        + ((∑ d ∈ Finset.range (n - i), c d) - c 0) := by
  have hsplit : (∑ j ∈ Finset.range (i + 1), c (max i j - min i j))
      + (∑ j ∈ Finset.Ico (i + 1) n, c (max i j - min i j))
      = ∑ j ∈ Finset.range n, c (max i j - min i j) :=
    Finset.sum_range_add_sum_Ico _ (by omega)
  have hlow : (∑ j ∈ Finset.range (i + 1), c (max i j - min i j))
      = ∑ d ∈ Finset.range (i + 1), c d := by
    have hterm : ∀ j ∈ Finset.range (i + 1), c (max i j - min i j) = c (i - j) := by
      intro j hj
      rw [Finset.mem_range] at hj
      rw [max_eq_left (by omega), min_eq_right (by omega)]
    rw [Finset.sum_congr rfl hterm]
    have := Finset.sum_range_reflect (fun j => c j) (i + 1)
    simpa using this
  have hhigh : (∑ j ∈ Finset.Ico (i + 1) n, c (max i j - min i j))
      = (∑ d ∈ Finset.range (n - i), c d) - c 0 := by
    have hterm : ∀ j ∈ Finset.Ico (i + 1) n, c (max i j - min i j) = c (j - i) := by
      intro j hj
      rw [Finset.mem_Ico] at hj
      rw [max_eq_right (by omega), min_eq_left (by omega)]
    rw [Finset.sum_congr rfl hterm, Finset.sum_Ico_eq_sum_range]
    have hidx : ∀ d ∈ Finset.range (n - (i + 1)), c (i + 1 + d - i) = c (d + 1) := by
      intro d _
      congr 1
      omega
    rw [Finset.sum_congr rfl hidx]
    have hni : n - i = (n - (i + 1)) + 1 := by omega
    rw [hni, Finset.sum_range_succ']
    ring
  rw [← hsplit, hlow, hhigh]

lemma sum_lag_double (c : ℕ → ℝ) (n : ℕ) (hn : 1 ≤ n) :
    ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n, c (max i j - min i j)
      = 2 * (∑ i ∈ Finset.range n, ∑ d ∈ Finset.range (i + 1), c d) - (n : ℝ) * c 0 := by
  have hrow : ∀ i ∈ Finset.range n, (∑ j ∈ Finset.range n, c (max i j - min i j))
      = (∑ d ∈ Finset.range (i + 1), c d)
        + ((∑ d ∈ Finset.range (n - i), c d) - c 0) := by
    intro i hi
    exact sum_lag_row c n i (Finset.mem_range.1 hi)
  rw [Finset.sum_congr rfl hrow]
  have hrefl : (∑ i ∈ Finset.range n, ∑ d ∈ Finset.range (n - i), c d)
      = ∑ i ∈ Finset.range n, ∑ d ∈ Finset.range (i + 1), c d := by
    rw [← Finset.sum_range_reflect (fun i => ∑ d ∈ Finset.range (i + 1), c d) n]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [Finset.mem_range] at hi
    have hidx : n - i = (n - 1 - i) + 1 := by omega
    rw [hidx]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, hrefl, Finset.sum_const,
    Finset.card_range, nsmul_eq_mul]
  ring

/-- **The CLT-scaled variance converges to the autocovariance series.** -/
theorem tendsto_integral_sq_scaled_sampleAvg (P : Kernel X X) [IsMarkovKernel P]
    (π : Measure X) [IsProbabilityMeasure π] (hinv : Kernel.Invariant P π)
    (huni : UniformlyErgodic P π) (f : X → ℝ) (hf : Measurable f) (B : ℝ)
    (hB : ∀ x, |f x| ≤ B) :
    Filter.Tendsto
      (fun n : ℕ => ∫ ω, (Real.sqrt n * (sampleAvg f n ω - ∫ x, f x ∂π)) ^ 2
        ∂(chainMeasure P π)) atTop (𝓝 (asymptoticVariance P π f)) := by
  classical
  obtain ⟨N, hN, hrate⟩ := exists_lag_tvDist_le_of_uniformlyErgodic P π huni
  set c : ℕ → ℝ := fun d => lagCovariance P π f f d with hcdef
  have hfi : Integrable f π := by
    refine Integrable.mono' (integrable_const B) hf.aestronglyMeasurable ?_
    exact Filter.Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hB x
  have hfL2 : MemLp f 2 π :=
    MemLp.of_bound hf.aestronglyMeasurable B
      (Filter.Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hB x)
  have hcabs : |∫ x, f x ∂π| ≤ B := by
    refine le_trans (abs_integral_le_integral_abs) ?_
    refine le_trans (integral_mono hfi.abs (integrable_const B) (fun x => hB x)) ?_
    simp
  set h : X → ℝ := fun x => f x - ∫ x, f x ∂π with hhdef
  have hhm : Measurable h := hf.sub measurable_const
  have hhB : ∀ x, |h x| ≤ 2 * B := by
    intro x
    calc |h x| = |f x - ∫ y, f y ∂π| := rfl
      _ ≤ |f x| + |∫ y, f y ∂π| := abs_sub _ _
      _ ≤ 2 * B := by linarith [hB x, hcabs]
  -- summability of the autocovariances
  have hsucc := summable_lagCovariance_succ P π hinv N hN hrate f f hf hf hfL2 hfL2
  have hsum : Summable c := (summable_nat_add_iff 1).1 (by simpa using hsucc)
  -- the scaled variance is the Cesàro average of the partial sums
  have hval : ∀ n : ℕ, 1 ≤ n →
      ∫ ω, (Real.sqrt n * (sampleAvg f n ω - ∫ x, f x ∂π)) ^ 2 ∂(chainMeasure P π)
        = 2 * ((n:ℝ)⁻¹ * ∑ i ∈ Finset.range n, ∑ d ∈ Finset.range (i + 1), c d) - c 0 := by
    intro n hn
    have hn0 : (n:ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
    rw [integral_congr_ae (Filter.Eventually.of_forall fun ω => sq_scaled_eq π f n ω)]
    rw [integral_const_mul]
    rw [integral_sq_sum_coord_eq_double P π h hhm (2 * B) hhB n]
    have hentry : ∀ i ∈ Finset.range n, (∑ j ∈ Finset.range n,
        ∫ ω, h (ω (i + 1)) * h (ω (j + 1)) ∂(chainMeasure P π))
        = ∑ j ∈ Finset.range n, c (max i j - min i j) := by
      intro i _
      exact Finset.sum_congr rfl fun j _ =>
        integral_prod_coord_eq_lagCovariance P π hinv f hf B hB i j
    rw [Finset.sum_congr rfl hentry, sum_lag_double c n hn]
    field_simp
  -- Cesàro
  have hpart : Filter.Tendsto (fun i : ℕ => ∑ d ∈ Finset.range (i + 1), c d) atTop
      (𝓝 (∑' d, c d)) :=
    (hsum.hasSum.tendsto_sum_nat).comp (Filter.tendsto_add_atTop_nat 1)
  have hces := hpart.cesaro
  have hlim : Filter.Tendsto
      (fun n : ℕ => 2 * ((n:ℝ)⁻¹ * ∑ i ∈ Finset.range n, ∑ d ∈ Finset.range (i + 1), c d) - c 0)
      atTop (𝓝 (2 * (∑' d, c d) - c 0)) := (hces.const_mul 2).sub_const _
  have hsig : asymptoticVariance P π f = 2 * (∑' d, c d) - c 0 := by
    have hz : (∑' d, c d) = c 0 + ∑' k, c (k + 1) := hsum.tsum_eq_zero_add
    simp only [asymptoticVariance, asymptoticCovariance, ← hcdef]
    rw [hz]; ring
  rw [hsig]
  refine hlim.congr' ?_
  filter_upwards [Filter.eventually_ge_atTop 1] with n hn
  exact (hval n hn).symm

/-! ### Uniform square-integrability and the identification of the limit variance -/

/-- `z ↦ min (z², T²)`, as a bounded continuous function. -/
noncomputable def truncSq (T : ℝ) : BoundedContinuousFunction ℝ ℝ :=
  BoundedContinuousFunction.mkOfBound
    ⟨fun z => min (z ^ 2) (T ^ 2), (continuous_pow 2).min continuous_const⟩
    (T ^ 2) (by
      intro x y
      have h1 : ∀ z : ℝ, 0 ≤ min (z ^ 2) (T ^ 2) := fun z => le_min (sq_nonneg _) (sq_nonneg _)
      have h2 : ∀ z : ℝ, min (z ^ 2) (T ^ 2) ≤ T ^ 2 := fun z => min_le_right _ _
      show dist (min (x ^ 2) (T ^ 2)) (min (y ^ 2) (T ^ 2)) ≤ T ^ 2
      rw [Real.dist_eq, abs_le]
      exact ⟨by linarith [h1 x, h2 y], by linarith [h1 y, h2 x]⟩)

@[simp] lemma truncSq_apply (T z : ℝ) : truncSq T z = min (z ^ 2) (T ^ 2) := rfl

lemma sub_truncSq_le (T : ℝ) (hT : 0 < T) (z : ℝ) :
    z ^ 2 - min (z ^ 2) (T ^ 2) ≤ z ^ 4 / T ^ 2 := by
  have hT2 : (0:ℝ) < T ^ 2 := by positivity
  rcases le_total (z ^ 2) (T ^ 2) with h | h
  · rw [min_eq_left h]
    simp only [sub_self]
    positivity
  · rw [min_eq_right h, le_div_iff₀ hT2]
    nlinarith [sq_nonneg z, sq_nonneg (z ^ 2)]

/-- The second moment of a centred real Gaussian is its variance parameter. -/
lemma integral_sq_gaussianReal (v : ℝ≥0) :
    ∫ z, z ^ 2 ∂(gaussianReal 0 v) = (v : ℝ) := by
  have hmem : MemLp (id : ℝ → ℝ) 2 (gaussianReal 0 v) := memLp_id_gaussianReal 2
  have hvar := ProbabilityTheory.variance_id_gaussianReal (μ := 0) (v := v)
  rw [ProbabilityTheory.variance_eq_sub hmem] at hvar
  simp only [Pi.pow_apply, id_eq, integral_id_gaussianReal] at hvar
  simpa using hvar

lemma tendsto_integral_truncSq_gaussian (v : ℝ≥0) :
    Filter.Tendsto (fun m : ℕ => ∫ z, min (z ^ 2) ((m:ℝ) ^ 2) ∂(gaussianReal 0 v))
      atTop (𝓝 ((v : ℝ))) := by
  have hmem : MemLp (id : ℝ → ℝ) 2 (gaussianReal 0 v) := memLp_id_gaussianReal 2
  have hsq : Integrable (fun z : ℝ => z ^ 2) (gaussianReal 0 v) := by
    have := (memLp_two_iff_integrable_sq (by fun_prop)).1 hmem
    simpa using this
  have hlim := tendsto_integral_of_dominated_convergence
    (F := fun (m : ℕ) (z : ℝ) => min (z ^ 2) ((m:ℝ) ^ 2)) (f := fun z : ℝ => z ^ 2)
    (bound := fun z : ℝ => z ^ 2) (μ := gaussianReal 0 v)
    (fun m => ((continuous_pow 2).min continuous_const).aestronglyMeasurable) hsq
    (fun m => Filter.Eventually.of_forall fun z => by
      rw [Real.norm_eq_abs, abs_of_nonneg (le_min (sq_nonneg _) (sq_nonneg _))]
      exact min_le_left _ _)
    (Filter.Eventually.of_forall fun z => by
      refine tendsto_atTop_of_eventually_const (i₀ := ⌈|z|⌉₊) fun m hm => ?_
      have h1 : |z| ≤ (m : ℝ) := le_trans (Nat.le_ceil _) (by exact_mod_cast hm)
      have h2 : z ^ 2 ≤ (m:ℝ) ^ 2 := by nlinarith [abs_nonneg z, sq_abs z]
      exact min_eq_left h2)
  rw [integral_sq_gaussianReal] at hlim
  exact hlim

lemma measurable_sampleAvg (f : X → ℝ) (hf : Measurable f) (n : ℕ) :
    Measurable (fun ω : ℕ → X => sampleAvg f n ω) := by
  unfold sampleAvg
  exact (Finset.measurable_sum _ fun i _ => hf.comp (measurable_pi_apply (i + 1))).const_mul _

/-- **Identification of the CLT limit variance for a bounded observable.** -/
theorem asymptoticVariance_eq_of_clt_bdd (P : Kernel X X) [IsMarkovKernel P] (π : Measure X)
    [IsProbabilityMeasure π] (hP : HarrisErgodic P π) (huni : UniformlyErgodic P π)
    (f : X → ℝ) (hf : Measurable f) (B : ℝ) (hB : ∀ x, |f x| ≤ B) (v : ℝ≥0)
    (hclt : TendstoInDistribution
      (fun (n : ℕ) (ω : ℕ → X) => Real.sqrt n * (sampleAvg f n ω - ∫ x, f x ∂π))
      atTop (id : ℝ → ℝ) (fun _ => chainMeasure P π) (gaussianReal 0 v)) :
    (v : ℝ) = asymptoticVariance P π f := by
  classical
  have hinv : Kernel.Invariant P π := hP.1
  obtain ⟨C, hC0, hC⟩ := integral_pow_four_scaled_sampleAvg_le P π hinv huni f hf B hB
  set μc := chainMeasure P π with hμc
  set Y : ℕ → (ℕ → X) → ℝ :=
    fun n ω => Real.sqrt n * (sampleAvg f n ω - ∫ x, f x ∂π) with hY
  set σ2 := asymptoticVariance P π f with hσ2
  have hYmeas : ∀ n, Measurable (Y n) := fun n =>
    ((measurable_sampleAvg f hf n).sub measurable_const).const_mul _
  have hfsq : Integrable (fun x => (f x) ^ 2) π := by
    refine Integrable.mono' (integrable_const (B * B)) ((hf.pow_const 2).aestronglyMeasurable) ?_
    refine Filter.Eventually.of_forall fun x => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), sq]
    have h0 : (0:ℝ) ≤ B := le_trans (abs_nonneg _) (hB x)
    have := hB x
    nlinarith [abs_nonneg (f x), sq_abs (f x)]
  have hYsq : ∀ n, Integrable (fun ω => (Y n ω) ^ 2) μc := fun n =>
    integrable_sq_scaled_sampleAvg P π hinv f hf hfsq n
  have hmom : Filter.Tendsto (fun n => ∫ ω, (Y n ω) ^ 2 ∂μc) atTop (𝓝 σ2) :=
    tendsto_integral_sq_scaled_sampleAvg P π hinv huni f hf B hB
  have hmin : ∀ (n : ℕ) (T : ℝ), Integrable (fun ω => min ((Y n ω) ^ 2) (T ^ 2)) μc := by
    intro n T
    refine Integrable.mono' (integrable_const (T ^ 2))
      (((hYmeas n).pow_const 2).min measurable_const).aestronglyMeasurable ?_
    refine Filter.Eventually.of_forall fun ω => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (le_min (sq_nonneg _) (sq_nonneg _))]
    exact min_le_right _ _
  -- portmanteau for the truncated square
  have hport : ∀ T : ℝ, Filter.Tendsto (fun n => ∫ ω, min ((Y n ω) ^ 2) (T ^ 2) ∂μc) atTop
      (𝓝 (∫ z, min (z ^ 2) (T ^ 2) ∂(gaussianReal 0 v))) := by
    intro T
    have h := (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto).1 hclt.tendsto (truncSq T)
    have h2 : Filter.Tendsto (fun n : ℕ => ∫ z, truncSq T z ∂(Measure.map (Y n) μc)) atTop
        (𝓝 (∫ z, truncSq T z ∂(Measure.map (id : ℝ → ℝ) (gaussianReal 0 v)))) := h
    rw [Measure.map_id] at h2
    refine Filter.Tendsto.congr (fun n => ?_) h2
    rw [integral_map (hYmeas n).aemeasurable ((truncSq T).continuous.aestronglyMeasurable)]
    rfl
  -- the two inequalities
  have hAle : ∀ T : ℝ, ∫ z, min (z ^ 2) (T ^ 2) ∂(gaussianReal 0 v) ≤ σ2 := by
    intro T
    refine le_of_tendsto_of_tendsto' (hport T) hmom fun n => ?_
    exact integral_mono (hmin n T) (hYsq n) (fun ω => min_le_left _ _)
  have hBge : ∀ T : ℝ, 0 < T →
      σ2 ≤ ∫ z, min (z ^ 2) (T ^ 2) ∂(gaussianReal 0 v) + C / T ^ 2 := by
    intro T hT
    have hT2 : (0:ℝ) < T ^ 2 := by positivity
    refine le_of_tendsto_of_tendsto' hmom ((hport T).add_const (C / T ^ 2)) fun n => ?_
    have h4 := hC n
    have hsum : Integrable (fun ω => min ((Y n ω) ^ 2) (T ^ 2) + (Y n ω) ^ 4 / T ^ 2) μc :=
      (hmin n T).fun_add (h4.1.div_const _)
    have hstep : ∫ ω, (Y n ω) ^ 2 ∂μc
        ≤ ∫ ω, (min ((Y n ω) ^ 2) (T ^ 2) + (Y n ω) ^ 4 / T ^ 2) ∂μc := by
      refine integral_mono (hYsq n) hsum fun ω => ?_
      linarith [sub_truncSq_le T hT (Y n ω)]
    have hsplit : ∫ ω, (min ((Y n ω) ^ 2) (T ^ 2) + (Y n ω) ^ 4 / T ^ 2) ∂μc
        = (∫ ω, min ((Y n ω) ^ 2) (T ^ 2) ∂μc) + (∫ ω, (Y n ω) ^ 4 ∂μc) / T ^ 2 := by
      rw [integral_add (hmin n T) (h4.1.div_const _), integral_div]
    rw [hsplit] at hstep
    have hdiv : (∫ ω, (Y n ω) ^ 4 ∂μc) / T ^ 2 ≤ C / T ^ 2 := by gcongr; exact h4.2
    linarith
  -- let T → ∞
  have hgauss := tendsto_integral_truncSq_gaussian v
  have hv1 : (v : ℝ) ≤ σ2 :=
    le_of_tendsto hgauss (Filter.Eventually.of_forall fun m => hAle (m : ℝ))
  have hCm : Filter.Tendsto (fun m : ℕ => C / ((m:ℝ) ^ 2)) atTop (𝓝 0) := by
    have hsq : Filter.Tendsto (fun m : ℕ => ((m:ℝ) ^ 2)) atTop atTop :=
      (tendsto_pow_atTop (by norm_num)).comp tendsto_natCast_atTop_atTop
    exact hsq.const_div_atTop C
  have hv2 : σ2 ≤ (v : ℝ) := by
    have hlim : Filter.Tendsto
        (fun m : ℕ => (∫ z, min (z ^ 2) ((m:ℝ) ^ 2) ∂(gaussianReal 0 v)) + C / ((m:ℝ) ^ 2))
        atTop (𝓝 ((v : ℝ) + 0)) := hgauss.add hCm
    rw [add_zero] at hlim
    refine ge_of_tendsto hlim ?_
    filter_upwards [Filter.eventually_gt_atTop 0] with m hm
    exact hBge (m : ℝ) (by exact_mod_cast hm)
  linarith

end MarkovChainCLT

theorem solution {X : Type*} [MeasurableSpace X]
    (P : Kernel X X) [IsMarkovKernel P] (π : Measure X) [IsProbabilityMeasure π]
    (hP : MarkovChainCLT.HarrisErgodic P π)
    (huni : MarkovChainCLT.UniformlyErgodic P π)
    (f : X → ℝ) (hf : Measurable f) (B : ℝ) (hB : ∀ x, |f x| ≤ B) (v : ℝ≥0)
    (hclt : TendstoInDistribution
      (fun (n : ℕ) (ω : ℕ → X) =>
        Real.sqrt n * (MarkovChainCLT.sampleAvg f n ω - ∫ x, f x ∂π))
      atTop (id : ℝ → ℝ) (fun _ => MarkovChainCLT.chainMeasure P π)
      (gaussianReal 0 v)) :
    (v : ℝ) = MarkovChainCLT.asymptoticVariance P π f :=
  MarkovChainCLT.asymptoticVariance_eq_of_clt_bdd P π hP huni f hf B hB v hclt
