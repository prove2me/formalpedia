-- Prove2me | solution 2 for MarkovChainCLT.asymptoticVariance_eq_of_clt_of_bounded
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-08-21T22:26:26.977407+00:00
-- url     : https://prove2.me/submissions/738a42b6-34ca-4c65-8a0a-d662d9478263

import Definitions.Def_MarkovAsymptoticVariance
import Definitions.Def_MarkovErgodicity
import Definitions.Def_MarkovChainPathMeasure
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.Probability.Moments.Variance
import Mathlib.Probability.Martingale.Basic
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Theorems.Thm_MarkovChainCLT_integral_sq_iterKernel_pow_le
import Theorems.Thm_MarkovChainCLT_exists_lag_tvDist_le_of_uniformlyErgodic
import Theorems.Thm_Martingale_clt_of_bounded_mds_array
import Theorems.Thm_MarkovChainCLT_poissonEquation_of_bounded_of_uniformlyErgodic
import Theorems.Thm_MarkovChainCLT_condExp_next_coord
import Theorems.Thm_MarkovChainCLT_integral_sq_sum_mds_le
import Theorems.Thm_MarkovChainCLT_integral_sq_sampleAvg_sub_le
import Theorems.Thm_MarkovChainCLT_abs_exp_variance_sub_le_of_tendstoInDistribution

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

lemma abs_mul_le_quad (t a b : ℝ) (ht : 0 < t) : |a * b| ≤ t * a ^ 2 + b ^ 2 / (4 * t) := by
  have h4t : (0:ℝ) < 4 * t := by linarith
  have e1 : t * a ^ 2 + b ^ 2 / (4 * t) - a * b = (2 * t * a - b) ^ 2 / (4 * t) := by
    field_simp; ring
  have e2 : t * a ^ 2 + b ^ 2 / (4 * t) + a * b = (2 * t * a + b) ^ 2 / (4 * t) := by
    field_simp; ring
  have p1 : 0 ≤ (2 * t * a - b) ^ 2 / (4 * t) := by positivity
  have p2 : 0 ≤ (2 * t * a + b) ^ 2 / (4 * t) := by positivity
  rw [abs_le]
  constructor <;> linarith

/-- **Geometric decay of the autocovariances of a uniformly ergodic `L²` observable.** -/
lemma abs_lagCovariance_le_geom (P : Kernel X X) [IsMarkovKernel P] (π : Measure X)
    [IsProbabilityMeasure π] (hinv : Kernel.Invariant P π)
    (huni : UniformlyErgodic P π) (f : X → ℝ) (hf : Measurable f) (hL2 : MemLp f 2 π) :
    ∃ (C : ℝ) (N : ℕ), 0 ≤ C ∧ 1 ≤ N ∧
      ∀ k : ℕ, |lagCovariance P π f f k| ≤ C * (1 / 2 : ℝ) ^ (k / N) := by
  obtain ⟨N, hN, hrate⟩ := exists_lag_tvDist_le_of_uniformlyErgodic P π huni
  set c : ℝ := ∫ y, f y ∂π with hc
  set h : X → ℝ := fun x => f x - c with hhdef
  have hh : Measurable h := hf.sub measurable_const
  have hhL2 : MemLp h 2 π := hL2.sub (memLp_const c)
  have hhsq : Integrable (fun x => (h x) ^ 2) π :=
    (memLp_two_iff_integrable_sq hh.aestronglyMeasurable).1 hhL2
  have hfint : Integrable f π := hL2.integrable (by norm_num)
  have hmean : ∫ x, h x ∂π = 0 := by
    rw [hhdef]
    rw [integral_sub hfint (integrable_const c), integral_const]
    simp [hc]
  set V : ℝ := ∫ x, (h x) ^ 2 ∂π with hV
  have hV0 : 0 ≤ V := integral_nonneg fun x => sq_nonneg _
  refine ⟨5 / 4 * V, N, by positivity, hN, fun k => ?_⟩
  set G : X → ℝ := fun x => ∫ y, h y ∂(iterKernel P k x) with hG
  have hGmeas : Measurable G :=
    (StronglyMeasurable.integral_kernel (κ := iterKernel P k) hh.stronglyMeasurable).measurable
  have hGb := iterMean_bound P π hinv k h hh hhsq
  have hGdecay := integral_sq_iterKernel_geom_decay P π hinv N hN (1 / 16) (by norm_num)
    (by norm_num) hrate h hh hhsq hmean k
  -- rewrite the lagged covariance in terms of the centred observable
  have hinvk : Kernel.Invariant (iterKernel P k) π := invariant_iterKernel P π hinv k
  have hfc : Integrable f ((iterKernel P k) ∘ₘ π) := by
    rw [show ((iterKernel P k) ∘ₘ π) = π from hinvk]; exact hfint
  have hsplit := (Measure.integrable_comp_iff (κ := iterKernel P k) (μ := π)
    (f := f) hf.aestronglyMeasurable).1 hfc
  have hlag : lagCovariance P π f f k = ∫ x, h x * G x ∂π := by
    unfold lagCovariance
    refine integral_congr_ae ?_
    filter_upwards [hsplit.1] with x hx
    have : ∫ y, h y ∂((iterKernel P k) x) = (∫ y, f y ∂((iterKernel P k) x)) - c := by
      rw [hhdef]
      rw [integral_sub hx (integrable_const c), integral_const]
      simp
    rw [hG]
    simp only
    rw [this]
  rw [hlag]
  set t : ℝ := (1 / 2 : ℝ) ^ (k / N) with ht
  have ht0 : 0 < t := by positivity
  have hprod : Integrable (fun x => h x * G x) π := by
    have hGL2 : MemLp G 2 π :=
      (memLp_two_iff_integrable_sq hGmeas.aestronglyMeasurable).2 hGb.1
    exact MemLp.integrable_mul (p := 2) (q := 2) hhL2 hGL2
  have hbdd : Integrable (fun x => t * (h x) ^ 2 + (G x) ^ 2 / (4 * t)) π :=
    (hhsq.const_mul t).add (hGb.1.div_const (4 * t))
  have hstep : |∫ x, h x * G x ∂π| ≤ ∫ x, (t * (h x) ^ 2 + (G x) ^ 2 / (4 * t)) ∂π := by
    refine le_trans (abs_integral_le_integral_abs) ?_
    refine integral_mono hprod.abs hbdd fun x => ?_
    exact abs_mul_le_quad t (h x) (G x) ht0
  have hcompute : ∫ x, (t * (h x) ^ 2 + (G x) ^ 2 / (4 * t)) ∂π
      = t * V + (∫ x, (G x) ^ 2 ∂π) / (4 * t) := by
    rw [integral_add (hhsq.const_mul t) (hGb.1.div_const (4 * t)), integral_const_mul,
      integral_div]
  have hAk : ∫ x, (G x) ^ 2 ∂π ≤ t ^ 2 * V := by
    have h4 : (1 / 4 : ℝ) = (1 / 2 : ℝ) ^ 2 := by norm_num
    have hpow : (1 / 4 : ℝ) ^ (k / N) = t ^ 2 := by
      rw [h4, ht, ← pow_mul, ← pow_mul, Nat.mul_comm 2 (k / N)]
    rw [← hpow]
    exact hGdecay
  have h4t : (0:ℝ) < 4 * t := by linarith
  have hdiv : (∫ x, (G x) ^ 2 ∂π) / (4 * t) ≤ t * V / 4 := by
    have hstep2 : (∫ x, (G x) ^ 2 ∂π) / (4 * t) ≤ (t ^ 2 * V) / (4 * t) := by gcongr
    refine le_trans hstep2 (le_of_eq ?_)
    field_simp
  calc |∫ x, h x * G x ∂π|
      ≤ ∫ x, (t * (h x) ^ 2 + (G x) ^ 2 / (4 * t)) ∂π := hstep
    _ = t * V + (∫ x, (G x) ^ 2 ∂π) / (4 * t) := hcompute
    _ ≤ t * V + t * V / 4 := by linarith
    _ = 5 / 4 * V * t := by ring

/-- **Absolute convergence of the autocovariance series** for a uniformly ergodic
chain and a square-integrable observable. -/
theorem summable_lagCovariance_of_uniformlyErgodic (P : Kernel X X) [IsMarkovKernel P]
    (π : Measure X) [IsProbabilityMeasure π] (hinv : Kernel.Invariant P π)
    (huni : UniformlyErgodic P π) (f : X → ℝ) (hf : Measurable f) (hL2 : MemLp f 2 π) :
    Summable (fun k : ℕ => lagCovariance P π f f (k + 1)) := by
  obtain ⟨C, N, hC, hN, hbound⟩ := abs_lagCovariance_le_geom P π hinv huni f hf hL2
  refine Summable.of_norm_bounded (g := fun k : ℕ => C * (1 / 2 : ℝ) ^ (k / N))
    ((summable_half_pow_div N hN).mul_left C) fun k => ?_
  rw [Real.norm_eq_abs]
  refine le_trans (hbound (k + 1)) ?_
  have hle : k / N ≤ (k + 1) / N := Nat.div_le_div_right (by omega)
  have hp : (1 / 2 : ℝ) ^ ((k + 1) / N) ≤ (1 / 2 : ℝ) ^ (k / N) :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) hle
  nlinarith [hC, hp]


/-! ### Part 1: an `L²` bound for a bounded martingale difference sequence -/

section MDS

variable {Ω : Type*} {m0 : MeasurableSpace Ω}

private lemma mds_integrable (μ : Measure Ω) [IsProbabilityMeasure μ]
    (V : Ω → ℝ) (b : ℝ) (hV : Measurable V) (hbd : ∀ ω, |V ω| ≤ b) :
    Integrable V μ :=
  (integrable_const b).mono' hV.aestronglyMeasurable
    (Filter.Eventually.of_forall fun ω => by simpa [Real.norm_eq_abs] using hbd ω)

private lemma mds_bound_nonneg (μ : Measure Ω) [IsProbabilityMeasure μ]
    (V : Ω → ℝ) (b : ℝ) (hV : Measurable V) (hbd : ∀ ω, |V ω| ≤ b) : 0 ≤ b := by
  have h1 : (0 : ℝ) ≤ ∫ ω, |V ω| ∂μ := integral_nonneg fun ω => abs_nonneg _
  have h2 : ∫ ω, |V ω| ∂μ ≤ ∫ _ω, b ∂μ :=
    integral_mono (mds_integrable μ V b hV hbd).abs (integrable_const b) hbd
  simpa using h1.trans h2

/-- Distinct terms of a bounded martingale difference sequence are orthogonal. -/
lemma integral_mul_mds_eq_zero (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ m0) (V : ℕ → Ω → ℝ) (b : ℝ)
    (hmeas : ∀ j, Measurable (V j))
    (hadapt : ∀ j, StronglyMeasurable[ℱ (j + 1)] (V j))
    (hbd : ∀ j ω, |V j ω| ≤ b)
    (hmds : ∀ j, μ[V j | ℱ j] =ᵐ[μ] 0) {i j : ℕ} (hij : i < j) :
    ∫ ω, V i ω * V j ω ∂μ = 0 := by
  have hb : 0 ≤ b := mds_bound_nonneg μ (V 0) b (hmeas 0) (hbd 0)
  have hint : ∀ k, Integrable (V k) μ := fun k =>
    mds_integrable μ (V k) b (hmeas k) (hbd k)
  have hintmul : Integrable (fun ω => V i ω * V j ω) μ := by
    refine (integrable_const (b * b)).mono' (((hmeas i).mul (hmeas j)).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun ω => ?_)
    simp only [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul (hbd i ω) (hbd j ω) (abs_nonneg _) hb
  have hVi : StronglyMeasurable[ℱ j] (V i) := (hadapt i).mono (ℱ.mono (by omega))
  have hpull : μ[fun ω => V i ω * V j ω | ℱ j] =ᵐ[μ] fun ω => V i ω * (μ[V j | ℱ j]) ω := by
    have := condExp_mul_of_stronglyMeasurable_left (m := ℱ j) (μ := μ)
      (f := V i) (g := V j) hVi (by simpa [Pi.mul_apply] using hintmul) (hint j)
    simpa [Pi.mul_apply] using this
  have hzero : μ[fun ω => V i ω * V j ω | ℱ j] =ᵐ[μ] 0 := by
    filter_upwards [hpull, hmds j] with ω h1 h2
    simp [h1, h2]
  calc ∫ ω, V i ω * V j ω ∂μ
      = ∫ ω, (μ[fun ω => V i ω * V j ω | ℱ j]) ω ∂μ := (integral_condExp (ℱ.le j)).symm
    _ = 0 := by rw [integral_congr_ae hzero]; simp

/-- `E[(∑_{j<m} V j)²] ≤ m · b²` for a martingale difference sequence bounded by `b`. -/
lemma integral_sq_sum_mds_bound (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ m0) (V : ℕ → Ω → ℝ) (b : ℝ)
    (hmeas : ∀ j, Measurable (V j))
    (hadapt : ∀ j, StronglyMeasurable[ℱ (j + 1)] (V j))
    (hbd : ∀ j ω, |V j ω| ≤ b)
    (hmds : ∀ j, μ[V j | ℱ j] =ᵐ[μ] 0) (m : ℕ) :
    ∫ ω, (∑ j ∈ Finset.range m, V j ω) ^ 2 ∂μ ≤ m * b ^ 2 := by
  have hb : 0 ≤ b := mds_bound_nonneg μ (V 0) b (hmeas 0) (hbd 0)
  have hintmul : ∀ i j, Integrable (fun ω => V i ω * V j ω) μ := by
    intro i j
    refine (integrable_const (b * b)).mono' (((hmeas i).mul (hmeas j)).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun ω => ?_)
    simp only [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul (hbd i ω) (hbd j ω) (abs_nonneg _) hb
  have hstep : ∫ ω, (∑ j ∈ Finset.range m, V j ω) ^ 2 ∂μ
      = ∑ i ∈ Finset.range m, ∑ j ∈ Finset.range m, ∫ ω, V i ω * V j ω ∂μ := by
    have hexp : ∀ ω, (∑ j ∈ Finset.range m, V j ω) ^ 2
        = ∑ i ∈ Finset.range m, ∑ j ∈ Finset.range m, V i ω * V j ω := by
      intro ω; rw [sq, Finset.sum_mul_sum]
    simp_rw [hexp]
    rw [integral_finset_sum _ (fun i _ => integrable_finset_sum _ (fun j _ => hintmul i j))]
    exact Finset.sum_congr rfl fun i _ => integral_finset_sum _ (fun j _ => hintmul i j)
  rw [hstep]
  have hinner : ∀ i ∈ Finset.range m,
      ∑ j ∈ Finset.range m, ∫ ω, V i ω * V j ω ∂μ = ∫ ω, V i ω * V i ω ∂μ := by
    intro i hi
    refine Finset.sum_eq_single i (fun j _ hji => ?_) (fun h => absurd hi h)
    rcases lt_or_gt_of_ne hji with h | h
    · have := integral_mul_mds_eq_zero μ ℱ V b hmeas hadapt hbd hmds h
      simpa [mul_comm] using this
    · exact integral_mul_mds_eq_zero μ ℱ V b hmeas hadapt hbd hmds h
  rw [Finset.sum_congr rfl hinner]
  have hdiag : ∀ i ∈ Finset.range m, ∫ ω, V i ω * V i ω ∂μ ≤ b ^ 2 := by
    intro i _
    have : ∫ ω, V i ω * V i ω ∂μ ≤ ∫ _ω, b ^ 2 ∂μ := by
      refine integral_mono (hintmul i i) (integrable_const _) fun ω => ?_
      nlinarith [hbd i ω, abs_nonneg (V i ω), sq_abs (V i ω)]
    simpa using this
  calc ∑ i ∈ Finset.range m, ∫ ω, V i ω * V i ω ∂μ
      ≤ ∑ _i ∈ Finset.range m, b ^ 2 := Finset.sum_le_sum hdiag
    _ = m * b ^ 2 := by simp [Finset.sum_const, mul_comm]

end MDS


/-! ### Part 2: geometric decay of the mixed autocovariance -/

/-- A bounded measurable function is integrable against a probability measure. -/
lemma integrable_of_bounded {Y : Type*} [MeasurableSpace Y] (μ : Measure Y)
    [IsProbabilityMeasure μ] (g : Y → ℝ) (hg : Measurable g) (B : ℝ) (hB : ∀ y, |g y| ≤ B) :
    Integrable g μ :=
  (integrable_const B).mono' hg.aestronglyMeasurable
    (Filter.Eventually.of_forall fun y => by simpa [Real.norm_eq_abs] using hB y)

/-- The lag-`k` covariance between two square-integrable observables of a uniformly
ergodic chain decays geometrically. -/
lemma abs_lagCovariance_pair_le_geom (P : Kernel X X) [IsMarkovKernel P] (π : Measure X)
    [IsProbabilityMeasure π] (hinv : Kernel.Invariant P π)
    (huni : UniformlyErgodic P π) (f g : X → ℝ) (hf : Measurable f) (hg : Measurable g)
    (hfL2 : MemLp f 2 π) (hgL2 : MemLp g 2 π) :
    ∃ (C : ℝ) (N : ℕ), 0 ≤ C ∧ 1 ≤ N ∧
      ∀ k : ℕ, |lagCovariance P π f g k| ≤ C * (1 / 2 : ℝ) ^ (k / N) := by
  obtain ⟨N, hN, hrate⟩ := exists_lag_tvDist_le_of_uniformlyErgodic P π huni
  set cf : ℝ := ∫ y, f y ∂π with hcf
  set cg : ℝ := ∫ y, g y ∂π with hcg
  set u : X → ℝ := fun x => f x - cf with hu
  set v : X → ℝ := fun x => g x - cg with hv
  have hum : Measurable u := hf.sub measurable_const
  have hvm : Measurable v := hg.sub measurable_const
  have huL2 : MemLp u 2 π := hfL2.sub (memLp_const cf)
  have hvL2 : MemLp v 2 π := hgL2.sub (memLp_const cg)
  have husq : Integrable (fun x => (u x) ^ 2) π :=
    (memLp_two_iff_integrable_sq hum.aestronglyMeasurable).1 huL2
  have hvsq : Integrable (fun x => (v x) ^ 2) π :=
    (memLp_two_iff_integrable_sq hvm.aestronglyMeasurable).1 hvL2
  have hgint : Integrable g π := hgL2.integrable (by norm_num)
  have hvmean : ∫ x, v x ∂π = 0 := by
    rw [hv]
    rw [integral_sub hgint (integrable_const cg), integral_const]
    simp [hcg]
  set Vu : ℝ := ∫ x, (u x) ^ 2 ∂π with hVu
  set Vv : ℝ := ∫ x, (v x) ^ 2 ∂π with hVv
  have hVu0 : 0 ≤ Vu := integral_nonneg fun x => sq_nonneg _
  have hVv0 : 0 ≤ Vv := integral_nonneg fun x => sq_nonneg _
  refine ⟨Vu + Vv / 4, N, by positivity, hN, fun k => ?_⟩
  set G : X → ℝ := fun x => ∫ y, v y ∂(iterKernel P k x) with hG
  have hGmeas : Measurable G :=
    (StronglyMeasurable.integral_kernel (κ := iterKernel P k) hvm.stronglyMeasurable).measurable
  have hGb := iterMean_bound P π hinv k v hvm hvsq
  have hGdecay := integral_sq_iterKernel_geom_decay P π hinv N hN (1 / 16) (by norm_num)
    (by norm_num) hrate v hvm hvsq hvmean k
  have hinvk : Kernel.Invariant (iterKernel P k) π := invariant_iterKernel P π hinv k
  have hgc : Integrable g ((iterKernel P k) ∘ₘ π) := by
    rw [show ((iterKernel P k) ∘ₘ π) = π from hinvk]; exact hgint
  have hsplit := (Measure.integrable_comp_iff (κ := iterKernel P k) (μ := π)
    (f := g) hg.aestronglyMeasurable).1 hgc
  have hlag : lagCovariance P π f g k = ∫ x, u x * G x ∂π := by
    unfold lagCovariance
    refine integral_congr_ae ?_
    filter_upwards [hsplit.1] with x hx
    have hvx : ∫ y, v y ∂((iterKernel P k) x) = (∫ y, g y ∂((iterKernel P k) x)) - cg := by
      rw [hv]
      rw [integral_sub hx (integrable_const cg), integral_const]
      simp
    rw [hG]
    simp only
    rw [hvx]
  rw [hlag]
  set t : ℝ := (1 / 2 : ℝ) ^ (k / N) with ht
  have ht0 : 0 < t := by positivity
  have hprod : Integrable (fun x => u x * G x) π := by
    have hGL2 : MemLp G 2 π :=
      (memLp_two_iff_integrable_sq hGmeas.aestronglyMeasurable).2 hGb.1
    exact MemLp.integrable_mul (p := 2) (q := 2) huL2 hGL2
  have hbdd : Integrable (fun x => t * (u x) ^ 2 + (G x) ^ 2 / (4 * t)) π :=
    (husq.const_mul t).add (hGb.1.div_const (4 * t))
  have hstep : |∫ x, u x * G x ∂π| ≤ ∫ x, (t * (u x) ^ 2 + (G x) ^ 2 / (4 * t)) ∂π := by
    refine le_trans (abs_integral_le_integral_abs) ?_
    refine integral_mono hprod.abs hbdd fun x => ?_
    exact abs_mul_le_quad t (u x) (G x) ht0
  have hcompute : ∫ x, (t * (u x) ^ 2 + (G x) ^ 2 / (4 * t)) ∂π
      = t * Vu + (∫ x, (G x) ^ 2 ∂π) / (4 * t) := by
    rw [integral_add (husq.const_mul t) (hGb.1.div_const (4 * t)), integral_const_mul,
      integral_div]
  have hAk : ∫ x, (G x) ^ 2 ∂π ≤ t ^ 2 * Vv := by
    have h4 : (1 / 4 : ℝ) = (1 / 2 : ℝ) ^ 2 := by norm_num
    have hpow : (1 / 4 : ℝ) ^ (k / N) = t ^ 2 := by
      rw [h4, ht, ← pow_mul, ← pow_mul, Nat.mul_comm 2 (k / N)]
    rw [← hpow]
    exact hGdecay
  have h4t : (0:ℝ) < 4 * t := by linarith
  have hdiv : (∫ x, (G x) ^ 2 ∂π) / (4 * t) ≤ t * Vv / 4 := by
    have hstep2 : (∫ x, (G x) ^ 2 ∂π) / (4 * t) ≤ (t ^ 2 * Vv) / (4 * t) := by gcongr
    refine le_trans hstep2 (le_of_eq ?_)
    field_simp
  calc |∫ x, u x * G x ∂π|
      ≤ ∫ x, (t * (u x) ^ 2 + (G x) ^ 2 / (4 * t)) ∂π := hstep
    _ = t * Vu + (∫ x, (G x) ^ 2 ∂π) / (4 * t) := hcompute
    _ ≤ t * Vu + t * Vv / 4 := by linarith
    _ = (Vu + Vv / 4) * t := by ring

lemma tendsto_lagCovariance_pair_zero (P : Kernel X X) [IsMarkovKernel P] (π : Measure X)
    [IsProbabilityMeasure π] (hinv : Kernel.Invariant P π)
    (huni : UniformlyErgodic P π) (f g : X → ℝ) (hf : Measurable f) (hg : Measurable g)
    (hfL2 : MemLp f 2 π) (hgL2 : MemLp g 2 π) :
    Tendsto (fun k : ℕ => lagCovariance P π f g k) atTop (𝓝 0) := by
  obtain ⟨C, N, hC, hN, hbound⟩ :=
    abs_lagCovariance_pair_le_geom P π hinv huni f g hf hg hfL2 hgL2
  have h0 : Tendsto (fun k : ℕ => C * (1 / 2 : ℝ) ^ (k / N)) atTop (𝓝 0) := by
    have h1 := (summable_half_pow_div N hN).tendsto_atTop_zero
    simpa using h1.const_mul C
  exact squeeze_zero_norm (fun k => by simpa [Real.norm_eq_abs] using hbound k) h0


/-! ### Part 3: the Poisson representation of the asymptotic variance -/

/-- The one-step conditional mean `(Pg)(x) = ∫ g dP(x, ·)`. -/
noncomputable def kerMean (P : Kernel X X) (g : X → ℝ) : X → ℝ := fun x => ∫ y, g y ∂(P x)

/-- The `k`-step conditional mean `(P^k g)(x) = ∫ g dP^k(x, ·)`. -/
noncomputable def iterMean (P : Kernel X X) (k : ℕ) (g : X → ℝ) : X → ℝ :=
  fun x => ∫ y, g y ∂(iterKernel P k x)

lemma measurable_iterMean (P : Kernel X X) [IsMarkovKernel P] (k : ℕ) (g : X → ℝ)
    (hg : Measurable g) : Measurable (iterMean P k g) :=
  (StronglyMeasurable.integral_kernel (κ := iterKernel P k) hg.stronglyMeasurable).measurable

lemma abs_iterMean_le (P : Kernel X X) [IsMarkovKernel P] (k : ℕ) (g : X → ℝ)
    (hg : Measurable g) (B : ℝ) (hB : ∀ x, |g x| ≤ B) (x : X) : |iterMean P k g x| ≤ B := by
  have hint : Integrable g (iterKernel P k x) :=
    integrable_of_bounded _ g hg B hB
  refine le_trans (abs_integral_le_integral_abs) ?_
  have : ∫ y, |g y| ∂(iterKernel P k x) ≤ ∫ _y, B ∂(iterKernel P k x) :=
    integral_mono hint.abs (integrable_const B) hB
  simpa using this

lemma measurable_kerMean (P : Kernel X X) [IsMarkovKernel P] (g : X → ℝ)
    (hg : Measurable g) : Measurable (kerMean P g) :=
  (StronglyMeasurable.integral_kernel (κ := P) hg.stronglyMeasurable).measurable

lemma abs_kerMean_le (P : Kernel X X) [IsMarkovKernel P] (g : X → ℝ)
    (hg : Measurable g) (B : ℝ) (hB : ∀ x, |g x| ≤ B) (x : X) : |kerMean P g x| ≤ B := by
  have hint : Integrable g (P x) := integrable_of_bounded _ g hg B hB
  refine le_trans (abs_integral_le_integral_abs) ?_
  have h : ∫ y, |g y| ∂(P x) ≤ ∫ _y, B ∂(P x) :=
    integral_mono hint.abs (integrable_const B) hB
  simpa using h

lemma iterMean_zero (P : Kernel X X) [IsMarkovKernel P] (g : X → ℝ)
    (hg : Measurable g) (x : X) : iterMean P 0 g x = g x := by
  simp only [iterMean, iterKernel_zero, Kernel.id_apply]
  exact integral_dirac' g x hg.stronglyMeasurable

lemma iterMean_kerMean (P : Kernel X X) [IsMarkovKernel P] (g : X → ℝ)
    (hg : Measurable g) (B : ℝ) (hB : ∀ x, |g x| ≤ B) (k : ℕ) (x : X) :
    iterMean P k (kerMean P g) x = iterMean P (k + 1) g x := by
  have hint : Integrable g ((P ∘ₖ iterKernel P k) x) := integrable_of_bounded _ g hg B hB
  have h := ProbabilityTheory.Kernel.integral_comp (η := P) (κ := iterKernel P k) (a := x) hint
  simp only [iterMean, kerMean, iterKernel_succ]
  rw [h]

lemma lagCovariance_eq_iterMean (P : Kernel X X) [IsMarkovKernel P] (π : Measure X)
    (f g : X → ℝ) (k : ℕ) :
    lagCovariance P π f g k
      = ∫ x, (f x - ∫ y, f y ∂π) * (iterMean P k g x - ∫ y, g y ∂π) ∂π := rfl

/-- **Poisson representation of the asymptotic variance.**  If `g` solves the Poisson
equation `g - Pg = f - E_π f` with `g` bounded, then the autocovariance series of `f`
collapses to `E_π g² - E_π (Pg)²`. -/
theorem asymptoticVariance_of_poisson (P : Kernel X X) [IsMarkovKernel P] (π : Measure X)
    [IsProbabilityMeasure π] (hinv : Kernel.Invariant P π) (huni : UniformlyErgodic P π)
    (f : X → ℝ) (hf : Measurable f) (B : ℝ) (hB : ∀ x, |f x| ≤ B)
    (g : X → ℝ) (hg : Measurable g) (Cg : ℝ) (hCg : ∀ x, |g x| ≤ Cg)
    (hpois : ∀ x, g x - kerMean P g x = f x - ∫ y, f y ∂π) :
    asymptoticVariance P π f = ∫ x, (g x) ^ 2 ∂π - ∫ x, (kerMean P g x) ^ 2 ∂π := by
  have hB0 : 0 ≤ B := by
    have h1 : (0 : ℝ) ≤ ∫ x, |f x| ∂π := integral_nonneg fun x => abs_nonneg _
    have h2 : ∫ x, |f x| ∂π ≤ ∫ _x, B ∂π :=
      integral_mono (integrable_of_bounded π f hf B hB).abs (integrable_const B) hB
    simpa using h1.trans h2
  have hCg0 : 0 ≤ Cg := by
    have h1 : (0 : ℝ) ≤ ∫ x, |g x| ∂π := integral_nonneg fun x => abs_nonneg _
    have h2 : ∫ x, |g x| ∂π ≤ ∫ _x, Cg ∂π :=
      integral_mono (integrable_of_bounded π g hg Cg hCg).abs (integrable_const Cg) hCg
    simpa using h1.trans h2
  set c : ℝ := ∫ y, f y ∂π with hc
  set cg : ℝ := ∫ y, g y ∂π with hcg
  set Pg : X → ℝ := kerMean P g with hPgdef
  have hPgm : Measurable Pg := measurable_kerMean P g hg
  have hPgb : ∀ x, |Pg x| ≤ Cg := abs_kerMean_le P g hg Cg hCg
  set u : X → ℝ := fun x => f x - c with hudef
  have hum : Measurable u := hf.sub measurable_const
  have hueq : ∀ x, u x = g x - Pg x := by
    intro x; rw [hudef]; exact (hpois x).symm
  have habs2 : ∀ a b : ℝ, |a - b| ≤ |a| + |b| := by
    intro a b
    simpa [sub_eq_add_neg] using abs_add_le a (-b)
  have hub : ∀ x, |u x| ≤ 2 * Cg := by
    intro x
    rw [hueq x]
    calc |g x - Pg x| ≤ |g x| + |Pg x| := habs2 _ _
      _ ≤ Cg + Cg := add_le_add (hCg x) (hPgb x)
      _ = 2 * Cg := by ring
  have hfint : Integrable f π := integrable_of_bounded π f hf B hB
  have hgint : Integrable g π := integrable_of_bounded π g hg Cg hCg
  have humean : ∫ x, u x ∂π = 0 := by
    have he : ∫ x, u x ∂π = (∫ x, f x ∂π) - c := by
      rw [hudef]
      simp only
      rw [integral_sub hfint (integrable_const c), integral_const]
      simp
    rw [he, hc]; ring
  have hsqbd : ∀ (h : X → ℝ) (D : ℝ), (∀ x, |h x| ≤ D) → ∀ x, |(h x) ^ 2| ≤ D ^ 2 := by
    intro h D hD x
    rw [abs_of_nonneg (sq_nonneg _)]
    nlinarith [hD x, abs_nonneg (h x), sq_abs (h x)]
  have hfsq : Integrable (fun x => (f x) ^ 2) π :=
    integrable_of_bounded π _ (hf.pow_const 2) (B ^ 2) (hsqbd f B hB)
  have hgsq : Integrable (fun x => (g x) ^ 2) π :=
    integrable_of_bounded π _ (hg.pow_const 2) (Cg ^ 2) (hsqbd g Cg hCg)
  have hPgsq : Integrable (fun x => (Pg x) ^ 2) π :=
    integrable_of_bounded π _ (hPgm.pow_const 2) (Cg ^ 2) (hsqbd Pg Cg hPgb)
  have hfL2 : MemLp f 2 π := (memLp_two_iff_integrable_sq hf.aestronglyMeasurable).2 hfsq
  have hgL2 : MemLp g 2 π := (memLp_two_iff_integrable_sq hg.aestronglyMeasurable).2 hgsq
  have hUprod : ∀ (h : X → ℝ), Measurable h → (∀ x, |h x| ≤ 2 * Cg) →
      Integrable (fun x => u x * h x) π := by
    intro h hhm hhb
    refine integrable_of_bounded π _ (hum.mul hhm) ((2 * Cg) * (2 * Cg)) fun x => ?_
    rw [abs_mul]
    exact mul_le_mul (hub x) (hhb x) (abs_nonneg _) (by positivity)
  have hUG : Integrable (fun x => u x * g x) π :=
    hUprod g hg fun x => le_trans (hCg x) (by linarith)
  have hQint : ∀ m : ℕ, Integrable (fun x => u x * iterMean P m g x) π := fun m =>
    hUprod _ (measurable_iterMean P m g hg)
      fun x => le_trans (abs_iterMean_le P m g hg Cg hCg x) (by linarith)
  have hUU : Integrable (fun x => u x * u x) π := hUprod u hum hub
  -- Step A: the Poisson equation propagates through the `k`-step kernel
  have hA : ∀ (k : ℕ) (x : X),
      iterMean P k f x - c = iterMean P k g x - iterMean P (k + 1) g x := by
    intro k x
    have hfi : Integrable f (iterKernel P k x) := integrable_of_bounded _ f hf B hB
    have hgi : Integrable g (iterKernel P k x) := integrable_of_bounded _ g hg Cg hCg
    have hPgi : Integrable Pg (iterKernel P k x) := integrable_of_bounded _ Pg hPgm Cg hPgb
    have e1 : iterMean P k f x - c = ∫ y, (f y - c) ∂(iterKernel P k x) := by
      simp only [iterMean]
      rw [integral_sub hfi (integrable_const c), integral_const]
      simp
    have e2 : ∫ y, (f y - c) ∂(iterKernel P k x) = ∫ y, (g y - Pg y) ∂(iterKernel P k x) := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
      have h := hueq y
      rw [hudef] at h
      simpa using h
    have e3 : ∫ y, (g y - Pg y) ∂(iterKernel P k x)
        = iterMean P k g x - iterMean P k Pg x := by
      simp only [iterMean]
      rw [integral_sub hgi hPgi]
    rw [e1, e2, e3, hPgdef, iterMean_kerMean P g hg Cg hCg k x]
  -- Step B: the autocovariances in terms of `u` and the `k`-step means of `g`
  have hlagff : ∀ k : ℕ, lagCovariance P π f f k
      = ∫ x, u x * (iterMean P k g x - iterMean P (k + 1) g x) ∂π := by
    intro k
    rw [lagCovariance_eq_iterMean, ← hc]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    dsimp only [hudef]
    rw [hA k x]
  have hlagfg : ∀ m : ℕ, lagCovariance P π f g m = ∫ x, u x * iterMean P m g x ∂π := by
    intro m
    rw [lagCovariance_eq_iterMean, ← hc, ← hcg]
    have hui : Integrable (fun x => u x * cg) π :=
      (integrable_of_bounded π u hum (2 * Cg) hub).mul_const cg
    have hsplit : ∫ x, (f x - c) * (iterMean P m g x - cg) ∂π
        = ∫ x, u x * iterMean P m g x ∂π - ∫ x, u x * cg ∂π := by
      rw [← integral_sub (hQint m) hui]
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      simp only [hudef]; ring
    rw [hsplit]
    have hz : ∫ x, u x * cg ∂π = 0 := by
      rw [integral_mul_const, humean, zero_mul]
    rw [hz, sub_zero]
  -- Step C: telescoping
  have hint_term : ∀ k : ℕ,
      Integrable (fun x => u x * (iterMean P k g x - iterMean P (k + 1) g x)) π := by
    intro k
    refine hUprod _
      ((measurable_iterMean P k g hg).sub (measurable_iterMean P (k + 1) g hg)) fun x => ?_
    calc |iterMean P k g x - iterMean P (k + 1) g x|
        ≤ |iterMean P k g x| + |iterMean P (k + 1) g x| := habs2 _ _
      _ ≤ Cg + Cg :=
          add_le_add (abs_iterMean_le P k g hg Cg hCg x) (abs_iterMean_le P (k+1) g hg Cg hCg x)
      _ = 2 * Cg := by ring
  have htel : ∀ K : ℕ, ∑ k ∈ Finset.range (K + 1), lagCovariance P π f f k
      = ∫ x, u x * (g x - iterMean P (K + 1) g x) ∂π := by
    intro K
    have h1 : ∑ k ∈ Finset.range (K + 1), lagCovariance P π f f k
        = ∑ k ∈ Finset.range (K + 1),
            ∫ x, u x * (iterMean P k g x - iterMean P (k + 1) g x) ∂π :=
      Finset.sum_congr rfl fun k _ => hlagff k
    rw [h1, ← integral_finset_sum _ (fun k _ => hint_term k)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    dsimp only
    rw [← Finset.mul_sum]
    congr 1
    rw [Finset.sum_range_sub' (fun k => iterMean P k g x) (K + 1),
      iterMean_zero P g hg x]
  -- Step D: pass to the limit
  have hsummable := summable_lagCovariance_of_uniformlyErgodic P π hinv huni f hf hfL2
  have hkey : ∀ K : ℕ, ∑ k ∈ Finset.range K, lagCovariance P π f f (k + 1)
      = (∫ x, u x * g x ∂π) - lagCovariance P π f g (K + 1) - lagCovariance P π f f 0 := by
    intro K
    have h1 := htel K
    rw [Finset.sum_range_succ'] at h1
    have h2 : ∫ x, u x * (g x - iterMean P (K + 1) g x) ∂π
        = (∫ x, u x * g x ∂π) - ∫ x, u x * iterMean P (K + 1) g x ∂π := by
      rw [← integral_sub hUG (hQint (K + 1))]
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      ring
    rw [h2, ← hlagfg (K + 1)] at h1
    linarith [h1]
  have htsum : ∑' k : ℕ, lagCovariance P π f f (k + 1)
      = (∫ x, u x * g x ∂π) - lagCovariance P π f f 0 := by
    have hL : Tendsto (fun K : ℕ => ∑ k ∈ Finset.range K, lagCovariance P π f f (k + 1)) atTop
        (𝓝 (∑' k : ℕ, lagCovariance P π f f (k + 1))) := hsummable.hasSum.tendsto_sum_nat
    have h0 : Tendsto (fun K : ℕ => lagCovariance P π f g (K + 1)) atTop (𝓝 0) :=
      (tendsto_lagCovariance_pair_zero P π hinv huni f g hf hg hfL2 hgL2).comp
        (Filter.tendsto_add_atTop_nat 1)
    have hR : Tendsto (fun K : ℕ =>
        (∫ x, u x * g x ∂π) - lagCovariance P π f g (K + 1) - lagCovariance P π f f 0) atTop
        (𝓝 ((∫ x, u x * g x ∂π) - 0 - lagCovariance P π f f 0)) :=
      (tendsto_const_nhds.sub h0).sub tendsto_const_nhds
    have huniq := tendsto_nhds_unique (Filter.Tendsto.congr (fun K => hkey K) hL) hR
    simpa using huniq
  -- Step E: assemble
  have hzero0 : lagCovariance P π f f 0 = ∫ x, u x * u x ∂π := by
    rw [lagCovariance_eq_iterMean, ← hc]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    dsimp only [hudef]
    rw [iterMean_zero P f hf x]
  simp only [asymptoticVariance, asymptoticCovariance]
  rw [htsum, hzero0]
  have hfinal : ∫ x, u x * u x ∂π + ((∫ x, u x * g x ∂π) - ∫ x, u x * u x ∂π)
        + ((∫ x, u x * g x ∂π) - ∫ x, u x * u x ∂π)
      = ∫ x, ((g x) ^ 2 - (Pg x) ^ 2) ∂π := by
    have h2 : (2 : ℝ) * (∫ x, u x * g x ∂π) - ∫ x, u x * u x ∂π
        = ∫ x, ((g x) ^ 2 - (Pg x) ^ 2) ∂π := by
      rw [← integral_const_mul, ← integral_sub (hUG.const_mul 2) hUU]
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      simp only [hueq x]
      ring
    linarith [h2]
  rw [hfinal]
  exact integral_sub hgsq hPgsq


/-! ### Part 4: the martingale difference array of the Poisson decomposition -/

/-- The σ-algebra generated by the coordinates `≤ k`, in the form used by
`MarkovChainCLT.condExp_next_coord`. -/
def pathSigma (X : Type*) [MeasurableSpace X] (k : ℕ) : MeasurableSpace (ℕ → X) :=
  MeasurableSpace.comap (Preorder.frestrictLe (π := fun _ : ℕ => X) k) inferInstance

/-- The natural filtration of path space. -/
noncomputable def pathFilt (X : Type*) [MeasurableSpace X] :
    Filtration ℕ (inferInstance : MeasurableSpace (ℕ → X)) where
  seq k := pathSigma X k
  mono' i j hij := by
    show pathSigma X i ≤ pathSigma X j
    simp only [pathSigma]
    rw [← Preorder.frestrictLe₂_comp_frestrictLe (π := fun _ : ℕ => X) hij,
      ← MeasurableSpace.comap_comp]
    exact MeasurableSpace.comap_mono
      (Measurable.comap_le (Preorder.measurable_frestrictLe₂ (X := fun _ : ℕ => X) hij))
  le' k := by
    show pathSigma X k ≤ _
    simp only [pathSigma]
    exact Measurable.comap_le (Preorder.measurable_frestrictLe (X := fun _ : ℕ => X) k)

lemma pathFilt_apply (X : Type*) [MeasurableSpace X] (k : ℕ) :
    pathFilt X k = pathSigma X k := rfl

lemma measurable_coord_pathSigma {i k : ℕ} (hik : i ≤ k) :
    Measurable[pathSigma X k] (fun ω : ℕ → X => ω i) := by
  have hfr : Measurable[pathSigma X k] (Preorder.frestrictLe (π := fun _ : ℕ => X) k) :=
    Measurable.of_comap_le le_rfl
  exact (measurable_pi_apply (⟨i, Finset.mem_Iic.2 hik⟩ : ↑(Finset.Iic k))).comp hfr

/-- The martingale difference array of the Poisson decomposition:
`D n k = n^{-1/2} (g(X_k) - (Pg)(X_{k-1}))` for `k ≥ 1`, and `0` at `k = 0`. -/
noncomputable def mdsArray (P : Kernel X X) (g : X → ℝ) (n : ℕ) : ℕ → (ℕ → X) → ℝ
  | 0 => fun _ => 0
  | (j + 1) => fun ω => (Real.sqrt n)⁻¹ * (g (ω (j + 1)) - kerMean P g (ω j))

lemma mdsArray_zero (P : Kernel X X) (g : X → ℝ) (n : ℕ) (ω : ℕ → X) :
    mdsArray P g n 0 ω = 0 := rfl

lemma mdsArray_succ (P : Kernel X X) (g : X → ℝ) (n j : ℕ) (ω : ℕ → X) :
    mdsArray P g n (j + 1) ω
      = (Real.sqrt n)⁻¹ * (g (ω (j + 1)) - kerMean P g (ω j)) := rfl

lemma measurable_mdsArray (P : Kernel X X) [IsMarkovKernel P] (g : X → ℝ)
    (hg : Measurable g) (n k : ℕ) : Measurable (mdsArray P g n k) := by
  cases k with
  | zero => exact measurable_const
  | succ j =>
      refine Measurable.const_mul ?_ _
      exact (hg.comp (measurable_pi_apply (j + 1))).sub
        ((measurable_kerMean P g hg).comp (measurable_pi_apply j))

lemma stronglyMeasurable_coord_kerMean (P : Kernel X X) [IsMarkovKernel P] (g : X → ℝ)
    (hg : Measurable g) {j k : ℕ} (hjk : j ≤ k) :
    StronglyMeasurable[pathSigma X k] (fun ω : ℕ → X => kerMean P g (ω j)) :=
  (((measurable_kerMean P g hg).comp (measurable_coord_pathSigma hjk)) :
    Measurable[pathSigma X k] _).stronglyMeasurable

lemma adapted_mdsArray (P : Kernel X X) [IsMarkovKernel P] (g : X → ℝ)
    (hg : Measurable g) (n k : ℕ) :
    StronglyMeasurable[pathFilt X k] (mdsArray P g n k) := by
  rw [pathFilt_apply]
  cases k with
  | zero => exact stronglyMeasurable_const
  | succ j =>
      have h1 : Measurable[pathSigma X (j + 1)] (fun ω : ℕ → X => g (ω (j + 1))) :=
        hg.comp (measurable_coord_pathSigma (le_refl (j + 1)))
      have h2 : Measurable[pathSigma X (j + 1)] (fun ω : ℕ → X => kerMean P g (ω j)) :=
        (measurable_kerMean P g hg).comp (measurable_coord_pathSigma (Nat.le_succ j))
      exact ((h1.sub h2).const_mul _).stronglyMeasurable

lemma abs_mdsArray_le (P : Kernel X X) [IsMarkovKernel P] (g : X → ℝ)
    (hg : Measurable g) (Cg : ℝ) (hCg : ∀ x, |g x| ≤ Cg) (hCg0 : 0 ≤ Cg) (n k : ℕ)
    (ω : ℕ → X) : |mdsArray P g n k ω| ≤ (Real.sqrt n)⁻¹ * (2 * Cg) := by
  have hs : (0 : ℝ) ≤ (Real.sqrt n)⁻¹ := by positivity
  cases k with
  | zero =>
      rw [mdsArray_zero, abs_zero]
      positivity
  | succ j =>
      rw [mdsArray_succ, abs_mul, abs_of_nonneg hs]
      refine mul_le_mul_of_nonneg_left ?_ hs
      calc |g (ω (j + 1)) - kerMean P g (ω j)|
          ≤ |g (ω (j + 1))| + |kerMean P g (ω j)| := by
            simpa [sub_eq_add_neg] using abs_add_le (g (ω (j + 1))) (-(kerMean P g (ω j)))
        _ ≤ Cg + Cg := add_le_add (hCg _) (abs_kerMean_le P g hg Cg hCg _)
        _ = 2 * Cg := by ring

lemma condExp_mdsArray (P : Kernel X X) [IsMarkovKernel P] (lam : Measure X)
    [IsProbabilityMeasure lam] (g : X → ℝ) (hg : Measurable g) (Cg : ℝ)
    (hCg : ∀ x, |g x| ≤ Cg) (n k : ℕ) :
    (chainMeasure P lam)[mdsArray P g n (k + 1) | pathSigma X k]
      =ᵐ[chainMeasure P lam] 0 := by
  have hle : pathSigma X k ≤ (inferInstance : MeasurableSpace (ℕ → X)) := (pathFilt X).le k
  have hgc : Measurable (fun ω : ℕ → X => g (ω (k + 1))) := hg.comp (measurable_pi_apply _)
  have hPc : Measurable (fun ω : ℕ → X => kerMean P g (ω k)) :=
    (measurable_kerMean P g hg).comp (measurable_pi_apply _)
  have hgi : Integrable (fun ω : ℕ → X => g (ω (k + 1))) (chainMeasure P lam) :=
    integrable_of_bounded _ _ hgc Cg fun ω => hCg _
  have hPi : Integrable (fun ω : ℕ → X => kerMean P g (ω k)) (chainMeasure P lam) :=
    integrable_of_bounded _ _ hPc Cg fun ω => abs_kerMean_le P g hg Cg hCg _
  have h1 : (chainMeasure P lam)[fun ω : ℕ → X => g (ω (k + 1)) | pathSigma X k]
      =ᵐ[chainMeasure P lam] fun ω : ℕ → X => kerMean P g (ω k) :=
    (condExp_next_coord P lam g hg Cg hCg k).symm
  have h2 := condExp_of_stronglyMeasurable (μ := chainMeasure P lam) hle
      (stronglyMeasurable_coord_kerMean P g hg (le_refl k)) hPi
  have hsub : (chainMeasure P lam)[((fun ω : ℕ → X => g (ω (k + 1)))
      - fun ω : ℕ → X => kerMean P g (ω k)) | pathSigma X k] =ᵐ[chainMeasure P lam] 0 := by
    have hd := condExp_sub (m := pathSigma X k) hgi hPi
    filter_upwards [hd, h1] with ω e0 e1
    simp only [Pi.zero_apply]
    rw [e0]
    simp only [Pi.sub_apply]
    rw [e1, congrFun h2 ω]
    ring
  have hEq : mdsArray P g n (k + 1)
      = (Real.sqrt n)⁻¹ • ((fun ω : ℕ → X => g (ω (k + 1)))
        - fun ω : ℕ → X => kerMean P g (ω k)) := rfl
  rw [hEq]
  have hsm := condExp_smul (𝕜 := ℝ) (μ := chainMeasure P lam) ((Real.sqrt n)⁻¹)
    ((fun ω : ℕ → X => g (ω (k + 1))) - fun ω : ℕ → X => kerMean P g (ω k)) (pathSigma X k)
  filter_upwards [hsm, hsub] with ω e1 e2
  rw [e1]
  simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at e2 ⊢
  rw [e2, mul_zero]


/-! ### Part 5: the quadratic variation of the array -/

/-- The one-step conditional variance of the martingale increment. -/
noncomputable def stepVar (P : Kernel X X) (g : X → ℝ) : X → ℝ :=
  fun x => kerMean P (fun y => (g y) ^ 2) x - (kerMean P g x) ^ 2

/-- The squared martingale increment at time `j`. -/
noncomputable def sqIncr (P : Kernel X X) (g : X → ℝ) (j : ℕ) : (ℕ → X) → ℝ :=
  fun ω => (g (ω (j + 1)) - kerMean P g (ω j)) ^ 2

lemma measurable_stepVar (P : Kernel X X) [IsMarkovKernel P] (g : X → ℝ)
    (hg : Measurable g) : Measurable (stepVar P g) :=
  (measurable_kerMean P _ (hg.pow_const 2)).sub ((measurable_kerMean P g hg).pow_const 2)

lemma sq_bound_of_abs_bound {g : X → ℝ} {Cg : ℝ} (hCg : ∀ x, |g x| ≤ Cg) (x : X) :
    |(g x) ^ 2| ≤ Cg ^ 2 := by
  rw [abs_of_nonneg (sq_nonneg _)]
  nlinarith [hCg x, abs_nonneg (g x), sq_abs (g x)]

lemma stepVar_nonneg (P : Kernel X X) [IsMarkovKernel P] (g : X → ℝ) (hg : Measurable g)
    (Cg : ℝ) (hCg : ∀ x, |g x| ≤ Cg) (x : X) : 0 ≤ stepVar P g x := by
  have hgi : Integrable (fun y => (g y) ^ 2) (P x) :=
    integrable_of_bounded _ _ (hg.pow_const 2) (Cg ^ 2) (sq_bound_of_abs_bound hCg)
  have hL2 : MemLp g 2 (P x) := (memLp_two_iff_integrable_sq hg.aestronglyMeasurable).2 hgi
  have h := sq_integral_le_integral_sq (P x) g hL2
  simp only [stepVar, kerMean, sub_nonneg]
  exact h

lemma abs_stepVar_le (P : Kernel X X) [IsMarkovKernel P] (g : X → ℝ) (hg : Measurable g)
    (Cg : ℝ) (hCg : ∀ x, |g x| ≤ Cg) (x : X) : |stepVar P g x| ≤ 2 * Cg ^ 2 := by
  have h1 : |kerMean P (fun y => (g y) ^ 2) x| ≤ Cg ^ 2 :=
    abs_kerMean_le P _ (hg.pow_const 2) (Cg ^ 2) (sq_bound_of_abs_bound hCg) x
  have h2 : |(kerMean P g x) ^ 2| ≤ Cg ^ 2 := by
    rw [abs_of_nonneg (sq_nonneg _)]
    nlinarith [abs_kerMean_le P g hg Cg hCg x, abs_nonneg (kerMean P g x),
      sq_abs (kerMean P g x)]
  calc |stepVar P g x| ≤ |kerMean P (fun y => (g y) ^ 2) x| + |(kerMean P g x) ^ 2| := by
        have hab := abs_add_le (kerMean P (fun y => (g y) ^ 2) x) (-((kerMean P g x) ^ 2))
        rw [abs_neg] at hab
        simpa only [stepVar, sub_eq_add_neg] using hab
    _ ≤ Cg ^ 2 + Cg ^ 2 := add_le_add h1 h2
    _ = 2 * Cg ^ 2 := by ring

lemma measurable_sqIncr (P : Kernel X X) [IsMarkovKernel P] (g : X → ℝ)
    (hg : Measurable g) (j : ℕ) : Measurable (sqIncr P g j) :=
  (((hg.comp (measurable_pi_apply (j + 1))).sub
    ((measurable_kerMean P g hg).comp (measurable_pi_apply j)))).pow_const 2

lemma abs_sqIncr_le (P : Kernel X X) [IsMarkovKernel P] (g : X → ℝ) (hg : Measurable g)
    (Cg : ℝ) (hCg : ∀ x, |g x| ≤ Cg) (j : ℕ) (ω : ℕ → X) :
    |sqIncr P g j ω| ≤ 4 * Cg ^ 2 := by
  have hd : |g (ω (j + 1)) - kerMean P g (ω j)| ≤ 2 * Cg := by
    calc |g (ω (j + 1)) - kerMean P g (ω j)|
        ≤ |g (ω (j + 1))| + |kerMean P g (ω j)| := by
          simpa [sub_eq_add_neg] using abs_add_le (g (ω (j + 1))) (-(kerMean P g (ω j)))
      _ ≤ Cg + Cg := add_le_add (hCg _) (abs_kerMean_le P g hg Cg hCg _)
      _ = 2 * Cg := by ring
  have hz := sq_bound_of_abs_bound (g := fun _ : Unit => g (ω (j + 1)) - kerMean P g (ω j))
    (Cg := 2 * Cg) (fun _ => hd) ()
  simp only [sqIncr]
  calc |(g (ω (j + 1)) - kerMean P g (ω j)) ^ 2| ≤ (2 * Cg) ^ 2 := hz
    _ = 4 * Cg ^ 2 := by ring

lemma stronglyMeasurable_sqIncr (P : Kernel X X) [IsMarkovKernel P] (g : X → ℝ)
    (hg : Measurable g) (j : ℕ) :
    StronglyMeasurable[pathSigma X (j + 1)] (sqIncr P g j) := by
  have h1 : Measurable[pathSigma X (j + 1)] (fun ω : ℕ → X => g (ω (j + 1))) :=
    hg.comp (measurable_coord_pathSigma (le_refl (j + 1)))
  have h2 : Measurable[pathSigma X (j + 1)] (fun ω : ℕ → X => kerMean P g (ω j)) :=
    (measurable_kerMean P g hg).comp (measurable_coord_pathSigma (Nat.le_succ j))
  exact ((h1.sub h2).pow_const 2).stronglyMeasurable

lemma condExp_sqIncr (P : Kernel X X) [IsMarkovKernel P] (lam : Measure X)
    [IsProbabilityMeasure lam] (g : X → ℝ) (hg : Measurable g) (Cg : ℝ)
    (hCg : ∀ x, |g x| ≤ Cg) (hCg0 : 0 ≤ Cg) (j : ℕ) :
    (chainMeasure P lam)[sqIncr P g j | pathSigma X j]
      =ᵐ[chainMeasure P lam] fun ω : ℕ → X => stepVar P g (ω j) := by
  have hle : pathSigma X j ≤ (inferInstance : MeasurableSpace (ℕ → X)) := (pathFilt X).le j
  have hgc : Measurable (fun ω : ℕ → X => g (ω (j + 1))) := hg.comp (measurable_pi_apply _)
  have hkc : Measurable (fun ω : ℕ → X => kerMean P g (ω j)) :=
    (measurable_kerMean P g hg).comp (measurable_pi_apply _)
  have hkm : Measurable[pathSigma X j] (fun ω : ℕ → X => kerMean P g (ω j)) :=
    (measurable_kerMean P g hg).comp (measurable_coord_pathSigma (le_refl j))
  have hgi : Integrable (fun ω : ℕ → X => g (ω (j + 1))) (chainMeasure P lam) :=
    integrable_of_bounded _ _ hgc Cg fun ω => hCg _
  have hgSqi : Integrable (fun ω : ℕ → X => (g (ω (j + 1))) ^ 2) (chainMeasure P lam) :=
    integrable_of_bounded _ _ (hgc.pow_const 2) (Cg ^ 2) fun ω => sq_bound_of_abs_bound hCg _
  have hcrossi : Integrable ((fun ω : ℕ → X => kerMean P g (ω j))
      * fun ω : ℕ → X => g (ω (j + 1))) (chainMeasure P lam) := by
    refine integrable_of_bounded _ _ (hkc.mul hgc) (Cg * Cg) fun ω => ?_
    simp only [Pi.mul_apply, abs_mul]
    exact mul_le_mul (abs_kerMean_le P g hg Cg hCg _) (hCg _) (abs_nonneg _) hCg0
  have hkerSqi : Integrable (fun ω : ℕ → X => (kerMean P g (ω j)) ^ 2) (chainMeasure P lam) := by
    refine integrable_of_bounded _ _ (hkc.pow_const 2) (Cg ^ 2) fun ω => ?_
    exact sq_bound_of_abs_bound (g := fun x : X => kerMean P g x)
      (fun x => abs_kerMean_le P g hg Cg hCg x) (ω j)
  have hdecomp : sqIncr P g j
      = (((fun ω : ℕ → X => (g (ω (j + 1))) ^ 2)
          - (2 : ℝ) • ((fun ω : ℕ → X => kerMean P g (ω j))
            * fun ω : ℕ → X => g (ω (j + 1))))
        + fun ω : ℕ → X => (kerMean P g (ω j)) ^ 2) := by
    funext ω
    simp only [sqIncr, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, Pi.mul_apply, smul_eq_mul]
    ring
  rw [hdecomp]
  have hsm2 : Integrable ((2 : ℝ) • ((fun ω : ℕ → X => kerMean P g (ω j))
      * fun ω : ℕ → X => g (ω (j + 1)))) (chainMeasure P lam) := hcrossi.smul (2 : ℝ)
  have e1 := condExp_add (m := pathSigma X j) (hgSqi.sub hsm2) hkerSqi
  have e2 := condExp_sub (m := pathSigma X j) hgSqi hsm2
  have e3 := condExp_smul (𝕜 := ℝ) (μ := chainMeasure P lam) (2 : ℝ)
    ((fun ω : ℕ → X => kerMean P g (ω j)) * fun ω : ℕ → X => g (ω (j + 1))) (pathSigma X j)
  have hA : (chainMeasure P lam)[fun ω : ℕ → X => (g (ω (j + 1))) ^ 2 | pathSigma X j]
      =ᵐ[chainMeasure P lam] fun ω : ℕ → X => kerMean P (fun y => (g y) ^ 2) (ω j) :=
    (condExp_next_coord P lam (fun y => (g y) ^ 2) (hg.pow_const 2) (Cg ^ 2)
      (sq_bound_of_abs_bound hCg) j).symm
  have hgcond : (chainMeasure P lam)[fun ω : ℕ → X => g (ω (j + 1)) | pathSigma X j]
      =ᵐ[chainMeasure P lam] fun ω : ℕ → X => kerMean P g (ω j) :=
    (condExp_next_coord P lam g hg Cg hCg j).symm
  have hB := condExp_mul_of_stronglyMeasurable_left (m := pathSigma X j)
    (μ := chainMeasure P lam)
    (f := fun ω : ℕ → X => kerMean P g (ω j)) (g := fun ω : ℕ → X => g (ω (j + 1)))
    (stronglyMeasurable_coord_kerMean P g hg (le_refl j)) hcrossi hgi
  have hC := condExp_of_stronglyMeasurable (μ := chainMeasure P lam) hle
    (hkm.pow_const 2).stronglyMeasurable hkerSqi
  filter_upwards [e1, e2, e3, hA, hgcond, hB] with ω q1 q2 q3 q4 q5 q6
  rw [q1]
  simp only [Pi.add_apply]
  rw [q2]
  simp only [Pi.sub_apply]
  rw [q3]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [q4, q6]
  simp only [Pi.mul_apply]
  rw [q5, congrFun hC ω]
  simp only [stepVar]
  ring


/-- The centred squared increment: a bounded martingale difference sequence. -/
noncomputable def mdsVar (P : Kernel X X) (g : X → ℝ) (j : ℕ) : (ℕ → X) → ℝ :=
  fun ω => sqIncr P g j ω - stepVar P g (ω j)

lemma measurable_mdsVar (P : Kernel X X) [IsMarkovKernel P] (g : X → ℝ)
    (hg : Measurable g) (j : ℕ) : Measurable (mdsVar P g j) :=
  (measurable_sqIncr P g hg j).sub ((measurable_stepVar P g hg).comp (measurable_pi_apply j))

lemma abs_mdsVar_le (P : Kernel X X) [IsMarkovKernel P] (g : X → ℝ) (hg : Measurable g)
    (Cg : ℝ) (hCg : ∀ x, |g x| ≤ Cg) (j : ℕ) (ω : ℕ → X) :
    |mdsVar P g j ω| ≤ 6 * Cg ^ 2 := by
  have hab := abs_add_le (sqIncr P g j ω) (-(stepVar P g (ω j)))
  rw [abs_neg] at hab
  calc |mdsVar P g j ω| ≤ |sqIncr P g j ω| + |stepVar P g (ω j)| := by
        simpa only [mdsVar, sub_eq_add_neg] using hab
    _ ≤ 4 * Cg ^ 2 + 2 * Cg ^ 2 :=
        add_le_add (abs_sqIncr_le P g hg Cg hCg j ω) (abs_stepVar_le P g hg Cg hCg _)
    _ = 6 * Cg ^ 2 := by ring

lemma stronglyMeasurable_mdsVar (P : Kernel X X) [IsMarkovKernel P] (g : X → ℝ)
    (hg : Measurable g) (j : ℕ) :
    StronglyMeasurable[pathFilt X (j + 1)] (mdsVar P g j) := by
  rw [pathFilt_apply]
  have h2 : Measurable[pathSigma X (j + 1)] (fun ω : ℕ → X => stepVar P g (ω j)) :=
    (measurable_stepVar P g hg).comp (measurable_coord_pathSigma (Nat.le_succ j))
  exact ((stronglyMeasurable_sqIncr P g hg j).sub h2.stronglyMeasurable)

lemma condExp_mdsVar (P : Kernel X X) [IsMarkovKernel P] (lam : Measure X)
    [IsProbabilityMeasure lam] (g : X → ℝ) (hg : Measurable g) (Cg : ℝ)
    (hCg : ∀ x, |g x| ≤ Cg) (hCg0 : 0 ≤ Cg) (j : ℕ) :
    (chainMeasure P lam)[mdsVar P g j | pathFilt X j] =ᵐ[chainMeasure P lam] 0 := by
  rw [pathFilt_apply]
  have hle : pathSigma X j ≤ (inferInstance : MeasurableSpace (ℕ → X)) := (pathFilt X).le j
  have hsi : Integrable (sqIncr P g j) (chainMeasure P lam) :=
    integrable_of_bounded _ _ (measurable_sqIncr P g hg j) (4 * Cg ^ 2)
      (abs_sqIncr_le P g hg Cg hCg j)
  have hvi : Integrable (fun ω : ℕ → X => stepVar P g (ω j)) (chainMeasure P lam) :=
    integrable_of_bounded _ _ ((measurable_stepVar P g hg).comp (measurable_pi_apply j))
      (2 * Cg ^ 2) fun ω => abs_stepVar_le P g hg Cg hCg _
  have hvm : Measurable[pathSigma X j] (fun ω : ℕ → X => stepVar P g (ω j)) :=
    (measurable_stepVar P g hg).comp (measurable_coord_pathSigma (le_refl j))
  have hEq : mdsVar P g j
      = sqIncr P g j - fun ω : ℕ → X => stepVar P g (ω j) := rfl
  rw [hEq]
  have e0 := condExp_sub (m := pathSigma X j) hsi hvi
  have e1 := condExp_sqIncr P lam g hg Cg hCg hCg0 j
  have e2 := condExp_of_stronglyMeasurable (μ := chainMeasure P lam) hle
    hvm.stronglyMeasurable hvi
  filter_upwards [e0, e1] with ω q0 q1
  simp only [Pi.zero_apply]
  rw [q0]
  simp only [Pi.sub_apply]
  rw [q1, congrFun e2 ω]
  ring

lemma integral_sq_sum_mdsVar_le (P : Kernel X X) [IsMarkovKernel P] (lam : Measure X)
    [IsProbabilityMeasure lam] (g : X → ℝ) (hg : Measurable g) (Cg : ℝ)
    (hCg : ∀ x, |g x| ≤ Cg) (hCg0 : 0 ≤ Cg) (m : ℕ) :
    ∫ ω, (∑ j ∈ Finset.range m, mdsVar P g j ω) ^ 2 ∂(chainMeasure P lam)
      ≤ m * (6 * Cg ^ 2) ^ 2 :=
  integral_sq_sum_mds_bound (chainMeasure P lam) (pathFilt X) (mdsVar P g) (6 * Cg ^ 2)
    (fun j => measurable_mdsVar P g hg j) (fun j => stronglyMeasurable_mdsVar P g hg j)
    (fun j ω => abs_mdsVar_le P g hg Cg hCg j ω)
    (fun j => condExp_mdsVar P lam g hg Cg hCg hCg0 j) m

/-- `L¹` is dominated by `L²` on a probability space. -/
lemma integral_abs_le_sqrt_integral_sq {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (h : Ω → ℝ) (hh : Measurable h) (b : ℝ)
    (hb : ∀ ω, |h ω| ≤ b) :
    ∫ ω, |h ω| ∂μ ≤ Real.sqrt (∫ ω, (h ω) ^ 2 ∂μ) := by
  have habs : Integrable (fun ω => (|h ω|) ^ 2) μ := by
    refine integrable_of_bounded μ _ (hh.abs.pow_const 2) (b ^ 2) fun ω => ?_
    have : |h ω| ^ 2 = (h ω) ^ 2 := sq_abs _
    rw [this]
    exact sq_bound_of_abs_bound hb ω
  have hL2 : MemLp (fun ω => |h ω|) 2 μ :=
    (memLp_two_iff_integrable_sq hh.abs.aestronglyMeasurable).2 habs
  have h1 := sq_integral_le_integral_sq μ (fun ω => |h ω|) hL2
  have h2 : ∫ ω, (|h ω|) ^ 2 ∂μ = ∫ ω, (h ω) ^ 2 ∂μ := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
    exact sq_abs _
  rw [h2] at h1
  have hnn : (0 : ℝ) ≤ ∫ ω, |h ω| ∂μ := integral_nonneg fun ω => abs_nonneg _
  have h3 := Real.sqrt_le_sqrt h1
  rwa [Real.sqrt_sq hnn] at h3

lemma sum_sq_mdsArray (P : Kernel X X) [IsMarkovKernel P] (g : X → ℝ) (n : ℕ) (hn : 1 ≤ n)
    (ω : ℕ → X) :
    ∑ k ∈ Finset.range n, (mdsArray P g n k ω) ^ 2
      = (n : ℝ)⁻¹ * ∑ j ∈ Finset.range (n - 1), sqIncr P g j ω := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  rw [Finset.sum_range_succ', Finset.mul_sum]
  have h0 : (mdsArray P g (m + 1) 0 ω) ^ 2 = 0 := by rw [mdsArray_zero]; ring
  rw [h0, add_zero]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h1 : ((Real.sqrt ((m + 1 : ℕ) : ℝ))⁻¹) ^ 2 = (((m + 1 : ℕ) : ℝ))⁻¹ := by
    rw [inv_pow, Real.sq_sqrt (by positivity)]
  rw [mdsArray_succ, mul_pow, h1]
  rfl

lemma sum_shift_boundary (q : X → ℝ) (n : ℕ) (hn : 1 ≤ n) (ω : ℕ → X) :
    (∑ j ∈ Finset.range (n - 1), q (ω j)) - (∑ i ∈ Finset.range n, q (ω (i + 1)))
      = q (ω 0) - q (ω (n - 1)) - q (ω n) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  have h1 : ∑ j ∈ Finset.range (m + 1), q (ω j)
      = (∑ i ∈ Finset.range m, q (ω (i + 1))) + q (ω 0) := Finset.sum_range_succ' _ _
  have h2 : ∑ j ∈ Finset.range (m + 1), q (ω j)
      = (∑ j ∈ Finset.range m, q (ω j)) + q (ω m) := Finset.sum_range_succ _ _
  have h3 : ∑ i ∈ Finset.range (m + 1), q (ω (i + 1))
      = (∑ i ∈ Finset.range m, q (ω (i + 1))) + q (ω (m + 1)) := Finset.sum_range_succ _ _
  linarith


/-- The Cesàro average of the centred squared increments. -/
noncomputable def mdsAvg (P : Kernel X X) (g : X → ℝ) (n : ℕ) : (ℕ → X) → ℝ :=
  fun ω => (n : ℝ)⁻¹ * ∑ j ∈ Finset.range (n - 1), mdsVar P g j ω

lemma measurable_mdsAvg (P : Kernel X X) [IsMarkovKernel P] (g : X → ℝ)
    (hg : Measurable g) (n : ℕ) : Measurable (mdsAvg P g n) :=
  (Finset.measurable_sum _ fun j _ => measurable_mdsVar P g hg j).const_mul _

lemma abs_sum_mdsVar_le (P : Kernel X X) [IsMarkovKernel P] (g : X → ℝ) (hg : Measurable g)
    (Cg : ℝ) (hCg : ∀ x, |g x| ≤ Cg) (m : ℕ) (ω : ℕ → X) :
    |∑ j ∈ Finset.range m, mdsVar P g j ω| ≤ (m : ℝ) * (6 * Cg ^ 2) := by
  calc |∑ j ∈ Finset.range m, mdsVar P g j ω|
      ≤ ∑ j ∈ Finset.range m, |mdsVar P g j ω| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j ∈ Finset.range m, 6 * Cg ^ 2 :=
        Finset.sum_le_sum fun j _ => abs_mdsVar_le P g hg Cg hCg j ω
    _ = (m : ℝ) * (6 * Cg ^ 2) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

lemma abs_mdsAvg_le (P : Kernel X X) [IsMarkovKernel P] (g : X → ℝ) (hg : Measurable g)
    (Cg : ℝ) (hCg : ∀ x, |g x| ≤ Cg) (hCg0 : 0 ≤ Cg) (n : ℕ) (ω : ℕ → X) :
    |mdsAvg P g n ω| ≤ 6 * Cg ^ 2 := by
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h
    simp only [mdsAvg, Nat.cast_zero, inv_zero, zero_mul, abs_zero]
    positivity
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast h
  have hm : ((n - 1 : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.sub_le n 1
  have hB : (0 : ℝ) ≤ 6 * Cg ^ 2 := by positivity
  calc |mdsAvg P g n ω| = (n : ℝ)⁻¹ * |∑ j ∈ Finset.range (n - 1), mdsVar P g j ω| := by
        rw [mdsAvg, abs_mul, abs_of_nonneg (le_of_lt (inv_pos.2 hn0))]
    _ ≤ (n : ℝ)⁻¹ * (((n - 1 : ℕ) : ℝ) * (6 * Cg ^ 2)) := by
        gcongr
        exact abs_sum_mdsVar_le P g hg Cg hCg (n - 1) ω
    _ ≤ (n : ℝ)⁻¹ * ((n : ℝ) * (6 * Cg ^ 2)) := by gcongr
    _ = 6 * Cg ^ 2 := by field_simp

lemma integral_abs_mdsAvg_le (P : Kernel X X) [IsMarkovKernel P] (lam : Measure X)
    [IsProbabilityMeasure lam] (g : X → ℝ) (hg : Measurable g) (Cg : ℝ)
    (hCg : ∀ x, |g x| ≤ Cg) (hCg0 : 0 ≤ Cg) (n : ℕ) (hn : 1 ≤ n) :
    ∫ ω, |mdsAvg P g n ω| ∂(chainMeasure P lam)
      ≤ Real.sqrt ((6 * Cg ^ 2) ^ 2 / (n : ℝ)) := by
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hne : (n : ℝ) ≠ 0 := ne_of_gt hn0
  have hm : ((n - 1 : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.sub_le n 1
  have hsq : ∫ ω, (mdsAvg P g n ω) ^ 2 ∂(chainMeasure P lam)
      ≤ (6 * Cg ^ 2) ^ 2 / (n : ℝ) := by
    have h1 : ∫ ω, (mdsAvg P g n ω) ^ 2 ∂(chainMeasure P lam)
        = ((n : ℝ)⁻¹) ^ 2
          * ∫ ω, (∑ j ∈ Finset.range (n - 1), mdsVar P g j ω) ^ 2 ∂(chainMeasure P lam) := by
      simp only [mdsAvg, mul_pow]
      rw [integral_const_mul]
    rw [h1]
    have h2 := integral_sq_sum_mdsVar_le P lam g hg Cg hCg hCg0 (n - 1)
    have hfrac : ((n - 1 : ℕ) : ℝ) / (n : ℝ) ≤ 1 := by rw [div_le_one hn0]; exact hm
    have hBn : (0 : ℝ) ≤ (6 * Cg ^ 2) ^ 2 / (n : ℝ) := by positivity
    calc ((n : ℝ)⁻¹) ^ 2
          * ∫ ω, (∑ j ∈ Finset.range (n - 1), mdsVar P g j ω) ^ 2 ∂(chainMeasure P lam)
        ≤ ((n : ℝ)⁻¹) ^ 2 * (((n - 1 : ℕ) : ℝ) * (6 * Cg ^ 2) ^ 2) := by
          gcongr
      _ = (((n - 1 : ℕ) : ℝ) / (n : ℝ)) * ((6 * Cg ^ 2) ^ 2 / (n : ℝ)) := by
          field_simp
      _ ≤ 1 * ((6 * Cg ^ 2) ^ 2 / (n : ℝ)) := by gcongr
      _ = (6 * Cg ^ 2) ^ 2 / (n : ℝ) := one_mul _
  exact le_trans (integral_abs_le_sqrt_integral_sq (chainMeasure P lam) (mdsAvg P g n)
    (measurable_mdsAvg P g hg n) (6 * Cg ^ 2) (abs_mdsAvg_le P g hg Cg hCg hCg0 n))
    (Real.sqrt_le_sqrt hsq)

lemma abs_sampleAvg_le (φ : X → ℝ) (Bφ : ℝ) (hBφ : ∀ x, |φ x| ≤ Bφ) (hB0 : 0 ≤ Bφ)
    (n : ℕ) (ω : ℕ → X) : |sampleAvg φ n ω| ≤ Bφ := by
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h; simpa [sampleAvg] using hB0
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast h
  rw [sampleAvg, abs_mul, abs_of_nonneg (le_of_lt (inv_pos.2 hn0))]
  have hsum : |∑ i ∈ Finset.range n, φ (ω (i + 1))| ≤ (n : ℝ) * Bφ := by
    calc |∑ i ∈ Finset.range n, φ (ω (i + 1))|
        ≤ ∑ i ∈ Finset.range n, |φ (ω (i + 1))| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i ∈ Finset.range n, Bφ := Finset.sum_le_sum fun i _ => hBφ _
      _ = (n : ℝ) * Bφ := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  calc (n : ℝ)⁻¹ * |∑ i ∈ Finset.range n, φ (ω (i + 1))|
      ≤ (n : ℝ)⁻¹ * ((n : ℝ) * Bφ) := by gcongr
    _ = Bφ := by field_simp


/-- **The quadratic variation of the array converges in `L¹` to the stationary
one-step conditional variance.** -/
lemma tendsto_quadVar (P : Kernel X X) [IsMarkovKernel P] (π : Measure X)
    [IsProbabilityMeasure π] (huni : UniformlyErgodic P π)
    (g : X → ℝ) (hg : Measurable g) (Cg : ℝ) (hCg : ∀ x, |g x| ≤ Cg) (hCg0 : 0 ≤ Cg) :
    Tendsto (fun n : ℕ => ∫ ω, |(∑ k ∈ Finset.range n, (mdsArray P g n k ω) ^ 2)
        - ∫ x, stepVar P g x ∂π| ∂(chainMeasure P π)) atTop (𝓝 0) := by
  have hqm : Measurable (stepVar P g) := measurable_stepVar P g hg
  have hqb : ∀ x, |stepVar P g x| ≤ 2 * Cg ^ 2 := fun x => abs_stepVar_le P g hg Cg hCg x
  have hq2 : (0 : ℝ) ≤ 2 * Cg ^ 2 := by positivity
  obtain ⟨K, hK0, hK⟩ :=
    integral_sq_sampleAvg_sub_le P π huni π (stepVar P g) hqm (2 * Cg ^ 2) hqb
  have hSb : |∫ x, stepVar P g x ∂π| ≤ 2 * Cg ^ 2 := by
    have hint : Integrable (stepVar P g) π := integrable_of_bounded π _ hqm (2 * Cg ^ 2) hqb
    calc |∫ x, stepVar P g x ∂π| ≤ ∫ x, |stepVar P g x| ∂π := abs_integral_le_integral_abs
      _ ≤ ∫ _x, 2 * Cg ^ 2 ∂π := integral_mono hint.abs (integrable_const _) hqb
      _ = 2 * Cg ^ 2 := by simp
  have hsam : ∀ n : ℕ, Measurable (fun ω : ℕ → X => sampleAvg (stepVar P g) n ω) := fun n =>
    (Finset.measurable_sum _ fun i _ => hqm.comp (measurable_pi_apply _)).const_mul _
  have hdiffb : ∀ (n : ℕ) (ω : ℕ → X),
      |sampleAvg (stepVar P g) n ω - ∫ x, stepVar P g x ∂π| ≤ 4 * Cg ^ 2 := by
    intro n ω
    have hab := abs_add_le (sampleAvg (stepVar P g) n ω) (-(∫ x, stepVar P g x ∂π))
    rw [abs_neg] at hab
    calc |sampleAvg (stepVar P g) n ω - ∫ x, stepVar P g x ∂π|
        ≤ |sampleAvg (stepVar P g) n ω| + |∫ x, stepVar P g x ∂π| := by
          simpa only [sub_eq_add_neg] using hab
      _ ≤ 2 * Cg ^ 2 + 2 * Cg ^ 2 :=
          add_le_add (abs_sampleAvg_le (stepVar P g) (2 * Cg ^ 2) hqb hq2 n ω) hSb
      _ = 4 * Cg ^ 2 := by ring
  have hbnd : ∀ n : ℕ, 1 ≤ n →
      ∫ ω, |(∑ k ∈ Finset.range n, (mdsArray P g n k ω) ^ 2)
          - ∫ x, stepVar P g x ∂π| ∂(chainMeasure P π)
        ≤ Real.sqrt ((6 * Cg ^ 2) ^ 2 / (n : ℝ)) + 3 * (2 * Cg ^ 2) / (n : ℝ)
          + Real.sqrt (K / (n : ℝ)) := by
    intro n hn
    have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have hpt : ∀ ω : ℕ → X,
        |(∑ k ∈ Finset.range n, (mdsArray P g n k ω) ^ 2) - ∫ x, stepVar P g x ∂π|
          ≤ |mdsAvg P g n ω| + 3 * (2 * Cg ^ 2) / (n : ℝ)
            + |sampleAvg (stepVar P g) n ω - ∫ x, stepVar P g x ∂π| := by
      intro ω
      have h1 := sum_sq_mdsArray P g n hn ω
      have h2 : ∑ j ∈ Finset.range (n - 1), sqIncr P g j ω
          = (∑ j ∈ Finset.range (n - 1), mdsVar P g j ω)
            + ∑ j ∈ Finset.range (n - 1), stepVar P g (ω j) := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun j _ => ?_
        simp [mdsVar]
      have h3 := sum_shift_boundary (stepVar P g) n hn ω
      have hsplit : (∑ k ∈ Finset.range n, (mdsArray P g n k ω) ^ 2)
          = mdsAvg P g n ω
            + (n : ℝ)⁻¹ * (∑ j ∈ Finset.range (n - 1), stepVar P g (ω j)) := by
        rw [h1, h2, mul_add, mdsAvg]
      have hR : (n : ℝ)⁻¹ * (∑ j ∈ Finset.range (n - 1), stepVar P g (ω j))
          - sampleAvg (stepVar P g) n ω
          = (n : ℝ)⁻¹ * (stepVar P g (ω 0) - stepVar P g (ω (n - 1))
              - stepVar P g (ω n)) := by
        rw [sampleAvg, ← mul_sub, h3]
      have hb3 : |stepVar P g (ω 0) - stepVar P g (ω (n - 1)) - stepVar P g (ω n)|
          ≤ 3 * (2 * Cg ^ 2) := by
        have h0 := abs_le.1 (hqb (ω 0))
        have h1' := abs_le.1 (hqb (ω (n - 1)))
        have h2' := abs_le.1 (hqb (ω n))
        rw [abs_le]
        constructor <;> linarith [h0.1, h0.2, h1'.1, h1'.2, h2'.1, h2'.2]
      have hRb : |(n : ℝ)⁻¹ * (∑ j ∈ Finset.range (n - 1), stepVar P g (ω j))
          - sampleAvg (stepVar P g) n ω| ≤ 3 * (2 * Cg ^ 2) / (n : ℝ) := by
        rw [hR, abs_mul, abs_of_nonneg (le_of_lt (inv_pos.2 hn0))]
        calc (n : ℝ)⁻¹ * |stepVar P g (ω 0) - stepVar P g (ω (n - 1)) - stepVar P g (ω n)|
            ≤ (n : ℝ)⁻¹ * (3 * (2 * Cg ^ 2)) := by gcongr
          _ = 3 * (2 * Cg ^ 2) / (n : ℝ) := by field_simp
      rw [hsplit]
      have htri : |mdsAvg P g n ω
            + (n : ℝ)⁻¹ * (∑ j ∈ Finset.range (n - 1), stepVar P g (ω j))
            - ∫ x, stepVar P g x ∂π|
          ≤ |mdsAvg P g n ω|
            + |(n : ℝ)⁻¹ * (∑ j ∈ Finset.range (n - 1), stepVar P g (ω j))
              - sampleAvg (stepVar P g) n ω|
            + |sampleAvg (stepVar P g) n ω - ∫ x, stepVar P g x ∂π| := by
        have e : mdsAvg P g n ω
              + (n : ℝ)⁻¹ * (∑ j ∈ Finset.range (n - 1), stepVar P g (ω j))
              - ∫ x, stepVar P g x ∂π
            = (mdsAvg P g n ω
                + ((n : ℝ)⁻¹ * (∑ j ∈ Finset.range (n - 1), stepVar P g (ω j))
                  - sampleAvg (stepVar P g) n ω))
              + (sampleAvg (stepVar P g) n ω - ∫ x, stepVar P g x ∂π) := by ring
        rw [e]
        have t1 := abs_add_le (mdsAvg P g n ω
            + ((n : ℝ)⁻¹ * (∑ j ∈ Finset.range (n - 1), stepVar P g (ω j))
              - sampleAvg (stepVar P g) n ω))
            (sampleAvg (stepVar P g) n ω - ∫ x, stepVar P g x ∂π)
        have t2 := abs_add_le (mdsAvg P g n ω)
            ((n : ℝ)⁻¹ * (∑ j ∈ Finset.range (n - 1), stepVar P g (ω j))
              - sampleAvg (stepVar P g) n ω)
        linarith
      linarith [htri, hRb]
    -- integrate the pointwise bound
    have hm1 : Measurable (fun ω : ℕ → X => |mdsAvg P g n ω|) :=
      (measurable_mdsAvg P g hg n).abs
    have hm3 : Measurable (fun ω : ℕ → X =>
        |sampleAvg (stepVar P g) n ω - ∫ x, stepVar P g x ∂π|) :=
      ((hsam n).sub measurable_const).abs
    have hi1 : Integrable (fun ω : ℕ → X => |mdsAvg P g n ω|) (chainMeasure P π) :=
      integrable_of_bounded _ _ hm1 (6 * Cg ^ 2)
        (fun ω => by rw [abs_abs]; exact abs_mdsAvg_le P g hg Cg hCg hCg0 n ω)
    have hi3 : Integrable (fun ω : ℕ → X =>
        |sampleAvg (stepVar P g) n ω - ∫ x, stepVar P g x ∂π|) (chainMeasure P π) :=
      integrable_of_bounded _ _ hm3 (4 * Cg ^ 2)
        (fun ω => by rw [abs_abs]; exact hdiffb n ω)
    have hi12 : Integrable (fun ω : ℕ → X =>
        |mdsAvg P g n ω| + 3 * (2 * Cg ^ 2) / (n : ℝ)) (chainMeasure P π) :=
      hi1.fun_add (integrable_const _)
    have hiR : Integrable (fun ω : ℕ → X => |mdsAvg P g n ω| + 3 * (2 * Cg ^ 2) / (n : ℝ)
        + |sampleAvg (stepVar P g) n ω - ∫ x, stepVar P g x ∂π|) (chainMeasure P π) :=
      hi12.fun_add hi3
    have hmL : Measurable (fun ω : ℕ → X =>
        |(∑ k ∈ Finset.range n, (mdsArray P g n k ω) ^ 2)
          - ∫ x, stepVar P g x ∂π|) :=
      ((Finset.measurable_sum _ fun k _ =>
        (measurable_mdsArray P g hg n k).pow_const 2).sub measurable_const).abs
    have hiL : Integrable (fun ω : ℕ → X =>
        |(∑ k ∈ Finset.range n, (mdsArray P g n k ω) ^ 2)
          - ∫ x, stepVar P g x ∂π|) (chainMeasure P π) :=
      hiR.mono' hmL.aestronglyMeasurable
        (Filter.Eventually.of_forall fun ω => by
          rw [Real.norm_eq_abs, abs_abs]; exact hpt ω)
    have hstep : ∫ ω, |(∑ k ∈ Finset.range n, (mdsArray P g n k ω) ^ 2)
          - ∫ x, stepVar P g x ∂π| ∂(chainMeasure P π)
        ≤ ∫ ω, (|mdsAvg P g n ω| + 3 * (2 * Cg ^ 2) / (n : ℝ)
            + |sampleAvg (stepVar P g) n ω - ∫ x, stepVar P g x ∂π|) ∂(chainMeasure P π) :=
      integral_mono hiL hiR hpt
    have hcomp : ∫ ω, (|mdsAvg P g n ω| + 3 * (2 * Cg ^ 2) / (n : ℝ)
          + |sampleAvg (stepVar P g) n ω - ∫ x, stepVar P g x ∂π|) ∂(chainMeasure P π)
        = (∫ ω, |mdsAvg P g n ω| ∂(chainMeasure P π)) + 3 * (2 * Cg ^ 2) / (n : ℝ)
          + ∫ ω, |sampleAvg (stepVar P g) n ω - ∫ x, stepVar P g x ∂π| ∂(chainMeasure P π) := by
      rw [integral_add hi12 hi3, integral_add hi1 (integrable_const _), integral_const]
      simp
    rw [hcomp] at hstep
    have hA := integral_abs_mdsAvg_le P π g hg Cg hCg hCg0 n hn
    have hB : ∫ ω, |sampleAvg (stepVar P g) n ω - ∫ x, stepVar P g x ∂π| ∂(chainMeasure P π)
        ≤ Real.sqrt (K / (n : ℝ)) := by
      refine le_trans (integral_abs_le_sqrt_integral_sq (chainMeasure P π) _
        ((hsam n).sub measurable_const) (4 * Cg ^ 2) (fun ω => hdiffb n ω)) ?_
      exact Real.sqrt_le_sqrt (hK n hn)
    linarith [hstep, hA, hB]
  have hb1 : Tendsto (fun n : ℕ => Real.sqrt ((6 * Cg ^ 2) ^ 2 / (n : ℝ))) atTop (𝓝 0) := by
    have h := (tendsto_const_div_atTop_nhds_zero_nat ((6 * Cg ^ 2) ^ 2)).sqrt
    simpa using h
  have hb2 : Tendsto (fun n : ℕ => 3 * (2 * Cg ^ 2) / (n : ℝ)) atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat _
  have hb3 : Tendsto (fun n : ℕ => Real.sqrt (K / (n : ℝ))) atTop (𝓝 0) := by
    have h := (tendsto_const_div_atTop_nhds_zero_nat K).sqrt
    simpa using h
  have hbnd0 : Tendsto (fun n : ℕ => Real.sqrt ((6 * Cg ^ 2) ^ 2 / (n : ℝ))
      + 3 * (2 * Cg ^ 2) / (n : ℝ) + Real.sqrt (K / (n : ℝ))) atTop (𝓝 0) := by
    have h := (hb1.add hb2).add hb3
    simpa using h
  refine squeeze_zero' ?_ ?_ hbnd0
  · filter_upwards with n using integral_nonneg fun ω => abs_nonneg _
  · filter_upwards [eventually_ge_atTop 1] with n hn using hbnd n hn


/-! ### Part 6: the CLT with identified variance, and the conclusion -/

lemma tendsto_inv_sqrt_nat : Tendsto (fun n : ℕ => (Real.sqrt (n : ℝ))⁻¹) atTop (𝓝 0) := by
  have h := (tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ)).sqrt
  simp only [Real.sqrt_zero] at h
  refine h.congr fun n => ?_
  rw [one_div, Real.sqrt_inv]

lemma scaled_sampleAvg_eq (f : X → ℝ) (c : ℝ) (n : ℕ) (hn : 1 ≤ n) (ω : ℕ → X) :
    Real.sqrt n * (sampleAvg f n ω - c)
      = (Real.sqrt n)⁻¹ * ∑ i ∈ Finset.range n, (f (ω (i + 1)) - c) := by
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  set t : ℝ := Real.sqrt (n : ℝ) with ht
  have ht0 : t ≠ 0 := by rw [ht]; positivity
  have hmul : t * t = (n : ℝ) := Real.mul_self_sqrt (le_of_lt hn0)
  have key : t * (n : ℝ)⁻¹ = t⁻¹ := by rw [← hmul]; field_simp
  have key2 : t⁻¹ * ((n : ℝ) * c) = t * c := by
    rw [← hmul]; field_simp
  have hR : t⁻¹ * ∑ i ∈ Finset.range n, (f (ω (i + 1)) - c)
      = t⁻¹ * (∑ i ∈ Finset.range n, f (ω (i + 1))) - t⁻¹ * ((n : ℝ) * c) := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_sub]
  rw [hR, key2, sampleAvg, mul_sub, ← mul_assoc, key]

lemma abs_scaled_sub_sum_mdsArray (P : Kernel X X) [IsMarkovKernel P] (f : X → ℝ) (c : ℝ)
    (g : X → ℝ) (hg : Measurable g) (Cg : ℝ) (hCg : ∀ x, |g x| ≤ Cg)
    (hpois : ∀ x, g x - kerMean P g x = f x - c) (n : ℕ) (hn : 1 ≤ n) (ω : ℕ → X) :
    |Real.sqrt n * (sampleAvg f n ω - c) - ∑ k ∈ Finset.range n, mdsArray P g n k ω|
      ≤ (Real.sqrt n)⁻¹ * (4 * Cg) := by
  have hsinv : (0 : ℝ) ≤ (Real.sqrt (n : ℝ))⁻¹ := by positivity
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  set K : X → ℝ := kerMean P g with hK
  have hsum2 : ∑ k ∈ Finset.range (m + 1), mdsArray P g (m + 1) k ω
      = (Real.sqrt ((m + 1 : ℕ) : ℝ))⁻¹
        * ∑ j ∈ Finset.range m, (g (ω (j + 1)) - K (ω j)) := by
    rw [Finset.sum_range_succ', mdsArray_zero, add_zero, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => rfl
  rw [scaled_sampleAvg_eq f c (m + 1) hn ω, hsum2, ← mul_sub, abs_mul,
    abs_of_nonneg hsinv]
  refine mul_le_mul_of_nonneg_left ?_ hsinv
  have hf0 : ∀ i : ℕ, f (ω (i + 1)) - c = g (ω (i + 1)) - K (ω (i + 1)) := fun i =>
    (hpois (ω (i + 1))).symm
  have hS1 : ∑ i ∈ Finset.range (m + 1), (f (ω (i + 1)) - c)
      = (∑ i ∈ Finset.range (m + 1), g (ω (i + 1)))
        - ∑ i ∈ Finset.range (m + 1), K (ω (i + 1)) := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => hf0 i
  have hS2 : ∑ j ∈ Finset.range m, (g (ω (j + 1)) - K (ω j))
      = (∑ j ∈ Finset.range m, g (ω (j + 1))) - ∑ j ∈ Finset.range m, K (ω j) := by
    rw [Finset.sum_sub_distrib]
  have ha : ∑ i ∈ Finset.range (m + 1), g (ω (i + 1))
      = (∑ i ∈ Finset.range m, g (ω (i + 1))) + g (ω (m + 1)) := Finset.sum_range_succ _ _
  have hb1 : ∑ j ∈ Finset.range (m + 1), K (ω j)
      = (∑ i ∈ Finset.range m, K (ω (i + 1))) + K (ω 0) := Finset.sum_range_succ' _ _
  have hb2 : ∑ j ∈ Finset.range (m + 1), K (ω j)
      = (∑ j ∈ Finset.range m, K (ω j)) + K (ω m) := Finset.sum_range_succ _ _
  have hb3 : ∑ i ∈ Finset.range (m + 1), K (ω (i + 1))
      = (∑ i ∈ Finset.range m, K (ω (i + 1))) + K (ω (m + 1)) := Finset.sum_range_succ _ _
  have hdiff : (∑ i ∈ Finset.range (m + 1), (f (ω (i + 1)) - c))
      - ∑ j ∈ Finset.range m, (g (ω (j + 1)) - K (ω j))
      = g (ω (m + 1)) - K (ω m) - K (ω (m + 1)) + K (ω 0) := by
    rw [hS1, hS2, ha, hb3]
    linarith [hb1, hb2]
  rw [hdiff]
  have e0 := abs_le.1 (hCg (ω (m + 1)))
  have e1 := abs_le.1 (abs_kerMean_le P g hg Cg hCg (ω m))
  have e2 := abs_le.1 (abs_kerMean_le P g hg Cg hCg (ω (m + 1)))
  have e3 := abs_le.1 (abs_kerMean_le P g hg Cg hCg (ω 0))
  rw [abs_le]
  constructor <;> linarith [e0.1, e0.2, e1.1, e1.2, e2.1, e2.2, e3.1, e3.2]


/-- **The CLT for a bounded observable of a uniformly ergodic chain, with the asymptotic
variance identified as the autocovariance series.**  Proved by the Poisson-equation
martingale decomposition together with the martingale central limit theorem. -/
theorem clt_asymptoticVariance_of_bounded (P : Kernel X X) [IsMarkovKernel P] (π : Measure X)
    [IsProbabilityMeasure π] (hinv : Kernel.Invariant P π) (huni : UniformlyErgodic P π)
    (f : X → ℝ) (hf : Measurable f) (B : ℝ) (hB : ∀ x, |f x| ≤ B) :
    0 ≤ asymptoticVariance P π f ∧
    TendstoInDistribution
      (fun (n : ℕ) (ω : ℕ → X) => Real.sqrt n * (sampleAvg f n ω - ∫ x, f x ∂π))
      atTop (id : ℝ → ℝ) (fun _ => chainMeasure P π)
      (gaussianReal 0 (asymptoticVariance P π f).toNNReal) := by
  obtain ⟨g, hgm, ⟨Cg0, hCgb⟩, hpois⟩ :=
    poissonEquation_of_bounded_of_uniformlyErgodic P π huni f hf B hB
  set Cg : ℝ := |Cg0| with hCgdef
  have hCg : ∀ x, |g x| ≤ Cg := fun x => le_trans (hCgb x) (le_abs_self _)
  have hCg0 : 0 ≤ Cg := abs_nonneg _
  have hpois' : ∀ x, g x - kerMean P g x = f x - ∫ y, f y ∂π := hpois
  have hσ2nn : 0 ≤ ∫ x, stepVar P g x ∂π :=
    integral_nonneg fun x => stepVar_nonneg P g hgm Cg hCg x
  have hg2b : ∀ x, |(g x) ^ 2| ≤ Cg ^ 2 := sq_bound_of_abs_bound hCg
  have hkb : ∀ x, |kerMean P g x| ≤ Cg := fun x => abs_kerMean_le P g hgm Cg hCg x
  have hg2int : Integrable (fun x => (g x) ^ 2) π :=
    integrable_of_bounded π _ (hgm.pow_const 2) (Cg ^ 2) hg2b
  have hkg2 : Integrable (fun x => kerMean P (fun y => (g y) ^ 2) x) π :=
    integrable_of_bounded π _ (measurable_kerMean P _ (hgm.pow_const 2)) (Cg ^ 2)
      (fun x => abs_kerMean_le P _ (hgm.pow_const 2) (Cg ^ 2) hg2b x)
  have hPg2 : Integrable (fun x => (kerMean P g x) ^ 2) π :=
    integrable_of_bounded π _ ((measurable_kerMean P g hgm).pow_const 2) (Cg ^ 2)
      (fun x => sq_bound_of_abs_bound hkb x)
  have hPeq : (⇑P ∘ₘ π) = π := hinv
  have hcomp : ∫ x, kerMean P (fun y => (g y) ^ 2) x ∂π = ∫ x, (g x) ^ 2 ∂π := by
    have h := integral_comp_measure P π (fun y => (g y) ^ 2) (by rw [hPeq]; exact hg2int)
    rw [hPeq] at h
    exact h.symm
  have hvarid : ∫ x, stepVar P g x ∂π = asymptoticVariance P π f := by
    have hsplit : ∫ x, stepVar P g x ∂π
        = (∫ x, kerMean P (fun y => (g y) ^ 2) x ∂π) - ∫ x, (kerMean P g x) ^ 2 ∂π := by
      simp only [stepVar]
      exact integral_sub hkg2 hPg2
    rw [hsplit, hcomp,
      asymptoticVariance_of_poisson P π hinv huni f hf B hB g hgm Cg hCg hpois']
  refine ⟨hvarid ▸ hσ2nn, ?_⟩
  set σ : ℝ := Real.sqrt (∫ x, stepVar P g x ∂π) with hσdef
  have hσsq : σ ^ 2 = ∫ x, stepVar P g x ∂π := Real.sq_sqrt hσ2nn
  have hM : ∀ (n : ℕ) (ω : ℕ → X),
      ∑ k ∈ Finset.range n, (mdsArray P g n k ω) ^ 2 ≤ 4 * Cg ^ 2 := by
    intro n ω
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h
      simp only [Finset.range_zero, Finset.sum_empty]
      positivity
    rw [sum_sq_mdsArray P g n h ω]
    have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast h
    have hm : ((n - 1 : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.sub_le n 1
    have hsum : ∑ j ∈ Finset.range (n - 1), sqIncr P g j ω
        ≤ ((n - 1 : ℕ) : ℝ) * (4 * Cg ^ 2) := by
      calc ∑ j ∈ Finset.range (n - 1), sqIncr P g j ω
          ≤ ∑ _j ∈ Finset.range (n - 1), 4 * Cg ^ 2 :=
            Finset.sum_le_sum fun j _ =>
              le_trans (le_abs_self _) (abs_sqIncr_le P g hgm Cg hCg j ω)
        _ = ((n - 1 : ℕ) : ℝ) * (4 * Cg ^ 2) := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    calc (n : ℝ)⁻¹ * ∑ j ∈ Finset.range (n - 1), sqIncr P g j ω
        ≤ (n : ℝ)⁻¹ * (((n - 1 : ℕ) : ℝ) * (4 * Cg ^ 2)) := by gcongr
      _ ≤ (n : ℝ)⁻¹ * ((n : ℝ) * (4 * Cg ^ 2)) := by gcongr
      _ = 4 * Cg ^ 2 := by field_simp
  have hmart := Martingale.clt_of_bounded_mds_array (chainMeasure P π) (pathFilt X)
    (mdsArray P g)
    (fun n k => measurable_mdsArray P g hgm n k)
    (fun n k => (adapted_mdsArray P g hgm n k).measurable)
    (fun n k => integrable_of_bounded _ _ (measurable_mdsArray P g hgm n k)
      ((Real.sqrt (n : ℝ))⁻¹ * (2 * Cg)) (abs_mdsArray_le P g hgm Cg hCg hCg0 n k))
    (fun n k => condExp_mdsArray P π g hgm Cg hCg n k)
    (fun n => by simp [mdsArray_zero])
    (fun n : ℕ => (Real.sqrt (n : ℝ))⁻¹ * (2 * Cg))
    (fun n k ω => abs_mdsArray_le P g hgm Cg hCg hCg0 n k ω)
    (by simpa using tendsto_inv_sqrt_nat.mul_const (2 * Cg))
    (4 * Cg ^ 2) hM σ
    (by rw [hσsq]; exact tendsto_quadVar P π huni g hgm Cg hCg hCg0)
  have hσA : σ ^ 2 = asymptoticVariance P π f := by rw [hσsq, hvarid]
  rw [hσA] at hmart
  have hYm : ∀ n : ℕ, Measurable (fun ω : ℕ → X =>
      Real.sqrt (n : ℝ) * (sampleAvg f n ω - ∫ x, f x ∂π)) := by
    intro n
    exact (((Finset.measurable_sum _ fun i _ =>
      hf.comp (measurable_pi_apply (i + 1))).const_mul _).sub measurable_const).const_mul _
  have htim : TendstoInMeasure (chainMeasure P π)
      ((fun (n : ℕ) (ω : ℕ → X) => Real.sqrt (n : ℝ) * (sampleAvg f n ω - ∫ x, f x ∂π))
        - fun (n : ℕ) (ω : ℕ → X) => ∑ k ∈ Finset.range n, mdsArray P g n k ω)
      atTop 0 := by
    refine tendstoInMeasure_of_ne_top ?_
    intro εe hεe hεtop
    set ε : ℝ := εe.toReal with hεdef
    have hε : 0 < ε := ENNReal.toReal_pos hεe.ne' hεtop
    have hlim : Tendsto (fun n : ℕ => (Real.sqrt (n : ℝ))⁻¹ * (4 * Cg)) atTop (𝓝 0) := by
      simpa using tendsto_inv_sqrt_nat.mul_const (4 * Cg)
    have hev : ∀ᶠ n : ℕ in atTop, (Real.sqrt (n : ℝ))⁻¹ * (4 * Cg) < ε :=
      hlim.eventually (gt_mem_nhds hε)
    have hzero : Tendsto (fun _ : ℕ => (0 : ℝ≥0∞)) atTop (𝓝 0) := tendsto_const_nhds
    refine Filter.Tendsto.congr' ?_ hzero
    filter_upwards [hev, eventually_ge_atTop 1] with n hn hn1
    refine (measure_mono_null (fun ω hω => ?_) measure_empty).symm
    simp only [Set.mem_setOf_eq, Pi.sub_apply, Pi.zero_apply, edist_dist, Real.dist_eq,
      sub_zero] at hω
    have h1 : εe.toReal ≤ (ENNReal.ofReal |Real.sqrt (n : ℝ)
        * (sampleAvg f n ω - ∫ x, f x ∂π)
        - ∑ k ∈ Finset.range n, mdsArray P g n k ω|).toReal :=
      ENNReal.toReal_mono ENNReal.ofReal_ne_top hω
    rw [ENNReal.toReal_ofReal (abs_nonneg _)] at h1
    have hb := abs_scaled_sub_sum_mdsArray P f (∫ x, f x ∂π) g hgm Cg hCg hpois' n hn1 ω
    exact absurd (lt_of_le_of_lt (le_trans h1 hb) hn) (lt_irrefl ε)
  exact tendstoInDistribution_of_tendstoInMeasure_sub _ (id : ℝ → ℝ) hmart htim
    (fun n => (hYm n).aemeasurable)


/-- **Identification of the CLT limit variance for a bounded observable.** -/
theorem asymptoticVariance_eq_of_clt_of_bounded' (P : Kernel X X) [IsMarkovKernel P]
    (π : Measure X) [IsProbabilityMeasure π] (hP : HarrisErgodic P π)
    (huni : UniformlyErgodic P π) (f : X → ℝ) (hf : Measurable f) (B : ℝ)
    (hB : ∀ x, |f x| ≤ B) (v : ℝ≥0)
    (hclt : TendstoInDistribution
      (fun (n : ℕ) (ω : ℕ → X) => Real.sqrt n * (sampleAvg f n ω - ∫ x, f x ∂π))
      atTop (id : ℝ → ℝ) (fun _ => chainMeasure P π) (gaussianReal 0 v)) :
    (v : ℝ) = asymptoticVariance P π f := by
  obtain ⟨hnn, hclt2⟩ := clt_asymptoticVariance_of_bounded P π hP.1 huni f hf B hB
  have hYm : ∀ n : ℕ, Measurable (fun ω : ℕ → X =>
      Real.sqrt (n : ℝ) * (sampleAvg f n ω - ∫ x, f x ∂π)) := by
    intro n
    exact (((Finset.measurable_sum _ fun i _ =>
      hf.comp (measurable_pi_apply (i + 1))).const_mul _).sub measurable_const).const_mul _
  have hkey := abs_exp_variance_sub_le_of_tendstoInDistribution (chainMeasure P π)
    (fun (n : ℕ) (ω : ℕ → X) => Real.sqrt (n : ℝ) * (sampleAvg f n ω - ∫ x, f x ∂π))
    (fun (n : ℕ) (ω : ℕ → X) => Real.sqrt (n : ℝ) * (sampleAvg f n ω - ∫ x, f x ∂π))
    v ((asymptoticVariance P π f).toNNReal) 0 hYm hYm hclt hclt2
    (fun n => by simp) (fun n => by simp)
  have hz : Real.exp (-(v : ℝ) / 2)
      - Real.exp (-((asymptoticVariance P π f).toNNReal : ℝ) / 2) = 0 :=
    abs_eq_zero.1 (le_antisymm hkey (abs_nonneg _))
  have heq : (-(v : ℝ) / 2) = (-((asymptoticVariance P π f).toNNReal : ℝ) / 2) :=
    Real.exp_eq_exp.1 (sub_eq_zero.1 hz)
  have hvv : (v : ℝ) = ((asymptoticVariance P π f).toNNReal : ℝ) := by linarith
  rw [hvv, Real.coe_toNNReal _ hnn]

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
  MarkovChainCLT.asymptoticVariance_eq_of_clt_of_bounded' P π hP huni f hf B hB v hclt
