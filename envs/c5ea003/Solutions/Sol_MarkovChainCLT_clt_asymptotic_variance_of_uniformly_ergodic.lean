-- Prove2me | solution 1 for MarkovChainCLT.clt_asymptotic_variance_of_uniformly_ergodic
-- status  : ACCEPTED   (prove)
-- author  : @LukeBernese
-- created : 2026-08-21T17:27:15.621721+00:00
-- url     : https://prove2.me/submissions/84660cd8-dda5-4b32-8ac9-60ff015e60d1

import Definitions.Def_MarkovAsymptoticVariance
import Definitions.Def_MarkovErgodicity
import Definitions.Def_MarkovChainPathMeasure
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.Probability.Moments.Variance
import Theorems.Thm_MarkovChainCLT_integral_sq_iterKernel_pow_le
import Theorems.Thm_MarkovChainCLT_exists_lag_tvDist_le_of_uniformlyErgodic
import Theorems.Thm_MarkovChainCLT_clt_of_uniformly_ergodic
import Theorems.Thm_MarkovChainCLT_asymptoticVariance_eq_of_clt

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

end MarkovChainCLT

open MarkovChainCLT in
theorem solution {X : Type*} [MeasurableSpace X]
    (P : Kernel X X) [IsMarkovKernel P] (π : Measure X) [IsProbabilityMeasure π]
    (hP : MarkovChainCLT.HarrisErgodic P π)
    (huni : MarkovChainCLT.UniformlyErgodic P π)
    (f : X → ℝ) (hf : Measurable f) (hL2 : MemLp f 2 π) :
    Summable (fun k : ℕ => MarkovChainCLT.lagCovariance P π f f (k + 1)) ∧
    0 ≤ MarkovChainCLT.asymptoticVariance P π f ∧
    ∀ (lam : Measure X) [IsProbabilityMeasure lam],
      TendstoInDistribution
        (fun (n : ℕ) (ω : ℕ → X) =>
          Real.sqrt n * (MarkovChainCLT.sampleAvg f n ω - ∫ x, f x ∂π))
        atTop (id : ℝ → ℝ) (fun _ => MarkovChainCLT.chainMeasure P lam)
        (gaussianReal 0 (MarkovChainCLT.asymptoticVariance P π f).toNNReal) := by
  have hinv : Kernel.Invariant P π := hP.1
  obtain ⟨v, hv⟩ := MarkovChainCLT.clt_of_uniformly_ergodic P π hP f hf huni hL2
  have hveq : (v : ℝ) = MarkovChainCLT.asymptoticVariance P π f :=
    MarkovChainCLT.asymptoticVariance_eq_of_clt P π hP huni f hf hL2 v (hv π)
  have hnn : (MarkovChainCLT.asymptoticVariance P π f).toNNReal = v := by
    rw [← hveq]; exact Real.toNNReal_coe
  refine ⟨summable_lagCovariance_of_uniformlyErgodic P π hinv huni f hf hL2, ?_, ?_⟩
  · rw [← hveq]; exact v.coe_nonneg
  · intro lam _
    rw [hnn]
    exact hv lam
