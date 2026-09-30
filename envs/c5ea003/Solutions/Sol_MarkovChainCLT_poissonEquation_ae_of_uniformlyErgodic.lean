-- Prove2me | solution 1 for MarkovChainCLT.poissonEquation_ae_of_uniformlyErgodic
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:40:16.689856+00:00
-- url     : https://prove2.me/submissions/5dd37a55-2152-4edc-96ad-dba3c6f11481

import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Probability.Kernel.Invariance
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_MarkovIterKernel
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.Algebra.InfiniteSum.Module
import Theorems.Thm_MarkovChainCLT_integral_sq_iterKernel_pow_le
import Theorems.Thm_MarkovChainCLT_exists_lag_tvDist_le_of_uniformlyErgodic
import Mathlib.MeasureTheory.Function.LpSpace.Complete

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace KernelL2

variable {X : Type*} [MeasurableSpace X]

theorem integral_sq_bound (μ : Measure X) [IsProbabilityMeasure μ]
    (f : X → ℝ) (hf : MemLp f 2 μ) :
    (∫ x, f x ∂μ) ^ 2 ≤ ∫ x, f x ^ 2 ∂μ := by
  have h1 : Integrable f μ := hf.integrable (by norm_num)
  have h2 : Integrable (fun x => f x ^ 2) μ := hf.integrable_sq
  let m := ∫ x, f x ∂μ
  have hnonneg : 0 ≤ ∫ x, (f x - m) ^ 2 ∂μ :=
    integral_nonneg (fun _ => sq_nonneg _)
  have heq : (fun x => (f x - m) ^ 2) =
      (fun x => f x ^ 2 - (2 * m) * f x + m ^ 2) := by
    funext x
    ring
  rw [heq] at hnonneg
  rw [integral_add (f := fun x => f x ^ 2 - (2 * m) * f x)
      (g := fun _ => m ^ 2) (h2.sub (h1.const_mul (2 * m))) (integrable_const _),
    integral_sub (f := fun x => f x ^ 2) (g := fun x => (2 * m) * f x)
      h2 (h1.const_mul (2 * m)), integral_const_mul, integral_const] at hnonneg
  simp only [probReal_univ, smul_eq_mul, one_mul] at hnonneg
  dsimp [m] at hnonneg
  nlinarith

theorem ae_integrable (P : Kernel X X) [IsMarkovKernel P]
    (π : Measure X) [IsProbabilityMeasure π] (hinv : Kernel.Invariant P π)
    {f : X → ℝ} (hf : Integrable f π) : ∀ᵐ x ∂π, Integrable f (P x) := by
  change P ∘ₘ π = π at hinv
  apply Measure.ae_integrable_of_integrable_comp
  simpa only [hinv] using hf

theorem integral_invariant (P : Kernel X X) [IsMarkovKernel P]
    (π : Measure X) [IsProbabilityMeasure π] (hinv : Kernel.Invariant P π)
    {f : X → ℝ} (hf : Integrable f π) :
    (∫ x, ∫ y, f y ∂P x ∂π) = ∫ x, f x ∂π := by
  change P ∘ₘ π = π at hinv
  have hcomp : Integrable f ((P ∘ₖ Kernel.const Unit π) ()) := by
    simpa only [← Measure.comp_eq_comp_const_apply, hinv] using hf
  simpa only [← Measure.comp_eq_comp_const_apply, hinv, Kernel.const_apply] using
    (Kernel.integral_comp hcomp).symm

theorem kernel_memLp_and_sq_bound (P : Kernel X X) [IsMarkovKernel P]
    (π : Measure X) [IsProbabilityMeasure π] (hinv : Kernel.Invariant P π)
    (f : X → ℝ) (hf : Measurable f) (h2 : MemLp f 2 π) :
    MemLp (fun x => ∫ y, f y ∂P x) 2 π ∧
      (∫ x, (∫ y, f y ∂P x) ^ 2 ∂π) ≤ ∫ x, f x ^ 2 ∂π := by
  have hmeas : Measurable (fun x => ∫ y, f y ∂P x) :=
    hf.stronglyMeasurable.integral_kernel.measurable
  have hsq : Integrable (fun x => f x ^ 2) π := h2.integrable_sq
  have hcomp : Integrable (fun x => f x ^ 2) (P ∘ₘ π) := by
    change P ∘ₘ π = π at hinv
    simpa only [hinv] using hsq
  have hi : Integrable (fun x => ∫ y, f y ^ 2 ∂P x) π := by
    simpa only [Real.norm_eq_abs, abs_sq] using
      Measure.integrable_integral_norm_of_integrable_comp hcomp
  have hj : ∀ᵐ x ∂π, (∫ y, f y ∂P x) ^ 2 ≤ ∫ y, f y ^ 2 ∂P x := by
    filter_upwards [ae_integrable P π hinv hsq] with x hx
    exact integral_sq_bound (P x) f
      ((memLp_two_iff_integrable_sq hf.aestronglyMeasurable).mpr hx)
  have hi2 : Integrable (fun x => (∫ y, f y ∂P x) ^ 2) π := by
    apply hi.mono' (hmeas.pow_const 2).aestronglyMeasurable
    filter_upwards [hj] with x hx
    simpa only [Real.norm_eq_abs, abs_sq] using hx
  refine ⟨(memLp_two_iff_integrable_sq hmeas.aestronglyMeasurable).mpr hi2, ?_⟩
  calc
    (∫ x, (∫ y, f y ∂P x) ^ 2 ∂π) ≤ ∫ x, ∫ y, f y ^ 2 ∂P x ∂π :=
      integral_mono_ae hi2 hi hj
    _ = ∫ x, f x ^ 2 ∂π := integral_invariant P π hinv hsq

theorem kernel_memLp (P : Kernel X X) [IsMarkovKernel P]
    (π : Measure X) [IsProbabilityMeasure π] (hinv : Kernel.Invariant P π)
    (f : X → ℝ) (hf : Measurable f) (h2 : MemLp f 2 π) :
    MemLp (fun x => ∫ y, f y ∂P x) 2 π :=
  (kernel_memLp_and_sq_bound P π hinv f hf h2).1

theorem norm_sq {π : Measure X} (f : Lp ℝ 2 π) : ‖f‖ ^ 2 = ∫ x, f x ^ 2 ∂π := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  congr 1
  funext x
  simp [Real.norm_eq_abs, sq_abs]

noncomputable def action (P : Kernel X X) [IsMarkovKernel P]
    (π : Measure X) [IsProbabilityMeasure π] (hinv : Kernel.Invariant P π)
    (f : Lp ℝ 2 π) : Lp ℝ 2 π :=
  (kernel_memLp P π hinv f (Lp.stronglyMeasurable f).measurable (Lp.memLp f)).toLp _

theorem action_ae (P : Kernel X X) [IsMarkovKernel P]
    (π : Measure X) [IsProbabilityMeasure π] (hinv : Kernel.Invariant P π)
    (f : Lp ℝ 2 π) :
    ⇑(action P π hinv f) =ᵐ[π] (fun x => ∫ y, f y ∂P x) :=
  MemLp.coeFn_toLp _

theorem action_norm_le (P : Kernel X X) [IsMarkovKernel P]
    (π : Measure X) [IsProbabilityMeasure π] (hinv : Kernel.Invariant P π)
    (f : Lp ℝ 2 π) : ‖action P π hinv f‖ ≤ ‖f‖ := by
  have hsq : ‖action P π hinv f‖ ^ 2 ≤ ‖f‖ ^ 2 := by
    rw [norm_sq, norm_sq]
    calc
      (∫ x, action P π hinv f x ^ 2 ∂π) = ∫ x, (∫ y, f y ∂P x) ^ 2 ∂π := by
        apply integral_congr_ae
        filter_upwards [action_ae P π hinv f] with x hx
        rw [hx]
      _ ≤ ∫ x, f x ^ 2 ∂π :=
        (kernel_memLp_and_sq_bound P π hinv f (Lp.stronglyMeasurable f).measurable
          (Lp.memLp f)).2
  nlinarith [norm_nonneg (action P π hinv f), norm_nonneg f]

theorem kernel_congr_ae (P : Kernel X X) [IsMarkovKernel P]
    (π : Measure X) [IsProbabilityMeasure π] (hinv : Kernel.Invariant P π)
    {f g : X → ℝ} (hfg : f =ᵐ[π] g) :
    (fun x => ∫ y, f y ∂P x) =ᵐ[π] (fun x => ∫ y, g y ∂P x) := by
  change P ∘ₘ π = π at hinv
  have hfg' : f =ᵐ[P ∘ₘ π] g := by simpa only [hinv] using hfg
  filter_upwards [Measure.ae_ae_of_ae_comp hfg'] with x hx
  exact integral_congr_ae hx

theorem action_add (P : Kernel X X) [IsMarkovKernel P]
    (π : Measure X) [IsProbabilityMeasure π] (hinv : Kernel.Invariant P π)
    (f g : Lp ℝ 2 π) :
    action P π hinv (f + g) = action P π hinv f + action P π hinv g := by
  apply Lp.ext
  filter_upwards [action_ae P π hinv (f + g), action_ae P π hinv f,
    action_ae P π hinv g, Lp.coeFn_add (action P π hinv f) (action P π hinv g),
    kernel_congr_ae P π hinv (Lp.coeFn_add f g),
    ae_integrable P π hinv ((Lp.memLp f).integrable (by norm_num)),
    ae_integrable P π hinv ((Lp.memLp g).integrable (by norm_num))]
      with x hsum hf hg ha hk hif hig
  rw [hsum, ha, Pi.add_apply, hf, hg, hk]
  exact integral_add hif hig

theorem action_smul (P : Kernel X X) [IsMarkovKernel P]
    (π : Measure X) [IsProbabilityMeasure π] (hinv : Kernel.Invariant P π)
    (c : ℝ) (f : Lp ℝ 2 π) :
    action P π hinv (c • f) = c • action P π hinv f := by
  apply Lp.ext
  filter_upwards [action_ae P π hinv (c • f), action_ae P π hinv f,
    Lp.coeFn_smul c (action P π hinv f),
    kernel_congr_ae P π hinv (Lp.coeFn_smul c f)] with x hcf hf ha hk
  rw [hcf, ha, Pi.smul_apply, hf, hk]
  exact integral_smul c f

noncomputable def markovOp (P : Kernel X X) [IsMarkovKernel P]
    (π : Measure X) [IsProbabilityMeasure π] (hinv : Kernel.Invariant P π) :
    Lp ℝ 2 π →L[ℝ] Lp ℝ 2 π :=
  LinearMap.mkContinuous
    { toFun := action P π hinv
      map_add' := action_add P π hinv
      map_smul' := action_smul P π hinv }
    1 (fun f => by simpa only [one_mul] using action_norm_le P π hinv f)

theorem markovOp_ae (P : Kernel X X) [IsMarkovKernel P]
    (π : Measure X) [IsProbabilityMeasure π] (hinv : Kernel.Invariant P π)
    (f : Lp ℝ 2 π) :
    ⇑(markovOp P π hinv f) =ᵐ[π] (fun x => ∫ y, f y ∂P x) :=
  action_ae P π hinv f

theorem markovOp_norm_le (P : Kernel X X) [IsMarkovKernel P]
    (π : Measure X) [IsProbabilityMeasure π] (hinv : Kernel.Invariant P π)
    (f : Lp ℝ 2 π) : ‖markovOp P π hinv f‖ ≤ ‖f‖ :=
  action_norm_le P π hinv f

theorem norm_markovOp_le (P : Kernel X X) [IsMarkovKernel P]
    (π : Measure X) [IsProbabilityMeasure π] (hinv : Kernel.Invariant P π) :
    ‖markovOp P π hinv‖ ≤ 1 :=
  (markovOp P π hinv).opNorm_le_bound zero_le_one
    (fun f => by simpa only [one_mul] using markovOp_norm_le P π hinv f)

end KernelL2

open MeasureTheory ProbabilityTheory MarkovChainCLT
open scoped ENNReal NNReal

namespace KernelPowers

variable {X : Type*} [MeasurableSpace X]

theorem invariant_iterKernel (P : Kernel X X) [IsMarkovKernel P]
    (π : Measure X) (hinv : Kernel.Invariant P π) (n : ℕ) :
    Kernel.Invariant (iterKernel P n) π := by
  induction n with
  | zero =>
      change π.bind (fun x => Measure.dirac x) = π
      exact Measure.bind_dirac
  | succ n ih =>
      exact hinv.comp ih

theorem markovOp_pow_ae (P : Kernel X X) [IsMarkovKernel P]
    (π : Measure X) [IsProbabilityMeasure π] (hinv : Kernel.Invariant P π)
    (n : ℕ) (f : Lp ℝ 2 π) :
    ⇑((KernelL2.markovOp P π hinv ^ n) f) =ᵐ[π]
      (fun x => ∫ y, f y ∂iterKernel P n x) := by
  induction n generalizing f with
  | zero =>
      apply Filter.Eventually.of_forall
      intro x
      simp only [pow_zero, ContinuousLinearMap.one_apply, iterKernel_zero,
        Kernel.id_apply, integral_dirac' f x (Lp.stronglyMeasurable f)]
  | succ n ih =>
      have hn := invariant_iterKernel P π hinv n
      have hsucc := invariant_iterKernel P π hinv (n + 1)
      filter_upwards [ih (KernelL2.markovOp P π hinv f),
        KernelL2.kernel_congr_ae (iterKernel P n) π hn (KernelL2.markovOp_ae P π hinv f),
        KernelL2.ae_integrable (iterKernel P (n + 1)) π hsucc
          ((Lp.memLp f).integrable (by norm_num))] with x hx hrep hInt
      rw [pow_succ, ContinuousLinearMap.mul_apply, hx, hrep, iterKernel_succ]
      exact (Kernel.integral_comp hInt).symm

end KernelPowers

namespace BlockResolvent

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem finite_telescope (A : E →L[ℝ] E) (s : E) (N : ℕ) :
    (∑ i ∈ Finset.range N, (A ^ i) s) - A (∑ i ∈ Finset.range N, (A ^ i) s) =
      s - (A ^ N) s := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, map_add]
    calc
      _ = ((∑ i ∈ Finset.range N, (A ^ i) s) -
          A (∑ i ∈ Finset.range N, (A ^ i) s)) +
          ((A ^ N) s - A ((A ^ N) s)) := by abel
      _ = s - (A ^ (N + 1)) s := by
        rw [ih, pow_succ']
        simp only [ContinuousLinearMap.mul_apply]
        abel

theorem exists_sub_apply_of_summable_blocks (A : E →L[ℝ] E) (h : E) (N : ℕ)
    (hs : Summable (fun j : ℕ => (A ^ (j * N)) h)) :
    ∃ g : E, g - A g = h := by
  let s : E := ∑' j : ℕ, (A ^ (j * N)) h
  have hshift : (A ^ N) s = ∑' j : ℕ, (A ^ ((j + 1) * N)) h := by
    rw [show s = ∑' j : ℕ, (A ^ (j * N)) h from rfl, (A ^ N).map_tsum hs]
    congr 1
    funext j
    rw [← ContinuousLinearMap.mul_apply, ← pow_add]
    congr 2
    ring
  have hhead : s = h + (A ^ N) s := by
    rw [hshift]
    simpa only [Nat.zero_mul, pow_zero, ContinuousLinearMap.one_apply] using
      hs.tsum_eq_zero_add
  refine ⟨∑ i ∈ Finset.range N, (A ^ i) s, ?_⟩
  rw [finite_telescope]
  exact sub_eq_iff_eq_add.mpr (by simpa [add_comm] using hhead)

theorem exists_sub_apply_of_sq_decay [CompleteSpace E]
    (A : E →L[ℝ] E) (h : E) (N : ℕ)
    (hdecay : ∀ j : ℕ, ‖(A ^ (j * N)) h‖ ^ 2 ≤ (1 / 4 : ℝ) ^ j * ‖h‖ ^ 2) :
    ∃ g : E, g - A g = h := by
  have hnorm (j : ℕ) : ‖(A ^ (j * N)) h‖ ≤ (1 / 2 : ℝ) ^ j * ‖h‖ := by
    have hsq : ((1 / 2 : ℝ) ^ j * ‖h‖) ^ 2 = (1 / 4 : ℝ) ^ j * ‖h‖ ^ 2 := by
      rw [mul_pow, ← pow_mul, Nat.mul_comm j 2, pow_mul]
      norm_num
    have hn : 0 ≤ (1 / 2 : ℝ) ^ j * ‖h‖ := mul_nonneg (by positivity) (norm_nonneg h)
    have hd := hdecay j
    nlinarith [norm_nonneg ((A ^ (j * N)) h)]
  apply exists_sub_apply_of_summable_blocks A h N
  apply Summable.of_norm_bounded (g := fun j : ℕ => (1 / 2 : ℝ) ^ j * ‖h‖)
  · exact (summable_geometric_of_norm_lt_one (by norm_num : ‖(1 / 2 : ℝ)‖ < 1)).mul_right ‖h‖
  · exact hnorm

end BlockResolvent

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology ProbabilityTheory
open MarkovChainCLT

theorem solution {X : Type*} [MeasurableSpace X]
    (P : Kernel X X) [IsMarkovKernel P] (π : Measure X) [IsProbabilityMeasure π]
    (hP : HarrisErgodic P π) (huni : UniformlyErgodic P π)
    (f : X → ℝ) (hf : Measurable f) (hL2 : MemLp f 2 π) :
    ∃ g : X → ℝ, Measurable g ∧ MemLp g 2 π ∧
      Measurable (fun x => ∫ y, g y ∂(P x)) ∧
      MemLp (fun x => ∫ y, g y ∂(P x)) 2 π ∧
      ∀ᵐ x ∂π, g x - ∫ y, g y ∂(P x) = f x - ∫ x, f x ∂π := by
  have hinv : Kernel.Invariant P π := hP.1
  let μf : ℝ := ∫ x, f x ∂π
  have hc : MemLp (fun x => f x - μf) 2 π := hL2.sub (memLp_const μf)
  let h : Lp ℝ 2 π := hc.toLp (fun x => f x - μf)
  have hae : ⇑h =ᵐ[π] (fun x => f x - μf) := MemLp.coeFn_toLp hc
  have hmean : ∫ x, h x ∂π = 0 := by
    rw [integral_congr_ae hae,
      integral_sub (hL2.integrable (by norm_num)) (integrable_const μf)]
    simp [μf]
  obtain ⟨N, _hN, hrate⟩ := exists_lag_tvDist_le_of_uniformlyErgodic P π huni
  let A : Lp ℝ 2 π →L[ℝ] Lp ℝ 2 π := KernelL2.markovOp P π hinv
  have hdecay : ∀ j : ℕ, ‖(A ^ (j * N)) h‖ ^ 2 ≤ (1 / 4 : ℝ) ^ j * ‖h‖ ^ 2 := by
    intro j
    rw [KernelL2.norm_sq, KernelL2.norm_sq]
    calc
      (∫ x, ((A ^ (j * N)) h) x ^ 2 ∂π) =
          ∫ x, (∫ y, h y ∂iterKernel P (j * N) x) ^ 2 ∂π := by
        apply integral_congr_ae
        filter_upwards [KernelPowers.markovOp_pow_ae P π hinv (j * N) h] with x hx
        rw [show ((A ^ (j * N)) h) x = ∫ y, h y ∂iterKernel P (j * N) x from hx]
      _ ≤ (1 / 4 : ℝ) ^ j * ∫ x, h x ^ 2 ∂π :=
        integral_sq_iterKernel_pow_le P π hinv N (1 / 16) (by norm_num) (by norm_num)
          hrate h (Lp.stronglyMeasurable h).measurable (Lp.memLp h).integrable_sq hmean j
  obtain ⟨g, hgeq⟩ := BlockResolvent.exists_sub_apply_of_sq_decay A h N hdecay
  have hgm : Measurable (g : X → ℝ) := (Lp.stronglyMeasurable g).measurable
  refine ⟨g, hgm, Lp.memLp g, hgm.stronglyMeasurable.integral_kernel.measurable,
    KernelL2.kernel_memLp P π hinv g hgm (Lp.memLp g), ?_⟩
  have hgeq_ae : ⇑(g - A g) =ᵐ[π] ⇑h := Filter.Eventually.of_forall (fun x => by rw [hgeq])
  filter_upwards [Lp.coeFn_sub g (A g), KernelL2.markovOp_ae P π hinv g,
    hgeq_ae, hae] with x hsub hAg heq hh
  change (g - A g) x = g x - (A g) x at hsub
  change (A g) x = ∫ y, g y ∂P x at hAg
  calc
    g x - ∫ y, g y ∂P x = (g - A g) x := by rw [hsub, hAg]
    _ = h x := heq
    _ = f x - ∫ x, f x ∂π := hh

#print axioms solution
