-- Prove2me | solution 1 for MarkovChainCLT.phiMixingCoef_le_of_tvDist_le
-- status  : ACCEPTED   (prove)
-- author  : @LukeBernese
-- created : 2026-08-15T21:18:16.897515+00:00
-- url     : https://prove2.me/submissions/537b569d-9f1f-4409-9bf7-f7a10ac17db6

import Theorems.Thm_MarkovChainCLT_chainMeasure_past_inter_future
import Theorems.Thm_MarkovChainCLT_processSigma_Ici_eq_comap_shift
import Theorems.Thm_MarkovChainCLT_processSigma_Iic_eq_comap_restrict
import Theorems.Thm_MarkovChainCLT_abs_integral_sub_le_tvDist
import Theorems.Thm_MarkovChainCLT_abs_setAverage_sub_le
import Theorems.Thm_MarkovChainCLT_isStrictlyStationary_chainMeasure

open Filter Finset Function MeasurableSpace MeasureTheory Preorder ProbabilityTheory
open scoped ENNReal NNReal Topology
open MarkovChainCLT

set_option maxHeartbeats 2000000

theorem solution {X : Type*} [MeasurableSpace X]
    (P : Kernel X X) [IsMarkovKernel P] (π : Measure X) [IsProbabilityMeasure π]
    (hinv : Kernel.Invariant P π) (n : ℕ) (hn : 1 ≤ n) (C : ℝ) (hC0 : 0 ≤ C)
    (hC : ∀ x, tvDist ((iterKernel P n) x) π ≤ C) :
    phiMixingCoef (chainMeasure P π) (fun i (ω : ℕ → X) => ω i) n ≤ C := by
  set μ := chainMeasure P π with hμ
  set K := BanditAlgorithm.markovChainKernel P with hK
  refine Real.sSup_le ?_ hC0
  rintro r ⟨k, A, B, hA, hAne, hB, rfl⟩
  rw [MarkovChainCLT.processSigma_Iic_eq_comap_restrict] at hA
  rw [MarkovChainCLT.processSigma_Ici_eq_comap_shift] at hB
  obtain ⟨A₀, hA₀, rfl⟩ := hA
  obtain ⟨B₀, hB₀, rfl⟩ := hB
  -- the two shift maps, in the shapes the lemmas use
  have hfr : (fun (ω : ℕ → X) => fun i : Finset.Iic k => ω i.1)
      = frestrictLe (π := fun _ : ℕ => X) k := rfl
  have hsh : Measurable (fun (ω : ℕ → X) => fun l => ω (k + n + l)) :=
    measurable_pi_lambda _ (fun _ => measurable_pi_apply _)
  set lamk := μ.map (frestrictLe (π := fun _ : ℕ => X) k) with hlamk
  -- the integrand `g`
  set g : X → ℝ := fun y => ((K y) B₀).toReal with hg
  have hgm : Measurable g := (Kernel.measurable_coe K hB₀).ennreal_toReal
  have hg0 : ∀ y, 0 ≤ g y := fun y => ENNReal.toReal_nonneg
  have hg1 : ∀ y, g y ≤ 1 := by
    intro y
    rw [hg]
    refine ENNReal.toReal_le_of_le_ofReal zero_le_one ?_
    simpa using prob_le_one
  -- toReal of a bind
  have hbindReal : ∀ (ν : Measure X), IsProbabilityMeasure ν →
      ((K ∘ₘ ν) B₀).toReal = ∫ y, g y ∂ν := by
    intro ν hν
    haveI := hν
    rw [Measure.bind_apply hB₀ (Kernel.aemeasurable _)]
    refine (integral_toReal (Kernel.measurable_coe K hB₀).aemeasurable ?_).symm
    filter_upwards with y
    exact measure_lt_top _ _
  -- the stationary value
  have hstat : μ ((fun (ω : ℕ → X) => fun l => ω (k + n + l)) ⁻¹' B₀) = μ B₀ := by
    have hconv : (fun (ω : ℕ → X) => fun l => ω (k + n + l))
        = (fun (ω : ℕ → X) => fun l => ω (l + (k + n))) := by
      funext ω; funext l; rw [Nat.add_comm]
    rw [← Measure.map_apply hsh hB₀, hconv]
    have hs := MarkovChainCLT.isStrictlyStationary_chainMeasure P π hinv (k + n)
    simp only at hs
    rw [hs]
    have : (fun (ω : ℕ → X) => fun l => ω l) = id := rfl
    rw [this, Measure.map_id]
  -- rewrite the three measures
  rw [hfr, hstat,
    MarkovChainCLT.chainMeasure_past_inter_future P π k n A₀ hA₀ B₀ hB₀,
    show μ (frestrictLe (π := fun _ : ℕ => X) k ⁻¹' A₀) = lamk A₀ from
      (Measure.map_apply (measurable_frestrictLe k) hA₀).symm]
  -- `μ B₀` as an integral of `g`
  have hmB : (μ B₀).toReal = ∫ y, g y ∂π := by
    rw [hμ, chainMeasure, ← hK]
    exact hbindReal π inferInstance
  -- the conditional value as an integral of `g`
  have hcond : ∀ u : Π _i : Finset.Iic k, X,
      ((K ∘ₘ (iterKernel P n (u ⟨k, Finset.mem_Iic.2 le_rfl⟩))) B₀).toReal
        = ∫ y, g y ∂(iterKernel P n (u ⟨k, Finset.mem_Iic.2 le_rfl⟩)) :=
    fun u => hbindReal _ inferInstance
  -- pass to real integrals
  have hmeasF : Measurable (fun u : Π _i : Finset.Iic k, X =>
      ((K ∘ₘ (iterKernel P n (u ⟨k, Finset.mem_Iic.2 le_rfl⟩))) B₀)) := by
    have h1 : Measurable (fun x : X => (K ∘ₘ (iterKernel P n x)) B₀) := by
      have : (fun x : X => (K ∘ₘ (iterKernel P n x)) B₀)
          = fun x : X => ((K ∘ₖ (iterKernel P n)) x) B₀ := by
        funext x; rw [Kernel.comp_apply]
      rw [this]
      exact Kernel.measurable_coe _ hB₀
    exact h1.comp (measurable_pi_apply _)
  have hlt : ∀ u : Π _i : Finset.Iic k, X,
      ((K ∘ₘ (iterKernel P n (u ⟨k, Finset.mem_Iic.2 le_rfl⟩))) B₀) < ∞ :=
    fun u => measure_lt_top _ _
  have hToReal : (∫⁻ u in A₀, ((K ∘ₘ (iterKernel P n (u ⟨k, Finset.mem_Iic.2 le_rfl⟩))) B₀)
        ∂lamk).toReal
      = ∫ u in A₀, ((K ∘ₘ (iterKernel P n (u ⟨k, Finset.mem_Iic.2 le_rfl⟩))) B₀).toReal ∂lamk :=
    (integral_toReal hmeasF.aemeasurable (Filter.Eventually.of_forall
      (fun u => hlt u))).symm
  rw [hToReal]
  -- apply the averaging bound
  haveI : IsProbabilityMeasure lamk := by
    rw [hlamk]
    exact Measure.isProbabilityMeasure_map (measurable_frestrictLe k).aemeasurable
  have hAne' : lamk A₀ ≠ 0 := by
    intro h
    apply hAne
    rw [hfr, show μ (frestrictLe (π := fun _ : ℕ => X) k ⁻¹' A₀) = lamk A₀ from
      (Measure.map_apply (measurable_frestrictLe k) hA₀).symm, h]
  have hintOn : IntegrableOn (fun u : Π _i : Finset.Iic k, X =>
      ((K ∘ₘ (iterKernel P n (u ⟨k, Finset.mem_Iic.2 le_rfl⟩))) B₀).toReal) A₀ lamk := by
    refine Integrable.integrableOn ⟨hmeasF.ennreal_toReal.aestronglyMeasurable, ?_⟩
    refine (hasFiniteIntegral_const (1:ℝ)).mono ?_
    filter_upwards with u
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_one,
      abs_of_nonneg ENNReal.toReal_nonneg, hcond u]
    calc ∫ y, g y ∂(iterKernel P n (u ⟨k, Finset.mem_Iic.2 le_rfl⟩))
        ≤ ∫ _y, (1:ℝ) ∂(iterKernel P n (u ⟨k, Finset.mem_Iic.2 le_rfl⟩)) := by
          refine integral_mono ?_ (integrable_const 1) (fun y => hg1 y)
          exact ⟨hgm.aestronglyMeasurable, by
            refine (hasFiniteIntegral_const (1:ℝ)).mono ?_
            filter_upwards with y
            rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_one, abs_of_nonneg (hg0 y)]
            exact hg1 y⟩
      _ = 1 := by simp
  refine MarkovChainCLT.abs_setAverage_sub_le lamk A₀ hA₀ hAne' _ hintOn _ C ?_
  intro u _
  rw [hcond u, hmB]
  refine le_trans (MarkovChainCLT.abs_integral_sub_le_tvDist _ π g hgm hg0 hg1) ?_
  exact hC _
