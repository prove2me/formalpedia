-- Prove2me | solution 1 for MarkovChainCLT.chainMeasure_past_inter_future
-- status  : ACCEPTED   (prove)
-- author  : @LukeBernese
-- created : 2026-08-15T21:09:45.028054+00:00
-- url     : https://prove2.me/submissions/6d07295a-e836-4cb6-828b-54f6fb9b820e

import Theorems.Thm_MarkovChainCLT_chainMeasure_eq_comp_traj
import Theorems.Thm_MarkovChainCLT_traj_map_shift_add_eq_comp_iter

open Filter Finset Function MeasurableEquiv MeasurableSpace MeasureTheory Preorder ProbabilityTheory
open scoped ENNReal NNReal Topology
open MarkovChainCLT

set_option maxHeartbeats 1000000

/-- Joint probability of a past event and a future event, disintegrated over the past. -/
theorem solution {X : Type*} [MeasurableSpace X] (P : Kernel X X) [IsMarkovKernel P]
    (lam : Measure X) [IsProbabilityMeasure lam] (k n : ℕ)
    (A₀ : Set (Π _i : Finset.Iic k, X)) (hA₀ : MeasurableSet A₀)
    (B₀ : Set (ℕ → X)) (hB₀ : MeasurableSet B₀) :
    (chainMeasure P lam) ((frestrictLe (π := fun _ : ℕ => X) k ⁻¹' A₀)
        ∩ ((fun ω : ℕ → X => fun l => ω (k + n + l)) ⁻¹' B₀))
      = ∫⁻ u in A₀, ((BanditAlgorithm.markovChainKernel P)
          ∘ₘ (iterKernel P n (u ⟨k, Finset.mem_Iic.2 le_rfl⟩))) B₀
          ∂((chainMeasure P lam).map (frestrictLe (π := fun _ : ℕ => X) k)) := by
  set τ := Kernel.traj (X := fun _ : ℕ => X) (BanditAlgorithm.markovChainStep P) k with hτ
  set SA := frestrictLe (π := fun _ : ℕ => X) k ⁻¹' A₀ with hSA
  set SB := (fun ω : ℕ → X => fun l => ω (k + n + l)) ⁻¹' B₀ with hSB
  have hshift : Measurable (fun (ω : ℕ → X) => fun l => ω (k + n + l)) :=
    measurable_pi_lambda _ (fun _ => measurable_pi_apply _)
  have hmeasA : MeasurableSet SA := (measurable_frestrictLe k) hA₀
  have hmeasB : MeasurableSet SB := hshift hB₀
  -- the trajectory kernel reproduces its own initial segment
  have hdirac : ∀ u : Π _i : Finset.Iic k, X,
      (τ u).map (frestrictLe (π := fun _ : ℕ => X) k) = Measure.dirac u := by
    intro u
    have h' : (Kernel.traj (X := fun _ : ℕ => X) (BanditAlgorithm.markovChainStep P) k).map
        (frestrictLe (π := fun _ : ℕ => X) k)
        = Kernel.partialTraj (X := fun _ : ℕ => X) (BanditAlgorithm.markovChainStep P) k k :=
      Kernel.traj_map_frestrictLe k k
    have h'' := congrArg (fun κ : Kernel (Π _i : Finset.Iic k, X) (Π _i : Finset.Iic k, X) => κ u) h'
    simp only at h''
    rw [Kernel.map_apply _ (measurable_frestrictLe k)] at h''
    rw [hτ, h'', Kernel.partialTraj_self, Kernel.id_apply]
  -- the future event, given the past
  have hfut : ∀ u : Π _i : Finset.Iic k, X, (τ u) SB
      = ((BanditAlgorithm.markovChainKernel P)
          ∘ₘ (iterKernel P n (u ⟨k, Finset.mem_Iic.2 le_rfl⟩))) B₀ := by
    intro u
    rw [hSB, ← Measure.map_apply hshift hB₀, hτ,
      MarkovChainCLT.traj_map_shift_add_eq_comp_iter P k n u]
  -- pointwise: the past event acts as an indicator
  have hpt : ∀ u : Π _i : Finset.Iic k, X, (τ u) (SA ∩ SB)
      = A₀.indicator (fun u => ((BanditAlgorithm.markovChainKernel P)
          ∘ₘ (iterKernel P n (u ⟨k, Finset.mem_Iic.2 le_rfl⟩))) B₀) u := by
    intro u
    by_cases hu : u ∈ A₀
    · rw [Set.indicator_of_mem hu, ← hfut u]
      have hnull : (τ u) SAᶜ = 0 := by
        rw [hSA, ← Set.preimage_compl, ← Measure.map_apply (measurable_frestrictLe k) hA₀.compl,
          hdirac u, Measure.dirac_apply' _ hA₀.compl]
        simp [hu]
      have h1 : (τ u) (SA ∩ SB) ≤ (τ u) SB := measure_mono Set.inter_subset_right
      have h2 : (τ u) SB ≤ (τ u) (SA ∩ SB) + (τ u) SAᶜ := by
        refine le_trans (measure_mono ?_) (measure_union_le _ _)
        intro ω hω
        by_cases hA : ω ∈ SA
        · exact Or.inl ⟨hA, hω⟩
        · exact Or.inr hA
      rw [hnull, add_zero] at h2
      exact le_antisymm h1 h2
    · rw [Set.indicator_of_notMem hu]
      have hzero : (τ u) SA = 0 := by
        rw [hSA, ← Measure.map_apply (measurable_frestrictLe k) hA₀, hdirac u,
          Measure.dirac_apply' _ hA₀]
        simp [hu]
      exact le_antisymm (le_trans (measure_mono Set.inter_subset_left) hzero.le) (by simp)
  -- integrate
  conv_lhs => rw [MarkovChainCLT.chainMeasure_eq_comp_traj P lam k]
  rw [Measure.bind_apply (hmeasA.inter hmeasB) (Kernel.aemeasurable _),
    lintegral_congr hpt, lintegral_indicator hA₀]
