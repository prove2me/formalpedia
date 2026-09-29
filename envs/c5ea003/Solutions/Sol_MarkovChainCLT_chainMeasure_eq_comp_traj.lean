-- Prove2me | solution 1 for MarkovChainCLT.chainMeasure_eq_comp_traj
-- status  : ACCEPTED   (prove)
-- author  : @LukeBernese
-- created : 2026-08-15T20:59:24.281394+00:00
-- url     : https://prove2.me/submissions/f6302da1-8568-408c-a8ff-2e97e06834ea

import Definitions.Def_MarkovChainPathMeasure

open Filter Finset Function MeasurableEquiv MeasurableSpace MeasureTheory Preorder ProbabilityTheory
open scoped ENNReal NNReal Topology
open MarkovChainCLT

set_option maxHeartbeats 1000000

lemma comp_comap {α β γ δ : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    [MeasurableSpace δ] (η : Kernel β γ) (κ : Kernel α β) {f : δ → α} (hf : Measurable f) :
    (η ∘ₖ κ).comap f hf = η ∘ₖ (κ.comap f hf) := by
  ext d s hs
  rw [Kernel.comap_apply, Kernel.comp_apply' _ _ _ hs, Kernel.comp_apply' _ _ _ hs]
  simp [Kernel.comap_apply]

/-- Conditioning the chain on its first `k+1` coordinates. -/
theorem solution {X : Type*} [MeasurableSpace X] (P : Kernel X X) [IsMarkovKernel P]
    (lam : Measure X) [IsProbabilityMeasure lam] (k : ℕ) :
    chainMeasure P lam
      = (Kernel.traj (X := fun _ : ℕ => X) (BanditAlgorithm.markovChainStep P) k)
          ∘ₘ ((chainMeasure P lam).map (frestrictLe (π := fun _ : ℕ => X) k)) := by
  have hemb : Measurable (fun (x : X) (_ : Finset.Iic 0) => x) :=
    measurable_pi_lambda _ (fun _ => measurable_id)
  set Q : Kernel X (Π _i : Finset.Iic k, X) :=
    (Kernel.partialTraj (X := fun _ : ℕ => X) (BanditAlgorithm.markovChainStep P) 0 k).comap
      (fun (x : X) (_ : Finset.Iic 0) => x) hemb with hQ
  have hkermarg : (BanditAlgorithm.markovChainKernel P).map
      (frestrictLe (π := fun _ : ℕ => X) k) = Q := by
    show ((Kernel.traj (X := fun _ : ℕ => X) (BanditAlgorithm.markovChainStep P) 0).comap
        (fun (x : X) (_ : Finset.Iic 0) => x) hemb).map
        (frestrictLe (π := fun _ : ℕ => X) k) = Q
    rw [hQ, ← Kernel.comap_map_comm _ hemb (measurable_frestrictLe k),
      Kernel.traj_map_frestrictLe]
  have hmarg : (chainMeasure P lam).map (frestrictLe (π := fun _ : ℕ => X) k) = Q ∘ₘ lam := by
    rw [chainMeasure, Measure.map_comp _ _ (measurable_frestrictLe k), hkermarg]
  have hdec : (Kernel.traj (X := fun _ : ℕ => X) (BanditAlgorithm.markovChainStep P) k) ∘ₖ Q
      = BanditAlgorithm.markovChainKernel P := by
    rw [hQ, ← comp_comap _ _ hemb, Kernel.traj_comp_partialTraj (Nat.zero_le k)]
    rfl
  rw [hmarg, Measure.comp_assoc, hdec, chainMeasure]
