-- Prove2me | solution 1 for MarkovChainCLT.map_coord_chainMeasure
-- status  : ACCEPTED   (prove)
-- author  : @LukeBernese
-- created : 2026-08-15T16:11:42.923433+00:00
-- url     : https://prove2.me/submissions/b1f831c6-7739-4b5d-bdcc-a495672d7e74

import Definitions.Def_MarkovErgodicity
import Definitions.Def_MarkovChainPathMeasure
import Mathlib.Probability.Kernel.IonescuTulcea.Traj

set_option maxHeartbeats 1000000

open MeasureTheory ProbabilityTheory Filter Finset Preorder
open scoped ENNReal NNReal Topology ProbabilityTheory
open MarkovChainCLT

/-- The `n`-th coordinate marginal of the trajectory law started at a point is `Pⁿ(x, ·)`. -/
private theorem map_eval_traj {X : Type*} [MeasurableSpace X]
    (P : Kernel X X) [IsMarkovKernel P] (n : ℕ) (y : Π _i : Iic 0, X) :
    Measure.map (fun ω : ℕ → X => ω n)
        (Kernel.traj (X := fun _ : ℕ => X) (BanditAlgorithm.markovChainStep P) 0 y)
      = iterKernel P n (y ⟨0, mem_Iic.2 le_rfl⟩) := by
  induction n with
  | zero =>
    have hfr : Measure.map (frestrictLe 0)
        (Kernel.traj (X := fun _ : ℕ => X) (BanditAlgorithm.markovChainStep P) 0 y) = Measure.dirac y := by
      rw [Kernel.traj_map_frestrictLe_apply, Kernel.partialTraj_self, Kernel.id_apply]
    calc Measure.map (fun ω : ℕ → X => ω 0)
          (Kernel.traj (X := fun _ : ℕ => X) (BanditAlgorithm.markovChainStep P) 0 y)
        = Measure.map ((fun z : Π _i : Iic 0, X => z ⟨0, mem_Iic.2 le_rfl⟩) ∘ (frestrictLe 0))
            (Kernel.traj (X := fun _ : ℕ => X) (BanditAlgorithm.markovChainStep P) 0 y) := rfl
      _ = Measure.map (fun z : Π _i : Iic 0, X => z ⟨0, mem_Iic.2 le_rfl⟩)
            (Measure.map (frestrictLe 0)
              (Kernel.traj (X := fun _ : ℕ => X) (BanditAlgorithm.markovChainStep P) 0 y)) :=
          (Measure.map_map (measurable_pi_apply _) (measurable_frestrictLe 0)).symm
      _ = Measure.map (fun z : Π _i : Iic 0, X => z ⟨0, mem_Iic.2 le_rfl⟩) (Measure.dirac y) := by
          rw [hfr]
      _ = Measure.dirac (y ⟨0, mem_Iic.2 le_rfl⟩) :=
          Measure.map_dirac' (measurable_pi_apply _) y
      _ = iterKernel P 0 (y ⟨0, mem_Iic.2 le_rfl⟩) := by
          rw [iterKernel_zero, Kernel.id_apply]
  | succ m ih =>
    -- split the trajectory at time `m`
    have hsplit : Kernel.traj (X := fun _ : ℕ => X) (BanditAlgorithm.markovChainStep P) 0 y
        = (Kernel.traj (X := fun _ : ℕ => X) (BanditAlgorithm.markovChainStep P) m)
            ∘ₘ (Kernel.partialTraj (X := fun _ : ℕ => X) (BanditAlgorithm.markovChainStep P) 0 m y) := by
      conv_lhs => rw [← Kernel.traj_comp_partialTraj (X := fun _ : ℕ => X) (κ := BanditAlgorithm.markovChainStep P)
        (Nat.zero_le m)]
      rw [Kernel.comp_apply]
    -- the `m`-th marginal of `partialTraj` is the `m`-th marginal of `traj`
    have hmarg : Measure.map (fun z : Π _i : Iic m, X => z ⟨m, mem_Iic.2 le_rfl⟩)
        (Kernel.partialTraj (X := fun _ : ℕ => X) (BanditAlgorithm.markovChainStep P) 0 m y)
        = Measure.map (fun ω : ℕ → X => ω m)
            (Kernel.traj (X := fun _ : ℕ => X) (BanditAlgorithm.markovChainStep P) 0 y) := by
      calc Measure.map (fun z : Π _i : Iic m, X => z ⟨m, mem_Iic.2 le_rfl⟩)
            (Kernel.partialTraj (X := fun _ : ℕ => X) (BanditAlgorithm.markovChainStep P) 0 m y)
          = Measure.map (fun z : Π _i : Iic m, X => z ⟨m, mem_Iic.2 le_rfl⟩)
              (Measure.map (frestrictLe m)
                (Kernel.traj (X := fun _ : ℕ => X) (BanditAlgorithm.markovChainStep P) 0 y)) := by
            rw [Kernel.traj_map_frestrictLe_apply]
        _ = Measure.map ((fun z : Π _i : Iic m, X => z ⟨m, mem_Iic.2 le_rfl⟩) ∘ (frestrictLe m))
              (Kernel.traj (X := fun _ : ℕ => X) (BanditAlgorithm.markovChainStep P) 0 y) :=
            Measure.map_map (measurable_pi_apply _) (measurable_frestrictLe m)
        _ = Measure.map (fun ω : ℕ → X => ω m)
              (Kernel.traj (X := fun _ : ℕ => X) (BanditAlgorithm.markovChainStep P) 0 y) := rfl
    -- `κ m` precomposes `P` with the coordinate at time `m`
    have hstep : ∀ ν : Measure (Π _i : Iic m, X),
        ν.bind (BanditAlgorithm.markovChainStep P m)
          = (Measure.map (fun z : Π _i : Iic m, X => z ⟨m, mem_Iic.2 le_rfl⟩) ν).bind P := by
      intro ν
      ext s hs
      rw [Measure.bind_apply hs (Kernel.aemeasurable _),
        Measure.bind_apply hs (Kernel.aemeasurable _),
        lintegral_map (Kernel.measurable_coe _ hs) (measurable_pi_apply _)]
      rfl
    rw [hsplit, Measure.map_comp _ _ (measurable_pi_apply (m + 1)),
      Kernel.map_traj_succ_self, hstep, hmarg, ih, iterKernel_succ, Kernel.comp_apply]

theorem solution {X : Type*} [MeasurableSpace X]
    (P : Kernel X X) [IsMarkovKernel P] (π : Measure X) [IsProbabilityMeasure π]
    (hinv : Kernel.Invariant P π) (n : ℕ) :
    Measure.map (fun ω : ℕ → X => ω n) (chainMeasure P π) = π := by
  have hmarg : Measure.map (fun ω : ℕ → X => ω n) (chainMeasure P π)
      = (iterKernel P n) ∘ₘ π := by
    rw [chainMeasure, Measure.map_comp _ _ (measurable_pi_apply n)]
    congr 1
    ext x s hs
    rw [Kernel.map_apply _ (measurable_pi_apply n),
      BanditAlgorithm.markovChainKernel, Kernel.comap_apply, map_eval_traj P n]
  rw [hmarg]
  clear hmarg
  induction n with
  | zero =>
    rw [iterKernel_zero]
    have hid : (⇑(Kernel.id : Kernel X X)) = (Measure.dirac : X → Measure X) := by
      funext a; exact Kernel.id_apply a
    show Measure.bind π _ = π
    rw [hid, Measure.bind_dirac]
  | succ m ih =>
    rw [iterKernel_succ, ← Measure.comp_assoc, ih]
    exact hinv
