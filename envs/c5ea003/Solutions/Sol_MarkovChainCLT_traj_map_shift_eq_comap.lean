-- Prove2me | solution 1 for MarkovChainCLT.traj_map_shift_eq_comap
-- status  : ACCEPTED   (prove)
-- author  : @LukeBernese
-- created : 2026-08-15T20:41:44.627909+00:00
-- url     : https://prove2.me/submissions/f5f4b9d1-da30-4033-8945-fa4b7912ef61

import Theorems.Thm_MarkovChainCLT_partialTraj_map_shiftK_succ
import Theorems.Thm_PathSpace_ext_of_map_frestrictLe

set_option maxHeartbeats 1000000

open Filter Finset Function MeasurableEquiv MeasurableSpace MeasureTheory Preorder ProbabilityTheory
open scoped ENNReal NNReal Topology

variable {S : Type*} [MeasurableSpace S]

/-- Drop the first `j` coordinates of an initial segment of length `j + m`. -/
def shK (m j : ℕ) (v : Π _i : Finset.Iic (j + m), S) : Π _i : Finset.Iic m, S :=
  fun i => v ⟨j + i.1, Finset.mem_Iic.2 (Nat.add_le_add_left (Finset.mem_Iic.mp i.2) j)⟩

lemma measurable_shK (m j : ℕ) : Measurable (shK (S := S) m j) :=
  measurable_pi_lambda _ (fun _ => measurable_pi_apply _)

/-- Read off the last coordinate as a length-one initial segment. -/
def embj (j : ℕ) (u : Π _i : Finset.Iic j, S) : Π _i : Finset.Iic 0, S :=
  fun _ => u ⟨j, Finset.mem_Iic.2 le_rfl⟩

lemma measurable_embj (j : ℕ) : Measurable (embj (S := S) j) :=
  measurable_pi_lambda _ (fun _ => measurable_pi_apply _)

lemma comp_comap' {α β γ δ : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    [MeasurableSpace δ] (η : Kernel β γ) (κ : Kernel α β) {f : δ → α} (hf : Measurable f) :
    (η ∘ₖ κ).comap f hf = η ∘ₖ (κ.comap f hf) := by
  ext d s hs
  rw [Kernel.comap_apply, Kernel.comp_apply' _ _ _ hs, Kernel.comp_apply' _ _ _ hs]
  simp [Kernel.comap_apply]

/-- Kernel form of the offset homogeneity lemma. -/
lemma shiftK_kernel (P : Kernel S S) [IsMarkovKernel P] (j m : ℕ) :
    (Kernel.partialTraj (X := fun _ : ℕ => S) (BanditAlgorithm.markovChainStep P)
        (j + m) (j + m + 1)).map (shK (m + 1) j)
      = (Kernel.partialTraj (X := fun _ : ℕ => S) (BanditAlgorithm.markovChainStep P)
          m (m + 1)).comap (shK m j) (measurable_shK m j) := by
  refine Kernel.ext (fun v => ?_)
  rw [Kernel.map_apply _ (measurable_shK (m + 1) j), Kernel.comap_apply]
  exact MarkovChainCLT.partialTraj_map_shiftK_succ P j m v

/-- The marginal induction. -/
theorem restart_step (P : Kernel S S) [IsMarkovKernel P] (j m : ℕ) :
    (Kernel.partialTraj (X := fun _ : ℕ => S) (BanditAlgorithm.markovChainStep P)
        j (j + m)).map (shK m j)
      = (Kernel.partialTraj (X := fun _ : ℕ => S) (BanditAlgorithm.markovChainStep P)
          0 m).comap (embj j) (measurable_embj j) := by
  induction m with
  | zero =>
    have hfun : shK (S := S) 0 j = embj j := by
      funext v; funext i
      obtain ⟨iv, hiv⟩ := i
      have hi : iv = 0 := Nat.le_zero.mp (Finset.mem_Iic.mp hiv)
      subst hi
      rfl
    rw [hfun]
    show (Kernel.partialTraj (X := fun _ : ℕ => S) (BanditAlgorithm.markovChainStep P)
        j j).map (embj j)
      = (Kernel.partialTraj (X := fun _ : ℕ => S) (BanditAlgorithm.markovChainStep P)
          0 0).comap (embj j) (measurable_embj j)
    rw [Kernel.partialTraj_self, Kernel.partialTraj_self]
    refine Kernel.ext (fun v => ?_)
    rw [Kernel.map_apply _ (measurable_embj j), Kernel.comap_apply, Kernel.id_apply,
      Kernel.id_apply]
    exact Measure.map_dirac' (measurable_embj j) v
  | succ m ih =>
    have hsplit : Kernel.partialTraj (X := fun _ : ℕ => S)
          (BanditAlgorithm.markovChainStep P) j (j + (m + 1))
        = Kernel.partialTraj (X := fun _ : ℕ => S) (BanditAlgorithm.markovChainStep P)
            (j + m) (j + m + 1)
          ∘ₖ Kernel.partialTraj (X := fun _ : ℕ => S) (BanditAlgorithm.markovChainStep P)
            j (j + m) := Kernel.partialTraj_succ_eq_comp (Nat.le_add_right j m)
    rw [hsplit, Kernel.map_comp, shiftK_kernel,
      ← Kernel.comp_map _ _ (measurable_shK m j), ih,
      ← comp_comap' _ _ (measurable_embj j),
      ← Kernel.partialTraj_succ_eq_comp (Nat.zero_le m)]

/-- **Restart from an arbitrary time.** -/
theorem solution (P : Kernel S S) [IsMarkovKernel P] (j : ℕ) :
    (Kernel.traj (X := fun _ : ℕ => S) (BanditAlgorithm.markovChainStep P) j).map
        (fun ω : ℕ → S => fun n => ω (j + n))
      = (BanditAlgorithm.markovChainKernel P).comap (fun u : Π _i : Finset.Iic j, S =>
          u ⟨j, Finset.mem_Iic.2 le_rfl⟩) (measurable_pi_apply _) := by
  have hσ : Measurable (fun (ω : ℕ → S) => fun n => ω (j + n)) :=
    measurable_pi_lambda _ (fun _ => measurable_pi_apply _)
  have hker : ∀ m : ℕ,
      ((Kernel.traj (X := fun _ : ℕ => S) (BanditAlgorithm.markovChainStep P) j).map
          (fun ω : ℕ → S => fun n => ω (j + n))).map (frestrictLe (π := fun _ : ℕ => S) m)
        = ((BanditAlgorithm.markovChainKernel P).comap (fun u : Π _i : Finset.Iic j, S =>
            u ⟨j, Finset.mem_Iic.2 le_rfl⟩) (measurable_pi_apply _)).map
          (frestrictLe (π := fun _ : ℕ => S) m) := by
    intro m
    have hcomp : (frestrictLe (π := fun _ : ℕ => S) m) ∘ (fun ω : ℕ → S => fun n => ω (j + n))
        = (shK m j) ∘ (frestrictLe (π := fun _ : ℕ => S) (j + m)) := rfl
    rw [← Kernel.map_comp_right _ hσ (measurable_frestrictLe m), hcomp,
      Kernel.map_comp_right _ (measurable_frestrictLe (j + m)) (measurable_shK m j),
      Kernel.traj_map_frestrictLe]
    have hRHS : (BanditAlgorithm.markovChainKernel P).comap (fun u : Π _i : Finset.Iic j, S =>
          u ⟨j, Finset.mem_Iic.2 le_rfl⟩) (measurable_pi_apply _)
        = (Kernel.traj (X := fun _ : ℕ => S) (BanditAlgorithm.markovChainStep P) 0).comap
            (embj j) (measurable_embj j) := Kernel.ext (fun u => rfl)
    rw [hRHS, ← Kernel.comap_map_comm _ (measurable_embj j) (measurable_frestrictLe m),
      Kernel.traj_map_frestrictLe]
    exact restart_step P j m
  haveI := Kernel.IsMarkovKernel.map
    (Kernel.traj (X := fun _ : ℕ => S) (BanditAlgorithm.markovChainStep P) j) hσ
  refine Kernel.ext (fun u => ?_)
  refine PathSpace.ext_of_map_frestrictLe (fun m => ?_)
  rw [← Kernel.map_apply _ (measurable_frestrictLe m),
    ← Kernel.map_apply _ (measurable_frestrictLe m), hker m]
