-- Prove2me | solution 1 for MarkovChainCLT.partialTraj_map_shift_succ
-- status  : ACCEPTED   (prove)
-- author  : @LukeBernese
-- created : 2026-08-15T20:06:09.597431+00:00
-- url     : https://prove2.me/submissions/0a062236-08e2-43c6-9757-1a72851134e8

import Theorems.Thm_MarkovChainCLT_partialTraj_succ_self_apply_eq_map

open Filter Finset Function MeasurableEquiv MeasurableSpace MeasureTheory Preorder ProbabilityTheory
open scoped ENNReal NNReal Topology

/-- One-step time-homogeneity: dropping the first coordinate of a one-step extension
gives the one-step extension of the dropped trajectory. -/
theorem solution {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P] (n : ℕ) (u : Π _j : Finset.Iic (n + 1), S) :
    (Kernel.partialTraj (X := fun _ : ℕ => S) (BanditAlgorithm.markovChainStep P)
        (n + 1) (n + 1 + 1) u).map
        (fun v i => v ⟨i.1 + 1, Finset.mem_Iic.2 (Nat.succ_le_succ (Finset.mem_Iic.mp i.2))⟩)
      = Kernel.partialTraj (X := fun _ : ℕ => S) (BanditAlgorithm.markovChainStep P) n (n + 1)
          (fun i => u ⟨i.1 + 1, Finset.mem_Iic.2 (Nat.succ_le_succ (Finset.mem_Iic.mp i.2))⟩) := by
  -- the shift on initial segments, and its measurability
  set sh : ∀ m : ℕ, (Π _j : Finset.Iic (m + 1), S) → (Π _i : Finset.Iic m, S) :=
    fun m v i => v ⟨i.1 + 1, Finset.mem_Iic.2 (Nat.succ_le_succ (Finset.mem_Iic.mp i.2))⟩
    with hsh
  have hmsh : ∀ m : ℕ, Measurable (sh m) := fun m =>
    measurable_pi_lambda _ (fun i => measurable_pi_apply _)
  -- for a constant family, `piSingleton` is the constant function
  have hps : ∀ (m : ℕ) (w : S) (j : Finset.Ioc m (m + 1)),
      MeasurableEquiv.piSingleton (X := fun _ : ℕ => S) m w j = w := by
    intro m w j
    simp [MeasurableEquiv.piSingleton]
  have hglue : Measurable (fun w : S => IicProdIoc (X := fun _ : ℕ => S) (n + 1) (n + 1 + 1)
      (u, MeasurableEquiv.piSingleton (X := fun _ : ℕ => S) (n + 1) w)) :=
    (measurable_IicProdIoc (X := fun _ : ℕ => S)).comp (measurable_const.prodMk
      (MeasurableEquiv.piSingleton (X := fun _ : ℕ => S) (n + 1)).measurable)
  rw [MarkovChainCLT.partialTraj_succ_self_apply_eq_map P (n + 1) u,
    MarkovChainCLT.partialTraj_succ_self_apply_eq_map P n (sh n u),
    Measure.map_map (hmsh (n + 1)) hglue]
  -- the two transition kernels agree: the last coordinate is the same
  have hlast : (sh n u) ⟨n, Finset.mem_Iic.2 le_rfl⟩
      = u ⟨n + 1, Finset.mem_Iic.2 le_rfl⟩ := rfl
  rw [hlast]
  congr 1
  funext w
  funext i
  show (IicProdIoc (X := fun _ : ℕ => S) (n + 1) (n + 1 + 1)
      (u, MeasurableEquiv.piSingleton (X := fun _ : ℕ => S) (n + 1) w))
      ⟨i.1 + 1, Finset.mem_Iic.2 (Nat.succ_le_succ (Finset.mem_Iic.mp i.2))⟩
    = IicProdIoc (X := fun _ : ℕ => S) n (n + 1)
      (sh n u, MeasurableEquiv.piSingleton (X := fun _ : ℕ => S) n w) i
  by_cases h : i.1 ≤ n
  · simp only [_root_.IicProdIoc]
    rw [dif_pos (Nat.succ_le_succ h), dif_pos h]
  · simp only [_root_.IicProdIoc]
    rw [dif_neg (fun hc => h (Nat.le_of_succ_le_succ hc)), dif_neg h, hps, hps]
