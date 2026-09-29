-- Prove2me | solution 1 for vlCostN_triangle
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-18T17:41:50.828717+00:00
-- url     : https://prove2.me/submissions/c16ef895-f8ac-4efe-b50b-1db9b45902b0

import Mathlib
import Definitions.Def_Bridges_VoiceLeadingSorted
theorem solution {n : ℕ} (x y z : Fin n → ℤ) :
    vlCostN x z ≤ vlCostN x y + vlCostN y z := by
  unfold vlCostN
  -- optimal voice assignments for `x → y` and `y → z`
  obtain ⟨σ, -, hσ⟩ := Finset.exists_mem_eq_inf' ⟨1, Finset.mem_univ 1⟩
    (fun σ : Equiv.Perm (Fin n) => ∑ i, Int.natAbs (x i - y (σ i)))
  obtain ⟨τ, -, hτ⟩ := Finset.exists_mem_eq_inf' ⟨1, Finset.mem_univ 1⟩
    (fun τ : Equiv.Perm (Fin n) => ∑ i, Int.natAbs (y i - z (τ i)))
  rw [hσ, hτ]
  -- compose them and use the triangle inequality voice by voice
  calc Finset.univ.inf' _ (fun ρ : Equiv.Perm (Fin n) => ∑ i, Int.natAbs (x i - z (ρ i)))
      ≤ ∑ i, Int.natAbs (x i - z ((σ.trans τ) i)) := Finset.inf'_le _ (Finset.mem_univ _)
    _ ≤ ∑ i, (Int.natAbs (x i - y (σ i)) + Int.natAbs (y (σ i) - z (τ (σ i)))) := by
        apply Finset.sum_le_sum
        intro i _
        rw [Equiv.trans_apply]
        calc Int.natAbs (x i - z (τ (σ i)))
            = Int.natAbs ((x i - y (σ i)) + (y (σ i) - z (τ (σ i)))) := by congr 1; ring
          _ ≤ _ := Int.natAbs_add_le _ _
    _ = ∑ i, Int.natAbs (x i - y (σ i)) + ∑ i, Int.natAbs (y i - z (τ i)) := by
        rw [Finset.sum_add_distrib]
        congr 1
        exact Equiv.sum_comp σ (fun j => Int.natAbs (y j - z (τ j)))
