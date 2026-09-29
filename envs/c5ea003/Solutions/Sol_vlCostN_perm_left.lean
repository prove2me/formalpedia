-- Prove2me | solution 1 for vlCostN_perm_left
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-18T19:13:45.741595+00:00
-- url     : https://prove2.me/submissions/2b6b8877-2885-43aa-b532-b50a7d4505ef

import Mathlib
import Definitions.Def_Bridges_VoiceLeadingSorted
theorem solution {n : ℕ} (x y : Fin n → ℤ) (σ : Equiv.Perm (Fin n)) :
    vlCostN (fun i => x (σ i)) y = vlCostN x y := by
  unfold vlCostN
  apply le_antisymm
  · -- an optimal assignment for `x` transports to one for `x ∘ σ`
    obtain ⟨ρ, -, hρ⟩ := Finset.exists_mem_eq_inf' ⟨1, Finset.mem_univ 1⟩
      (fun ρ : Equiv.Perm (Fin n) => ∑ i, Int.natAbs (x i - y (ρ i)))
    rw [hρ]
    calc _ ≤ ∑ i, Int.natAbs (x (σ i) - y ((σ.trans ρ) i)) :=
          Finset.inf'_le (fun τ : Equiv.Perm (Fin n) => ∑ i, Int.natAbs (x (σ i) - y (τ i)))
            (Finset.mem_univ (σ.trans ρ))
      _ = ∑ i, Int.natAbs (x i - y (ρ i)) := Equiv.sum_comp σ (fun j => Int.natAbs (x j - y (ρ j)))
  · -- and conversely, through `σ⁻¹`
    obtain ⟨τ, -, hτ⟩ := Finset.exists_mem_eq_inf' ⟨1, Finset.mem_univ 1⟩
      (fun τ : Equiv.Perm (Fin n) => ∑ i, Int.natAbs (x (σ i) - y (τ i)))
    rw [hτ]
    calc _ ≤ ∑ j, Int.natAbs (x j - y ((σ.symm.trans τ) j)) :=
          Finset.inf'_le (fun ρ : Equiv.Perm (Fin n) => ∑ j, Int.natAbs (x j - y (ρ j)))
            (Finset.mem_univ (σ.symm.trans τ))
      _ = ∑ i, Int.natAbs (x (σ i) - y (τ i)) := by
          rw [← Equiv.sum_comp σ]
          simp [Equiv.trans_apply]
