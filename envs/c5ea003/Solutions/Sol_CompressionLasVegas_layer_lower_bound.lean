-- Prove2me | solution 1 for CompressionLasVegas.layer_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-17T21:51:26.754082+00:00
-- url     : https://prove2.me/submissions/7094b7a3-69d6-4cbb-95e1-dd65072025fd

import Definitions.Def_Speculative_AutoResearch_CompressionLasVegasOWF
open CompressionOWF CompressionLasVegas in
theorem solution {α : Type*} (c : α → ℕ) (T : Finset α) (bnd : ℕ → ℕ) (S : ℕ)
    (h : ∀ s < S, (T.filter (fun y => c y ≤ s)).card ≤ bnd s) :
    S * T.card ≤ (∑ y ∈ T, c y) + ∑ s ∈ Finset.range S, bnd s := by
  classical
  have hpt : ∀ y, S ≤ c y + ((Finset.range S).filter (fun s => c y ≤ s)).card := by
    intro y
    by_cases hy : S ≤ c y
    · omega
    · have heq : (Finset.range S).filter (fun s => c y ≤ s) = Finset.Ico (c y) S := by
        ext s
        simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
        omega
      rw [heq, Nat.card_Ico]
      omega
  calc S * T.card = ∑ _y ∈ T, S := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
    _ ≤ ∑ y ∈ T, (c y + ((Finset.range S).filter (fun s => c y ≤ s)).card) :=
        Finset.sum_le_sum (fun y _ => hpt y)
    _ = (∑ y ∈ T, c y) + ∑ s ∈ Finset.range S, (T.filter (fun y => c y ≤ s)).card := by
        rw [Finset.sum_add_distrib]
        congr 1
        simp only [Finset.card_filter]
        exact Finset.sum_comm
    _ ≤ (∑ y ∈ T, c y) + ∑ s ∈ Finset.range S, bnd s := by
        gcongr with s hs
        exact h s (Finset.mem_range.mp hs)
