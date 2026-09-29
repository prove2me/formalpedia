-- Prove2me | solution 1 for DiophantineLattice.sum_sq_sub_self_even
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-18T01:52:21.767425+00:00
-- url     : https://prove2.me/submissions/256c641c-29c6-455f-96a0-d48e3e240cf1

import Mathlib
import Definitions.Def_Novelty_DiophantineLatticeSpectralGap
import Definitions.Def_Novelty_DiophantineLatticeCompleteSquare
import Definitions.Def_Novelty_DiophantineLatticeTorsionGap
open DiophantineLattice Finset in
theorem solution {n : ℕ} (m : Fin n → ℤ) :
    ∃ k : ℤ, 0 ≤ k ∧ (∑ i, ((m i) ^ 2 - m i)) = 2 * k := by
  have hterm : ∀ a : ℤ, 0 ≤ a ^ 2 - a ∧ 2 ∣ (a ^ 2 - a) := by
    intro a
    refine ⟨?_, ?_⟩
    · by_cases ha : a ≤ 0
      · nlinarith
      · have h1 : 1 ≤ a := by omega
        nlinarith
    · rcases Int.even_or_odd a with ⟨b, rfl⟩ | ⟨b, rfl⟩
      · exact ⟨2 * b ^ 2 - b, by ring⟩
      · exact ⟨2 * b ^ 2 + b, by ring⟩
  have h1 : 0 ≤ ∑ i, ((m i) ^ 2 - m i) :=
    Finset.sum_nonneg (fun i _ => (hterm (m i)).1)
  have h2 : (2 : ℤ) ∣ ∑ i, ((m i) ^ 2 - m i) :=
    Finset.dvd_sum (fun i _ => (hterm (m i)).2)
  obtain ⟨k, hk⟩ := h2
  exact ⟨k, by omega, hk⟩
