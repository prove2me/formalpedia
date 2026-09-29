-- Prove2me | solution 1 for DiophantineLattice.deepHole_spectrum_via_characteristic
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-18T01:57:38.130923+00:00
-- url     : https://prove2.me/submissions/5f64271c-20d3-4414-9a7a-d94a33c5c201

import Mathlib
import Definitions.Def_Novelty_DiophantineLatticeSpectralGap
import Definitions.Def_Novelty_DiophantineLatticeCompleteSquare
import Definitions.Def_Novelty_DiophantineLatticeCharacteristic
import Definitions.Def_Novelty_DiophantineLatticeShiftedTheta
open DiophantineLattice Finset in
theorem solution {n : ℕ} (m : Fin n → ℤ) :
    ∃ k : ℤ, form (1 : Matrix (Fin n) (Fin n) ℚ) (fun i => deepHole n i - emb m i)
      = (n : ℚ) / 4 + 2 * k := by
  have hscale : ∀ (B : Matrix (Fin n) (Fin n) ℚ) (c : ℚ) (x : Fin n → ℚ),
      form B (fun i => c * x i) = c ^ 2 * form B x := by
    intro B c x
    simp only [form, bil, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    refine Finset.sum_congr rfl (fun j _ => ?_)
    ring
  have hzero : ∀ B : Matrix (Fin n) (Fin n) ℚ, form B (fun _ => (0 : ℚ)) = 0 := by
    intro B
    simp [form, bil]
  have hembz : ∀ m : Fin n → ℤ, emb m = 0 → m = 0 := by
    intro m hm
    funext i
    have := congrFun hm i
    simp only [emb, Pi.zero_apply] at this
    exact_mod_cast this
  have hembne : ∀ {m : Fin n → ℤ}, m ≠ 0 → emb m ≠ 0 := by
    intro m h he
    exact h (hembz m he)
  have hone : ∀ x : Fin n → ℚ, form (1 : Matrix (Fin n) (Fin n) ℚ) x = ∑ i, x i ^ 2 := by
    intro x
    simp only [form, bil, Matrix.one_apply]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finset.sum_eq_single i]
    · simp
      ring
    · intro j _ hj
      simp [Ne.symm hj]
    · intro hi
      exact absurd (Finset.mem_univ i) hi
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
  obtain ⟨k, hk⟩ : (2 : ℤ) ∣ ∑ i, ((m i) ^ 2 - m i) :=
    Finset.dvd_sum (fun i _ => (hterm (m i)).2)
  refine ⟨k, ?_⟩
  rw [hone]
  have e : ∀ i : Fin n, (deepHole n i - emb m i) ^ 2 = 1 / 4 + (((m i) ^ 2 - m i : ℤ) : ℚ) := by
    intro i
    simp only [deepHole, emb]
    push_cast
    ring
  rw [Finset.sum_congr rfl (fun i _ => e i), Finset.sum_add_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, ← Int.cast_sum, hk]
  push_cast
  ring
