-- Prove2me | solution 1 for DiophantineLattice.isInhomMin_translate
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-18T02:02:39.888808+00:00
-- url     : https://prove2.me/submissions/a4706e6d-b278-4faf-9b78-a2042481a131

import Mathlib
import Definitions.Def_Novelty_DiophantineLatticeSpectralGap
import Definitions.Def_Novelty_DiophantineLatticeExactOrder
open DiophantineLattice Finset in
theorem solution {n : ℕ} (B : Matrix (Fin n) (Fin n) ℚ) (t : Fin n → ℚ) (k : Fin n → ℤ)
    {mu : ℚ} (h : IsInhomMin B t mu) :
    IsInhomMin B (fun i => t i + emb k i) mu := by
  obtain ⟨⟨m0, hm0⟩, hall⟩ := h
  refine ⟨⟨fun i => m0 i + k i, ?_⟩, ?_⟩
  · have e : (fun i => (fun i => t i + emb k i) i - emb (fun i => m0 i + k i) i)
        = fun i => t i - emb m0 i := by
      funext i
      simp only [emb]
      push_cast
      ring
    rw [e, hm0]
  · intro m
    have e : (fun i => (fun i => t i + emb k i) i - emb m i)
        = fun i => t i - emb (fun j => m j - k j) i := by
      funext i
      simp only [emb]
      push_cast
      ring
    rw [e]
    exact hall _
