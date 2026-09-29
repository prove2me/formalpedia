-- Prove2me | solution 1 for Catalog.Probability.SeedRec.lfsr_stream_lt
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-17T21:09:17.419719+00:00
-- url     : https://prove2.me/submissions/f6fe455e-a6ae-4d1d-b205-a73efaa2cb6d

import Mathlib
import Definitions.Def_Probability_PRNGLFSRDetection
import Definitions.Def_Probability_PRNGSeedRecovery
open Catalog.Probability.SeedRec in
theorem solution {K : Type*} [CommRing K] {L : ℕ} (c σ : Fin L → K) (k : ℕ) (h : k < L) :
    (lfsrPRNG c).stream σ k = σ ⟨k, h⟩ := by
  have hstate : ∀ (σ : Fin L → K) (i : ℕ) (h : i < L) (k : ℕ),
      ((lfsrStep c)^[k] σ) ⟨i, h⟩ = (lfsrPRNG c).stream σ (i + k) := by
    intro σ i
    induction i with
    | zero =>
      intro h k
      simp [PRNG.stream, lfsrPRNG, lfsrOut, h]
    | succ i ih =>
      intro h k
      have h' : i < L := by omega
      rw [show i + 1 + k = i + (k + 1) by ring, ← ih h' (k + 1), Function.iterate_succ_apply']
      simp [lfsrStep, h]
  have hlt : ∀ (σ : Fin L → K) (k : ℕ) (h : k < L), (lfsrPRNG c).stream σ k = σ ⟨k, h⟩ := by
    intro σ k h
    simpa using (hstate σ k h 0).symm
  exact hlt σ k h
