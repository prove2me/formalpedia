-- Prove2me | solution 1 for Catalog.Probability.SeedRec.lfsr_detect
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-17T21:21:08.914005+00:00
-- url     : https://prove2.me/submissions/30cb0388-9259-4384-8423-de583c1253ff

import Mathlib
import Definitions.Def_Probability_PRNGLFSRDetection
import Definitions.Def_Probability_PRNGSeedRecovery
open Catalog.Probability.SeedRec in
theorem solution {K : Type*} [CommRing K] {L : ℕ} [NeZero L] (c : Fin L → K) (y : ℕ → K) :
    SatisfiesLFSR c y ↔ ∃ σ : Fin L → K, ∀ t, (lfsrPRNG c).stream σ t = y t := by
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
  have hrec : ∀ (σ : Fin L → K) (t : ℕ), (lfsrPRNG c).stream σ (t + L) =
      ∑ j : Fin L, c j * (lfsrPRNG c).stream σ (t + (j : ℕ)) := by
    intro σ t
    have hL : 0 < L := Nat.pos_of_ne_zero (NeZero.ne L)
    have h1 := hstate σ (L - 1) (by omega) (t + 1)
    rw [show L - 1 + (t + 1) = t + L by omega, Function.iterate_succ_apply'] at h1
    rw [← h1]
    have hn : ¬ (L - 1 + 1 < L) := by omega
    simp only [lfsrStep, hn, dite_false]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [add_comm t (j : ℕ), ← hstate σ j.val j.isLt t]
  have hrepro : ∀ y : ℕ → K, SatisfiesLFSR c y → ∀ t, (lfsrPRNG c).stream (fun i : Fin L => y i.val) t = y t := by
    intro y hy t
    induction t using Nat.strong_induction_on with
    | _ t ih =>
      by_cases ht : t < L
      · rw [hlt _ t ht]
      · obtain ⟨s, rfl⟩ : ∃ s, t = s + L := ⟨t - L, by omega⟩
        rw [hrec _ s, hy s]
        refine Finset.sum_congr rfl (fun j _ => ?_)
        rw [ih (s + j) (by have := j.isLt; omega)]
  constructor
  · intro hy
    exact ⟨fun i => y i.val, hrepro y hy⟩
  · rintro ⟨σ, hσ⟩
    have e : y = (lfsrPRNG c).stream σ := funext fun t => (hσ t).symm
    subst e
    intro t
    exact hrec σ t
