-- Prove2me | solution 2 for Catalog.Probability.SeedRec.lfsr_pref_zero
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-18T06:54:20.27081+00:00
-- url     : https://prove2.me/submissions/48aa8a21-a9aa-49a7-87a7-a7e3d6598bad

import Mathlib
import Definitions.Def_Probability_PRNGLFSRDetection
import Definitions.Def_Probability_PRNGSeedRecovery
import Definitions.Def_Probability_PRNGClassifier
import Definitions.Def_Probability_PRNGComplexityHierarchy
import Definitions.Def_Probability_PRNGRouterCapacity
open Catalog.Probability.SeedRec in
theorem solution (K : Type*) [CommRing K] {L : ℕ}
    (c : Fin L → K) (n : ℕ) :
    (lfsrPRNG c).pref n (fun _ => 0) = fun _ => 0 := by
  have hstateG : ∀ {L : ℕ} (c σ : Fin L → K) (i : ℕ) (h : i < L) (k : ℕ),
      ((lfsrStep c)^[k] σ) ⟨i, h⟩ = (lfsrPRNG c).stream σ (i + k) := by
    intro L c σ i
    induction i with
    | zero =>
      intro h k
      simp [PRNG.stream, lfsrPRNG, lfsrOut, h]
    | succ i ih =>
      intro h k
      have h' : i < L := by omega
      rw [show i + 1 + k = i + (k + 1) by ring, ← ih h' (k + 1), Function.iterate_succ_apply']
      simp [lfsrStep, h]
  have hltG : ∀ {L : ℕ} (c σ : Fin L → K) (k : ℕ) (h : k < L),
      (lfsrPRNG c).stream σ k = σ ⟨k, h⟩ := by
    intro L c σ k h
    simpa using (hstateG c σ k h 0).symm
  have hrecG : ∀ {L : ℕ}, 0 < L → ∀ (c σ : Fin L → K) (t : ℕ),
      (lfsrPRNG c).stream σ (t + L) = ∑ j : Fin L, c j * (lfsrPRNG c).stream σ (t + (j : ℕ)) := by
    intro L hL c σ t
    have h1 := hstateG c σ (L - 1) (by omega) (t + 1)
    rw [show L - 1 + (t + 1) = t + L by omega, Function.iterate_succ_apply'] at h1
    rw [← h1]
    have hn : ¬ (L - 1 + 1 < L) := by omega
    simp only [lfsrStep, hn, dite_false]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [add_comm t (j : ℕ), ← hstateG c σ j.val j.isLt t]
  have hzeroG : ∀ {L : ℕ} (c : Fin L → K) (t : ℕ), (lfsrPRNG c).stream (fun _ => 0) t = 0 := by
    intro L c t
    have hf : lfsrStep c (fun _ => (0 : K)) = fun _ => (0 : K) := by
      funext i
      simp [lfsrStep]
    simp [PRNG.stream, lfsrPRNG, Function.iterate_fixed hf, lfsrOut]
  have hreproG : ∀ {L : ℕ}, 0 < L → ∀ (c : Fin L → K) (y : ℕ → K),
      (∀ t, y (t + L) = ∑ j : Fin L, c j * y (t + (j : ℕ))) →
      ∀ t, (lfsrPRNG c).stream (fun i : Fin L => y i.val) t = y t := by
    intro L hL c y hy t
    induction t using Nat.strong_induction_on with
    | _ t ih =>
      by_cases ht : t < L
      · rw [hltG c _ t ht]
      · obtain ⟨s, rfl⟩ : ∃ s, t = s + L := ⟨t - L, by omega⟩
        rw [hrecG hL c _ s, hy s]
        refine Finset.sum_congr rfl (fun j _ => ?_)
        rw [ih (s + j) (by have := j.isLt; omega)]
  funext t
  simpa [PRNG.pref] using hzeroG c t.val
