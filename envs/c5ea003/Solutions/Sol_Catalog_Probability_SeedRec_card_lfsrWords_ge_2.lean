-- Prove2me | solution 2 for Catalog.Probability.SeedRec.card_lfsrWords_ge
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-18T00:35:12.14893+00:00
-- url     : https://prove2.me/submissions/f31718e5-c48f-48d7-9ad1-22cce6fd803f

import Mathlib
import Definitions.Def_Probability_PRNGLFSRDetection
import Definitions.Def_Probability_PRNGSeedRecovery
import Definitions.Def_Probability_PRNGBerlekampMassey
import Definitions.Def_Probability_PRNGComplexityHierarchy
import Definitions.Def_Probability_PRNGLinearComplexity
open Catalog.Probability.SeedRec in
theorem solution (K : Type*) [CommRing K] [Fintype K] [DecidableEq K] [Nontrivial K] (L n : ℕ)
    [NeZero L] (h : L ≤ n) : Fintype.card K ^ L ≤ (lfsrWords K L n).card := by
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
  have hinj : Function.Injective (fun σ : Fin L → K => (lfsrPRNG (0 : Fin L → K)).pref n σ) := by
    intro σ σ' he
    funext i
    have hi : (i : ℕ) < n := lt_of_lt_of_le i.isLt h
    have hc := congrFun he ⟨i.val, hi⟩
    simp only [PRNG.pref, Fin.val_mk] at hc
    rw [hltG 0 σ i.val i.isLt, hltG 0 σ' i.val i.isLt] at hc
    simpa using hc
  have h1 : (Finset.univ.image (fun σ : Fin L → K => (lfsrPRNG (0 : Fin L → K)).pref n σ))
      ⊆ lfsrWords K L n := by
    intro x hx
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at hx
    obtain ⟨σ, rfl⟩ := hx
    simp only [lfsrWords, Finset.mem_image, Finset.mem_univ, true_and]
    exact ⟨(0, σ), rfl⟩
  calc Fintype.card K ^ L = (Finset.univ : Finset (Fin L → K)).card := by simp
    _ = (Finset.univ.image (fun σ : Fin L → K => (lfsrPRNG (0 : Fin L → K)).pref n σ)).card :=
        (Finset.card_image_of_injective _ hinj).symm
    _ ≤ (lfsrWords K L n).card := Finset.card_le_card h1
