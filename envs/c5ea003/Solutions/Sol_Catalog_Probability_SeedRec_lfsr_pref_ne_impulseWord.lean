-- Prove2me | solution 1 for Catalog.Probability.SeedRec.lfsr_pref_ne_impulseWord
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-18T00:39:39.175495+00:00
-- url     : https://prove2.me/submissions/a4a16a27-dca1-4042-94be-b52a1497439b

import Mathlib
import Definitions.Def_Probability_PRNGLFSRDetection
import Definitions.Def_Probability_PRNGSeedRecovery
import Definitions.Def_Probability_PRNGRecoveryAlgorithm
import Definitions.Def_Probability_PRNGRouterCapacity
open Catalog.Probability.SeedRec in
theorem solution {K : Type*} [CommRing K] {L n : ℕ} [Nontrivial K] (c σ : Fin L → K) (hL : L < n) :
    (lfsrPRNG c).pref n σ ≠ impulseWord K n := by
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
  intro heq
  have hσ : σ = fun _ => 0 := by
    funext i
    have hc := congrFun heq ⟨i.val, lt_trans i.isLt hL⟩
    simp only [PRNG.pref, impulseWord, Fin.val_mk] at hc
    rw [hltG c σ i.val i.isLt] at hc
    have hne : ¬ ((i : ℕ) + 1 = n) := by have := i.isLt; omega
    simpa [hne] using hc
  subst hσ
  have hc := congrFun heq ⟨n - 1, by omega⟩
  simp only [PRNG.pref, impulseWord, Fin.val_mk, show n - 1 + 1 = n by omega, if_pos,
    hzeroG c (n - 1)] at hc
  exact zero_ne_one hc
