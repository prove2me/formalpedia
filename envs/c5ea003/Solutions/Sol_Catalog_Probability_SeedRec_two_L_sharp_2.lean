-- Prove2me | solution 2 for Catalog.Probability.SeedRec.two_L_sharp
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-18T00:44:04.113741+00:00
-- url     : https://prove2.me/submissions/43deb53d-fae0-4fb8-a744-55f350831b47

import Mathlib
import Definitions.Def_Probability_PRNGLFSRDetection
import Definitions.Def_Probability_PRNGSeedRecovery
import Definitions.Def_Probability_PRNGBerlekampMassey
open Catalog.Probability.SeedRec in
theorem solution {K : Type*} [CommRing K] {L : ℕ} [NeZero L] [Nontrivial K] :
    ∃ c c' σ σ' : Fin L → K,
      (∀ t < 2 * L - 1, (lfsrPRNG c).stream σ t = (lfsrPRNG c').stream σ' t) ∧
        (lfsrPRNG c).stream σ (2 * L - 1) ≠ (lfsrPRNG c').stream σ' (2 * L - 1) := by
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
  have hL : 0 < L := Nat.pos_of_ne_zero (NeZero.ne L)
  set e : Fin L → K := fun i => if (i : ℕ) = L - 1 then 1 else 0 with he
  set d : Fin L → K := fun j => if (j : ℕ) = 0 then 1 else 0 with hd
  refine ⟨0, d, e, e, ?_, ?_⟩
  · intro t ht
    by_cases hlt : t < L
    · rw [hltG 0 e t hlt, hltG d e t hlt]
    · obtain ⟨s, rfl⟩ : ∃ s, t = s + L := ⟨t - L, by omega⟩
      have hA : (lfsrPRNG (0 : Fin L → K)).stream e (s + L) = 0 := by
        rw [hrecG hL]
        simp
      have hs : s < L - 1 := by omega
      have hB : (lfsrPRNG d).stream e (s + L) = 0 := by
        rw [hrecG hL]
        rw [Finset.sum_eq_single (⟨0, hL⟩ : Fin L)]
        · simp only [hd, Fin.val_mk, if_pos]
          rw [one_mul, add_zero, hltG d e s (by omega), he]
          simp only [Fin.val_mk]
          rw [if_neg (by omega)]
        · intro j _ hj
          have hj' : (j : ℕ) ≠ 0 := fun h0 => hj (Fin.ext (by simpa using h0))
          simp only [hd]
          rw [if_neg hj', zero_mul]
        · intro hmem
          exact absurd (Finset.mem_univ _) hmem
      rw [hA, hB]
  · have hA : (lfsrPRNG (0 : Fin L → K)).stream e (2 * L - 1) = 0 := by
      rw [show 2 * L - 1 = (L - 1) + L by omega, hrecG hL]
      simp
    have hB : (lfsrPRNG d).stream e (2 * L - 1) = 1 := by
      rw [show 2 * L - 1 = (L - 1) + L by omega, hrecG hL]
      rw [Finset.sum_eq_single (⟨0, hL⟩ : Fin L)]
      · simp only [hd, Fin.val_mk, if_pos]
        rw [one_mul, add_zero, hltG d e (L - 1) (by omega), he]
        simp
      · intro j _ hj
        have hj' : (j : ℕ) ≠ 0 := fun h0 => hj (Fin.ext (by simpa using h0))
        simp only [hd]
        rw [if_neg hj', zero_mul]
      · intro hmem
        exact absurd (Finset.mem_univ _) hmem
    rw [hA, hB]
    exact zero_ne_one
