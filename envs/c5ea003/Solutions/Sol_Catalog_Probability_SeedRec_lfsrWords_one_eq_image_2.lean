-- Prove2me | solution 2 for Catalog.Probability.SeedRec.lfsrWords_one_eq_image
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-18T06:45:02.857042+00:00
-- url     : https://prove2.me/submissions/2ac39ecc-6577-473f-aec4-50222f97f318

import Mathlib
import Definitions.Def_Probability_PRNGLFSRDetection
import Definitions.Def_Probability_PRNGSeedRecovery
import Definitions.Def_Probability_PRNGEnumerationL1
import Definitions.Def_Probability_PRNGComplexityHierarchy
import Definitions.Def_Probability_PRNGRouterCapacity
open Catalog.Probability.SeedRec in
theorem solution (K : Type*) [Field K] [Fintype K] [DecidableEq K] (n : ℕ) :
    lfsrWords K 1 n = (geomParams K).image (geomWord n) := by
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
  have horder1 : ∀ (c σ : Fin 1 → K) (t : ℕ), (lfsrPRNG c).stream σ t = c 0 ^ t * σ 0 := by
    intro c σ t
    have hstep1 : ∀ τ : Fin 1 → K, lfsrStep c τ = fun _ => c 0 * τ 0 := by
      intro τ
      funext i
      fin_cases i
      simp [lfsrStep]
    have hit : ∀ k : ℕ, (lfsrStep c)^[k] σ = fun _ => c 0 ^ k * σ 0 := by
      intro k
      induction k with
      | zero =>
        funext i
        fin_cases i
        simp
      | succ k ih =>
        rw [Function.iterate_succ_apply', ih, hstep1]
        funext i
        simp [pow_succ]
        ring
    simp [PRNG.stream, lfsrPRNG, lfsrOut, hit]
  have himg : ∀ n : ℕ, lfsrWords K 1 n = (geomParams K).image (geomWord n) := by
    intro n
    apply Finset.Subset.antisymm
    · intro x hx
      simp only [lfsrWords, Finset.mem_image, Finset.mem_univ, true_and] at hx
      obtain ⟨p, rfl⟩ := hx
      by_cases h0 : p.2 0 = 0
      · refine Finset.mem_image.mpr ⟨(0, 0), ?_, ?_⟩
        · simp [geomParams]
        · funext i
          simp only [geomWord, PRNG.pref]
          rw [horder1 p.1 p.2 i.val, h0]
          simp
      · refine Finset.mem_image.mpr ⟨(p.2 0, p.1 0), ?_, ?_⟩
        · simp only [geomParams, Finset.mem_union, Finset.mem_product, Finset.mem_compl,
            Finset.mem_singleton, Finset.mem_univ, and_true]
          exact Or.inl h0
        · funext i
          simp only [geomWord, PRNG.pref]
          rw [horder1 p.1 p.2 i.val]
    · intro x hx
      obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp hx
      simp only [lfsrWords, Finset.mem_image, Finset.mem_univ, true_and]
      refine ⟨((fun _ => p.2), (fun _ => p.1)), ?_⟩
      funext i
      simp only [geomWord, PRNG.pref]
      rw [horder1 (fun _ => p.2) (fun _ => p.1) i.val]
  exact himg n
