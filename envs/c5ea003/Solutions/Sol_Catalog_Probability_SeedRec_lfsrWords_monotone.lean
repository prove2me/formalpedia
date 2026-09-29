-- Prove2me | solution 1 for Catalog.Probability.SeedRec.lfsrWords_monotone
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-18T01:00:48.060695+00:00
-- url     : https://prove2.me/submissions/2bc7414b-dc16-4804-b1e8-f2de6390bf27

import Mathlib
import Definitions.Def_Probability_PRNGLFSRDetection
import Definitions.Def_Probability_PRNGSeedRecovery
import Definitions.Def_Probability_PRNGBerlekampMassey
import Definitions.Def_Probability_PRNGLinearComplexity
import Definitions.Def_Probability_PRNGComplexityHierarchy
open Catalog.Probability.SeedRec in
theorem solution (K : Type*) [CommRing K] [Fintype K] [DecidableEq K] (n : ℕ) : ∀ {L M : ℕ}, 0 < L → L ≤ M →
    lfsrWords K L n ⊆ lfsrWords K M n := by
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
  have hmono : ∀ {L M : ℕ}, 0 < L → L ≤ M → lfsrWords K L n ⊆ lfsrWords K M n := by
    intro L M hL hLM x hx
    obtain ⟨m, rfl⟩ : ∃ m, M = m + L := ⟨M - L, by omega⟩
    simp only [lfsrWords, Finset.mem_image, Finset.mem_univ, true_and] at hx ⊢
    obtain ⟨p, rfl⟩ := hx
    obtain ⟨c, σ⟩ := p
    have hM : 0 < m + L := by omega
    set y : ℕ → K := (lfsrPRNG c).stream σ with hy
    set cc : ℕ → K := fun i => if h : i < L then c ⟨i, h⟩ else 0 with hcc
    set F : ℕ → ℕ → K := fun t j => (if m ≤ j then cc (j - m) else 0) * y (t + j) with hF
    set c' : Fin (m + L) → K := fun j => if m ≤ (j : ℕ) then cc ((j : ℕ) - m) else 0 with hc'
    have hsat : ∀ t, y (t + (m + L)) = ∑ j : Fin (m + L), c' j * y (t + (j : ℕ)) := by
      intro t
      have e1 : y (t + (m + L)) = ∑ i : Fin L, c i * y (t + m + (i : ℕ)) := by
        rw [show t + (m + L) = t + m + L by omega, hy]
        exact hrecG hL c σ (t + m)
      have e2 : ∑ j : Fin (m + L), c' j * y (t + (j : ℕ)) = ∑ j ∈ Finset.range (m + L), F t j := by
        rw [← Fin.sum_univ_eq_sum_range (F t) (m + L)]
      have e3 : ∑ j ∈ Finset.range m, F t j = 0 := by
        refine Finset.sum_eq_zero (fun j hj => ?_)
        rw [Finset.mem_range] at hj
        simp only [hF]
        rw [if_neg (by omega), zero_mul]
      have e4 : ∑ i : Fin L, c i * y (t + m + (i : ℕ)) = ∑ i ∈ Finset.range L, cc i * y (t + m + i) := by
        rw [← Fin.sum_univ_eq_sum_range (fun i => cc i * y (t + m + i)) L]
        exact Finset.sum_congr rfl (fun i _ => by simp only [hcc, dif_pos i.isLt])
      rw [e1, e2, Finset.sum_range_add, e3, zero_add, e4]
      refine Finset.sum_congr rfl (fun i hi => ?_)
      rw [Finset.mem_range] at hi
      simp only [hF]
      rw [if_pos (by omega), Nat.add_sub_cancel_left, show t + (m + i) = t + m + i by omega]
    refine ⟨(c', fun i : Fin (m + L) => y i.val), ?_⟩
    funext i
    simpa [PRNG.pref] using hreproG hM c' y hsat i.val
  intro L M hL hLM
  exact hmono hL hLM
