-- Prove2me | solution 2 for Catalog.Probability.SeedRec.lfsr_stream_determined_by_two_L
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-18T12:56:00.847777+00:00
-- url     : https://prove2.me/submissions/41785aec-a728-4218-985e-f55ba5d42a44

import Mathlib
import Definitions.Def_Probability_PRNGLFSRDetection
import Definitions.Def_Probability_PRNGSeedRecovery
open Catalog.Probability.SeedRec Polynomial in
theorem solution {K : Type*} [CommRing K] {L : ℕ} [Nontrivial K] [NeZero L]
    (c c' : Fin L → K) (σ σ' : Fin L → K)
    (hagree : ∀ t < 2 * L, (lfsrPRNG c).stream σ t = (lfsrPRNG c').stream σ' t) :
    ∀ t, (lfsrPRNG c).stream σ t = (lfsrPRNG c').stream σ' t := by
  -- the LFSR recurrence, for arbitrary taps and seed
  have hrec : ∀ (e τ : Fin L → K) (t : ℕ),
      (lfsrPRNG e).stream τ (t + L) = ∑ j : Fin L, e j * (lfsrPRNG e).stream τ (t + (j : ℕ)) := by
    intro e τ t
    have hstate : ∀ (τ : Fin L → K) (i : ℕ) (h : i < L) (k : ℕ),
        ((lfsrStep e)^[k] τ) ⟨i, h⟩ = (lfsrPRNG e).stream τ (i + k) := by
      intro τ i
      induction i with
      | zero =>
        intro h k
        simp [PRNG.stream, lfsrPRNG, lfsrOut, h]
      | succ i ih =>
        intro h k
        have h' : i < L := by omega
        rw [show i + 1 + k = i + (k + 1) by ring, ← ih h' (k + 1), Function.iterate_succ_apply']
        simp [lfsrStep, h]
    have hlt : ∀ (τ : Fin L → K) (k : ℕ) (h : k < L), (lfsrPRNG e).stream τ k = τ ⟨k, h⟩ := by
      intro τ k h
      simpa using (hstate τ k h 0).symm
    have hrec : ∀ (τ : Fin L → K) (t : ℕ), (lfsrPRNG e).stream τ (t + L) =
        ∑ j : Fin L, e j * (lfsrPRNG e).stream τ (t + (j : ℕ)) := by
      intro τ t
      have hL : 0 < L := Nat.pos_of_ne_zero (NeZero.ne L)
      have h1 := hstate τ (L - 1) (by omega) (t + 1)
      rw [show L - 1 + (t + 1) = t + L by omega, Function.iterate_succ_apply'] at h1
      rw [← h1]
      have hn : ¬ (L - 1 + 1 < L) := by omega
      simp only [lfsrStep, hn, dite_false]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [add_comm t (j : ℕ), ← hstate τ j.val j.isLt t]
    exact hrec τ t
  set y := (lfsrPRNG c).stream σ with hy
  set y' := (lfsrPRNG c').stream σ' with hy'
  -- the defect `z t = Σ (cⱼ - c'ⱼ) y(t+j)` measures how far `y` is from the `c'` recurrence
  set z : ℕ → K := fun t => ∑ j : Fin L, (c j - c' j) * y (t + (j : ℕ)) with hz
  -- `z` obeys the `c`-recurrence, since every shift of `y` does and the recurrence is linear
  have hzrec : ∀ t, z (t + L) = ∑ i : Fin L, c i * z (t + (i : ℕ)) := by
    intro t
    simp only [hz]
    have hshift : ∀ j : Fin L, y (t + L + (j : ℕ))
        = ∑ i : Fin L, c i * y (t + (j : ℕ) + (i : ℕ)) := by
      intro j
      rw [show t + L + (j : ℕ) = (t + (j : ℕ)) + L by ring, hy]
      exact hrec c σ (t + (j : ℕ))
    simp only [hshift, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [show t + (j : ℕ) + (i : ℕ) = t + (i : ℕ) + (j : ℕ) by ring]
    ring
  -- `z` vanishes on the initial window, by the agreement on the first `2L` terms
  have hz0 : ∀ t, t < L → z t = 0 := by
    intro t ht
    have hyt : y (t + L) = ∑ j : Fin L, c j * y (t + (j : ℕ)) := by rw [hy]; exact hrec c σ t
    have hyt' : y' (t + L) = ∑ j : Fin L, c' j * y' (t + (j : ℕ)) := by
      rw [hy']; exact hrec c' σ' t
    have hagL : y (t + L) = y' (t + L) := hagree (t + L) (by omega)
    have hagj : ∀ j : Fin L, y (t + (j : ℕ)) = y' (t + (j : ℕ)) :=
      fun j => hagree _ (by have := j.isLt; omega)
    have e1 : ∑ j : Fin L, c' j * y' (t + (j : ℕ)) = ∑ j : Fin L, c' j * y (t + (j : ℕ)) :=
      Finset.sum_congr rfl fun j _ => by rw [hagj j]
    show ∑ j : Fin L, (c j - c' j) * y (t + (j : ℕ)) = 0
    have e2 : ∑ j : Fin L, (c j - c' j) * y (t + (j : ℕ))
        = (∑ j : Fin L, c j * y (t + (j : ℕ))) - ∑ j : Fin L, c' j * y (t + (j : ℕ)) := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [e2, ← hyt, ← e1, ← hyt', hagL, sub_self]
  -- a solution of the recurrence vanishing on its initial window vanishes everywhere
  have hzall : ∀ n, z n = 0 := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      by_cases hn : n < L
      · exact hz0 n hn
      · obtain ⟨t, rfl⟩ : ∃ t, n = t + L := ⟨n - L, by omega⟩
        rw [hzrec t]
        exact Finset.sum_eq_zero fun i _ => by
          rw [ih (t + (i : ℕ)) (by have := i.isLt; omega), mul_zero]
  -- so `y` also obeys the `c'` recurrence; conclude by strong induction
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    by_cases hn : n < 2 * L
    · exact hagree n hn
    · obtain ⟨t, rfl⟩ : ∃ t, n = t + L := ⟨n - L, by omega⟩
      have hyt : y (t + L) = ∑ j : Fin L, c j * y (t + (j : ℕ)) := by rw [hy]; exact hrec c σ t
      have hyt' : y' (t + L) = ∑ j : Fin L, c' j * y' (t + (j : ℕ)) := by
        rw [hy']; exact hrec c' σ' t
      have hyy : ∀ j : Fin L, y' (t + (j : ℕ)) = y (t + (j : ℕ)) :=
        fun j => (ih _ (by have := j.isLt; omega)).symm
      have hzt : ∑ j : Fin L, (c j - c' j) * y (t + (j : ℕ)) = 0 := hzall t
      show y (t + L) = y' (t + L)
      have hR : ∑ j : Fin L, c' j * y' (t + (j : ℕ)) = ∑ j : Fin L, c' j * y (t + (j : ℕ)) :=
        Finset.sum_congr rfl fun j _ => by rw [hyy j]
      rw [hyt, hyt', hR]
      have e2 : ∑ j : Fin L, (c j - c' j) * y (t + (j : ℕ))
          = (∑ j : Fin L, c j * y (t + (j : ℕ))) - ∑ j : Fin L, c' j * y (t + (j : ℕ)) := by
        rw [← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun j _ => by ring
      rw [e2] at hzt
      exact sub_eq_zero.mp hzt
