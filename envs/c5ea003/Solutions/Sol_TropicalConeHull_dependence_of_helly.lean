-- Prove2me | solution 1 for TropicalConeHull.dependence_of_helly
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-20T12:26:10.380008+00:00
-- url     : https://prove2.me/submissions/d3cf33ea-c9eb-4381-8457-208d351d0207

import Mathlib
import Definitions.Def_Tropical_TropicalConvexity_ConeHullOptimization

open Finset TropicalConeHull in
theorem solution {d : ℕ} (hd : 0 < d)
    (helly : ∀ C : Fin (d + 1) → Set (Fin d → ℝ), (∀ k, IsTropCone (C k)) →
      (∀ I : Finset (Fin (d + 1)), I.card ≤ d → ∃ x, ∀ k ∈ I, x ∈ C k) →
      ∃ x, ∀ k, x ∈ C k)
    (p : Fin (d + 1) → Fin d → ℝ) :
    ∃ lam : Fin (d + 1) → ℝ, ∀ (i : Fin d) (k : Fin (d + 1)),
      ∃ j, j ≠ k ∧ lam k + p k i ≤ lam j + p j i := by
  classical
  have hne : ∀ k : Fin (d + 1), (univ.erase k).Nonempty := by
    intro k
    apply Finset.card_pos.1
    rw [card_erase_of_mem (mem_univ k), card_univ, Fintype.card_fin]
    omega
  have hdi : (univ : Finset (Fin d)).Nonempty := ⟨⟨0, hd⟩, mem_univ _⟩
  -- `C k`: the tropical span of the points other than `p k`
  set C : Fin (d + 1) → Set (Fin d → ℝ) := fun k =>
    {x | ∃ μ : Fin (d + 1) → ℝ, ∀ i, x i = (univ.erase k).sup' (hne k) (fun j => μ j + p j i)}
    with hC
  have hcone : ∀ k, IsTropCone (C k) := by
    intro k x hx y hy s t
    obtain ⟨μ, hμ⟩ := hx
    obtain ⟨ν, hν⟩ := hy
    refine ⟨fun j => max (s + μ j) (t + ν j), fun i => ?_⟩
    show max (s + x i) (t + y i) = _
    rw [hμ i, hν i]
    apply le_antisymm
    · apply max_le
      · obtain ⟨j, hj, hjeq⟩ := exists_mem_eq_sup' (hne k) (fun j => μ j + p j i)
        rw [hjeq]
        have h1 := le_sup' (fun j => max (s + μ j) (t + ν j) + p j i) hj
        have h2 := le_max_left (s + μ j) (t + ν j)
        simp only at h1 ⊢
        linarith
      · obtain ⟨j, hj, hjeq⟩ := exists_mem_eq_sup' (hne k) (fun j => ν j + p j i)
        rw [hjeq]
        have h1 := le_sup' (fun j => max (s + μ j) (t + ν j) + p j i) hj
        have h2 := le_max_right (s + μ j) (t + ν j)
        simp only at h1 ⊢
        linarith
    · apply sup'_le
      intro j hj
      show max (s + μ j) (t + ν j) + p j i ≤ _
      have h1 := le_sup' (fun j => μ j + p j i) hj
      have h2 := le_sup' (fun j => ν j + p j i) hj
      simp only at h1 h2
      rcases le_total (s + μ j) (t + ν j) with h | h
      · rw [max_eq_right h]
        exact le_max_of_le_right (by linarith)
      · rw [max_eq_left h]
        exact le_max_of_le_left (by linarith)
  -- any `d` of the cones share one of the points
  have hsmall : ∀ I : Finset (Fin (d + 1)), I.card ≤ d → ∃ x, ∀ k ∈ I, x ∈ C k := by
    intro I hI
    obtain ⟨j, -, hj⟩ := exists_mem_notMem_of_card_lt_card
      (show I.card < (univ : Finset (Fin (d + 1))).card by
        rw [card_univ, Fintype.card_fin]
        omega)
    refine ⟨p j, fun k hk => ?_⟩
    have hjk : j ≠ k := fun h => hj (h ▸ hk)
    refine ⟨fun j' => (univ : Finset (Fin d)).inf' hdi (fun i => p j i - p j' i), fun i => ?_⟩
    apply le_antisymm
    · have h1 := le_sup' (fun j' => (univ : Finset (Fin d)).inf' hdi (fun i => p j i - p j' i) + p j' i)
        (mem_erase.2 ⟨hjk, mem_univ j⟩)
      have h0 : (univ : Finset (Fin d)).inf' hdi (fun i => p j i - p j i) = 0 := by simp
      simp only [h0, zero_add] at h1
      exact h1
    · apply sup'_le
      intro j' _
      have := inf'_le (fun i => p j i - p j' i) (mem_univ i)
      simp only at this ⊢
      linarith
  obtain ⟨x, hx⟩ := helly C hcone hsmall
  -- the maximal coefficients
  refine ⟨fun j => (univ : Finset (Fin d)).inf' hdi (fun i => x i - p j i), fun i k => ?_⟩
  obtain ⟨μ, hμ⟩ := hx k
  obtain ⟨j, hj, hjeq⟩ := exists_mem_eq_sup' (hne k) (fun j => μ j + p j i)
  have hxi := hμ i
  rw [hjeq] at hxi
  refine ⟨j, (mem_erase.1 hj).1, ?_⟩
  have hμj : μ j ≤ (univ : Finset (Fin d)).inf' hdi (fun i => x i - p j i) := by
    apply le_inf'
    intro i' _
    have h1 := le_sup' (fun j => μ j + p j i') hj
    rw [← hμ i'] at h1
    show μ j ≤ x i' - p j i'
    linarith
  have hk : (univ : Finset (Fin d)).inf' hdi (fun i => x i - p k i) ≤ x i - p k i :=
    inf'_le (fun i => x i - p k i) (mem_univ i)
  show (univ : Finset (Fin d)).inf' hdi (fun i => x i - p k i) + p k i
    ≤ (univ : Finset (Fin d)).inf' hdi (fun i => x i - p j i) + p j i
  linarith
