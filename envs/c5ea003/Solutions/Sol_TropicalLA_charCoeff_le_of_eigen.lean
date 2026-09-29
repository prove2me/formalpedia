-- Prove2me | solution 1 for TropicalLA.charCoeff_le_of_eigen
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-20T09:50:33.84455+00:00
-- url     : https://prove2.me/submissions/16b6ce42-6ccb-4193-b1b9-be2bdafedb18

import Mathlib
import Definitions.Def_Algebra_TropicalLinearAlgebra_TropicalCharPoly
import Definitions.Def_Algebra_TropicalLinearAlgebra_TropicalEigenvalue

open Finset TropicalLA in
theorem solution {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι] {A : Matrix ι ι ℝ}
    {lam : ℝ} {v : ι → ℝ} (h : IsTropEigen A lam v) {k : ℕ} (hk : k ≤ Fintype.card ι) :
    charCoeff A k ≤ k * lam := by
  have hne : (admPairs ι k).Nonempty := by
    obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq
      (show k ≤ (univ : Finset ι).card by simpa using hk)
    exact ⟨(s, 1), by simp [admPairs, hs]⟩
  unfold charCoeff
  rw [dif_pos hne]
  apply Finset.sup'_le
  rintro ⟨s, σ⟩ hp
  simp only [admPairs, Finset.mem_filter, Finset.mem_univ, true_and] at hp
  obtain ⟨hcard, hmaps⟩ := hp
  dsimp only
  -- every edge is dominated by the eigen-equation
  have hedge : ∀ i, A i (σ i) ≤ lam + v i - v (σ i) := by
    intro i
    have h1 := Finset.le_sup' (fun j => A i j + v j) (mem_univ (σ i))
    have h2 : univ.sup' univ_nonempty (fun j => A i j + v j) = lam + v i := h i
    simp only at h1
    linarith
  -- `σ` permutes `s`, so the potential terms cancel
  have himage : s.image σ = s := by
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hx
      exact hmaps y hy
    · simp [Finset.card_image_of_injective _ σ.injective]
  have hsum : ∑ i ∈ s, v (σ i) = ∑ i ∈ s, v i := by
    rw [← Finset.sum_image (f := v) (g := σ) (fun x _ y _ hxy => σ.injective hxy), himage]
  unfold minorWeight
  calc ∑ i ∈ s, A i (σ i) ≤ ∑ i ∈ s, (lam + v i - v (σ i)) :=
        Finset.sum_le_sum fun i _ => hedge i
    _ = k * lam := by
      rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, hsum, Finset.sum_const, hcard,
        nsmul_eq_mul]
      ring
