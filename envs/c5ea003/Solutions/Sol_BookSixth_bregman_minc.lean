-- Prove2me | solution 1 for BookSixth.bregman_minc
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-09-16T02:10:16.370859+00:00
-- url     : https://prove2.me/submissions/6146b379-28dc-46e4-8883-044e4e0ee35b

import Mathlib
import Definitions.Def_BookSixth
import Definitions.Def_BregmanMincWeights
import Theorems.Thm_BookSixth_bregman_minc_claimA
import Theorems.Thm_BookSixth_bregman_minc_claimB
open scoped BigOperators
open BookSixth BregmanMincWeights

noncomputable section

private def rowSum' {n : ℕ} (A : Matrix (Fin n) (Fin n) ℕ) (i : Fin n) : ℕ := ∑ j, A i j

private lemma preS_eq_image {n : ℕ} (A : Matrix (Fin n) (Fin n) ℕ) (σ : Equiv.Perm (Fin n))
    (i : Fin n) :
    preS A σ i = Finset.image σ.symm (Finset.univ.filter (fun j => A i j = 1)) := by
  ext l
  simp only [preS, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
  constructor
  · intro h; exact ⟨σ l, h, σ.symm_apply_apply l⟩
  · rintro ⟨j, hj, rfl⟩; rwa [σ.apply_symm_apply]

private lemma permanent_eq_aSys {n : ℕ} (A : Matrix (Fin n) (Fin n) ℕ)
    (hA : ∀ i j, A i j ≤ 1) : permanent A = (aSys A).card := by
  simp only [permanent, aSys]
  have key : ∀ σ : Equiv.Perm (Fin n), ∏ i, A i (σ i) = if (∀ i, A i (σ i) = 1) then 1 else 0 := by
    intro σ; split_ifs with h
    · exact Finset.prod_eq_one (fun i _ => h i)
    · push_neg at h; obtain ⟨i, hi⟩ := h
      exact Finset.prod_eq_zero (Finset.mem_univ i) (by have := hA i (σ i); omega)
  simp_rw [key, ← Finset.card_filter]

theorem solution {n : ℕ} (A : Matrix (Fin n) (Fin n) ℕ) (hA : ∀ i j, A i j ≤ 1)
    (hrows : ∀ i, 0 < ∑ j, A i j) :
    (permanent A : ℝ) ≤ ∏ i, ((Nat.factorial (∑ j, A i j) : ℕ) : ℝ) ^
      (1 / ((∑ j, A i j : ℕ) : ℝ)) := by
  -- Reduce to counting A-systems
  have hperm : (permanent A : ℝ) = ((aSys A).card : ℝ) := by
    exact_mod_cast permanent_eq_aSys A hA
  rw [hperm]
  by_cases hasy : (aSys A).card = 0
  · simp [hasy]; apply Finset.prod_nonneg; intro i _; positivity
  -- Define B = ∏_i (d_i!)^{-1/d_i}
  let B := ∏ i : Fin n, ((Nat.factorial (∑ j, A i j) : ℕ) : ℝ) ^ (-(1 : ℝ) / ((∑ j, A i j : ℕ) : ℝ))
  have hB_pos : 0 < B :=
    Finset.prod_pos (fun i _ => Real.rpow_pos_of_pos (by positivity) _)
  -- Lower bound via Claim B: |aSys| × n! × B ≤ ∑_σ ∑_π qW
  have hge : ((aSys A).card : ℝ) * ((n.factorial : ℝ) * B) ≤
      ∑ σ ∈ aSys A, ∑ π : Equiv.Perm (Fin n), qW A σ π := by
    have hconst : ((aSys A).card : ℝ) * ((n.factorial : ℝ) * B) =
        ∑ _σ ∈ aSys A, ((n.factorial : ℝ) * B) := by
      simp [Finset.sum_const, nsmul_eq_mul]
    rw [hconst]
    apply Finset.sum_le_sum; intro σ hσ
    linarith [bregman_minc_claimB n A hA hrows σ hσ]
  -- Upper bound via Claim A: ∑_σ ∑_π qW ≤ n!
  have hle : ∑ σ ∈ aSys A, ∑ π : Equiv.Perm (Fin n), qW A σ π ≤ n.factorial := by
    calc ∑ σ ∈ aSys A, ∑ π : Equiv.Perm (Fin n), qW A σ π
        = ∑ π : Equiv.Perm (Fin n), ∑ σ ∈ aSys A, qW A σ π := Finset.sum_comm
      _ ≤ ∑ _ : Equiv.Perm (Fin n), (1 : ℝ) :=
          Finset.sum_le_sum (fun π _ => bregman_minc_claimA n A hA hrows π)
      _ = n.factorial := by simp [Finset.sum_const, Fintype.card_perm, nsmul_eq_mul]
  -- Combine: |aSys| × B ≤ 1
  have hn_pos : (0 : ℝ) < n.factorial := by positivity
  have hcard_B : ((aSys A).card : ℝ) * B ≤ 1 := by
    have h1 : ((aSys A).card : ℝ) * (n.factorial * B) ≤ n.factorial := le_trans hge hle
    have h2 : (n.factorial : ℝ) * (((aSys A).card : ℝ) * B) ≤ n.factorial * 1 := by
      rw [mul_one]
      linarith [show (n.factorial : ℝ) * (((aSys A).card : ℝ) * B) =
                    ((aSys A).card : ℝ) * (n.factorial * B) from by ring]
    exact le_of_mul_le_mul_left h2 hn_pos
  -- |aSys| ≤ B⁻¹ = ∏_i (d_i!)^{1/d_i}
  have hcard_le : ((aSys A).card : ℝ) ≤ B⁻¹ := by
    calc ((aSys A).card : ℝ)
        = ((aSys A).card : ℝ) * B * B⁻¹ := by field_simp
      _ ≤ 1 * B⁻¹ := mul_le_mul_of_nonneg_right hcard_B (by positivity)
      _ = B⁻¹ := one_mul _
  have hBinv : B⁻¹ = ∏ i : Fin n, ((Nat.factorial (∑ j, A i j) : ℕ) : ℝ) ^
      ((1 : ℝ) / ((∑ j, A i j : ℕ) : ℝ)) := by
    simp only [B, ← Finset.prod_inv_distrib]
    congr 1; ext i
    rw [← Real.rpow_neg (by positivity)]; ring_nf
  exact hcard_le.trans (hBinv ▸ le_refl _)

end
