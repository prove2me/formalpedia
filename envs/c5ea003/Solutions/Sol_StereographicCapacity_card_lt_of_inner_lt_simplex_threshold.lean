-- Prove2me | solution 1 for StereographicCapacity.card_lt_of_inner_lt_simplex_threshold
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-20T00:36:37.299033+00:00
-- url     : https://prove2.me/submissions/c5315aeb-2d09-4a24-8596-57d595a6eef6

import Mathlib
open Finset in
theorem solution {ι E : Type*} [DecidableEq ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (s : Finset ι) (v : ι → E) (N : ℕ)
    (hN : 2 ≤ N)
    (hunit : ∀ i ∈ s, ‖v i‖ = 1)
    (hpair : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
      inner ℝ (v i) (v j) < -(1 / ((N : ℝ) - 1))) :
    s.card < N := by
  by_contra hge
  replace hge := le_of_not_gt hge
  have hNR : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hn : (N : ℝ) ≤ s.card := by exact_mod_cast hge
  -- `0 ≤ ‖Σ v_i‖² = Σ_i Σ_j ⟨v_i, v_j⟩`
  have hsq : 0 ≤ ∑ i ∈ s, ∑ j ∈ s, inner ℝ (v i) (v j) := by
    have h := real_inner_self_nonneg (x := ∑ i ∈ s, v i)
    rw [sum_inner] at h
    simp only [inner_sum] at h
    exact h
  -- each row is `1 + Σ_{j ≠ i} ⟨v_i, v_j⟩ < 1 - (|s| - 1)/(N - 1)`
  have hrow : ∀ i ∈ s, ∑ j ∈ s, inner ℝ (v i) (v j) < 1 - ((s.card : ℝ) - 1) / ((N : ℝ) - 1) := by
    intro i hi
    rw [← add_sum_erase s _ hi]
    have hii : inner ℝ (v i) (v i) = (1 : ℝ) := by
      rw [real_inner_self_eq_norm_sq, hunit i hi]
      norm_num
    have hcard1 : 1 ≤ s.card := by omega
    have hne : (s.erase i).Nonempty := by
      rw [← card_pos, card_erase_of_mem hi]
      omega
    have hlt : ∑ j ∈ s.erase i, inner ℝ (v i) (v j) < ∑ j ∈ s.erase i, -(1 / ((N : ℝ) - 1)) :=
      sum_lt_sum_of_nonempty hne
        (fun j hj => hpair i hi j (mem_of_mem_erase hj) (ne_of_mem_erase hj).symm)
    rw [sum_const, card_erase_of_mem hi, nsmul_eq_mul, Nat.cast_sub hcard1, Nat.cast_one] at hlt
    have e : ((s.card : ℝ) - 1) * -(1 / ((N : ℝ) - 1)) = -(((s.card : ℝ) - 1) / ((N : ℝ) - 1)) := by
      ring
    rw [hii]
    linarith
  have htot := sum_lt_sum_of_nonempty (card_pos.1 (by omega)) hrow
  rw [sum_const, nsmul_eq_mul] at htot
  -- but `|s| ≥ N` makes the right-hand side `≤ 0`
  have hfrac : 1 ≤ ((s.card : ℝ) - 1) / ((N : ℝ) - 1) := by
    rw [le_div_iff₀ (by linarith)]
    linarith
  have hneg : (s.card : ℝ) * (1 - ((s.card : ℝ) - 1) / ((N : ℝ) - 1)) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg _) (by linarith)
  linarith
