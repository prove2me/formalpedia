-- Prove2me | solution 1 for Catalog.Probability.NeuralCoding.SparseEntropy.log_sum_choose_sub_entropy_abs_le
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-20T12:15:56.294913+00:00
-- url     : https://prove2.me/submissions/93b1f25c-dee4-432d-b1f7-cb13de4291f0

import Mathlib
import Definitions.Def_Probability_SparseEntropyLowerBound

open Finset Real in
theorem solution {N k : ℕ} (hk : 0 < k) (h2k : 2 * k ≤ N) :
    |Real.log (∑ j ∈ range (k + 1), (N.choose j : ℝ))
        - (N : ℝ) * Real.binEntropy ((k : ℝ) / N)| ≤ Real.log ((N : ℝ) + 1) := by
  have hkN : k < N := by omega
  have hN : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hkr : (0 : ℝ) < k := by exact_mod_cast hk
  have hkNr : (k : ℝ) < N := by exact_mod_cast hkN
  have h2kr : (2 : ℝ) * k ≤ N := by exact_mod_cast h2k
  set p : ℝ := (k : ℝ) / N with hp
  set q : ℝ := 1 - p with hq
  have hp0 : 0 < p := div_pos hkr hN
  have hphalf : p ≤ 1 / 2 := by
    rw [hp, div_le_iff₀ hN]
    linarith
  have hpq : p ≤ q := by
    rw [hq]
    linarith
  have hq0 : 0 < q := by linarith
  have hNp : (N : ℝ) * p = k := by
    rw [hp]
    field_simp
  have hNq : (N : ℝ) * q = (N : ℝ) - k := by
    rw [hq, mul_sub, mul_one, hNp]
  have hpk : p * ((N : ℝ) - k) = q * k := by
    rw [← hNq, ← hNp]
    ring
  have hchoose : ∀ j : ℕ, j < N →
      (N.choose (j + 1) : ℝ) * ((j : ℝ) + 1) = (N.choose j : ℝ) * ((N : ℝ) - j) := by
    intro j hj
    have h := Nat.choose_succ_right_eq N j
    have h' : ((N.choose (j + 1) * (j + 1) : ℕ) : ℝ) = ((N.choose j * (N - j) : ℕ) : ℝ) := by
      rw [h]
    push_cast [Nat.cast_sub hj.le] at h'
    linarith
  -- the binomial probabilities
  set b : ℕ → ℝ := fun j => p ^ j * q ^ (N - j) * (N.choose j : ℝ) with hb
  have hbnn : ∀ j, 0 ≤ b j := fun j => by
    simp only [hb]
    positivity
  have hsum1 : ∑ j ∈ range (N + 1), b j = 1 := by
    have h := (add_pow p q N).symm
    rw [show p + q = 1 by rw [hq]; ring, one_pow] at h
    exact h
  have hratio : ∀ j : ℕ, j < N →
      b (j + 1) * (((j : ℝ) + 1) * ((N : ℝ) - k)) = b j * (((N : ℝ) - j) * k) := by
    intro j hj
    obtain ⟨r, hr⟩ : ∃ r, N = j + 1 + r := ⟨N - (j + 1), by omega⟩
    have e1 : N - (j + 1) = r := by omega
    have e2 : N - j = r + 1 := by omega
    have hc := hchoose j hj
    simp only [hb, e1, e2]
    rw [pow_succ, pow_succ]
    linear_combination (p ^ j * p * q ^ r * ((N : ℝ) - k)) * hc
      + (p ^ j * q ^ r * (N.choose j : ℝ) * ((N : ℝ) - j)) * hpk
  have hinc : ∀ j : ℕ, j < k → b j ≤ b (j + 1) := by
    intro j hj
    have h := hratio j (by omega)
    have hj' : (j : ℝ) + 1 ≤ k := by exact_mod_cast hj
    have hpos : (0 : ℝ) < ((j : ℝ) + 1) * ((N : ℝ) - k) := mul_pos (by positivity) (by linarith)
    have hineq : ((j : ℝ) + 1) * ((N : ℝ) - k) ≤ ((N : ℝ) - j) * k := by
      nlinarith [mul_nonneg (sub_nonneg.2 hj') (by linarith : (0 : ℝ) ≤ (N : ℝ) - k),
        mul_nonneg hkr.le (by linarith : (0 : ℝ) ≤ (k : ℝ) - j)]
    have h2 := mul_le_mul_of_nonneg_left hineq (hbnn j)
    rw [← h] at h2
    exact le_of_mul_le_mul_right h2 hpos
  have hdec : ∀ j : ℕ, k ≤ j → j < N → b (j + 1) ≤ b j := by
    intro j hkj hj
    have h := hratio j hj
    have hkj' : (k : ℝ) ≤ j := by exact_mod_cast hkj
    have hjN : (j : ℝ) < N := by exact_mod_cast hj
    have hpos : (0 : ℝ) < ((j : ℝ) + 1) * ((N : ℝ) - k) := mul_pos (by positivity) (by linarith)
    have hineq : ((N : ℝ) - j) * k ≤ ((j : ℝ) + 1) * ((N : ℝ) - k) := by
      nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ (N : ℝ) - k) (by linarith : (0 : ℝ) ≤ (j : ℝ) + 1 - k),
        mul_nonneg hkr.le (by linarith : (0 : ℝ) ≤ (j : ℝ) - k)]
    have h2 := mul_le_mul_of_nonneg_left hineq (hbnn j)
    rw [← h] at h2
    exact le_of_mul_le_mul_right h2 hpos
  have hdown : ∀ d : ℕ, d ≤ k → b (k - d) ≤ b k := by
    intro d
    induction d with
    | zero => intro _; simp
    | succ d ih =>
      intro hd
      have h1 := hinc (k - (d + 1)) (by omega)
      rw [show k - (d + 1) + 1 = k - d by omega] at h1
      exact le_trans h1 (ih (by omega))
  have hupw : ∀ d : ℕ, k + d ≤ N → b (k + d) ≤ b k := by
    intro d
    induction d with
    | zero => intro _; simp
    | succ d ih =>
      intro hd
      have h1 := hdec (k + d) (by omega) (by omega)
      rw [show k + d + 1 = k + (d + 1) by omega] at h1
      exact le_trans h1 (ih (by omega))
  have hmax : ∀ j, j ≤ N → b j ≤ b k := by
    intro j hjN
    rcases le_total j k with hjk | hkj
    · have := hdown (k - j) (by omega)
      rwa [show k - (k - j) = j by omega] at this
    · have := hupw (j - k) (by omega)
      rwa [show k + (j - k) = j by omega] at this
  have hbk : 1 / ((N : ℝ) + 1) ≤ b k := by
    have h1 : ∑ j ∈ range (N + 1), b j ≤ ∑ j ∈ range (N + 1), b k :=
      Finset.sum_le_sum fun j hj => hmax j (by have := Finset.mem_range.1 hj; omega)
    rw [hsum1, Finset.sum_const, Finset.card_range, nsmul_eq_mul] at h1
    rw [div_le_iff₀ (by positivity)]
    push_cast at h1
    linarith
  -- the sum of the first `k + 1` binomial coefficients
  set S : ℝ := ∑ j ∈ range (k + 1), (N.choose j : ℝ) with hS
  set P : ℝ := p ^ k * q ^ (N - k) with hP
  have hP0 : 0 < P := by positivity
  have hPle : ∀ j, j ≤ k → P ≤ p ^ j * q ^ (N - j) := by
    intro j hj
    obtain ⟨d, rfl⟩ : ∃ d, k = j + d := ⟨k - j, by omega⟩
    rw [hP, show N - j = d + (N - (j + d)) by omega, pow_add, pow_add]
    have h1 : p ^ d ≤ q ^ d := pow_le_pow_left₀ hp0.le hpq d
    have h2 : 0 ≤ p ^ j * q ^ (N - (j + d)) := by positivity
    nlinarith
  have hSP_le : S * P ≤ 1 := by
    rw [← hsum1, hS, Finset.sum_mul]
    calc ∑ j ∈ range (k + 1), (N.choose j : ℝ) * P
        ≤ ∑ j ∈ range (k + 1), b j := by
          refine Finset.sum_le_sum fun j hj => ?_
          have hj' : j ≤ k := by have := Finset.mem_range.1 hj; omega
          simp only [hb]
          have := hPle j hj'
          have hc : (0 : ℝ) ≤ (N.choose j : ℝ) := Nat.cast_nonneg _
          nlinarith
      _ ≤ ∑ j ∈ range (N + 1), b j :=
          Finset.sum_le_sum_of_subset_of_nonneg
            (fun x hx => Finset.mem_range.2 (by have := Finset.mem_range.1 hx; omega))
            (fun j _ _ => hbnn j)
  have hSP_ge : 1 / ((N : ℝ) + 1) ≤ S * P := by
    have hSk : (N.choose k : ℝ) ≤ S :=
      Finset.single_le_sum (fun j _ => Nat.cast_nonneg (N.choose j)) (Finset.mem_range.2 (by omega))
    have hbkP : b k = P * (N.choose k : ℝ) := by simp only [hb, hP]
    nlinarith
  have hSpos : 0 < S * P := lt_of_lt_of_le (by positivity) hSP_ge
  have hS0 : 0 < S := by
    by_contra h
    have h' : S ≤ 0 := not_lt.1 h
    nlinarith
  -- entropy is minus the log of the typical probability
  have hH : (N : ℝ) * Real.binEntropy p = -Real.log P := by
    rw [Real.binEntropy, hP, Real.log_mul (by positivity) (by positivity), Real.log_pow,
      Real.log_pow, Real.log_inv, Real.log_inv, Nat.cast_sub hkN.le]
    rw [show (1 : ℝ) - p = q from rfl]
    linear_combination (-Real.log p) * hNp + (-Real.log q) * hNq
  have hN1 : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  rw [hH, sub_neg_eq_add, ← Real.log_mul hS0.ne' hP0.ne', abs_le]
  constructor
  · have := Real.log_le_log (by positivity) hSP_ge
    rw [one_div, Real.log_inv] at this
    linarith
  · have h1 := Real.log_le_log hSpos hSP_le
    rw [Real.log_one] at h1
    have h2 : 0 ≤ Real.log ((N : ℝ) + 1) := Real.log_nonneg (by linarith)
    linarith
