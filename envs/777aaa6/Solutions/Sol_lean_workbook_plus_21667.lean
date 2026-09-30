-- Prove2me | solution 1 for lean_workbook_plus_21667
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-06T00:26:09.340707+00:00
-- url     : https://prove2.me/submissions/668b56ef-012b-471b-87c7-fe67cab2cb63

import Mathlib

set_option autoImplicit false

open Polynomial Finset

namespace FiniteExponentialInterpolation

noncomputable def basis (k : ℕ) : Polynomial ℝ :=
  C ((k.factorial : ℝ)⁻¹) * descPochhammer ℝ k

noncomputable def interpolant (N : ℕ) : Polynomial ℝ :=
  ∑ k ∈ range N, basis k

theorem basis_degree (k : ℕ) : (basis k).natDegree = k := by
  rw [basis, natDegree_C_mul (inv_ne_zero (by exact_mod_cast Nat.factorial_ne_zero k)),
    descPochhammer_natDegree]

theorem basis_top_coefficient (k : ℕ) :
    (basis k).coeff k = (k.factorial : ℝ)⁻¹ := by
  have h : (descPochhammer ℝ k).coeff k = 1 := by
    simpa only [descPochhammer_natDegree] using (monic_descPochhammer ℝ k).coeff_natDegree
  simp only [basis, coeff_C_mul, h, mul_one]

theorem basis_at_nat (k n : ℕ) : (basis k).eval (n : ℝ) = (n.choose k : ℝ) := by
  simp only [basis, eval_mul, eval_C]
  rw [mul_comm, ← div_eq_mul_inv, ← Nat.cast_choose_eq_descPochhammer_div]

theorem interpolant_zero : interpolant 0 = 0 := by simp [interpolant]

theorem interpolant_succ (N : ℕ) : interpolant (N + 1) = interpolant N + basis N := by
  simp only [interpolant, sum_range_succ]

theorem degree_bound (N : ℕ) : (interpolant N).natDegree ≤ N - 1 := by
  apply natDegree_sum_le_of_forall_le
  intro k hk
  rw [basis_degree]
  have := mem_range.mp hk
  omega

theorem top_coefficient (N : ℕ) :
    (interpolant (N + 1)).coeff N = (N.factorial : ℝ)⁻¹ := by
  rw [interpolant_succ, coeff_add, basis_top_coefficient]
  have hz : (interpolant N).coeff N = 0 := by
    by_cases hn : N = 0
    · subst N
      simp [interpolant_zero]
    · apply coeff_eq_zero_of_natDegree_lt
      have := degree_bound N
      omega
  rw [hz, zero_add]

theorem exact_degree (N : ℕ) (hN : 0 < N) : (interpolant N).natDegree = N - 1 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hN)
  apply natDegree_eq_of_le_of_coeff_ne_zero (degree_bound (m + 1))
  simpa only [Nat.add_sub_cancel, top_coefficient] using
    inv_ne_zero (show (m.factorial : ℝ) ≠ 0 by exact_mod_cast Nat.factorial_ne_zero m)

theorem evaluation (N n : ℕ) :
    (interpolant N).eval (n : ℝ) = ((∑ k ∈ range N, n.choose k : ℕ) : ℝ) := by
  simp [interpolant, eval_finset_sum, basis_at_nat]

theorem truncated_binomial_eq (N n : ℕ) (hn : n < N) :
    (∑ k ∈ range N, n.choose k) = 2 ^ n := by
  rw [← Nat.sum_range_choose n]
  symm
  apply sum_subset (range_mono (by omega : n + 1 ≤ N))
  intro k _ hk
  apply Nat.choose_eq_zero_of_lt
  simp only [mem_range, not_lt] at hk
  omega

theorem truncated_binomial_lt (N n : ℕ) (hn : N ≤ n) :
    (∑ k ∈ range N, n.choose k) < 2 ^ n := by
  have h : (∑ k ∈ range (N + 1), n.choose k) ≤ 2 ^ n := by
    rw [← Nat.sum_range_choose n]
    exact sum_le_sum_of_subset_of_nonneg (range_mono (by omega : N + 1 ≤ n + 1))
      (fun _ _ _ => Nat.zero_le _)
  rw [sum_range_succ] at h
  have hp := Nat.choose_pos hn
  omega

theorem grid_values (N n : ℕ) (hn : n < N) :
    (interpolant N).eval (n : ℝ) = (2 : ℝ) ^ n := by
  rw [evaluation, truncated_binomial_eq N n hn]
  norm_cast

theorem beyond_grid (N n : ℕ) (hn : N ≤ n) :
    (interpolant N).eval (n : ℝ) < (2 : ℝ) ^ n := by
  rw [evaluation]
  exact_mod_cast truncated_binomial_lt N n hn

theorem matching_indices (N n : ℕ) :
    (interpolant N).eval (n : ℝ) = (2 : ℝ) ^ n ↔ n < N := by
  constructor
  · intro he
    by_contra hn
    have hlt := beyond_grid N n (Nat.le_of_not_gt hn)
    rw [he] at hlt
    exact lt_irrefl _ hlt
  · exact grid_values N n

theorem next_value (N : ℕ) :
    (interpolant N).eval (N : ℝ) = (2 : ℝ) ^ N - 1 := by
  rw [evaluation]
  have h := Nat.sum_range_choose N
  rw [sum_range_succ, Nat.choose_self] at h
  have hc : ((∑ k ∈ range N, N.choose k : ℕ) : ℝ) + 1 = (2 : ℝ) ^ N := by
    exact_mod_cast h
  linarith

theorem uniqueness (N : ℕ) (hN : 0 < N) (P : Polynomial ℝ)
    (hP : P.natDegree < N)
    (hv : ∀ n : ℕ, n < N → P.eval (n : ℝ) = (2 : ℝ) ^ n) :
    P = interpolant N := by
  apply eq_of_natDegree_lt_card_of_eval_eq P (interpolant N)
    (f := fun i : Fin N => (i.val : ℝ))
  · intro i j h
    apply Fin.ext
    change (i.val : ℝ) = (j.val : ℝ) at h
    exact_mod_cast h
  · intro i
    rw [hv i.val i.isLt, grid_values N i.val i.isLt]
  · rw [Fintype.card_fin, exact_degree N hN]
    exact max_lt hP (by omega)

theorem minimum_degree (N : ℕ) (hN : 0 < N) (P : Polynomial ℝ)
    (hv : ∀ n : ℕ, n < N → P.eval (n : ℝ) = (2 : ℝ) ^ n) :
    N - 1 ≤ P.natDegree := by
  by_contra hn
  have hP : P.natDegree < N := by omega
  rw [uniqueness N hN P hP hv, exact_degree N hN] at hn
  exact hn le_rfl

theorem source_polynomial :
    ∃ P : Polynomial ℝ, P.natDegree = 9 ∧
      (∀ n : ℕ, n < 10 → P.eval (n : ℝ) = (2 : ℝ) ^ n) ∧ P.eval 10 = 1023 := by
  refine ⟨interpolant 10, by simpa using exact_degree 10 (by decide),
    fun n hn => grid_values 10 n hn, ?_⟩
  have h := next_value 10
  norm_num at h
  exact h

theorem source_unique :
    ∃! P : Polynomial ℝ, P.natDegree < 10 ∧
      ∀ n : ℕ, n < 10 → P.eval (n : ℝ) = (2 : ℝ) ^ n := by
  refine ⟨interpolant 10, ⟨by rw [exact_degree 10 (by decide)]; norm_num,
    fun n hn => grid_values 10 n hn⟩, ?_⟩
  rintro P ⟨hP, hv⟩
  exact uniqueness 10 (by decide) P hP hv

end FiniteExponentialInterpolation

theorem solution (_x : ℝ) : ∃ P : ℝ → ℝ, ∀ n : ℕ, n < 10 → P n = 2 ^ n := by
  exact ⟨(FiniteExponentialInterpolation.interpolant 10).eval,
    fun n hn => FiniteExponentialInterpolation.grid_values 10 n hn⟩

#print axioms FiniteExponentialInterpolation.basis
#print axioms FiniteExponentialInterpolation.interpolant
#print axioms FiniteExponentialInterpolation.basis_degree
#print axioms FiniteExponentialInterpolation.basis_top_coefficient
#print axioms FiniteExponentialInterpolation.basis_at_nat
#print axioms FiniteExponentialInterpolation.interpolant_zero
#print axioms FiniteExponentialInterpolation.interpolant_succ
#print axioms FiniteExponentialInterpolation.degree_bound
#print axioms FiniteExponentialInterpolation.top_coefficient
#print axioms FiniteExponentialInterpolation.exact_degree
#print axioms FiniteExponentialInterpolation.evaluation
#print axioms FiniteExponentialInterpolation.truncated_binomial_eq
#print axioms FiniteExponentialInterpolation.truncated_binomial_lt
#print axioms FiniteExponentialInterpolation.grid_values
#print axioms FiniteExponentialInterpolation.beyond_grid
#print axioms FiniteExponentialInterpolation.matching_indices
#print axioms FiniteExponentialInterpolation.next_value
#print axioms FiniteExponentialInterpolation.uniqueness
#print axioms FiniteExponentialInterpolation.minimum_degree
#print axioms FiniteExponentialInterpolation.source_polynomial
#print axioms FiniteExponentialInterpolation.source_unique
#print axioms solution
