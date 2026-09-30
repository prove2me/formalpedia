-- Prove2me | solution 1 for lean_workbook_plus_40279
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T22:18:41.894649+00:00
-- url     : https://prove2.me/submissions/c9c0826f-1fef-47d3-b0e1-c86ab7955d6c

import Mathlib

namespace BarycentricMomentIdentities

open Polynomial

theorem denominator_ne_zero {F I : Type*} [Field F] [DecidableEq I]
    (s : Finset I) (a : I → F) (ha : Set.InjOn a s) {i : I} (hi : i ∈ s) :
    (∏ j ∈ s.erase i, (a i - a j)) ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro j hj
  apply sub_ne_zero.mpr
  intro he
  exact (Finset.mem_erase.mp hj).1 ((ha hi (Finset.mem_erase.mp hj).2 he).symm)

theorem polynomial_coefficient {F I : Type*} [Field F] [DecidableEq I]
    (s : Finset I) (a : I → F) (ha : Set.InjOn a s)
    (P : Polynomial F) (hP : P.degree < s.card) :
    (∑ i ∈ s, P.eval (a i) / ∏ j ∈ s.erase i, (a i - a j)) =
      P.coeff (s.card - 1) := by
  exact (Lagrange.coeff_eq_sum ha hP).symm

theorem moment_table {F I : Type*} [Field F] [DecidableEq I]
    (s : Finset I) (a : I → F) (ha : Set.InjOn a s)
    (k : ℕ) (hk : k < s.card) :
    (∑ i ∈ s, a i ^ k / ∏ j ∈ s.erase i, (a i - a j)) =
      if k = s.card - 1 then 1 else 0 := by
  have hp : (X ^ k : Polynomial F).degree < s.card := by
    rw [degree_X_pow]
    exact_mod_cast hk
  have h := polynomial_coefficient s a ha (X ^ k) hp
  simpa [coeff_X_pow, eq_comm] using h

theorem lower_moments_vanish {F I : Type*} [Field F] [DecidableEq I]
    (s : Finset I) (a : I → F) (ha : Set.InjOn a s)
    (k : ℕ) (hk : k + 1 < s.card) :
    (∑ i ∈ s, a i ^ k / ∏ j ∈ s.erase i, (a i - a j)) = 0 := by
  rw [moment_table s a ha k (by omega), if_neg (by omega)]

theorem highest_moment {F I : Type*} [Field F] [DecidableEq I]
    (s : Finset I) (a : I → F) (ha : Set.InjOn a s) (hs : s.Nonempty) :
    (∑ i ∈ s, a i ^ (s.card - 1) / ∏ j ∈ s.erase i, (a i - a j)) = 1 := by
  have hc : 0 < s.card := Finset.card_pos.mpr hs
  rw [moment_table s a ha (s.card - 1) (by omega), if_pos rfl]

theorem inverse_denominators_sum {F I : Type*} [Field F] [DecidableEq I]
    (s : Finset I) (a : I → F) (ha : Set.InjOn a s) (hs : 1 < s.card) :
    (∑ i ∈ s, (∏ j ∈ s.erase i, (a i - a j))⁻¹) = 0 := by
  simpa using lower_moments_vanish s a ha 0 (by simpa using hs)

theorem source_identity (n : ℕ) (hn : 1 < n) (a : Fin n → ℝ)
    (ha : Function.Injective a) :
    (∑ i, (∏ j ∈ Finset.univ.erase i, (a i - a j))⁻¹) = 0 := by
  simpa using inverse_denominators_sum Finset.univ a ha.injOn (by simpa using hn)

theorem source_denominators_nonzero (n : ℕ) (a : Fin n → ℝ)
    (ha : Function.Injective a) (i : Fin n) :
    (∏ j ∈ Finset.univ.erase i, (a i - a j)) ≠ 0 := by
  exact denominator_ne_zero Finset.univ a ha.injOn (Finset.mem_univ i)

theorem source_highest_moment (n : ℕ) (hn : 0 < n) (a : Fin n → ℝ)
    (ha : Function.Injective a) :
    (∑ i, a i ^ (n - 1) / ∏ j ∈ Finset.univ.erase i, (a i - a j)) = 1 := by
  have hs : (Finset.univ : Finset (Fin n)).Nonempty :=
    ⟨⟨0, hn⟩, Finset.mem_univ _⟩
  simpa using highest_moment Finset.univ a ha.injOn hs

theorem included_diagonal_product (n : ℕ) (a : Fin n → ℝ) (i : Fin n) :
    (∏ j, (a i - a j)) = 0 := by
  exact Finset.prod_eq_zero (Finset.mem_univ i) (sub_self (a i))

end BarycentricMomentIdentities

theorem solution (n : ℕ) (hn : 1 < n) (a : Fin n → ℝ) (ha : a.Injective) :
    ∑ i, (∏ j, (a i - a j))⁻¹ = 0 := by
  have hsource := BarycentricMomentIdentities.source_identity n hn a ha
  simp only [BarycentricMomentIdentities.included_diagonal_product, inv_zero,
    Finset.sum_const_zero]

