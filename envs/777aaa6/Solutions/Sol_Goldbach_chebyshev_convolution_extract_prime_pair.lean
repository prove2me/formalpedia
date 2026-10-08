-- Prove2me | solution 1 for Goldbach.chebyshev_convolution_extract_prime_pair
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-05T01:48:15.276963+00:00
-- url     : https://prove2.me/submissions/77ef1751-e960-48f9-8645-8679f258fe8a

import Mathlib.NumberTheory.Chebyshev
import Mathlib.Tactic

open scoped BigOperators ArithmeticFunction.vonMangoldt
open Finset Real
set_option autoImplicit false

namespace GoldbachChebyshevExtraction
noncomputable section

private theorem prime_power_weight (x : ℝ) (hx : 4 ≤ x) :
    Chebyshev.psi x - Chebyshev.theta x ≤
      Real.log 4 * Real.sqrt x + 2 * x ^ ((1 : ℝ) / 3) * Real.log x := by
  have hx0 : 0 ≤ x := by linarith
  have hk : 2 ≤ ⌊Real.log x / Real.log 2⌋₊ := by
    apply Nat.le_floor
    rw [le_div_iff₀ (Real.log_pos (by norm_num))]
    have hl := Real.log_le_log (by norm_num : (0 : ℝ) < 4) hx
    have h4 : Real.log (4 : ℝ) = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
    norm_num at ⊢
    linarith
  rw [Chebyshev.psi_eq_theta_add_sum_theta (by linarith), add_sub_cancel_left,
    ← Finset.add_sum_Ioc_eq_sum_Icc hk]
  have ht : (∑ i ∈ Finset.Ioc 2 ⌊Real.log x / Real.log 2⌋₊,
      Chebyshev.theta (x ^ ((1 : ℝ) / i))) ≤
      2 * x ^ ((1 : ℝ) / 3) * Real.log x := by
    calc
      _ ≤ ∑ i ∈ Finset.Ioc 2 ⌊Real.log x / Real.log 2⌋₊,
          Real.log 4 * x ^ ((1 : ℝ) / 3) := by
        apply Finset.sum_le_sum
        intro i hi
        have hi3 : 3 ≤ i := by have := (Finset.mem_Ioc.mp hi).1; omega
        apply le_trans (Chebyshev.theta_le_log4_mul_x (Real.rpow_nonneg hx0 _))
        apply mul_le_mul_of_nonneg_left _ (Real.log_nonneg (by norm_num))
        apply Real.rpow_le_rpow_of_exponent_le (by linarith : 1 ≤ x)
        exact one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 3)
          (by exact_mod_cast hi3 : (3 : ℝ) ≤ (i : ℝ))
      _ = ((Finset.Ioc 2 ⌊Real.log x / Real.log 2⌋₊).card : ℝ) *
          (Real.log 4 * x ^ ((1 : ℝ) / 3)) := by simp
      _ ≤ (Real.log x / Real.log 2) * (Real.log 4 * x ^ ((1 : ℝ) / 3)) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        calc
          _ ≤ (⌊Real.log x / Real.log 2⌋₊ : ℝ) := by
            exact_mod_cast (show (Finset.Ioc 2 ⌊Real.log x / Real.log 2⌋₊).card ≤
                ⌊Real.log x / Real.log 2⌋₊ by simp only [Nat.card_Ioc]; omega)
          _ ≤ _ := Nat.floor_le (div_nonneg (Real.log_nonneg (by linarith)) (Real.log_nonneg (by norm_num)))
      _ = _ := by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
        field_simp
        ring
  have hs := Chebyshev.theta_le_log4_mul_x (Real.rpow_nonneg hx0 ((1 : ℝ) / 2))
  rw [← Real.sqrt_eq_rpow] at hs
  convert add_le_add hs ht using 1
  norm_num [Real.sqrt_eq_rpow]

private lemma mangoldt_upper (N n : ℕ) (hn : n ≤ N) : Λ n ≤ Real.log N := by
  by_cases hn0 : n = 0
  · subst n
    simp only [ArithmeticFunction.map_zero]
    exact Real.log_natCast_nonneg N
  · exact ArithmeticFunction.vonMangoldt_le_log.trans
      (Real.log_le_log (by exact_mod_cast Nat.pos_of_ne_zero hn0) (by exact_mod_cast hn))

private theorem contamination_bound (N : ℕ) (hN4 : 4 ≤ N) :
    (∑ m ∈ Finset.range (N+1),
      if Nat.Prime m ∧ Nat.Prime (N-m) then (0:ℝ) else Λ m * Λ (N-m)) ≤
    2 * (Real.log 4 * Real.sqrt N + 2 * (N : ℝ) ^ ((1 : ℝ) / 3) * Real.log N) *
      Real.log N := by
  classical
  let B := (Finset.Ioc 0 N).filter (fun n => ¬ Nat.Prime n)
  let f : ℕ → ℝ := fun m => if Nat.Prime m ∧ Nat.Prime (N-m) then 0 else Λ m * Λ (N-m)
  let g : ℕ → ℝ := fun m => if m ∈ B then Λ m * Real.log N else 0
  have hg0 (m : ℕ) : 0 ≤ g m := by
    dsimp [g]
    split_ifs
    · exact mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.log_natCast_nonneg N)
    · exact le_rfl
  have hpoint (m : ℕ) (hm : m ∈ Finset.range (N+1)) : f m ≤ g m + g (N-m) := by
    have hmN : m ≤ N := by have := Finset.mem_range.mp hm; omega
    by_cases hf : f m = 0
    · rw [hf]; exact add_nonneg (hg0 m) (hg0 (N-m))
    have hm0 : Λ m ≠ 0 := by intro h; apply hf; simp [f,h]
    have hn0 : Λ (N-m) ≠ 0 := by intro h; apply hf; simp [f,h]
    have hpq : ¬ (Nat.Prime m ∧ Nat.Prime (N-m)) := by
      intro h; apply hf; simp [f,h]
    have heqf : f m = Λ m * Λ (N-m) := if_neg hpq
    have hmem : m ∈ B ∨ N-m ∈ B := by
      by_cases hp : Nat.Prime m
      · apply Or.inr
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_Ioc.mpr ⟨?_,Nat.sub_le N m⟩, fun hq => hpq ⟨hp,hq⟩⟩
        by_contra hz
        have hz' : N-m = 0 := by omega
        exact hn0 (by simp [hz'])
      · apply Or.inl
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_Ioc.mpr ⟨?_,hmN⟩,hp⟩
        by_contra hz
        have hz' : m = 0 := by omega
        exact hm0 (by simp [hz'])
    rcases hmem with h | h
    · have heq : g m = Λ m * Real.log N := if_pos h
      have hu : f m ≤ Λ m * Real.log N := by
        rw [heqf]
        exact mul_le_mul_of_nonneg_left (mangoldt_upper N (N-m) (Nat.sub_le N m))
          ArithmeticFunction.vonMangoldt_nonneg
      linarith [hg0 (N-m)]
    · have heq : g (N-m) = Λ (N-m) * Real.log N := if_pos h
      have hu : f m ≤ Λ (N-m) * Real.log N := by
        rw [heqf, mul_comm]
        exact mul_le_mul_of_nonneg_left (mangoldt_upper N m hmN)
          ArithmeticFunction.vonMangoldt_nonneg
      linarith [hg0 m]
  have hsum : (∑ m ∈ Finset.range (N+1), f m) ≤
      2 * ∑ m ∈ Finset.range (N+1), g m := by
    calc
      _ ≤ ∑ m ∈ Finset.range (N+1), (g m + g (N-m)) := Finset.sum_le_sum hpoint
      _ = _ := by rw [Finset.sum_add_distrib, ← Finset.sum_range_reflect g (N+1)]; simp; ring
  have hg : (∑ m ∈ Finset.range (N+1), g m) ≤
      (∑ m ∈ B, Λ m) * Real.log N := by
    calc
      _ = ∑ m ∈ (Finset.range (N+1)).filter (fun m => m ∈ B), Λ m * Real.log N := by
        simp only [g, Finset.sum_filter]
      _ ≤ ∑ m ∈ B, Λ m * Real.log N := Finset.sum_le_sum_of_subset_of_nonneg
        (fun m hm => (Finset.mem_filter.mp hm).2)
        (fun _ _ _ => mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.log_natCast_nonneg N))
      _ = _ := by rw [Finset.sum_mul]
  have hw : (∑ m ∈ B, Λ m) ≤
      Real.log 4 * Real.sqrt N + 2 * (N : ℝ) ^ ((1 : ℝ) / 3) * Real.log N := by
    have hw := prime_power_weight (N : ℝ) (by exact_mod_cast hN4)
    rw [Chebyshev.psi_sub_theta_eq_sum_not_prime] at hw
    simpa [B] using hw
  have hgfinal : (∑ m ∈ Finset.range (N+1), g m) ≤
      (Real.log 4 * Real.sqrt N + 2 * (N : ℝ) ^ ((1 : ℝ) / 3) * Real.log N) *
        Real.log N := hg.trans (mul_le_mul_of_nonneg_right hw (Real.log_natCast_nonneg N))
  change (∑ m ∈ Finset.range (N+1), f m) ≤ _
  linarith [hsum,hgfinal]

end
end GoldbachChebyshevExtraction

theorem solution (N : ℕ) (hN4 : 4 ≤ N)
    (hlarge : (2 * (Real.log 4 * Real.sqrt N + 2 * (N : ℝ) ^ ((1 : ℝ) / 3) * Real.log N) * Real.log N) <
      ∑ m ∈ Finset.range (N+1),
        ArithmeticFunction.vonMangoldt m * ArithmeticFunction.vonMangoldt (N-m)) :
    ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ N = p+q := by
  classical
  by_contra hpair
  have hb := GoldbachChebyshevExtraction.contamination_bound N hN4
  have heq : (∑ m ∈ Finset.range (N+1),
      if Nat.Prime m ∧ Nat.Prime (N-m) then (0:ℝ) else Λ m * Λ (N-m)) =
      ∑ m ∈ Finset.range (N+1), Λ m * Λ (N-m) := by
    apply Finset.sum_congr rfl
    intro m hm
    apply if_neg
    intro h
    exact hpair ⟨m,N-m,h.1,h.2,by have := Finset.mem_range.mp hm; omega⟩
  rw [heq] at hb
  linarith

#print axioms solution
