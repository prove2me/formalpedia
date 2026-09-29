-- Prove2me | solution 1 for ChordSwapUniv.wpath_RQ_window
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-19T11:44:11.60726+00:00
-- url     : https://prove2.me/submissions/cab74f71-7285-4139-b240-ffa80675a899

import Mathlib
import Definitions.Def_Applications_NeuralCoding_ChordSwapUniversality
open ChordSwapUniv Finset in
theorem solution {c : ℝ} (hc : 0 ≤ c) {n : ℕ} (hn2 : 2 ≤ n) :
    6 * c / (n : ℝ) ^ 3 ≤ RQ (wpathQ c n) (idf n) ∧
      RQ (wpathQ c n) (idf n) ≤ 12 * c / (n : ℝ) ^ 3 := by
  have hn : 1 ≤ n := by omega
  have hdir : dir (wpathQ c n) (idf n) = 2 * c * ((n : ℝ) - 1) := by
    -- pass from `Fin n` to `range n`
    have h1 : ∀ F : ℕ → ℕ → ℝ,
        ∑ x : Fin n, ∑ y : Fin n, F x y = ∑ x ∈ range n, ∑ y ∈ range n, F x y := by
      intro F
      rw [Fin.sum_univ_eq_sum_range (fun x => ∑ y : Fin n, F x y) n]
      exact sum_congr rfl (fun x _ => Fin.sum_univ_eq_sum_range (F x) n)
    unfold dir wpathQ idf
    refine (h1 (fun a b => (if a + 1 = b ∨ b + 1 = a then c else 0) * ((a : ℝ) - b) ^ 2)).trans ?_
    -- each neighbouring ordered pair contributes `c`
    have hsplit : ∀ a b : ℕ, (if a + 1 = b ∨ b + 1 = a then c else 0) * ((a : ℝ) - b) ^ 2
        = (if a + 1 = b then c else 0) + (if b + 1 = a then c else 0) := by
      intro a b
      by_cases h₁ : a + 1 = b
      · subst h₁
        rw [if_pos (Or.inl rfl), if_pos rfl, if_neg (by omega)]
        push_cast
        ring
      · by_cases h₂ : b + 1 = a
        · subst h₂
          rw [if_pos (Or.inr rfl), if_neg h₁, if_pos rfl]
          push_cast
          ring
        · rw [if_neg (by tauto), if_neg h₁, if_neg h₂]
          ring
    simp only [hsplit, sum_add_distrib]
    rw [sum_comm (f := fun x y => if y + 1 = x then c else 0)]
    simp only [sum_ite_eq]
    -- `#{x < n | x + 1 < n} = n - 1`
    have hcount : ∑ x ∈ range n, (if x + 1 ∈ range n then c else 0) = ((n : ℝ) - 1) * c := by
      rw [← sum_filter]
      have : (range n).filter (fun x => x + 1 ∈ range n) = range (n - 1) := by
        ext x
        simp only [mem_filter, mem_range]
        omega
      rw [this, sum_const, card_range, nsmul_eq_mul, Nat.cast_sub hn, Nat.cast_one]
    rw [hcount]
    ring
  -- the variation `Σ_{x,y} (x − y)² = n²(n² − 1)/6`
  have hs1 : ∀ m : ℕ, ∑ i ∈ range m, (i : ℝ) = (m : ℝ) * ((m : ℝ) - 1) / 2 := by
    intro m
    induction m with
    | zero => simp
    | succ m ih => rw [sum_range_succ, ih]; push_cast; ring
  have hs2 : ∀ m : ℕ, ∑ i ∈ range m, (i : ℝ) ^ 2
      = (m : ℝ) * ((m : ℝ) - 1) * (2 * (m : ℝ) - 1) / 6 := by
    intro m
    induction m with
    | zero => simp
    | succ m ih => rw [sum_range_succ, ih]; push_cast; ring
  have hvr : vr (idf n) = (n : ℝ) ^ 2 * ((n : ℝ) ^ 2 - 1) / 6 := by
    have h1 : ∀ F : ℕ → ℕ → ℝ,
        ∑ x : Fin n, ∑ y : Fin n, F x y = ∑ x ∈ range n, ∑ y ∈ range n, F x y := by
      intro F
      rw [Fin.sum_univ_eq_sum_range (fun x => ∑ y : Fin n, F x y) n]
      exact sum_congr rfl (fun x _ => Fin.sum_univ_eq_sum_range (F x) n)
    unfold vr idf
    refine (h1 (fun a b => ((a : ℝ) - b) ^ 2)).trans ?_
    have hrow : ∀ x : ℕ, ∑ y ∈ range n, ((x : ℝ) - y) ^ 2
        = (n : ℝ) * (x : ℝ) ^ 2 - 2 * (x : ℝ) * ∑ y ∈ range n, (y : ℝ)
          + ∑ y ∈ range n, (y : ℝ) ^ 2 := by
      intro x
      simp only [sub_sq, sum_add_distrib, sum_sub_distrib, sum_const, card_range, nsmul_eq_mul,
        ← mul_sum]
    simp only [hrow, sum_add_distrib, sum_sub_distrib, sum_const, card_range, nsmul_eq_mul,
      ← mul_sum, ← sum_mul, hs1, hs2]
    ring
  have hP : (2 : ℝ) ≤ n := by exact_mod_cast hn2
  have hRQ : RQ (wpathQ c n) (idf n) = 12 * c / ((n : ℝ) ^ 2 * ((n : ℝ) + 1)) := by
    unfold RQ
    rw [hdir, hvr]
    have hq : (n : ℝ) ^ 2 - 1 ≠ 0 := by nlinarith
    have hn0 : (n : ℝ) ≠ 0 := by linarith
    have hn1 : (n : ℝ) + 1 ≠ 0 := by linarith
    field_simp
    ring
  rw [hRQ]
  constructor
  · rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have : 0 ≤ c * (n : ℝ) ^ 2 * ((n : ℝ) - 1) := by
      apply mul_nonneg (mul_nonneg hc (sq_nonneg _))
      linarith
    nlinarith
  · apply div_le_div_of_nonneg_left (by linarith) (by positivity)
    nlinarith
