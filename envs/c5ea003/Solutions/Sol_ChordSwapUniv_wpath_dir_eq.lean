-- Prove2me | solution 1 for ChordSwapUniv.wpath_dir_eq
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-19T11:39:42.507222+00:00
-- url     : https://prove2.me/submissions/dda2b207-825c-473a-9094-968293ea80f6

import Mathlib
import Definitions.Def_Applications_NeuralCoding_ChordSwapUniversality
open ChordSwapUniv Finset in
theorem solution {c : ℝ} {n : ℕ} (hn : 1 ≤ n) :
    dir (wpathQ c n) (idf n) = 2 * c * ((n : ℝ) - 1) := by
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
