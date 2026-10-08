-- Prove2me | solution 1 for Goldbach.vonMangoldt_convolution_extract_prime_pair
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-04T17:07:22.942056+00:00
-- url     : https://prove2.me/submissions/659d9eec-6f0d-4a8a-8e83-225082b9b24c

import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.Data.Nat.Sqrt
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic

open scoped BigOperators ArithmeticFunction.vonMangoldt
set_option autoImplicit false

namespace GoldbachPrimePowerExtraction
noncomputable section

/-- An over-cover of proper prime powers; nonprime bases are harmless. -/
def powerCover (N : ℕ) : Finset ℕ :=
  ((Finset.Icc 2 (Nat.sqrt N)).product (Finset.Icc 2 (Nat.log 2 N))).image
    (fun t : ℕ × ℕ => t.1 ^ t.2)

lemma cover_card (N : ℕ) : (powerCover N).card ≤ Nat.sqrt N * Nat.log 2 N := by
  have hs : (Finset.Icc 2 (Nat.sqrt N)).card ≤ Nat.sqrt N := by
    simp only [Nat.card_Icc]
    omega
  have hk : (Finset.Icc 2 (Nat.log 2 N)).card ≤ Nat.log 2 N := by
    simp only [Nat.card_Icc]
    omega
  exact Finset.card_image_le.trans
    ((Finset.card_product _ _).le.trans (Nat.mul_le_mul hs hk))

lemma nonprime_mem_cover (N n : ℕ) (hn : n ≤ N)
    (hpp : IsPrimePow n) (hnp : ¬ Nat.Prime n) : n ∈ powerCover N := by
  obtain ⟨p,k,hp,hk,heq⟩ := (isPrimePow_nat_iff n).mp hpp
  have hk2 : 2 ≤ k := by
    by_contra h
    have hk1 : k = 1 := by omega
    have heq' : p = n := by simpa [hk1] using heq
    have hnprime : Nat.Prime n := heq' ▸ hp
    exact hnp hnprime
  have hpow : p^k ≤ N := heq ▸ hn
  have hN : N ≠ 0 := by
    have hpos : 0 < p^k := Nat.pow_pos hp.pos
    omega
  have hpl : p ≤ Nat.sqrt N := Nat.le_sqrt'.mpr
    ((Nat.pow_le_pow_right hp.pos hk2).trans hpow)
  have hkl : k ≤ Nat.log 2 N := (Nat.le_log_iff_pow_le (by norm_num) hN).mpr
    ((Nat.pow_le_pow_left hp.two_le k).trans hpow)
  exact Finset.mem_image.mpr ⟨(p,k),
    Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr ⟨hp.two_le,hpl⟩,
      Finset.mem_Icc.mpr ⟨hk2,hkl⟩⟩,heq⟩

lemma mangoldt_upper (N n : ℕ) (hn : n ≤ N) : Λ n ≤ Real.log N := by
  by_cases hn0 : n = 0
  · subst n
    simp only [ArithmeticFunction.map_zero]
    exact Real.log_natCast_nonneg N
  · exact ArithmeticFunction.vonMangoldt_le_log.trans
      (Real.log_le_log (by exact_mod_cast Nat.pos_of_ne_zero hn0) (by exact_mod_cast hn))

/-- The mass contributed by pairs containing a proper prime power is small. -/
theorem contamination_bound (N : ℕ) :
    (∑ m ∈ Finset.range (N+1),
      if Nat.Prime m ∧ Nat.Prime (N-m) then (0:ℝ) else Λ m * Λ (N-m)) ≤
    2 * (Nat.sqrt N * Nat.log 2 N : ℕ) * (Real.log N)^2 := by
  classical
  let B := powerCover N
  let f : ℕ → ℝ := fun m => if Nat.Prime m ∧ Nat.Prime (N-m) then 0 else Λ m * Λ (N-m)
  let g : ℕ → ℝ := fun m => if m ∈ B then (Real.log N)^2 else 0
  have hg0 (m : ℕ) : 0 ≤ g m := by dsimp [g]; split_ifs <;> positivity
  have hpoint (m : ℕ) (hm : m ∈ Finset.range (N+1)) : f m ≤ g m + g (N-m) := by
    have hmN : m ≤ N := by have := Finset.mem_range.mp hm; omega
    by_cases hf : f m = 0
    · rw [hf]; exact add_nonneg (hg0 m) (hg0 (N-m))
    · have hm0 : Λ m ≠ 0 := by intro h; apply hf; simp [f,h]
      have hn0 : Λ (N-m) ≠ 0 := by intro h; apply hf; simp [f,h]
      have hmem : m ∈ B ∨ N-m ∈ B := by
        by_cases hp : Nat.Prime m
        · have hq : ¬ Nat.Prime (N-m) := by
            intro hq
            apply hf
            simp [f,hp,hq]
          exact Or.inr (nonprime_mem_cover N (N-m) (Nat.sub_le N m)
            (ArithmeticFunction.vonMangoldt_ne_zero_iff.mp hn0) hq)
        · exact Or.inl (nonprime_mem_cover N m hmN
            (ArithmeticFunction.vonMangoldt_ne_zero_iff.mp hm0) hp)
      have hfupper : f m ≤ (Real.log N)^2 := by
        dsimp [f]
        split_ifs
        · positivity
        simpa [pow_two] using mul_le_mul (mangoldt_upper N m hmN)
          (mangoldt_upper N (N-m) (Nat.sub_le N m))
          ArithmeticFunction.vonMangoldt_nonneg (Real.log_natCast_nonneg N)
      rcases hmem with h | h
      · have heq : g m = (Real.log N)^2 := if_pos h
        linarith [hg0 (N-m)]
      · have heq : g (N-m) = (Real.log N)^2 := if_pos h
        linarith [hg0 m]
  have hsum : (∑ m ∈ Finset.range (N+1), f m) ≤
      2 * ∑ m ∈ Finset.range (N+1), g m := by
    calc
      _ ≤ ∑ m ∈ Finset.range (N+1), (g m + g (N-m)) := Finset.sum_le_sum hpoint
      _ = _ := by rw [Finset.sum_add_distrib, ← Finset.sum_range_reflect g (N+1)]; simp; ring
  have hg : (∑ m ∈ Finset.range (N+1), g m) ≤ (B.card:ℝ) * (Real.log N)^2 := by
    calc
      _ = ∑ m ∈ (Finset.range (N+1)).filter (fun m => m ∈ B), (Real.log N)^2 := by
        simp only [g, Finset.sum_filter]
      _ ≤ ∑ _m ∈ B, (Real.log N)^2 := Finset.sum_le_sum_of_subset_of_nonneg
        (fun m hm => (Finset.mem_filter.mp hm).2) (fun _ _ _ => sq_nonneg _)
      _ = _ := by simp
  have hcard : (B.card:ℝ) ≤ (Nat.sqrt N * Nat.log 2 N : ℕ) := by
    exact_mod_cast cover_card N
  have hgfinal := hg.trans (mul_le_mul_of_nonneg_right hcard (sq_nonneg (Real.log N)))
  change (∑ m ∈ Finset.range (N+1), f m) ≤ _
  nlinarith [hsum,hgfinal]

#print axioms cover_card
#print axioms nonprime_mem_cover
/-- A strict convolution lower bound above contamination forces a prime pair. -/
theorem extraction (N : ℕ)
    (hlarge : 2 * (Nat.sqrt N * Nat.log 2 N : ℕ) * (Real.log N)^2 <
      ∑ m ∈ Finset.range (N+1), Λ m * Λ (N-m)) :
    ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ N = p+q := by
  classical
  by_contra hpair
  have hb := contamination_bound N
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

#print axioms contamination_bound
#print axioms extraction
end
end GoldbachPrimePowerExtraction


theorem solution (N : ℕ)
    (hlarge : 2 * (Nat.sqrt N * Nat.log 2 N : ℕ) * (Real.log N)^2 <
      ∑ m ∈ Finset.range (N+1), ArithmeticFunction.vonMangoldt m * ArithmeticFunction.vonMangoldt (N-m)) :
    ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ N = p+q :=
  GoldbachPrimePowerExtraction.extraction N hlarge

#print axioms solution
