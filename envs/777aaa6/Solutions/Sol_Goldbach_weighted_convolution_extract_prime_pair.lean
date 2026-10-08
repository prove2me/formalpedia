-- Prove2me | solution 1 for Goldbach.weighted_convolution_extract_prime_pair
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-05T01:22:12.321827+00:00
-- url     : https://prove2.me/submissions/6de2a8a1-1d9e-4cd9-9ddb-8d7458c04814

import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.Data.Nat.Sqrt
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic

open scoped BigOperators ArithmeticFunction.vonMangoldt
set_option autoImplicit false

namespace GoldbachWeightedPrimePowerExtraction
noncomputable section

private def powerCover (N : ℕ) : Finset ℕ :=
  (Finset.Icc 2 (Nat.sqrt N)).biUnion fun p =>
    (Finset.Icc 2 (Nat.log p N)).image (fun k => p ^ k)

private lemma nonprime_mem_cover (N n : ℕ) (hn : n ≤ N)
    (hpp : IsPrimePow n) (hnp : ¬ Nat.Prime n) : n ∈ powerCover N := by
  obtain ⟨p,k,hp,hk,heq⟩ := (isPrimePow_nat_iff n).mp hpp
  have hk2 : 2 ≤ k := by
    by_contra h
    have hk1 : k = 1 := by omega
    have heq' : p = n := by simpa [hk1] using heq
    exact hnp (heq' ▸ hp)
  have hpow : p ^ k ≤ N := heq ▸ hn
  have hpl : p ≤ Nat.sqrt N := Nat.le_sqrt'.mpr
    ((Nat.pow_le_pow_right hp.pos hk2).trans hpow)
  have hkl : k ≤ Nat.log p N := Nat.le_log_of_pow_le hp.one_lt hpow
  exact Finset.mem_biUnion.mpr ⟨p, Finset.mem_Icc.mpr ⟨hp.two_le,hpl⟩,
    Finset.mem_image.mpr ⟨k, Finset.mem_Icc.mpr ⟨hk2,hkl⟩,heq⟩⟩

private lemma sum_biUnion_le (s : Finset ℕ) (t : ℕ → Finset ℕ)
    (f : ℕ → ℝ) (hf : ∀ n, 0 ≤ f n) :
    (∑ n ∈ s.biUnion t, f n) ≤ ∑ p ∈ s, ∑ n ∈ t p, f n := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    simp only [Finset.biUnion_insert, Finset.sum_insert ha]
    have hu : (∑ n ∈ (t a) ∪ s.biUnion t, f n) +
        (∑ n ∈ (t a) ∩ s.biUnion t, f n) =
        (∑ n ∈ t a, f n) + (∑ n ∈ s.biUnion t, f n) := Finset.sum_union_inter
    have hn : 0 ≤ ∑ n ∈ (t a) ∩ (s.biUnion t), f n :=
      Finset.sum_nonneg (fun n _ => hf n)
    linarith

private lemma cover_weight (N : ℕ) (hN : N ≠ 0) :
    (∑ n ∈ powerCover N, Λ n) ≤ (Nat.sqrt N : ℝ) * Real.log N := by
  classical
  have hbase (p : ℕ) (hp : p ∈ Finset.Icc 2 (Nat.sqrt N)) :
      (∑ n ∈ (Finset.Icc 2 (Nat.log p N)).image (fun k => p ^ k), Λ n) ≤ Real.log N := by
    have hp2 : 2 ≤ p := (Finset.mem_Icc.mp hp).1
    have hp0 : (0 : ℝ) < p := by exact_mod_cast (show 0 < p by omega)
    have hcard : ((Finset.Icc 2 (Nat.log p N)).card : ℝ) ≤ Nat.log p N := by
      exact_mod_cast (show (Finset.Icc 2 (Nat.log p N)).card ≤ Nat.log p N by
        simp only [Nat.card_Icc]; omega)
    have hlog : (Nat.log p N : ℝ) * Real.log p ≤ Real.log N := by
      have hpow : (p : ℝ) ^ Nat.log p N ≤ N := by
        exact_mod_cast Nat.pow_log_le_self p hN
      have h := Real.log_le_log (by positivity : 0 < (p : ℝ) ^ Nat.log p N) hpow
      rwa [Real.log_pow] at h
    calc
      _ ≤ ∑ k ∈ Finset.Icc 2 (Nat.log p N), Λ (p ^ k) :=
        Finset.sum_image_le_of_nonneg (fun _ _ => ArithmeticFunction.vonMangoldt_nonneg)
      _ = ∑ _k ∈ Finset.Icc 2 (Nat.log p N), Λ p := by
        apply Finset.sum_congr rfl
        intro k hk
        exact ArithmeticFunction.vonMangoldt_apply_pow (by have := (Finset.mem_Icc.mp hk).1; omega)
      _ = ((Finset.Icc 2 (Nat.log p N)).card : ℝ) * Λ p := by simp
      _ ≤ ((Finset.Icc 2 (Nat.log p N)).card : ℝ) * Real.log p :=
        mul_le_mul_of_nonneg_left ArithmeticFunction.vonMangoldt_le_log (by positivity)
      _ ≤ (Nat.log p N : ℝ) * Real.log p :=
        mul_le_mul_of_nonneg_right hcard (Real.log_natCast_nonneg p)
      _ ≤ Real.log N := hlog
  have hcard : ((Finset.Icc 2 (Nat.sqrt N)).card : ℝ) ≤ Nat.sqrt N := by
    exact_mod_cast (show (Finset.Icc 2 (Nat.sqrt N)).card ≤ Nat.sqrt N by
      simp only [Nat.card_Icc]; omega)
  calc
    _ ≤ ∑ p ∈ Finset.Icc 2 (Nat.sqrt N),
        ∑ n ∈ (Finset.Icc 2 (Nat.log p N)).image (fun k => p ^ k), Λ n :=
      sum_biUnion_le _ _ _ (fun _ => ArithmeticFunction.vonMangoldt_nonneg)
    _ ≤ ∑ _p ∈ Finset.Icc 2 (Nat.sqrt N), Real.log N := Finset.sum_le_sum hbase
    _ = ((Finset.Icc 2 (Nat.sqrt N)).card : ℝ) * Real.log N := by simp
    _ ≤ (Nat.sqrt N : ℝ) * Real.log N :=
      mul_le_mul_of_nonneg_right hcard (Real.log_natCast_nonneg N)

private lemma mangoldt_upper (N n : ℕ) (hn : n ≤ N) : Λ n ≤ Real.log N := by
  by_cases hn0 : n = 0
  · subst n
    simp only [ArithmeticFunction.map_zero]
    exact Real.log_natCast_nonneg N
  · exact ArithmeticFunction.vonMangoldt_le_log.trans
      (Real.log_le_log (by exact_mod_cast Nat.pos_of_ne_zero hn0) (by exact_mod_cast hn))

private theorem contamination_bound (N : ℕ) :
    (∑ m ∈ Finset.range (N+1),
      if Nat.Prime m ∧ Nat.Prime (N-m) then (0:ℝ) else Λ m * Λ (N-m)) ≤
    2 * (Nat.sqrt N : ℝ) * (Real.log N)^2 := by
  classical
  by_cases hN : N = 0
  · subst N
    simp
  let B := powerCover N
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
      · exact Or.inr (nonprime_mem_cover N (N-m) (Nat.sub_le N m)
          (ArithmeticFunction.vonMangoldt_ne_zero_iff.mp hn0) (fun hq => hpq ⟨hp,hq⟩))
      · exact Or.inl (nonprime_mem_cover N m hmN
          (ArithmeticFunction.vonMangoldt_ne_zero_iff.mp hm0) hp)
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
  have hgfinal : (∑ m ∈ Finset.range (N+1), g m) ≤ (Nat.sqrt N : ℝ) * (Real.log N)^2 := by
    calc
      _ ≤ (∑ m ∈ B, Λ m) * Real.log N := hg
      _ ≤ ((Nat.sqrt N : ℝ) * Real.log N) * Real.log N :=
        mul_le_mul_of_nonneg_right (cover_weight N hN) (Real.log_natCast_nonneg N)
      _ = _ := by ring
  change (∑ m ∈ Finset.range (N+1), f m) ≤ _
  nlinarith [hsum,hgfinal]

end
end GoldbachWeightedPrimePowerExtraction

theorem solution (N : ℕ)
    (hlarge : 2 * (Nat.sqrt N : ℝ) * (Real.log N)^2 <
      ∑ m ∈ Finset.range (N+1),
        ArithmeticFunction.vonMangoldt m * ArithmeticFunction.vonMangoldt (N-m)) :
    ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ N = p+q := by
  classical
  by_contra hpair
  have hb := GoldbachWeightedPrimePowerExtraction.contamination_bound N
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
