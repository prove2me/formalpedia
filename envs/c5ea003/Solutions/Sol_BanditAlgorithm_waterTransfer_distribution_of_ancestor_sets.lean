-- Prove2me | solution 1 for BanditAlgorithm.waterTransfer_distribution_of_ancestor_sets
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-08-13T17:45:41.104643+00:00
-- url     : https://prove2.me/submissions/8adc43f8-07ef-4f19-b547-96075731e640

import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Algebra.Order.BigOperators.Group.Finset

open scoped BigOperators

namespace BanditAlgorithm

noncomputable section

theorem _root_.solution {k : ℕ} (hk : 0 < k) (q : Fin k → ℝ)
    (hq : q ∈ stdSimplex ℝ (Fin k))
    (anc : Fin k → Finset (Fin k))
    (hself : ∀ b, b ∈ anc b)
    (R : Fin k → Fin k → Prop)
    (hclosure : ∀ a b, R a b → ∀ c, b ∈ anc c → a ∈ anc c) :
    ∃ r : Fin k → ℝ,
      r ∈ stdSimplex ℝ (Fin k) ∧
      (∀ a, q a / k ≤ r a) ∧
      (∀ a b, R a b → r b ≤ r a) ∧
      ∀ y : Fin k → ℝ,
        (∀ a b, a ∈ anc b → y b ≤ y a) →
          ∑ b : Fin k, q b * y b ≤ ∑ a : Fin k, r a * y a := by
  classical
  let r : Fin k → ℝ := fun a =>
    ∑ b : Fin k, if a ∈ anc b then q b / (anc b).card else 0
  have hcard (b : Fin k) : 0 < (anc b).card := Finset.card_pos.mpr ⟨b, hself b⟩
  have hcardle (b : Fin k) : (anc b).card ≤ k := by
    simpa using Finset.card_le_card (Finset.subset_univ (anc b))
  have hrnonneg (a : Fin k) : 0 ≤ r a := by
    dsimp [r]
    apply Finset.sum_nonneg
    intro b hb
    split
    · exact div_nonneg (hq.1 b) (by positivity)
    · exact le_rfl
  have hrsum : ∑ a : Fin k, r a = 1 := by
    dsimp [r]
    rw [Finset.sum_comm]
    calc
      (∑ b : Fin k, ∑ a : Fin k, if a ∈ anc b then q b / (anc b).card else 0) =
          ∑ b : Fin k, q b := by
        apply Finset.sum_congr rfl
        intro b hb
        rw [Finset.sum_ite]
        simp only [Finset.filter_univ_mem, Finset.sum_const_zero, add_zero,
          Finset.sum_const, nsmul_eq_mul]
        have hc : ((anc b).card : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (hcard b))
        field_simp [hc]
      _ = 1 := hq.2
  refine ⟨r, ⟨hrnonneg, hrsum⟩, ?_, ?_, ?_⟩
  · intro a
    have hone : q a / (anc a).card ≤ r a := by
      dsimp [r]
      have ht := Finset.single_le_sum
        (s := Finset.univ)
        (f := fun b : Fin k => if a ∈ anc b then q b / (anc b).card else 0)
        (fun b hb => by
          dsimp
          by_cases hba : a ∈ anc b
          · rw [if_pos hba]
            exact div_nonneg (hq.1 b) (by exact_mod_cast (Nat.zero_le (anc b).card))
          · rw [if_neg hba])
        (Finset.mem_univ a)
      simpa [hself a] using ht
    have hqnonneg := hq.1 a
    have hden : (0 : ℝ) < (anc a).card := by exact_mod_cast hcard a
    have hkR : (0 : ℝ) < k := by exact_mod_cast hk
    have hdiv : q a / k ≤ q a / (anc a).card := by
      exact div_le_div_of_nonneg_left hqnonneg hden (by exact_mod_cast hcardle a)
    exact hdiv.trans hone
  · intro a b hab
    dsimp [r]
    apply Finset.sum_le_sum
    intro c hc
    by_cases hb : b ∈ anc c
    · have ha := hclosure a b hab c hb
      simp [hb, ha]
    · rw [if_neg hb]
      by_cases ha : a ∈ anc c
      · rw [if_pos ha]
        exact div_nonneg (hq.1 c) (by exact_mod_cast (Nat.zero_le (anc c).card))
      · rw [if_neg ha]
  · intro y hy
    calc
      (∑ b : Fin k, q b * y b) =
          ∑ b : Fin k, ∑ a ∈ anc b, (q b / (anc b).card) * y b := by
        apply Finset.sum_congr rfl
        intro b hb
        rw [Finset.sum_const]
        simp only [nsmul_eq_mul]
        have hc : ((anc b).card : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (hcard b))
        field_simp [hc]
      _ ≤ ∑ b : Fin k, ∑ a ∈ anc b, (q b / (anc b).card) * y a := by
        apply Finset.sum_le_sum
        intro b hb
        apply Finset.sum_le_sum
        intro a ha
        exact mul_le_mul_of_nonneg_left (hy a b ha)
          (div_nonneg (hq.1 b) (by positivity))
      _ = ∑ a : Fin k, r a * y a := by
        dsimp [r]
        have hreindex :
            (∑ b : Fin k, ∑ a ∈ anc b, (q b / (anc b).card) * y a) =
              ∑ b : Fin k, ∑ a : Fin k,
                if a ∈ anc b then (q b / (anc b).card) * y a else 0 := by
          apply Finset.sum_congr rfl
          intro b hb
          rw [Finset.sum_ite]
          simp
        rw [hreindex, Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro a ha
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro b hb
        by_cases hab : a ∈ anc b <;> simp [hab]

end
end BanditAlgorithm
