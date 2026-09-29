-- Prove2me | solution 1 for BanditAlgorithm.adversarial_bandit_exp3ix_master_high_probability_regret
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-07-21T02:16:10.716683+00:00
-- url     : https://prove2.me/submissions/93416c75-a8a6-449e-ac25-ef1ef78004bc

import Theorems.Thm_BanditAlgorithm_exp3ix_pathwise_regret_decomposition
import Theorems.Thm_BanditAlgorithm_exp3ix_estimate_concentration_variance
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open MeasureTheory ProbabilityTheory

theorem solution
    {k : ℕ} (hk : 1 < k) (n : ℕ) (hn : 0 < n)
    (x : ℕ → Fin k → ℝ) (hx : ∀ t : ℕ, ∀ i : Fin k, x t i ∈ Set.Icc (0 : ℝ) 1)
    (δ : ℝ) (hδ : δ ∈ Set.Ioo (0 : ℝ) 1)
    (η : ℝ) (hη : 0 < η)
    (π : BanditAlgorithm.BanditPolicy k)
    (hπ : BanditAlgorithm.IsExp3IXPolicy η (η / 2) π) :
    BanditAlgorithm.adversarialMeasure x π n
      {h : BanditAlgorithm.BanditHistory k n |
        Real.log k / η + η * (n * k) +
            (1 + 1 / η) * Real.log ((k + 1) / δ) ≤
          BanditAlgorithm.adversarialRandomRegret n x h} ≤
      ENNReal.ofReal δ := by
  let c : ℝ := Real.log ((k + 1) / δ) / η
  let D : BanditAlgorithm.BanditHistory k n → ℝ := fun h ↦
    ⨆ i : Fin k,
      BanditAlgorithm.exp3IXEstimate η (η / 2) n h i -
        ∑ t : Fin n, (1 - x t i)
  let S : BanditAlgorithm.BanditHistory k n → ℝ := fun h ↦
    ∑ i : Fin k,
      (BanditAlgorithm.exp3IXEstimate η (η / 2) n h i -
        ∑ t : Fin n, (1 - x t i))
  apply le_trans (measure_mono ?_)
    (BanditAlgorithm.exp3ix_estimate_concentration_variance
      hk n hn x hx δ hδ η hη π hπ)
  intro h hh
  simp only [Set.mem_setOf_eq] at hh ⊢
  by_contra hnot
  have hrange : ∀ t : Fin n, (h t).2 ∈ Set.Icc (0 : ℝ) 1 := by
    intro t
    by_contra ht
    exact hnot (Or.inl ⟨t, ht⟩)
  have hD : D h < c := by
    exact lt_of_not_ge (fun hdc ↦ hnot (Or.inr (Or.inl hdc)))
  have hS : S h < c := by
    exact lt_of_not_ge (fun hsc ↦ hnot (Or.inr (Or.inr hsc)))
  have hpath := BanditAlgorithm.exp3ix_pathwise_regret_decomposition
    hk n x hx η hη h hrange
  change BanditAlgorithm.adversarialRandomRegret n x h ≤
      Real.log k / η + D h +
        η * ∑ i : Fin k,
          BanditAlgorithm.exp3IXEstimate η (η / 2) n h i at hpath
  have htrue (i : Fin k) :
      (∑ t : Fin n, (1 - x t i)) ≤ n := by
    calc
      (∑ t : Fin n, (1 - x t i)) ≤ ∑ _t : Fin n, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro t ht
        linarith [(hx t i).1]
      _ = n := by simp
  have htrue_sum :
      (∑ i : Fin k, ∑ t : Fin n, (1 - x t i)) ≤ n * k := by
    calc
      (∑ i : Fin k, ∑ t : Fin n, (1 - x t i)) ≤
          ∑ _i : Fin k, (n : ℝ) := by
        apply Finset.sum_le_sum
        intro i hi
        exact htrue i
      _ = n * k := by simp [mul_comm]
  have hestimate_sum :
      (∑ i : Fin k, BanditAlgorithm.exp3IXEstimate η (η / 2) n h i) <
        c + n * k := by
    calc
      (∑ i : Fin k, BanditAlgorithm.exp3IXEstimate η (η / 2) n h i) =
          S h + ∑ i : Fin k, ∑ t : Fin n, (1 - x t i) := by
        dsimp [S]
        rw [Finset.sum_sub_distrib]
        ring
      _ < c + n * k := add_lt_add_of_lt_of_le hS htrue_sum
  have hηestimate :
      η * (∑ i : Fin k, BanditAlgorithm.exp3IXEstimate η (η / 2) n h i) <
        η * (c + n * k) :=
    mul_lt_mul_of_pos_left hestimate_sum hη
  have hηc : η * c = Real.log ((k + 1) / δ) := by
    dsimp [c]
    field_simp [ne_of_gt hη]
  have hupper :
      BanditAlgorithm.adversarialRandomRegret n x h <
        Real.log k / η + c + η * (c + n * k) := by
    calc
      _ ≤ Real.log k / η + D h +
          η * ∑ i : Fin k,
            BanditAlgorithm.exp3IXEstimate η (η / 2) n h i := hpath
      _ < Real.log k / η + c + η * (c + n * k) := by
        linarith
  have hthreshold :
      Real.log k / η + c + η * (c + n * k) =
        Real.log k / η + η * (n * k) +
          (1 + 1 / η) * Real.log ((k + 1) / δ) := by
    rw [mul_add, hηc]
    dsimp [c]
    ring
  rw [hthreshold] at hupper
  linarith
