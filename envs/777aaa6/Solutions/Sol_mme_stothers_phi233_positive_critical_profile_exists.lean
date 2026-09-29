-- Prove2me | solution 1 for mme_stothers_phi233_positive_critical_profile_exists
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-02T22:45:49.709895+00:00
-- url     : https://prove2.me/submissions/d4bd02f8-73d4-487f-8f69-7fbee5a691cc

import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option warningAsError true

/-- Every pair of strict interior `phi_233` marginals has a positive profile
at which the one-dimensional critical product equation holds. -/
theorem solution
    (sigma mu : ℝ) (hsigma0 : 0 < sigma) (hmu0 : 0 < mu)
    (hsigma1 : sigma < 1) (hcompat : sigma / 2 + mu < 1) :
    ∃ a b c d : ℝ,
      0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < d ∧
      2 * a + b + c + d = 1 ∧
      2 * a + b = sigma ∧ a + c = mu ∧
      a ^ (2 : ℕ) * d = b ^ (2 : ℕ) * c := by
  let lo : ℝ := max 0 (sigma + mu - 1)
  let hi : ℝ := min (sigma / 2) mu
  let f : ℝ → ℝ := fun x ↦
    x ^ (2 : ℕ) * (1 - sigma - mu + x) -
      (sigma - 2 * x) ^ (2 : ℕ) * (mu - x)
  have hlohi : lo < hi := by
    dsimp only [lo, hi]
    apply lt_min
    · apply max_lt
      · linarith
      · linarith
    · apply max_lt
      · exact hmu0
      · linarith
  have hfContinuous : Continuous f := by
    dsimp only [f]
    fun_prop
  have hflo : f lo < 0 := by
    by_cases hbase : 0 ≤ sigma + mu - 1
    · have hb : 0 < sigma - 2 * (sigma + mu - 1) := by
        linarith
      have hc : 0 < mu - (sigma + mu - 1) := by
        linarith
      have hp : 0 < (sigma - 2 * (sigma + mu - 1)) ^ (2 : ℕ) *
          (mu - (sigma + mu - 1)) :=
        mul_pos (pow_pos hb 2) hc
      dsimp only [f, lo]
      rw [max_eq_right hbase]
      nlinarith
    · have hbase' : sigma + mu - 1 ≤ 0 := le_of_not_ge hbase
      have hp : 0 < sigma ^ (2 : ℕ) * mu :=
        mul_pos (pow_pos hsigma0 2) hmu0
      dsimp only [f, lo]
      rw [max_eq_left hbase']
      norm_num
      nlinarith
  have hfhi : 0 < f hi := by
    by_cases hhalf : sigma / 2 ≤ mu
    · have hd : 0 < 1 - sigma - mu + sigma / 2 := by
        linarith
      have hp : 0 < (sigma / 2) ^ (2 : ℕ) *
          (1 - sigma - mu + sigma / 2) :=
        mul_pos (pow_pos (div_pos hsigma0 (by norm_num)) 2) hd
      dsimp only [f, hi]
      rw [min_eq_left hhalf]
      nlinarith
    · have hhalf' : mu ≤ sigma / 2 := le_of_not_ge hhalf
      have hd : 0 < 1 - sigma - mu + mu := by linarith
      have hp : 0 < mu ^ (2 : ℕ) * (1 - sigma - mu + mu) :=
        mul_pos (pow_pos hmu0 2) hd
      dsimp only [f, hi]
      rw [min_eq_right hhalf']
      nlinarith
  have hzero : (0 : ℝ) ∈ Set.Icc (f lo) (f hi) :=
    ⟨le_of_lt hflo, le_of_lt hfhi⟩
  obtain ⟨x, hx, hfx⟩ :=
    (intermediate_value_Icc (le_of_lt hlohi) hfContinuous.continuousOn) hzero
  have hxlo : lo < x := by
    rcases hx.1.eq_or_lt with h | h
    · subst x
      linarith
    · exact h
  have hxhi : x < hi := by
    rcases hx.2.eq_or_lt with h | h
    · subst x
      linarith
    · exact h
  refine ⟨x, sigma - 2 * x, mu - x, 1 - sigma - mu + x,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hlo0 : 0 ≤ lo := by
      dsimp only [lo]
      exact le_max_left _ _
    linarith
  · have hh : hi ≤ sigma / 2 := by
      dsimp only [hi]
      exact min_le_left _ _
    linarith
  · have hh : hi ≤ mu := by
      dsimp only [hi]
      exact min_le_right _ _
    linarith
  · have hloBase : sigma + mu - 1 ≤ lo := by
      dsimp only [lo]
      exact le_max_right _ _
    linarith
  · ring
  · ring
  · ring
  · dsimp only [f] at hfx
    linarith
