-- Prove2me | solution 1 for Bridges.AttentionKneeEntropyBound.uniform_l2_bound
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-19T20:09:52.466974+00:00
-- url     : https://prove2.me/submissions/d56bbb8b-76d1-425e-9a12-83d4e6aeb2e6

import Mathlib
import Definitions.Def_Bridges_AttentionKneeEntropyBound
import Definitions.Def_Bridges_AttentionKneeGeometry
open Finset Bridges.AttentionKneeGeometry Bridges.AttentionKneeEntropyBound in
theorem solution {n : ℕ} {g : ℝ} (hn : 0 < n) (hg : 0 ≤ g)
    (hex : ∃ k, g ≤ mass (stepProfile n (1 / n)) k) :
    g ^ 2 * n ≤ (knee (stepProfile n (1 / n)) g : ℝ) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  -- the plateau profile has energy at most `1/n` on every prefix
  have hEbound : ∀ k, energy (stepProfile n (1 / n)) k ≤ 1 / n := by
    intro k
    unfold energy stepProfile
    have e : ∑ i ∈ range k, (if i < n then (1 / (n : ℝ)) else 0) ^ 2
        = ∑ i ∈ (range k).filter (fun i => i < n), (1 / (n : ℝ)) ^ 2 := by
      rw [sum_filter]
      refine sum_congr rfl (fun i _ => ?_)
      split_ifs <;> simp
    rw [e, sum_const, nsmul_eq_mul]
    have hc : (((range k).filter (fun i => i < n)).card : ℝ) ≤ n := by
      have : (range k).filter (fun i => i < n) ⊆ range n := by
        intro i hi
        simp only [mem_filter, mem_range] at hi ⊢
        exact hi.2
      exact_mod_cast (card_le_card this).trans (card_range n).le
    calc (((range k).filter (fun i => i < n)).card : ℝ) * (1 / (n : ℝ)) ^ 2
        ≤ n * (1 / (n : ℝ)) ^ 2 := mul_le_mul_of_nonneg_right hc (sq_nonneg _)
      _ = 1 / n := by field_simp
  -- Cauchy–Schwarz at the knee
  have hK : g ≤ mass (stepProfile n (1 / n)) (knee (stepProfile n (1 / n)) g) := Nat.sInf_mem hex
  have hcs : mass (stepProfile n (1 / n)) (knee (stepProfile n (1 / n)) g) ^ 2
      ≤ (knee (stepProfile n (1 / n)) g : ℝ)
        * energy (stepProfile n (1 / n)) (knee (stepProfile n (1 / n)) g) := by
    have := sq_sum_le_card_mul_sum_sq (s := range (knee (stepProfile n (1 / n)) g))
      (f := stepProfile n (1 / n))
    rw [card_range] at this
    exact this
  have hsq : g ^ 2 ≤ mass (stepProfile n (1 / n)) (knee (stepProfile n (1 / n)) g) ^ 2 :=
    pow_le_pow_left₀ hg hK 2
  have hen : (knee (stepProfile n (1 / n)) g : ℝ)
        * energy (stepProfile n (1 / n)) (knee (stepProfile n (1 / n)) g)
      ≤ (knee (stepProfile n (1 / n)) g : ℝ) * (1 / n) :=
    mul_le_mul_of_nonneg_left (hEbound _) (Nat.cast_nonneg _)
  have h1 : g ^ 2 ≤ (knee (stepProfile n (1 / n)) g : ℝ) * (1 / n) := by linarith
  rw [mul_one_div, le_div_iff₀ hn'] at h1
  exact h1
