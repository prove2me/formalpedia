-- Prove2me | solution 1 for Martingale.clt_truncation_matches_of_lt
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:10:01.208977+00:00
-- url     : https://prove2.me/submissions/53d06408-e89e-4cc1-84c5-95fff8ebb628

import Mathlib.Probability.Martingale.Basic
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology ProbabilityTheory

theorem solution {Ω : Type*} {m0 : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P] (D : ℕ → ℕ → Ω → ℝ)
    (hmeas : ∀ n k, Measurable (D n k))
    (σ : ℝ) (hσ2 : σ ^ 2 < 2)
    (hvar : TendstoInMeasure P
      (fun (n : ℕ) ω => ∑ k ∈ Finset.range n, D n k ω ^ 2) atTop (fun _ => σ ^ 2)) :
    TendstoInMeasure P
      (fun (n : ℕ) ω => (∑ k ∈ Finset.range n, D n k ω)
        - ∑ k ∈ Finset.range n, (Set.indicator
            {ω' | ∑ j ∈ Finset.range k, D n j ω' ^ 2 ≤ 2} (D n k) ω))
      atTop (fun _ => 0) := by
  classical
  rw [tendstoInMeasure_iff_norm] at hvar ⊢
  intro ε hε
  have hlim := hvar (2 - σ ^ 2) (sub_pos.mpr hσ2)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
    (fun _ => bot_le) ?_
  intro n
  apply measure_mono
  intro ω hω
  by_cases htotal : (∑ k ∈ Finset.range n, D n k ω ^ 2) ≤ 2
  · have hsame : (∑ k ∈ Finset.range n, D n k ω) =
        ∑ k ∈ Finset.range n, (Set.indicator
          {ω' | ∑ j ∈ Finset.range k, D n j ω' ^ 2 ≤ 2} (D n k) ω) := by
      apply Finset.sum_congr rfl
      intro k hk
      symm
      apply Set.indicator_of_mem
      change (∑ j ∈ Finset.range k, D n j ω ^ 2) ≤ 2
      refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_) htotal
      · exact Finset.range_mono (Nat.le_of_lt (Finset.mem_range.mp hk))
      · intro j _ _
        exact sq_nonneg _
    simp only [Set.mem_setOf_eq, hsame, sub_self, norm_zero] at hω
    exact False.elim ((not_le_of_gt hε) hω)
  · change 2 - σ ^ 2 ≤ ‖(∑ k ∈ Finset.range n, D n k ω ^ 2) - σ ^ 2‖
    rw [Real.norm_eq_abs]
    exact (sub_le_sub_right (le_of_lt (lt_of_not_ge htotal)) _).trans (le_abs_self _)

#print axioms solution
