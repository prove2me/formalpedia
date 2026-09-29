-- Prove2me | solution 1 for erdos243_cubic_rate_every_tail_irrational
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-25T01:57:02.85904+00:00
-- url     : https://prove2.me/submissions/86feee69-f78d-403a-b99f-558dc1d96986

import Theorems.Thm_ErdosProblems_Erdos243_PaperCompleteR21_cubic_rate_irrationality_unconditional

open Filter

noncomputable section

theorem solution
    (a : ℕ → ℕ) (ha : StrictMono a) (hpos : ∀ n, 0 < a n)
    (hrate : Filter.Tendsto (fun n : ℕ => (n : ℝ) ^ 3 *
      ((a n : ℝ) ^ 2 / (a (n + 1) : ℝ) - (1 + 3 / (n : ℝ))))
      Filter.atTop (nhds 0))
    (Sv : ℝ) (hS : HasSum (fun n : ℕ => 1 / (a n : ℝ)) Sv)
    (N : ℕ) :
    Irrational (∑' n : ℕ, 1 / (a (n + N) : ℝ)) := by
  have hIrr : Irrational Sv :=
    ErdosProblems.Erdos243.PaperCompleteR21.cubic_rate_irrationality_unconditional
      a ha hpos hrate Sv hS
  let q : ℚ := ∑ n ∈ Finset.range N, (1 : ℚ) / (a n : ℚ)
  have hprefix :
      (∑ n ∈ Finset.range N, (1 : ℝ) / (a n : ℝ)) = (q : ℝ) := by
    simp [q]
  have hTail :
      HasSum (fun n : ℕ => 1 / (a (n + N) : ℝ)) (Sv - (q : ℝ)) := by
    simpa only [hprefix] using
      ((hasSum_nat_add_iff' (f := fun n : ℕ => 1 / (a n : ℝ)) N).2 hS)
  rw [hTail.tsum_eq]
  exact hIrr.sub_ratCast q
