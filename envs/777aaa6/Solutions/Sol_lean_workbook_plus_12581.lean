-- Prove2me | solution 1 for lean_workbook_plus_12581
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:07:00.578454+00:00
-- url     : https://prove2.me/submissions/2981d693-f203-4878-8057-68c2e9900cdd

import Mathlib.Analysis.Complex.Basic

theorem solution (x : ℕ → ℝ) (f : ℝ → ℝ) (hf: Continuous f)
    (hx: ∃ a, ∀ ε, 0 < ε → ∃ N, ∀ n, N ≤ n → |x n - a| < ε) :
    ∃ a, ∀ ε, 0 < ε → ∃ N, ∀ n, N ≤ n → |f (x n) - a| < ε := by
  obtain ⟨a, ha⟩ := hx
  refine ⟨f a, fun ε hε => ?_⟩
  obtain ⟨δ, hδ, hfδ⟩ := Metric.continuousAt_iff.mp hf.continuousAt ε hε
  obtain ⟨N, hN⟩ := ha δ hδ
  refine ⟨N, fun n hn => ?_⟩
  exact hfδ (by simpa only [Real.dist_eq] using hN n hn)

#print axioms solution
