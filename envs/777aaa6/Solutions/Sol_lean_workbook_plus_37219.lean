-- Prove2me | solution 1 for lean_workbook_plus_37219
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:53:05.021922+00:00
-- url     : https://prove2.me/submissions/57c7e2e1-48c5-496e-9b84-e00c2c0e5a3a

import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.UniformSpace.Cauchy
import Mathlib.Tactic

private theorem rapid_subsequence (x : ℕ → ℝ) (hx : CauchySeq x) :
    ∃ n : ℕ → ℕ, StrictMono n ∧
      ∀ k : ℕ, |x (n (k + 1)) - x (n k)| < 1 / 2 ^ k := by
  obtain ⟨n, hn, hdist⟩ := hx.subseq_mem
    (V := fun k => {p : ℝ × ℝ | dist p.1 p.2 < 1 / 2 ^ k})
    (fun k => Metric.dist_mem_uniformity (by positivity))
  refine ⟨n, hn, fun k => ?_⟩
  simpa only [Set.mem_setOf_eq, Real.dist_eq] using hdist k

theorem solution (x : ℕ → ℝ) (hx : CauchySeq x) :
    ∃ n : ℕ → ℕ, ∀ k : ℕ, k > 0 → |x (n (k + 1)) - x (n k)| < 1 / 2 ^ k := by
  obtain ⟨n, _, hn⟩ := rapid_subsequence x hx
  exact ⟨n, fun k _ => hn k⟩

#print axioms solution
