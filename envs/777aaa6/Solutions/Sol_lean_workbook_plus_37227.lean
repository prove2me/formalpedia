-- Prove2me | solution 1 for lean_workbook_plus_37227
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:31:40.070817+00:00
-- url     : https://prove2.me/submissions/8299cdfb-3181-462e-bd57-65583b60b104

import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Real

theorem solution (ι : Type*) (a b : ι → ℝ) (h₁ : Nonempty ι)
    (h₂ : ∀ n, a n < b n) (h₃ : Summable a) (h₄ : Summable b) :
    ∑' n, a n < ∑' n, b n := by
  obtain ⟨i⟩ := h₁
  exact Summable.tsum_lt_tsum (fun n => (h₂ n).le) (h₂ i) h₃ h₄

#print axioms solution
