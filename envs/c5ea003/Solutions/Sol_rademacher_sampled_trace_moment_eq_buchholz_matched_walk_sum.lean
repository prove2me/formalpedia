-- Prove2me | solution 1 for rademacher_sampled_trace_moment_eq_buchholz_matched_walk_sum
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-06-23T23:06:37.617224+00:00
-- url     : https://prove2.me/submissions/827c4937-ecba-4256-86a3-5431081a7a20

import Theorems.Thm_rademacher_sampled_trace_moment_eq_buchholz_signed_walk_sum
import Theorems.Thm_buchholz_signed_walk_sum_expectation_eq_matched_walk_sum

open MatrixCompletion
open scoped BigOperators

/-!
Source: Buchholz, "Operator Khintchine inequality in non-commutative
probability", Math. Ann. 319 (2001), Section 2, the closed-walk expansion and
sign-survival step; Candès--Recht, Section 6.1, Lemma 6.1, PDF p. 25.

Reduction: expand the trace moment into the raw signed closed-walk sum, then
evaluate the Rademacher sign expectation to keep exactly the matched walks.
-/
theorem solution
    (n : Nat) (hn : 1 ≤ n)
    {n1 n2 : Nat} (Omega : Finset (Fin n1 × Fin n2)) (p : ℝ) (hp : 0 < p)
    (X : RealMatrix n1 n2) :
    rademacherExpectation
        (fun eps =>
          Matrix.trace
            ((rademacherSampledMatrix Omega eps p X *
                (rademacherSampledMatrix Omega eps p X).transpose) ^ n))
      = buchholzMatchedWalkSum n Omega p X := by
  rw [rademacher_sampled_trace_moment_eq_buchholz_signed_walk_sum n hn Omega p hp X]
  exact buchholz_signed_walk_sum_expectation_eq_matched_walk_sum n hn Omega p hp X
