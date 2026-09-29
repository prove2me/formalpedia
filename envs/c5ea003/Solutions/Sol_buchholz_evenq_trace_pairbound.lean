-- Prove2me | solution 1 for buchholz_evenq_trace_pairbound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-06-23T22:59:00.690306+00:00
-- url     : https://prove2.me/submissions/bb7bbcad-da99-4364-92e2-fc0b0a7e73a7

import Theorems.Thm_rademacher_sampled_trace_moment_eq_buchholz_matched_walk_sum
import Theorems.Thm_buchholz_matched_walk_sum_le_pair_count_gram_schatten

open MatrixCompletion
open scoped BigOperators

/-!
Source: Buchholz, "Operator Khintchine inequality in non-commutative
probability", Math. Ann. 319 (2001), Sections 2--3, the even-moment
closed-walk expansion and pair-partition estimate; Candès--Recht, Section 6.1,
Lemma 6.1, PDF p. 25.

Reduction: first use the trace-power expansion plus Rademacher sign
orthogonality to identify the averaged trace moment with the matched-walk sum.
Then apply Buchholz's matched-walk pair-count estimate for the sampled
coordinate series.
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
      ≤ ((Nat.factorial (2 * n) : ℝ) / ((2 ^ n : ℝ) * (Nat.factorial n : ℝ))) *
          max ((sampledRowGramSchatten Omega p X (2 * n : ℝ)) ^ (2 * n))
              ((sampledColumnGramSchatten Omega p X (2 * n : ℝ)) ^ (2 * n)) := by
  rw [rademacher_sampled_trace_moment_eq_buchholz_matched_walk_sum n hn Omega p hp X]
  exact buchholz_matched_walk_sum_le_pair_count_gram_schatten n hn Omega p hp X
