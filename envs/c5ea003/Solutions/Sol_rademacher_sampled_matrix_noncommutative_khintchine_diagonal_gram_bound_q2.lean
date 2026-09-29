-- Prove2me | solution 1 for rademacher_sampled_matrix_noncommutative_khintchine_diagonal_gram_bound_q2
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-06-23T22:14:34.693924+00:00
-- url     : https://prove2.me/submissions/561f3ec0-71a2-4b6a-8f39-3edc7aac9d25

import Theorems.Thm_rademacher_sampled_matrix_even_schatten_moment_trace_pairbound
import Theorems.Thm_rademacher_sampled_matrix_noncommutative_khintchine_q2_from_even_trace_pairbound

open MatrixCompletion
open scoped BigOperators

/-- Source: Candes-Recht 2008, PDF p. 24, Section 6.1, Lemma 6.1, citing the
noncommutative Khintchine inequality of Lust-Picquard sharpened by Buchholz.
The reduction isolates the genuinely noncommutative even-moment trace estimate
from the formal passage to arbitrary integer Schatten exponent `q ≥ 2`.

The imported even-moment theorem supplies the Buchholz trace-pairing estimate at
exponent `2n`.  The bridge theorem performs the remaining interpolation and
constant absorption: choose the next even exponent above `q`, use the
operator/Schatten sandwich and the `q ≥ β log n` window to compare the `q` and
even moments, apply Jensen to the Rademacher expectation, and transfer the
sampled row/column Gram scale back from the even exponent to `q`. -/
theorem solution :
    ∃ C : ℝ, 0 < C ∧
      ∀ (β : ℝ), 2 < β →
      ∀ (n₁ n₂ m q : ℕ)
        (Omega : Finset (Fin n₁ × Fin n₂))
        (X : Matrix (Fin n₁) (Fin n₂) ℝ),
        2 ≤ q →
        (q : ℝ) ≥ β * Real.log (↑(max n₁ n₂)) →
        rademacherExpectation
            (fun eps =>
              schattenNorm (q : ℝ)
                (rademacherSampledMatrix Omega eps
                  ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) X) ^ q) ≤
          (C * Real.sqrt (q : ℝ) *
            max (sampledRowGramSchatten Omega
                  ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) X (q : ℝ))
                (sampledColumnGramSchatten Omega
                  ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) X (q : ℝ))) ^ q := by
  exact
    rademacher_sampled_matrix_noncommutative_khintchine_q2_from_even_trace_pairbound
      (fun n hn {n1 n2} Omega p hp X =>
        rademacher_sampled_matrix_even_schatten_moment_trace_pairbound
          n hn (n1 := n1) (n2 := n2) Omega p hp X)
