-- Prove2me | Theorems.Thm_rademacher_sampled_matrix_schatten_moment_khintchine_low_q_unit_dimension_bound
-- name    : rademacher_sampled_matrix_schatten_moment_khintchine_low_q_unit_dimension_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-06-23T20:55:46.580527+00:00
-- url     : https://prove2.me/theorems/d2f8ecca-dc8b-462a-9509-d6cb85c31d8a
-- statement:
--   **Unit-dimensional residue of the low-$q$ Khintchine boundary.**
--
--   Assume the formal low-$q$ hypotheses
--   $$
--   1\le q,\qquad \neg(2\le q),\qquad q\ge\beta\log(\max\{n_1,n_2\}),\qquad \beta>2,
--   $$
--   and also assume the arithmetic consequence
--   $$
--   \max\{n_1,n_2\}\le1.
--   $$
--   Then there is a universal constant $C_{\rm low}>0$ such that every $C'\ge C_{\rm low}$ controls the Rademacher Schatten moment by the conditional variance scale:
--   $$
--   \mathbb E_\varepsilon\,\|S_\varepsilon(\Omega,p,X)\|_{S_q}^q
--   \le
--   \left(C'\sqrt q\,V(\Omega,p,X)\right)^q,
--   $$
--   where $p=m/(n_1n_2)$ and $V$ is `rademacherSampledVarianceScale`.
--
--   Conceptually, this is only the at-most-one-entry matrix case left after the source theorem's $q\ge2$ range has been separated. It contains no noncommutative Khintchine estimate.
--
--   Source: Candes--Recht, Section 6.1, Lemma 6.1, PDF p. 24; this node is the finite-dimensional formal residue outside the source $q\ge2$ analytic range.
-- source:
--   Candes, Emmanuel, and Benjamin Recht. "Exact matrix completion via convex optimization." Communications of the ACM 55.6 (2012): 111-119.

import Definitions.Def_matrix_completion_gram_schatten
open MatrixCompletion

theorem rademacher_sampled_matrix_schatten_moment_khintchine_low_q_unit_dimension_bound :
    ∃ Ckh : ℝ, 0 < Ckh ∧
      ∀ C' : ℝ, Ckh ≤ C' →
      ∀ (β : ℝ), 2 < β →
      ∀ (n₁ n₂ m q : ℕ)
        (Omega : Finset (Fin n₁ × Fin n₂))
        (X : Matrix (Fin n₁) (Fin n₂) ℝ),
        1 ≤ q →
        ¬ 2 ≤ q →
        max n₁ n₂ ≤ 1 →
        (q : ℝ) ≥ β * Real.log (↑(max n₁ n₂)) →
        rademacherExpectation
            (fun eps =>
              schattenNorm (q : ℝ)
                (rademacherSampledMatrix Omega eps
                  ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) X) ^ q) ≤
          (C' * Real.sqrt (q : ℝ) *
            rademacherSampledVarianceScale Omega
              ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) X) ^ q := by
  sorry
