-- Prove2me | Theorems.Thm_rademacher_sampled_matrix_noncommutative_khintchine_q2_from_even_trace_pairbound
-- name    : rademacher_sampled_matrix_noncommutative_khintchine_q2_from_even_trace_pairbound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-06-23T22:11:14.745732+00:00
-- url     : https://prove2.me/theorems/2b31bb0b-a1c4-4fca-99ec-a5ac1aadf63b
-- statement:
--   **Formal bridge from even Buchholz moments to the $qge2$ Khintchine core.**
--
--   Let $S_arepsilon(Omega,p,X)$ be the Rademacher-signed sampled matrix used in the Candes--Recht symmetrization argument, and let
--   $$
--   R_q=operatorname{sampledRowGramSchatten}(Omega,p,X,q),qquad C_q=operatorname{sampledColumnGramSchatten}(Omega,p,X,q).
--   $$
--   This theorem says that if one has the even-integer Buchholz trace-moment estimate
--   $$
--   mathbb E_arepsilon|S_arepsilon|_{S_{2n}}^{2n}le { (2n)!over 2^n n!}max{R_{2n}^{2n},C_{2n}^{2n}}
--   $$
--   for every $nge1$, then there is a universal constant $C>0$ such that every integer $qge2$ in the Candes--Recht window $qgeetalogmax(n_1,n_2)$ satisfies
--   $$
--   mathbb E_arepsilon|S_arepsilon|_{S_q}^{q}leleft(Csqrt qmax{R_q,C_q}ight)^q.
--   $$
--
--   The bridge contains no new noncommutative combinatorics.  The intended proof chooses the next even exponent $2nge q$, compares $S_q$ and $S_{2n}$ using the Schatten/operator-norm sandwich and the rank window $operatorname{rank}^{1/q}le e$, applies Jensen/power-mean to pass from the $q$-th moment to the $2n$-th moment, uses Buchholz's double-factorial constant bound $((2n)!/(2^n n!))^{1/(2n)}lesssimsqrt{2n}$, and transfers the sampled row/column Gram scales back from $2n$ to $q$ by Schatten antitonicity.
--
--   Source: Candes--Recht, Section 6.1, Lemma 6.1, PDF p. 24, where the proof invokes the Lust-Picquard/Buchholz noncommutative Khintchine inequality; Buchholz, *Operator Khintchine inequality in non-commutative probability*, Math. Ann. 319 (2001), Sections 2--3, for the even trace-moment constant.  This node is the formal interpolation layer separating the even Buchholz moment estimate from the arbitrary-$q$ statement used by Candes--Recht.
-- source:
--   Candes, Emmanuel, and Benjamin Recht. "Exact matrix completion via convex optimization." Communications of the ACM 55.6 (2012): 111-119.

import Definitions.Def_matrix_completion_gram_schatten
open MatrixCompletion
open scoped BigOperators

theorem rademacher_sampled_matrix_noncommutative_khintchine_q2_from_even_trace_pairbound
    (hEven :
      ∀ (n : Nat), 1 ≤ n →
      ∀ {n1 n2 : Nat} (Omega : Finset (Fin n1 × Fin n2)) (p : ℝ), 0 < p →
      ∀ X : RealMatrix n1 n2,
        rademacherExpectation
            (fun eps =>
              schattenNorm (2 * n : ℝ) (rademacherSampledMatrix Omega eps p X) ^
                (2 * n))
          ≤ ((Nat.factorial (2 * n) : ℝ) / ((2 ^ n : ℝ) * (Nat.factorial n : ℝ))) *
              max ((sampledRowGramSchatten Omega p X (2 * n : ℝ)) ^ (2 * n))
                  ((sampledColumnGramSchatten Omega p X (2 * n : ℝ)) ^ (2 * n))) :
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
  sorry
