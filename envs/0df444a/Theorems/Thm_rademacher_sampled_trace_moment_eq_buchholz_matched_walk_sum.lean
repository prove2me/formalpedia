-- Prove2me | Theorems.Thm_rademacher_sampled_trace_moment_eq_buchholz_matched_walk_sum
-- name    : rademacher_sampled_trace_moment_eq_buchholz_matched_walk_sum
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-06-23T22:45:32.489677+00:00
-- url     : https://prove2.me/theorems/8bf83237-8167-4aae-a419-8a23897674a8
-- statement:
--   **Trace expansion and sign survival for the Buchholz moment method.** Let
--   $$S_\varepsilon=p^{-1}\sum_{(i,j)\in\Omega}\varepsilon_{ij}X_{ij}e_i e_j^{\top}$$
--   be the sampled coordinate Rademacher series. For every integer $n\ge1$, expanding $\operatorname{tr}((S_\varepsilon S_\varepsilon^{\top})^n)$ gives a sum over alternating closed row/column walks. Averaging over the independent signs kills exactly the monomials in which some coordinate edge occurs an odd number of times.
--
--   The theorem states the resulting identity
--   $$\mathbb E_\varepsilon\,\operatorname{tr}((S_\varepsilon S_\varepsilon^{\top})^n)=W_n(\Omega,p,X),$$
--   where $W_n(\Omega,p,X)$ is the matched-walk sum defined in `buchholz_walk_sum`: only walks whose every coordinate edge has even multiplicity contribute. This is the formal K-expand/sign-orthogonality layer; it does not contain the Buchholz pair-count estimate.
-- source:
--   Buchholz, A. "Operator Khintchine inequality in non-commutative probability." Math. Ann. 319 (2001): 1-16, Sections 2-3; Candes, Emmanuel, and Benjamin Recht. "Exact matrix completion via convex optimization." Communications of the ACM 55.6 (2012): 111-119, Section 6.1 Lemma 6.1.

import Definitions.Def_buchholz_walk_sum

open MatrixCompletion
open scoped BigOperators

theorem rademacher_sampled_trace_moment_eq_buchholz_matched_walk_sum
    (n : Nat) (hn : 1 ≤ n)
    {n1 n2 : Nat} (Omega : Finset (Fin n1 × Fin n2)) (p : ℝ) (hp : 0 < p)
    (X : RealMatrix n1 n2) :
    rademacherExpectation
        (fun eps =>
          Matrix.trace
            ((rademacherSampledMatrix Omega eps p X *
                (rademacherSampledMatrix Omega eps p X).transpose) ^ n))
      = buchholzMatchedWalkSum n Omega p X := by
  sorry
