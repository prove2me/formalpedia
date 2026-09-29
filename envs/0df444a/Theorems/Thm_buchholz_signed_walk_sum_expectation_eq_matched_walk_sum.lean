-- Prove2me | Theorems.Thm_buchholz_signed_walk_sum_expectation_eq_matched_walk_sum
-- name    : buchholz_signed_walk_sum_expectation_eq_matched_walk_sum
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-06-23T23:06:36.708909+00:00
-- url     : https://prove2.me/theorems/03281b1f-596a-43f8-81e5-28e047ff9596
-- statement:
--   **Rademacher sign survival for the Buchholz walk expansion.** Let $\widetilde W_n(\varepsilon;\Omega,p,X)$ be the signed closed-walk sum.  Each coordinate edge $(i,j)$ contributes a sign factor $\varepsilon_{ij}$ every time the walk traverses that edge.
--
--   Averaging over all independent signs gives
--   $$\mathbb E_\varepsilon\,\widetilde W_n(\varepsilon;\Omega,p,X)=W_n(\Omega,p,X),$$
--   where $W_n$ is the matched-walk sum: a walk survives if and only if every coordinate edge has even multiplicity.  This is the finite sign-cube orthogonality step $\mathbb E\prod_c\varepsilon_c^{m_c}=1$ for all even $m_c$, and $0$ otherwise.
-- source:
--   Buchholz, A. "Operator Khintchine inequality in non-commutative probability." Math. Ann. 319 (2001): 1-16, Section 2; Candes, Emmanuel, and Benjamin Recht. "Exact matrix completion via convex optimization." Communications of the ACM 55.6 (2012): 111-119, Section 6.1 Lemma 6.1.

import Definitions.Def_buchholz_signed_walk_sum

open MatrixCompletion
open scoped BigOperators

theorem buchholz_signed_walk_sum_expectation_eq_matched_walk_sum
    (n : Nat) (hn : 1 ≤ n)
    {n1 n2 : Nat} (Omega : Finset (Fin n1 × Fin n2)) (p : ℝ) (hp : 0 < p)
    (X : RealMatrix n1 n2) :
    rademacherExpectation
        (fun eps => buchholzSignedWalkSum n Omega p X eps)
      = buchholzMatchedWalkSum n Omega p X := by
  sorry
