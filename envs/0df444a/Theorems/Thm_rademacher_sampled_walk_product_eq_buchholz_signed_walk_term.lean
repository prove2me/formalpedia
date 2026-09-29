-- Prove2me | Theorems.Thm_rademacher_sampled_walk_product_eq_buchholz_signed_walk_term
-- name    : rademacher_sampled_walk_product_eq_buchholz_signed_walk_term
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-06-24T01:29:32.30035+00:00
-- url     : https://prove2.me/theorems/ff829823-6603-4b17-bf29-b0e20d505460
-- statement:
--   Fix a set of observed coordinates $\Omega\subseteq[n_1]\times[n_2]$, a Rademacher sign assignment $\varepsilon$, a scalar $p$, a matrix $X\in\mathbb R^{n_1\times n_2}$, and one alternating closed walk $(i_k,j_k)_{k\in\mathbb Z/n\mathbb Z}$.
--
--   If $S_\varepsilon$ is the sampled signed matrix with entries
--   $$S_\varepsilon(i,j)=p^{-1}{\bf 1}_{(i,j)\in\Omega}\varepsilon_{ij}X_{ij},$$
--   then the walk product factors as
--   $$\prod_k S_\varepsilon(i_k,j_k)S_\varepsilon(i_{k+1},j_k)
--   =\Big[\prod_k p^{-1}{\bf 1}_{(i_k,j_k)\in\Omega}X_{i_kj_k}\,p^{-1}{\bf 1}_{(i_{k+1},j_k)\in\Omega}X_{i_{k+1}j_k}\Big]
--   \Big[\prod_k \varepsilon_{i_kj_k}\varepsilon_{i_{k+1}j_k}\Big].$$
--   The first bracket is `buchholzWalkProduct`; the second bracket is `buchholzWalkSignMonomial`.  Thus the whole product is exactly `buchholzSignedWalkTerm`.
-- source:
--   Candes, Emmanuel, and Benjamin Recht. "Exact matrix completion via convex optimization." Communications of the ACM 55.6 (2012): 111-119.

import Definitions.Def_buchholz_signed_walk_sum
open MatrixCompletion
open scoped BigOperators

theorem rademacher_sampled_walk_product_eq_buchholz_signed_walk_term
    {n n1 n2 : Nat} (Omega eps : Finset (Fin n1 × Fin n2)) (p : ℝ)
    (X : RealMatrix n1 n2)
    (rows : Fin n → Fin n1) (cols : Fin n → Fin n2) :
    (∏ k : Fin n,
      rademacherSampledMatrix Omega eps p X (rows k) (cols k) *
        rademacherSampledMatrix Omega eps p X
          (rows (buchholzCyclicSucc k)) (cols k))
      =
    buchholzSignedWalkTerm Omega eps p X rows cols := by
  sorry
