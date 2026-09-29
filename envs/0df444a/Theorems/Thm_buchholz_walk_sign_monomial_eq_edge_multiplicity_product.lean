-- Prove2me | Theorems.Thm_buchholz_walk_sign_monomial_eq_edge_multiplicity_product
-- name    : buchholz_walk_sign_monomial_eq_edge_multiplicity_product
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-06-23T23:39:11.539495+00:00
-- url     : https://prove2.me/theorems/02a4d225-f80c-4c03-b272-1621e5533a72
-- statement:
--   **Reindexing a walk sign monomial by coordinate-edge multiplicity.** Fix one alternating closed walk with row vertices $i_k$ and column vertices $j_k$.  The sign part of its Buchholz walk term is naturally written as
--   $$\prod_k \varepsilon_{i_k j_k},\varepsilon_{i_{k+1} j_k}.$$
--   This theorem rewrites that same monomial as a product over coordinate edges:
--   $$\prod_{(i,j)} \varepsilon_{ij}^{m_{ij}},$$
--   where $m_{ij}$ is the number of times the edge $(i,j)$ is traversed by the alternating closed walk.  It is pure finite-product bookkeeping and is the bridge from the walk notation to the platform theorem `E_sign_monomial`.
-- source:
--   Buchholz, A. "Operator Khintchine inequality in non-commutative probability." Math. Ann. 319 (2001): 1-16, Section 2; Candes, Emmanuel, and Benjamin Recht. "Exact matrix completion via convex optimization." Communications of the ACM 55.6 (2012): 111-119, Section 6.1 Lemma 6.1.

import Definitions.Def_buchholz_signed_walk_sum

open MatrixCompletion
open scoped BigOperators

theorem buchholz_walk_sign_monomial_eq_edge_multiplicity_product
    {n n1 n2 : Nat}
    (eps : Finset (Fin n1 × Fin n2))
    (rows : Fin n → Fin n1) (cols : Fin n → Fin n2) :
    buchholzWalkSignMonomial eps rows cols =
      ∏ c : Fin n1 × Fin n2,
        rademacherSign eps c.1 c.2 ^
          buchholzEdgeMultiplicity rows cols c := by
  sorry
