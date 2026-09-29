-- Prove2me | Theorems.Thm_mme_stothers_general_hash_degree_exponential_budget
-- name    : mme_stothers_general_hash_degree_exponential_budget
-- status  : Proved
-- author  : @allychan327
-- created : 2026-09-08T05:40:59.622628+00:00
-- url     : https://prove2.me/theorems/cfbb150f-9949-492c-a8e9-4b3d88168135
-- title:
--   Exponential budget for a general hash degree
-- statement:
--   **A crude exponential budget for the hash degree.**
--
--   Fix an integral ten-class profile $\beta$ with strictly positive counts and a scale $m\ge1$, and
--   put $N = 3Dm$. Then
--
--   $$\bigl(6(N+1)\bigr)^{100}\,D_*\;\le\;5^{1000N},$$
--
--   where $D_*$ is the star degree of the exact profile at scale $m$.
--
--   The bound is deliberately generous: it is not a sharp estimate but the crude ceiling the
--   Behrend-type parameter selection needs, so that an odd prime modulus and a progression-free
--   residue set of adequate size can be produced for the outer affine hash. Its content is only that
--   the degree grows at most exponentially in the address length -- the star degree is at most the
--   total number of addresses, which is $729^N$ -- and that a fixed power of a linear polynomial is
--   swallowed by an exponential.
-- source:
--   A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication, Proceedings of the Royal Society of Edinburgh A 143(2), 2013, Section 3, Lemma 3.3; https://www.maths.ed.ac.uk/~sandy/a11164.pdf.

import Definitions.Def_mme_stothers_general_outer_profile

open MME BigOperators

set_option autoImplicit false

theorem mme_stothers_general_hash_degree_exponential_budget
    (base : Fin 10 → ℕ) (m : ℕ) (hm : 0 < m)
    (hbase : ∀ r, 0 < base r) :
    let N := MME.StothersFourth.genOuterLength base m
    (6 * (N + 1)) ^ 100 *
        MME.StothersFourth.genHashTargetStarDegree base m ≤
      5 ^ (1000 * N) := by
  sorry
