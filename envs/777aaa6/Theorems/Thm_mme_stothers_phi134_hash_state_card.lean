-- Prove2me | Theorems.Thm_mme_stothers_phi134_hash_state_card
-- name    : mme_stothers_phi134_hash_state_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-05T10:27:19.461068+00:00
-- url     : https://prove2.me/theorems/0e3d2ee1-b93b-442f-a9dd-33db5df22e1c
-- title:
--   $\Phi_{1,3,4}$ affine hash-state cardinality
-- statement:
--   For a prime $p$, the affine hash-state space for the cyclic $\Phi_{1,3,4}$ family has cardinality
--
--   $$
--   |\Omega_{p,N}|=p^2\,p^{6N}.
--   $$
--
--   The $6N$ exponent records three rows of $2N$ independent hash weights, while the remaining two powers of $p$ record the common shift and progression offset. This exact state-space factorization is the normalization used by the finite Type-2 collision budget.
-- source:
--   A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication, Proc. Roy. Soc. Edinburgh Sect. A 143 (2013), 351–369, affine hashing parameter count in Lemma 3.3 (pp. 359–361), specialized to the cyclic $\Phi_{1,3,4}$ family of Lemma 5.1(iii) (p. 365); https://www.maths.ed.ac.uk/~sandy/a11164.pdf.

import Definitions.Def_mme_stothers_phi134_cyclic_hash_data

open MME.StothersFourth.Phi134

set_option autoImplicit false

theorem mme_stothers_phi134_hash_state_card
    (p N : ℕ) [Fact p.Prime] :
    Fintype.card (HashState p N) = p ^ 2 * p ^ (6 * N) := by
  sorry
