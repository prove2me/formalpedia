-- Prove2me | Theorems.Thm_mme_CW_q6_exact_coupled_address_regularity
-- name    : mme_CW_q6_exact_coupled_address_regularity
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-24T19:13:21.695489+00:00
-- url     : https://prove2.me/theorems/a358629f-4b53-4e04-82c2-1609f8274ed5
-- title:
--   Exact enumeration and biregularity of the coupled q=6 profile hypergraph
-- statement:
--   Assume $L+G=N$. The finite hypergraph of exact coupled q=6 addresses is biregular with the precise counts displayed on CW90 pp. 270–271. It has
--
--   $$choose(2N,L) choose(2N-L,L) choose(2G,G)$$
--
--   edges, $choose(2N,N)$ distinct X words and the same number of Y words, and $choose(2N,L)choose(2N-L,L)$ distinct Z words. Every X or Y word lies in exactly $choose(N,G)^2$ addresses, while every Z word lies in exactly $choose(2G,G)$ addresses.
--
--   These identities justify both the modulus $4choose(N,G)^2+1$ and the unpruned middle-fiber size used in the q=6 first hash.
-- source:
--   D. Coppersmith and S. Winograd, Matrix Multiplication via Arithmetic Progressions, Journal of Symbolic Computation 9 (1990), journal pp. 270–271, displayed exact-profile counts immediately before and after M=4*choose(L+G,G)^2+1; https://doi.org/10.1016/S0747-7171(08)80013-2

import Definitions.Def_mme_CW_q6_exact_address_incidence

open MME

theorem mme_CW_q6_exact_coupled_address_regularity
    (N L G : ℕ) (hLG : L + G = N) :
    CWQ6ExactAddressRegularity N L G := by sorry
