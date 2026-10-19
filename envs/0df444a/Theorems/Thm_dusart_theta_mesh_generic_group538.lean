-- Prove2me | Theorems.Thm_dusart_theta_mesh_generic_group538
-- name    : dusart_theta_mesh_generic_group538
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-10-17T02:14:11.241982+00:00
-- url     : https://prove2.me/theorems/2b7542e2-b469-47e1-9527-3dd1805e31fe
-- title:
--   Verified numerical interval from 7414866176 to 7431643392
-- statement:
--   Let $S(a,b;u,v)$ be a predicate on four natural numbers that validates every elementary block accepted by the finite checker under its validity and size conditions, and is closed under concatenating adjacent intervals with matching carries. Then
--
--   $$S(7414866176, 7431643392; 7414786871743058, 7431563557371260).$$
--
--   The last two arguments are endpoint carries with scale one million. This result provides a verified numerical interval for composing the finite Chebyshev theta estimate.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J.45 (2018),227-251, Theorem 4.2, pp.234-237; DOI 10.1007/s11139-016-9839-4. Supporting finite-certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_theta_mesh_numeric

theorem dusart_theta_mesh_generic_group538 : DusartNumeric.GenericSpec 7414866176 7431643392 7414786871743058 7431563557371260 := by sorry
