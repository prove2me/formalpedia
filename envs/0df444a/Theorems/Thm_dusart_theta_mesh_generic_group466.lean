-- Prove2me | Theorems.Thm_dusart_theta_mesh_generic_group466
-- name    : dusart_theta_mesh_generic_group466
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-10-17T02:07:10.120139+00:00
-- url     : https://prove2.me/theorems/cb2b2c31-5bc3-4c50-bcda-00c2227a0bbe
-- title:
--   Verified numerical interval from 6206906624 to 6223683840
-- statement:
--   Let $S(a,b;u,v)$ be a predicate on four natural numbers that validates every elementary block accepted by the finite checker under its validity and size conditions, and is closed under concatenating adjacent intervals with matching carries. Then
--
--   $$S(6206906624, 6223683840; 6206865834885360, 6223635651701983).$$
--
--   The last two arguments are endpoint carries with scale one million. This result provides a verified numerical interval for composing the finite Chebyshev theta estimate.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J.45 (2018),227-251, Theorem 4.2, pp.234-237; DOI 10.1007/s11139-016-9839-4. Supporting finite-certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_theta_mesh_numeric

theorem dusart_theta_mesh_generic_group466 : DusartNumeric.GenericSpec 6206906624 6223683840 6206865834885360 6223635651701983 := by sorry
