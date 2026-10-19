-- Prove2me | Theorems.Thm_dusart_theta_mesh_generic_group378
-- name    : dusart_theta_mesh_generic_group378
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-10-17T01:56:26.164826+00:00
-- url     : https://prove2.me/theorems/664cdccb-f5db-4898-a76d-a390cabe54a1
-- title:
--   Verified numerical interval from 4730511616 to 4747288832
-- statement:
--   Let $S(a,b;u,v)$ be a predicate on four natural numbers that validates every elementary block accepted by the finite checker under its validity and size conditions, and is closed under concatenating adjacent intervals with matching carries. Then
--
--   $$S(4730511616, 4747288832; 4730453531620289, 4747234539669818).$$
--
--   The last two arguments are endpoint carries with scale one million. This result provides a verified numerical interval for composing the finite Chebyshev theta estimate.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J.45 (2018),227-251, Theorem 4.2, pp.234-237; DOI 10.1007/s11139-016-9839-4. Supporting finite-certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_theta_mesh_numeric

theorem dusart_theta_mesh_generic_group378 : DusartNumeric.GenericSpec 4730511616 4747288832 4730453531620289 4747234539669818 := by sorry
