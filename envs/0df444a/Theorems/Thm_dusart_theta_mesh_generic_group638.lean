-- Prove2me | Theorems.Thm_dusart_theta_mesh_generic_group638
-- name    : dusart_theta_mesh_generic_group638
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-10-17T02:26:44.96573+00:00
-- url     : https://prove2.me/theorems/64e9a1fa-bc53-4d97-90b3-f91e16ade552
-- title:
--   Verified numerical interval from 9092587776 to 9109364992
-- statement:
--   Let $S(a,b;u,v)$ be a predicate on four natural numbers that validates every elementary block accepted by the finite checker under its validity and size conditions, and is closed under concatenating adjacent intervals with matching carries. Then
--
--   $$S(9092587776, 9109364992; 9092501640137034, 9109271493254758).$$
--
--   The last two arguments are endpoint carries with scale one million. This result provides a verified numerical interval for composing the finite Chebyshev theta estimate.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J.45 (2018),227-251, Theorem 4.2, pp.234-237; DOI 10.1007/s11139-016-9839-4. Supporting finite-certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_theta_mesh_numeric

theorem dusart_theta_mesh_generic_group638 : DusartNumeric.GenericSpec 9092587776 9109364992 9092501640137034 9109271493254758 := by sorry
