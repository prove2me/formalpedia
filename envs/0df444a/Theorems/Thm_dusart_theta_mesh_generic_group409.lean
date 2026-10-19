-- Prove2me | Theorems.Thm_dusart_theta_mesh_generic_group409
-- name    : dusart_theta_mesh_generic_group409
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-10-17T01:59:49.546834+00:00
-- url     : https://prove2.me/theorems/e10671e2-5817-45f3-a51f-ff81642220de
-- title:
--   Verified numerical interval from 5250605312 to 5267382528
-- statement:
--   Let $S(a,b;u,v)$ be a predicate on four natural numbers that validates every elementary block accepted by the finite checker under its validity and size conditions, and is closed under concatenating adjacent intervals with matching carries. Then
--
--   $$S(5250605312, 5267382528; 5250535794512304, 5267313562107754).$$
--
--   The last two arguments are endpoint carries with scale one million. This result provides a verified numerical interval for composing the finite Chebyshev theta estimate.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J.45 (2018),227-251, Theorem 4.2, pp.234-237; DOI 10.1007/s11139-016-9839-4. Supporting finite-certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_theta_mesh_numeric

theorem dusart_theta_mesh_generic_group409 : DusartNumeric.GenericSpec 5250605312 5267382528 5250535794512304 5267313562107754 := by sorry
