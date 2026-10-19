-- Prove2me | Theorems.Thm_dusart_theta_mesh_generic_group662
-- name    : dusart_theta_mesh_generic_group662
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-10-17T02:30:16.813472+00:00
-- url     : https://prove2.me/theorems/7bc64b95-52a7-4eec-a0da-83970b8e8a3a
-- title:
--   Verified numerical interval from 9495240960 to 9512018176
-- statement:
--   Let $S(a,b;u,v)$ be a predicate on four natural numbers that validates every elementary block accepted by the finite checker under its validity and size conditions, and is closed under concatenating adjacent intervals with matching carries. Then
--
--   $$S(9495240960, 9512018176; 9495154464216269, 9511925213794728).$$
--
--   The last two arguments are endpoint carries with scale one million. This result provides a verified numerical interval for composing the finite Chebyshev theta estimate.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J.45 (2018),227-251, Theorem 4.2, pp.234-237; DOI 10.1007/s11139-016-9839-4. Supporting finite-certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_theta_mesh_numeric

theorem dusart_theta_mesh_generic_group662 : DusartNumeric.GenericSpec 9495240960 9512018176 9495154464216269 9511925213794728 := by sorry
