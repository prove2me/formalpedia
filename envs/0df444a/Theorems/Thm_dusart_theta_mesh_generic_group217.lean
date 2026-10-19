-- Prove2me | Theorems.Thm_dusart_theta_mesh_generic_group217
-- name    : dusart_theta_mesh_generic_group217
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-10-17T01:37:37.875007+00:00
-- url     : https://prove2.me/theorems/ac8e5d0b-6b85-4607-b743-918b45bbb534
-- title:
--   Verified numerical interval from 2029379840 to 2046157056
-- statement:
--   Let $S(a,b;u,v)$ be a predicate on four natural numbers that validates every elementary block accepted by the finite checker under its validity and size conditions, and is closed under concatenating adjacent intervals with matching carries. Then
--
--   $$S(2029379840, 2046157056; 2029339248153841, 2046118247616594).$$
--
--   The last two arguments are endpoint carries with scale one million. This result provides a verified numerical interval for composing the finite Chebyshev theta estimate.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J.45 (2018),227-251, Theorem 4.2, pp.234-237; DOI 10.1007/s11139-016-9839-4. Supporting finite-certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_theta_mesh_numeric

theorem dusart_theta_mesh_generic_group217 : DusartNumeric.GenericSpec 2029379840 2046157056 2029339248153841 2046118247616594 := by sorry
