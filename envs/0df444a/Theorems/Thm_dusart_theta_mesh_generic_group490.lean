-- Prove2me | Theorems.Thm_dusart_theta_mesh_generic_group490
-- name    : dusart_theta_mesh_generic_group490
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-10-17T02:09:51.417985+00:00
-- url     : https://prove2.me/theorems/67d09f54-3560-42b4-82b1-55636c0ad894
-- title:
--   Verified numerical interval from 6609559808 to 6626337024
-- statement:
--   Let $S(a,b;u,v)$ be a predicate on four natural numbers that validates every elementary block accepted by the finite checker under its validity and size conditions, and is closed under concatenating adjacent intervals with matching carries. Then
--
--   $$S(6609559808, 6626337024; 6609501735073195, 6626281690382488).$$
--
--   The last two arguments are endpoint carries with scale one million. This result provides a verified numerical interval for composing the finite Chebyshev theta estimate.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J.45 (2018),227-251, Theorem 4.2, pp.234-237; DOI 10.1007/s11139-016-9839-4. Supporting finite-certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_theta_mesh_numeric

theorem dusart_theta_mesh_generic_group490 : DusartNumeric.GenericSpec 6609559808 6626337024 6609501735073195 6626281690382488 := by sorry
