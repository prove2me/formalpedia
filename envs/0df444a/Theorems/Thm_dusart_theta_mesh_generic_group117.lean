-- Prove2me | Theorems.Thm_dusart_theta_mesh_generic_group117
-- name    : dusart_theta_mesh_generic_group117
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-10-17T01:27:39.156234+00:00
-- url     : https://prove2.me/theorems/c38a41cc-e4ec-4f1b-bff3-98a025f89cef
-- title:
--   Verified numerical interval from 578150656 to 586539264
-- statement:
--   Let $S(a,b;u,v)$ be a predicate on four natural numbers that validates every elementary block accepted by the finite checker under its validity and size conditions, and is closed under concatenating adjacent intervals with matching carries. Then
--
--   $$S(578150656, 586539264; 578122438954017, 586512061945941).$$
--
--   The last two arguments are endpoint carries with scale one million. This result provides a verified numerical interval for composing the finite Chebyshev theta estimate.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J.45 (2018),227-251, Theorem 4.2, pp.234-237; DOI 10.1007/s11139-016-9839-4. Supporting finite-certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_theta_mesh_numeric

theorem dusart_theta_mesh_generic_group117 : DusartNumeric.GenericSpec 578150656 586539264 578122438954017 586512061945941 := by sorry
