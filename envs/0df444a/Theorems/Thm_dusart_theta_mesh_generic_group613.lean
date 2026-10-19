-- Prove2me | Theorems.Thm_dusart_theta_mesh_generic_group613
-- name    : dusart_theta_mesh_generic_group613
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-10-17T02:23:41.136278+00:00
-- url     : https://prove2.me/theorems/5ca34ab7-da1c-4c29-81b2-1b8be33129db
-- title:
--   Verified numerical interval from 8673157376 to 8689934592
-- statement:
--   Let $S(a,b;u,v)$ be a predicate on four natural numbers that validates every elementary block accepted by the finite checker under its validity and size conditions, and is closed under concatenating adjacent intervals with matching carries. Then
--
--   $$S(8673157376, 8689934592; 8673073751814701, 8689843290874405).$$
--
--   The last two arguments are endpoint carries with scale one million. This result provides a verified numerical interval for composing the finite Chebyshev theta estimate.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J.45 (2018),227-251, Theorem 4.2, pp.234-237; DOI 10.1007/s11139-016-9839-4. Supporting finite-certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_theta_mesh_numeric

theorem dusart_theta_mesh_generic_group613 : DusartNumeric.GenericSpec 8673157376 8689934592 8673073751814701 8689843290874405 := by sorry
