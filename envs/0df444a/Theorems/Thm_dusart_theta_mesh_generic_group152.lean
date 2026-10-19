-- Prove2me | Theorems.Thm_dusart_theta_mesh_generic_group152
-- name    : dusart_theta_mesh_generic_group152
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-10-17T01:30:13.569813+00:00
-- url     : https://prove2.me/theorems/3aa70d9c-ad09-45a5-9cf6-901020e6d9bf
-- title:
--   Verified numerical interval from 938860800 to 955638016
-- statement:
--   Let $S(a,b;u,v)$ be a predicate on four natural numbers that validates every elementary block accepted by the finite checker under its validity and size conditions, and is closed under concatenating adjacent intervals with matching carries. Then
--
--   $$S(938860800, 955638016; 938827934867994, 955604281400543).$$
--
--   The last two arguments are endpoint carries with scale one million. This result provides a verified numerical interval for composing the finite Chebyshev theta estimate.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J.45 (2018),227-251, Theorem 4.2, pp.234-237; DOI 10.1007/s11139-016-9839-4. Supporting finite-certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_theta_mesh_numeric

theorem dusart_theta_mesh_generic_group152 : DusartNumeric.GenericSpec 938860800 955638016 938827934867994 955604281400543 := by sorry
