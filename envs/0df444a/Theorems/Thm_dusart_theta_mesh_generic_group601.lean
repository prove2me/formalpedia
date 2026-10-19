-- Prove2me | Theorems.Thm_dusart_theta_mesh_generic_group601
-- name    : dusart_theta_mesh_generic_group601
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-10-17T02:22:00.428782+00:00
-- url     : https://prove2.me/theorems/328a6619-2988-4221-bb5c-ca007e256a49
-- title:
--   Verified numerical interval from 8471830784 to 8488608000
-- statement:
--   Let $S(a,b;u,v)$ be a predicate on four natural numbers that validates every elementary block accepted by the finite checker under its validity and size conditions, and is closed under concatenating adjacent intervals with matching carries. Then
--
--   $$S(8471830784, 8488608000; 8471751149244558, 8488525828068548).$$
--
--   The last two arguments are endpoint carries with scale one million. This result provides a verified numerical interval for composing the finite Chebyshev theta estimate.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J.45 (2018),227-251, Theorem 4.2, pp.234-237; DOI 10.1007/s11139-016-9839-4. Supporting finite-certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_theta_mesh_numeric

theorem dusart_theta_mesh_generic_group601 : DusartNumeric.GenericSpec 8471830784 8488608000 8471751149244558 8488525828068548 := by sorry
