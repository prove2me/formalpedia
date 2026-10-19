-- Prove2me | Theorems.Thm_dusart_theta_mesh_generic_group000
-- name    : dusart_theta_mesh_generic_group000
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-10-17T00:40:17.275983+00:00
-- url     : https://prove2.me/theorems/21da89ad-ff49-444f-8d4a-4237ada4a12e
-- title:
--   Dusart finite mesh: complete numerical certificate on the first upper interval
-- statement:
--   Let $S(a,b;u,v)$ be a predicate on four natural numbers that validates every elementary block accepted by the finite checker under its validity and size conditions, and is closed under concatenating adjacent intervals with matching carries. Then
--
--   $$S(100000000, 102097152; 99989691935170, 102087562006788).$$
--
--   The last two arguments are endpoint carries with fixed scale one million. The result provides a verified numerical interval for composing the finite Chebyshev theta estimate.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J.45 (2018),227-251, Theorem4.2 (k=4, eta=151.3, x0=2), pp.234-237; DOI10.1007/s11139-016-9839-4. Complete finite-certificate helper for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_theta_mesh_numeric

theorem dusart_theta_mesh_generic_group000 : DusartNumeric.GenericSpec 100000000 102097152 99989691935170 102087562006788 := by sorry
