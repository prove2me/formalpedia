-- Prove2me | Theorems.Thm_dusart_theta_mesh_generic_group458
-- name    : dusart_theta_mesh_generic_group458
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-10-17T02:07:07.720234+00:00
-- url     : https://prove2.me/theorems/94cb89e1-f07d-49f7-a421-76d0f84e8f61
-- title:
--   Verified numerical interval from 6072688896 to 6089466112
-- statement:
--   Let $S(a,b;u,v)$ be a predicate on four natural numbers that validates every elementary block accepted by the finite checker under its validity and size conditions, and is closed under concatenating adjacent intervals with matching carries. Then
--
--   $$S(6072688896, 6089466112; 6072613033599204, 6089392974397733).$$
--
--   The last two arguments are endpoint carries with scale one million. This result provides a verified numerical interval for composing the finite Chebyshev theta estimate.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J.45 (2018),227-251, Theorem 4.2, pp.234-237; DOI 10.1007/s11139-016-9839-4. Supporting finite-certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_theta_mesh_numeric

theorem dusart_theta_mesh_generic_group458 : DusartNumeric.GenericSpec 6072688896 6089466112 6072613033599204 6089392974397733 := by sorry
