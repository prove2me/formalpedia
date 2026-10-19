-- Prove2me | Theorems.Thm_dusart_theta_mesh_generic_group357
-- name    : dusart_theta_mesh_generic_group357
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-10-17T01:53:31.359903+00:00
-- url     : https://prove2.me/theorems/f8e1eb53-c731-48e5-b165-7e4b41b3cd3b
-- title:
--   Verified numerical interval from 4378190080 to 4394967296
-- statement:
--   Let $S(a,b;u,v)$ be a predicate on four natural numbers that validates every elementary block accepted by the finite checker under its validity and size conditions, and is closed under concatenating adjacent intervals with matching carries. Then
--
--   $$S(4378190080, 4394967296; 4378143440479471, 4394911128012826).$$
--
--   The last two arguments are endpoint carries with scale one million. This result provides a verified numerical interval for composing the finite Chebyshev theta estimate.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J.45 (2018),227-251, Theorem 4.2, pp.234-237; DOI 10.1007/s11139-016-9839-4. Supporting finite-certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_theta_mesh_numeric

theorem dusart_theta_mesh_generic_group357 : DusartNumeric.GenericSpec 4378190080 4394967296 4378143440479471 4394911128012826 := by sorry
