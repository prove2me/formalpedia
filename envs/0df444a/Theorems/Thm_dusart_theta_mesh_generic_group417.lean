-- Prove2me | Theorems.Thm_dusart_theta_mesh_generic_group417
-- name    : dusart_theta_mesh_generic_group417
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-10-17T02:01:47.105881+00:00
-- url     : https://prove2.me/theorems/3b2e16b6-4a00-422b-b3eb-c3556580f82b
-- title:
--   Verified numerical interval from 5384823040 to 5401600256
-- statement:
--   Let $S(a,b;u,v)$ be a predicate on four natural numbers that validates every elementary block accepted by the finite checker under its validity and size conditions, and is closed under concatenating adjacent intervals with matching carries. Then
--
--   $$S(5384823040, 5401600256; 5384753289893376, 5401514206111290).$$
--
--   The last two arguments are endpoint carries with scale one million. This result provides a verified numerical interval for composing the finite Chebyshev theta estimate.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J.45 (2018),227-251, Theorem 4.2, pp.234-237; DOI 10.1007/s11139-016-9839-4. Supporting finite-certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_theta_mesh_numeric

theorem dusart_theta_mesh_generic_group417 : DusartNumeric.GenericSpec 5384823040 5401600256 5384753289893376 5401514206111290 := by sorry
