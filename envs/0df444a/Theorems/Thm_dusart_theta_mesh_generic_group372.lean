-- Prove2me | Theorems.Thm_dusart_theta_mesh_generic_group372
-- name    : dusart_theta_mesh_generic_group372
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-10-17T01:54:55.643986+00:00
-- url     : https://prove2.me/theorems/4594101e-d696-4532-83c0-f49324f4ce5e
-- title:
--   Verified numerical interval from 4629848320 to 4646625536
-- statement:
--   Let $S(a,b;u,v)$ be a predicate on four natural numbers that validates every elementary block accepted by the finite checker under its validity and size conditions, and is closed under concatenating adjacent intervals with matching carries. Then
--
--   $$S(4629848320, 4646625536; 4629786647480499, 4646560854027854).$$
--
--   The last two arguments are endpoint carries with scale one million. This result provides a verified numerical interval for composing the finite Chebyshev theta estimate.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J.45 (2018),227-251, Theorem 4.2, pp.234-237; DOI 10.1007/s11139-016-9839-4. Supporting finite-certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_theta_mesh_numeric

theorem dusart_theta_mesh_generic_group372 : DusartNumeric.GenericSpec 4629848320 4646625536 4629786647480499 4646560854027854 := by sorry
