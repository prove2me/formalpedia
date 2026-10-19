-- Prove2me | Theorems.Thm_dusart_theta_mesh_generic_group371
-- name    : dusart_theta_mesh_generic_group371
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-10-17T01:54:25.899666+00:00
-- url     : https://prove2.me/theorems/bccd994a-6a37-4c60-a002-621a580a3bc0
-- title:
--   Verified numerical interval from 4613071104 to 4629848320
-- statement:
--   Let $S(a,b;u,v)$ be a predicate on four natural numbers that validates every elementary block accepted by the finite checker under its validity and size conditions, and is closed under concatenating adjacent intervals with matching carries. Then
--
--   $$S(4613071104, 4629848320; 4613007872066884, 4629786647480499).$$
--
--   The last two arguments are endpoint carries with scale one million. This result provides a verified numerical interval for composing the finite Chebyshev theta estimate.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J.45 (2018),227-251, Theorem 4.2, pp.234-237; DOI 10.1007/s11139-016-9839-4. Supporting finite-certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_theta_mesh_numeric

theorem dusart_theta_mesh_generic_group371 : DusartNumeric.GenericSpec 4613071104 4629848320 4613007872066884 4629786647480499 := by sorry
