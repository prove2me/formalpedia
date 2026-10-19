-- Prove2me | Theorems.Thm_dusart_theta_mesh_generic_group009
-- name    : dusart_theta_mesh_generic_group009
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-10-17T01:05:13.116263+00:00
-- url     : https://prove2.me/theorems/ccefdbf5-e8e1-42f6-a3e2-9daf4c9b2d2b
-- title:
--   Verified numerical interval from 118874368 to 120971520
-- statement:
--   Let $S(a,b;u,v)$ be a predicate on four natural numbers that validates every elementary block accepted by the finite checker under its validity and size conditions, and is closed under concatenating adjacent intervals with matching carries. Then
--
--   $$S(118874368, 120971520; 118864984369831, 120957678469077).$$
--
--   The last two arguments are endpoint carries with scale one million. This result provides a verified numerical interval for composing the finite Chebyshev theta estimate.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J.45 (2018),227-251, Theorem 4.2, pp.234-237; DOI 10.1007/s11139-016-9839-4. Supporting finite-certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_theta_mesh_numeric

theorem dusart_theta_mesh_generic_group009 : DusartNumeric.GenericSpec 118874368 120971520 118864984369831 120957678469077 := by sorry
