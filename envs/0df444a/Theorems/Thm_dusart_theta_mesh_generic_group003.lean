-- Prove2me | Theorems.Thm_dusart_theta_mesh_generic_group003
-- name    : dusart_theta_mesh_generic_group003
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-10-17T01:05:13.033754+00:00
-- url     : https://prove2.me/theorems/a0918b8c-19dc-404c-b571-cbd5b4fdc22f
-- title:
--   Verified numerical interval from 106291456 to 108388608
-- statement:
--   Let $S(a,b;u,v)$ be a predicate on four natural numbers that validates every elementary block accepted by the finite checker under its validity and size conditions, and is closed under concatenating adjacent intervals with matching carries. Then
--
--   $$S(106291456, 108388608; 106282121086858, 108382945134435).$$
--
--   The last two arguments are endpoint carries with scale one million. This result provides a verified numerical interval for composing the finite Chebyshev theta estimate.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J.45 (2018),227-251, Theorem 4.2, pp.234-237; DOI 10.1007/s11139-016-9839-4. Supporting finite-certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_theta_mesh_numeric

theorem dusart_theta_mesh_generic_group003 : DusartNumeric.GenericSpec 106291456 108388608 106282121086858 108382945134435 := by sorry
