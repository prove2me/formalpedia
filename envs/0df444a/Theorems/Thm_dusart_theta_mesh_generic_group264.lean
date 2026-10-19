-- Prove2me | Theorems.Thm_dusart_theta_mesh_generic_group264
-- name    : dusart_theta_mesh_generic_group264
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-10-17T01:43:19.93931+00:00
-- url     : https://prove2.me/theorems/45ab0547-66b5-495c-b42e-8d62d8c4e978
-- title:
--   Verified numerical interval from 2817908992 to 2834686208
-- statement:
--   Let $S(a,b;u,v)$ be a predicate on four natural numbers that validates every elementary block accepted by the finite checker under its validity and size conditions, and is closed under concatenating adjacent intervals with matching carries. Then
--
--   $$S(2817908992, 2834686208; 2817860004039128, 2834641331636288).$$
--
--   The last two arguments are endpoint carries with scale one million. This result provides a verified numerical interval for composing the finite Chebyshev theta estimate.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J.45 (2018),227-251, Theorem 4.2, pp.234-237; DOI 10.1007/s11139-016-9839-4. Supporting finite-certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_theta_mesh_numeric

theorem dusart_theta_mesh_generic_group264 : DusartNumeric.GenericSpec 2817908992 2834686208 2817860004039128 2834641331636288 := by sorry
