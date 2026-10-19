-- Prove2me | Theorems.Thm_dusart_theta_mesh_generic_group335
-- name    : dusart_theta_mesh_generic_group335
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-10-17T01:52:01.327308+00:00
-- url     : https://prove2.me/theorems/c296f60d-d0a7-41cf-8225-3ae799d419c6
-- title:
--   Verified numerical interval from 4009091328 to 4025868544
-- statement:
--   Let $S(a,b;u,v)$ be a predicate on four natural numbers that validates every elementary block accepted by the finite checker under its validity and size conditions, and is closed under concatenating adjacent intervals with matching carries. Then
--
--   $$S(4009091328, 4025868544; 4009045358044043, 4025812541910781).$$
--
--   The last two arguments are endpoint carries with scale one million. This result provides a verified numerical interval for composing the finite Chebyshev theta estimate.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J.45 (2018),227-251, Theorem 4.2, pp.234-237; DOI 10.1007/s11139-016-9839-4. Supporting finite-certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_theta_mesh_numeric

theorem dusart_theta_mesh_generic_group335 : DusartNumeric.GenericSpec 4009091328 4025868544 4009045358044043 4025812541910781 := by sorry
