-- Prove2me | Theorems.Thm_dusart_theta_mesh_generic_group472
-- name    : dusart_theta_mesh_generic_group472
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-10-17T02:06:06.775306+00:00
-- url     : https://prove2.me/theorems/fb4c6c0b-295d-432c-a47f-0d375183e226
-- title:
--   Verified numerical interval from 6307569920 to 6324347136
-- statement:
--   Let $S(a,b;u,v)$ be a predicate on four natural numbers that validates every elementary block accepted by the finite checker under its validity and size conditions, and is closed under concatenating adjacent intervals with matching carries. Then
--
--   $$S(6307569920, 6324347136; 6307532163252222, 6324305511144393).$$
--
--   The last two arguments are endpoint carries with scale one million. This result provides a verified numerical interval for composing the finite Chebyshev theta estimate.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J.45 (2018),227-251, Theorem 4.2, pp.234-237; DOI 10.1007/s11139-016-9839-4. Supporting finite-certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_theta_mesh_numeric

theorem dusart_theta_mesh_generic_group472 : DusartNumeric.GenericSpec 6307569920 6324347136 6307532163252222 6324305511144393 := by sorry
