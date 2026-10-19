-- Prove2me | Theorems.Thm_dusart_theta_mesh_generic_group094
-- name    : dusart_theta_mesh_generic_group094
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-10-17T01:26:14.935651+00:00
-- url     : https://prove2.me/theorems/adb32059-3964-4223-8548-d59cd5c5e1ba
-- title:
--   Verified numerical interval from 393601280 to 397795584
-- statement:
--   Let $S(a,b;u,v)$ be a predicate on four natural numbers that validates every elementary block accepted by the finite checker under its validity and size conditions, and is closed under concatenating adjacent intervals with matching carries. Then
--
--   $$S(393601280, 397795584; 393583985566110, 397777292601651).$$
--
--   The last two arguments are endpoint carries with scale one million. This result provides a verified numerical interval for composing the finite Chebyshev theta estimate.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J.45 (2018),227-251, Theorem 4.2, pp.234-237; DOI 10.1007/s11139-016-9839-4. Supporting finite-certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_theta_mesh_numeric

theorem dusart_theta_mesh_generic_group094 : DusartNumeric.GenericSpec 393601280 397795584 393583985566110 397777292601651 := by sorry
