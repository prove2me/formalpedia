-- Prove2me | Theorems.Thm_dusart_theta_mesh_generic_group029
-- name    : dusart_theta_mesh_generic_group029
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-10-17T01:11:53.381781+00:00
-- url     : https://prove2.me/theorems/fe7940b0-5b2e-4ae1-a684-21b6966f715f
-- title:
--   Verified numerical interval from 160817408 to 162914560
-- statement:
--   Let $S(a,b;u,v)$ be a predicate on four natural numbers that validates every elementary block accepted by the finite checker under its validity and size conditions, and is closed under concatenating adjacent intervals with matching carries. Then
--
--   $$S(160817408, 162914560; 160804854096877, 162900023398825).$$
--
--   The last two arguments are endpoint carries with scale one million. This result provides a verified numerical interval for composing the finite Chebyshev theta estimate.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J.45 (2018),227-251, Theorem 4.2, pp.234-237; DOI 10.1007/s11139-016-9839-4. Supporting finite-certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_theta_mesh_numeric

theorem dusart_theta_mesh_generic_group029 : DusartNumeric.GenericSpec 160817408 162914560 160804854096877 162900023398825 := by sorry
