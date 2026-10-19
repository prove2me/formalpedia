-- Prove2me | Theorems.Thm_dusart_theta_mesh_generic_group032
-- name    : dusart_theta_mesh_generic_group032
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-10-17T01:11:51.341429+00:00
-- url     : https://prove2.me/theorems/425d3288-2003-4b17-9972-11aade7cac95
-- title:
--   Verified numerical interval from 167108864 to 169206016
-- statement:
--   Let $S(a,b;u,v)$ be a predicate on four natural numbers that validates every elementary block accepted by the finite checker under its validity and size conditions, and is closed under concatenating adjacent intervals with matching carries. Then
--
--   $$S(167108864, 169206016; 167094547216418, 169193166247805).$$
--
--   The last two arguments are endpoint carries with scale one million. This result provides a verified numerical interval for composing the finite Chebyshev theta estimate.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J.45 (2018),227-251, Theorem 4.2, pp.234-237; DOI 10.1007/s11139-016-9839-4. Supporting finite-certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_theta_mesh_numeric

theorem dusart_theta_mesh_generic_group032 : DusartNumeric.GenericSpec 167108864 169206016 167094547216418 169193166247805 := by sorry
