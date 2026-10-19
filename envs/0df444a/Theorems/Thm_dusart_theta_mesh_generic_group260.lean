-- Prove2me | Theorems.Thm_dusart_theta_mesh_generic_group260
-- name    : dusart_theta_mesh_generic_group260
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-10-17T01:43:01.644978+00:00
-- url     : https://prove2.me/theorems/d0fb7506-a28b-46e6-9e82-73eafc06ddd7
-- title:
--   Verified numerical interval from 2750800128 to 2767577344
-- statement:
--   Let $S(a,b;u,v)$ be a predicate on four natural numbers that validates every elementary block accepted by the finite checker under its validity and size conditions, and is closed under concatenating adjacent intervals with matching carries. Then
--
--   $$S(2750800128, 2767577344; 2750744977759491, 2767518079463206).$$
--
--   The last two arguments are endpoint carries with scale one million. This result provides a verified numerical interval for composing the finite Chebyshev theta estimate.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J.45 (2018),227-251, Theorem 4.2, pp.234-237; DOI 10.1007/s11139-016-9839-4. Supporting finite-certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_theta_mesh_numeric

theorem dusart_theta_mesh_generic_group260 : DusartNumeric.GenericSpec 2750800128 2767577344 2750744977759491 2767518079463206 := by sorry
