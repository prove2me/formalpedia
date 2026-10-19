-- Prove2me | Theorems.Thm_dusart_theta_mesh_generic_group427
-- name    : dusart_theta_mesh_generic_group427
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-10-17T02:01:18.01431+00:00
-- url     : https://prove2.me/theorems/9708a53b-bd84-491b-af3a-7f7ae5429569
-- title:
--   Verified numerical interval from 5552595200 to 5569372416
-- statement:
--   Let $S(a,b;u,v)$ be a predicate on four natural numbers that validates every elementary block accepted by the finite checker under its validity and size conditions, and is closed under concatenating adjacent intervals with matching carries. Then
--
--   $$S(5552595200, 5569372416; 5552502261794356, 5569281288368260).$$
--
--   The last two arguments are endpoint carries with scale one million. This result provides a verified numerical interval for composing the finite Chebyshev theta estimate.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J.45 (2018),227-251, Theorem 4.2, pp.234-237; DOI 10.1007/s11139-016-9839-4. Supporting finite-certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_theta_mesh_numeric

theorem dusart_theta_mesh_generic_group427 : DusartNumeric.GenericSpec 5552595200 5569372416 5552502261794356 5569281288368260 := by sorry
