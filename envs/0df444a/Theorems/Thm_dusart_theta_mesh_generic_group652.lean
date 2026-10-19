-- Prove2me | Theorems.Thm_dusart_theta_mesh_generic_group652
-- name    : dusart_theta_mesh_generic_group652
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-10-17T02:32:15.476911+00:00
-- url     : https://prove2.me/theorems/d751eec7-6918-4c81-93f3-f20413180b52
-- title:
--   Verified numerical interval from 9327468800 to 9344246016
-- statement:
--   Let $S(a,b;u,v)$ be a predicate on four natural numbers that validates every elementary block accepted by the finite checker under its validity and size conditions, and is closed under concatenating adjacent intervals with matching carries. Then
--
--   $$S(9327468800, 9344246016; 9327393591579001, 9344164654172618).$$
--
--   The last two arguments are endpoint carries with scale one million. This result provides a verified numerical interval for composing the finite Chebyshev theta estimate.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J.45 (2018),227-251, Theorem 4.2, pp.234-237; DOI 10.1007/s11139-016-9839-4. Supporting finite-certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_theta_mesh_numeric

theorem dusart_theta_mesh_generic_group652 : DusartNumeric.GenericSpec 9327468800 9344246016 9327393591579001 9344164654172618 := by sorry
