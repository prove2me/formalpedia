-- Prove2me | Theorems.Thm_dusart_theta_mesh_generic_group480
-- name    : dusart_theta_mesh_generic_group480
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-10-17T02:07:25.336701+00:00
-- url     : https://prove2.me/theorems/3b587712-8cda-4c2c-96a3-99087d9e7b65
-- title:
--   Verified numerical interval from 6441787648 to 6458564864
-- statement:
--   Let $S(a,b;u,v)$ be a predicate on four natural numbers that validates every elementary block accepted by the finite checker under its validity and size conditions, and is closed under concatenating adjacent intervals with matching carries. Then
--
--   $$S(6441787648, 6458564864; 6441698088936622, 6458465810877130).$$
--
--   The last two arguments are endpoint carries with scale one million. This result provides a verified numerical interval for composing the finite Chebyshev theta estimate.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J.45 (2018),227-251, Theorem 4.2, pp.234-237; DOI 10.1007/s11139-016-9839-4. Supporting finite-certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_theta_mesh_numeric

theorem dusart_theta_mesh_generic_group480 : DusartNumeric.GenericSpec 6441787648 6458564864 6441698088936622 6458465810877130 := by sorry
