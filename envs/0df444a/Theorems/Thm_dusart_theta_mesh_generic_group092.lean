-- Prove2me | Theorems.Thm_dusart_theta_mesh_generic_group092
-- name    : dusart_theta_mesh_generic_group092
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-10-17T01:26:28.402743+00:00
-- url     : https://prove2.me/theorems/986ff8b0-a53f-4c29-8885-65b30aa9a6b4
-- title:
--   Verified numerical interval from 385212672 to 389406976
-- statement:
--   Let $S(a,b;u,v)$ be a predicate on four natural numbers that validates every elementary block accepted by the finite checker under its validity and size conditions, and is closed under concatenating adjacent intervals with matching carries. Then
--
--   $$S(385212672, 389406976; 385199025489431, 389394181625960).$$
--
--   The last two arguments are endpoint carries with scale one million. This result provides a verified numerical interval for composing the finite Chebyshev theta estimate.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J.45 (2018),227-251, Theorem 4.2, pp.234-237; DOI 10.1007/s11139-016-9839-4. Supporting finite-certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_theta_mesh_numeric

theorem dusart_theta_mesh_generic_group092 : DusartNumeric.GenericSpec 385212672 389406976 385199025489431 389394181625960 := by sorry
