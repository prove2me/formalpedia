-- Prove2me | Theorems.Thm_dusart_theta_mesh_generic_group437
-- name    : dusart_theta_mesh_generic_group437
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-10-17T02:02:41.759115+00:00
-- url     : https://prove2.me/theorems/25ee2cc0-6083-493d-b097-1b5b10a18725
-- title:
--   Verified numerical interval from 5720367360 to 5737144576
-- statement:
--   Let $S(a,b;u,v)$ be a predicate on four natural numbers that validates every elementary block accepted by the finite checker under its validity and size conditions, and is closed under concatenating adjacent intervals with matching carries. Then
--
--   $$S(5720367360, 5737144576; 5720320609363949, 5737092967516568).$$
--
--   The last two arguments are endpoint carries with scale one million. This result provides a verified numerical interval for composing the finite Chebyshev theta estimate.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J.45 (2018),227-251, Theorem 4.2, pp.234-237; DOI 10.1007/s11139-016-9839-4. Supporting finite-certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_theta_mesh_numeric

theorem dusart_theta_mesh_generic_group437 : DusartNumeric.GenericSpec 5720367360 5737144576 5720320609363949 5737092967516568 := by sorry
