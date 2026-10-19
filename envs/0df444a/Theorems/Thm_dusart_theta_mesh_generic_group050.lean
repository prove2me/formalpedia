-- Prove2me | Theorems.Thm_dusart_theta_mesh_generic_group050
-- name    : dusart_theta_mesh_generic_group050
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-10-17T01:13:06.316846+00:00
-- url     : https://prove2.me/theorems/7371b9d7-0737-4567-9359-d4eed0a6e09a
-- title:
--   Verified numerical interval from 209051904 to 213246208
-- statement:
--   Let $S(a,b;u,v)$ be a predicate on four natural numbers that validates every elementary block accepted by the finite checker under its validity and size conditions, and is closed under concatenating adjacent intervals with matching carries. Then
--
--   $$S(209051904, 213246208; 209036219309465, 213231713435177).$$
--
--   The last two arguments are endpoint carries with scale one million. This result provides a verified numerical interval for composing the finite Chebyshev theta estimate.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J.45 (2018),227-251, Theorem 4.2, pp.234-237; DOI 10.1007/s11139-016-9839-4. Supporting finite-certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_theta_mesh_numeric

theorem dusart_theta_mesh_generic_group050 : DusartNumeric.GenericSpec 209051904 213246208 209036219309465 213231713435177 := by sorry
