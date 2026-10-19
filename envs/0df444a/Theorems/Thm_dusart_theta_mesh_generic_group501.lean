-- Prove2me | Theorems.Thm_dusart_theta_mesh_generic_group501
-- name    : dusart_theta_mesh_generic_group501
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-10-17T02:09:58.281826+00:00
-- url     : https://prove2.me/theorems/5842aa5c-5568-4163-800b-e1a25478d399
-- title:
--   Verified numerical interval from 6794109184 to 6810886400
-- statement:
--   Let $S(a,b;u,v)$ be a predicate on four natural numbers that validates every elementary block accepted by the finite checker under its validity and size conditions, and is closed under concatenating adjacent intervals with matching carries. Then
--
--   $$S(6794109184, 6810886400; 6794064458272428, 6810831926992327).$$
--
--   The last two arguments are endpoint carries with scale one million. This result provides a verified numerical interval for composing the finite Chebyshev theta estimate.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J.45 (2018),227-251, Theorem 4.2, pp.234-237; DOI 10.1007/s11139-016-9839-4. Supporting finite-certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_theta_mesh_numeric

theorem dusart_theta_mesh_generic_group501 : DusartNumeric.GenericSpec 6794109184 6810886400 6794064458272428 6810831926992327 := by sorry
