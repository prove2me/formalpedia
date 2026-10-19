-- Prove2me | Theorems.Thm_dusart_theta_mesh_generic_group287
-- name    : dusart_theta_mesh_generic_group287
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-10-17T01:46:11.487274+00:00
-- url     : https://prove2.me/theorems/145ae07d-2d68-417d-8428-420ff38972db
-- title:
--   Verified numerical interval from 3203784960 to 3220562176
-- statement:
--   Let $S(a,b;u,v)$ be a predicate on four natural numbers that validates every elementary block accepted by the finite checker under its validity and size conditions, and is closed under concatenating adjacent intervals with matching carries. Then
--
--   $$S(3203784960, 3220562176; 3203725715833124, 3220498643003530).$$
--
--   The last two arguments are endpoint carries with scale one million. This result provides a verified numerical interval for composing the finite Chebyshev theta estimate.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J.45 (2018),227-251, Theorem 4.2, pp.234-237; DOI 10.1007/s11139-016-9839-4. Supporting finite-certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_theta_mesh_numeric

theorem dusart_theta_mesh_generic_group287 : DusartNumeric.GenericSpec 3203784960 3220562176 3203725715833124 3220498643003530 := by sorry
