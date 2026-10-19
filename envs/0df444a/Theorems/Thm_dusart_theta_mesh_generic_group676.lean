-- Prove2me | Theorems.Thm_dusart_theta_mesh_generic_group676
-- name    : dusart_theta_mesh_generic_group676
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-10-17T02:32:12.665095+00:00
-- url     : https://prove2.me/theorems/9218f5c4-c419-47b1-88ee-45fb54185cdd
-- title:
--   Verified numerical interval from 9730121984 to 9746899200
-- statement:
--   Let $S(a,b;u,v)$ be a predicate on four natural numbers that validates every elementary block accepted by the finite checker under its validity and size conditions, and is closed under concatenating adjacent intervals with matching carries. Then
--
--   $$S(9730121984, 9746899200; 9730071355745047, 9746855096141681).$$
--
--   The last two arguments are endpoint carries with scale one million. This result provides a verified numerical interval for composing the finite Chebyshev theta estimate.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J.45 (2018),227-251, Theorem 4.2, pp.234-237; DOI 10.1007/s11139-016-9839-4. Supporting finite-certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_theta_mesh_numeric

theorem dusart_theta_mesh_generic_group676 : DusartNumeric.GenericSpec 9730121984 9746899200 9730071355745047 9746855096141681 := by sorry
