-- Prove2me | Theorems.Thm_dusart_theta_mesh_generic_group146
-- name    : dusart_theta_mesh_generic_group146
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-10-17T01:29:54.684147+00:00
-- url     : https://prove2.me/theorems/1bac081f-64bb-406c-afd7-eddf23c9963d
-- title:
--   Verified numerical interval from 838197504 to 854974720
-- statement:
--   Let $S(a,b;u,v)$ be a predicate on four natural numbers that validates every elementary block accepted by the finite checker under its validity and size conditions, and is closed under concatenating adjacent intervals with matching carries. Then
--
--   $$S(838197504, 854974720; 838177896673063, 854955660176134).$$
--
--   The last two arguments are endpoint carries with scale one million. This result provides a verified numerical interval for composing the finite Chebyshev theta estimate.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J.45 (2018),227-251, Theorem 4.2, pp.234-237; DOI 10.1007/s11139-016-9839-4. Supporting finite-certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_theta_mesh_numeric

theorem dusart_theta_mesh_generic_group146 : DusartNumeric.GenericSpec 838197504 854974720 838177896673063 854955660176134 := by sorry
