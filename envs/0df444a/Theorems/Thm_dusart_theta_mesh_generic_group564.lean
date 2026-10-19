-- Prove2me | Theorems.Thm_dusart_theta_mesh_generic_group564
-- name    : dusart_theta_mesh_generic_group564
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-10-17T02:17:08.703423+00:00
-- url     : https://prove2.me/theorems/b1ae8bfa-75a5-4439-b8a5-4a5426700cfc
-- title:
--   Verified numerical interval from 7851073792 to 7867851008
-- statement:
--   Let $S(a,b;u,v)$ be a predicate on four natural numbers that validates every elementary block accepted by the finite checker under its validity and size conditions, and is closed under concatenating adjacent intervals with matching carries. Then
--
--   $$S(7851073792, 7867851008; 7850964414587917, 7867743125277874).$$
--
--   The last two arguments are endpoint carries with scale one million. This result provides a verified numerical interval for composing the finite Chebyshev theta estimate.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J.45 (2018),227-251, Theorem 4.2, pp.234-237; DOI 10.1007/s11139-016-9839-4. Supporting finite-certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_theta_mesh_numeric

theorem dusart_theta_mesh_generic_group564 : DusartNumeric.GenericSpec 7851073792 7867851008 7850964414587917 7867743125277874 := by sorry
