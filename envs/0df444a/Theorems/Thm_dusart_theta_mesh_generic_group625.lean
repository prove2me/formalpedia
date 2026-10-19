-- Prove2me | Theorems.Thm_dusart_theta_mesh_generic_group625
-- name    : dusart_theta_mesh_generic_group625
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-10-17T02:25:12.282075+00:00
-- url     : https://prove2.me/theorems/8d96bb13-a4c4-43bd-b416-9338a7a65851
-- title:
--   Verified numerical interval from 8874483968 to 8891261184
-- statement:
--   Let $S(a,b;u,v)$ be a predicate on four natural numbers that validates every elementary block accepted by the finite checker under its validity and size conditions, and is closed under concatenating adjacent intervals with matching carries. Then
--
--   $$S(8874483968, 8891261184; 8874400845369826, 8891174447209440).$$
--
--   The last two arguments are endpoint carries with scale one million. This result provides a verified numerical interval for composing the finite Chebyshev theta estimate.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J.45 (2018),227-251, Theorem 4.2, pp.234-237; DOI 10.1007/s11139-016-9839-4. Supporting finite-certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_theta_mesh_numeric

theorem dusart_theta_mesh_generic_group625 : DusartNumeric.GenericSpec 8874483968 8891261184 8874400845369826 8891174447209440 := by sorry
