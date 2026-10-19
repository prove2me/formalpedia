-- Prove2me | Theorems.Thm_dusart_theta_mesh_generic_group337
-- name    : dusart_theta_mesh_generic_group337
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-10-17T01:51:28.741768+00:00
-- url     : https://prove2.me/theorems/9518ee71-b5a4-4d42-977c-cb8f9cb6b89e
-- title:
--   Verified numerical interval from 4042645760 to 4059422976
-- statement:
--   Let $S(a,b;u,v)$ be a predicate on four natural numbers that validates every elementary block accepted by the finite checker under its validity and size conditions, and is closed under concatenating adjacent intervals with matching carries. Then
--
--   $$S(4042645760, 4059422976; 4042586689850676, 4059363188859537).$$
--
--   The last two arguments are endpoint carries with scale one million. This result provides a verified numerical interval for composing the finite Chebyshev theta estimate.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J.45 (2018),227-251, Theorem 4.2, pp.234-237; DOI 10.1007/s11139-016-9839-4. Supporting finite-certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_theta_mesh_numeric

theorem dusart_theta_mesh_generic_group337 : DusartNumeric.GenericSpec 4042645760 4059422976 4042586689850676 4059363188859537 := by sorry
