-- Prove2me | Theorems.Thm_dusart_theta_mesh_generic_group185
-- name    : dusart_theta_mesh_generic_group185
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-10-17T01:33:51.126301+00:00
-- url     : https://prove2.me/theorems/cc2837c7-ed59-47b8-8454-1f9609ff766d
-- title:
--   Verified numerical interval from 1492508928 to 1509286144
-- statement:
--   Let $S(a,b;u,v)$ be a predicate on four natural numbers that validates every elementary block accepted by the finite checker under its validity and size conditions, and is closed under concatenating adjacent intervals with matching carries. Then
--
--   $$S(1492508928, 1509286144; 1492480993565049, 1509264249391272).$$
--
--   The last two arguments are endpoint carries with scale one million. This result provides a verified numerical interval for composing the finite Chebyshev theta estimate.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J.45 (2018),227-251, Theorem 4.2, pp.234-237; DOI 10.1007/s11139-016-9839-4. Supporting finite-certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_theta_mesh_numeric

theorem dusart_theta_mesh_generic_group185 : DusartNumeric.GenericSpec 1492508928 1509286144 1492480993565049 1509264249391272 := by sorry
