-- Prove2me | Theorems.Thm_dusart_theta_mesh_generic_group296
-- name    : dusart_theta_mesh_generic_group296
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-10-17T01:46:25.842769+00:00
-- url     : https://prove2.me/theorems/acea198d-40b9-44c0-bdd4-be86f86324fc
-- title:
--   Verified numerical interval from 3354779904 to 3371557120
-- statement:
--   Let $S(a,b;u,v)$ be a predicate on four natural numbers that validates every elementary block accepted by the finite checker under its validity and size conditions, and is closed under concatenating adjacent intervals with matching carries. Then
--
--   $$S(3354779904, 3371557120; 3354715008240241, 3371479131617780).$$
--
--   The last two arguments are endpoint carries with scale one million. This result provides a verified numerical interval for composing the finite Chebyshev theta estimate.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J.45 (2018),227-251, Theorem 4.2, pp.234-237; DOI 10.1007/s11139-016-9839-4. Supporting finite-certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_theta_mesh_numeric

theorem dusart_theta_mesh_generic_group296 : DusartNumeric.GenericSpec 3354779904 3371557120 3354715008240241 3371479131617780 := by sorry
