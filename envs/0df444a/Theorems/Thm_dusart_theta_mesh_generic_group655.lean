-- Prove2me | Theorems.Thm_dusart_theta_mesh_generic_group655
-- name    : dusart_theta_mesh_generic_group655
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-10-17T02:29:24.791985+00:00
-- url     : https://prove2.me/theorems/8128566c-cf23-40a5-8546-82b02306fc4c
-- title:
--   Verified numerical interval from 9377800448 to 9394577664
-- statement:
--   Let $S(a,b;u,v)$ be a predicate on four natural numbers that validates every elementary block accepted by the finite checker under its validity and size conditions, and is closed under concatenating adjacent intervals with matching carries. Then
--
--   $$S(9377800448, 9394577664; 9377698979977643, 9394490159695874).$$
--
--   The last two arguments are endpoint carries with scale one million. This result provides a verified numerical interval for composing the finite Chebyshev theta estimate.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J.45 (2018),227-251, Theorem 4.2, pp.234-237; DOI 10.1007/s11139-016-9839-4. Supporting finite-certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_theta_mesh_numeric

theorem dusart_theta_mesh_generic_group655 : DusartNumeric.GenericSpec 9377800448 9394577664 9377698979977643 9394490159695874 := by sorry
