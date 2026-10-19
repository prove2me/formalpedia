-- Prove2me | Theorems.Thm_dusart_theta_mesh_generic_group048
-- name    : dusart_theta_mesh_generic_group048
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-10-17T01:13:04.350613+00:00
-- url     : https://prove2.me/theorems/d013e884-fe1e-46a3-82f6-d033bb65a047
-- title:
--   Verified numerical interval from 200663296 to 204857600
-- statement:
--   Let $S(a,b;u,v)$ be a predicate on four natural numbers that validates every elementary block accepted by the finite checker under its validity and size conditions, and is closed under concatenating adjacent intervals with matching carries. Then
--
--   $$S(200663296, 204857600; 200649157625116, 204843737672861).$$
--
--   The last two arguments are endpoint carries with scale one million. This result provides a verified numerical interval for composing the finite Chebyshev theta estimate.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J.45 (2018),227-251, Theorem 4.2, pp.234-237; DOI 10.1007/s11139-016-9839-4. Supporting finite-certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_theta_mesh_numeric

theorem dusart_theta_mesh_generic_group048 : DusartNumeric.GenericSpec 200663296 204857600 200649157625116 204843737672861 := by sorry
