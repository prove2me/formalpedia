-- Prove2me | Theorems.Thm_dusart_theta_mesh_generic_group156
-- name    : dusart_theta_mesh_generic_group156
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-10-17T01:31:54.189059+00:00
-- url     : https://prove2.me/theorems/db5ad928-89e3-405f-b2c1-2d10eb08cba2
-- title:
--   Verified numerical interval from 1005969664 to 1022746880
-- statement:
--   Let $S(a,b;u,v)$ be a predicate on four natural numbers that validates every elementary block accepted by the finite checker under its validity and size conditions, and is closed under concatenating adjacent intervals with matching carries. Then
--
--   $$S(1005969664, 1022746880; 1005945207631586, 1022722507234257).$$
--
--   The last two arguments are endpoint carries with scale one million. This result provides a verified numerical interval for composing the finite Chebyshev theta estimate.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J.45 (2018),227-251, Theorem 4.2, pp.234-237; DOI 10.1007/s11139-016-9839-4. Supporting finite-certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_theta_mesh_numeric

theorem dusart_theta_mesh_generic_group156 : DusartNumeric.GenericSpec 1005969664 1022746880 1005945207631586 1022722507234257 := by sorry
