-- Prove2me | Theorems.Thm_dusart_theta_mesh_generic_group133
-- name    : dusart_theta_mesh_generic_group133
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-10-17T01:28:50.017988+00:00
-- url     : https://prove2.me/theorems/07925508-4833-4a59-a8bf-9ed97720b2f6
-- title:
--   Verified numerical interval from 712368384 to 720756992
-- statement:
--   Let $S(a,b;u,v)$ be a predicate on four natural numbers that validates every elementary block accepted by the finite checker under its validity and size conditions, and is closed under concatenating adjacent intervals with matching carries. Then
--
--   $$S(712368384, 720756992; 712350748335705, 720735444082394).$$
--
--   The last two arguments are endpoint carries with scale one million. This result provides a verified numerical interval for composing the finite Chebyshev theta estimate.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J.45 (2018),227-251, Theorem 4.2, pp.234-237; DOI 10.1007/s11139-016-9839-4. Supporting finite-certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_theta_mesh_numeric

theorem dusart_theta_mesh_generic_group133 : DusartNumeric.GenericSpec 712368384 720756992 712350748335705 720735444082394 := by sorry
