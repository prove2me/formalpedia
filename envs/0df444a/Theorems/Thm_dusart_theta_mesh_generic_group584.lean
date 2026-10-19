-- Prove2me | Theorems.Thm_dusart_theta_mesh_generic_group584
-- name    : dusart_theta_mesh_generic_group584
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-10-17T02:19:53.74925+00:00
-- url     : https://prove2.me/theorems/e467cf78-b8cf-4b5e-9247-a9e061ef5da3
-- title:
--   Verified numerical interval from 8186618112 to 8203395328
-- statement:
--   Let $S(a,b;u,v)$ be a predicate on four natural numbers that validates every elementary block accepted by the finite checker under its validity and size conditions, and is closed under concatenating adjacent intervals with matching carries. Then
--
--   $$S(8186618112, 8203395328; 8186513010903911, 8203304132097112).$$
--
--   The last two arguments are endpoint carries with scale one million. This result provides a verified numerical interval for composing the finite Chebyshev theta estimate.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J.45 (2018),227-251, Theorem 4.2, pp.234-237; DOI 10.1007/s11139-016-9839-4. Supporting finite-certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_theta_mesh_numeric

theorem dusart_theta_mesh_generic_group584 : DusartNumeric.GenericSpec 8186618112 8203395328 8186513010903911 8203304132097112 := by sorry
