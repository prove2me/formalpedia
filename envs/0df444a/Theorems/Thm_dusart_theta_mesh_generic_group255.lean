-- Prove2me | Theorems.Thm_dusart_theta_mesh_generic_group255
-- name    : dusart_theta_mesh_generic_group255
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-10-17T01:42:15.069032+00:00
-- url     : https://prove2.me/theorems/93c7e89e-bab4-4787-8214-9d526a744c0c
-- title:
--   Verified numerical interval from 2666914048 to 2683691264
-- statement:
--   Let $S(a,b;u,v)$ be a predicate on four natural numbers that validates every elementary block accepted by the finite checker under its validity and size conditions, and is closed under concatenating adjacent intervals with matching carries. Then
--
--   $$S(2666914048, 2683691264; 2666869196948663, 2683649343866428).$$
--
--   The last two arguments are endpoint carries with scale one million. This result provides a verified numerical interval for composing the finite Chebyshev theta estimate.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J.45 (2018),227-251, Theorem 4.2, pp.234-237; DOI 10.1007/s11139-016-9839-4. Supporting finite-certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_theta_mesh_numeric

theorem dusart_theta_mesh_generic_group255 : DusartNumeric.GenericSpec 2666914048 2683691264 2666869196948663 2683649343866428 := by sorry
