-- Prove2me | Theorems.Thm_dusart_theta_mesh_generic_group054
-- name    : dusart_theta_mesh_generic_group054
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-10-17T01:13:35.664578+00:00
-- url     : https://prove2.me/theorems/a604693f-89fe-4fe7-af68-e31003927987
-- title:
--   Verified numerical interval from 225829120 to 230023424
-- statement:
--   Let $S(a,b;u,v)$ be a predicate on four natural numbers that validates every elementary block accepted by the finite checker under its validity and size conditions, and is closed under concatenating adjacent intervals with matching carries. Then
--
--   $$S(225829120, 230023424; 225812328932166, 230006969642245).$$
--
--   The last two arguments are endpoint carries with scale one million. This result provides a verified numerical interval for composing the finite Chebyshev theta estimate.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J.45 (2018),227-251, Theorem 4.2, pp.234-237; DOI 10.1007/s11139-016-9839-4. Supporting finite-certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_theta_mesh_numeric

theorem dusart_theta_mesh_generic_group054 : DusartNumeric.GenericSpec 225829120 230023424 225812328932166 230006969642245 := by sorry
