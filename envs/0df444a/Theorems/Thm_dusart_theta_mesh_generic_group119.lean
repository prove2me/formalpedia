-- Prove2me | Theorems.Thm_dusart_theta_mesh_generic_group119
-- name    : dusart_theta_mesh_generic_group119
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-10-17T01:27:42.033077+00:00
-- url     : https://prove2.me/theorems/2222a6c9-a653-4167-8630-1a95f728e5c9
-- title:
--   Verified numerical interval from 594927872 to 603316480
-- statement:
--   Let $S(a,b;u,v)$ be a predicate on four natural numbers that validates every elementary block accepted by the finite checker under its validity and size conditions, and is closed under concatenating adjacent intervals with matching carries. Then
--
--   $$S(594927872, 603316480; 594906541143356, 603300169918635).$$
--
--   The last two arguments are endpoint carries with scale one million. This result provides a verified numerical interval for composing the finite Chebyshev theta estimate.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J.45 (2018),227-251, Theorem 4.2, pp.234-237; DOI 10.1007/s11139-016-9839-4. Supporting finite-certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_theta_mesh_numeric

theorem dusart_theta_mesh_generic_group119 : DusartNumeric.GenericSpec 594927872 603316480 594906541143356 603300169918635 := by sorry
