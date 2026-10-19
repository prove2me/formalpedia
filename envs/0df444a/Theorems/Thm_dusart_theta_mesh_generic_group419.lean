-- Prove2me | Theorems.Thm_dusart_theta_mesh_generic_group419
-- name    : dusart_theta_mesh_generic_group419
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-10-17T02:01:59.337353+00:00
-- url     : https://prove2.me/theorems/afd907b9-506a-48a2-9fd5-8622556b5364
-- title:
--   Verified numerical interval from 5418377472 to 5435154688
-- statement:
--   Let $S(a,b;u,v)$ be a predicate on four natural numbers that validates every elementary block accepted by the finite checker under its validity and size conditions, and is closed under concatenating adjacent intervals with matching carries. Then
--
--   $$S(5418377472, 5435154688; 5418297100246709, 5435055145641967).$$
--
--   The last two arguments are endpoint carries with scale one million. This result provides a verified numerical interval for composing the finite Chebyshev theta estimate.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J.45 (2018),227-251, Theorem 4.2, pp.234-237; DOI 10.1007/s11139-016-9839-4. Supporting finite-certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_theta_mesh_numeric

theorem dusart_theta_mesh_generic_group419 : DusartNumeric.GenericSpec 5418377472 5435154688 5418297100246709 5435055145641967 := by sorry
