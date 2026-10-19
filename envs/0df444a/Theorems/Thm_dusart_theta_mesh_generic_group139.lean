-- Prove2me | Theorems.Thm_dusart_theta_mesh_generic_group139
-- name    : dusart_theta_mesh_generic_group139
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-10-17T01:29:25.952326+00:00
-- url     : https://prove2.me/theorems/7244bd65-dfd8-4434-8df9-ae97ff615cae
-- title:
--   Verified numerical interval from 762700032 to 771088640
-- statement:
--   Let $S(a,b;u,v)$ be a predicate on four natural numbers that validates every elementary block accepted by the finite checker under its validity and size conditions, and is closed under concatenating adjacent intervals with matching carries. Then
--
--   $$S(762700032, 771088640; 762668836872636, 771053993855944).$$
--
--   The last two arguments are endpoint carries with scale one million. This result provides a verified numerical interval for composing the finite Chebyshev theta estimate.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J.45 (2018),227-251, Theorem 4.2, pp.234-237; DOI 10.1007/s11139-016-9839-4. Supporting finite-certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_theta_mesh_numeric

theorem dusart_theta_mesh_generic_group139 : DusartNumeric.GenericSpec 762700032 771088640 762668836872636 771053993855944 := by sorry
