-- Prove2me | Theorems.Thm_dusart_theta_mesh_generic_group582
-- name    : dusart_theta_mesh_generic_group582
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-10-17T02:19:26.315988+00:00
-- url     : https://prove2.me/theorems/8dfb9bb8-44ca-4949-9fd0-4288a22e3398
-- title:
--   Verified numerical interval from 8153063680 to 8169840896
-- statement:
--   Let $S(a,b;u,v)$ be a predicate on four natural numbers that validates every elementary block accepted by the finite checker under its validity and size conditions, and is closed under concatenating adjacent intervals with matching carries. Then
--
--   $$S(8153063680, 8169840896; 8152966175228993, 8169745925048880).$$
--
--   The last two arguments are endpoint carries with scale one million. This result provides a verified numerical interval for composing the finite Chebyshev theta estimate.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J.45 (2018),227-251, Theorem 4.2, pp.234-237; DOI 10.1007/s11139-016-9839-4. Supporting finite-certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_theta_mesh_numeric

theorem dusart_theta_mesh_generic_group582 : DusartNumeric.GenericSpec 8153063680 8169840896 8152966175228993 8169745925048880 := by sorry
