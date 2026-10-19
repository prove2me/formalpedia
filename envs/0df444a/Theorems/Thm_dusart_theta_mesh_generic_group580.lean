-- Prove2me | Theorems.Thm_dusart_theta_mesh_generic_group580
-- name    : dusart_theta_mesh_generic_group580
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-10-17T02:22:11.381547+00:00
-- url     : https://prove2.me/theorems/781a7377-9216-4e1c-bb2c-74be3e54f0a8
-- title:
--   Verified numerical interval from 8119509248 to 8136286464
-- statement:
--   Let $S(a,b;u,v)$ be a predicate on four natural numbers that validates every elementary block accepted by the finite checker under its validity and size conditions, and is closed under concatenating adjacent intervals with matching carries. Then
--
--   $$S(8119509248, 8136286464; 8119422376195915, 8136183078121757).$$
--
--   The last two arguments are endpoint carries with scale one million. This result provides a verified numerical interval for composing the finite Chebyshev theta estimate.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J.45 (2018),227-251, Theorem 4.2, pp.234-237; DOI 10.1007/s11139-016-9839-4. Supporting finite-certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_theta_mesh_numeric

theorem dusart_theta_mesh_generic_group580 : DusartNumeric.GenericSpec 8119509248 8136286464 8119422376195915 8136183078121757 := by sorry
