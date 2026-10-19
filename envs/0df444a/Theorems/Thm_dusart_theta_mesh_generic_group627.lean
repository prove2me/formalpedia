-- Prove2me | Theorems.Thm_dusart_theta_mesh_generic_group627
-- name    : dusart_theta_mesh_generic_group627
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-10-17T02:25:22.820834+00:00
-- url     : https://prove2.me/theorems/ce364240-665a-40c7-8a78-9341d2f78a08
-- title:
--   Verified numerical interval from 8908038400 to 8924815616
-- statement:
--   Let $S(a,b;u,v)$ be a predicate on four natural numbers that validates every elementary block accepted by the finite checker under its validity and size conditions, and is closed under concatenating adjacent intervals with matching carries. Then
--
--   $$S(8908038400, 8924815616; 8907943290773587, 8924714659064325).$$
--
--   The last two arguments are endpoint carries with scale one million. This result provides a verified numerical interval for composing the finite Chebyshev theta estimate.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J.45 (2018),227-251, Theorem 4.2, pp.234-237; DOI 10.1007/s11139-016-9839-4. Supporting finite-certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_theta_mesh_numeric

theorem dusart_theta_mesh_generic_group627 : DusartNumeric.GenericSpec 8908038400 8924815616 8907943290773587 8924714659064325 := by sorry
