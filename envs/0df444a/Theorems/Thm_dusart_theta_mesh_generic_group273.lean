-- Prove2me | Theorems.Thm_dusart_theta_mesh_generic_group273
-- name    : dusart_theta_mesh_generic_group273
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-10-17T01:44:26.363722+00:00
-- url     : https://prove2.me/theorems/33db3386-b3ee-45d5-90d6-0cc8782a8d70
-- title:
--   Verified numerical interval from 2968903936 to 2985681152
-- statement:
--   Let $S(a,b;u,v)$ be a predicate on four natural numbers that validates every elementary block accepted by the finite checker under its validity and size conditions, and is closed under concatenating adjacent intervals with matching carries. Then
--
--   $$S(2968903936, 2985681152; 2968860180781066, 2985635550423196).$$
--
--   The last two arguments are endpoint carries with scale one million. This result provides a verified numerical interval for composing the finite Chebyshev theta estimate.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J.45 (2018),227-251, Theorem 4.2, pp.234-237; DOI 10.1007/s11139-016-9839-4. Supporting finite-certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_theta_mesh_numeric

theorem dusart_theta_mesh_generic_group273 : DusartNumeric.GenericSpec 2968903936 2985681152 2968860180781066 2985635550423196 := by sorry
