-- Prove2me | Theorems.Thm_dusart_theta_mesh_generic_group008
-- name    : dusart_theta_mesh_generic_group008
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-10-17T01:05:15.243753+00:00
-- url     : https://prove2.me/theorems/919ca4c5-7f78-444f-82dd-5948c51feb80
-- title:
--   Verified numerical interval from 116777216 to 118874368
-- statement:
--   Let $S(a,b;u,v)$ be a predicate on four natural numbers that validates every elementary block accepted by the finite checker under its validity and size conditions, and is closed under concatenating adjacent intervals with matching carries. Then
--
--   $$S(116777216, 118874368; 116769517294322, 118864984369831).$$
--
--   The last two arguments are endpoint carries with scale one million. This result provides a verified numerical interval for composing the finite Chebyshev theta estimate.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J.45 (2018),227-251, Theorem 4.2, pp.234-237; DOI 10.1007/s11139-016-9839-4. Supporting finite-certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_theta_mesh_numeric

theorem dusart_theta_mesh_generic_group008 : DusartNumeric.GenericSpec 116777216 118874368 116769517294322 118864984369831 := by sorry
