-- Prove2me | Theorems.Thm_dusart_theta_mesh_generic_group562
-- name    : dusart_theta_mesh_generic_group562
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-10-17T02:20:48.831977+00:00
-- url     : https://prove2.me/theorems/2ae94062-a641-4538-9fa7-e115db7dade4
-- title:
--   Verified numerical interval from 7817519360 to 7834296576
-- statement:
--   Let $S(a,b;u,v)$ be a predicate on four natural numbers that validates every elementary block accepted by the finite checker under its validity and size conditions, and is closed under concatenating adjacent intervals with matching carries. Then
--
--   $$S(7817519360, 7834296576; 7817389415504941, 7834184407366033).$$
--
--   The last two arguments are endpoint carries with scale one million. This result provides a verified numerical interval for composing the finite Chebyshev theta estimate.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J.45 (2018),227-251, Theorem 4.2, pp.234-237; DOI 10.1007/s11139-016-9839-4. Supporting finite-certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_theta_mesh_numeric

theorem dusart_theta_mesh_generic_group562 : DusartNumeric.GenericSpec 7817519360 7834296576 7817389415504941 7834184407366033 := by sorry
