-- Prove2me | Theorems.Thm_dusart_theta_mesh_generic_group657
-- name    : dusart_theta_mesh_generic_group657
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-10-17T02:30:37.488871+00:00
-- url     : https://prove2.me/theorems/b8c02c14-2b3d-4ca9-84ec-1d245f72f5eb
-- title:
--   Verified numerical interval from 9411354880 to 9428132096
-- statement:
--   Let $S(a,b;u,v)$ be a predicate on four natural numbers that validates every elementary block accepted by the finite checker under its validity and size conditions, and is closed under concatenating adjacent intervals with matching carries. Then
--
--   $$S(9411354880, 9428132096; 9411264939493626, 9428053009794339).$$
--
--   The last two arguments are endpoint carries with scale one million. This result provides a verified numerical interval for composing the finite Chebyshev theta estimate.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J.45 (2018),227-251, Theorem 4.2, pp.234-237; DOI 10.1007/s11139-016-9839-4. Supporting finite-certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_theta_mesh_numeric

theorem dusart_theta_mesh_generic_group657 : DusartNumeric.GenericSpec 9411354880 9428132096 9411264939493626 9428053009794339 := by sorry
