-- Prove2me | Theorems.Thm_dusart_theta_mesh_generic_group452
-- name    : dusart_theta_mesh_generic_group452
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-10-17T02:05:33.880974+00:00
-- url     : https://prove2.me/theorems/1a82e6ca-34bb-40ff-b125-76f842a973a6
-- title:
--   Verified numerical interval from 5972025600 to 5988802816
-- statement:
--   Let $S(a,b;u,v)$ be a predicate on four natural numbers that validates every elementary block accepted by the finite checker under its validity and size conditions, and is closed under concatenating adjacent intervals with matching carries. Then
--
--   $$S(5972025600, 5988802816; 5971946052504644, 5988744626008700).$$
--
--   The last two arguments are endpoint carries with scale one million. This result provides a verified numerical interval for composing the finite Chebyshev theta estimate.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J.45 (2018),227-251, Theorem 4.2, pp.234-237; DOI 10.1007/s11139-016-9839-4. Supporting finite-certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_theta_mesh_numeric

theorem dusart_theta_mesh_generic_group452 : DusartNumeric.GenericSpec 5972025600 5988802816 5971946052504644 5988744626008700 := by sorry
